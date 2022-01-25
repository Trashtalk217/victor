use crate::board_constants::U64Ext;
use crate::gamestate::GameState;
use crate::rules::Rule;
use crate::rules::RuleType;
use itertools::chain;
use petgraph::graph::Graph;
use petgraph::graph::NodeIndex;
use petgraph::Undirected;
use std::collections::HashSet;

pub struct Evaluator {
    threat_indices: HashSet<NodeIndex>,
    rule_indices: HashSet<NodeIndex>,
    rules: Vec<Rule>,
    resolutions: Graph<usize, (), Undirected>,
    rule_conflicts: Graph<usize, (), Undirected>,
}

// make a sparse matrix from rules to rules (square), where a 1 represents
// a conflict between two rules (can't be applied simultaneously)
// construct a sparse matrix between rules and potential threats (for whom?)
// write out the following pseudo code:

impl Evaluator {
    pub fn new(state: &GameState) -> Evaluator {
        Evaluator::with_rules_and_threats(state.all_rules().collect::<Vec<Rule>>(), state.threats())
    }

    pub fn new_with_exclude(state: &GameState, exclude_mask: u64) -> Evaluator {
        Evaluator::with_rules_and_threats(
            state.all_rules().collect::<Vec<Rule>>(),
            state
                .threats()
                .into_iter()
                .filter(|group| group.is_disjoint(&exclude_mask))
                .collect(),
        )
    }

    pub fn new_with_forced_rule(state: &GameState, rule: Rule) -> Evaluator {
        Evaluator::with_rules_and_threats(
            state
                .all_rules()
                .filter(|r| r.squares.is_disjoint(&rule.squares))
                .collect::<Vec<Rule>>(),
            state
                .threats()
                .into_iter()
                .filter(|group| !(rule.solves)(group))
                .collect(),
        )
    }

    pub fn with_rules_and_threats(rules: Vec<Rule>, threats: Vec<u64>) -> Evaluator {
        let mut rule_conflicts: Graph<usize, (), Undirected> = Graph::new_undirected();

        let rule_indices: HashSet<NodeIndex> = (0..rules.len())
            .map(|i| rule_conflicts.add_node(i))
            .collect();

        // connections between rules and threats
        let mut resolutions: Graph<usize, (), Undirected> = rule_conflicts.clone();

        for i in &rule_indices {
            for j in &rule_indices {
                let rule1 = &rules[*rule_conflicts.node_weight(*i).unwrap()];
                let rule2 = &rules[*rule_conflicts.node_weight(*j).unwrap()];
                // not sure what to do when i == j, currently a connection
                if !rule1.can_pair(rule2) {
                    rule_conflicts.add_edge(*i, *j, ());
                }
            }
        }

        let threat_indices: HashSet<NodeIndex> = (0..threats.len())
            .map(|i| resolutions.add_node(i))
            .collect();

        for i in &rule_indices {
            for j in &threat_indices {
                let rule = &rules[*resolutions.node_weight(*i).unwrap()];
                let threat = threats[*resolutions.node_weight(*j).unwrap()];
                if (rule.solves)(&threat) {
                    resolutions.add_edge(*i, *j, ());
                }
            }
        }

        Evaluator {
            threat_indices,
            rule_indices,
            rules,
            rule_conflicts,
            resolutions,
        }
    }

    pub fn eval(&self) -> bool {
        self.solve_exists(self.rule_indices.clone(), self.threat_indices.clone())
    }

    #[inline]
    fn worst_threat(&self, threats_set: &HashSet<NodeIndex>) -> NodeIndex {
        *threats_set
            .into_iter()
            .min_by(|x, y| {
                self.resolutions
                    .neighbors_undirected(**x)
                    .count()
                    .cmp(&self.resolutions.neighbors_undirected(**y).count())
            })
            .unwrap()
    }

    fn solve_exists(&self, rules_set: HashSet<NodeIndex>, threats_set: HashSet<NodeIndex>) -> bool {
        if threats_set.is_empty() {
            return true;
        } else {
            let worst_threat = self.worst_threat(&threats_set);

            if self.resolutions.neighbors_undirected(worst_threat).count() == 0 {
                return false;
            }

            for rule in self
                .resolutions
                .neighbors_undirected(worst_threat)
                .collect::<HashSet<NodeIndex>>()
                .intersection(&rules_set)
            {
                // wondering if I can do the same with .difference()
                let mut new_rules = rules_set.clone();
                for rule_to_remove in self.rule_conflicts.neighbors_undirected(*rule) {
                    new_rules.remove(&rule_to_remove);
                }
                let mut new_threats = threats_set.clone();
                for threat_to_remove in self.resolutions.neighbors_undirected(*rule) {
                    new_threats.remove(&threat_to_remove);
                }
                let sol = self.solve_exists(new_rules, new_threats);
                if sol {
                    return true;
                }
            }
            return false;
        }
    }

    fn find_valid_subset(
        &self,
        rules_set: HashSet<NodeIndex>,
        threats_set: HashSet<NodeIndex>,
    ) -> Option<HashSet<NodeIndex>> {
        if threats_set.is_empty() {
            return Some(HashSet::new());
        } else {
            let worst_threat = self.worst_threat(&threats_set);

            for rule in self
                .resolutions
                .neighbors_undirected(worst_threat)
                .collect::<HashSet<NodeIndex>>()
                .intersection(&rules_set)
            {
                // wondering if I can do the same with .difference()
                let mut new_rules = rules_set.clone();
                for rule_to_remove in self.rule_conflicts.neighbors_undirected(*rule) {
                    new_rules.remove(&rule_to_remove);
                }
                let mut new_threats = threats_set.clone();
                for threat_to_remove in self.resolutions.neighbors_undirected(*rule) {
                    new_threats.remove(&threat_to_remove);
                }

                let sol = self.find_valid_subset(new_rules, new_threats);
                match sol {
                    Some(set) => {
                        let mut new_set = set.clone();
                        new_set.insert(*rule);
                        return Some(new_set);
                    }
                    None => (),
                }
            }
            return None;
        }
    }

    pub fn eval_actual(&self) -> Option<Vec<(RuleType, u64)>> {
        let indices =
            self.find_valid_subset(self.rule_indices.clone(), self.threat_indices.clone());
        match indices {
            None => None,
            Some(set) => Some(
                set.into_iter()
                    .map(|i| &self.rules[self.rule_conflicts[i].clone()])
                    .map(|rule| (rule.rule_name, rule.squares))
                    .collect(),
            ),
        }
    }
}

pub fn eval(state: &GameState) -> i32 {
    /*
    A position in which White is to move, can be evaluated with Black as
    controller of the Zugzwang, while a position with Black to move can be
    evaluated with White as controller. In the last case the evaluation should be
    done on a part of the board, without one (odd threat) or two columns (threat
    combination).
     */

    match state.plies() % 2 {
        0 => {
            if state.can_win_next() {
                return 1;
            }

            let evaluator = Evaluator::new(state);
            if evaluator.eval() {
                return -1;
            }
            return 0;
        }
        _ => {
            if state.can_win_next() {
                return -1;
            }
            // evaluation on part of the board means that there are squares which
            // we can remove the threats for
            if chain!(
                state.odd_threats().into_iter(),
                state.threat_combination_high().into_iter(),
                state.threat_combination_low().into_iter()
            )
            .any(|rule| Evaluator::new_with_forced_rule(state, rule).eval())
            {
                return 1;
            } else {
                return 0;
            }
        }
    }
}

#[cfg(test)]
mod eval_tests {
    use crate::eval::eval;
    use crate::eval::Evaluator;
    use crate::gamestate::GameState;
    use crate::rules::RuleType;

    #[test]
    fn claim_even_eval_test() {
        // same testcase used in rules.rs
        let state1 = GameState::from_string("34444445");
        let evaluator1 = Evaluator::with_rules_and_threats(
            state1.rules_from_type(RuleType::ClaimEven),
            state1.threats(),
        );
        assert!(evaluator1.eval());

        let state2 = GameState::from_string("1333333777777421");
        let evaluator2 = Evaluator::with_rules_and_threats(
            state2.rules_from_type(RuleType::ClaimEven),
            state2.threats(),
        );
        assert!(evaluator2.eval());
    }

    #[test]
    fn three_rules_test() {
        // test with only BaseInverse, ClaimEven and Vertical
        // this is a very broad test, wish I could go more granular
        let state = GameState::from_string("655651721435342216255374674123");
        assert!(eval(&state) == 0);
    }

    #[ignore]
    #[test]
    fn empty_test() {
        let state = GameState::empty();
        assert!(eval(&state) == 0);
    }

    #[test]
    fn after_even_test() {
        let state1 = GameState::from_string("3344354551");
        let evaluator1 = Evaluator::with_rules_and_threats(
            state1.rules(vec![
                RuleType::ClaimEven,
                RuleType::BaseInverse,
                RuleType::Vertical,
                RuleType::AfterEven,
            ]),
            state1.threats(),
        );
        assert!(evaluator1.eval());

        // position 3.1 from the paper
        let state2 = GameState::from_string("444545443331313351115155");
        let evaluator2 = Evaluator::with_rules_and_threats(
            state2.rules(vec![
                RuleType::ClaimEven,
                RuleType::BaseInverse,
                RuleType::Vertical,
                RuleType::AfterEven,
            ]),
            state2.threats(),
        );
        assert!(evaluator2.eval());
    }

    #[test]
    fn before_test() {
        let state1 = GameState::from_string("12");
        let evaluator1 = Evaluator::with_rules_and_threats(
            state1.rules(vec![
                RuleType::Before,
                RuleType::BaseInverse,
                RuleType::ClaimEven,
            ]),
            state1.threats(),
        );
        assert!(evaluator1.eval());

        let state2 = GameState::from_string("23");
        let evaluator2 = Evaluator::with_rules_and_threats(
            state2.rules(vec![
                RuleType::Before,
                RuleType::BaseInverse,
                RuleType::ClaimEven,
            ]),
            state2.threats(),
        );
        assert!(evaluator2.eval());

        let state3 = GameState::from_string("34");
        let evaluator3 = Evaluator::with_rules_and_threats(
            state3.rules(vec![
                RuleType::Before,
                RuleType::BaseInverse,
                RuleType::ClaimEven,
            ]),
            state3.threats(),
        );
        assert!(evaluator3.eval());
    }

    #[ignore]
    #[test]
    fn before_fail() {
        let state1 = GameState::from_string("777627122221557755");
        assert!(eval(&state1) == 0);

        let state2 = GameState::from_string("751321");
        assert!(eval(&state2) == 0);
    }

    #[test]
    fn odd_threat_test() {
        let state1 = GameState::from_string("333244442525155");
        assert!(eval(&state1) == 1);

        let state2 = GameState::from_string("333244442525755");
        assert!(eval(&state2) == 1);
    }

    #[ignore]
    #[test]
    fn threat_combination_high() {
        let state = GameState::from_string("512731675216777764255326525213664");
        println!("{}", state.to_string());
        assert!(eval(&state) == 1);

        let state = GameState::from_string("4554444455557");
        println!("{}", state.to_string());
        assert!(eval(&state) == 1);

        // should maybe complete? Not entirely sure.
        let state = GameState::from_string("45454354554");
        println!("{}", state.to_string());
        assert!(eval(&state) == 1);
    }
}
