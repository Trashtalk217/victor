// debug helper functions

use crate::board_constants::U64Ext;
use crate::gamestate::GameState;
use crate::rules::Rule;
use crate::rules::RuleType;

use std::sync::Arc;

impl Rule {
    pub fn new_from_threats(rule_name: RuleType, squares: u64, solutions: Vec<u64>) -> Rule {
        Rule {
            rule_name,
            squares,
            solves: Arc::new(move |group| solutions.contains(group)),
        }
    }

    pub fn from_strings(rule_name: RuleType, squares: &str, solutions: Vec<&str>) -> Rule {
        Rule::new_from_threats(
            rule_name,
            u64::from_pretty(squares),
            solutions.into_iter().map(|m| u64::from_pretty(m)).collect(),
        )
    }

    pub fn equal(&self, other: &Rule, state: &GameState) -> bool {
        self.rule_name == other.rule_name
            && self.squares == other.squares
            && state.threats().iter().fold(true, |b, group| {
                b && (self.solves)(group) == (other.solves)(group)
            })
    }

    fn not_empty(&self, state: &GameState) -> bool {
        state
            .threats()
            .iter()
            .fold(false, |b, group| (self.solves)(group))
    }
}

pub fn same_rules(rules1: Vec<Rule>, rules2: Vec<Rule>, state: &GameState) {
    // filters out the empty rules
    let rules1: Vec<Rule> = rules1
        .into_iter()
        .filter(|rule| rule.not_empty(&state))
        .collect();
    let rules2: Vec<Rule> = rules2
        .into_iter()
        .filter(|rule| rule.not_empty(&state))
        .collect();

    assert_eq!(rules1.len(), rules2.len());
    for rule in rules1 {
        assert!(rules2.iter().any(|other| rule.equal(other, state)));
    }
}
