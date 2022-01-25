use crate::board_constants::*;
use crate::gamestate::GameState;
use crate::group_predicates::*;

use itertools::chain;
use itertools::iproduct;
use itertools::Itertools;
use std::fmt::Debug;
use std::sync::Arc;

#[derive(Copy, Clone, Hash, PartialEq, Eq, Debug, PartialOrd, Ord)]
pub enum RuleType {
    ClaimEven = 1,
    BaseInverse = 2,
    Vertical = 3,
    AfterEven = 4,
    LowInverse = 5,
    HighInverse = 6,
    BaseClaim = 7,
    Before = 8,
    SpecialBefore = 9,
    OddThreat = 10,
    HighThreatCombination = 11,
    LowThreatCombination = 12,
}

#[derive(Clone)]
pub struct Rule {
    pub rule_name: RuleType,
    pub squares: u64,
    pub solves: GroupPredicate,
}

impl Rule {
    fn new(rule_name: RuleType, squares: u64, solves: GroupPredicate) -> Rule {
        Rule {
            rule_name,
            squares,
            solves,
        }
    }
}

impl Rule {
    fn disjoint(&self, other: &Rule) -> bool {
        self.squares & other.squares == 0
    }

    fn column_wise_disjoint_or_equal(&self, other: &Rule) -> bool {
        for i in 0..WIDTH {
            let column_mask = u64::column(i);
            let col1 = column_mask & self.squares;
            let col2 = column_mask & other.squares;
            if col1 != col2 && (col1 & col2) > 0 {
                return false;
            }
        }
        return true;
    }

    fn disjoint_or_equal_columns(&self, other: &Rule) -> bool {
        let cols1 = self.squares.fill_up() & TOP_MASK;
        let cols2 = other.squares.fill_up() & TOP_MASK;
        cols1 & cols2 == 0 || cols1 == cols2
    }

    // this is the weakest of the pairing functions
    // as in, I'm not sure it's correct, but I'm pretty sure
    fn not_below(&self, other: &Rule) -> bool {
        self.squares.fill_up() & other.squares <= 1
    }

    pub fn can_pair(&self, other: &Rule) -> bool {
        if self.rule_name > other.rule_name {
            return other.can_pair(self);
        }

        use RuleType::*;
        match (self.rule_name, other.rule_name) {
            (ClaimEven, ClaimEven)
            | (ClaimEven, BaseInverse)
            | (ClaimEven, Vertical)
            | (ClaimEven, AfterEven)
            | (ClaimEven, BaseClaim)
            | (ClaimEven, Before)
            | (ClaimEven, SpecialBefore)
            | (BaseInverse, BaseInverse)
            | (BaseInverse, Vertical)
            | (BaseInverse, AfterEven)
            | (BaseInverse, LowInverse)
            | (BaseInverse, HighInverse)
            | (BaseInverse, BaseClaim)
            | (BaseInverse, Before)
            | (BaseInverse, SpecialBefore)
            | (Vertical, Vertical)
            | (Vertical, AfterEven)
            | (Vertical, LowInverse)
            | (Vertical, HighInverse)
            | (Vertical, BaseClaim)
            | (Vertical, Before)
            | (Vertical, SpecialBefore)
            | (AfterEven, BaseClaim)
            | (BaseClaim, BaseClaim)
            | (BaseClaim, Before)
            | (BaseClaim, SpecialBefore) => self.disjoint(other),
            (AfterEven, AfterEven)
            | (AfterEven, Before)
            | (AfterEven, SpecialBefore)
            | (Before, Before)
            | (Before, SpecialBefore)
            | (SpecialBefore, SpecialBefore) => self.column_wise_disjoint_or_equal(other),
            (ClaimEven, LowInverse) | (ClaimEven, HighInverse) => self.not_below(other),
            (AfterEven, LowInverse)
            | (AfterEven, HighInverse)
            | (LowInverse, BaseClaim)
            | (HighInverse, BaseClaim)
            | (HighInverse, Before)
            | (HighInverse, SpecialBefore) => self.not_below(other) && self.disjoint(other),
            (LowInverse, LowInverse) | (LowInverse, HighInverse) | (HighInverse, HighInverse) => {
                self.disjoint_or_equal_columns(other) && self.disjoint(other)
            }
            (LowInverse, Before) | (LowInverse, SpecialBefore) => {
                self.not_below(other) && self.column_wise_disjoint_or_equal(other)
            }
            _ => {
                panic!("Rule Pair not covered");
            }
        }
    }
}

// returns high and low threat_combinations seperated
type ThreatTriple = (u64, u64, u64);

impl GameState {
    fn claim_even(&self) -> impl Iterator<Item = Rule> + '_ {
        CLAIM_EVEN_PAIRS
            .iter()
            .cloned()
            .filter(move |pair| self.mask.is_disjoint(pair))
            .map(|pair| Rule::new(RuleType::ClaimEven, pair, through(EVEN_MASK & pair)))
    }

    fn base_inverse(&self) -> impl Iterator<Item = Rule> + '_ {
        let playable_moves_mask = (self.mask + BOTTOM_MASK) & BOARD_MASK;
        COLUMN_MASK_PAIRS
            .iter()
            .map(move |column_mask_pair| column_mask_pair & playable_moves_mask)
            .filter(move |maybe_pair| maybe_pair.count_ones() == 2)
            .map(move |pair| Rule::new(RuleType::BaseInverse, pair, through(pair)))
    }

    fn vertical(&self) -> impl Iterator<Item = Rule> + '_ {
        VERTICAL_PAIRS
            .iter()
            .cloned()
            .filter(move |pair| self.mask.is_disjoint(pair))
            .map(move |pair| Rule::new(RuleType::Vertical, pair, through(pair)))
    }

    fn after_even(&self) -> impl Iterator<Item = Rule> + '_ {
        let opponent_mask = self.position ^ self.mask;
        let claim_even_mask = EVEN_MASK & (self.mask.smear_up(1) ^ BOARD_MASK);
        let opponent_threat_mask = opponent_mask | claim_even_mask;

        self.opponent_threats()
            .into_iter()
            .filter(move |group| group.is_subset(&opponent_threat_mask))
            .map(move |group| ((self.mask ^ BOARD_MASK) & group).fill_up())
            .unique()
            .map(move |squares| {
                Rule::new(
                    RuleType::AfterEven,
                    squares.smear_down(1),
                    Arc::new(move |group| {
                        (group & squares).fill_up() & TOP_MASK == squares & TOP_MASK
                    }),
                )
            })
    }

    pub fn low_inverse(&self) -> impl Iterator<Item = Rule> + '_ {
        LOW_INVERSE_PAIRS
            .iter()
            .cloned()
            .filter(move |squares| self.mask.is_disjoint(squares))
            .map(move |squares| {
                Rule::new(
                    RuleType::LowInverse,
                    squares,
                    Arc::new(move |group| {
                        (ODD_MASK & squares).is_subset(group)
                            || (group.is_vertical() && squares.num_overlap(group) == 2)
                    }),
                )
            })
    }

    pub fn high_inverse(&self) -> impl Iterator<Item = Rule> + '_ {
        let playable_squares = (self.mask + BOTTOM_MASK) & BOARD_MASK;
        HIGH_INVERSE_SQUARES
            .iter()
            .cloned()
            .filter(move |squares| self.mask.is_disjoint(squares))
            .map(move |squares| {
                Rule::new(
                    RuleType::HighInverse,
                    squares,
                    Arc::new(move |group| {
                        let bottom_squares = squares & (squares >> 2);
                        let middle_squares = bottom_squares << 1;
                        let upper_squares = middle_squares << 1;
                        upper_squares.is_subset(group)
                            || middle_squares.is_subset(group)
                            || (group.is_vertical()
                                && ((middle_squares | upper_squares) & *group).count_ones() == 2)
                            || (!group.is_vertical()
                                && (playable_squares & bottom_squares & *group).count_ones() == 1
                                && ((*group & upper_squares).count_ones() == 1))
                    }),
                )
            })
    }

    // check if there exists a threat that goes through 2 given squares
    // this could be solved more cleverly, but that can be figured out later
    fn threat_through_exists(&self, square1: u64, square2: u64) -> bool {
        self.threats()
            .iter()
            .any(|group| (square1 | square2).is_subset(group))
    }

    pub fn base_claim(&self) -> impl Iterator<Item = Rule> + '_ {
        // calculate Vec<u64> with singles being playable moves
        let playable_singles: Vec<u64> = self.playable_mask().split();
        let playable_doubles: Vec<u64> = playable_singles
            .clone()
            .into_iter()
            .filter(|square| (square << 1).is_subset(&EVEN_MASK))
            .collect();
        iproduct!(
            playable_singles.clone().into_iter(),
            playable_doubles.into_iter(),
            playable_singles.into_iter()
        )
        // this filter removes
        // 1. the invalid triples (they can't overlap)
        // 2. the useless triples that don't result in substantive rules
        .filter(move |(s1, d, s2)| {
            (*s1 | *d | *s2).count_ones() == 3
                && self.threat_through_exists(*s1, *d << 1)
                && self.threat_through_exists(*s2, *d)
        })
        .map(move |(s1, d, s2)| {
            Rule::new(
                RuleType::BaseClaim,
                s1 | d.smear_up(1) | s2,
                Arc::new(move |group| {
                    (s1 | (d << 1)).is_subset(group) || (s2 | d).is_subset(group)
                }),
            )
        })
    }

    fn permute_smear(n: u64) -> Vec<u64> {
        n.split()
            .into_iter()
            .map(|x| vec![x.smear_up(1), x.smear_down(1)].into_iter())
            .fold(vec![0], |vec1, vec2| {
                vec1.into_iter()
                    .cartesian_product(vec2)
                    .map(|(x, y)| x | y)
                    .collect()
            })
    }

    // used by before and special_before
    fn before_groups(&self) -> impl Iterator<Item = u64> + '_ {
        // verticals are excluded, and it's very unlikely that will ever be included
        // I don't think they work with the logic in the paper
        self.opponent_threats()
            .into_iter()
            .filter(|group| !group.is_vertical())
            .map(move |group| group & (BOARD_MASK ^ self.mask))
            .filter(|squares| *squares & TOP_MASK == 0)
            .unique()
    }

    fn before_rules_from_group(&self, before_group: u64) -> Vec<Rule> {
        GameState::permute_smear(before_group)
            .into_iter()
            .filter(|squares| squares.count_ones() == before_group.count_ones() * 2)
            .filter(|squares| self.mask.is_disjoint(squares))
            .map(|squares| {
                let verticals = (squares.clear_up(1) & ODD_MASK).smear_down(1);
                let even_claims = squares.clear_up(1) & EVEN_MASK;
                Rule::new(
                    RuleType::Before,
                    squares,
                    Arc::new(move |group| {
                        (before_group << 1).is_subset(group)
                            || (verticals.num_overlap(group) == 2 && group.is_vertical())
                            || even_claims & *group > 0
                    }),
                )
            })
            .collect()
    }

    fn before(&self) -> impl Iterator<Item = Rule> + '_ {
        self.before_groups()
            .map(|squares| self.before_rules_from_group(squares))
            .concat()
            .into_iter()
    }

    // I'm by far the least sure about this function, it might just be wrong and cause problems later
    fn special_before(&self) -> impl Iterator<Item = Rule> + '_ {
        let special_before_group = self
            .before_groups()
            .filter(|squares| squares & self.playable_mask() > 0);

        // generate the normal before rules
        let playable_pairs = COLUMN_MASK_PAIRS
            .clone()
            .into_iter()
            .map(|cols| cols & self.playable_mask())
            .filter(|squares| squares.count_ones() == 2);

        let combination = special_before_group
            .cartesian_product(playable_pairs)
            .filter(|(group, pair)| {
                (group & pair).count_ones() == 1 && (group.fill_down() & pair).count_ones() == 1
            });

        combination
            .map(|(squares, pair)| {
                self.before_rules_from_group(squares)
                    .into_iter()
                    .map(|rule| {
                        Rule::new(
                            RuleType::SpecialBefore,
                            rule.squares | pair,
                            or2(rule.solves, through(pair)),
                        )
                    })
                    .collect::<Vec<Rule>>()
            })
            .concat()
            .into_iter()
    }
    // rule used by white
    pub fn odd_threats(&self) -> Vec<Rule> {
        let empties = BOARD_MASK ^ self.mask;

        // I could probably get away with checking only even threats
        let black_threat_mask: u64 = (self
            .threats()
            .into_iter()
            .map(|group| {
                if group.is_vertical() {
                    group.clear_up(3)
                } else {
                    group
                }
            })
            .fold(0, |acc, group| acc | group)
            & empties)
            .fill_up()
            << 1
            & BOARD_MASK;

        // assume that it's blacks turn
        let white_mask = self.mask ^ self.position;
        let odd_threats = self
            .opponent_threats()
            .into_iter()
            .filter(|group| white_mask.num_overlap(group) == 3)
            .map(|group| group - (group & white_mask))
            .filter(|square| square.is_subset(&ODD_MASK))
            .filter(|square| (self.mask + BOTTOM_MASK).is_disjoint(square))
            .filter(|square| !square.is_subset(&black_threat_mask));
        // find the best oppdd threat per column
        (0..WIDTH)
            .filter_map(|i| {
                // get the lowest odd threat in this column i (if available)
                odd_threats
                    .clone()
                    .into_iter()
                    .filter(|square| square.is_subset(&u64::column(i)))
                    .min()
            })
            .map(|square| {
                // this may be very wrong, but it doesn't seem to fail
                Rule::new(RuleType::OddThreat, 0, hits(square.fill_up()))
            })
            .collect()
    }

    pub fn threat_combinations(&self) -> (Vec<ThreatTriple>, Vec<ThreatTriple>) {
        // assume that it's blacks turn
        let white_mask = self.mask ^ self.position;
        let threats_with_two_squares = self
            .opponent_threats()
            .into_iter()
            .filter(|group| white_mask.num_overlap(group) == 2);

        let temp = threats_with_two_squares
            .clone()
            .cartesian_product(threats_with_two_squares)
            .filter(|(group1, group2)| group1 != group2)
            .filter(|(group1, _)| (!self.mask & group1).is_subset(&ODD_MASK))
            .filter(|(group1, group2)| (!self.mask & group1 & group2).count_ones() == 1)
            .map(|(group1, group2)| {
                let crossing = !self.mask & group1 & group2;
                let other_odd = !(crossing | white_mask) & group1;
                let other_even = !(crossing | white_mask) & group2;
                (crossing, other_odd, other_even)
            });

        let high_threat_combination: Vec<ThreatTriple> = temp
            .clone()
            .filter(|(_, other_odd, other_even)| *other_even == (other_odd << 1))
            .filter(|(crossing, _, _)| crossing.is_disjoint(&(self.mask + BOTTOM_MASK)))
            .collect();
        let low_threat_combination: Vec<ThreatTriple> = temp
            .filter(|(_, other_odd, other_even)| *other_even == (other_odd >> 1))
            .filter(|(crossing, _, _)| crossing.is_disjoint(&(self.mask + BOTTOM_MASK)))
            .collect();

        (low_threat_combination, high_threat_combination)
    }

    fn exclude_from_upper_threat_triple(&self, crossing: u64, other: u64) -> Vec<Rule> {
        let pad_up_mask = self.mask.smear_up(1);
        let crossing_column = crossing.fill_up().fill_down();
        let other_column = other.fill_up().fill_down();
        let first_playable = (self.mask + BOTTOM_MASK) & crossing_column;
        let other_playable = (self.mask + BOTTOM_MASK) & other_column;
        let other_is_playable = self.square_is_playable(other);

        let base_predicate = or4(
            hits(crossing_column & ODD_MASK & (!pad_up_mask)),
            through_pairs_above(crossing, other),
            through(other | crossing << 1),
            optional(other_is_playable, hits(crossing.fill_up().clear_up(2))),
        );

        let rule1 = Rule::new(
            RuleType::LowThreatCombination,
            crossing_column | other_column,
            or2(
                base_predicate.clone(),
                through_vertical_pairs_between(other_playable, other),
            ),
        );

        // can we use rule 5?
        if first_playable.is_subset(&ODD_MASK) && !other_is_playable {
            // if so, generate rule2 with 5 and 6b
            let rule2 = Rule::new(
                RuleType::LowThreatCombination,
                crossing_column | other_column,
                or3(
                    base_predicate,
                    hits(first_playable | other_playable),
                    through_vertical_pairs_between(other_playable >> 1, other),
                ),
            );

            return vec![rule1, rule2];
        }
        return vec![rule1];
    }

    // these are a lot like rules, maybe we should start calling them that way
    // TODO: find a way to concat Rules
    pub fn threat_combination_high(&self) -> Vec<Rule> {
        let (_, threat_combination_triples) = self.threat_combinations();

        threat_combination_triples
            .into_iter()
            .map(|(crossing, other_odd, _)| {
                self.exclude_from_upper_threat_triple(crossing, other_odd)
            })
            .collect::<Vec<Vec<Rule>>>()
            .concat()
    }

    fn exclude_from_lower_threat_triple(&self, crossing: u64, other: u64, even: u64) -> Vec<Rule> {
        // two cases, the lower even is playable and the lower even is not
        let crossing_column = crossing.fill_down().fill_up();
        let other_column = other.fill_down().fill_up();
        let pad_up_mask = self.mask.smear_up(1);
        let first_playable = (self.mask + BOTTOM_MASK) & crossing_column;
        let other_playable = (self.mask + BOTTOM_MASK) & other_column;
        let other_is_playable = self.square_is_playable(other);

        let base_predicate = or2(
            hits(crossing_column & ODD_MASK & (!pad_up_mask)),
            through_pairs_above(crossing, other),
        );

        if !self.square_is_playable(even) {
            // can we apply rule 3?
            let rule1 = Rule::new(
                RuleType::LowThreatCombination,
                crossing_column | other_column,
                or2(
                    base_predicate.clone(),
                    through_vertical_pairs_between(other_playable, other),
                ),
            );

            // if we can use rule 3, an additional rule has to be created
            if first_playable.is_subset(&ODD_MASK) && !other_is_playable {
                // return two rules
                // do apply rule 3 and 4b
                let rule2 = Rule::new(
                    RuleType::LowThreatCombination,
                    crossing_column | other_column,
                    or3(
                        base_predicate,
                        through(first_playable | other_playable),
                        through_vertical_pairs_between(other_playable >> 1, other),
                    ),
                );

                return vec![rule1, rule2];
            }

            return vec![rule1];
        }

        return vec![Rule::new(
            RuleType::LowThreatCombination,
            crossing_column | other_column,
            base_predicate,
        )];
    }

    pub fn threat_combination_low(&self) -> Vec<Rule> {
        let (threat_combination_triples, _) = self.threat_combinations();

        threat_combination_triples
            .into_iter()
            .map(|(crossing, other_odd, other_even)| {
                self.exclude_from_lower_threat_triple(crossing, other_odd, other_even)
            })
            .collect::<Vec<Vec<Rule>>>()
            .concat()
    }

    pub fn rules_from_type(&self, rule_name: RuleType) -> Vec<Rule> {
        match rule_name {
            RuleType::ClaimEven => self.claim_even().collect(),
            RuleType::BaseInverse => self.base_inverse().collect(),
            RuleType::Vertical => self.vertical().collect(),
            RuleType::AfterEven => self.after_even().collect(),
            RuleType::LowInverse => self.low_inverse().collect(),
            RuleType::HighInverse => self.high_inverse().collect(),
            RuleType::BaseClaim => self.base_claim().collect(),
            RuleType::Before => self.before().collect(),
            RuleType::SpecialBefore => self.special_before().collect(),
            RuleType::OddThreat => self.odd_threats(),
            RuleType::HighThreatCombination => self.threat_combination_high(),
            RuleType::LowThreatCombination => self.threat_combination_low(),
            _ => panic!(),
        }
    }

    pub fn rules(&self, types: Vec<RuleType>) -> Vec<Rule> {
        types
            .into_iter()
            .map(|name| self.rules_from_type(name))
            .concat()
    }

    pub fn all_rules(&self) -> impl Iterator<Item = Rule> + '_ {
        // special_before() left out intentionally
        chain!(
            self.vertical(),
            self.claim_even(),
            self.base_inverse(),
            self.after_even(),
            self.low_inverse(),
            self.high_inverse(),
            self.base_claim(),
            self.before(),
            // self.special_before()
        )
    }
}

#[cfg(test)]
mod rule_tests {
    use crate::board_constants::U64Ext;
    use crate::debug::same_rules;
    use crate::rules::GameState;
    use crate::rules::Rule;
    use crate::rules::RuleType as RT;

    macro_rules! rule {
        ( $RTV:ident, $SQUARES:literal, [$($POS:literal ),* $(,)?] $(,)?) => {
            Rule::from_strings(RT::$RTV, $SQUARES ,vec![ $($POS ,)* ])
        };
    }

    #[test]
    fn rule_equality_test() {
        let state = GameState::empty();

        assert!(rule!(ClaimEven, "(a1, a2)", ["a1-d4"])
            .equal(&rule!(ClaimEven, "(a1, a2)", ["a1-d4"]), &state));

        assert!(!rule!(BaseInverse, "(b5)", []).equal(&rule!(Vertical, "(b5)", []), &state));

        assert!(!rule!(BaseInverse, "(d6)", ["a1-a4"])
            .equal(&rule!(BaseInverse, "(d6)", ["a2-a5"]), &state));

        assert!(rule!(Vertical, "(a1)", ["c1-c4", "a1-a4"])
            .equal(&rule!(Vertical, "(a1)", ["a1-a4", "c1-c4"]), &state));
    }

    #[test]
    fn claim_even_test() {
        let state = GameState::from_string("34444445");

        // there are too many rules, this is a subset
        let expected_rules = [
            rule!(ClaimEven, "(a1, a2)", ["a1-a4", "a2-a5", "a2-d2"]),
            rule!(
                ClaimEven,
                "(c3, c4)",
                ["c1-c4", "c2-c5", "c3-c6", "a4-d4", "b4-e4", "c4-f4"],
            ),
            rule!(
                ClaimEven,
                "(f1, f2)",
                ["f1-f4", "f2-f5", "c2-f2", "d2-g2", "c5-f2", "d4-g1"],
            ),
        ];

        let calculated_rules: Vec<Rule> = state.claim_even().collect();
    }

    #[test]
    fn base_inverse_test() {
        let state = GameState::from_string("354433");

        let expected_rules: Vec<Rule> = vec![
            rule!(BaseInverse, "(a1, b1)", ["a1-d1"]),
            rule!(BaseInverse, "(b1, d3)", ["b1-e4"]),
            rule!(BaseInverse, "(c4, d3)", ["a6-d3", "b5-e2", "c4-f1"]),
            rule!(BaseInverse, "(c4, e2)", ["b5-e2", "c4-f1"]),
            rule!(BaseInverse, "(c4, f1)", ["c4-f1"]),
            rule!(BaseInverse, "(d3, e2)", ["b5-e2", "c4-f1"]),
            rule!(BaseInverse, "(d3, f1)", ["c4-f1"]),
            rule!(BaseInverse, "(e2, f1)", ["c4-f1"]),
        ];

        let calculated_rules: Vec<Rule> = state.base_inverse().collect();

        same_rules(expected_rules, calculated_rules, &state);
    }

    #[test]
    fn vertical_test() {
        let state = GameState::from_string("3533435453");

        let expected_rules = vec![
            rule!(Vertical, "(a2, a3)", ["a1-a4", "a2-a5"]),
            rule!(Vertical, "(a4, a5)", ["a2-a5", "a3-a6"]),
            rule!(Vertical, "(b2, b3)", ["b1-b4", "b2-b5"]),
            rule!(Vertical, "(b4, b5)", ["b2-b5", "b3-b6"]),
            rule!(Vertical, "(d4, d5)", ["d3-d6"]),
            rule!(Vertical, "(e4, e5)", ["e2-e5", "e3-e6"]),
            rule!(Vertical, "(f2, f3)", ["f1-f4", "f2-f5"]),
            rule!(Vertical, "(f4, f5)", ["f2-f5", "f3-f6"]),
            rule!(Vertical, "(g2, g3)", ["g1-g4", "g2-g5"]),
            rule!(Vertical, "(g4, g5)", ["g2-g5", "g3-g6"]),
        ];

        let calculated_rules: Vec<Rule> = state.vertical().collect();

        same_rules(calculated_rules, expected_rules, &state);
    }

    #[test]
    fn after_even_test() {
        let state = GameState::from_string("444545443331313351115155");

        let calculated_rules: Vec<Rule> = state.after_even().collect();

        #[rustfmt::skip]
        let expected_rules = vec![
            rule!(
                AfterEven,
                "|b|",
                ["b1-b4", "b2-b5", "b3-b6",
                     "a4-d4", "b3-e3", "b4-e4", "b5-e5",
                     "b2-e5",
                     "b6-e3"]
            ),
            rule!(
                AfterEven,
                "|f|",
                ["f1-f4", "f2-f5", "f3-f6",
                 "c3-f3", "c4-f4", "c5-f5", "d3-g3", "d4-g4", "d5-g5",
                 "c3-f6", "d3-g6",
                     "c5-f2", "d4-g1", "d5-g2"],
            ),
            // these two act as a break even, could probably delete later
            rule!(AfterEven, "(b5, b6)", ["b3-b6", "b6-e3"]),
            rule!(AfterEven, "(f5, f6)", ["f3-f6", "c3-f6"]),
            rule!(
                AfterEven,
                "|f|g|",
                ["d3-g3", "d4-g4", "d5-g5", "d3-g6", "d5-g2"],
            ),
        ];

        same_rules(calculated_rules, expected_rules, &state);
    }

    #[test]
    fn low_inverse_test() {
        let state = GameState::from_string("11222254433661133554");

        let expected_rules = vec![
            rule!(
                LowInverse,
                "(d4, d5, e4, e5)",
                ["e3-e6", "b5-e5", "c5-f5", "d5-g5"],
            ),
            rule!(
                LowInverse,
                "(d4, d5, f4, f5)",
                ["f2-f5", "f3-f6", "c5-f5", "d5-g5"],
            ),
            rule!(LowInverse, "(d4, d5, g4, g5)", ["g2-g5", "g3-g6", "d5-g5"],),
            rule!(
                LowInverse,
                "(e4, e5, f4, f5)",
                ["e3-e6", "f2-f5", "f3-f6", "c5-f5", "d5-g5"],
            ),
            rule!(
                LowInverse,
                "(e4, e5, g2, g3)",
                ["e3-e6", "g1-g4", "g2-g5", "d6-g3"],
            ),
            rule!(
                LowInverse,
                "(e4, e5, g4, g5)",
                ["e3-e6", "g2-g5", "g3-g6", "d5-g5"],
            ),
            rule!(
                LowInverse,
                "(f4, f5, g4, g5)",
                ["f2-f5", "f3-f6", "g2-g5", "g3-g6", "d5-g5"],
            ),
        ];

        let calculated_rules: Vec<Rule> = state.low_inverse().collect();

        same_rules(calculated_rules, expected_rules, &state);
    }

    #[test]
    fn high_inverse_test() {
        let state = GameState::from_string("44536756767567561134327111");
        println!("{}", state.to_string());

        let expected_rules = vec![
            rule!(
                HighInverse,
                "(b2, b3, b4, c4, c5, c6)",
                ["b2-b5", "b3-b6", "c3-c6", "a4-d4", "b4-e4"],
            ),
            rule!(
                HighInverse,
                "(b2, b3, b4, d4, d5, d6)",
                ["b2-b5", "b3-b6", "a4-d4", "b4-e4", "b3-e6"],
            ),
            rule!(
                HighInverse,
                "(b4, b5, b6, c4, c5, c6)",
                ["b3-b6", "c3-c6", "a6-d6", "b5-e5", "b6-e6"],
            ),
            rule!(
                HighInverse,
                "(b4, b5, b6, d4, d5, d6)",
                ["b3-b6", "a6-d6", "b5-e5", "b6-e6"],
            ),
            rule!(
                HighInverse,
                "(c4, c5, c6, d4, d5, d6)",
                ["c3-c6", "a6-d6", "b5-e5", "b6-e6", "c6-f6"],
            ),
        ];

        let calculated_rules: Vec<Rule> = state.high_inverse().collect();

        same_rules(calculated_rules, expected_rules, &state);
    }

    #[test]
    fn base_claim_test() {
        let state = GameState::from_string("1233777777");

        let expected_rules = vec![
            rule!(BaseClaim, "(a2, b2, c3, c4)", ["a2-d5", "a1-d4", "b2-e5"],),
            rule!(BaseClaim, "(a2, c3, c4, e1)", ["a2-d5", "b4-e1"]),
            rule!(BaseClaim, "(b2, c3, c4, f1)", ["a1-d4", "b2-e5", "c4-f1"],),
            rule!(BaseClaim, "(c3, c4, e1, f1)", ["b4-e1", "c4-f1"]),
            rule!(
                BaseClaim,
                "(c3, d1, d2, e1)",
                ["a5-d2", "b4-e1", "c1-f1", "d1-g1"],
            ),
            rule!(
                BaseClaim,
                "(c3, d1, d2, f1)",
                ["a5-d2", "b4-e1", "c1-f1", "d1-g1"],
            ),
            rule!(BaseClaim, "(d1, d2, e1, f1)", ["b4-e1", "c1-f1", "d1-g1"],),
            rule!(BaseClaim, "(c3, e1, e2, f1)", ["b4-e1", "c4-f1"]),
            rule!(BaseClaim, "(d1, e1, e2, f1)", ["c4-f1", "c1-f1", "d1-g1"],),
        ];

        let calculated_rules: Vec<Rule> = state.base_claim().collect();

        same_rules(calculated_rules, expected_rules, &state);
    }

    #[test]
    fn before_test() {
        let state = GameState::from_string("12");

        // a subset of all calculated rules, since there are too many to check all.
        let expected_rules = vec![
            rule!(
                Before,
                "(a2, a3, b2, b3, c1, c2, d1, d2)",
                [
                    "a3-d3", "a1-a4", "a2-a5", "b2-b5", "c1-c4", "c2-c5", "a2-d2", "b2-e2",
                    "c2-f2", "c2-f5", "a4-d1", "d1-d4", "d2-d5", "d2-g2", "c1-f4", "d2-g5",
                    "a5-d2", "b4-e1",
                ],
            ),
            rule!(
                Before,
                "(a4, a5, b4, b5, c3, c4, d3, d4)",
                [
                    "a5-d5", "a2-a5", "a3-a6", "b2-b5", "b3-b6", "c1-c4", "c2-c5", "c3-c6",
                    "a4-d4", "b4-e4", "c4-f4", "a2-d5", "b3-e6", "a6-d3", "b5-e2", "c4-f1",
                    "d1-d4", "d2-d5", "d3-d6", "d4-g4", "a1-d4", "b2-e5", "c3-f6", "b6-e3",
                    "c5-f2", "d4-g1",
                ],
            ),
        ];

        let calculated_rules: Vec<Rule> = state.before().collect();

        // 164 may be wrong, but it's good to keep of it changing
        println!("{}", calculated_rules.len());
        assert_eq!(calculated_rules.len(), 407);
        for rule1 in expected_rules {
            assert!(calculated_rules
                .iter()
                .any(|rule2| rule1.equal(rule2, &state)));
        }
    }

    #[test]
    fn permute_smear_test() {
        let group = u64::from_pretty("(d5, f5, g5)");
        let variations = GameState::permute_smear(group);
        let expected_variations = vec![
            u64::from_pretty("(d4, d5, f4, f5, g4, g5)"),
            u64::from_pretty("(d4, d5, f4, f5, g5, g6)"),
            u64::from_pretty("(d4, d5, f5, f6, g4, g5)"),
            u64::from_pretty("(d4, d5, f5, f6, g5, g6)"),
            u64::from_pretty("(d5, d6, f4, f5, g4, g5)"),
            u64::from_pretty("(d5, d6, f4, f5, g5, g6)"),
            u64::from_pretty("(d5, d6, f5, f6, g4, g5)"),
            u64::from_pretty("(d5, d6, f5, f6, g5, g6)"),
        ];
        assert_eq!(variations.len(), expected_variations.len());
        for variation in expected_variations {
            assert!(variations.contains(&variation));
        }
    }

    #[test]
    fn single_before_group_test() {
        let state = GameState::from_string("655651721435342216255374674123");
        let group = u64::from_pretty("(d5, f5, g5)");
        println!("{}", state.to_string());

        let calculated_rules = state.before_rules_from_group(group);
        let expected_rules = vec![
            rule!(
                Before,
                "(d5, d6, f5, f6, g5, g6)",
                ["a6-d6", "b6-e6", "c6-f6", "d6-g6", "a3-d6"]
            ),
            rule!(
                Before,
                "(d5, d6, f5, f6, g4, g5)",
                ["a6-d6", "b6-e6", "c6-f6", "d6-g6", "a3-d6"]
            ),
        ];

        same_rules(calculated_rules, expected_rules, &state);
    }

    #[test]
    fn special_before_test() {
        let state = GameState::from_string("655651721435342216255374674123");

        let calculated_rules: Vec<Rule> = state.special_before().collect();
        let expected_rules: Vec<Rule> = vec![
            rule!(
                SpecialBefore,
                "(a5, c5, c6, d5, d6, f5, f6)",
                ["a6-d6", "b6-e6", "c6-f6", "d6-g6", "a3-d6", "a5-d5"]
            ),
            rule!(
                SpecialBefore,
                "(a5, c5, c6, d5, d6, f5, f6)",
                ["a6-d6", "b6-e6", "c6-f6", "d6-g6", "a3-d6", "a5-d5"]
            ),
            rule!(
                SpecialBefore,
                "(b6, c5, c6, d5, d6, f5, f6)",
                ["a6-d6", "b6-e6", "c6-f6", "d6-g6", "a3-d6", "b6-e3"]
            ),
            rule!(
                SpecialBefore,
                "(b6, c5, c6, d5, d6, f5, f6)",
                ["a6-d6", "b6-e6", "c6-f6", "d6-g6", "a3-d6"]
            ),
            rule!(
                SpecialBefore,
                "(c5, c6, d5, d6, f5, f6, g5)",
                ["a6-d6", "b6-e6", "c6-f6", "d6-g6", "a3-d6"]
            ),
            rule!(
                SpecialBefore,
                "(c5, c6, d5, d6, f5, f6, g5)",
                ["a6-d6", "b6-e6", "c6-f6", "d6-g6", "a3-d6"]
            ),
            rule!(
                SpecialBefore,
                "(a1, d5, d6, f5, f6, g4, g5)",
                ["a6-d6", "b6-e6", "c6-f6", "d6-g6", "a3-d6", "a5-d5"]
            ),
            rule!(
                SpecialBefore,
                "(a5, d5, d6, f5, f6, g4, g5)",
                ["a6-d6", "b6-e6", "c6-f6", "d6-g6", "a3-d6", "a5-d5"]
            ),
            rule!(
                SpecialBefore,
                "(b6, d5, d6, f5, f6, g4, g5)",
                ["a6-d6", "b6-e6", "c6-f6", "d6-g6", "a3-d6"]
            ),
            rule!(
                SpecialBefore,
                "(c5, d5, d6, f5, f6, g4, g5)",
                ["a6-d6", "b6-e6", "c6-f6", "d6-g6", "a3-d6", "a5-d5"]
            ),
            rule!(
                SpecialBefore,
                "(c5, d5, d6, f5, f6, g4, g5)",
                ["a6-d6", "b6-e6", "c6-f6", "d6-g6", "a3-d6"]
            ),
            rule!(
                SpecialBefore,
                "(a5, d5, d6, f5, f6, g5, g6)",
                ["a6-d6", "b6-e6", "c6-f6", "d6-g6", "a3-d6", "a5-d5"]
            ),
            rule!(
                SpecialBefore,
                "(b6, d5, d6, f5, f6, g5, g6)",
                ["a6-d6", "b6-e6", "c6-f6", "d6-g6", "a3-d6"]
            ),
            rule!(
                SpecialBefore,
                "(c5, d5, d6, f5, f6, g5, g6)",
                ["a6-d6", "b6-e6", "c6-f6", "d6-g6", "a3-d6", "a5-d5"]
            ),
            rule!(
                SpecialBefore,
                "(c5, d5, d6, f5, f6, g5, g6)",
                ["a6-d6", "b6-e6", "c6-f6", "d6-g6", "a3-d6"]
            ),
        ];
        same_rules(expected_rules, calculated_rules, &state);
    }

    #[test]
    fn threat_combination_test() {
        let state = GameState::from_string("512731675216777764255326525213664");
        println!("{}", state.to_string());
        let (low_threat_combinations, high_threat_combinations) = state.threat_combinations();
        let expected_high_threat_combinations = vec![
            (
                u64::from_pretty("(c5)"),
                u64::from_pretty("(d5)"),
                u64::from_pretty("(d6)"),
            ),
            (
                u64::from_pretty("(d5)"),
                u64::from_pretty("(c5)"),
                u64::from_pretty("(c6)"),
            ),
        ];

        assert_eq!(
            high_threat_combinations.len(),
            expected_high_threat_combinations.len()
        );

        for triple in high_threat_combinations.clone().into_iter() {
            assert!(expected_high_threat_combinations.contains(&triple));
        }

        let expected_low_threat_combinations = vec![(
            u64::from_pretty("(d5)"),
            u64::from_pretty("(c5)"),
            u64::from_pretty("(c4)"),
        )];

        assert_eq!(
            low_threat_combinations.len(),
            expected_low_threat_combinations.len()
        );

        for triple in low_threat_combinations.clone().into_iter() {
            assert!(expected_low_threat_combinations.contains(&triple));
        }
    }
}
