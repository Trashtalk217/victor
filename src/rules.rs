use crate::gamestate::GameState;

use crate::board_constants::U64Ext;
use crate::board_constants::BOARD_MASK;
use crate::board_constants::BOTTOM_MASK;
use crate::board_constants::CLAIM_EVEN_PAIRS;
use crate::board_constants::COLUMN_MASK_PAIRS;
use crate::board_constants::EVEN_MASK;
use crate::board_constants::HIGH_INVERSE_SQUARES;
use crate::board_constants::LOW_INVERSE_PAIRS;
use crate::board_constants::ODD_MASK;
use crate::board_constants::TOP_MASK;
use crate::board_constants::VERTICAL_PAIRS;
use crate::board_constants::WIDTH;

use itertools::chain;
use itertools::iproduct;
use itertools::Itertools;
use std::collections::HashSet;
use std::fmt::Debug;
use std::fmt::Formatter;
use std::fmt::Result;

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

#[derive(Hash)]
pub struct Rule {
    pub rule_name: RuleType,
    pub squares: u64,        // more of a mask really
    pub solutions: Vec<u64>, // must be a subset of GROUPS
}

impl Rule {
    fn new(rule_name: RuleType, squares: u64, solutions: Vec<u64>) -> Rule {
        Rule {
            rule_name,
            squares,
            solutions,
        }
    }

    fn try_new(rule_name: RuleType, squares: u64, solutions: Vec<u64>) -> Option<Rule> {
        if solutions.is_empty() {
            None
        } else {
            Some(Rule::new(rule_name, squares, solutions))
        }
    }

    fn from_strings(rule_name: RuleType, squares: &str, solutions: Vec<&str>) -> Rule {
        Rule::new(
            rule_name,
            u64::from_pretty(squares),
            solutions.into_iter().map(|m| u64::from_pretty(m)).collect(),
        )
    }

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

// really slow, shouldn't be used often
impl PartialEq for Rule {
    fn eq(&self, other: &Rule) -> bool {
        let mut a_sol = self.solutions.clone();
        let mut b_sol = other.solutions.clone();
        a_sol.sort();
        b_sol.sort();

        self.rule_name == other.rule_name && self.squares == other.squares && a_sol == b_sol
    }
}

impl Debug for Rule {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        f.debug_struct("Rule")
            .field("name", &self.rule_name)
            .field("squares", &self.squares.to_pretty())
            .field(
                "solutions",
                &self
                    .solutions
                    .clone()
                    .into_iter()
                    .map(|m| m.to_pretty())
                    .collect::<Vec<String>>(),
            )
            .finish()
    }
}

impl Eq for Rule {}

// returns high and low threat_combinations seperated
type ThreatTriple = (u64, u64, u64);

impl GameState {
    fn claim_even(&self) -> impl Iterator<Item = Rule> + '_ {
        CLAIM_EVEN_PAIRS
            .iter()
            .cloned()
            .filter(move |pair| self.mask.is_disjoint(pair))
            .filter_map(move |pair| {
                Rule::try_new(
                    RuleType::ClaimEven,
                    pair,
                    self.potential_threats()
                        .into_iter()
                        .filter(|group| (EVEN_MASK & pair).is_subset(group))
                        .collect(),
                )
            })
    }

    fn base_inverse(&self) -> impl Iterator<Item = Rule> + '_ {
        let playable_moves_mask = (self.mask + BOTTOM_MASK) & BOARD_MASK;
        COLUMN_MASK_PAIRS
            .iter()
            .map(move |column_mask_pair| column_mask_pair & playable_moves_mask)
            .filter(move |maybe_pair| maybe_pair.count_ones() == 2)
            .filter_map(move |pair| {
                Rule::try_new(
                    RuleType::BaseInverse,
                    pair,
                    self.potential_threats()
                        .into_iter()
                        .filter(|group| pair.is_subset(group))
                        .collect(),
                )
            })
    }

    fn vertical(&self) -> impl Iterator<Item = Rule> + '_ {
        VERTICAL_PAIRS
            .iter()
            .cloned()
            .filter(move |pair| self.mask.is_disjoint(pair))
            .filter_map(move |pair| {
                Rule::try_new(
                    RuleType::Vertical,
                    pair,
                    self.potential_threats()
                        .into_iter()
                        .filter(|group| pair.is_subset(group))
                        .collect(),
                )
            })
    }

    fn after_even(&self) -> impl Iterator<Item = Rule> {
        let opponent_mask = self.position ^ self.mask;
        let claim_even_mask = EVEN_MASK & (self.mask.smear_up(1) ^ BOARD_MASK);
        let opponent_threat_mask = opponent_mask | claim_even_mask;

        self.opponent_threats()
            .into_iter()
            .filter(|group| group.is_subset(&opponent_threat_mask))
            .map(|group| ((self.mask ^ BOARD_MASK) & group).fill_up())
            .filter_map(|squares| {
                Rule::try_new(
                    RuleType::AfterEven,
                    squares.smear_down(1),
                    self.potential_threats()
                        .into_iter()
                        .filter(|threat| {
                            (threat & squares).fill_up() & TOP_MASK == squares & TOP_MASK
                        })
                        .collect(),
                )
            })
            .collect::<HashSet<Rule>>() // should probably avoid this, there are better ways
            .into_iter()
    }

    pub fn low_inverse(&self) -> impl Iterator<Item = Rule> + '_ {
        LOW_INVERSE_PAIRS
            .iter()
            .cloned()
            .filter(move |squares| self.mask.is_disjoint(squares))
            .filter_map(move |squares| -> Option<Rule> {
                Rule::try_new(
                    RuleType::LowInverse,
                    squares,
                    self.potential_threats()
                        .into_iter()
                        .filter(|group| {
                            (ODD_MASK & squares).is_subset(group)
                                || (group.is_vertical() && squares.num_overlap(group) == 2)
                        })
                        .collect(),
                )
            })
    }

    pub fn high_inverse(&self) -> impl Iterator<Item = Rule> + '_ {
        let playable_squares = (self.mask + BOTTOM_MASK) & BOARD_MASK;
        HIGH_INVERSE_SQUARES
            .iter()
            .cloned()
            .filter(move |squares| self.mask.is_disjoint(squares))
            .filter_map(move |squares| {
                Rule::try_new(
                    RuleType::HighInverse,
                    squares,
                    self.potential_threats()
                        .clone()
                        .into_iter()
                        .filter(|group| {
                            let bottom_squares = squares & (squares >> 2);
                            let middle_squares = bottom_squares << 1;
                            let upper_squares = middle_squares << 1;
                            upper_squares.is_subset(group)
                                || middle_squares.is_subset(group)
                                || (group.is_vertical()
                                    && ((middle_squares | upper_squares) & *group).count_ones()
                                        == 2)
                                || (!group.is_vertical()
                                    && (playable_squares & bottom_squares & *group).count_ones()
                                        == 1
                                    && ((*group & upper_squares).count_ones() == 1))
                        })
                        .collect(),
                )
            })
    }

    pub fn base_claim(&self) -> impl Iterator<Item = Rule> + '_ {
        // calculate Vec<u64> with singles being playable moves
        let playable_singles: Vec<u64> = (0..WIDTH)
            .map(|i| u64::column(i) & (self.mask + BOTTOM_MASK))
            .filter(|i| *i > 0)
            .collect();
        let playable_doubles: Vec<u64> = playable_singles
            .clone()
            .iter()
            .map(|square| square.smear_up(1))
            .filter(|squares| squares & (squares << 1) & EVEN_MASK > 0)
            .collect();
        iproduct!(
            playable_singles.clone().into_iter(),
            playable_doubles.into_iter(),
            playable_singles.into_iter()
        )
        .filter(move |(s1, d, s2)| (*s1 | *d | *s2).count_ones() == 4)
        .map(move |(s1, d, s2)| {
            (
                (s1, d, s2),
                self.potential_threats()
                    .clone()
                    .into_iter()
                    .filter(|group| {
                        (s1 | (d & d << 1)).is_subset(group) || (s2 | (d & d >> 1)).is_subset(group)
                    })
                    .collect::<Vec<u64>>(),
            )
        })
        .filter(|((s1, d, s2), groups)| {
            groups
                .iter()
                .any(|group| (s1 | (d & d << 1)).is_subset(group))
                && groups
                    .iter()
                    .any(|group| (s2 | (d & d >> 1)).is_subset(group))
        })
        .map(|((s1, d, s2), groups)| Rule::new(RuleType::BaseClaim, s1 | d | s2, groups))
    }

    fn permute_shift(n: u64) -> Vec<u64> {
        fn split(n: u64) -> Vec<u64> {
            let mut i = n;
            let mut result = vec![];
            while i != 0 {
                let part: u64 = 1 << i.trailing_zeros();
                result.push(part);
                i ^= part;
            }
            result
        }

        if n == 0 {
            return vec![];
        }
        // split up n in powers of two
        let pairs: Vec<Vec<u64>> = split(n).into_iter().map(|x| vec![x >> 1, x << 1]).collect();

        pairs.into_iter().fold(vec![0], |vec1: Vec<u64>, vec2| {
            vec1.into_iter()
                .cartesian_product(vec2.into_iter())
                .map(|(x, y)| x | y)
                .collect()
        })
    }

    fn before(&self) -> impl Iterator<Item = Rule> + '_ {
        let claim_even_mask = (self.mask.smear_up(1) ^ BOARD_MASK) & EVEN_MASK;

        // verticals are excluded, because they work strange with permute_shift
        // could maybe make that work later
        self.opponent_threats()
            .into_iter()
            .filter(|group| !group.is_vertical()) // <-- here
            .map(|group| group & (BOARD_MASK ^ self.mask))
            .filter(|squares| *squares & TOP_MASK == 0)
            .map(|squares| {
                GameState::permute_shift(squares & claim_even_mask)
                    .into_iter()
                    .map(|shifts| {
                        (
                            squares,
                            shifts | squares | ((squares ^ (squares & claim_even_mask)) << 1),
                        )
                    })
                    .collect::<Vec<(u64, u64)>>()
            })
            .concat()
            .into_iter()
            .map(move |(base, squares)| {
                Rule::new(
                    RuleType::Before,
                    squares,
                    self.potential_threats()
                        .into_iter()
                        .filter(|group| {
                            (base << 1).is_subset(&group)
                                || (((squares.clear_up(1) & ODD_MASK).smear_down(1) & *group)
                                    .count_ones()
                                    == 2
                                    && group.is_vertical())
                                || (squares.clear_up(1) & EVEN_MASK & *group > 0)
                        })
                        .collect(),
                )
            })
    }

    // I'm by far the least sure about this function, it might just be wrong and cause problems later.
    fn special_before(&self) -> impl Iterator<Item = Rule> + '_ {
        let claim_even_mask = (self.mask.smear_up(1) ^ BOARD_MASK) & EVEN_MASK;
        let playable_singles = (0..WIDTH)
            .map(move |i| u64::column(i) & (self.mask + BOTTOM_MASK))
            .filter(|i| *i > 0);
        let playable_squares = (self.mask + BOTTOM_MASK) & BOARD_MASK;

        // only horizontals are used, because they seem to work
        // could maybe make that work later
        self.opponent_threats()
            .into_iter()
            .filter(|group| group.is_horizontal()) // <-- here
            .map(|group| group & (BOARD_MASK ^ self.mask))
            .filter(|squares| {
                (*squares & TOP_MASK == 0) && ((*squares & playable_squares).is_power_of_two())
            })
            .map(|squares| {
                GameState::permute_shift(squares & claim_even_mask)
                    .into_iter()
                    .map(|shifts| {
                        (
                            squares,
                            shifts | squares | ((squares ^ (squares & claim_even_mask)) << 1),
                        )
                    })
                    .collect::<Vec<(u64, u64)>>()
            })
            .concat()
            .into_iter()
            .cartesian_product(playable_singles)
            .filter(|((_, squares), playable_square)| {
                playable_square.fill_up() & squares.fill_up() == 0
            })
            .map(move |((base, squares), playable_square)| {
                (
                    playable_square,
                    base,
                    Rule::new(
                        RuleType::SpecialBefore,
                        squares | playable_square,
                        self.potential_threats()
                            .into_iter()
                            .filter(|group| {
                                (((base << 1) | playable_square).is_subset(group))
                                    || ((playable_square | (playable_squares & base))
                                        .is_subset(group))
                                    || (((squares.clear_up(1) & ODD_MASK).smear_down(1) & *group)
                                        .count_ones()
                                        == 2
                                        && group.is_vertical())
                                    || (squares.clear_up(1) & EVEN_MASK & *group > 0)
                            })
                            .collect(),
                    ),
                )
            })
            .filter(move |(playable_square, base, rule)| {
                rule.solutions
                    .clone()
                    .into_iter()
                    .any(|group| (playable_square | (base << 1)).is_subset(&group))
                    && rule.solutions.clone().into_iter().any(|group| {
                        (playable_square | (base & playable_squares)).is_subset(&group)
                    })
            })
            .map(|(_, _, rule)| rule)
    }

    // rule used by white
    pub fn odd_threats(&self) -> Vec<Rule> {
        let empties = BOARD_MASK ^ self.mask;

        // I could probably get away with checking only even threats
        let black_threat_mask: u64 = (self
            .potential_threats()
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
                Rule::new(
                    RuleType::OddThreat,
                    0, // this may be very wrong, but it doesn't seem to fail
                    self.potential_threats()
                        .into_iter()
                        .filter(|group| group.is_disjoint(&square.fill_up()))
                        .collect(),
                )
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

    fn exclude_from_upper_threat_triple(&self, crossing: u64, other: u64) -> Rule {
        let pad_up_mask = self.mask.smear_up(1);
        let crossing_column = crossing.fill_up().fill_down();
        let other_column = other.fill_up().fill_down();
        let first_playable = (self.mask + BOTTOM_MASK) & crossing_column;
        let other_playable = (self.mask + BOTTOM_MASK) & other_column;

        let pairs: Vec<u64> = (crossing << 1)
            .fill_up()
            .split()
            .into_iter()
            .cartesian_product((other << 1).fill_up().split().into_iter())
            .map(|(x, y)| x | y)
            .collect();

        let threats = self
            .potential_threats()
            .into_iter()
            .filter(|group| group.is_disjoint(&(crossing_column & ODD_MASK & (!pad_up_mask))))
            .filter(|group| {
                !pairs
                    .clone()
                    .into_iter()
                    .map(|pair| pair.is_subset(&group))
                    .fold(false, |x, acc| acc || x)
            })
            .filter(|group| !(other | crossing << 1).is_subset(group))
            .filter(|group| {
                !self.square_is_playable(other)
                    | group.is_disjoint(&(crossing.fill_up().clear_up(2)))
            })
            .filter(|group| {
                !(first_playable.is_subset(&ODD_MASK) && !self.square_is_playable(other))
                    | !(first_playable | other_playable).is_subset(group)
            })
            .filter(|group| {
                if first_playable.is_subset(&ODD_MASK) && !self.square_is_playable(other) {
                    !group.is_vertical()
                        || group.is_disjoint(&(other.fill_down() & (other_playable << 1).fill_up()))
                } else {
                    !group.is_vertical()
                        || group.is_disjoint(&(other.fill_down() & other_playable.fill_up()))
                }
            });

        // rule 6 (and possibly 5) are not implemented correctly
        // there's no evaluation on "4554444455557", while there should be
        // the threat d6-g6 should be resolved, but isn't...
        // it currently doesn't break anything, but could be more effective then it is

        // might be fixed due to broadening rule 2, but I still don't full understand 5 and 6

        Rule::new(
            RuleType::HighThreatCombination,
            crossing_column | other_column,
            threats.collect(),
        )
    }

    // these are a lot like rules, maybe we should start calling them that way
    pub fn threat_combination_high(&self) -> Vec<Rule> {
        let (_, threat_combination_triples) = self.threat_combinations();

        threat_combination_triples
            .into_iter()
            .map(|(crossing, other_odd, _)| {
                self.exclude_from_upper_threat_triple(crossing, other_odd)
            })
            .collect()
    }

    fn exclude_from_lower_threat_triple(&self, crossing: u64, other: u64, even: u64) -> Rule {
        // two cases, the lower even is playable and the lower even is not
        let crossing_column = crossing.fill_down().fill_up();
        let other_column = other.fill_down().fill_up();
        let pad_up_mask = self.mask.smear_up(1);
        let first_playable = (self.mask + BOTTOM_MASK) & crossing_column;
        let other_playable = (self.mask + BOTTOM_MASK) & other_column;

        let pairs: Vec<u64> = (crossing << 1)
            .fill_up()
            .split()
            .into_iter()
            .cartesian_product((other << 1).fill_up().split().into_iter())
            .map(|(x, y)| x | y)
            .collect();

        // it is not playable
        if !self.square_is_playable(even) {
            let threats = self
                .potential_threats()
                .into_iter()
                .filter(|group| group.is_disjoint(&(crossing_column & ODD_MASK & (!pad_up_mask))))
                .filter(|group| {
                    !pairs
                        .clone()
                        .into_iter()
                        .map(|pair| pair.is_subset(&group))
                        .fold(false, |x, acc| acc || x)
                })
                .filter(|group| {
                    !(first_playable.is_subset(&ODD_MASK) && !self.square_is_playable(other))
                        | !(first_playable | other_playable).is_subset(group)
                })
                .filter(|group| {
                    if first_playable.is_subset(&ODD_MASK) && !self.square_is_playable(other) {
                        !group.is_vertical()
                            || group
                                .is_disjoint(&(other.fill_down() & (other_playable << 1).fill_up()))
                    } else {
                        !group.is_vertical()
                            || group.is_disjoint(&(other.fill_down() & other_playable.fill_up()))
                    }
                });

            // the problems of the high combination threats with the last two rules apply here too
            // if they do apply
            Rule::new(
                RuleType::LowThreatCombination,
                crossing_column | other_column,
                threats.collect(),
            )
        } else {
            let threats = self
                .potential_threats()
                .into_iter()
                .filter(|group| group.is_disjoint(&(crossing_column & ODD_MASK & (!pad_up_mask))))
                .filter(|group| {
                    !pairs
                        .clone()
                        .into_iter()
                        .map(|pair| pair.is_subset(&group))
                        .fold(false, |x, acc| acc || x)
                });

            Rule::new(
                RuleType::LowThreatCombination,
                crossing_column | other_column,
                threats.collect(),
            )
        }
    }

    pub fn threat_combination_low(&self) -> Vec<Rule> {
        let (threat_combination_triples, _) = self.threat_combinations();

        threat_combination_triples
            .into_iter()
            .map(|(crossing, other_odd, other_even)| {
                self.exclude_from_lower_threat_triple(crossing, other_odd, other_even)
            })
            .collect()
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
        )
    }
}

#[cfg(test)]
mod rule_tests {
    use crate::board_constants::U64Ext;
    use crate::rules::GameState;
    use crate::rules::Rule;
    use crate::rules::RuleType;

    #[test]
    fn rule_equality_test() {
        assert_eq!(
            Rule::new(RuleType::ClaimEven, 39, vec![20, 19]),
            Rule::new(RuleType::ClaimEven, 39, vec![19, 20])
        );

        assert_ne!(
            Rule::new(RuleType::BaseInverse, 48, vec![]),
            Rule::new(RuleType::Vertical, 48, vec![])
        );

        assert_ne!(
            Rule::new(RuleType::BaseInverse, 28, vec![1]),
            Rule::new(RuleType::BaseInverse, 28, vec![3])
        );

        assert_eq!(
            Rule::new(RuleType::Vertical, 88, vec![1, 2]),
            Rule::new(RuleType::Vertical, 88, vec![2, 1])
        );
    }

    #[test]
    fn claim_even_test() {
        let state = GameState::from_string("34444445");

        // there are too many rules, this is a subset
        let expected_rules = vec![
            Rule::from_strings(
                RuleType::ClaimEven,
                "(a1, a2)",
                vec!["a1-a4", "a2-a5", "a2-d2"],
            ),
            Rule::from_strings(
                RuleType::ClaimEven,
                "(c3, c4)",
                vec!["c1-c4", "c2-c5", "c3-c6", "a4-d4", "b4-e4", "c4-f4"],
            ),
            Rule::from_strings(
                RuleType::ClaimEven,
                "(f1, f2)",
                vec!["f1-f4", "f2-f5", "c2-f2", "d2-g2", "c5-f2", "d4-g1"],
            ),
        ];

        let calculated_rules: Vec<Rule> = state.claim_even().collect();

        assert_eq!(calculated_rules.len(), 16);
        for rule in &expected_rules {
            assert!(calculated_rules.contains(rule));
        }
    }

    #[test]
    fn base_inverse_test() {
        let state = GameState::from_string("354433");

        let expected_rules: Vec<Rule> = vec![
            Rule::from_strings(RuleType::BaseInverse, "(a1, b1)", vec!["a1-d1"]),
            Rule::from_strings(RuleType::BaseInverse, "(b1, d3)", vec!["b1-e4"]),
            Rule::from_strings(
                RuleType::BaseInverse,
                "(c4, d3)",
                vec!["a6-d3", "b5-e2", "c4-f1"],
            ),
            Rule::from_strings(RuleType::BaseInverse, "(c4, e2)", vec!["b5-e2", "c4-f1"]),
            Rule::from_strings(RuleType::BaseInverse, "(c4, f1)", vec!["c4-f1"]),
            Rule::from_strings(RuleType::BaseInverse, "(d3, e2)", vec!["b5-e2", "c4-f1"]),
            Rule::from_strings(RuleType::BaseInverse, "(d3, f1)", vec!["c4-f1"]),
            Rule::from_strings(RuleType::BaseInverse, "(e2, f1)", vec!["c4-f1"]),
        ];

        let calculated_rules: Vec<Rule> = state.base_inverse().collect();

        assert_eq!(calculated_rules.len(), expected_rules.len());
        for rule in &expected_rules {
            assert!(expected_rules.contains(rule));
        }
    }

    #[test]
    fn vertical_test() {
        let state = GameState::from_string("3533435453");

        let expected_rules = vec![
            Rule::from_strings(RuleType::Vertical, "(a2, a3)", vec!["a1-a4", "a2-a5"]),
            Rule::from_strings(RuleType::Vertical, "(a4, a5)", vec!["a2-a5", "a3-a6"]),
            Rule::from_strings(RuleType::Vertical, "(b2, b3)", vec!["b1-b4", "b2-b5"]),
            Rule::from_strings(RuleType::Vertical, "(b4, b5)", vec!["b2-b5", "b3-b6"]),
            Rule::from_strings(RuleType::Vertical, "(d4, d5)", vec!["d3-d6"]),
            Rule::from_strings(RuleType::Vertical, "(e4, e5)", vec!["e2-e5", "e3-e6"]),
            Rule::from_strings(RuleType::Vertical, "(f2, f3)", vec!["f1-f4", "f2-f5"]),
            Rule::from_strings(RuleType::Vertical, "(f4, f5)", vec!["f2-f5", "f3-f6"]),
            Rule::from_strings(RuleType::Vertical, "(g2, g3)", vec!["g1-g4", "g2-g5"]),
            Rule::from_strings(RuleType::Vertical, "(g4, g5)", vec!["g2-g5", "g3-g6"]),
        ];

        let calculated_rules: Vec<Rule> = state.vertical().collect();

        assert_eq!(calculated_rules.len(), expected_rules.len());
        for rule in &expected_rules {
            assert!(calculated_rules.contains(rule));
        }
    }

    #[test]
    fn after_even_test() {
        let state = GameState::from_string("444545443331313351115155");

        let calculated_rules: Vec<Rule> = state.after_even().collect();

        #[rustfmt::skip]
        let expected_rules = vec![
            Rule::from_strings(
                RuleType::AfterEven,
                "|b|",
                vec!["b1-b4", "b2-b5", "b3-b6",
                     "a4-d4", "b3-e3", "b4-e4", "b5-e5",
                     "b2-e5",
                     "b6-e3"]
            ),
            Rule::from_strings(
                RuleType::AfterEven,
                "|f|",
                vec!["f1-f4", "f2-f5", "f3-f6",
                     "c3-f3", "c4-f4", "c5-f5", "d3-g3", "d4-g4", "d5-g5",
                     "c3-f6", "d3-g6",
                     "c5-f2", "d4-g1", "d5-g2"],
            ),
            // these two act as a break even, could probably delete later
            Rule::from_strings(RuleType::AfterEven, "(b5, b6)", vec!["b3-b6", "b6-e3"]),
            Rule::from_strings(RuleType::AfterEven, "(f5, f6)", vec!["f3-f6", "c3-f6"]),
            Rule::from_strings(
                RuleType::AfterEven,
                "|f|g|",
                vec!["d3-g3", "d4-g4", "d5-g5", "d3-g6", "d5-g2"],
            ),
        ];

        assert_eq!(calculated_rules.len(), expected_rules.len());
        for rule in &expected_rules {
            assert!(calculated_rules.contains(rule));
        }
    }

    #[test]
    fn low_inverse_test() {
        let state = GameState::from_string("11222254433661133554");

        let expected_rules = vec![
            Rule::from_strings(
                RuleType::LowInverse,
                "(d4, d5, e4, e5)",
                vec!["e3-e6", "b5-e5", "c5-f5", "d5-g5"],
            ),
            Rule::from_strings(
                RuleType::LowInverse,
                "(d4, d5, f4, f5)",
                vec!["f2-f5", "f3-f6", "c5-f5", "d5-g5"],
            ),
            Rule::from_strings(
                RuleType::LowInverse,
                "(d4, d5, g4, g5)",
                vec!["g2-g5", "g3-g6", "d5-g5"],
            ),
            Rule::from_strings(
                RuleType::LowInverse,
                "(e4, e5, f4, f5)",
                vec!["e3-e6", "f2-f5", "f3-f6", "c5-f5", "d5-g5"],
            ),
            Rule::from_strings(
                RuleType::LowInverse,
                "(e4, e5, g2, g3)",
                vec!["e3-e6", "g1-g4", "g2-g5", "d6-g3"],
            ),
            Rule::from_strings(
                RuleType::LowInverse,
                "(e4, e5, g4, g5)",
                vec!["e3-e6", "g2-g5", "g3-g6", "d5-g5"],
            ),
            Rule::from_strings(
                RuleType::LowInverse,
                "(f4, f5, g4, g5)",
                vec!["f2-f5", "f3-f6", "g2-g5", "g3-g6", "d5-g5"],
            ),
        ];

        let calculated_rules: Vec<Rule> = state.low_inverse().collect();

        assert_eq!(expected_rules.len(), calculated_rules.len());
        for rule in &expected_rules {
            assert!(calculated_rules.contains(rule));
        }
    }

    #[test]
    fn high_inverse_test() {
        let state = GameState::from_string("44536756767567561134327111");
        println!("{}", state.to_string());

        let expected_rules = vec![
            Rule::from_strings(
                RuleType::HighInverse,
                "(b2, b3, b4, c4, c5, c6)",
                vec!["b2-b5", "b3-b6", "c3-c6", "a4-d4", "b4-e4"],
            ),
            Rule::from_strings(
                RuleType::HighInverse,
                "(b2, b3, b4, d4, d5, d6)",
                vec!["b2-b5", "b3-b6", "a4-d4", "b4-e4", "b3-e6"],
            ),
            Rule::from_strings(
                RuleType::HighInverse,
                "(b4, b5, b6, c4, c5, c6)",
                vec!["b3-b6", "c3-c6", "a6-d6", "b5-e5", "b6-e6"],
            ),
            Rule::from_strings(
                RuleType::HighInverse,
                "(b4, b5, b6, d4, d5, d6)",
                vec!["b3-b6", "a6-d6", "b5-e5", "b6-e6"],
            ),
            Rule::from_strings(
                RuleType::HighInverse,
                "(c4, c5, c6, d4, d5, d6)",
                vec!["c3-c6", "a6-d6", "b5-e5", "b6-e6", "c6-f6"],
            ),
        ];

        let calculated_rules: Vec<Rule> = state.high_inverse().collect();

        assert_eq!(calculated_rules.len(), expected_rules.len());
        for rule in &expected_rules {
            assert!(calculated_rules.contains(rule));
        }
    }

    #[test]
    fn base_claim_test() {
        let state = GameState::from_string("1233777777");

        let expected_rules = vec![
            Rule::from_strings(
                RuleType::BaseClaim,
                "(a2, b2, c3, c4)",
                vec!["a2-d5", "a1-d4", "b2-e5"],
            ),
            Rule::from_strings(
                RuleType::BaseClaim,
                "(a2, c3, c4, e1)",
                vec!["a2-d5", "b4-e1"],
            ),
            Rule::from_strings(
                RuleType::BaseClaim,
                "(b2, c3, c4, f1)",
                vec!["a1-d4", "b2-e5", "c4-f1"],
            ),
            Rule::from_strings(
                RuleType::BaseClaim,
                "(c3, c4, e1, f1)",
                vec!["b4-e1", "c4-f1"],
            ),
            Rule::from_strings(
                RuleType::BaseClaim,
                "(c3, d1, d2, e1)",
                vec!["a5-d2", "b4-e1", "c1-f1", "d1-g1"],
            ),
            Rule::from_strings(
                RuleType::BaseClaim,
                "(c3, d1, d2, f1)",
                vec!["a5-d2", "b4-e1", "c1-f1", "d1-g1"],
            ),
            Rule::from_strings(
                RuleType::BaseClaim,
                "(d1, d2, e1, f1)",
                vec!["b4-e1", "c1-f1", "d1-g1"],
            ),
            Rule::from_strings(
                RuleType::BaseClaim,
                "(c3, e1, e2, f1)",
                vec!["b4-e1", "c4-f1"],
            ),
            Rule::from_strings(
                RuleType::BaseClaim,
                "(d1, e1, e2, f1)",
                vec!["c4-f1", "c1-f1", "d1-g1"],
            ),
        ];

        let calculated_rules: Vec<Rule> = state.base_claim().collect();

        assert_eq!(calculated_rules.len(), expected_rules.len());
        for rule in &expected_rules {
            assert!(calculated_rules.contains(rule));
        }
    }

    #[test]
    fn before_test() {
        let state = GameState::from_string("12");

        // a subset of all calculated rules, since there are too many to check all.
        let expected_rules = vec![
            Rule::from_strings(
                RuleType::Before,
                "(a2, a3, b2, b3, c1, c2, d1, d2)",
                vec![
                    "a3-d3", "a1-a4", "a2-a5", "b2-b5", "c1-c4", "c2-c5", "a2-d2", "b2-e2",
                    "c2-f2", "c2-f5", "a4-d1", "d1-d4", "d2-d5", "d2-g2", "c1-f4", "d2-g5",
                    "a5-d2", "b4-e1",
                ],
            ),
            Rule::from_strings(
                RuleType::Before,
                "(a4, a5, b4, b5, c3, c4, d3, d4)",
                vec![
                    "a5-d5", "a2-a5", "a3-a6", "b2-b5", "b3-b6", "c1-c4", "c2-c5", "c3-c6",
                    "a4-d4", "b4-e4", "c4-f4", "a2-d5", "b3-e6", "a6-d3", "b5-e2", "c4-f1",
                    "d1-d4", "d2-d5", "d3-d6", "d4-g4", "a1-d4", "b2-e5", "c3-f6", "b6-e3",
                    "c5-f2", "d4-g1",
                ],
            ),
        ];

        let calculated_rules: Vec<Rule> = state.before().collect();

        // this number (164) may be wrong, but it's good to keep of it changing
        assert_eq!(calculated_rules.len(), 164);
        for rule in &expected_rules {
            assert!(calculated_rules.contains(rule));
        }
    }

    #[test]
    fn special_before_test() {
        let state = GameState::from_string("35333344");

        let expected_rules = vec![Rule::from_strings(
            RuleType::SpecialBefore,
            "(d3, e2, e3, f1, f2, g1, g2)",
            vec![
                "d3-g3", "c4-f1", "b5-e2", "e2-e5", "f1-f4", "f2-f5", "d4-g1", "g1-g4", "g2-g5",
                "d5-g2",
            ],
        )];

        let calculated_rules: Vec<Rule> = state.special_before().collect();

        println!("{}", calculated_rules.len());
        for rule in &calculated_rules {
            println!("{:?}", rule);
        }

        for rule in &expected_rules {
            println!("{:?}", rule);
            assert!(calculated_rules.contains(rule));
        }
    }

    #[ignore]
    #[test]
    fn special_before_fail_test() {
        let state = GameState::from_string("6754265411");

        let calculated_rules: Vec<Rule> = state.special_before().collect();
        for rule in &calculated_rules {
            println!("{:?}", rule);
        }
        assert!(false);
    }

    /*
    #[test]
    fn odd_threat_rule_test() {
        let state = GameState::from_string("333244442525755");

        println!("{}", state.to_string());

        let calculated_threats: Vec<u64> = state.odd_threats();
        let expected_threats: Vec<u64> = vec![u64::from_pretty("(a3)")];

        assert_eq!(calculated_threats.len(), expected_threats.len());
        for threat in &expected_threats {
            assert!(calculated_threats.contains(threat));
        }

        let state = GameState::from_string("3642756176227637211322113551637574556");
        println!("{}", state.to_string());

        let calculated_threats: Vec<u64> = state.odd_threats();
        assert!(calculated_threats.is_empty());

        let state = GameState::from_string("67255217565535272362732377313616611");
        println!("{}", state.to_string());

        let calculated_threats: Vec<u64> = state.odd_threats();
        assert!(calculated_threats.is_empty());

        let state = GameState::from_string("514725241775125111576567272344434");
        println!("{}", state.to_string());

        let calculated_threats: Vec<u64> = state.odd_threats();
        assert!(calculated_threats.is_empty());
    }
    */

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
