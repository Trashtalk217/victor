use itertools::Itertools;
use once_cell::sync::Lazy;
use regex::Regex;
use std::ops::Range;

pub const WIDTH: u64 = 7;
pub const HEIGHT: u64 = 6;
pub const BOTTOM_MASK: u64 = bottom(WIDTH);
pub const TOP_MASK: u64 = BOTTOM_MASK << (HEIGHT - 1);
pub const COLUMN_MASK: u64 = (1 << HEIGHT) - 1;
pub const BOARD_MASK: u64 = (BOTTOM_MASK << HEIGHT) - BOTTOM_MASK;
pub const VERTICAL: u64 = 0b1111;
pub const HORIZONTAL: u64 = extend_thrice(1, HEIGHT + 1);
pub const DIAGONAL_UP: u64 = extend_thrice(1, HEIGHT + 2);
pub const DIAGONAL_DOWN: u64 = extend_thrice(1, HEIGHT);
pub const ODD_MASK: u64 = horizontal_stripes((HEIGHT - 2) as i32);
pub const EVEN_MASK: u64 = BOARD_MASK ^ ODD_MASK;

pub static GROUPS: Lazy<Vec<u64>> = Lazy::new(|| {
    let number_of_groups: u64 =
        WIDTH * (HEIGHT - 3) + (WIDTH - 3) * HEIGHT + 2 * (WIDTH - 3) * (HEIGHT - 3);
    let mut groups = Vec::with_capacity(number_of_groups as usize);

    fn directional_groups(cols: Range<u64>, rows: Range<u64>, offset: u64) -> Vec<u64> {
        cols.cartesian_product(rows)
            .map(|(col, row)| extend_thrice(bit_mask(col, row), offset))
            .collect()
    }

    groups.extend(directional_groups(0..WIDTH, 0..(HEIGHT - 3), 1));
    groups.extend(directional_groups(0..(WIDTH - 3), 0..HEIGHT, HEIGHT + 1));
    groups.extend(directional_groups(
        0..(WIDTH - 3),
        0..(HEIGHT - 3),
        HEIGHT + 2,
    ));
    groups.extend(directional_groups(0..(WIDTH - 3), 3..HEIGHT, HEIGHT));

    groups
});

pub static CLAIM_EVEN_PAIRS: Lazy<Vec<u64>> = Lazy::new(|| {
    (0..WIDTH)
        .cartesian_product((0..HEIGHT).step_by(2))
        .map(|(col, row)| bit_mask(col, row) | bit_mask(col, row + 1))
        .collect()
});

pub static VERTICAL_PAIRS: Lazy<Vec<u64>> = Lazy::new(|| {
    (0..WIDTH)
        .cartesian_product((2..HEIGHT).step_by(2))
        .map(|(col, row)| bit_mask(col, row) | bit_mask(col, row - 1))
        .collect()
});

pub static COLUMN_MASK_PAIRS: Lazy<Vec<u64>> = Lazy::new(|| {
    (0..WIDTH)
        .cartesian_product(1..4)
        .map(|(col1, offset)| (col1, col1 + offset))
        .filter(|(_, col2)| *col2 < WIDTH)
        .map(|(col1, col2)| u64::column(col1) | u64::column(col2))
        .collect()
});

pub static LOW_INVERSE_PAIRS: Lazy<Vec<u64>> = Lazy::new(|| {
    VERTICAL_PAIRS
        .clone()
        .into_iter()
        .cartesian_product(VERTICAL_PAIRS.clone().into_iter())
        .filter(|(pair1, pair2)| *pair1 > (*pair2 << 2))
        .map(|(pair1, pair2)| (pair1 | pair2))
        .filter(|squares| {
            GROUPS
                .clone()
                .into_iter()
                .map(|group| (*squares & ODD_MASK & group).count_ones() == 2)
                .fold(false, |acc, b| (acc | b))
        })
        .collect()
});

pub static HIGH_INVERSE_SQUARES: Lazy<Vec<u64>> = Lazy::new(|| {
    let vertical_triples: Vec<u64> = VERTICAL_PAIRS
        .clone()
        .into_iter()
        .map(|pair| pair.smear_up(1))
        .collect();
    vertical_triples
        .clone()
        .into_iter()
        .cartesian_product(vertical_triples.into_iter())
        .filter(|(triple1, triple2)| (*triple1 & *triple2 == 0) && (*triple1 < *triple2))
        .map(|(triple1, triple2)| triple1 | triple2)
        .filter(|squares| {
            GROUPS
                .clone()
                .into_iter()
                .map(|group| ((*squares & group).count_ones() == 2) && !group.is_vertical())
                .fold(false, |acc, b| acc || b)
        })
        .collect()
});

const fn bit_mask(col: u64, row: u64) -> u64 {
    1 << (col * (HEIGHT + 1) + row)
}

const fn bottom(width: u64) -> u64 {
    if width == 0 {
        0
    } else {
        let index = (HEIGHT + 1) * (width - 1);
        (1 << index) | bottom(width - 1)
    }
}

const fn horizontal_stripes(height: i32) -> u64 {
    if height < 0 {
        0
    } else {
        (BOTTOM_MASK << height) | horizontal_stripes(height - 2)
    }
}

const fn extend_thrice(start: u64, offset: u64) -> u64 {
    start | (start << offset) | (start << (offset * 2)) | (start << (offset * 3))
}

pub trait U64Ext {
    fn is_vertical(&self) -> bool;
    fn is_horizontal(&self) -> bool;
    fn is_up_diagonal(&self) -> bool;
    fn is_down_diagonal(&self) -> bool;
    fn in_bounds(&self) -> bool;
    fn is_group(&self) -> bool;
    fn is_subset(&self, other: &Self) -> bool;
    fn num_overlap(&self, other: &Self) -> u32;
    fn is_disjoint(&self, other: &Self) -> bool;
    fn clear_up(&self, n: u64) -> Self;
    fn smear_up(&self, n: u64) -> Self;
    fn fill_up(&self) -> Self;
    fn clear_down(&self, n: u64) -> Self;
    fn smear_down(&self, n: u64) -> Self;
    fn split(&self) -> Vec<u64>;
    fn fill_down(&self) -> Self;
    fn to_pretty(&self) -> String;
    fn from_pretty(string: &str) -> Self;
    fn column(n: u64) -> Self;
    fn row(n: u64) -> Self;
    fn bit_mask(col: u64, row: u64) -> Self;
}

fn to_alphabet(n: u64) -> String {
    let mut i = n + 1;
    let mut result = String::new();

    while i > 0 {
        result.insert(
            0,
            char::from_digit((((i - 1) % 26) + 10) as u32, 36).unwrap(),
        );
        i /= 26;
    }

    return result;
}

fn from_alphabet(string: &str) -> u64 {
    let mut string = string.to_string();
    let mut acc: u64 = 0;

    while !string.is_empty() {
        let letter = string.remove(0);
        acc += (letter.to_digit(36).unwrap() - 9) as u64;
        acc *= 26;
    }
    acc / 26 - 1
}

fn bit_index_to_string(n: u64) -> String {
    let row = n % (HEIGHT + 1);
    let column = n / (HEIGHT + 1);
    let mut result = to_alphabet(column);
    result.push_str(&(row + 1).to_string());
    result
}

impl U64Ext for u64 {
    fn is_vertical(&self) -> bool {
        (self / VERTICAL).is_power_of_two() && (self % VERTICAL == 0)
    }

    fn is_horizontal(&self) -> bool {
        (self / HORIZONTAL).is_power_of_two() && (self % HORIZONTAL == 0)
    }

    fn is_up_diagonal(&self) -> bool {
        (self / DIAGONAL_UP).is_power_of_two() && (self % DIAGONAL_UP == 0)
    }

    fn is_down_diagonal(&self) -> bool {
        (self / DIAGONAL_DOWN).is_power_of_two() && (self % DIAGONAL_DOWN == 0)
    }

    fn in_bounds(&self) -> bool {
        self & BOARD_MASK == *self
    }

    fn is_group(&self) -> bool {
        self.in_bounds()
            && (self.is_vertical()
                || self.is_horizontal()
                || self.is_up_diagonal()
                || self.is_down_diagonal())
    }

    fn is_subset(&self, other: &Self) -> bool {
        self & other == *self
    }

    fn num_overlap(&self, other: &Self) -> u32 {
        (self & other).count_ones()
    }

    fn is_disjoint(&self, other: &Self) -> bool {
        self & other == 0
    }

    fn clear_up(&self, n: u64) -> Self {
        let mut result = *self;
        for _ in 0..n {
            result &= result << 1;
        }
        result
    }

    fn smear_up(&self, n: u64) -> Self {
        let mut result = *self;
        for _ in 0..n {
            result |= (result << 1) & BOARD_MASK;
        }
        result
    }

    fn fill_up(&self) -> Self {
        self.smear_up(HEIGHT - 1)
    }

    fn clear_down(&self, n: u64) -> Self {
        let mut result = *self;
        for _ in 0..n {
            result &= result >> 1;
        }
        result
    }

    fn smear_down(&self, n: u64) -> Self {
        let mut result = *self;
        for _ in 0..n {
            result |= (result >> 1) & BOARD_MASK;
        }
        result
    }

    fn fill_down(&self) -> Self {
        self.smear_down(HEIGHT - 1)
    }

    fn split(&self) -> Vec<u64> {
        let mut running_total = 0;
        let mut r = *self;
        let mut result = vec![];
        while r > 0 {
            running_total = running_total + r.trailing_zeros();
            result.push(1 << running_total);
            r = r >> (r.trailing_zeros() + 1);
            running_total += 1;
        }
        result
    }

    fn to_pretty(&self) -> String {
        if self.is_group() {
            let mut first = bit_index_to_string(self.trailing_zeros() as u64);
            let last = bit_index_to_string(63 - self.leading_zeros() as u64);
            first.push('-');
            first.push_str(&last);
            return first;
        }
        let mut result = "(".to_string();
        for i in 0..64 {
            if (1 << i) & self > 0 {
                result.push_str(&bit_index_to_string(i));
                result.push_str(", ");
            }
        }
        result.pop();
        result.pop();
        result.push(')');
        result
    }

    fn column(n: u64) -> Self {
        COLUMN_MASK << (n * (HEIGHT + 1))
    }

    fn row(n: u64) -> Self {
        BOTTOM_MASK << n
    }

    fn bit_mask(col: u64, row: u64) -> u64 {
        bit_mask(col, row)
    }

    fn from_pretty(string: &str) -> Self {
        let group_re = Regex::new(r"^([a-z]+)(\d+)-([a-z]+)(\d+)$").unwrap();

        match group_re.captures(string) {
            Some(cap) => {
                let index1 =
                    from_alphabet(&cap[1]) * (HEIGHT + 1) + (&cap[2].parse::<u64>().unwrap() - 1);
                let index4 =
                    from_alphabet(&cap[3]) * (HEIGHT + 1) + (&cap[4].parse::<u64>().unwrap() - 1);
                let offset = (index4 - index1) / 3;
                let (index2, index3) = (index1 + offset, index4 - offset);
                return 1 << index1 | 1 << index2 | 1 << index3 | 1 << index4;
            }
            None => (),
        }

        let empty_re = Regex::new(r"^()$").unwrap();
        if empty_re.is_match(string) {
            return 0;
        }

        let squares_re = Regex::new(r"\( *[a-z]+[0-9]+( *, *[a-z]+[0-9]+)* *\)").unwrap();
        if squares_re.is_match(string) {
            let extract = Regex::new(r"([a-z]+)([0-9]+)").unwrap();
            return extract
                .captures_iter(string)
                .map(|m| {
                    1 << (from_alphabet(&m[1]) * (HEIGHT + 1) + (&m[2].parse::<u64>().unwrap() - 1))
                })
                .sum();
        }

        let columns_re = Regex::new(r"\|[a-z]+(\|[a-z]+)*\|").unwrap();
        if columns_re.is_match(string) {
            let extract = Regex::new(r"([a-z]+)").unwrap();
            return extract
                .captures_iter(string)
                .map(|m| u64::column(from_alphabet(&m[1])))
                .sum();
        }
        0
    }
}

#[cfg(test)]
mod u64_ext_tests {
    use crate::board_constants::*;

    #[test]
    fn column_test() {
        assert_eq!(u64::column(1), 0b111111 << 7);
    }

    #[test]
    fn smear_test() {
        assert_eq!(
            u64::from_pretty("(a2)").smear_down(1),
            u64::from_pretty("(a1, a2)")
        );
        assert_eq!(
            u64::from_pretty("(e2)").smear_up(2),
            u64::from_pretty("(e2, e3, e4)")
        );
        assert_eq!(
            u64::from_pretty("(b3)").fill_up(),
            u64::from_pretty("(b3, b4, b5, b6)")
        );
    }

    #[test]
    fn group_test() {
        assert!(!0b1100000110.is_vertical());
        assert!(!0b1100000110.is_group());
        assert!(!0b1100000000000000110.is_up_diagonal());
        assert!(!0b11000000000000000000011000.is_down_diagonal());
        assert!(!0b11000000000000000000011000.is_up_diagonal());
        assert!(!0b11000000000000000000011000.is_horizontal());
        assert!(!0b11000000000000000000011000.is_vertical());
        assert!(!0b11000000000000000000011000.is_group());
    }

    #[test]
    fn split_test() {
        let n = 0b00000111010011;
        let expected = vec![0b1, 0b10, 0b10000, 0b1000000, 0b10000000, 0b100000000];
        assert_eq!(n.split().len(), expected.len());
        for two_power in n.split() {
            assert!(expected.contains(&two_power));
        }
    }

    #[test]
    fn to_alphabet_test() {
        assert_eq!(to_alphabet(13), "n".to_string());
        assert_eq!(to_alphabet(27), "ab".to_string());
        assert_eq!(to_alphabet(31), "af".to_string());
    }

    #[test]
    fn from_alphabet_test() {
        assert_eq!(from_alphabet("a"), 0);
        assert_eq!(from_alphabet("aa"), 26);
        assert_eq!(from_alphabet("d"), 3);
        assert_eq!(from_alphabet("ad"), 29);
    }

    #[test]
    fn to_pretty_test() {
        assert_eq!(0b1111.to_pretty(), "a1-a4".to_string());
        assert_eq!(0b1000000100000010000001.to_pretty(), "a1-d1".to_string());
        assert_eq!(0b1000000010000000100000001.to_pretty(), "a1-d4".to_string());
        assert_eq!(
            (0b1000001000001000001 << 3).to_pretty(),
            "a4-d1".to_string()
        );
        assert_eq!(0b11.to_pretty(), "(a1, a2)".to_string());
        assert_eq!(0b1100000110.to_pretty(), "(a2, a3, b2, b3)");
    }

    #[test]
    fn from_pretty_test() {
        assert_eq!(u64::from_pretty("a1-a4"), 0b1111);
        assert_eq!(u64::from_pretty("c4-f1"), 0b1000001000001000001 << 17);
        assert_eq!(u64::from_pretty("()"), 0);
        assert_eq!(u64::from_pretty("(a1, a2)"), 0b11);
        assert_eq!(
            u64::from_pretty("(d2, e3, g6)"),
            1 << 22 | 1 << 30 | 1 << 47
        );
        assert_eq!(u64::from_pretty("(c3)"), 1 << 16);
        assert_eq!(u64::from_pretty("|a|"), 0b111111);
        assert_eq!(u64::from_pretty("|a|d|"), 0b111111 | (0b111111 << 21));
    }
}

#[cfg(test)]
mod constant_tests {
    use crate::board_constants::*;

    #[test]
    fn bottom_mask_test() {
        assert_eq!(
            BOTTOM_MASK,
            u64::from_pretty("(a1, b1, c1, d1, e1, f1, g1)")
        );
    }

    #[test]
    fn board_mask_test() {
        #[rustfmt::skip]
        let board = u64::from_pretty(
            "(a1, a2, a3, a4, a5, a6, b1, b2, b3, b4, b5, b6, c1, c2, c3, c4, \
             c5, c6, d1, d2, d3, d4, d5, d6, e1, e2, e3, e4, e5, e6, f1, f2, \
             f3, f4, f5, f6, g1, g2, g3, g4, g5, g6)",
        );

        assert!(BOARD_MASK == board);
    }

    #[test]
    fn odd_mask_test() {
        #[rustfmt::skip]
        let odd = u64::from_pretty(
            "(a1, a3, a5, b1, b3, b5, c1, c3, c5, d1,d3, d5, e1, e3, e5, \
             f1, f3, f5, g1, g3, g5)"
        );

        assert_eq!(ODD_MASK, odd);
    }

    #[test]
    fn even_mask_test() {
        let even = u64::from_pretty(
            "(a2, a4, a6, b2, b4, b6, c2, c4, c6, d2, d4, d6, e2, e4, e6, \
             f2, f4, f6, g2, g4, g6)",
        );

        assert!(EVEN_MASK == even);
    }

    #[test]
    fn groups_test() {
        #[rustfmt::skip]
        let mut expected_groups: Vec<u64> = vec![
            "a1-a4", "a2-a5", "a3-a6", "b1-b4", "b2-b5", "b3-b6", "c1-c4", "c2-c5",
            "c3-c6", "d1-d4", "d2-d5", "d3-d6", "e1-e4", "e2-e5", "e3-e6", "f1-f4",
            "f2-f5", "f3-f6", "g1-g4", "g2-g5", "g3-g6",
            "a1-d1", "a2-d2", "a3-d3", "a4-d4", "a5-d5", "a6-d6", "b1-e1", "b2-e2",
            "b3-e3", "b4-e4", "b5-e5", "b6-e6", "c1-f1", "c2-f2", "c3-f3", "c4-f4",
            "c5-f5", "c6-f6", "d1-g1", "d2-g2", "d3-g3", "d4-g4", "d5-g5", "d6-g6",
            "a1-d4", "a2-d5", "a3-d6", "b1-e4", "b2-e5", "b3-e6", "c1-f4", "c2-f5",
            "c3-f6", "d1-g4", "d2-g5", "d3-g6",
            "a4-d1", "a5-d2", "a6-d3", "b4-e1", "b5-e2", "b6-e3", "c4-f1", "c5-f2",
            "c6-f3", "d4-g1", "d5-g2", "d6-g3",
        ].into_iter().map(|string| u64::from_pretty(string)).collect();

        let mut calculated_groups = GROUPS.clone();

        calculated_groups.sort();
        expected_groups.sort();

        assert_eq!(calculated_groups, expected_groups);
    }

    #[test]
    fn claim_even_pairs_test() {
        #[rustfmt::skip]
        let mut expected_pairs: Vec<u64> = vec![
            "(a1, a2)", "(a3, a4)", "(a5, a6)", "(b1, b2)", "(b3, b4)", "(b5, b6)",
            "(c1, c2)", "(c3, c4)", "(c5, c6)", "(d1, d2)", "(d3, d4)", "(d5, d6)",
            "(e1, e2)", "(e3, e4)", "(e5, e6)", "(f1, f2)", "(f3, f4)", "(f5, f6)",
            "(g1, g2)", "(g3, g4)", "(g5, g6)"
        ].into_iter().map(|string| u64::from_pretty(string)).collect();

        let mut calculated_pairs = CLAIM_EVEN_PAIRS.clone();

        expected_pairs.sort();
        calculated_pairs.sort();

        assert_eq!(expected_pairs, calculated_pairs);
    }

    #[test]
    fn vertical_pairs_test() {
        #[rustfmt::skip]
        let mut expected_pairs: Vec<u64> = vec![
            "(a2, a3)", "(a4, a5)", "(b2, b3)", "(b4, b5)", "(c2, c3)", "(c4, c5)",
            "(d2, d3)", "(d4, d5)", "(e2, e3)", "(e4, e5)", "(f2, f3)", "(f4, f5)",
            "(g2, g3)", "(g4, g5)"
        ].into_iter().map(|string| u64::from_pretty(string)).collect();

        let mut calculated_pairs = VERTICAL_PAIRS.clone();

        expected_pairs.sort();
        calculated_pairs.sort();

        assert_eq!(expected_pairs, calculated_pairs);
    }

    #[test]
    fn column_mask_pair_test() {
        #[rustfmt::skip]
        let mut expected_pairs: Vec<u64> = vec![
            "|a|b|", "|a|c|", "|a|d|", "|b|c|", "|b|d|", "|b|e|", "|c|d|", "|c|e|",
            "|c|f|", "|d|e|", "|d|f|", "|d|g|", "|e|f|", "|e|g|", "|f|g|"
        ].into_iter().map(|string| u64::from_pretty(string)).collect();

        let mut calculated_pairs = COLUMN_MASK_PAIRS.clone();

        expected_pairs.sort();
        calculated_pairs.sort();

        assert_eq!(expected_pairs, calculated_pairs);
    }

    #[test]
    fn low_inverse_squares_test() {
        #[rustfmt::skip]
        let mut expected_pairs: Vec<u64> = vec![
            "(a2, a3, b2, b3)", "(a2, a3, c2, c3)", "(a2, a3, c4, c5)", "(a2, a3, d2, d3)",
            "(a4, a5, b4, b5)", "(a4, a5, c2, c3)", "(a4, a5, c4, c5)", "(a4, a5, d4, d5)",
            "(b2, b3, c2, c3)", "(b2, b3, d2, d3)", "(b2, b3, d4, d5)", "(b2, b3, e2, e3)",
            "(b4, b5, c4, c5)", "(b4, b5, d2, d3)", "(b4, b5, d4, d5)", "(b4, b5, e4, e5)",
            "(c2, c3, d2, d3)", "(c2, c3, e2, e3)", "(c2, c3, e4, e5)", "(c2, c3, f2, f3)",
            "(c4, c5, d4, d5)", "(c4, c5, e2, e3)", "(c4, c5, e4, e5)", "(c4, c5, f4, f5)",
            "(d2, d3, e2, e3)", "(d2, d3, f2, f3)", "(d2, d3, f4, f5)", "(d2, d3, g2, g3)",
            "(d4, d5, e4, e5)", "(d4, d5, f2, f3)", "(d4, d5, f4, f5)", "(d4, d5, g4, g5)",
            "(e2, e3, f2, f3)", "(e2, e3, g2, g3)", "(e2, e3, g4, g5)",
            "(e4, e5, f4, f5)", "(e4, e5, g2, g3)", "(e4, e5, g4, g5)",
            "(f2, f3, g2, g3)",
            "(f4, f5, g4, g5)",
        ].into_iter().map(|string| u64::from_pretty(string)).collect();

        let mut calculated_pairs = LOW_INVERSE_PAIRS.clone();

        expected_pairs.sort();
        calculated_pairs.sort();

        assert_eq!(calculated_pairs, expected_pairs);
    }

    #[test]
    fn high_inverse_squares_test() {
        #[rustfmt::skip]
        let mut expected_squares: Vec<u64> = vec![
            "(a2, a3, a4, b2, b3, b4)", "(a2, a3, a4, b4, b5, b6)",
            "(a2, a3, a4, c2, c3, c4)", "(a2, a3, a4, c4, c5, c6)",
            "(a2, a3, a4, d2, d3, d4)", "(a2, a3, a4, d4, d5, d6)",
            "(a4, a5, a6, b2, b3, b4)", "(a4, a5, a6, b4, b5, b6)",
            "(a4, a5, a6, c2, c3, c4)", "(a4, a5, a6, c4, c5, c6)",
            "(a4, a5, a6, d2, d3, d4)", "(a4, a5, a6, d4, d5, d6)",
            "(b2, b3, b4, c2, c3, c4)", "(b2, b3, b4, c4, c5, c6)",
            "(b2, b3, b4, d2, d3, d4)", "(b2, b3, b4, d4, d5, d6)",
            "(b2, b3, b4, e2, e3, e4)", "(b2, b3, b4, e4, e5, e6)",
            "(b4, b5, b6, c2, c3, c4)", "(b4, b5, b6, c4, c5, c6)",
            "(b4, b5, b6, d2, d3, d4)", "(b4, b5, b6, d4, d5, d6)",
            "(b4, b5, b6, e2, e3, e4)", "(b4, b5, b6, e4, e5, e6)",
            "(c2, c3, c4, d2, d3, d4)", "(c2, c3, c4, d4, d5, d6)",
            "(c2, c3, c4, e2, e3, e4)", "(c2, c3, c4, e4, e5, e6)",
            "(c2, c3, c4, f2, f3, f4)", "(c2, c3, c4, f4, f5, f6)",
            "(c4, c5, c6, d2, d3, d4)", "(c4, c5, c6, d4, d5, d6)",
            "(c4, c5, c6, e2, e3, e4)", "(c4, c5, c6, e4, e5, e6)",
            "(c4, c5, c6, f2, f3, f4)", "(c4, c5, c6, f4, f5, f6)",
            "(d2, d3, d4, e2, e3, e4)", "(d2, d3, d4, e4, e5, e6)",
            "(d2, d3, d4, f2, f3, f4)", "(d2, d3, d4, f4, f5, f6)",
            "(d2, d3, d4, g2, g3, g4)", "(d2, d3, d4, g4, g5, g6)",
            "(d4, d5, d6, e2, e3, e4)", "(d4, d5, d6, e4, e5, e6)",
            "(d4, d5, d6, f2, f3, f4)", "(d4, d5, d6, f4, f5, f6)",
            "(d4, d5, d6, g2, g3, g4)", "(d4, d5, d6, g4, g5, g6)",
            "(e2, e3, e4, f2, f3, f4)", "(e2, e3, e4, f4, f5, f6)",
            "(e2, e3, e4, g2, g3, g4)", "(e2, e3, e4, g4, g5, g6)",
            "(e4, e5, e6, f2, f3, f4)", "(e4, e5, e6, f4, f5, f6)",
            "(e4, e5, e6, g2, g3, g4)", "(e4, e5, e6, g4, g5, g6)",
            "(f2, f3, f4, g2, g3, g4)", "(f2, f3, f4, g4, g5, g6)",
            "(f4, f5, f6, g2, g3, g4)", "(f4, f5, f6, g4, g5, g6)",         
        ].into_iter().map(|string| u64::from_pretty(string)).collect();

        let mut calculated_squares = HIGH_INVERSE_SQUARES.clone();
        println!("3");
        calculated_squares.sort();
        expected_squares.sort();

        assert_eq!(calculated_squares, expected_squares);
    }
}
