use crate::board_constants::U64Ext;
use itertools::Itertools;
use std::sync::Arc;

pub type GroupPredicate = Arc<dyn Fn(&u64) -> bool>;

// checks if the group goes through a pair of squares above two given squares in different collumns
pub fn through_pairs_above(square1: u64, square2: u64) -> GroupPredicate {
    let pairs = (square1 << 1)
        .fill_up()
        .split()
        .into_iter()
        .cartesian_product((square2 << 1).fill_up().split().into_iter())
        .map(|(x, y)| x | y);

    // why do I need a clone here
    Arc::new(move |group| pairs.clone().any(|pair| pair.is_subset(group)))
}

// checks if the group goes through all the given squares
pub fn through(squares: u64) -> GroupPredicate {
    Arc::new(move |group| squares.is_subset(group))
}

// checks if the group goes through any of the given squares
pub fn hits(squares: u64) -> GroupPredicate {
    Arc::new(move |group| squares & group > 0)
}

// checks if the group goes through one of the vertical pairs of squares between two squares
// it assumes that square1 and square2 are in the same column, with square1 lower then square2
pub fn through_vertical_pairs_between(square1: u64, square2: u64) -> GroupPredicate {
    let in_between = square1.fill_up() & square2.fill_up();
    let pairs = in_between
        .clear_down(1)
        .split()
        .into_iter()
        .map(|square| square.smear_up(1));

    Arc::new(move |group| pairs.clone().any(|pair| pair.is_subset(group)))
}

// if b == true, return p, otherwise return a predicate that rejects all groups
// this is needed, because some solves only happen on certain conditions unrelated to the group
pub fn optional(b: bool, p: GroupPredicate) -> GroupPredicate {
    if b {
        p
    } else {
        Arc::new(|_| false)
    }
}

// I don't know how macro_rules! works, change it later
pub fn or2(p1: GroupPredicate, p2: GroupPredicate) -> GroupPredicate {
    Arc::new(move |group| p1(group) || p2(group))
}

pub fn or3(p1: GroupPredicate, p2: GroupPredicate, p3: GroupPredicate) -> GroupPredicate {
    Arc::new(move |group| p1(group) || p2(group) || p3(group))
}

pub fn or4(
    p1: GroupPredicate,
    p2: GroupPredicate,
    p3: GroupPredicate,
    p4: GroupPredicate,
) -> GroupPredicate {
    Arc::new(move |group| p1(group) || p2(group) || p3(group) || p4(group))
}

pub fn or5(
    p1: GroupPredicate,
    p2: GroupPredicate,
    p3: GroupPredicate,
    p4: GroupPredicate,
    p5: GroupPredicate,
) -> GroupPredicate {
    Arc::new(move |group| p1(group) || p2(group) || p3(group) || p4(group) || p5(group))
}
