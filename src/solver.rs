use crate::eval::eval;
use crate::gamestate::GameState;
use petgraph::graph::Graph;
use petgraph::graph::NodeIndex;
use petgraph::Directed;
use petgraph::EdgeDirection::{Incoming, Outgoing};
use std::cmp::Ordering;
use std::collections::HashMap;
use std::ops::{Add, Sub};

// not sure about the partialOrd, but should work
#[derive(PartialEq, Eq, PartialOrd, Debug, Copy, Clone)]
enum ConspiracyNumber {
    Num(u64),
    Inf,
}

impl Ord for ConspiracyNumber {
    fn cmp(&self, other: &Self) -> Ordering {
        match (self, other) {
            (ConspiracyNumber::Num(n), ConspiracyNumber::Num(m)) => n.cmp(&m),
            (ConspiracyNumber::Inf, ConspiracyNumber::Num(_)) => Ordering::Greater,
            (ConspiracyNumber::Num(_), ConspiracyNumber::Inf) => Ordering::Less,
            (ConspiracyNumber::Inf, ConspiracyNumber::Inf) => Ordering::Equal,
        }
    }
}

impl Add for ConspiracyNumber {
    type Output = Self;

    fn add(self, other: Self) -> Self {
        match (self, other) {
            (ConspiracyNumber::Num(n), ConspiracyNumber::Num(m)) => Self::Num(n + m),
            _ => Self::Inf,
        }
    }
}

impl Sub for ConspiracyNumber {
    type Output = Self;

    fn sub(self, other: Self) -> Self::Output {
        match (self, other) {
            (ConspiracyNumber::Num(n), ConspiracyNumber::Num(m)) => Self::Num(n + m),
            (ConspiracyNumber::Inf, ConspiracyNumber::Num(_)) => Self::Inf,
            _ => panic!("Tried to subtract infinity"),
        }
    }
}

#[derive(Clone, Debug)]
pub struct Node {
    state: GameState,
    white_conspiracy_num: ConspiracyNumber, // conspiracy(1)
    black_conspiracy_num: ConspiracyNumber, // conspiracy(-1)
}

impl ToString for Node {
    fn to_string(&self) -> String {
        format!(
            "{}\nwhite conspiracy num: {:?}\nblack conspiracy num: {:?}",
            self.state.to_string(),
            self.white_conspiracy_num,
            self.black_conspiracy_num
        )
    }
}

impl Node {
    pub fn new(state: GameState) -> Node {
        let white_conspiracy_num;
        let black_conspiracy_num;

        if state.plies() % 2 == 0 {
            black_conspiracy_num = ConspiracyNumber::Num(state.num_children());
            white_conspiracy_num = ConspiracyNumber::Num(1);
        } else {
            black_conspiracy_num = ConspiracyNumber::Num(1);
            white_conspiracy_num = ConspiracyNumber::Num(state.num_children());
        }

        Node {
            state,
            white_conspiracy_num,
            black_conspiracy_num,
        }
    }

    // black, white
    fn base_conspiracy_number(&self) -> (u64, u64) {
        if self.state.plies() % 2 == 0 {
            (self.state.num_children(), 1)
        } else {
            (1, self.state.num_children())
        }
    }

    fn knowledge_eval(&mut self) {
        match eval(&self.state) {
            -1 => {
                self.black_conspiracy_num = ConspiracyNumber::Num(0);
                self.white_conspiracy_num = ConspiracyNumber::Inf;
            }
            1 => {
                self.black_conspiracy_num = ConspiracyNumber::Inf;
                self.white_conspiracy_num = ConspiracyNumber::Num(0);
            }
            _ => {}
        }
    }
}

struct TranspositionTable {
    size: usize,
    keys: Vec<u64>,
    values: Vec<Option<NodeIndex>>,
}

impl TranspositionTable {
    fn index(&self, key: u64) -> usize {
        (key as usize) & self.size
    }

    fn lookup(&self, key: u64) -> Option<NodeIndex> {
        let index = self.index(key);
        if self.keys[index] == key && key != 0 {
            return Some(self.values[index].unwrap());
        } else {
            return None;
        }
    }

    pub fn new(size: usize) -> TranspositionTable {
        TranspositionTable {
            size,
            keys: vec![0; size],
            values: vec![None; size],
        }
    }

    pub fn put(&mut self, key: u64, val: NodeIndex) {
        let index = self.index(key);
        self.keys[index] = key;
        self.values[index] = Some(val);
    }
}

pub struct ConspiracySolver {
    num_nodes: u128,
    root: NodeIndex,
    table: HashMap<u64, NodeIndex>,
    tree: Graph<Node, (), Directed>,
}

impl ConspiracySolver {
    pub fn new(state: GameState) -> ConspiracySolver {
        let node = Node::new(state);
        let table = HashMap::new();
        let mut tree: Graph<Node, (), Directed> = Graph::new();
        let root = tree.add_node(node);
        ConspiracySolver {
            num_nodes: 1,
            root,
            table,
            tree,
        }
    }

    pub fn conspiracy_eval(&mut self) -> (i32, u128) {
        let mut root_node = self.node(self.root).clone();
        root_node.knowledge_eval();
        if root_node.black_conspiracy_num == ConspiracyNumber::Num(0) {
            return (-1, 1);
        }
        if root_node.white_conspiracy_num == ConspiracyNumber::Num(0) {
            return (1, 1);
        }

        self.expand(self.root);
        root_node = self.node(self.root).clone();
        while root_node.black_conspiracy_num > ConspiracyNumber::Num(0)
            && root_node.white_conspiracy_num > ConspiracyNumber::Num(0)
        {
            if root_node.white_conspiracy_num < root_node.black_conspiracy_num {
                self.decrease_black();
            } else {
                self.decrease_white();
            }
            root_node = self.node(self.root).clone();
        }

        // steps:
        // choose a strategy
        // traverse the tree down from the root with that strategy
        // when a leaf node is reached, expand this node
        // if the new nodes already are in the tree, just add an edge and do a thing
        // otherwise create new nodes
        // update conspiracy numbers of the expanded node / score
        // propagate upwards
        // repeat

        let node = &self.tree[self.root];
        if node.black_conspiracy_num == ConspiracyNumber::Num(0) {
            return (-1, self.num_nodes);
        } else if node.white_conspiracy_num == ConspiracyNumber::Num(0) {
            return (1, self.num_nodes);
        } else {
            return (0, self.num_nodes);
        }
    }

    // make use of the already existing graph structure to find transpositions
    // not very fast, but it doesn't require extra memory

    // in it's current state this is significantly slower then just using
    // the built-in find on the node vector :(
    /*
    fn find_state(&self, state: GameState) -> Option<NodeIndex> {
        let mut queue: VecDeque<NodeIndex> = VecDeque::new();
        queue.push_back(self.root);
        while queue.len() > 0 {
            let node_index = queue.pop_front().unwrap();
            let check_state = self.tree[node_index].state;
            if state.key() == check_state.key() {
                return Some(node_index);
            } else if (state.is_successor(&check_state)) {
                let mut children: VecDeque<NodeIndex> =
                    self.tree.neighbors_directed(node_index, Outgoing).collect();
                queue.append(&mut children);
            }
        }
        return None; // 703 nodes (mean average)
    }
    */

    fn expand(&mut self, expand_index: NodeIndex) {
        let node = self.node(expand_index).clone();

        let sons: Vec<GameState> = node
            .state
            .valid_moves()
            .into_iter()
            .map(|i| node.state.play_column(i))
            .collect();

        // while exiting out early, may be helpfull, for testing purposes it's best to leave it be
        for son in sons {
            // first find out if the node exists in the tree
            // this is decently fast, but takes up memory,
            // the paper doesn't directly propose a way of making this fast
            let index = self.table.get(&son.key());

            match index {
                Some(i) => {
                    self.tree.add_edge(expand_index, *i, ());
                }
                None => {
                    let mut node1 = Node::new(son);
                    node1.knowledge_eval();
                    let node2 = node1.clone();

                    let index = self.tree.add_node(node2);
                    self.table.insert(son.key(), index);
                    self.num_nodes += 1;
                    self.tree.add_edge(expand_index, index, ());
                }
            }
        }
        self.update_node_from_children(expand_index);
    }

    fn update_node_from_children(&mut self, index: NodeIndex) {
        let children: Vec<(NodeIndex, Node)> = self
            .tree
            .neighbors_directed(index, Outgoing)
            .map(|i| (i, self.tree[i].clone()))
            .collect();
        let mut black_sorted: Vec<(NodeIndex, Node)> = children.clone();
        black_sorted
            .sort_by(|(_, n1), (_, n2)| n1.black_conspiracy_num.cmp(&n2.black_conspiracy_num));
        let (black_conspiracy_num, white_conspiracy_num) =
            self.tree[index].base_conspiracy_number();
        let candidate_black_num = black_sorted
            .iter()
            .take(black_conspiracy_num as usize)
            .map(|(_, n)| n.black_conspiracy_num)
            .fold(ConspiracyNumber::Num(0), |r, x| r + x);
        let mut white_sorted: Vec<(NodeIndex, Node)> = children.clone();
        white_sorted
            .sort_by(|(_, n1), (_, n2)| n1.white_conspiracy_num.cmp(&n2.white_conspiracy_num));
        let candidate_white_num = white_sorted
            .iter()
            .take(white_conspiracy_num as usize)
            .map(|(_, n)| n.white_conspiracy_num)
            .fold(ConspiracyNumber::Num(0), |r, x| r + x);

        let node = self.node(index);
        node.black_conspiracy_num = candidate_black_num;
        node.white_conspiracy_num = candidate_white_num;
    }

    fn propagate_up(&mut self, expand_index: NodeIndex) {
        let mut stack: Vec<NodeIndex> = self
            .tree
            .neighbors_directed(expand_index, Incoming)
            .collect();

        // propagate upwards
        while stack.len() > 0 {
            let top = stack.pop().unwrap();
            let node = self.tree[top].clone();
            self.update_node_from_children(top);
            let changed_node = self.tree[top].clone();
            // if anything changes, we need to continu up the tree, otherwise don't bother
            if node.black_conspiracy_num != changed_node.black_conspiracy_num
                || node.white_conspiracy_num != changed_node.white_conspiracy_num
            {
                let parents: Vec<NodeIndex> = self.tree.neighbors_directed(top, Incoming).collect();
                stack.append(&mut parents.clone());
            }
        }
    }

    fn traverse_down<F>(&self, mut cmp_node: F) -> NodeIndex
    where
        F: FnMut(&Node, &Node) -> Ordering,
    {
        // traverse the tree down from the root
        let mut current = self.root;
        let mut children: Vec<NodeIndex> =
            self.tree.neighbors_directed(current, Outgoing).collect();
        while children.len() != 0 {
            let pairs: Vec<(NodeIndex, Node)> = children
                .into_iter()
                .map(|i| (i, self.tree[i].clone()))
                .collect();
            current = pairs
                .into_iter()
                .filter(|(_, n)| {
                    n.black_conspiracy_num > ConspiracyNumber::Num(0)
                        && n.white_conspiracy_num > ConspiracyNumber::Num(0)
                })
                .min_by(|(_, n1), (_, n2)| cmp_node(n1, n2))
                .unwrap()
                .0;
            children = self.tree.neighbors_directed(current, Outgoing).collect();
        }

        current
    }

    fn decrease_black(&mut self) {
        // traverse the tree down from the root
        let current =
            self.traverse_down(|n1, n2| n1.black_conspiracy_num.cmp(&n2.black_conspiracy_num));

        // make it immutable
        let current = current.clone();
        // we've reached a leaf node with a zero score
        self.expand(current);

        // I'm reasonably sure that it can't be both at the same time, but time will tell
        let n = self.node(current);
        if n.black_conspiracy_num == ConspiracyNumber::Num(0) {
            n.white_conspiracy_num = ConspiracyNumber::Inf;
        } else if n.white_conspiracy_num == ConspiracyNumber::Num(0) {
            n.black_conspiracy_num = ConspiracyNumber::Inf;
        }

        self.propagate_up(current);
    }

    fn decrease_white(&mut self) {
        let current =
            self.traverse_down(|n1, n2| n1.white_conspiracy_num.cmp(&n2.white_conspiracy_num));

        // make it immutable
        let current = current.clone();
        // we've reached a leaf node with a zero score
        self.expand(current);

        // I'm reasonably sure that it can't be both at the same time, but time will tell
        let n = self.node(current);
        if n.black_conspiracy_num == ConspiracyNumber::Num(0) {
            n.white_conspiracy_num = ConspiracyNumber::Inf;
        } else if n.white_conspiracy_num == ConspiracyNumber::Num(0) {
            n.black_conspiracy_num = ConspiracyNumber::Inf;
        }

        self.propagate_up(current);
    }

    fn node(&mut self, index: NodeIndex) -> &mut Node {
        &mut self.tree[index] // &Node
    }
}

#[cfg(test)]
mod conspiracy_tests {
    use crate::gamestate::GameState;
    use crate::solver::ConspiracySolver;

    #[test]
    fn easy_test() {
        let state = GameState::from_string("2252576253462244111563365343671351441");
        println!("{}", state.to_string());
        let expected = 1; // white wins
        let (calculated, _) = ConspiracySolver::new(state).conspiracy_eval();
        assert_eq!(expected, calculated);

        let state = GameState::from_string("7422341735647741166133573473242566");
        println!("{}", state.to_string());
        //panic!();
    }

    #[test]
    fn easy_test_two() {
        let state = GameState::from_string("71255763773133525731261364622167124446454");
        println!("{}", state.to_string());
        let expected = -1;
        let (calculated, _) = ConspiracySolver::new(state).conspiracy_eval();
        assert_eq!(calculated, expected);
    }

    /*
    these take forever for some reason...

    ..●....
    ○.●....
    ○.●....
    ○○○...●
    ●●○...○
    ●●○●..○
    White to play

    .......
    ....○..
    ....○..
    ●●.●●○.
    ○●.○●○○
    ●○●○●●○
    White to play

    .......
    ....●..
    ●...●..
    ○○..○.●
    ○●●○●○○
    ●○●○○●●
    Black to play

    // thing

    ●○○●.○○
    ○●●●○●○
    ●○○●●●○
    ○●●○●●●
    ○○●●●○○
    ○●○○○●●

     */
}
