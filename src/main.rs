pub mod bench;
pub mod board_constants;
pub mod eval;
pub mod gamestate;
pub mod rules;
pub mod solver;

use crate::bench::eval_test;
use crate::bench::eval_test_two;
use crate::eval::eval;
use crate::gamestate::GameState;
use crate::solver::ConspiracySolver;
use crate::solver::Node;
use std::env;

fn main() {
    let args: Vec<String> = env::args().collect();

    match args[1].as_str() {
        "knowledge-bench" => eval_test(&args[2]),
        "conspiracy-bench" => eval_test_two(&args[2]),
        "knowledge-eval" => {
            let state = match args[2].as_str() {
                "empty" => GameState::empty(),
                string => GameState::from_string(string),
            };
            let non_losing = eval(&state);
            println!("non-losing: {}", non_losing);
        }
        "full-eval" => {
            let state = match args[2].as_str() {
                "empty" => GameState::empty(),
                string => GameState::from_string(string),
            };
            let (score, nodes) = ConspiracySolver::new(state).conspiracy_eval();
            println!("score: {}, number of nodes: {}", score, nodes);
        }
        "show" => {
            println!("{}", GameState::from_string(&args[2]).to_string())
        }
        _ => panic!("Invalid input"),
    }
}
