use std::fs::File;
use std::io::{BufRead, BufReader};
use std::path::Path;
use std::time::SystemTime;

use crate::board_constants::U64Ext;
use crate::eval::eval;
use crate::eval::Evaluator;
use crate::gamestate::GameState;
use crate::solver::ConspiracySolver;

type Test = (String, i32);

fn parse_line(line: String) -> Test {
    let parts = line.split_once(char::is_whitespace).unwrap();
    (String::from(parts.0), parts.1.parse::<i32>().unwrap())
}

fn read_test_set(filename: &str) -> Vec<Test> {
    let path = Path::new(filename);
    let file = match File::open(path) {
        Err(why) => panic!("Couldn't open {}: {}", path.display(), why),
        Ok(file) => file,
    };

    let reader = BufReader::new(file);
    reader.lines().map(|s| parse_line(s.unwrap())).collect()
}

pub fn eval_test(filename: &str) {
    let test_set = read_test_set(filename);
    let test_size = test_set.len();
    let now = SystemTime::now();
    let mut successfull_evaluations = 0;
    let mut evaluatable = 0;

    for (setup, expected) in test_set {
        let state = GameState::from_string(&setup);
        if expected <= 0 {
            evaluatable += 1;
        }
        let score = eval(&state);

        if score != 0 {
            if (expected <= 0 && score == -1 && (state.plies() % 2 == 0))
                || (expected < 0 && score == 1 && (state.plies() % 2 == 1))
            {
                successfull_evaluations += 1;
            } else {
                println!("{}", setup);
                println!("{}", state.to_string());
                let evaluator = Evaluator::new(&state);
                let solution = evaluator.eval_actual().unwrap();
                for (name, squares) in solution {
                    println!("{:?} {}", name, squares.to_pretty());
                }
                println!();
            }
        }
    }

    let duration = now.elapsed().unwrap();
    println!(
        "Evaluated {}% of evaluatable test cases.",
        (successfull_evaluations as f32) / (evaluatable as f32) * (100 as f32)
    );
    println!(
        "Mean time: {} micro sec",
        (duration.as_micros() as f32) / (test_size as f32)
    );
}

pub fn eval_test_two(filename: &str) {
    let test_set = read_test_set(filename);
    let test_size = test_set.len();
    let now = SystemTime::now();
    let mut successfull_evaluations = 0;
    let mut nodes = 0;

    for (setup, expected) in test_set {
        let state = GameState::from_string(&setup);
        // println!("{}", state.to_string());
        let mut node = ConspiracySolver::new(state);
        let (score, num_nodes) = node.conspiracy_eval();
        nodes += num_nodes;

        // white to play
        if state.plies() % 2 == 0
            && ((expected > 0 && score == 1) || (expected <= 0 && score == -1))
        {
            // white to play
            successfull_evaluations += 1;
        } else if state.plies() % 2 == 1
            && ((expected < 0 && score == 1) || (expected >= 0 && score == -1))
        {
            // black to play
            successfull_evaluations += 1;
        } else {
            println!("{}", setup);
            println!("{}", state.to_string());
            println!("expected score: {}", expected);
            println!("calculated score: {}", score);
            break;
        }
    }

    let duration = now.elapsed().unwrap();
    println!(
        "Evaluated {}% of evaluatable test cases.",
        (successfull_evaluations as f32) / (test_size as f32) * (100 as f32)
    );
    println!(
        "Mean time: {} micro sec",
        (duration.as_micros() as f32) / (test_size as f32)
    );
    println!(
        "Mean number of nodes: {}",
        (nodes as f32) / (test_size as f32)
    );
}
