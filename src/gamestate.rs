use crate::board_constants::U64Ext;
use crate::board_constants::BOARD_MASK;
use crate::board_constants::BOTTOM_MASK;
use crate::board_constants::GROUPS;
use crate::board_constants::HEIGHT;
use crate::board_constants::WIDTH;
use std::cmp::min;

#[derive(Copy, Clone, Debug)]
pub struct GameState {
    pub mask: u64,
    pub position: u64,
    pub plies: i32,
}

impl GameState {
    pub fn empty() -> GameState {
        GameState {
            mask: 0,
            position: 0,
            plies: 0,
        }
    }

    pub fn from_string(string: &str) -> GameState {
        let mut state = GameState::empty();

        for letter in string.chars() {
            let number: u64 = match letter.to_digit(10) {
                Some(d) => (d as u64),
                None => panic!("Character {} is not a valid digit.", letter),
            };
            state = state.play_column(number - 1); // we assume that the move is valid.
        }

        state
    }

    pub fn potential_threats(&self) -> Vec<u64> {
        // gives back the groups the current player can still make
        let opponent_mask = self.position ^ self.mask;
        GROUPS
            .clone()
            .into_iter()
            .filter(|group| *group & opponent_mask == 0)
            .collect()
    }

    fn compute_winning_position(position: u64, mask: u64) -> u64 {
        // vertical
        let mut r = (position << 1) & (position << 2) & (position << 3);

        // horizontal
        let p = (position << 7) & (position << 14);
        r |= p & (position << 21);
        r |= p & (position >> 7);
        let p = (position >> 7) & (position >> 14);
        r |= p & (position << 7);
        r |= p & (position >> 21);

        // diagonal 1
        let p = (position << 6) & (position << 12);
        r |= p & (position << 18);
        r |= p & (position >> 6);
        let p = (position >> 6) & (position >> 12);
        r |= p & (position << 6);
        r |= p & (position >> 18);

        // diagonal 2
        let p = (position << 8) & (position << 16);
        r |= p & (position << 24);
        r |= p & (position >> 8);
        let p = (position >> 8) & (position >> 16);
        r |= p & (position << 8);
        r |= p & (position >> 24);

        r & (BOARD_MASK ^ mask)
    }

    fn winning_position(&self) -> u64 {
        GameState::compute_winning_position(self.position, self.mask)
    }

    fn opponent_winning_position(&self) -> u64 {
        GameState::compute_winning_position(self.position ^ self.mask, self.mask)
    }

    fn possible(&self) -> u64 {
        (self.mask + BOTTOM_MASK) & BOARD_MASK
    }

    pub fn num_children(&self) -> u64 {
        self.possible().count_ones() as u64
    }

    fn can_play(&self, col: u64) -> bool {
        self.mask & u64::bit_mask(col, HEIGHT - 1) == 0
    }

    pub fn can_win_next(&self) -> bool {
        self.winning_position() & self.possible() > 0
    }

    pub fn possible_non_losing_moves(&self) -> u64 {
        let mut possible_mask = self.possible();
        let opponent_win = self.opponent_winning_position();
        let forced_moves = possible_mask & opponent_win;
        if forced_moves > 0 {
            if (forced_moves & (forced_moves - 1)) > 0 {
                return 0;
            } else {
                possible_mask = forced_moves;
            }
        }
        return possible_mask & !(opponent_win >> 1);
    }

    pub fn valid_moves(&self) -> Vec<u64> {
        let mut moves: Vec<u64> = Vec::new();
        for col in 0..7 {
            if self.can_play(col) {
                moves.push(col as u64);
            }
        }
        moves
    }

    pub fn key(&self) -> u64 {
        self.position + self.mask
    }

    pub fn square_is_playable(&self, square: u64) -> bool {
        square.is_subset(&((self.mask + BOTTOM_MASK) & BOARD_MASK))
    }

    // specific to a 7x6 board
    pub fn flip_key(key: u64) -> u64 {
        // turn
        // 000000000000000gggggggfffffffeeeeeeedddddddcccccccbbbbbbbaaaaaaa
        // into
        // 000000000000000aaaaaaabbbbbbbcccccccdddddddeeeeeeefffffffggggggg

        fn swap_part(zyx: u64) -> u64 {
            let x = (zyx & 0b1111111) << 14;
            let y = zyx & 0b11111110000000;
            let z = zyx >> 14;
            let xyz = x | y | z;
            return xyz;
        }

        let gfe = key >> 28;
        let efg = swap_part(gfe);

        //                   dddddddxxxxxxxyyyyyyyzzzzzzz
        let d = key & 0b1111111000000000000000000000;

        let cba = key & 0b111111111111111111111;
        let abc = swap_part(cba); // still aligned to the right

        let flipped_key = (abc << 28) | d | efg;
        return flipped_key;
    }

    pub fn key2(&self) -> u64 {
        let key1 = self.key();
        let key2 = GameState::flip_key(key1);
        return min(key1, key2);
    }

    pub fn move_score(&self, m: u64) -> u64 {
        GameState::compute_winning_position(self.position | m, self.mask)
            .count_ones()
            .into()
    }

    pub fn play_square(&self, square: u64) -> GameState {
        GameState {
            position: self.position ^ self.mask,
            mask: self.mask | square,
            plies: self.plies + 1,
        }
    }

    pub fn opponent_threats(&self) -> Vec<u64> {
        GROUPS
            .clone()
            .into_iter()
            .filter(|group| *group & self.position == 0)
            .collect()
    }

    pub fn play_column(&self, col: u64) -> GameState {
        GameState {
            position: self.position ^ self.mask,
            mask: self.mask | (self.mask + u64::bit_mask(col, 0)),
            plies: self.plies + 1,
        }
    }

    pub fn is_successor(&self, other: &Self) -> bool {
        if (other.plies + self.plies) % 2 == 0 {
            other.mask.is_subset(&self.mask) && other.position.is_subset(&self.position)
        } else {
            other.mask.is_subset(&self.mask)
                && other.position.is_subset(&(self.position ^ self.mask))
        }
    }
}

impl ToString for GameState {
    fn to_string(&self) -> String {
        let mut result = String::with_capacity((HEIGHT * (WIDTH + 1) + 13) as usize);

        let (current, other) = match self.plies % 2 {
            0 => ('●', '○'),
            _ => ('○', '●'),
        };

        for row in (0..HEIGHT).rev() {
            for col in 0..WIDTH {
                let index = row + (col * (HEIGHT + 1));
                let single_bit_mask = 1 << index;

                if (self.mask & single_bit_mask) == 0 {
                    result.push('.');
                } else {
                    if (self.position & single_bit_mask) > 0 {
                        result.push(current);
                    } else {
                        result.push(other);
                    }
                }
            }
            result.push_str("\n");
        }

        result.push_str(match self.plies % 2 {
            0 => "White to play",
            _ => "Black to play",
        });

        result
    }
}

#[cfg(test)]
mod gamestate_tests {
    use crate::GameState;

    #[test]
    fn successor_test() {
        let state1 = GameState::from_string("11223313");
        let state2 = GameState::from_string("11223313567");
        assert!(state2.is_successor(&state1));

        let state3 = GameState::from_string("11223313");
        let state4 = GameState::from_string("2211331377");
        assert!(state4.is_successor(&state3));
    }
}
