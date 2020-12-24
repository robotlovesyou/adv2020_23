use std::collections::HashMap;

fn main() {
    let mut game = Game::new(&[4, 1, 8, 9, 7, 6, 2, 3, 5], 9);
    game.advance_n(100);
    println!("Part 1\n======\n{}", game.label());

    let mut game = Game::new(&[4, 1, 8, 9, 7, 6, 2, 3, 5], 1_000_000);
    game.advance_n(10_000_000);
    println!("Part 2\n======\n{}", game.game_result());
}

struct IndexedDeque {
    front: Option<u64>,
    back: Option<u64>,
    edges: HashMap<u64, (Option<u64>, Option<u64>)>,
}

impl IndexedDeque {
    fn new() -> IndexedDeque {
        IndexedDeque {
            front: None,
            back: None,
            edges: HashMap::new(),
        }
    }

    #[allow(dead_code)]
    fn push_front(&mut self, itm: u64) {
        if self.edges.contains_key(&itm) {
            panic!("queue already contains {}", itm)
        }

        if let Some(front) = self.front.take() {
            match *self.edges.get(&front).expect("no front") {
                (None, next) => self.edges.insert(front, (Some(itm), next)),
                other => panic!("front item should not have a prev entry: {:?}", other),
            };
            self.edges.insert(itm, (None, Some(front)));
        } else {
            self.edges.insert(itm, (None, None));
        }

        if self.back.is_none() {
            self.back = Some(itm)
        }

        self.front = Some(itm);
    }

    fn pop_front(&mut self) -> Option<u64> {
        self.front.map(|front| {
            match self
                .edges
                .remove(&front)
                .expect("no front in edges when popping")
            {
                (None, None) => {
                    self.front = None;
                    self.back = None;
                    front
                }
                (None, Some(next)) => {
                    let (_, next_next) = *self.edges.get(&next).expect("no next->next in edges");
                    self.edges.insert(next, (None, next_next));
                    self.front = Some(next);
                    front
                }
                other => panic!("invalid front state {:?} when calling pop_front", other),
            }
        })
    }

    fn push_back(&mut self, itm: u64) {
        if self.edges.contains_key(&itm) {
            panic!("queue already contains {}", itm);
        }

        if let Some(back) = self.back.take() {
            match *self.edges.get(&back).expect("no back") {
                (prev_opt, None) => self.edges.insert(back, (prev_opt, Some(itm))),
                other => panic!(
                    "back item should not have a next entry: {}->{:?}",
                    back, other
                ),
            };
            self.edges.insert(itm, (Some(back), None));
        } else {
            self.edges.insert(itm, (None, None));
        }

        if self.front.is_none() {
            self.front = Some(itm);
        }

        self.back = Some(itm);
    }

    #[allow(dead_code)]
    fn pop_back(&mut self) -> Option<u64> {
        self.back.map(|back| {
            match self
                .edges
                .remove(&back)
                .expect("no back in edges when popping")
            {
                (None, None) => {
                    self.front = None;
                    self.back = None;
                    back
                }
                (Some(prev), None) => {
                    let (prev_prev_opt, _) =
                        *self.edges.get(&prev).expect("no prev->prev in edges");
                    self.edges.insert(prev, (prev_prev_opt, None));
                    self.back = Some(prev);
                    back
                }
                other => panic!("invalid back state {:?} when calling pop_back", other),
            }
        })
    }

    fn insert_after(&mut self, itm: u64, after: u64) {
        if !self.contains(after) {
            panic!("does not contain item {}", after);
        }

        let (prev_opt, next_opt) = *self.edges.get(&after).unwrap();
        self.edges.insert(after, (prev_opt, Some(itm)));

        if let Some(next) = next_opt {
            let (_, next_next) = *self.edges.get(&next).unwrap();
            self.edges.insert(next, (Some(itm), next_next));
            self.edges.insert(itm, (Some(after), Some(next)));
        } else {
            self.edges.insert(itm, (Some(after), None));
            self.back = Some(itm);
        }
    }

    fn remove_after(&mut self, after: u64) -> Option<u64> {
        if !self.contains(after) {
            panic!("does not contain item {}", after);
        }

        let (after_prev_opt, after_next_opt) = *self.edges.get(&after).unwrap();
        after_next_opt.map(|after_next| {
            match *self.edges.get(&after_next).unwrap() {
                (_, Some(after_next_next)) => {
                    self.edges
                        .insert(after, (after_prev_opt, Some(after_next_next)));
                    let (_, after_next_next_next_opt) = *self.edges.get(&after_next_next).unwrap();
                    self.edges
                        .insert(after_next_next, (Some(after), after_next_next_next_opt));
                }
                (_, None) => {
                    self.edges.insert(after, (after_prev_opt, None));
                    self.back = Some(after);
                }
            }
            after_next
        })
    }

    #[allow(dead_code)]
    fn front(&self) -> Option<u64> {
        self.front.as_ref().copied()
    }

    #[allow(dead_code)]
    fn back(&self) -> Option<u64> {
        self.back.as_ref().copied()
    }

    fn contains(&self, itm: u64) -> bool {
        self.edges.contains_key(&itm)
    }
}

struct Game {
    queue: IndexedDeque,
    min: u64,
    max: u64,
}

impl Game {
    fn new(seed: &[u64], len: usize) -> Game {
        if len < seed.len() {
            panic!("len must be >= seed.len");
        }

        let mut queue = IndexedDeque::new();
        let mut max = 0;
        let mut min = u64::MAX;
        for n in seed.iter() {
            max = u64::max(max, *n);
            min = u64::min(min, *n);
            queue.push_back(*n);
        }
        for n in 1..=(len - seed.len()) {
            queue.push_back(max + n as u64);
        }
        Game {
            queue,
            min,
            max: max + (len - seed.len()) as u64,
        }
    }

    fn find_destination(&self, current: u64, a: u64, b: u64, c: u64) -> u64 {
        let next_destination = |n: u64| if n <= self.min { self.max } else { n - 1 };

        let mut destination = next_destination(current);
        while [current, a, b, c].contains(&destination) || !self.queue.contains(destination) {
            destination = next_destination(destination);
        }
        destination
    }

    fn advance(&mut self) {
        let (current, a, b, c) = (
            self.queue.pop_front().unwrap(),
            self.queue.pop_front().unwrap(),
            self.queue.pop_front().unwrap(),
            self.queue.pop_front().unwrap(),
        );

        let destination = self.find_destination(current, a, b, c);
        self.queue.insert_after(a, destination);
        self.queue.insert_after(b, a);
        self.queue.insert_after(c, b);

        self.queue.push_back(current);
    }

    fn advance_n(&mut self, n: usize) {
        for _i in 0..n {
            self.advance();
            // if _i % 10_000 == 0 || _i == n - 1 {
            //     println!("{} rounds", _i+1);
            // }
        }
    }

    fn game_result(&mut self) -> u64 {
        let a_opt = self.queue.remove_after(1);
        let b_opt = self.queue.remove_after(1);

        let (a, b) = match (a_opt, b_opt) {
            (Some(a), Some(b)) => (a, b),
            (Some(a), None) => {
                let b = self.queue.pop_front().unwrap();
                (a, b)
            }
            _ => {
                let a = self.queue.pop_front().unwrap();
                let b = self.queue.pop_front().unwrap();
                (a, b)
            }
        };
        a * b
    }

    fn label(&mut self) -> String {
        let mut label = String::new();
        while let Some(n) = self.queue.remove_after(1) {
            label += format!("{}", n).as_str();
        }
        while let Some(n) = self.queue.pop_front() {
            if n == 1 {
                break;
            }
            label += format!("{}", n).as_str();
        }
        label
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn can_push_and_pop_from_front_of_deque() {
        let mut queue = IndexedDeque::new();
        queue.push_front(5);
        queue.push_front(6);
        queue.push_front(7);

        assert!(matches!(queue.back(), Some(5)));
        assert!(matches!(queue.front(), Some(7)));
        assert!(matches!(queue.pop_front(), Some(7)));
        assert!(matches!(queue.pop_front(), Some(6)));
        assert!(matches!(queue.pop_front(), Some(5)));
        assert!(matches!(queue.pop_front(), None));
        assert!(matches!(queue.back(), None));
        assert!(matches!(queue.front(), None));
    }

    #[test]
    fn can_push_and_pop_back() {
        let mut queue = IndexedDeque::new();
        queue.push_back(5);
        queue.push_back(6);
        queue.push_back(7);

        assert!(matches!(queue.back(), Some(7)));
        assert!(matches!(queue.front(), Some(5)));
        assert!(matches!(queue.pop_back(), Some(7)));
        assert!(matches!(queue.pop_back(), Some(6)));
        assert!(matches!(queue.pop_back(), Some(5)));
        assert!(matches!(queue.pop_back(), None));
        assert!(matches!(queue.back(), None));
        assert!(matches!(queue.front(), None));
    }

    #[test]
    fn can_check_contains_key() {
        let mut queue = IndexedDeque::new();
        queue.push_back(123);
        assert!(queue.contains(123));
        assert!(!queue.contains(124));
    }

    #[test]
    fn can_insert_after() {
        let mut queue = IndexedDeque::new();
        queue.push_back(5);
        queue.insert_after(6, 5);
        queue.insert_after(7, 6);

        queue.push_front(3);
        queue.insert_after(4, 3);

        let popped = [
            queue.pop_front().unwrap(),
            queue.pop_front().unwrap(),
            queue.pop_front().unwrap(),
            queue.pop_front().unwrap(),
            queue.pop_front().unwrap(),
        ];

        assert_eq!([3, 4, 5, 6, 7], popped);
    }

    #[test]
    fn can_remove_after() {
        let mut queue = IndexedDeque::new();
        queue.push_back(4);
        queue.push_back(5);
        queue.push_back(6);
        queue.push_back(7);
        queue.push_back(8);

        assert!(matches!(queue.remove_after(4), Some(5)));
        assert!(matches!(queue.remove_after(4), Some(6)));
        assert!(matches!(queue.remove_after(7), Some(8)));
        assert!(matches!(queue.back(), Some(7)));
    }

    #[test]
    fn game_advances_as_expected() {
        let mut game = Game::new(&[3, 8, 9, 1, 2, 5, 4, 6, 7], 9);
        game.advance_n(10);
        assert_eq!(18, game.game_result());

        let mut game = Game::new(&[3, 8, 9, 1, 2, 5, 4, 6, 7], 9);
        game.advance_n(100);
        assert_eq!(42, game.game_result());
    }
}
