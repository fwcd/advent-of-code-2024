use std::{cmp::Ordering, collections::{BinaryHeap, HashSet}, env, fs, ops::Index, process};

#[derive(Clone, Copy, Debug, Hash, PartialEq, Eq)]
struct Vec2<T> {
    x: T,
    y: T,
}

impl<T> Vec2<T> {
    fn new(x: T, y: T) -> Self {
        Self { x, y }
    }
}

#[derive(Clone, Debug, Hash, PartialEq, Eq)]
struct Racetrack {
    rows: Vec<Vec<char>>,
}

#[derive(Clone, Copy, Debug, Hash, PartialEq, Eq)]
struct Cheat {
    start: Vec2<i32>,
    end: Option<Vec2<i32>>,
    picos_left: i32,
}

#[derive(Clone, Copy, Debug, Hash, PartialEq, Eq)]
struct Node {
    pos: Vec2<i32>,
    picos: i32,
    cost: i32,
    cheat: Option<Cheat>,
}

impl Ord for Node {
    fn cmp(&self, other: &Self) -> Ordering {
        other.picos.cmp(&self.picos) // Intentionally reversed to make BinaryHeap behave like a min-heap
    }
}

impl PartialOrd for Node {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

#[derive(Clone, Copy, Debug, Hash, PartialEq, Eq)]
enum CheatPolicy {
    Allowed { picos: i32 },
    Forbidden,
}

impl Racetrack {
    fn height(&self) -> i32 {
        self.rows.len() as i32
    }

    fn width(&self) -> i32 {
        self.rows[0].len() as i32
    }

    fn in_bounds(&self, pos: Vec2<i32>) -> bool {
        pos.x >= 0 && pos.x < self.width() && pos.y >= 0 && pos.y < self.height()
    }

    fn neighbors<'a>(&'a self, pos: Vec2<i32>) -> impl Iterator<Item = Vec2<i32>> + 'a {
        (-1..=1)
            .flat_map(move |dy| (-1..=1)
                .filter(move |&dx| (dx != 0) ^ (dy != 0))
                .map(move |dx| Vec2::new(pos.x + dx, pos.y + dy)))
            .filter(move |&neigh| self.in_bounds(neigh))
    }

    fn locate(&self, c: char) -> Option<Vec2<i32>> {
        self.rows.iter()
            .enumerate()
            .find_map(|(y, row)| row.iter().enumerate().find(|(_, &cell)| cell == c).map(|(x, _)| Vec2::new(x as i32, y as i32)))
    }

    /// Finds paths through the racetrack, ordered ascendingly by total picoseconds.
    fn find_paths(&self, start: Vec2<i32>, end: Vec2<i32>, cheat_policy: CheatPolicy, condition: impl Fn(Node) -> bool) -> Vec<Node> {
        // Your run-of-the-mill A* (Dijkstra + heuristic) implementation

        let mut queue = BinaryHeap::new();
        let mut visited = HashSet::new();
        let mut paths = Vec::new();

        queue.push(Node { pos: start, picos: 0, cost: 0, cheat: None });
        visited.insert((start, None));

        while let Some(node) = queue.pop() {
            if node.pos == end {
                if !condition(node) {
                    break;
                }
                println!("{node:?}");
                paths.push(node);
            }

            for neigh in self.neighbors(node.pos) {
                let is_wall = self[neigh] == '#';

                let cheats_allowed = matches!(cheat_policy, CheatPolicy::Allowed { .. });
                let can_cheat = cheats_allowed && node.cheat.map_or(true, |c| c.picos_left > 0);
                let new_cheat = if let Some(cheat) = node.cheat {
                    let is_ending = cheat.picos_left == 1;
                    if is_ending && is_wall {
                        continue;
                    }
                    Some(Cheat { start: cheat.start, end: if is_ending { Some(neigh) } else { cheat.end }, picos_left: (cheat.picos_left - 1).max(0) })
                } else if cheats_allowed && is_wall {
                    if let CheatPolicy::Allowed { picos: cheat_picos } = cheat_policy {
                        Some(Cheat { start: node.pos, end: None, picos_left: cheat_picos })
                    } else {
                        unreachable!()
                    }
                } else {
                    node.cheat
                };

                if !visited.contains(&(neigh, new_cheat)) && (!is_wall || can_cheat) {
                    visited.insert((neigh, new_cheat));

                    let new_picos = node.picos + 1;
                    let new_dist_to_end = (neigh.x.abs_diff(end.x) + neigh.y.abs_diff(end.y)) as i32;
                    let new_cost = new_picos + new_dist_to_end;
                    queue.push(Node { pos: neigh, picos: new_picos, cost: new_cost, cheat: new_cheat });
                }
            }
        }

        paths
    }
}

impl Index<Vec2<i32>> for Racetrack {
    type Output = char;

    fn index(&self, index: Vec2<i32>) -> &char {
        &self.rows[index.y as usize][index.x as usize]
    }
}

fn main() {
    let args: Vec<_> = env::args().collect();
    if args.len() == 1 {
        println!("Usage: {} <path to input>", args[0]);
        process::exit(1);
    }

    let raw = fs::read_to_string(&args[1]).unwrap();
    let track = Racetrack { rows: raw.trim().split("\n").map(|row| row.chars().collect()).collect() };

    let start = track.locate('S').unwrap();
    let end = track.locate('E').unwrap();

    let shortest_path = track.find_paths(start, end, CheatPolicy::Forbidden, |_| true)[0];
    let base_picos = shortest_path.picos;

    let cheat_paths1 = track.find_paths(start, end, CheatPolicy::Allowed { picos: 2 }, |n| n.picos <= base_picos - 100);
    let part1 = cheat_paths1.len();
    println!("Part 1: {part1}");

    let cheat_paths2 = track.find_paths(start, end, CheatPolicy::Allowed { picos: 20 }, |n| n.picos <= base_picos - 100);
    let part2 = cheat_paths2.len();
    println!("Part 2: {part2}");
}
