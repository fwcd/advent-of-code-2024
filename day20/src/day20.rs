use std::{cmp::Ordering, collections::{BinaryHeap, HashMap, HashSet}, env, fs, ops::Index, process};

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

impl Vec2<i32> {
    fn manhattan_dist(self, rhs: Self) -> usize {
        (self.x.abs_diff(rhs.x) + self.y.abs_diff(rhs.y)) as usize
    }

    fn in_bounds(&self, width: usize, height: usize) -> bool {
        self.x >= 0 && self.x < width as i32 && self.y >= 0 && self.y < height as i32
    }
}

#[derive(Clone, Debug, Hash, PartialEq, Eq)]
struct Racetrack {
    rows: Vec<Vec<char>>,
}

#[derive(Clone, Copy, Debug, Hash, PartialEq, Eq)]
struct Cheat {
    start: Vec2<i32>,
    end: Vec2<i32>,
    picos: usize,
}

#[derive(Clone, Copy, Debug, Hash, PartialEq, Eq)]
struct Node {
    pos: Vec2<i32>,
    picos: usize,
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

#[derive(Clone, Debug, PartialEq, Eq)]
struct Trace {
    dists_to_end: HashMap<Vec2<i32>, usize>,
    end: Vec2<i32>,
}

impl Racetrack {
    fn height(&self) -> usize {
        self.rows.len()
    }

    fn width(&self) -> usize {
        self.rows[0].len()
    }

    fn is_wall(&self, pos: Vec2<i32>) -> bool {
        self[pos] == '#'
    }

    fn positions(&self) -> impl Iterator<Item = Vec2<i32>> {
        let width = self.width();
        let height = self.height();
        (0..height).flat_map(move |y| (0..width).map(move |x| Vec2::new(x as i32, y as i32)))
    }

    fn neighbors(&self, pos: Vec2<i32>) -> impl Iterator<Item = Vec2<i32>> {
        let width = self.width();
        let height = self.height();
        (-1..=1)
            .flat_map(move |dy| (-1..=1)
                .filter(move |&dx| (dx != 0) ^ (dy != 0))
                .map(move |dx| Vec2::new(pos.x + dx, pos.y + dy))
                .filter(move |&neigh| neigh.in_bounds(width, height)))
    }

    fn cheat_targets<'a>(&'a self, start: Vec2<i32>, dist: usize) -> impl Iterator<Item = Vec2<i32>> + 'a {
        self.positions()
            .filter(move |&p| !self.is_wall(p) && {
                let d = start.manhattan_dist(p);
                d >= 1 && d <= dist
            })
    }

    fn locate(&self, c: char) -> Option<Vec2<i32>> {
        self.rows.iter()
            .enumerate()
            .find_map(|(y, row)| row.iter().enumerate().find(|(_, &cell)| cell == c).map(|(x, _)| Vec2::new(x as i32, y as i32)))
    }

    /// Traces out the racetrack to the end, finding the distances from every position.
    fn trace_to_end(&self, start: Vec2<i32>) -> Trace {
        let mut stack = Vec::new();
        let mut dists_to_end = HashMap::new();

        stack.push(start);

        while let Some(next) = self.neighbors(*stack.last().unwrap()).find(|&v| self[v] != '#' && Some(&v) != stack.get(stack.len() - 2)) {
            stack.push(next);
        }

        for (i, &pos) in stack.iter().enumerate() {
            dists_to_end.insert(pos, stack.len() - 1 - i);
        }

        Trace { dists_to_end, end: *stack.last().unwrap() }
    }

    /// Finds paths through the racetrack, ordered ascendingly by total picoseconds.
    fn count_paths(&self, start: Vec2<i32>, cheat_picos: usize) -> i32 {
        // Your (not quite) run-of-the-mill Dijkstra implementation

        let trace = self.trace_to_end(start);
        let base_picos = trace.dists_to_end[&start];

        let mut queue = BinaryHeap::new();
        let mut visited = HashSet::new();
        let mut paths = 0;

        macro_rules! offer_node {
            ($node:expr) => {
                if !visited.contains(&($node.pos, $node.cheat)) {
                    visited.insert(($node.pos, $node.cheat));
                    queue.push($node);
                }
            }
        }

        offer_node!(Node { pos: start, picos: 0, cheat: None });

        while let Some(node) = queue.pop() {
            if node.pos == trace.end {
                if node.picos + 100 > base_picos {
                    break;
                }
                paths += 1;
                continue;
            }

            assert!(node.cheat.is_none());

            // Explore cheating (and hopping straight to the end since we can't cheat afterwards)
            for target in self.cheat_targets(node.pos, cheat_picos) {
                let cheat_picos = node.pos.manhattan_dist(target);
                let new_cheat = Some(Cheat { start: node.pos, end: target, picos: cheat_picos });
                let new_picos = node.picos + cheat_picos + trace.dists_to_end[&target];
                let new_node = Node { pos: trace.end, picos: new_picos, cheat: new_cheat };
                offer_node!(new_node);
            }

            // Explore continuing along the path
            for neigh in self.neighbors(node.pos) {
                if !self.is_wall(neigh) {
                    let new_picos = node.picos + 1;
                    offer_node!(Node { pos: neigh, picos: new_picos, cheat: node.cheat });
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

    let part1 = track.count_paths(start, 2);
    println!("Part 1: {part1}");

    let part2 = track.count_paths(start, 20);
    println!("Part 2: {part2}");
}
