import scala.io.Source
import scala.collection.mutable

// The algorithm/approach is effectively a Scala port of
// https://www.reddit.com/r/adventofcode/comments/1hj2odw/comment/m36j01x For
// some reason my Dijkstra-based shortest-path constructions didn't yield the
// specific/right ordering, so, after long (and frustrating) experimentation, I
// eventually just ended up using that hardcoded map too. Most of the
// experiments can be found in earlier commits.

val SHORTEST_PATHS = Map(
  (('A', '0'), "<A"),
  (('0', 'A'), ">A"),
  (('A', '1'), "^<<A"),
  (('1', 'A'), ">>vA"),
  (('A', '2'), "<^A"),
  (('2', 'A'), "v>A"),
  (('A', '3'), "^A"),
  (('3', 'A'), "vA"),
  (('A', '4'), "^^<<A"),
  (('4', 'A'), ">>vvA"),
  (('A', '5'), "<^^A"),
  (('5', 'A'), "vv>A"),
  (('A', '6'), "^^A"),
  (('6', 'A'), "vvA"),
  (('A', '7'), "^^^<<A"),
  (('7', 'A'), ">>vvvA"),
  (('A', '8'), "<^^^A"),
  (('8', 'A'), "vvv>A"),
  (('A', '9'), "^^^A"),
  (('9', 'A'), "vvvA"),
  (('0', '1'), "^<A"),
  (('1', '0'), ">vA"),
  (('0', '2'), "^A"),
  (('2', '0'), "vA"),
  (('0', '3'), "^>A"),
  (('3', '0'), "<vA"),
  (('0', '4'), "^<^A"),
  (('4', '0'), ">vvA"),
  (('0', '5'), "^^A"),
  (('5', '0'), "vvA"),
  (('0', '6'), "^^>A"),
  (('6', '0'), "<vvA"),
  (('0', '7'), "^^^<A"),
  (('7', '0'), ">vvvA"),
  (('0', '8'), "^^^A"),
  (('8', '0'), "vvvA"),
  (('0', '9'), "^^^>A"),
  (('9', '0'), "<vvvA"),
  (('1', '2'), ">A"),
  (('2', '1'), "<A"),
  (('1', '3'), ">>A"),
  (('3', '1'), "<<A"),
  (('1', '4'), "^A"),
  (('4', '1'), "vA"),
  (('1', '5'), "^>A"),
  (('5', '1'), "<vA"),
  (('1', '6'), "^>>A"),
  (('6', '1'), "<<vA"),
  (('1', '7'), "^^A"),
  (('7', '1'), "vvA"),
  (('1', '8'), "^^>A"),
  (('8', '1'), "<vvA"),
  (('1', '9'), "^^>>A"),
  (('9', '1'), "<<vvA"),
  (('2', '3'), ">A"),
  (('3', '2'), "<A"),
  (('2', '4'), "<^A"),
  (('4', '2'), "v>A"),
  (('2', '5'), "^A"),
  (('5', '2'), "vA"),
  (('2', '6'), "^>A"),
  (('6', '2'), "<vA"),
  (('2', '7'), "<^^A"),
  (('7', '2'), "vv>A"),
  (('2', '8'), "^^A"),
  (('8', '2'), "vvA"),
  (('2', '9'), "^^>A"),
  (('9', '2'), "<vvA"),
  (('3', '4'), "<<^A"),
  (('4', '3'), "v>>A"),
  (('3', '5'), "<^A"),
  (('5', '3'), "v>A"),
  (('3', '6'), "^A"),
  (('6', '3'), "vA"),
  (('3', '7'), "<<^^A"),
  (('7', '3'), "vv>>A"),
  (('3', '8'), "<^^A"),
  (('8', '3'), "vv>A"),
  (('3', '9'), "^^A"),
  (('9', '3'), "vvA"),
  (('4', '5'), ">A"),
  (('5', '4'), "<A"),
  (('4', '6'), ">>A"),
  (('6', '4'), "<<A"),
  (('4', '7'), "^A"),
  (('7', '4'), "vA"),
  (('4', '8'), "^>A"),
  (('8', '4'), "<vA"),
  (('4', '9'), "^>>A"),
  (('9', '4'), "<<vA"),
  (('5', '6'), ">A"),
  (('6', '5'), "<A"),
  (('5', '7'), "<^A"),
  (('7', '5'), "v>A"),
  (('5', '8'), "^A"),
  (('8', '5'), "vA"),
  (('5', '9'), "^>A"),
  (('9', '5'), "<vA"),
  (('6', '7'), "<<^A"),
  (('7', '6'), "v>>A"),
  (('6', '8'), "<^A"),
  (('8', '6'), "v>A"),
  (('6', '9'), "^A"),
  (('9', '6'), "vA"),
  (('7', '8'), ">A"),
  (('8', '7'), "<A"),
  (('7', '9'), ">>A"),
  (('9', '7'), "<<A"),
  (('8', '9'), ">A"),
  (('9', '8'), "<A"),
  (('<', '^'), ">^A"),
  (('^', '<'), "v<A"),
  (('<', 'v'), ">A"),
  (('v', '<'), "<A"),
  (('<', '>'), ">>A"),
  (('>', '<'), "<<A"),
  (('<', 'A'), ">>^A"),
  (('A', '<'), "v<<A"),
  (('^', 'v'), "vA"),
  (('v', '^'), "^A"),
  (('^', '>'), "v>A"),
  (('>', '^'), "<^A"),
  (('^', 'A'), ">A"),
  (('A', '^'), "<A"),
  (('v', '>'), ">A"),
  (('>', 'v'), "<A"),
  (('v', 'A'), "^>A"),
  (('A', 'v'), "<vA"),
  (('>', 'A'), "^A"),
  (('A', '>'), "vA"),
)

val memo = mutable.Map[(Int, String), Long]()

def shortestProgramLength(robots: Int, goal: String): Long =
  val key = (robots, goal)
  if memo.contains(key) then
    return memo(key)

  val result = if robots < 0 then
    goal.length.toLong
  else
    var current = 'A'
    var length = 0L
    for next <- goal do
      length += moveCount(robots, current, next)
      current = next
    length

  memo(key) = result
  result

def moveCount(robots: Int, current: Char, next: Char): Long =
  if current == next then
    1
  else
    shortestProgramLength(robots - 1, SHORTEST_PATHS((current, next)))

def solve(robots: Int, goals: List[String]): Long =
  goals.map { goal =>
    val shortest = shortestProgramLength(robots, goal)
    shortest * goal.dropRight(1).toLong
  }.sum

@main def main(path: String) =
  val goals = Source.fromFile(path).getLines.toList

  println(s"Part 1: ${solve(2, goals)}")
  println(s"Part 2: ${solve(25, goals)}")
