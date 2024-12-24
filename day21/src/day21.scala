import scala.io.Source
import scala.collection.mutable

case class Vec2(x: Int, y: Int) {
  def neighbors = (-1 to 1).flatMap { dy =>
    (-1 to 1)
      .filter { dx => (dx != 0) ^ (dy != 0) }
      .map { dx => new Vec2(x + dx, y + dy) }
  }

  def +(that: Vec2) = Vec2(x + that.x, y + that.y)

  def manhattanDist(that: Vec2) = (x - that.x).abs + (y - that.y).abs
}

enum PadType:
  case Num, Dir

val PAD_LAYOUTS = Map(
  (PadType.Num, Map(
    (Vec2(0, 0), '7'), (Vec2(1, 0), '8'), (Vec2(2, 0), '9'),
    (Vec2(0, 1), '4'), (Vec2(1, 1), '5'), (Vec2(2, 1), '6'),
    (Vec2(0, 2), '1'), (Vec2(1, 2), '2'), (Vec2(2, 2), '3'),
                       (Vec2(1, 3), '0'), (Vec2(2, 3), 'A'),
  )),
  (PadType.Dir, Map(
                       (Vec2(1, 0), '^'), (Vec2(2, 0), 'A'),
    (Vec2(0, 1), '<'), (Vec2(1, 1), 'v'), (Vec2(2, 1), '>'),
  )),
)

extension (ptype: PadType) {
  def layout = PAD_LAYOUTS(ptype)

  def locate(c: Char) = ptype.layout.find(_._2 == c).get._1

  def shortestPath(startPos: Vec2, endPos: Vec2): String =
    case class Node(pos: Vec2, index: Int, program: String = "") extends Ordered[Node] {
      def cost = program.length * 1_000_000 + turns * 1_000 + index

      def turns = program.zip(program.tail).count { case (c1, c2) => c1 != c2 }

      def compare(that: Node): Int = that.cost compare cost // Intentionally reversed for min-heap
    }

    val queue = mutable.PriorityQueue[Node]()
    val visited = mutable.Set[Vec2]()
    var index = 0

    queue.enqueue(Node(startPos, index))

    while !queue.isEmpty do
      val node = queue.dequeue()
      if node.pos == endPos then
        // Annoying edge cases, what rule do they follow?
        return Map(
          (">>^", "^>>"),
          ("vv<", "<vv"),
          ("vv>v", ">vvv"),
          (">>v", "v>>"),
          ("vvv<", "<vvv"),
          ("vv<", "<vv"),
          ("<^<", "^<<"),
          ("^^<", "<^^"),
          ("^^^<", "<^^^"),
          ("<v<", "v<<"),
          ("<^^", "^<^"),
          ("<^^^", "^^^<"),
          ("v>>", ">>v"),
          ("^>>", ">>^"),
        ).getOrElse(node.program, node.program)
          .appended('A')
      
      for action <- List('<', '^', 'v', '>') do
        val dir = DIRECTIONS(action)
        val neigh = node.pos + dir
        if layout.contains(neigh) && !visited.contains(neigh) then
          visited.add(neigh)
          queue.enqueue(Node(neigh, index, node.program.appended(action)))
          index += 1
      
    throw RuntimeException("No shortest program found")
  
  def shortestPaths: Map[(Char, Char), String] =
    layout.flatMap { case (p1, a1) => layout.map { case (p2, a2) => ((a1, a2), shortestPath(p1, p2)) } }.toMap
}

val DIRECTIONS = Map(
  ('<', Vec2(-1,  0)),
  ('>', Vec2( 1,  0)),
  ('^', Vec2( 0, -1)),
  ('v', Vec2( 0,  1)),
)

val ACTIONS = List('A') ++ DIRECTIONS.keySet

case class Pad(ptype: PadType, pos: Vec2) {
  def layout = ptype.layout

  def activate: Char = layout(pos)

  def isValid = layout.contains(pos)

  def perform(action: Char): (Option[Char], Pad) =
    action match
      case 'A' => (Some(activate), this)
      case _ => (None, Pad(ptype, pos + DIRECTIONS(action)))
}

object Pad {
  def apply(ptype: PadType): Pad = Pad(ptype, ptype.locate('A'))
}

def shortestProgram(robots: Int, goal: String): String =
  case class State(pads: List[Pad] = List.fill(robots)(Pad(PadType.Dir)) :+ Pad(PadType.Num), output: String = "") {
    def perform(action: Char) =
      for
        (newPads, outAction) <- pads.foldLeft[Option[(List[Pad], Option[Char])]](Some((List(), Some(action)))) { (acc, pad) =>
          acc.flatMap { case (pads, action) =>
            action match
              case Some(action) =>
                for
                  (newAction, newPad) <- Some(pad.perform(action))
                  if newPad.isValid
                yield (pads :+ newPad, newAction)
              case None => Some((pads :+ pad, None))
          }
        }
      yield
        val newOutput = outAction.map(output.appended(_)).getOrElse(output)
        State(newPads, newOutput)
  }

  case class Node(state: State = State(), program: String = "") extends Ordered[Node] {
    def compare(that: Node): Int = that.program.length compare program.length // Intentionally reversed for min-heap
  }

  // Your run-of-the-mill Dijkstra implementation

  val queue = mutable.PriorityQueue[Node]()
  val visited = mutable.Set[State]()

  val startState = State()
  val start = Node(startState)
  queue.enqueue(start)
  visited.add(startState)

  while !queue.isEmpty do
    val node = queue.dequeue()
    if node.state.output == goal then
      return node.program

    if node.state.output.length < goal.length then
      for
        action <- ACTIONS
        newState <- node.state.perform(action)
      do
        if !visited.contains(newState) then
          visited.add(newState)
          queue.enqueue(Node(newState, node.program.appended(action)))

  throw RuntimeException("No shortest program found")

def shortestProgramLength(robots: Int, goal: String): Int =
  case class State(pos: Vec2 = PadType.Num.locate('A'), dPos: Vec2 = PadType.Dir.locate('A'), output: String = "")

  case class Node(state: State, total: Int = 0) extends Ordered[Node] {
    def compare(that: Node): Int = that.total compare total // Intentionally reversed for min-heap
  }

  def cost(robots: Int, pos: Vec2, dPos: Vec2, action: Char): (Int, Vec2) =
    if robots <= 0 then
      (1, dPos)
    else
      // Only considering robots = 1 for now
      val targetDPos = PadType.Dir.locate(action)
      val steps = dPos.manhattanDist(targetDPos) + 1 // needs 'A' press
      // println(s"$dPos -> $targetDPos ('${PAD_LAYOUTS(PadType.Dir)(dPos)}' ${steps} -> '${PAD_LAYOUTS(PadType.Dir)(targetDPos)}')")
      (steps, targetDPos)

  // Your run-of-the-mill Dijkstra implementation (this time on the numpad)

  val queue = mutable.PriorityQueue[Node]()
  val visited = mutable.Set[State]()

  val startState = State()
  val start = Node(startState)
  queue.enqueue(start)
  visited.add(startState)

  while !queue.isEmpty do
    val node = queue.dequeue()
    if node.state.output == goal then
      return node.total

    if node.state.output.length < goal.length then
      for
        action <- ACTIONS
      do
        val newPos = node.state.pos + DIRECTIONS.get(action).getOrElse(Vec2(0, 0))
        if PAD_LAYOUTS(PadType.Num).contains(newPos) then
          val (c, newDPos) = cost(robots, node.state.pos, node.state.dPos, action)
          val newOutput = if action == 'A' then node.state.output.appended(PAD_LAYOUTS(PadType.Num)(node.state.pos)) else node.state.output
          val newState = State(newPos, newDPos, newOutput)
          if !visited.contains(newState) then
            visited.add(newState)
            queue.enqueue(Node(newState, node.total + c))

  throw RuntimeException("No shortest program found")

def solve(robots: Int, goals: List[String], func: (Int, String) => Long): Long =
  goals.map { goal =>
    val shortest = func(robots, goal)
    shortest * goal.dropRight(1).toLong
  }.sum

// Algorithm/approach is effectively a Scala port of
// https://www.reddit.com/r/adventofcode/comments/1hj2odw/comment/m36j01x For
// some reason my Dijkstra-based shortest-path constructions didn't yield the
// specific/right ordering, so I eventually just ended up using the hardcoded
// map too. Most of the experiments can be found in earlier commits.

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

def shortestProgramLengthClever(robots: Int, goal: String): Long =
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
    shortestProgramLengthClever(robots - 1, SHORTEST_PATHS((current, next)))

@main def main(path: String) =
  val goals = Source.fromFile(path).getLines.toList
  // println(s"Part 1: ${solve(2, goals)}")
  // println(s"Part 2: ${solve(25, goals)}")

  // for (k, p) <- SHORTEST_PATHS.toList.sorted do
  //   if k._1 != k._2 && p != SHORTEST_PATHS_2(k) then
  //     println(s"(\"$p\", \"${SHORTEST_PATHS_2(k)}\")")

  println(s"Part 1: ${solve(2, goals, shortestProgramLengthClever)}")
  println(s"Part 2: ${solve(25, goals, shortestProgramLengthClever)}")

  // for i <- (0 to 3) do
  //   println(s"${solve(i, goals, { (r, g) => shortestProgram(r, g).length })} vs ${solve(i, goals, shortestProgramLength)} vs ${solve(i, goals, shortestProgramLengthClever)}")

  // for c <- ('0' to '5') do
  //   println(s"$c -> ${(0 to 3).map { i => shortestProgram(makeState(i), s"$c").length }}")
