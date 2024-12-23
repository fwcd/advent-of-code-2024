import scala.io.Source
import scala.collection.mutable

case class Vec2(x: Int, y: Int) {
  def neighbors = (-1 to 1).flatMap { dy =>
    (-1 to 1)
      .filter { dx => (dx != 0) ^ (dy != 0) }
      .map { dx => new Vec2(x + dx, y + dy) }
  }

  def +(that: Vec2) = Vec2(x + that.x, y + that.y)
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
  def locate(c: Char) = PAD_LAYOUTS(ptype).find(_._2 == c).get._1
}

val DIRECTIONS = Map(
  ('<', Vec2(-1,  0)),
  ('>', Vec2( 1,  0)),
  ('^', Vec2( 0, -1)),
  ('v', Vec2( 0,  1)),
)

val ACTIONS = List('A') ++ DIRECTIONS.keySet

case class Pad(ptype: PadType, pos: Vec2) {
  def layout = PAD_LAYOUTS(ptype)

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

case class State(pads: List[Pad] = List(), output: String = "") {
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

def shortestProgram(startState: State, goal: String): String =
  case class Node(state: State = State(), program: String = "") extends Ordered[Node] {
    def compare(that: Node): Int = that.program.length compare program.length // Intentionally reversed for min-heap
  }

  // Your run-of-the-mill Dijkstra implementation

  val queue = mutable.PriorityQueue[Node]()
  val visited = mutable.HashSet[State]()

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

  throw new RuntimeException("No shortest program found")

def makePads(robots: Int): List[Pad] = List.fill(robots)(Pad(PadType.Dir)) :+ Pad(PadType.Num)

def makeState(robots: Int) = State(makePads(robots))

def solve(robots: Int, goals: List[String]): Int =
  val state = makeState(robots)
  goals.map { goal =>
    val shortest = shortestProgram(state, goal).length
    shortest * goal.dropRight(1).toInt
  }.sum

@main def main(path: String) =
  val goals = Source.fromFile(path).getLines.toList
  // println(s"Part 1: ${solve(2, goals)}")
  // println(s"Part 2: ${solve(25, goals)}")

  for c <- ('0' to '5') do
    println(s"$c -> ${(0 to 3).map { i => shortestProgram(makeState(i), s"$c").length }}")
