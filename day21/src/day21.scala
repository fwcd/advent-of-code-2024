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
    (Vec2(0, 0), '1'), (Vec2(1, 0), '2'), (Vec2(2, 0), '3'),
    (Vec2(0, 1), '4'), (Vec2(1, 1), '5'), (Vec2(2, 1), '6'),
    (Vec2(0, 2), '7'), (Vec2(1, 2), '7'), (Vec2(2, 2), '8'),
                       (Vec2(1, 3), '9'), (Vec2(2, 3), 'A'),
  )),
  (PadType.Dir, Map(
                       (Vec2(1, 0), '^'), (Vec2(2, 0), 'A'),
    (Vec2(0, 1), '<'), (Vec2(1, 1), 'v'), (Vec2(2, 1), '>'),
  )),
)

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

  def perform(action: Char): (Option[Char], Pad) =
    action match
      case 'A' => (Some(activate), this)
      case _ => (None, Pad(ptype, pos + DIRECTIONS(action)))
}

case class State(pads: List[Pad], output: String) {
  def perform(action: Char) =
    val (newPads, outAction) = pads.foldLeft[(List[Pad], Option[Char])]((List(), Some(action))) { case ((pads, action), pad) =>
      action match
        case Some(action) =>
          val (newAction, newPad) = pad.perform(action)
          (pads :+ newPad, newAction)
        case None => (pads :+ pad, None)
    }
    val newOutput = outAction.map(output.appended(_)).getOrElse(output)
    State(newPads, newOutput)
}

case class Node(state: State, program: String) extends Ordered[Node] {
  def compare(that: Node): Int = program.length() compare that.program.length()
}

def shortestProgram(goal: String): String =
  // Your run-of-the-mill Dijkstra implementation

  val queue = mutable.PriorityQueue[Node]()
  val visited = mutable.HashSet[State]()

  val start = Node(State(List(), ""), "")
  queue.enqueue(start)
  visited.add(start.state)

  while (!queue.isEmpty) do
    val node = queue.dequeue()
    if (node.state.output == goal) then
      return node.program

    for action <- ACTIONS do
      val newState = node.state.perform(action)
      if !visited.contains(newState) then
        visited.add(newState)
        queue.enqueue(Node(newState, node.program.appended(action)))

  throw new RuntimeException("No shortest program found")

@main def main(path: String) =
  val input = Source.fromFile(path).getLines.toList
  println(s"$input")
