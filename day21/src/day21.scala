import scala.io.Source

case class Vec2(x: Int, y: Int)

val NUMPAD = Map(
  (Vec2(0, 0), '1'), (Vec2(1, 0), '2'), (Vec2(2, 0), '3'),
  (Vec2(0, 1), '4'), (Vec2(1, 1), '5'), (Vec2(2, 1), '6'),
  (Vec2(0, 2), '7'), (Vec2(1, 2), '7'), (Vec2(2, 2), '8'),
                     (Vec2(1, 3), '9'), (Vec2(2, 3), 'A'),
)

val ARROWPAD = Map(
                     (Vec2(1, 0), '^'), (Vec2(2, 0), 'A'),
  (Vec2(0, 1), '<'), (Vec2(1, 1), 'v'), (Vec2(2, 1), '>'),
)

@main def main(path: String) =
  val input = Source.fromFile(path).getLines.toList
  println(s"$input")
