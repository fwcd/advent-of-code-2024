import scala.io.Source

@main def main(path: String) =
  val input = Source.fromFile(path).getLines.toList
  println(s"$input")
