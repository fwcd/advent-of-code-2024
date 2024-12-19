import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Paths;
import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.PriorityQueue;
import java.util.Set;
import java.util.stream.Collectors;
import java.util.stream.IntStream;
import java.util.stream.Stream;

public class Day18 {
  private static record Vec2(int x, int y) {}

  private static record Node(Vec2 pos, List<Vec2> path, int total) {}

  private static record Board(List<List<String>> rows) {
    public final int getHeight() { return rows.size(); }

    public final int getWidth() { return rows.get(0).size(); }

    public final boolean inBounds(Vec2 pos) { return pos.x >= 0 && pos.x < getWidth() && pos.y >= 0 && pos.y < getHeight(); }

    public final String get(Vec2 pos) { return rows.get(pos.y).get(pos.x); }

    public final Vec2 getStart() { return new Vec2(0, 0); }

    public final Vec2 getEnd() { return new Vec2(getWidth() - 1, getHeight() - 1); }

    public final int findShortestPath() {
      // Run-of-the-mill Dijkstra implementation

      Vec2 start = getStart();
      Vec2 end = getEnd();

      Set<Vec2> visited = new HashSet<>();
      PriorityQueue<Node> queue = new PriorityQueue<>((l, r) -> l.total - r.total);

      queue.offer(new Node(start, List.of(), 0));
      visited.add(start);

      while (!queue.isEmpty()) {
        Node node = queue.poll();
        if (node.pos.equals(end)) {
          return node.total;
        }
        for (int dy = -1; dy <= 1; dy++) {
          for (int dx = -1; dx <= 1; dx++) {
            if (dx != 0 ^ dy != 0) {
              Vec2 neigh = new Vec2(node.pos.x + dx, node.pos.y + dy);
              if (!visited.contains(neigh) && inBounds(neigh) && get(neigh).equals(".")) {
                queue.offer(new Node(neigh, Stream.concat(node.path.stream(), Stream.of(neigh)).toList(), node.total + 1));
                visited.add(neigh);
              }
            }
          }
        }
      }

      throw new RuntimeException("No path found");
    }

    @Override
    public final String toString() {
      return rows.stream().map(row -> row.stream().collect(Collectors.joining())).collect(Collectors.joining("\n"));
    }
  }

  public static void main(String[] args) throws IOException {
    if (args.length == 0) {
      System.err.println("Usage: day18 <path to input>");
      System.exit(1);
    }

    int prefix = 1024;
    int size = 71;

    Set<Vec2> positions = Files.readAllLines(Paths.get(args[0]))
      .stream()
      .map(l -> l.split(","))
      .map(s -> new Vec2(Integer.parseInt(s[0]), Integer.parseInt(s[1])))
      .limit(prefix)
      .collect(Collectors.toCollection(HashSet::new));
    
    Board board = new Board(
      IntStream.range(0, size).mapToObj(y ->
        IntStream.range(0, size).mapToObj(x ->
          positions.contains(new Vec2(x, y)) ? "#" : "."
        ).collect(Collectors.toCollection(ArrayList::new))
      ).collect(Collectors.toCollection(ArrayList::new))
    );

    System.out.println("Part 1: " + board.findShortestPath());
  }
}
