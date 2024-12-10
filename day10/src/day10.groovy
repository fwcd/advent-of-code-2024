#!/usr/bin/env groovy

record Vec2(int x, int y) {}

class TopoMap {
  private List<List<Integer>> values

  TopoMap(List<List<Integer>> values) {
    this.values = values
  }

  def getHeight() { values.size() }

  def getWidth() { values[0].size() }

  def get(Vec2 pos) { values[pos.y][pos.x] }

  def traceTrail(Vec2 pos, Set<Vec2> visited) {
    if (visited != null) {
      if (pos in visited) {
        return 0
      }
      visited.add(pos)
    }

    int value = get(pos)
    int score = 0
    if (value == 0) {
      score++
    }

    for (int dy in (-1..1)) {
      for (int dx in (-1..1)) {
        if (dy == 0 ^ dx == 0) {
          Vec2 neigh = new Vec2(pos.x + dx, pos.y + dy)
          if (neigh.y >= 0 && neigh.y < height && neigh.x >= 0 && neigh.x < width && get(neigh) == value - 1) {
            score += traceTrail(neigh, visited)
          }
        }
      }
    }

    return score
  }
}

if (args.length == 0) {
  println "Usage: day10 <path to values>"
  System.exit(1)
}

List<List<Integer>> values = new File(args[0]).text.lines().map { it.chars().map { it - (int) '0' }.toList() }.toList()
TopoMap topoMap = new TopoMap(values)

int part1 = 0
int part2 = 0

for (int y in 0..<topoMap.height) {
  for (int x in 0..<topoMap.width) {
    Vec2 pos = new Vec2(x, y)
    if (topoMap.get(pos) == 9) {
      part1 += topoMap.traceTrail(pos, new HashSet())
      part2 += topoMap.traceTrail(pos, null)
    }
  }
}

println "Part 1: $part1"
println "Part 2: $part2"
