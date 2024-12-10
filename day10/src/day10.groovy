#!/usr/bin/env groovy

record Vec2(int x, int y) {}

class TopoMap {
  private List<List<Integer>> values

  int part1 = 0

  TopoMap(List<List<Integer>> values) {
    this.values = values
  }

  def getHeight() { values.size() }

  def getWidth() { values[0].size() }

  def get(Vec2 pos) { values[pos.y][pos.x] }

  def traceTrail(Vec2 pos, Set<Vec2> visited = new HashSet()) {
    if (pos in visited) {
      return
    }

    visited.add(pos)

    int value = get(pos)
    if (value == 0) {
      part1++
    }

    for (int dy in (-1..1)) {
      for (int dx in (-1..1)) {
        if (dy == 0 ^ dx == 0) {
          Vec2 neigh = new Vec2(pos.x + dx, pos.y + dy)
          if (neigh.y >= 0 && neigh.y < height && neigh.x >= 0 && neigh.x < width && get(neigh) == value - 1) {
            traceTrail(neigh, visited)
          }
        }
      }
    }
  }
}

if (args.length == 0) {
  println "Usage: day10 <path to values>"
  System.exit(1)
}

List<List<Integer>> values = new File(args[0]).text
  .lines()
  .map { it.chars().map { it - (int) '0' }.toList() }
  .toList()

TopoMap topoMap = new TopoMap(values)

for (int y in 0..<topoMap.height) {
  for (int x in 0..<topoMap.width) {
    Vec2 pos = new Vec2(x, y)
    if (topoMap.get(pos) == 9) {
      topoMap.traceTrail(pos)
    }
  }
}

println "Part 1: $topoMap.part1"
