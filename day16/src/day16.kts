#!/usr/bin/env kotlin

import java.io.File
import java.util.PriorityQueue
import kotlin.system.exitProcess

if (args.isEmpty()) {
  println("Usage: day16 <path to input>")
  exitProcess(1)
}

data class Vec2(val x: Int, val y: Int) {
  fun rotateCW() = Vec2(-y, x)

  fun rotateCCW() = Vec2(y, -x)

  operator fun plus(rhs: Vec2) = Vec2(x + rhs.x, y + rhs.y)
}

data class Node(val total: Int, val visited: Set<Vec2>, val pos: Vec2, val dir: Vec2)

data class ShortestPaths(val length: Int, val visited: Set<Vec2>)

data class Board(val rows: List<String>) {
  val height: Int get() = rows.size
  val width: Int get() = rows[0].length
  
  operator fun get(pos: Vec2): Char = rows[pos.y][pos.x]

  fun shortestPaths(start: Vec2, end: Vec2): ShortestPaths {
    // Your run-of-the-mill Dijkstra implementation below

    val queue = PriorityQueue<Node>(11) { l, r -> l.total - r.total }
    val visited = mutableSetOf<Pair<Vec2, Vec2>>()

    val startDir: Vec2 = Vec2(1, 0)
    queue.add(Node(0, setOf(start), start, startDir))
    visited.add(Pair(start, startDir))

    var shortestTotal: Int? = null
    val shortestPaths = mutableSetOf<Vec2>()

    while (!queue.isEmpty()) {
      val node = queue.poll()
      if (shortestTotal?.let { node.total > it } ?: false) {
        break
      }
      if (node.pos == end) {
        shortestTotal = node.total
        shortestPaths.addAll(node.visited)
      }
      visited.add(Pair(node.pos, node.dir))

      // Step
      val next = node.pos + node.dir
      if (Pair(next, node.dir) !in visited && this[next] != '#') {
        queue.add(Node(node.total + 1, node.visited.union(listOf(next)), next, node.dir))
      }

      // Rotate
      for (dir in listOf(node.dir.rotateCW(), node.dir.rotateCCW())) {
        if (Pair(node.pos, dir) !in visited) {
          queue.add(Node(node.total + 1000, node.visited, node.pos, dir))
        }
      }
    }

    return shortestTotal?.let { ShortestPaths(it, shortestPaths) } ?: throw RuntimeException("No path found")
  }
}

val board = Board(File(args[0]).readLines())

// TODO: Don't hardcode these
val start = Vec2(1, board.height - 2)
val end = Vec2(board.width - 2, 1)

val result = board.shortestPaths(start, end)
println("Part 1: ${result.length}")
println("Part 2: ${result.visited.size}")
