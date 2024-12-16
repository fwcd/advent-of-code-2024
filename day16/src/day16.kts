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

data class Node(val total: Int, val pos: Vec2, val dir: Vec2)

data class Board(val rows: List<String>) {
  val height: Int get() = rows.size
  val width: Int get() = rows[0].length
  
  operator fun get(pos: Vec2): Char = rows[pos.y][pos.x]

  fun shortestPath(start: Vec2, end: Vec2): Int {
    val queue = PriorityQueue<Node>(11) { l, r -> r.total - l.total }
    val visited = mutableSetOf<Pair<Vec2, Vec2>>()

    val startDir: Vec2 = Vec2(0, -1)
    queue.add(Node(0, start, startDir))
    visited.add(Pair(start, startDir))

    while (!queue.isEmpty()) {
      val node = queue.poll()
      println("${node.pos} and ${this[node.pos]}")
      if (node.pos == end) {
        return node.total
      }
      visited.add(Pair(node.pos, node.dir))
      for (dir in listOf(node.dir, node.dir.rotateCW(), node.dir.rotateCCW())) {
        val next = node.pos + dir
        val weight = if (dir == node.dir) 1 else 1001
        if (Pair(next, dir) !in visited && this[next] != '#') {
          queue.add(Node(node.total + weight, next, dir))
        }
      }
    }

    throw RuntimeException("No path found")
  }
}

val board = Board(File(args[0]).readLines())

// TODO: Don't hardcode these
val start = Vec2(1, board.height - 2)
val end = Vec2(board.width - 2, 1)

print("Part 1: ${board.shortestPath(start, end)}")
