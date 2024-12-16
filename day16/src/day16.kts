#!/usr/bin/env kotlin

import java.io.File
import kotlin.system.exitProcess

if (args.isEmpty()) {
  println("Usage: day16 <path to input>")
  exitProcess(1)
}

val lines = File(args[0]).readLines()
