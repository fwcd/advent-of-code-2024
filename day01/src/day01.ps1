#!/usr/bin/env pwsh

function Sum {
  param ($list)
  ($list | Measure-Object -Sum).Sum
}

$input = Get-Content $args[0] | % { ,($_ -split '\s+') }
$left = $input | % { $_[0] } | Sort-Object
$right = $input | % { $_[1] } | Sort-Object

$part1 = Sum $((0..($input.Count - 1)) | % { [Math]::Abs($left[$_] - $right[$_]) })
Write-Output "Part 1: $part1"

$freqs = $right | Group-Object -AsHashTable
$part2 = Sum $($left | % { [int]$_ * $freqs[$_].Count })
Write-Output "Part 2: $part2"
