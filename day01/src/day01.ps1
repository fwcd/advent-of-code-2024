#!/usr/bin/env pwsh

$input = Get-Content $args[0] | % { ,($_ -split '\s+') }
$left = $input | % { $_[0] } | Sort-Object
$right = $input | % { $_[1] } | Sort-Object
$pairs = (0..($input.Count - 1)) | % { [Math]::Abs($left[$_] - $right[$_]) }

$part1 = ($pairs | Measure-Object -Sum).Sum
Write-Output "Part 1: $part1"
