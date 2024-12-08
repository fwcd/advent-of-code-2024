<?php

class Vec2 {
  public int $x;
  public int $y;

  function __construct(int $x = 0, int $y = 0) {
    $this->x = $x;
    $this->y = $y;
  }

  static function parse(string $raw): Vec2 {
    $split = explode(",", $raw);
    return new Vec2(intval($split[0]), intval($split[1]));
  }

  function __toString(): string {
    return "$this->x,$this->y";
  }

  function add(Vec2 $rhs): Vec2 {
    return new Vec2($this->x + $rhs->x, $this->y + $rhs->y);
  }

  function sub(Vec2 $rhs): Vec2 {
    return new Vec2($this->x - $rhs->x, $this->y - $rhs->y);
  }
}

function findFrequencyLocations(array $matrix, int $width, int $height): array {
  $freqLocs = [];

  for ($y = 0; $y < $height; $y++) {
    if (strlen($matrix[$y]) > 0) {
      for ($x = 0; $x < $width; $x++) {
        $cell = $matrix[$y][$x];
        if ($cell != '.') {
          $freqLocs[$cell] = [...($freqLocs[$cell] ?? []), new Vec2($x, $y)];
        }
      }
    }
  }

  return $freqLocs;
}

function findAntennas(array $freqLocs, int $width, int $height): array {
  $antennas = [];

  foreach ($freqLocs as $freq => $locs) {
    foreach ($locs as $loc) {
      $antennas["$loc"] = true;
    }
  }
  
  return $antennas;
}

function findAntinodes(array $antennas, array $freqLocs, int $width, int $height): array {
  $antinodes = [];

  foreach ($freqLocs as $freq => $locs) {
    for ($i = 0; $i < count($locs); $i++) {
      for ($j = $i + 1; $j < count($locs); $j++) {
        $diff = $locs[$j]->sub($locs[$i]);
        echo "{$locs[$i]} to {$locs[$j]} -> $diff" . PHP_EOL;
        foreach ([$locs[$i]->sub($diff), $locs[$j]->add($diff)] as $antinode) {
          if (!array_key_exists("$antinode", $antennas)) {
            $antinodes["$antinode"] = true;
          }
        }
      }
    }
  }

  return $antinodes;
}

if ($argc <= 1) {
  echo "Usage: day08 <path to input>" . PHP_EOL;
  exit(1);
}

$filePath = $argv[1];
$raw = file_get_contents($filePath);
$matrix = preg_split('/\R/', $raw);

$height = count($matrix);
$width = strlen($matrix[0]);

$freqLocs = findFrequencyLocations($matrix, $width, $height);
$antennas = findAntennas($freqLocs, $width, $height);
$antinodes = findAntinodes($antennas, $freqLocs, $width, $height);

foreach (array_keys($antinodes) as $rawAntinode) {
  $antinode = Vec2::parse($rawAntinode);
  $matrix[$antinode->y][$antinode->x] = '#';
}

foreach ($matrix as $line) {
  echo "$line" . PHP_EOL;
}

$part1 = count($antinodes);
echo "Part 1: $part1" . PHP_EOL;
