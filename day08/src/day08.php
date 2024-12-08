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

  function inBounds(int $width, int $height): bool {
    return $this->x >= 0 && $this->x < $width && $this->y >= 0 && $this->y < $height;
  }

  function add(Vec2 $rhs): Vec2 {
    return new Vec2($this->x + $rhs->x, $this->y + $rhs->y);
  }

  function sub(Vec2 $rhs): Vec2 {
    return new Vec2($this->x - $rhs->x, $this->y - $rhs->y);
  }

  function scale(int $factor): Vec2 {
    return new Vec2($this->x * $factor, $this->y * $factor);
  }
}

function findFrequencyLocations(array $matrix, int $width, int $height): array {
  $freqLocs = [];

  for ($y = 0; $y < $height; $y++) {
    for ($x = 0; $x < $width; $x++) {
      $cell = $matrix[$y][$x];
      if ($cell != '.') {
        $freqLocs[$cell] = [...($freqLocs[$cell] ?? []), new Vec2($x, $y)];
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

function findAntinodes(array $freqLocs, int $width, int $height, bool $includeStart = true, int $maxRepeats = PHP_INT_MAX): array {
  $antinodes = [];

  foreach ($freqLocs as $freq => $locs) {
    for ($i = 0; $i < count($locs); $i++) {
      for ($j = $i + 1; $j < count($locs); $j++) {
        $diff = $locs[$j]->sub($locs[$i]);
        foreach ([-1 => $locs[$i], 1 => $locs[$j]] as $dir => $start) {
          if ($includeStart) {
            $antinodes["$start"] = true;
          }
          $delta = $diff->scale($dir);
          $pos = $start->add($delta);
          $k = 0;
          while ($k < $maxRepeats && $pos->inBounds($width, $height)) {
            $antinodes["$pos"] = true;
            $pos = $pos->add($delta);
            $k++;
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
$matrix = array_slice(preg_split('/\R/', $raw), 0, -1);

$height = count($matrix);
$width = strlen($matrix[0]);

$freqLocs = findFrequencyLocations($matrix, $width, $height);
$antennas = findAntennas($freqLocs, $width, $height);

foreach (array_keys(findAntinodes($freqLocs, $width, $height)) as $rawAntinode) {
  $antinode = Vec2::parse($rawAntinode);
  $matrix[$antinode->y][$antinode->x] = '#';
}

foreach ($matrix as $line) {
  echo "$line" . PHP_EOL;
}

$part1 = count(findAntinodes($freqLocs, $width, $height, false, 1));
echo "Part 1: $part1" . PHP_EOL;

$part2 = count(findAntinodes($freqLocs, $width, $height));
echo "Part 2: $part2" . PHP_EOL;
