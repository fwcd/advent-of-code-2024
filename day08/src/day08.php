<?php

class Vec2 {
  public int $x;
  public int $y;

  function __construct(int $x = 0, int $y = 0) {
    $this->x = $x;
    $this->y = $y;
  }

  function __toString(): string {
    return "($this->x, $this->y)";
  }
}

function findFrequencyLocations(array $matrix): array {
  $freqLocs = [];

  $height = count($matrix);
  $width = strlen($matrix[0]);

  for ($y = 0; $y < $height; $y++) {
    for ($x = 0; $x < $width; $x++) {
      $cell = $matrix[$y][$x];
      if ($cell != '.' && $cell != '') {
        $freqLocs[$cell] = [...($freqLocs[$cell] ?? []), new Vec2($x, $y)];
      }
    }
  }

  return $freqLocs;
}

if ($argc <= 1) {
  echo "Usage: day08 <path to input>" . PHP_EOL;
  exit(1);
}

$filePath = $argv[1];
$raw = file_get_contents($filePath);
$input = preg_split('/\R/', $raw);

$freqLocs = findFrequencyLocations($input);
var_dump($freqLocs);
