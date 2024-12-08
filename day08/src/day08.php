<?php

if ($argc <= 1) {
  echo "Usage: day08 <path to input>" . PHP_EOL;
  exit(1);
}

$filePath = $argv[1];
$raw = file_get_contents($filePath);
$input = preg_split('/\R/', $raw);

foreach ($input as $line) {
  echo $line . PHP_EOL;
}
