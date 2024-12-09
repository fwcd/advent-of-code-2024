#!/usr/bin/env node

const fs = require('fs');

function pretty(blocks) {
  return blocks.map(b => `${`${b.value}`.repeat(b.count)}${'.'.repeat(b.free)}`).join('');
}

function defragment1(blocks) {
  blocks = JSON.parse(JSON.stringify(blocks));

  for (let i = 0; i < blocks.length - 1; i++) {
    const current = blocks[i];
    for (let j = blocks.length - 1; j > i; j--) {
      const candidate = blocks[j];
      const moved = Math.min(candidate.count, current.free);
      if (moved > 0) {
        blocks.splice(i + 1, 0, {
          value: candidate.value,
          count: moved,
          free: current.free - moved,
        });
        current.free = 0;
        candidate.count -= moved;
        break;
      }
    }
  }

  return blocks;
}

function defragment2(blocks) {
  blocks = JSON.parse(JSON.stringify(blocks));

  for (let j = blocks.length - 1; j >= 0; j--) {
    const candidate = blocks[j];
    for (let i = 0; i < j; i++) {
      const current = blocks[i];
      const moved = Math.min(candidate.count, current.free);
      if (moved > 0 && moved === candidate.count) {
        blocks.splice(i + 1, 0, {
          value: candidate.value,
          count: moved,
          free: current.free - moved,
        });
        j++; // j is shifting up due to the splice/insert above
        current.free = 0;
        candidate.count -= moved;
        blocks[j].free += moved;
        break;
      }
    }
  }

  return blocks;
}

function checksum(blocks) {
  let sum = 0;
  let i = 0;
  for (const block of blocks) {
    for (let j = 0; j < block.count; j++) {
      sum += i * block.value;
      i++;
    }
    i += block.free;
  }
  return sum;
}

if (process.argv.length <= 2) {
  console.log('Usage: day09 <path to input>');
  process.exit(1);
}

const rawInput = fs.readFileSync(process.argv[2], { encoding: 'utf-8' }).trim();
const input = [...rawInput].map(c => parseInt(c));
const blocks = [...Array(Math.ceil(input.length / 2))]
  .map((_, i) => ({
    value: i,
    count: input[2 * i],
    free: input[2 * i + 1] ?? 0
  }));

const blocks1 = defragment1(blocks);
const blocks2 = defragment2(blocks);

const part1 = checksum(blocks1);
console.log(`Part 1: ${part1}`);

const part2 = checksum(blocks2);
console.log(`Part 2: ${part2}`);
