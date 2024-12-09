const fs = require('fs');

function defragment(blocks, wholeFiles) {
  blocks = JSON.parse(JSON.stringify(blocks));

  for (let i = 0; i < blocks.length; i++) {
    const current = blocks[i];
    for (let j = blocks.length - 1; j > i; j--) {
      const candidate = blocks[j];
      if (current.free > 0) {
        const moved = Math.min(candidate.count, current.free);
        if (moved > 0 && (!wholeFiles || moved === candidate.count)) {
          blocks.splice(i + 1, 0, {
            value: candidate.value,
            count: moved,
            free: current.free - moved,
          });
          current.free = 0;
          candidate.count -= moved;
          changed = true;
        }
        if (candidate.count === 0) {
          // NOTE: candidate shifted from j to j + 1 at earlier splice
          blocks.splice(j + 1, 1);
        }
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

const blocks1 = defragment(blocks, false);
console.log(blocks1);

const blocks2 = defragment(blocks, true);
console.log(blocks2);

const part1 = checksum(blocks1);
console.log(`Part 1: ${part1}`);

const part2 = checksum(blocks2);
console.log(`Part 2: ${part2}`);
