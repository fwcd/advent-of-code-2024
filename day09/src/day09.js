const fs = require('fs');

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

for (let i = 0; i < blocks.length; i++) {
  const current = blocks[i];
  const last = blocks[blocks.length - 1];
  if (current.free > 0) {
    const moved = Math.min(last.count, current.free);
    if (moved > 0) {
      blocks.splice(i + 1, 0, {
        value: last.value,
        count: moved,
        free: current.free - moved,
      });
      current.free = 0;
      last.count -= moved;
    }
    if (last.count === 0) {
      blocks.pop();
    }
  }
}

console.log(blocks);

let part1 = 0;
let i = 0;
for (const block of blocks) {
  for (let j = 0; j < block.count; j++) {
    part1 += i * block.value;
    i++;
  }
}

console.log(`Part 1: ${part1}`);
