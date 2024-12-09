const fs = require('fs');

if (process.argv.length <= 2) {
  console.log('Usage: day09 <path to input>');
  process.exit(1);
}

const input = fs.readFileSync(process.argv[2], { encoding: 'utf-8' }).trim();

console.log(input);
