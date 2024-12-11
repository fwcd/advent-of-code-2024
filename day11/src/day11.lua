#!/usr/bin/env lua

function copy(table)
  local copied = {}
  for k, v in pairs(table) do
    copied[k] = v
  end
  return copied
end

function dump(table)
  for k, v in pairs(table) do
    print(tostring(k) .. ' => ' .. tostring(v))
  end
end

function add(stone, n, stones)
  stones[stone] = (stones[stone] or 0) + n
end

function count(stones)
  local total = 0
  for stone, n in pairs(stones) do
    total = total + n
  end
  return total
end

function simulate(stones, blinks)
  for i = 1, blinks do
    local new_stones = {}
    for stone, n in pairs(stones) do
      if stone == 0 then
        add(1, n, new_stones)
      else
        raw = tostring(stone)
        if #raw % 2 == 0 then
          add(tonumber(raw:sub(0, #raw / 2)), n, new_stones)
          add(tonumber(raw:sub(#raw / 2 + 1, #raw)), n, new_stones)
        else
          add(stone * 2024, n, new_stones)
        end
      end
    end
    stones = new_stones
  end

  return stones
end

if #arg < 1 then
  print("Usage: day11 <path to input>")
  os.exit(1)
end

local stones = {}

for line in io.lines(arg[1]) do
  for raw in line:gmatch("%d+") do
    local stone = tonumber(raw)
    add(stone, 1, stones)
  end
end

part1 = count(simulate(stones, 25))
print('Part 1: ' .. tostring(part1))
