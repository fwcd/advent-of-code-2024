#!/usr/bin/env lua

if #arg < 1 then
  print("Usage: day11 <path to input>")
  os.exit(1)
end

local stones = {}

for line in io.lines(arg[1]) do
  for raw in line:gmatch("%d+") do
    local stone = tonumber(raw)
    stones[stone] = (stones[stone] or 0) + 1
  end
end

for k, v in pairs(stones) do
  print(tostring(k) .. ' => ' .. tostring(v))
end
