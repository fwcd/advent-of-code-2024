#!/usr/bin/env python3

import fileinput
import re
import numpy as np

mats = []
vecs = []

cols = []

for line in fileinput.input():
    if m := re.search(r'Button .: X\+(\d+), Y\+(\d+)', line):
        cols.append(list(map(int, [m[1], m[2]])))
    elif m := re.search(r'Prize: X=(\d+), Y=(\d+)', line):
        vecs.append(np.array(list(map(int, [m[1], m[2]]))))
    elif cols:
        mats.append(np.array(cols).T)
        cols = []

def solve(offset: np.ndarray) -> int:
    lcombs = [np.linalg.inv(m) @ (v + offset) for m, v in zip(mats, vecs)]
    return sum(int(np.sum(np.array([3, 1]) * np.round(lcomb))) for lcomb in lcombs if np.sum(np.abs(np.round(lcomb) - lcomb)) < 0.001)

print('Part 1:', solve(np.array([0, 0])))
print('Part 2:', solve(10000000000000 * np.array([1, 1])))
