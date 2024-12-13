#!/usr/bin/env python3

import fileinput
import re
import numpy as np

mats = []
vecs = []

cols = []

for line in fileinput.input():
    if m := re.search(r'Button .: X\+(\d+), Y\+(\d+)', line):
        cols.append([int(m[1]), int(m[2])])
    elif m := re.search(r'Prize: X=(\d+), Y=(\d+)', line):
        vecs.append(np.array(list([int(m[1]), int(m[2])])))
    elif cols:
        mats.append(np.array(cols).T)
        cols = []

def solve(offset: np.ndarray) -> int:
    lcombs = [np.linalg.inv(m) @ (v + offset) for m, v in zip(mats, vecs)]
    solvable = [np.round(lcomb).astype(int) for lcomb in lcombs if np.sum(np.abs(np.round(lcomb) - lcomb)) < 0.001]
    return sum(3 * lcomb[0] + lcomb[1] for lcomb in solvable)

print('Part 1:', solve(np.array([0, 0])))
print('Part 2:', solve(10000000000000 * np.array([1, 1])))
