#include <stdio.h>
#include <stdbool.h>
#include <stdlib.h>
#include <string.h>

#define GRID_SIZE 140
#define LENGTH(S) (sizeof(S) / sizeof(char) - 1)

struct Grid {
  char data[GRID_SIZE][GRID_SIZE];
  int width;
  int height;
};

struct Solution {
  int part1;
  int part2;
};

bool in_bounds(struct Grid grid, int i, int j) {
  return i >= 0 && i < grid.height && j >= 0 && j < grid.width;
}

bool matches_at(struct Grid grid, int i, int j, int di, int dj, const char pattern[], int length) {
  for (int k = 0; k < length; k++) {
    int ni = i + k * di;
    int nj = j + k * dj;
    if (!in_bounds(grid, ni, nj) || grid.data[ni][nj] != pattern[k]) {
      return false;
    }
  }
  return true;
}

bool matches_xmas_at(struct Grid grid, int i, int j, int di, int dj) {
  const char XMAS[] = "XMAS";
  return matches_at(grid, i, j, di, dj, XMAS, LENGTH(XMAS));
}

int count_xmas1_at(struct Grid grid, int i, int j) {
  return matches_xmas_at(grid, i, j,  1, 0) + matches_xmas_at(grid, i, j,  0,  1)
       + matches_xmas_at(grid, i, j, -1, 0) + matches_xmas_at(grid, i, j,  0, -1)
       + matches_xmas_at(grid, i, j,  1, 1) + matches_xmas_at(grid, i, j, -1, -1)
       + matches_xmas_at(grid, i, j, -1, 1) + matches_xmas_at(grid, i, j,  1, -1);
}

bool matches_mas_at(struct Grid grid, int i, int j, int di, int dj) {
  const char MAS[] = "MAS";
  return matches_at(grid, i, j, di, dj, MAS, LENGTH(MAS));
}

bool has_xmas2_at(struct Grid grid, int i, int j) {
  return (matches_mas_at(grid, i - 1, j - 1,  1,  1) && matches_mas_at(grid, i + 1, j - 1, -1,  1))
      || (matches_mas_at(grid, i + 1, j - 1, -1,  1) && matches_mas_at(grid, i + 1, j + 1, -1, -1))
      || (matches_mas_at(grid, i - 1, j - 1,  1,  1) && matches_mas_at(grid, i - 1, j + 1,  1, -1))
      || (matches_mas_at(grid, i - 1, j + 1,  1, -1) && matches_mas_at(grid, i + 1, j + 1, -1, -1));
}

struct Grid parse_grid(FILE *input) {
  struct Grid grid = { .width = 0, .height = 0 };
  char *line = NULL;
  size_t length = 0;
  size_t size = 0;

  while ((length = getline(&line, &size, input)) != -1) {
    if (length > 0) {
      memcpy(&grid.data[grid.height], line, length);
      grid.width = length - 1;
      grid.height++;
    }
  }

  free(line);
  return grid;
}

struct Solution solve(struct Grid grid) {
  struct Solution solution = { .part1 = 0, .part2 = 0 };
  for (int i = 0; i < grid.height; i++) {
    for (int j = 0; j < grid.width; j++) {
      solution.part1 += count_xmas1_at(grid, i, j);
      solution.part2 += has_xmas2_at(grid, i, j);
    }
  }
  return solution;
}

int main(int argc, const char *argv[]) {
  if (argc <= 1) {
    fprintf(stderr, "Usage: %s <path to input>\n", argv[0]);
    return 1;
  }

  const char *input_path = argv[1];
  FILE *input = fopen(input_path, "r");
  if (input == NULL) {
    fprintf(stderr, "Could not open input\n");
    return 1;
  }

  struct Grid grid = parse_grid(input);
  printf("Grid is of width %d and height %d\n", grid.width, grid.height);
  fclose(input);

  struct Solution solution = solve(grid);
  printf("Part 1: %d\n", solution.part1);
  printf("Part 2: %d\n", solution.part2);

  return 0;
}
