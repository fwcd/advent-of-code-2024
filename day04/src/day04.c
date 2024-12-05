#include <stdio.h>
#include <stdbool.h>
#include <stdlib.h>
#include <string.h>

const char XMAS[] = "XMAS";

#define GRID_SIZE 140
#define XMAS_LENGTH (sizeof(XMAS) / sizeof(char) - 1)

struct Grid {
  char data[GRID_SIZE][GRID_SIZE];
  int width;
  int height;
};

bool in_bounds(struct Grid grid, int i, int j) {
  return i >= 0 && i < grid.height && j >= 0 && j < grid.width;
}

bool has_xmas_at(struct Grid grid, int i, int j, int di, int dj) {
  for (int k = 0; k < XMAS_LENGTH; k++) {
    int ni = i + k * di;
    int nj = j + k * dj;
    if (!in_bounds(grid, ni, nj) || grid.data[ni][nj] != XMAS[k]) {
      if (k > 0 && in_bounds(grid, ni, nj)) {
        printf("Failed at %d, %d -> %d, %d (%c != %c)\n", i, j, ni, nj, grid.data[ni][nj], XMAS[k]);
      }
      return false;
    }
  }
  return true;
}

int count_xmas_at(struct Grid grid, int i, int j) {
  return has_xmas_at(grid, i, j,  1, 0) + has_xmas_at(grid, i, j,  0,  1)
       + has_xmas_at(grid, i, j, -1, 0) + has_xmas_at(grid, i, j,  0, -1)
       + has_xmas_at(grid, i, j,  1, 1) + has_xmas_at(grid, i, j, -1, -1)
       + has_xmas_at(grid, i, j, -1, 1) + has_xmas_at(grid, i, j,  1, -1);
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

int count_xmas(struct Grid grid) {
  int count = 0;
  for (int i = 0; i < grid.height; i++) {
    for (int j = 0; j < grid.width; j++) {
      count += count_xmas_at(grid, i, j);
    }
  }
  return count;
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

  int part1 = count_xmas(grid);
  printf("Part 1: %d\n", part1);

  return 0;
}
