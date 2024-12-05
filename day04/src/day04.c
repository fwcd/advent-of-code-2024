#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define GRID_SIZE 140

struct Grid {
  char data[GRID_SIZE][GRID_SIZE];
  int width;
  int height;
};

struct Grid parse_grid(FILE *input) {
  struct Grid grid = { .width = 0, .height = 0 };
  char *line = NULL;
  size_t length = 0;
  size_t size = 0;

  while ((length = getline(&line, &size, input)) != -1) {
    if (length > 0) {
      memcpy(&grid.data[grid.height], line, length);
      grid.width = length;
      grid.height++;
    }
  }

  free(line);
  return grid;
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
  fclose(input);

  return 0;
}
