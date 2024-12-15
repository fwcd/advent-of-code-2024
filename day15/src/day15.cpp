#include <iostream>
#include <fstream>
#include <string>
#include <vector>

struct Board {
  std::vector<std::string> rows;
  std::array<int, 2> robot;
};

int main(int argc, char *argv[]) {
  if (argc == 1) {
    std::cerr << "Usage: " << argv[0] << " <path to input>" << std::endl;
    return 1;
  }

  Board board;
  std::string instructions;

  {
    std::ifstream file;
    file.open(argv[1]);

    bool in_board = true;
    int y = 0;
    for (std::string line; std::getline(file, line);) {
      if (in_board) {
        if (line.empty()) {
          in_board = false;
        } else {
          std::string row;
          int x = 0;
          for (char cell : line) {
            if (cell == '@') {
              board.robot = {x, y};
              row.push_back('.');
            } else {
              row.push_back(cell);
            }
            x++;
          }
          board.rows.push_back(row);
        }
      } else {
        instructions += line;
      }
      y++;
    }
  }

  std::cout << "Robot: " << board.robot[0] << ", " << board.robot[1] << std::endl;
  for (const std::string &row : board.rows) {
    std::cout << "Row: " << row << std::endl;
  }
  std::cout << "Instructions: " << instructions << std::endl;

  return 0;
}
