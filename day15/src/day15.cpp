#include <iostream>
#include <fstream>
#include <string>
#include <vector>

struct State {
  std::vector<std::string> board;
  std::string instructions;
  std::array<int, 2> robot = {-1, -1};

  static State parse_from(std::istream &istream) {
    State state;

    bool in_board = true;
    int y = 0;
    for (std::string line; std::getline(istream, line);) {
      if (in_board) {
        if (line.empty()) {
          in_board = false;
        } else {
          std::string row;
          int x = 0;
          for (char cell : line) {
            if (cell == '@') {
              state.robot = {x, y};
              row.push_back('.');
            } else {
              row.push_back(cell);
            }
            x++;
          }
          state.board.push_back(row);
        }
      } else {
        state.instructions += line;
      }
      y++;
    }

    return state;
  }
};

int main(int argc, char *argv[]) {
  if (argc == 1) {
    std::cerr << "Usage: " << argv[0] << " <path to input>" << std::endl;
    return 1;
  }

  State state;

  {
    std::ifstream file;
    file.open(argv[1]);
    state = State::parse_from(file);
  }

  std::cout << "Robot: " << state.robot[0] << ", " << state.robot[1] << std::endl;
  for (const std::string &row : state.board) {
    std::cout << "Row: " << row << std::endl;
  }
  std::cout << "Instructions: " << state.instructions << std::endl;

  return 0;
}
