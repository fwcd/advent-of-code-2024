#include <iostream>
#include <fstream>
#include <string>

int main(int argc, char *argv[]) {
  if (argc == 1) {
    std::cerr << "Usage: " << argv[0] << " <path to input>" << std::endl;
    return 1;
  }

  std::vector<std::string> board;
  std::string instructions;

  {
    std::ifstream file;
    file.open(argv[1]);

    bool in_board = true;
    for (std::string line; std::getline(file, line);) {
      if (in_board) {
        if (line.empty()) {
          in_board = false;
        } else {
          board.push_back(line);
        }
      } else {
        instructions += line;
      }
    }
  }

  for (const std::string &line : board) {
    std::cout << "Line: " << line << std::endl;
  }
  std::cout << "Instructions: " << instructions << std::endl;

  return 0;
}
