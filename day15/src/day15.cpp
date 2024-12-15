#include <iostream>
#include <fstream>
#include <stdexcept>
#include <string>
#include <vector>

template <typename T>
struct Vec2 {
  T x;
  T y;

  bool operator<=>(const Vec2<T> &rhs) const = default;

  Vec2<T> operator+(const Vec2<T> &rhs) const {
    return {x + rhs.x, y + rhs.y};
  }
};

enum class Inst : char {
  Left = '<',
  Up = '^',
  Right = '>',
  Down = 'v',
};

std::ostream &operator<<(std::ostream &os, Inst inst) {
  os << char(inst);
  return os;
}

struct Board {
  std::vector<std::string> rows;
  Vec2<int> robot = {-1, -1};

  int width() const {
    return rows[0].size();
  }

  int height() const {
    return rows.size();
  }

  bool in_bounds(Vec2<int> pos) const {
    return pos.x >= 0 && pos.x < width() && pos.y >= 0 && pos.y < height();
  }

  char operator[](Vec2<int> pos) const {
    return in_bounds(pos) ? rows[pos.y][pos.x] : '#';
  }

  char &operator[](Vec2<int> pos) {
    if (!in_bounds(pos)) throw std::runtime_error("Not in bounds");
    return rows[pos.y][pos.x];
  }

  void perform(Inst inst) {
    Vec2<int> dir;
    switch (inst) {
    case Inst::Left: dir = {-1, 0}; break;
    case Inst::Up: dir = {0, -1}; break;
    case Inst::Right: dir = {1, 0}; break;
    case Inst::Down: dir = {0, 1}; break;
    }

    Vec2<int> next = robot + dir;
    Vec2<int> end = next;
    while ((*this)[end] == 'O') {
      end = end + dir;
    }

    if ((*this)[end] != '#') {
      robot = next;
      if ((*this)[next] == 'O' && (*this)[end] == '.') {
        std::swap((*this)[next], (*this)[end]);
      }
    }
  }

  int sum_box_coords() const {
    int sum = 0;

    for (int y = 0; y < height(); y++) {
      for (int x = 0; x < width(); x++) {
        if ((*this)[{x, y}] == 'O') {
          sum += 100 * y + x;
        }
      }
    }

    return sum;
  }
};

std::ostream &operator<<(std::ostream &os, const Board &board) {
  for (int y = 0; y < board.height(); y++) {
    for (int x = 0; x < board.width(); x++) {
      if (board.robot == Vec2<int>({x, y})) {
        os << '@';
      } else {
        os << board[{x, y}];
      }
    }
    os << std::endl;
  }
  return os;
}

struct State {
  Board board1;
  std::vector<Inst> insts;

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
              state.board1.robot = {x, y};
              row.push_back('.');
            } else {
              row.push_back(cell);
            }
            x++;
          }
          state.board1.rows.push_back(row);
        }
      } else {
        for (char raw_inst : line) {
          state.insts.push_back(Inst(raw_inst));
        }
      }
      y++;
    }

    return state;
  }

  void run() {
    for (Inst inst : insts) {
      board1.perform(inst);
    }
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

  // std::cout << state.board;
  // for (Inst inst : state.insts) {
  //   state.board.perform(inst);
  //   std::cout << "After " << inst << ":" << std::endl << state.board;
  // }
  state.run();
  std::cout << "Part 1: " << state.board1.sum_box_coords() << std::endl;

  return 0;
}
