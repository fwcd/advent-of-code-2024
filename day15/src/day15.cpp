#include <iostream>
#include <fstream>
#include <stdexcept>
#include <string>
#include <unordered_set>
#include <vector>

template <typename T>
struct Vec2 {
  T x;
  T y;

  bool operator<=>(const Vec2<T> &rhs) const = default;

  Vec2<T> operator+(const Vec2<T> &rhs) const {
    return {x + rhs.x, y + rhs.y};
  }

  Vec2<T> operator-(const Vec2<T> &rhs) const {
    return {x - rhs.x, y - rhs.y};
  }

  void operator+=(const Vec2<T> &rhs) {
    x += rhs.x;
    y += rhs.y;
  }

  void operator-=(const Vec2<T> &rhs) {
    x -= rhs.x;
    y -= rhs.y;
  }
};

template <typename T>
std::ostream &operator<<(std::ostream &os, Vec2<T> vec) {
  return os << vec.x << ", " << vec.y;
}

template <typename T>
struct std::hash<Vec2<T>> {
  std::size_t operator()(const Vec2<T> &vec) const {
    return std::hash<T>()(vec.x) ^ std::hash<T>()(vec.y);
  }
};

enum class Inst : char {
  Left = '<',
  Up = '^',
  Right = '>',
  Down = 'v',
};

Vec2<int> inst_dir(Inst inst) {
  switch (inst) {
  case Inst::Left: return {-1, 0};
  case Inst::Up: return {0, -1};
  case Inst::Right: return {1, 0};
  case Inst::Down: return {0, 1};
  }
}

std::ostream &operator<<(std::ostream &os, Inst inst) {
  return os << char(inst);
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

  bool is_box(Vec2<int> pos, bool include_end = true) const {
    char cell = (*this)[pos];
    return cell == 'O' || cell == '[' || (include_end && cell == ']');
  }

  bool is_space(Vec2<int> pos) const {
    return (*this)[pos] == '.';
  }

  bool is_wall(Vec2<int> pos) const {
    return (*this)[pos] == '#';
  }

  void dfs_attached(Vec2<int> pos, Inst inst, std::unordered_set<Vec2<int>> &visited) const {
    if (visited.contains(pos) || !in_bounds(pos) || !is_box(pos)) {
      return;
    }
    visited.insert(pos);

    char cell = (*this)[pos];
    switch (cell) {
    case '[':
      dfs_attached({pos.x + 1, pos.y}, inst, visited);
      break;
    case ']':
      dfs_attached({pos.x - 1, pos.y}, inst, visited);
      break;
    }

    Vec2<int> dir = inst_dir(inst);
    dfs_attached(pos + dir, inst, visited);
  }

  void perform(Inst inst) {
    Vec2<int> dir = inst_dir(inst);
    Vec2<int> next = robot + dir;

    std::unordered_set<Vec2<int>> attached;
    dfs_attached(next, inst, attached);

    for (Vec2<int> pos : attached) {
      if (is_wall(pos + dir)) {
        return;
      }
    }

    Board board = *this;
    for (Vec2<int> pos : attached) {
      board[pos] = '.';
    }
    for (Vec2<int> pos : attached) {
      board[pos + dir] = (*this)[pos];
    }
    *this = board;

    robot = next;
  }

  int sum_box_coords() const {
    int sum = 0;

    for (int y = 0; y < height(); y++) {
      for (int x = 0; x < width(); x++) {
        if (is_box({x, y}, /*include_end=*/false)) {
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
  Board board2;
  std::vector<Inst> insts;

  static State parse_from(std::istream &istream) {
    State state;

    bool in_board = true;
    for (std::string line; std::getline(istream, line);) {
      if (in_board) {
        if (line.empty()) {
          in_board = false;
        } else {
          std::string row1;
          std::string row2;
          for (char cell : line) {
            if (cell == '@') {
              int x1 = row1.size();
              int x2 = row2.size();
              int y1 = state.board1.rows.size();
              int y2 = state.board2.rows.size();
              state.board1.robot = {x1, y1};
              state.board2.robot = {x2, y2};
              row1.push_back('.');
              row2 += "..";
            } else {
              row1.push_back(cell);
              if (cell == 'O') {
                row2 += "[]";
              } else {
                row2.push_back(cell);
                row2.push_back(cell);
              }
            }
          }
          state.board1.rows.push_back(row1);
          state.board2.rows.push_back(row2);
        }
      } else {
        for (char raw_inst : line) {
          state.insts.push_back(Inst(raw_inst));
        }
      }
    }

    return state;
  }

  void run() {
    for (Inst inst : insts) {
      board1.perform(inst);
      board2.perform(inst);
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

  std::cout << state.board1;
  std::cout << state.board2;
  for (Inst inst : state.insts) {
    state.board2.perform(inst);
    std::cout << "After " << inst << ": " << std::endl << state.board2;
  }
  // state.run();
  // std::cout << "Part 1: " << state.board1.sum_box_coords() << std::endl;
  // std::cout << "Part 2: " << state.board2.sum_box_coords() << std::endl;

  return 0;
}
