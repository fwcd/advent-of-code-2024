const std = @import("std");

const allocator = std.heap.page_allocator;

const List = std.ArrayList;
const Map = std.AutoHashMap;
const String = []u8;
const Matrix = List(String);
const Vec2 = struct { x: i32, y: i32 };
const Guard = struct { pos: Vec2, dir: Vec2 };

fn Set(comptime T: type) type {
    return Map(T, void);
}

fn width(matrix: Matrix) usize {
    return matrix.items[0].len;
}

fn height(matrix: Matrix) usize {
    return matrix.items.len;
}

fn vecAdd(a: Vec2, b: Vec2) Vec2 {
    return .{ .x = a.x + b.x, .y = a.y + b.y };
}

fn turnRight(dir: Vec2) Vec2 {
    return .{ .x = -dir.y, .y = dir.x };
}

fn step(guard: Guard) Guard {
    return .{ .pos = vecAdd(guard.pos, guard.dir), .dir = guard.dir };
}

fn inBounds(pos: Vec2, matrix: Matrix) bool {
    return pos.x >= 0 and pos.x < width(matrix) and pos.y >= 0 and pos.y < height(matrix);
}

fn get(pos: Vec2, matrix: Matrix) u8 {
    return matrix.items[@intCast(pos.y)][@intCast(pos.x)];
}

fn parseDirection(c: u8) ?Vec2 {
    return switch (c) {
        '^' => .{ .x = 0, .y = -1 },
        'v' => .{ .x = 0, .y = 1 },
        '<' => .{ .x = -1, .y = 0 },
        '>' => .{ .x = 1, .y = 0 },
        else => null,
    };
}

fn findStart(matrix: Matrix) Guard {
    for (0..height(matrix)) |y| {
        for (0..width(matrix)) |x| {
            const dir = parseDirection(matrix.items[y][x]);
            if (dir != null) {
                return .{ .pos = .{ .x = @intCast(x), .y = @intCast(y) }, .dir = dir.? };
            }
        }
    }
    std.debug.panic("Could not find start", .{});
}

fn patrol(matrix: Matrix) !Set(Vec2) {
    var visited = Set(Vec2).init(allocator);
    var guard = findStart(matrix);

    while (inBounds(guard.pos, matrix)) {
        try visited.put(guard.pos, {});
        const next = step(guard);
        if (inBounds(next.pos, matrix) and get(next.pos, matrix) == '#') {
            guard.dir = turnRight(guard.dir);
        } else {
            guard = next;
        }
    }

    return visited;
}

pub fn main() !u8 {
    const args = try std.process.argsAlloc(allocator);
    if (args.len <= 1) {
        try std.io.getStdErr().writer().print("Usage: {s} <path to input>\n", .{args[0]});
        return 1;
    }

    var matrix = Matrix.init(allocator);
    defer {
        for (matrix.items) |line| {
            allocator.free(line);
        }
        matrix.deinit();
    }

    var buffer: [1024]u8 = undefined;
    var file = try std.fs.cwd().openFile(args[1], .{});
    var bufReader = std.io.bufferedReader(file.reader());
    var reader = bufReader.reader();
    defer file.close();

    while (try reader.readUntilDelimiterOrEof(&buffer, '\n')) |bufLine| {
        const line = try allocator.dupeZ(u8, bufLine);
        try matrix.append(line);
    }

    for (matrix.items) |line| {
        std.log.debug("{s}", .{line});
    }

    const part1 = (try patrol(matrix)).count();
    std.log.debug("Part 1: {}", .{part1});

    return 0;
}
