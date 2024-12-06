const std = @import("std");

const allocator = std.heap.page_allocator;

const List = std.ArrayList;
const Map = std.AutoHashMap;
const String = []u8;
const Matrix = List(String);
const Vec2 = struct { x: i32, y: i32 };
const Guard = struct { pos: Vec2, dir: Vec2 };
const Walk = struct { visited: Set(Vec2), loops: bool };

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

fn walkFrom(start: Guard, matrix: Matrix, extraObstacle: ?Vec2) !Walk {
    var visited = Set(Vec2).init(allocator);
    var visitedGuards = Set(Guard).init(allocator);
    var guard = start;

    defer {
        visitedGuards.deinit();
    }

    while (inBounds(guard.pos, matrix)) {
        if (visitedGuards.contains(guard)) {
            return .{ .visited = visited, .loops = true };
        }
        try visited.put(guard.pos, {});
        try visitedGuards.put(guard, {});
        const next = step(guard);
        if (inBounds(next.pos, matrix) and ((extraObstacle != null and std.meta.eql(next.pos, extraObstacle.?)) or get(next.pos, matrix) == '#')) {
            guard.dir = turnRight(guard.dir);
        } else {
            guard = next;
        }
    }

    return .{ .visited = visited, .loops = false };
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

    const start = findStart(matrix);
    var walk = try walkFrom(start, matrix, null);
    defer {
        walk.visited.deinit();
    }

    const part1 = walk.visited.count();
    std.log.debug("Part 1: {}", .{part1});

    var part2: usize = 0;
    var walkIterator = walk.visited.keyIterator();
    while (walkIterator.next()) |pos| {
        if (!std.meta.eql(pos.*, start.pos)) {
            var walkWithObstacle = try walkFrom(start, matrix, pos.*);
            defer {
                walkWithObstacle.visited.deinit();
            }
            if (walkWithObstacle.loops) {
                part2 += 1;
            }
        }
    }

    std.log.debug("Part 2: {}", .{part2});

    return 0;
}
