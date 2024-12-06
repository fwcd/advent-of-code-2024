const std = @import("std");

const allocator = std.heap.page_allocator;

const List = std.ArrayList;
const Map = std.AutoHashMap;
const String = []u8;
const Matrix = List(String);
const Vec2 = struct { x: i32, y: i32 };
const State = struct { pos: Vec2, dir: Vec2 };

fn Set(comptime T: type) type {
    return Map(T, void);
}

fn width(matrix: Matrix) i32 {
    return matrix.items[0].len;
}

fn height(matrix: Matrix) i32 {
    return matrix.items.len;
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

fn findStart(matrix: Matrix) State {
    for (0..height(matrix)) |i| {
        for (0..width(matrix)) |j| {
            const dir = parseDirection(matrix[i][j]);
            if (dir != null) {
                return dir;
            }
        }
    }
    std.debug.panic("Could not find start");
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

    return 0;
}
