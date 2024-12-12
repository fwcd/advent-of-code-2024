#import <Foundation/Foundation.h>

@interface Vec2 : NSObject

@property(nonatomic) int x;
@property(nonatomic) int y;

@end

@implementation Vec2

- (id)initWithX:(int)x y:(int)y {
  self.x = x;
  self.y = y;
  return self;
}

- (NSString *)description {
  return [NSString stringWithFormat:@"Vec2[x=%d, y=%d]", self.x, self.y];
}

- (BOOL)isEqual:(id)other {
  return [other isKindOfClass:self.class] && self.x == [other x] && self.y == [other y];
}

- (NSUInteger)hash {
  return self.x ^ self.y;
}

@end

@interface Region : NSObject

@property(nonatomic) char plant;
@property(nonatomic) int perimeter;
@property(nonatomic) int sides;
@property(nonatomic) int area;

@property(nonatomic, retain) Vec2 *lastBoundaryPos;
@property(nonatomic, retain) Vec2 *lastBoundaryDir;

@end

@implementation Region

- (NSString *)description {
  return [NSString stringWithFormat:@"Region[plant=%c, perimeter=%d, sides=%d, area=%d]", self.plant, self.perimeter, self.sides, self.area];
}

@end

char plantAt(Vec2 *pos, NSArray<NSString *> *matrix) {
  return [matrix[pos.y] characterAtIndex:pos.x];
}

bool inBounds(Vec2 *pos, NSArray<NSString *> *matrix) {
  return pos.x >= 0 && pos.x < matrix[0].length && pos.y >= 0 && pos.y < matrix.count;
}

void dfsRegion(Vec2 *pos, NSArray<NSString *> *matrix, NSMutableSet<Vec2 *> *visited, Region *region) {
  region.area++;

  for (int dy = -1; dy <= 1; dy++) {
    for (int dx = -1; dx <= 1; dx++) {
      if (dx == 0 ^ dy == 0) {
        Vec2 *neigh = [[Vec2 alloc] initWithX:pos.x + dx y:pos.y + dy];
        if (inBounds(neigh, matrix) && plantAt(neigh, matrix) == region.plant) {
          if (![visited containsObject:neigh]) {
            [visited addObject:neigh];
            dfsRegion(neigh, matrix, visited, region);
          }
        } else {
          region.perimeter++;
        }
      }
    }
  }
}

NSArray<Region *> *findRegions(NSArray<NSString *> *matrix) {
  NSMutableArray<Region *> *regions = [[NSMutableArray alloc] init];
  NSMutableSet<Vec2 *> *visited = [[NSMutableSet alloc] init];

  for (int y = 0; y < matrix.count; y++) {
    for (int x = 0; x < matrix[y].length; x++) {
      Vec2 *pos = [[Vec2 alloc] initWithX:x y:y];
      if (![visited containsObject:pos]) {
        [visited addObject:pos];
        Region *region = [[Region alloc] init];
        region.plant = plantAt(pos, matrix);
        dfsRegion(pos, matrix, visited, region);
        [regions addObject:region];
      }
    }
  }

  return regions;
}

int main(void) {
  NSArray<NSString *> *args = NSProcessInfo.processInfo.arguments;
  if (args.count < 2) {
    fprintf(stderr, "usage: %s <path to input>\n", args[0].UTF8String);
    return 1;
  }

  NSString *input = [NSString stringWithContentsOfFile:args[1] encoding:NSUTF8StringEncoding error:nil];
  input = [input stringByTrimmingCharactersInSet:NSCharacterSet.whitespaceAndNewlineCharacterSet];

  NSArray<NSString *> *matrix = [input componentsSeparatedByString:@"\n"];
  NSArray<Region *> *regions = findRegions(matrix);
  NSLog(@"Regions: %@", regions);

  int part1 = 0;
  int part2 = 0;
  for (Region *region in regions) {
    part1 += region.perimeter * region.area;
    part2 += region.sides * region.area;
  }
  NSLog(@"Part 1: %d", part1);
  NSLog(@"Part 2: %d", part2);

  return 0;
}
