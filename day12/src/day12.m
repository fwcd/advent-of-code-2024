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

@property(nonatomic) int perimeter;
@property(nonatomic) int area;

@end

@implementation Region

- (NSString *)description {
  return [NSString stringWithFormat:@"Region[perimeter=%d, area=%d]", self.perimeter, self.area];
}

- (int)price {
  return self.perimeter * self.area;
}

@end

char charAt(Vec2 *pos, NSArray<NSString *> *matrix) {
  return [matrix[pos.y] characterAtIndex:pos.x];
}

bool inBounds(Vec2 *pos, NSArray<NSString *> *matrix) {
  return pos.x >= 0 && pos.x < matrix[0].length && pos.y >= 0 && pos.y < matrix.count;
}

void dfsRegion(Vec2 *pos, char c, NSArray<NSString *> *matrix, NSMutableSet<Vec2 *> *visited, Region *region) {
  region.area++;

  for (int dy = -1; dy <= 1; dy++) {
    for (int dx = -1; dx <= 1; dx++) {
      if (dx == 0 ^ dy == 0) {
        Vec2 *neigh = [[Vec2 alloc] initWithX:pos.x + dx y:pos.y + dy];
        if (inBounds(neigh, matrix) && charAt(neigh, matrix) == c) {
          if (![visited containsObject:neigh]) {
            [visited addObject:neigh];
            dfsRegion(neigh, c, matrix, visited, region);
          }
        } else {
          region.perimeter++;
        }
      }
    }
  }
}

NSDictionary<NSString *, Region *> *findRegions(NSArray<NSString *> *matrix) {
  NSMutableDictionary<NSString *, Region *> *regions = [[NSMutableDictionary alloc] init];
  NSMutableSet<Vec2 *> *visited = [[NSMutableSet alloc] init];

  for (int y = 0; y < matrix.count; y++) {
    for (int x = 0; x < matrix[y].length; x++) {
      Vec2 *pos = [[Vec2 alloc] initWithX:x y:y];
      if (![visited containsObject:pos]) {
        [visited addObject:pos];
        char c = charAt(pos, matrix);
        Region *region = [[Region alloc] init];
        dfsRegion(pos, c, matrix, visited, region);
        regions[[NSString stringWithFormat:@"%c", c]] = region;
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
  NSDictionary<NSString *, Region *> *regions = findRegions(matrix);
  NSLog(@"Regions: %@", regions);

  return 0;
}
