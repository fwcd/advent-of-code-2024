#import <Foundation/Foundation.h>

int main(void) {
  NSArray<NSString *> *args = NSProcessInfo.processInfo.arguments;
  if (args.count < 2) {
    fprintf(stderr, "usage: %s <path to input>\n", args[0].UTF8String);
    return 1;
  }

  NSString *input = [NSString stringWithContentsOfFile:args[1] encoding:NSUTF8StringEncoding error:nil];
  NSLog(@"Input: %@", input);
  return 0;
}
