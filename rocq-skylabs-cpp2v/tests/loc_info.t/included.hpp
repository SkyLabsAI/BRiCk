#pragma once

#define HEADER_PLUS_ONE(value) ((value) + 1)

inline int header_only_location(int value) {
  int copy = value;
  return copy;
}
