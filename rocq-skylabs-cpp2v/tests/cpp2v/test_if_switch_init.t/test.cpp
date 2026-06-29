int if_init_only(int x) {
  if (int seed = x + 1; seed == 4) {
    return seed;
  } else {
    return 0;
  }
}

int if_decl_only(int x) {
  if (int value = x + 2) {
    return value;
  } else {
    return 0;
  }
}

int if_init_and_decl(int x) {
  if (int seed = x + 1; int value = seed + 2) {
    return value;
  } else {
    return 0;
  }
}

int switch_init_only(int x) {
  switch (int tag = x + 1; tag) {
  case 4:
    return tag;
  default:
    return 0;
  }
}

int switch_decl_only(int x) {
  switch (int tag = x + 2) {
  case 5:
    return tag;
  default:
    return 0;
  }
}

int switch_init_and_decl(int x) {
  switch (int seed = x + 1; int tag = seed + 2) {
  case 6:
    return tag;
  default:
    return 0;
  }
}
