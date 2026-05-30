template<int X, int Y>
int dependent_case_labels(int value)
{
  switch (value) {
  case X:
    return 1;
  case 4 ... Y:
    return 2;
  case 9 ... 11:
    return 3;
  default:
    return 0;
  }
}

template<int X>
int dependent_case_expression(int value)
{
  switch (value) {
  case X + 1:
    return X;
  default:
    return -1;
  }
}
