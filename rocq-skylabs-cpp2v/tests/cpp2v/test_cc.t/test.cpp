/*
 * Copyright (c) 2020 BlueRock Security, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 */

__attribute__((regcall)) int foo() {
  return 0;
}

__attribute__((ms_abi)) int bar() {
  return 1;
}
