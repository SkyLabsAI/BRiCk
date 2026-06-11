/*
 * Copyright (c) 2024 BlueRock Security, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 */
float max();
float
lowest() {
  return -max();
}

void foo() {
	float f = 1.0f;
	double d = 1.0;
	float tenth_f = 0.1f;
	double tenth_d = 0.1;
	float zero_f = 0.0f;
	float neg_zero_f = -0.0f;
	double zero_d = 0.0;
	double neg_zero_d = -0.0;
	float subnormal_f = 0x1p-149f;
	float overflow_f = 1e39f;
	double overflow_d = 1e400;
	bool b = static_cast<bool>(f);
	double widened = static_cast<double>(f);
	float narrowed = static_cast<float>(d);
	float from_int = static_cast<float>(1);
	int to_int = static_cast<int>(f);
	bool to_bool = static_cast<bool>(f);
}
