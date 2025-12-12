/*
 * Copyright (C) 2019 BlueRock Security, Inc.
 *
 * SPDX-License-Identifier:MIT-0
 */

void test() {
    for(int i = 0; i < 10; i++) { }
    for(int i = 0; i < 10; ++i) { }
    int i = 0;
    while (i) ;
    do { } while(i);
    while(i < 10) i++;
    do {
        i--;
    } while(i > 0);

    for(i=0; ; i++) { }
    for( ; ; ) { }

    for (; i ; ) ;
}
