struct __attribute__((packed)) H {
  unsigned char tag;
  unsigned int len;
  unsigned short w[2];
  short m[2][2];
};
unsigned int assign(H *h, unsigned int v) { return h->len = v; }
void bump(H *h) { h->len += 2; }
unsigned int pre(H *h) { return ++h->len; }
unsigned int post(H *h) { return h->len++; }
void discard(H *h, unsigned int v) { (void)(h->len = v), ++h->len; }
void loop(H *h, int n) { for (int i = 0; i < n; h->len++) ++i; }
unsigned short word(const H *h, int i) { return h->w[i]; }
unsigned short rword(const H *h, int i) { return i[h->w]; }
void set_word(H *h, int i, unsigned short v) { h->w[i] = v; }
short cell(const H *h) { return h->m[1][0]; }
H make() { return H{1, 2, {3, 4}, {{5, 6}, {7, 8}}}; }
H zero() { return H{}; }
H copy(const H &h) { return h; }
// Still unsupported: addresses, references, decays and uses of an update.
unsigned int *addr(H *h) { return &h->len; }
unsigned int &ref(H *h) { return h->len; }
unsigned short *decay(H *h) { return h->w; }
short *row(H *h) { return h->m[1]; }
unsigned int *paddr(H *h) { return &++h->len; }
