typedef struct Before Before;
struct Before {
  int x;
};

struct After {
  int x;
};
typedef struct After After;

typedef struct Inline {
  int x;
} Inline;

typedef struct ForwardOnly ForwardOnly;

struct D;
typedef struct D Dtypedef;

// no [struct X]
typedef struct X Xtypedef;
