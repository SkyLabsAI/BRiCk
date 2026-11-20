struct FieldPacked { char c; int i __attribute__((packed)); };
struct [[gnu::packed]] GnuPacked { char c; int i; };
#pragma pack(1)
struct PragmaNoPush { char c; int i; };
#pragma pack()
struct AfterReset { char c; int i; };
#pragma pack(push, 2)
struct PragmaAlignas { char c; alignas(8) long l; int i; };
#pragma pack(pop)
struct __attribute__((packed)) PackedArray { char c; short a[3]; };
struct __attribute__((packed)) PackedNested { char c; struct Inner { char d; int j; } in; };
