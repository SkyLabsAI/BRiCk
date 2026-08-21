# Changelog

### How to use

This document is a best-effort that tracks breaking changes to the code base.

When adding a new entry, add it to the **top** of the list with the date.
When a release occurs, change the `Since Last Release` heading to the name
of the release, and introduce a new heading.

## Since Last Release

2026.08.21: C++ source coordinates use primitive `uint63` values
- Physical byte offsets, lines, columns, presumed lines and columns, and
  include-parent offsets changed from `N` to `PrimInt63.int`.
- cpp2v rejects 64-bit byte offsets above `Uint63.max_int`.

2026.08.21: Generated C++ source locations use relocatable typed names
- `source_file_physical_name`, `source_file_requested_name`, `presumed_file`,
  and encoded presumed-filename rows now use `source_name` instead of
  `PrimString.string`.
- Wrap hand-written non-filesystem names with `LiteralSourceName`; resolve
  generated paths with `SourcePath.resolve` and the absolute AST `.v` path.

2025.03.20: Change global prefix `bedrock.xxx` to `bluerock.xxx`
- See `scripts/fm-refactorings/bedrock-bluerock.sh`

2025.03.17: Split the C++ program logic BRiCk from the BlueRock prelude (`rocq-skylabs-prelude`) and Iris extensions (`rocq-skylabs-iris`).
- See `scripts/fm-refactorings/split-brick.sh`


