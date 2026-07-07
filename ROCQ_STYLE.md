# Rocq Style

- **Always** use attributes to track command modifiers. For example.
  - `#[local]`, NOT `Local`,
  - `#[global]`, NOT `Global`,
  - `#[export]`, NOT `Export`,
  - `#[program]`, NOT `Program`, and
  - `#[universes(polymorphic=yes)]` instead of `Polymorphic`
  - `#[universes(polymorphic=yes,cumulative=yes)]` instead of `Polymorphic Cumulative`

- Top-level definitions should have
  - Type ascriptions on all arguments except for variables of type `Type`.
  - A return type annotation

- When working in a section that requires a lot of `Proof using xxx` lines. Use `Set Default Proof Using` rather than replicating the line.
- Prefer `Set Default Proof Using "Type*"`.

- `Arguments` commands **MUST** have a locality defined, e.g. `#[local] Arguments`.

- Avoid explicit qualifications when possible. For example,
  - use `length` rather than `Datatypes.length`.
  - AGENT: When editing code that is meant to be simple, semantics-preserving refactoring, the need for additional qualification should be called out explicitly.
