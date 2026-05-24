---
name: Rust Programming
description: The essential best practices for Rust development
version: 1.0.0
---

## Avoid Direct Indexing

Use slice pattern matching instead of index access:

```rust
// Bad: panic risk
if matching_users.len() == 1 {
    let user = &matching_users[0];
}

// Good: compiler-checked
match matching_users.as_slice() {
    [] => handle_empty(),
    [user] => use_user(user),
    _ => Err(DuplicateUsers),
}
```

## Be Explicit with Defaults

Destructure to make defaulted fields visible:

```rust
let Foo { field1, field2, field3 } = Foo::default();
let foo = Foo { field1: custom, field2, field3 };
```

## Destructure in Trait Impls

Force compiler errors when fields are added:

```rust
impl PartialEq for Order {
    fn eq(&self, other: &Self) -> bool {
        let Self { id, total, created_at: _ } = self;
        // Now adding a field forces you to handle it
    }
}
```

## Use `TryFrom` for Fallible Conversions

Never hide errors in `From`:

```rust
// Bad: hides failure
impl From<String> for MyType { ... }

// Good: errors are explicit
impl TryFrom<String> for MyType { ... }
```

## Match All Enum Variants Explicitly

Avoid catch-all `_` patterns:

```rust
// Bad: new variants silently fall through
match state {
    State::A => {},
    _ => {},
}

// Good: compiler warns on new variants
match state {
    State::A => {},
    State::B | State::C => {},
}
```

## Replace Booleans with Enums

```rust
// Bad: what do these mean?
process(&data, true, false);

// Good: self-documenting
process(&data, Compression::Strong, Encryption::None);
```

## Scope Mutability

```rust
let data = {
    let mut data = get_vec();
    data.sort();
    data
};  // data is now immutable
```

## Enforce Constructor Validation

```rust
pub struct ValidEmail {
    value: String,
    _private: (),  // prevents direct construction
}

impl ValidEmail {
    pub fn new(s: String) -> Result<Self, Error> {
        validate(&s)?;
        Ok(Self { value: s, _private: () })
    }
}
```

## Use `#[must_use]`

```rust
#[must_use = "Config must be applied"]
pub struct Config { ... }
```

## Cargo.toml Edition

Never downgrade the `edition` field in `Cargo.toml` unless explicitly requested.
When creating new projects or when edition is unspecified, prefer `edition = "2024"`.

## Dependency Management

Always use `cargo add` instead of manually editing `Cargo.toml`:

```bash
# Good: validates crate exists, uses latest compatible version
cargo add serde
cargo add serde --features derive
cargo add tokio --features full

# With specific version
cargo add clap@4.0

# Dev dependency
cargo add --dev mockall
```

This ensures correct syntax, validates crate names, and resolves compatible versions automatically.

## Combine Imports

Merge imports sharing a common prefix into nested groups:

```rust
// Bad: redundant prefixes
use std::collections::HashMap;
use std::collections::HashSet;
use std::io::Read;
use std::io::Write;

// Good: grouped
use std::{
    collections::{HashMap, HashSet},
    io::{Read, Write},
};
```

## Formatting

Always run `cargo fmt` after making changes:

```bash
cargo fmt
```

## Use `dbg!` for Debugging

Prefer `dbg!` over `println!` for temporary debug output:

```rust
// Bad: manual formatting, no file/line info
println!("value = {:?}", some_value);

// Good: includes file:line, expression, and value
dbg!(&some_value);
// Prints: [src/main.rs:42] &some_value = SomeType { ... }

// Works inline in expressions
let result = dbg!(compute_something());
```

`dbg!` prints to stderr (not stdout), shows the source location, and returns the value so it can be used inline.

## Strongly-Typed Parsing

Avoid weakly-typed parsing (e.g. `serde_json::Value`, `Map<String, Value>`). Define structs with `Serialize`/`Deserialize` derives:

```rust
// Bad: stringly-typed, no compile-time guarantees
let v: serde_json::Value = serde_json::from_str(&data)?;
let name = v["name"].as_str().unwrap();

// Good: schema enforced at parse time
#[derive(Deserialize)]
struct Config {
    name: String,
    count: u32,
}
let config: Config = serde_json::from_str(&data)?;
```

This applies to all structured formats (JSON, TOML, YAML, etc.). Typed structs catch missing/wrong fields at deserialization, not deep in business logic.

## Recommended Clippy Lints

```toml
[lints.clippy]
indexing_slicing = "warn"
fallible_impl_from = "warn"
wildcard_enum_match_arm = "warn"
fn_params_excessive_bools = "warn"
must_use_candidate = "warn"
```

---

**Core principle**: Make implicit invariants explicit and compiler-checked.
