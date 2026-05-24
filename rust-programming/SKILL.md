---
name: rust-programming
description: The essential best practices for Rust development
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

## Use `From` and `TryFrom` for Type Conversions

Always use standard conversion traits when converting between types:

- Use `From<T>` for infallible, lossless, unambiguous conversions.
- Use `TryFrom<T>` for fallible, validating, narrowing, or otherwise rejectable conversions.
- Do not create bespoke conversion methods like `to_domain`, `from_api`, `into_model`, or `parse_foo` when `From`/`TryFrom` fits.

Never hide errors in `From`, and never encode conversion failure with `Option`, sentinel values, panics, or lossy defaults.

```rust
// Bad: ad hoc conversion API, easy to miss at call sites
impl ApiUser {
    fn to_domain(self) -> Result<User, UserError> {
        User::new(self.email)
    }
}

// Bad: fallible conversion hidden behind From
impl From<ApiUser> for User {
    fn from(value: ApiUser) -> Self {
        User::new(value.email).unwrap()
    }
}

// Good: call sites use User::try_from(api_user) or api_user.try_into()
impl TryFrom<ApiUser> for User {
    type Error = UserError;

    fn try_from(value: ApiUser) -> Result<Self, Self::Error> {
        User::new(value.email)
    }
}

// Good: infallible conversion uses From
impl From<User> for PublicUser {
    fn from(value: User) -> Self {
        Self { id: value.id, email: value.email }
    }
}
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

## Default Crates

When multiple crates solve the same problem, prefer the standard library first.
If the surrounding codebase already uses a competing crate, follow the project.
Otherwise, use the defaults below.

| Task | Default | Install | Notes |
|------|---------|---------|-------|
| Error reporting | `rootcause` | `cargo add rootcause` | Structured, inspectable error reports. |
| Serialization derives | `serde` | `cargo add serde --features derive` | Ecosystem default for typed serialization. |
| JSON | `serde_json` | `cargo add serde_json` | Prefer typed structs over `serde_json::Value` unless the schema is genuinely dynamic. |
| TOML | `toml` | `cargo add toml` | Use `toml_edit` only when preserving comments/formatting matters. |
| Compact binary serialization | `postcard` | `cargo add postcard` | Compact Serde format; add `alloc`/`use-std` only when needed. |
| Zero-copy byte/layout parsing | `zerocopy` + `zerocopy-derive` | `cargo add zerocopy zerocopy-derive` | Do not write custom `unsafe` casts for byte/layout conversion. |
| CLI framework | `clap` | `cargo add clap --features derive` | Use stdlib args only for trivial scripts. |
| HTTP client | `reqwest` | `cargo add reqwest --no-default-features --features rustls,json` | Add cookies, compression, proxy, HTTP/2, blocking, etc. only when used. |
| TLS | `rustls` | `cargo add rustls` | Avoid OpenSSL/native TLS unless platform policy requires it. |
| QUIC | `quinn` | `cargo add quinn` | Also prefer when free to choose a secure app transport. |
| Async runtime | `tokio` | `cargo add tokio --features macros,rt-multi-thread,signal,time` | Add `net`, `io-util`, `sync`, `fs`, etc. only when used. |
| Diagnostics | `tracing` + `tracing-subscriber` | `cargo add tracing`; `cargo add tracing-subscriber --features env-filter,fmt` | Structured, async-aware diagnostics with env-based filtering. |
| SQL ORM/query builder | `diesel` | `cargo add diesel --features postgres` or `sqlite`/`mysql` | Default for SQL work. Do not start new `sqlx`/SeaORM use unless the project already uses them. |
| SQL migrations | `diesel_migrations` | `cargo add diesel_migrations` | Use when the app owns schema migrations. |
| SQL pooling | Diesel `r2d2` feature | `cargo add diesel --features postgres,r2d2` | Use for long-running apps with synchronous DB connections. |
| Datetimes | `jiff` | `cargo add jiff` | Prefer timezone-aware datetime handling over ad hoc timestamps. |
| UTF-8 paths | `camino` | `cargo add camino` | Use when paths are user-visible, serialized, or displayed; keep std `Path` for arbitrary OS paths. |
| Temporary files | `tempfile` | `cargo add tempfile` | Avoid manual temp path construction. |
| Data parallelism | `rayon` | `cargo add rayon` | CPU-bound work only; not async I/O concurrency. |
| Regex | `regex` | `cargo add regex` | No backreferences/look-around. |
| Memory zeroing | `zeroize` | `cargo add zeroize --features derive` | Use for secret-bearing custom types. |
| Constant-time primitives | `subtle` | `cargo add subtle` | Use for crypto-sensitive equality/selection. |
| Content hashing | `blake3` | `cargo add blake3` | Not a password hash or MAC replacement. |

Defaults explicitly not set: web framework, retry crate, YAML crate, low-level
crypto primitive crate. Do not design custom TCP/TLS protocols when `quinn`
fits the transport requirements.

## Dependency Management

Always use `cargo add` instead of manually editing `Cargo.toml`:

```bash
# Good: validates crate exists, uses latest compatible version
cargo add serde --features derive
cargo add tokio --features macros,rt-multi-thread,signal,time
cargo add reqwest --no-default-features --features rustls,json

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
