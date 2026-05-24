---
name: Python Programming
description: Best practices for Python development
version: 1.0.0
---

# Python Development

## Strategy

When starting a task, create a todo list. Structure it as follows:

- If `ruff`, `basedpyright`, and `pytest` are not already in dev dependencies, add them as the first item:
  ```bash
  uv add --dev ruff basedpyright pytest
  ```
- ... task-specific items ...
- Format and lint:
  ```bash
  uv run ruff format .
  uv run ruff check --fix .
  ```
- Type check — fix all warnings, not just errors:
  ```bash
  uv run basedpyright
  ```
- Run tests:
  ```bash
  uv run pytest
  ```

The format/lint, type check, and test items must always be the last three items on the list.

Never leave warnings unresolved. Prefer fixing the root cause — add type annotations,
use `cast(...)`, or refactor the code. Only use `# pyright: ignore[...]` as a last
resort for genuine false positives from third-party libraries with incomplete stubs
(e.g. `reportAny` from untyped library calls). Every suppression should be the
narrowest possible rule (e.g. `# pyright: ignore[reportAny]`, not a blanket ignore).

## Default Libraries

When multiple libraries solve the same problem, always pick the default below
unless the user or surrounding codebase already uses something else.

| Task | Default | Install |
|------|---------|---------|
| Read TOML | stdlib `tomllib` | — |
| Env-driven settings | `pydantic-settings` | `uv add pydantic-settings` |
| Wire JSON | stdlib `json` | — |
| HTTP client | `httpx` (sync + async same API) | `uv add httpx` |
| Filesystem paths | `pathlib.Path` (never `os.path` strings) | — |
| Subprocess | `subprocess.run(..., check=True)` (never `shell=True`) | — |
| CLI framework | `typer` | `uv add typer` |
| Datetimes | stdlib `datetime` + `zoneinfo`, always tz-aware (`datetime.now(UTC)`) | — |
| Async runtime | stdlib `asyncio` + `asyncio.TaskGroup` | — |
| CPU-bound parallelism | `concurrent.futures.ProcessPoolExecutor` | — |
| Tabular data | `polars` (pandas only when an external lib requires DataFrames) | `uv add polars` |
| Arrays | `numpy` | `uv add numpy` |
| Crypto-strength random | stdlib `secrets` | — |
| Non-crypto random | stdlib `random` | — |
| Identity / dedup hashing (not passwords) | `hashlib.blake2b` | — |
| Constant-time compare | `hmac.compare_digest` | — |
| Cryptography (AEAD, KDF, signatures, x509) | `cryptography` (avoid `pycryptodome`) | `uv add cryptography` |
| Password hashing | `from cryptography.hazmat.primitives.kdf.argon2 import Argon2id` | (via `cryptography`) |
| JWT | `pyjwt` (avoid unmaintained `python-jose`) | `uv add pyjwt` |
| Progress bars | `tqdm` | `uv add tqdm` |

Defaults explicitly *not* set (pick ad hoc per context): retry library, TOML writing,
faster JSON (`orjson` / `msgspec` only when stdlib `json` is profiled as the bottleneck).

## Printing/Emojis

Never use emojis of any kind, unless explicitly asked to by the user.

## Secret Input

Never accept secrets (passwords, API keys, signing keys) via CLI arguments — they
leak into shell history, `ps` output, and process accounting. Read from stdin
instead, which works for both interactive use and piping (`echo $SECRET | tool`,
`tool < secret.txt`):

```python
import sys
from getpass import getpass

def read_secret(prompt: str = "Secret: ") -> str:
    if sys.stdin.isatty():
        return getpass(prompt)  # interactive: no echo
    return sys.stdin.readline().rstrip("\n")  # piped: one line, strip trailing newline
```

Env vars are an acceptable alternative for non-interactive/CI use, but stdin is
the default for CLI tools.

## Package Management

Never pollute the global python enviroment.
Always use `uv` as the package manager:

```bash
# Initialize a new project
uv init

# Add dependencies
uv add requests
uv add --dev pytest

# Run scripts
uv run python script.py
uv run pytest
```

Pin resolver to recent packages in `pyproject.toml` for reproducible builds:

```toml
[tool.uv]
exclude-newer = "30 days"
```

## Type Hints

Use type hints for function signatures and complex variables:

```python
def process_items(items: list[str], limit: int | None = None) -> dict[str, int]:
    ...
```

Run type checking with `basedpyright`:

```bash
uv add --dev basedpyright
uv run basedpyright
```

## Code Formatting

Use `ruff` for linting and formatting:

```bash
uv add --dev ruff

# Format code
uv run ruff format .

# Lint and fix
uv run ruff check --fix .
```

## Testing

Use `pytest` for testing:

```bash
uv add --dev pytest

# Run tests
uv run pytest

# With coverage
uv add --dev pytest-cov
uv run pytest --cov=src
```

### Test Structure

```python
def test_function_does_expected_thing():
    # Arrange
    input_data = create_input()

    # Act
    result = function_under_test(input_data)

    # Assert
    assert result == expected_value
```

## Unit Testing

### Structure Code for Testability

Separate pure logic from I/O and side effects. Functions that only transform data
can be tested directly without mocking, patching, or touching the filesystem.

```python
# Bad: logic and I/O tangled together — hard to test
def process_file(path: str) -> None:
    with open(path) as f:
        data = json.load(f)
    result = [item["value"] * 2 for item in data if item["active"]]
    with open(path + ".out", "w") as f:
        json.dump(result, f)

# Good: pure logic extracted — trivial to test
def process_items(items: list[dict[str, Any]]) -> list[int]:
    return [item["value"] * 2 for item in items if item["active"]]

def process_file(path: str) -> None:
    with open(path) as f:
        data = json.load(f)
    result = process_items(data)
    with open(path + ".out", "w") as f:
        json.dump(result, f)
```

Test the pure core exhaustively; test I/O boundaries minimally (e.g. one integration
test or a test using `tmp_path`).

### Coverage Goals

Aim for full coverage. Every function should have tests for:

- **Happy path**: typical valid inputs and expected outputs
- **Edge cases**: boundary values, empty inputs, single-element collections, zero, max values
- **Error cases**: invalid inputs that should raise exceptions

```python
def test_divide_normal():
    assert divide(10, 2) == 5.0

def test_divide_negative():
    assert divide(-10, 2) == -5.0

def test_divide_zero_numerator():
    assert divide(0, 5) == 0.0

def test_divide_by_zero():
    with pytest.raises(ZeroDivisionError):
        divide(1, 0)
```

Use `pytest.mark.parametrize` to cover multiple cases without repetition:

```python
@pytest.mark.parametrize("a,b,expected", [
    (10, 2, 5.0),
    (-10, 2, -5.0),
    (0, 5, 0.0),
    (7, 2, 3.5),
])
def test_divide(a: int, b: int, expected: float) -> None:
    assert divide(a, b) == expected
```

Track coverage and treat gaps as missing tests, not acceptable holes:

```bash
uv add --dev pytest-cov
uv run pytest --cov=src --cov-report=term-missing
```

## Project Structure

```
project/
  src/
    package_name/
      __init__.py
      module.py
  tests/
    test_module.py
  pyproject.toml
```

## Logging

Use `logging` instead of `print` unless otherwise explicitly specified:

```python
import logging

logger = logging.getLogger(__name__)

# Bad: print statements
print(f"Processing {item}")
print(f"Error: {e}")

# Good: structured logging
logger.info("Processing item", extra={"item_id": item.id})
logger.exception("Failed to process item")
```

Basic setup:

```python
logging.basicConfig(
    level=logging.INFO,
    format="%(asctime)s %(levelname)s %(name)s: %(message)s"
)
```

## Error Handling

Be explicit with exceptions:

```python
# Bad: catches everything
try:
    do_something()
except:
    pass

# Good: specific exceptions
try:
    do_something()
except ValueError as e:
    handle_value_error(e)
except IOError as e:
    handle_io_error(e)
```

## Dataclasses

Use `dataclasses` instead of dicts with constant keys or complex tuples for structured data:

```python
from dataclasses import dataclass

# Bad: dict with constant keys
def get_user() -> dict:
    return {"id": 1, "name": "Alice", "active": True}

user = get_user()
name = user["name"]  # No type checking, easy to typo keys

# Bad: complex tuple
def get_user() -> tuple[int, str, bool]:
    return (1, "Alice", True)

user_id, name, active = get_user()  # Positional, unclear meaning

# Good: dataclass
@dataclass
class User:
    id: int
    name: str
    active: bool = True

def get_user() -> User:
    return User(id=1, name="Alice")

user = get_user()
name = user.name  # Type-checked, IDE autocomplete
```

### Immutable Dataclasses

Use `frozen=True` for immutable data (e.g. for hashing):

```python
@dataclass(frozen=True)
class Point:
    x: float
    y: float

p = Point(1.0, 2.0)
p.x = 3.0  # Error: frozen dataclass
```

### When to Use Dataclasses vs Pydantic

- **Dataclasses**: Internal data structures, simple containers, no validation needed
- **Pydantic**: External input, API boundaries, complex validation, serialization

## Enums Instead of Booleans

Always aim to replace boolean parameters with enums for self-documenting code:

```python
from enum import Enum, auto

# Bad: what do these mean?
process(data, True, False)

# Good: self-documenting
class Compression(Enum):
    FAST = auto()
    GOOD = auto()

class Encryption(Enum):
    NONE = auto()
    AES256 = auto()

process(data, Compression.GOOD, Encryption.NONE)
```

### Multiple Booleans are a Code Smell

```python
# Bad: boolean blindness
def create_user(name: str, active: bool, admin: bool, verified: bool) -> User:
    ...

create_user("Alice", True, False, True)  # What is True/False here?

# Good: explicit states
class UserStatus(Enum):
    PENDING = auto()
    ACTIVE = auto()
    SUSPENDED = auto()

class UserRole(Enum):
    USER = auto()
    ADMIN = auto()

def create_user(name: str, status: UserStatus, role: UserRole) -> User:
    ...

create_user("Alice", UserStatus.ACTIVE, UserRole.USER)
```

### When Booleans Are Acceptable

- Single boolean with obvious meaning: `visible`, `enabled`, `dry_run`
- Private/internal helper functions where context is clear

## Pattern Matching

Use `match` when branching over a finite set of possibilities such as an enum or a fixed set of values.
Prefer it over chains of `if/elif`:

```python
from enum import Enum, auto

class Direction(Enum):
    NORTH = auto()
    SOUTH = auto()
    EAST = auto()
    WEST = auto()

# Bad: if/elif chain
def describe(d: Direction) -> str:
    if d == Direction.NORTH:
        return "up"
    elif d == Direction.SOUTH:
        return "down"
    elif d == Direction.EAST:
        return "right"
    else:
        return "left"

# Good: match statement
def describe(d: Direction) -> str:
    match d:
        case Direction.NORTH:
            return "up"
        case Direction.SOUTH:
            return "down"
        case Direction.EAST:
            return "right"
        case Direction.WEST:
            return "left"
```

Avoid a catch-all `case _` when all cases are covered — its absence lets the type checker warn you about unhandled members.
If a default branch is needed for defensive purposes, raise rather than silently falling through:

```python
# Bad: match statement with fallthrough for invalid variants
def describe(d: Direction) -> str:
    match d:
        case Direction.NORTH:
            return "up"
        case Direction.SOUTH:
            return "down"
        case Direction.EAST:
            return "right"
        case _:
            return "left"

# Good: match checks for valid variant
match d:
    case Direction.NORTH:
        return "up"
    case Direction.SOUTH:
        return "down"
    case Direction.EAST:
        return "right"
    case Direction.WEST:
        return "left"
    case _:
        raise ValueError(f"unhandled direction: {d}")
```

The same applies to `if/elif` chains over a fixed set — always end with `else: raise`
instead of a silent fallthrough or a default that hides programming errors.

## Data Modeling with Pydantic

Use Pydantic consistently for structured data, validation, and serialization:

```bash
uv add pydantic
```

### Basic Models

```python
from pydantic import BaseModel, EmailStr

class User(BaseModel):
    id: int
    name: str
    email: EmailStr
```

### Immutable Models

```python
from pydantic import BaseModel, ConfigDict

class Config(BaseModel):
    model_config = ConfigDict(frozen=True)

    host: str
    port: int
```

### Validation

```python
from pydantic import BaseModel, Field, field_validator

class Order(BaseModel):
    quantity: int = Field(gt=0)
    price: float = Field(ge=0)

    @field_validator("quantity")
    @classmethod
    def check_quantity(cls, v: int) -> int:
        if v > 1000:
            raise ValueError("quantity too large")
        return v
```

### Serialization

```python
user = User(id=1, name="Alice", email="alice@example.com")

# To dict
user.model_dump()

# To JSON
user.model_dump_json()

# From dict
User.model_validate({"id": 1, "name": "Alice", "email": "alice@example.com"})

# From JSON
User.model_validate_json('{"id": 1, "name": "Alice", "email": "alice@example.com"}')
```

## Continuous Integration

If the project has CI, add checks for formatting, linting, type checking, and tests.

### GitHub Actions

```yaml
# .github/workflows/ci.yml
name: CI

on:
  push:
    branches: [main]
  pull_request:

jobs:
  check:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v4

      - name: Install uv
        uses: astral-sh/setup-uv@v4

      - name: Install dependencies
        run: uv sync --dev

      - name: Check formatting
        run: uv run ruff format --check .

      - name: Lint
        run: uv run ruff check .

      - name: Type check
        run: uv run basedpyright

      - name: Test
        run: uv run pytest
```

### Required Dev Dependencies

Ensure these are in `pyproject.toml`:

```bash
uv add --dev ruff basedpyright pytest
```

