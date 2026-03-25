## ADDED Requirements

### Requirement: SeqNum Type
The library SHALL define a `SeqNum` type representing TCP sequence numbers as
unsigned 32-bit integers with modular arithmetic (RFC 793 §3.3). The type SHALL
support addition by an offset (`SeqNum → UInt32 → SeqNum`) and subtraction
yielding a distance (`SeqNum → SeqNum → UInt32`), both computed modulo 2^32.

#### Scenario: Modular wrap-around
- **WHEN** `SeqNum.add` is applied to a sequence number near `2^32 - 1` with a positive offset
- **THEN** the result wraps around to the low end of the sequence space

#### Scenario: Round-trip identity
- **WHEN** an offset `n` is added to a sequence number `a` and then `a` is subtracted from the result
- **THEN** the distance equals `n`

### Requirement: Circular Less-Than Relation
The library SHALL define a strict less-than relation `SeqNum.lt` over the
circular sequence number space, where `a < b` holds if and only if
`(b - a) mod 2^32` falls in the open interval `(0, 2^31)` (the forward
half-space). A corresponding `SeqNum.le` SHALL also be provided.
(RFC 793 §3.3: "=<" means "less than or equal modulo 2^32".)

#### Scenario: Half-space comparison
- **WHEN** `b - a = 1` (modulo 2^32)
- **THEN** `SeqNum.lt a b` holds

#### Scenario: Opposite half-space
- **WHEN** `b - a = 2^32 - 1` (i.e., `a` is one ahead of `b` in forward direction)
- **THEN** `SeqNum.lt a b` does NOT hold (instead `SeqNum.lt b a` holds)

#### Scenario: Equal values
- **WHEN** `a = b`
- **THEN** neither `SeqNum.lt a b` nor `SeqNum.lt b a` holds

### Requirement: SeqNum Properties
The library SHALL prove the following properties of `SeqNum.lt`:
- Irreflexivity: `¬ (a < a)`
- Transitivity within the half-space: if `a < b` and `b < c` and the total
  span `c - a` is less than `2^31`, then `a < c`
- Trichotomy within the half-space: for any `a, b` with `a - b ≠ 2^31` and
  `b - a ≠ 2^31`, exactly one of `a < b`, `a = b`, `b < a` holds
- Decidability: `SeqNum.lt` SHALL have a `Decidable` instance

#### Scenario: Transitivity proof typechecks
- **WHEN** `lake build Tcp.SeqNum` is run
- **THEN** the transitivity theorem typechecks without `sorry`

#### Scenario: Decidability enables if-then-else
- **WHEN** `SeqNum.lt` is used in an `if` expression
- **THEN** Lean resolves the `Decidable` instance automatically
