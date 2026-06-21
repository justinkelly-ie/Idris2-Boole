# idris2-Boole

**Wildberger's Algebra of Boole — not Boolean Algebra — formalized in [Idris 2](https://github.com/idris-lang/Idris2).**

[![Idris2](https://img.shields.io/badge/Idris2-Algebra-blue.svg)](https://github.com/idris-lang/Idris2)

---

## The Distinction

The Algebra of Boole and Boolean Algebra are **not the same**.

| | Algebra of Boole | Boolean Algebra |
|---|---|---|
| Addition | `+` (XOR, exclusive or) | `∨` (OR, inclusive or) |
| Multiplication | `*` (AND) | `∧` (AND) |
| `1 + 1` | `0` | `1` |
| NOT x | `1 + x` (derived from addition) | `x̄` (primitive) |
| OR(x,y) | `x + y + xy` (derived) | `x ∨ y` (primitive) |
| Canonical form | Unique Boole polynumber | Sum-of-products / Product-of-sums (non-unique) |
| Circuit equivalence | Coefficient vector equality | SAT problem (NP-complete) |

Boole's original algebra (1847) uses **mod 2 arithmetic**. Boolean algebra, developed later by Huntington and Shannon, replaces XOR with inclusive-or. Wildberger argues the original is superior for circuit analysis, propositional logic, and the Möbius transform.

---

## Core Types

| Type | Definition | Meaning |
|---|---|---|
| `Bit` | `O \| I` | Element of the by-field B₂ |
| `Byte n` | `Vect n Bit` | N-dimensional Boole vector in B₂ⁿ |
| `BoolePolynumber n` | `Vect (2ⁿ) Bit` | Multilinear polynomial over B₂ |
| `Circuit` | `Input \| Xor \| And` | Logic circuit (two primitive gates) |

Only two operations are fundamental: **addition (XOR)** and **multiplication (AND)**.
Everything else — NOT, OR, NAND, NOR, implication — is derived.

---

## Modules

| Module | Role |
|---|---|
| `Boole.Bit` | By-field B₂ arithmetic, Num/Neg/Eq/linear instances |
| `Boole.Byte` | B₂ⁿ vectors, Aristotle's four syllogistic forms |
| `Boole.Connective` | All 16 binary connectives with Boole expressions |
| `Boole.Polynumber` | Boole polynumbers, multiplication, evaluation, equivalence |
| `Boole.MobiusTransform` | Self-inverse Boole-Möbius transform (T² = I) |
| `Boole.Circuit` | Circuit AST, derived gates, gate counting |
| `Boole.Syllogism` | Barbara, Celarent, Darii, Ferio, modus ponens |
| `Boole.Interfaces` | Linear interface bridge (LConsumable, LComonoid, LEq) |

---

## Installation & Pack Integration

```toml
[custom.all.idris2-Boole]
type = "local"
path = "../Idris2-Boole"
ipkg = "idris2-Boole.ipkg"
```

```
depends = base, contrib, linear, idris2-Multiset, idris2-Boole
```

---

## References

Based on Norman J. Wildberger's lecture series *Algebra of Boole* (Math Foundations 255–280).

---

© Justin Kelly. All rights reserved.
