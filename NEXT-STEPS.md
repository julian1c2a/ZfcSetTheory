# Next Steps — ZfcSetTheory Project

**Last updated**: 2026-03-24

This document outlines actionable next steps for the project, organized by priority and dependency.

---

## 1. Fundamental Theorem of Arithmetic (TFA) — High Priority

### 1.1 Status

The TFA is **fully proved** in `peanolib` (`PeanoNatLib/PeanoNatPrimes.lean`):

- §1–§2: `Prime`, `Irreducible`, equivalence `prime_iff_irreducible`
- §3: Coprimality, Gauss's lemma (`coprime_dvd_of_dvd_mul`)
- §4: `PrimeList`, `product_list` for `DList ℕ₀`
- §5: `exists_prime_divisor` — every n ≥ 2 has a prime divisor
- §6: `exists_prime_factorization` — TFA existence
- §7: `unique_prime_factorization` — TFA uniqueness (same multiplicity for each prime)
- §8: `ℙ` — the set of primes as a subtype

**No bridge lemmas exist yet** between the Peano primes and ZFC.

### 1.2 Proposed Plan: `NaturalNumbersPrimes.lean`

Create a new module that:

1. **Defines ZFC-native `isPrime`** (or `zfcPrime`):

   ```
   isPrime(p) ⟺ p ∈ ω ∧ p ≠ ∅ ∧ p ≠ σ ∅ ∧ ∀ a b ∈ ω, divides p (mul a b) → divides p a ∨ divides p b
   ```

2. **Creates bridge lemma `fromPeano_prime`**:

   ```
   Prime p ↔ isPrime (fromPeano p)
   ```

   This should follow directly from `fromPeano_divides`, `fromPeano_mul`, `fromPeano_injective` (for ≠ ∅, ≠ σ ∅).

3. **Lifts the TFA** via the isomorphism:
   - The main obstacle is representing `DList ℕ₀` (Peano lists) in ZFC. Two possible approaches:
     - **(A) Direct bridge**: State the theorem using `DList ℕ₀` on the Peano side and transport to ZFC only the conclusion (existence of factors, uniqueness of multiplicity).
     - **(B) ZFC-native lists**: Define finite sequences in ZFC as functions `f : n → ω` (where n ∈ ω), then bridge to `DList`.

   **Recommendation**: Start with **(A)** — it's simpler and still gives a complete ZFC proof of TFA. Approach (B) can come later for a fully self-contained ZFC formulation.

4. **Key theorems to export**:
   - `isPrime_ne_zero`, `isPrime_ne_one`, `isPrime_ge_two`
   - `isPrime_iff_irreducible` (ZFC version)
   - `exists_prime_divisor_ZFC`: ∀ n ∈ ω, σ(σ ∅) ∈ n ∨ n = σ(σ ∅) → ∃ p ∈ ω, isPrime p ∧ divides p n
   - `exists_prime_factorization_ZFC` (TFA existence)
   - `unique_prime_factorization_ZFC` (TFA uniqueness)

### 1.3 Dependencies

- `NaturalNumbersGcd.lean` (already complete — provides `gcd`, `divides`)
- `NaturalNumbersArith.lean` (provides `divides`, `gcdOf`, `divOf`, etc.)
- `PeanoImport.lean` (provides `fromPeano`/`toPeano`, order bridges)
- `PeanoNatLib.PeanoNatPrimes` (provides the Peano-side proofs)

### 1.4 Estimated Difficulty

**Medium**. The pattern is well-established by `NaturalNumbersGcd.lean` and `NaturalNumbersArith.lean`. The main new challenge is handling `DList ℕ₀` across the bridge, but approach (A) sidesteps this.

---

## 2. Binomial Coefficients — Medium Priority

### 2.1 Status

`peanolib` has `PeanoNatBinom.lean` with:

- `binom n k` (binomial coefficient)
- Pascal's rule: `binom (σ n) (σ k) = add (binom n k) (binom n (σ k))`
- `binom_mul_factorials`: n! = C(n,k) · k! · (n−k)!
- Standard identities: C(n,0) = 1, C(n,n) = 1, C(n,1) = n, etc.

And `PeanoNatNewtonBinom.lean` likely contains Newton's binomial theorem.

**No bridge exists yet.**

### 2.2 Proposed Plan: `NaturalNumbersBinom.lean`

Follow Pattern B (bridge-only):

1. Define `binomOf n k` via `fromPeano (binom (toPeano n _) (toPeano k _))`
2. Bridge lemma `fromPeano_binom`
3. Lift Pascal's rule and key identities

### 2.3 Dependencies

- `NaturalNumbersFactorial.lean` (for the factorial connection)
- `NaturalNumbersMul.lean`, `NaturalNumbersAdd.lean`

---

## 3. Atomic Boolean Algebra Completion — Medium Priority

### 3.1 Status (per ReflexionesParaLaIA.md [6]–[11])

`AtomicBooleanAlgebra.lean` is complete (atoms, atomicity of 𝒫(A), decomposition into atoms). Remaining goals:

1. **Complete Boolean Algebra**: Show 𝒫(A) is a complete atomic Boolean algebra (every subset has a supremum/infimum).
2. **Representation theorem**: Every complete atomic Boolean algebra is isomorphic to some 𝒫(A).
3. **Boolean Ring ↔ Boolean Algebra functor** ([7]): Formal biyection between Boolean rings and Boolean algebras.
4. **Non-atomic Boolean algebra** ([8]): Construct the algebra of finite/cofinite subsets of an infinite set, show it is not atomic, hence not isomorphic to any 𝒫(A).
5. **Finite power set cardinality** ([10]): |𝒫(F)| = 2^n when |F| = n.
6. **Finite Boolean algebra theorem** ([11]): Every finite Boolean algebra has cardinality 2^n for some n ∈ ω.

### 3.2 Proposed Approach

Create a unified module (or small family of modules) for items 1–6. This requires:

- Supremum/infimum for arbitrary subsets of 𝒫(A) (via ⋃ and ⋂)
- Isomorphism machinery (bijections preserving ∧, ∨, ¬)
- Finite/cofinite subset construction as a new algebra
- Cardinality arguments connecting finite sets to ω

---

## 4. Finite Sequences in ZFC — Lower Priority (enabler for full ZFC-TFA)

### 4.1 Motivation

For a truly ZFC-native statement of TFA (approach B in §1), we need finite sequences modeled as functions `f : n → ω` where `n ∈ ω`. This is also a prerequisite for many future developments (polynomials, ordinal arithmetic, etc.).

### 4.2 Proposed Plan

1. Define `FinSeq n A` = `{ f ∈ (n ×ₛ A) | isFunctionFromTo f n A }` for n ∈ ω
2. Define `concat`, `length`, `nth`, `product` for finite sequences
3. Bridge to `DList ℕ₀` via the Peano isomorphism
4. Restate TFA with ZFC-native sequences

---

## 5. Integers (ℤ) in ZFC — Future

Per ReflexionesParaLaIA.md [15]. Define ℤ as equivalence classes of pairs (a, b) ∈ ω × ω under (a, b) ~ (c, d) ⟺ a + d = b + c. All arithmetic operations, ring structure.

---

## 6. Gödel's Incompleteness Theorems — Future

Per ReflexionesParaLaIA.md [5], [12]. Rosser's strengthened form. Requires encoding of syntax, Gödel numbering, representability of recursive functions in ZFC.

---

## 7. Project Reorganization — Future

Per ReflexionesParaLaIA.md [14]. Restructure into clear module hierarchies:

- `ZfcSetTheory.Core` (axioms, basic set operations)
- `ZfcSetTheory.Algebra` (Boolean algebras, rings, lattices)
- `ZfcSetTheory.Arithmetic` (ω, operations, TFA)
- `ZfcSetTheory.NumberSystems` (ℤ, ℚ, ℝ)
- `ZfcSetTheory.Ordinals` (ordinal arithmetic, transfinite recursion)

---

## Summary of Immediate Actionable Items

| Priority | Task | New File | Key Dependency |
|----------|------|----------|----------------|
| **1** | TFA via Peano bridge (primes + factorization) | `NaturalNumbersPrimes.lean` | `NaturalNumbersGcd`, `PeanoNatPrimes` |
| **2** | Binomial coefficients bridge | `NaturalNumbersBinom.lean` | `NaturalNumbersFactorial`, `PeanoNatBinom` |
| **3** | Complete atomic Boolean algebra + representation | Extension of `AtomicBooleanAlgebra.lean` or new module | `AtomicBooleanAlgebra`, `Cardinality` |
| **4** | Finite sequences in ZFC | `FiniteSequences.lean` | `Functions`, `NaturalNumbers` |

---

*Generated 2026-03-24 from analysis of peanolib, PeanoImport bridges, and ReflexionesParaLaIA.md roadmap.*
