/-
  # Natural Numbers (von Neumann ordinals)

  This file defines the natural numbers as von Neumann ordinals without introducing the Axiom of Infinity,
  and without induction principle (this will be a theorem)

  ## Main definitions
  - `σ` n : Successor function ∀ (n : U), σ(n) = n ∪ {n}
  - `isInductive` I : A set I is inductive if ∅ ∈ I and ∀ x ∈ I, σ(x) ∈ I
  - `isTransitiveSet` S : The set S is a transitive set if ∀ x ∈ S, x ⊆ S
  - `StrictOrderMembershipGuided` S : ∈[S] ∈ S ×ₛ S, where S is a transitive set,
        - ∀ p ∈ ∈[S], p is a pair (x, y) with x, y ∈ S, and p ∈[S] q iff x ∈ y
            - ∀ x y ∈ S, x ∈[S] y → ¬(y ∈[S] x) (asymmetry)
            - ∀ x y z ∈ S, x ∈[S] y → y ∈[S] z → x ∈[S] z (transitivity)
  - `TotalStrictOrderMembershipGuided` : ∀ x y ∈ S, x ∈[S] y ∨ x = y ∨ y ∈[S] x (trichotomy)
  - `WellOrderMembershipGuided` : ⟨S, ∈[S]⟩ is a well-ordered membership set, if and only if
        - ∀ T ∈ 𝒫 S:
            - T ≠ ∅ → ∃ m ∈ T, ∀ x ∈ T, m = x ∨ m ∈[S] x (existence of minimal element)
            - T ≠ ∅ → ∃ m ∈ T, ∀ x ∈ T, m = x ∨ x ∈[S] m (existence of maximal element)
  - `isNat` n : n is a natural number if and only if:
        - n is a transitive set
        - ∈[n] is a strict total order on n
        - ⟨n, ∈[n]⟩ is well-ordered by ∈[n]

  ## Firsts theorems
  - ∅ is a natural number by the previous definition
  - Examples:
    - 1 =  {∅},  is a natural number by the previous definition
    - 2 = {∅, {∅}},  is a natural number by the previous definition
    - 3 = {∅, {∅}, {∅, {∅}}} is a natural number by the previous definition
  - n is a natural number, then n ∉ n (regularity.1)
  - n m are natural numbers, then ¬(n ∈ m ∨ m ∈ n) (regularity.2)
  - n m are natural numbers, then n ∈ m → ¬(m ∈ n) (asymmetry of membership)
  - n is a natural number, then ∀ m ∈ n, m is a natural number (transitivity)
  - n m k are natural numbers, then n ∈ m ∧ m ∈ k → n ∈ k (transitivity of membership)
  - n m are natural numbers, then n = m ∨ n ∈ m ∨ m ∈ n (trichotomy)
  - n m k are natural numbers, then n ∈ m ∧ m ∈ k → n ∈ k (transitivity of membership)
  - ∈[n] is a well-ordered membership set (well-foundedness of each natural number)
  - isNat n → isNat (σ n) (closure under successor)
  - isNat n → ∀ m ∈ n, isNat m (closure under subsets)
  - ∀ n m, isNat n → isNat m → n ∈ m → ∀ k ∈ m, n ∈ k ∨ n = k (initial segment property)
  - ∀ n m, isNat n → isNat m → σ(n) = σ(m) → n = m (injectivity of successor)
  - ∀ n, isNat n → σ(n) ≠ ∅ (successor is never empty)
  - ∀ n, isNat n → n ∈ σ(n) (each natural number is in its successor)
  - ∀ n m, isNat n → isNat m → n ∈ m → n ∈ σ(m) (membership is preserved by successor)

  ## Main theorems
  - If I is an inductive set, and n is a natural number, then n ∈ I (ω is the smallest inductive set)
  - Induction principle: If P is a first order predicate of the natural number, and P(0) holds, and ∀ n, P(n) → P(σ(n)) holds, then
    ∀ n, Nat(n) → P(n) holds (induction principle) (this need a intermiadate elaboration)
-/

import Init.Classical
import ZfcSetTheory.Prelim
import ZfcSetTheory.Extension
import ZfcSetTheory.Existence
import ZfcSetTheory.Specification
import ZfcSetTheory.Pairing
import ZfcSetTheory.Union
import ZfcSetTheory.PowerSet
import ZfcSetTheory.OrderedPair
import ZfcSetTheory.CartesianProduct
import ZfcSetTheory.Relations
import ZfcSetTheory.Functions
import ZfcSetTheory.Cardinality

namespace SetUniverse
  open Classical
  open SetUniverse.ExtensionAxiom
  open SetUniverse.ExistenceAxiom
  open SetUniverse.SpecificationAxiom
  open SetUniverse.PairingAxiom
  open SetUniverse.UnionAxiom
  open SetUniverse.PowerSetAxiom
  open SetUniverse.OrderedPairExtensions
  open SetUniverse.CartesianProduct
  open SetUniverse.Relations
  open SetUniverse.Functions
  open SetUniverse.Cardinality
  universe u
  variable {U : Type u}

  namespace NaturalNumbers



  end NaturalNumbers

  export NaturalNumbers (

  )

end SetUniverse
