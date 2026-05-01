/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT

# ℚ es incompleto: √2 es irracional

Este fichero contiene la demostración de la irracionalidad de √2 en ZFC y la
no-convergencia en ℚ de la sucesión de Newton–Raphson `sqrtApproxSeq`. Estas
demostraciones requieren `ZFC.Nat.Primes` (descenso 2-ádico vía Peano), cuya
cadena transitiva de imports (`PeanoNatLib.PeanoNatArith`) declara una
notación global `notation:50 a " ∈ " l => DList.Mem a l` que entra en
conflicto con la notación ZFC `∈` en patrones del estilo
`p ∈ X ↔ p ∈ Y ∧ ...`. Por eso, este fichero se mantiene separado de
`ZFC/Rat/SqrtApprox.lean`: aquí no usamos esos patrones y la notación ZFC
sigue funcionando.

REFERENCE.md: Este archivo debe proyectarse en REFERENCE.md cuando compile.
-/

import ZFC.Rat.SqrtApprox
import ZFC.Nat.Primes

namespace ZFC
  open Classical
  open ZFC.Axiom.Extension
  open ZFC.Axiom.Existence
  open ZFC.Axiom.Specification
  open ZFC.Axiom.Pairing
  open ZFC.Axiom.Union
  open ZFC.Axiom.PowerSet
  open ZFC.Axiom.Infinity
  open ZFC.SetOps.OrderedPair
  open ZFC.SetOps.CartesianProduct
  open ZFC.SetOps.Relations
  open ZFC.SetOps.Functions
  open ZFC.Nat.Basic
  open ZFC.Nat.MaxMin
  open ZFC.Nat.Primes
  open ZFC.Int.Basic
  open ZFC.Int.Add
  open ZFC.Int.Mul
  open ZFC.Int.Order
  open ZFC.Rat.Equiv
  open ZFC.Rat.Basic
  open ZFC.Rat.Add
  open ZFC.Rat.Neg
  open ZFC.Rat.Mul
  open ZFC.Rat.Order
  open ZFC.Rat.Abs
  open ZFC.Rat.Field
  open ZFC.Rat.MaxMin
  open ZFC.Rat.Sequences
  open ZFC.Rat.Convergence
  open ZFC.Rat.CauchyQ
  open ZFC.Rat.Monotone
  open ZFC.Rat.SqrtApprox

  universe u
  variable {U : Type u}

  namespace Rat.SqrtIrrational

    /-- √2 es irracional: ningún racional L satisface L · L = 2.

        Esquema de demostración (descenso 2-ádico sobre enteros):
        Si L = a/b y (a/b)² = 2, entonces a² = 2·b² en ℤ. Tomando |·| y
        viendo en ω, queda |a|² = 2·|b|². Por `omega_descent_two_squares`
        (descenso infinito vía 2 primo en Peano) deducimos |a| = 0, luego
        a = 0. Sustituyendo en a² = 2·b² obtenemos 0 = 2·b², pero el
        producto de no-nulos es no-nulo: contradicción. -/
    theorem sqrt2_irrational :
        ¬ ∃ L : U, (L ∈ (RatSet : U)) ∧ mulQ L L = addQ (oneQ : U) (oneQ : U) := by
      -- Abreviatura local: el entero ZFC 2 = intClass (σ σ ∅) ∅
      let twoZint : U := intClass (σ (σ (∅ : U))) ∅
      -- Pertenencias auxiliares usadas a continuación
      have h_two_omega : σ (σ (∅ : U)) ∈ (ω : U) :=
        succ_in_Omega _ (succ_in_Omega ∅ zero_in_Omega)
      have h_twoZint_int : twoZint ∈ (IntSet : U) :=
        intClass_mem_IntSet _ _ h_two_omega zero_in_Omega
      have h_twoZint_ne : twoZint ≠ zeroZ := by
        intro h
        unfold twoZint zeroZ at h
        rw [intClass_eq_iff (σ (σ (∅ : U))) ∅ ∅ ∅
              h_two_omega zero_in_Omega zero_in_Omega zero_in_Omega] at h
        rw [add_zero (σ (σ (∅ : U))) h_two_omega,
            zero_add (∅ : U) zero_in_Omega] at h
        exact succ_nonempty (σ (∅ : U)) h
      have h_twoZint_nz : twoZint ∈ (NonZeroIntSet : U) :=
        (mem_NonZeroIntSet twoZint).mpr ⟨h_twoZint_int, h_twoZint_ne⟩
      -- addQ oneQ oneQ = ratClass twoZint oneZ
      have h_addQ_one_one : addQ (oneQ : U) (oneQ : U) =
            ratClass twoZint oneZ := by
        unfold oneQ
        rw [addQ_class oneZ oneZ oneZ oneZ
              oneZ_mem_IntSet oneZ_mem_NonZeroIntSet
              oneZ_mem_IntSet oneZ_mem_NonZeroIntSet]
        rw [mulZ_one_left oneZ oneZ_mem_IntSet]
        have h_addZ : addZ (oneZ : U) oneZ = twoZint := by
          unfold oneZ twoZint
          have h_one_om : (σ (∅ : U)) ∈ (ω : U) := succ_in_Omega (∅ : U) zero_in_Omega
          rw [addZ_class (σ (∅ : U)) (∅ : U) (σ (∅ : U)) (∅ : U)
                h_one_om zero_in_Omega h_one_om zero_in_Omega]
          rw [add_succ (σ (∅ : U)) (∅ : U) h_one_om zero_in_Omega,
              add_zero (σ (∅ : U)) h_one_om,
              add_zero (∅ : U) zero_in_Omega]
        rw [h_addZ]
      -- absZ twoZint = σ σ ∅
      have h_absZ_two : absZ twoZint = σ (σ (∅ : U)) := by
        unfold twoZint
        exact absZ_intClass_pos _ h_two_omega
      -- Suponemos que existe L; derivamos contradicción
      rintro ⟨L, hL, hLsq⟩
      obtain ⟨a, b, ha, hb, rfl⟩ := mem_RatSet_is_ratClass L hL
      rw [mulQ_class a b a b ha hb ha hb, h_addQ_one_one] at hLsq
      have h_b_int : b ∈ (IntSet : U) := NonZeroIntSet_mem_IntSet b hb
      have h_b_ne : b ≠ zeroZ := NonZeroIntSet_ne_zero b hb
      have h_bb_int : mulZ b b ∈ (IntSet : U) := mulZ_in_IntSet b b h_b_int h_b_int
      have h_bb_ne : mulZ b b ≠ zeroZ :=
        mulZ_nonzero_of_nonzero b b h_b_int h_b_int h_b_ne h_b_ne
      have h_bb_nz : mulZ b b ∈ (NonZeroIntSet : U) :=
        (mem_NonZeroIntSet _).mpr ⟨h_bb_int, h_bb_ne⟩
      have h_aa_int : mulZ a a ∈ (IntSet : U) := mulZ_in_IntSet a a ha ha
      rw [ratClass_eq_iff (mulZ a a) (mulZ b b) twoZint oneZ
            h_aa_int h_bb_nz h_twoZint_int oneZ_mem_NonZeroIntSet] at hLsq
      rw [mulZ_one_right (mulZ a a) h_aa_int] at hLsq
      -- hLsq : mulZ a a = mulZ (mulZ b b) twoZint
      have h_abs : absZ (mulZ a a) = absZ (mulZ (mulZ b b) twoZint) := by
        rw [hLsq]
      rw [absZ_mulZ a a ha ha,
          absZ_mulZ (mulZ b b) twoZint h_bb_int h_twoZint_int,
          absZ_mulZ b b h_b_int h_b_int,
          h_absZ_two] at h_abs
      have h_absA_om : absZ a ∈ (ω : U) := absZ_in_omega a ha
      have h_absB_om : absZ b ∈ (ω : U) := absZ_in_omega b h_b_int
      have h_absBB_om : mul (absZ b) (absZ b) ∈ (ω : U) :=
        mul_in_Omega _ _ h_absB_om h_absB_om
      rw [mul_comm_Omega (mul (absZ b) (absZ b)) (σ (σ (∅ : U)))
            h_absBB_om h_two_omega] at h_abs
      -- h_abs : mul (absZ a) (absZ a) = mul (σ σ ∅) (mul (absZ b) (absZ b))
      have h_a_zero : absZ a = (∅ : U) :=
        omega_descent_two_squares (absZ a) (absZ b) h_absA_om h_absB_om h_abs
      have h_a_eq : a = zeroZ := (absZ_eq_zero_iff a ha).mp h_a_zero
      -- Sustituyendo a = zeroZ: mulZ a a = zeroZ
      have h_lhs_aa : mulZ a a = zeroZ := by
        rw [h_a_eq, mulZ_zero_left zeroZ zeroZ_mem_IntSet]
      rw [h_lhs_aa] at hLsq
      -- hLsq : zeroZ = mulZ (mulZ b b) twoZint
      have h_prod_ne : mulZ (mulZ b b) twoZint ≠ zeroZ :=
        mulZ_nonzero_of_nonzero (mulZ b b) twoZint h_bb_int h_twoZint_int
          h_bb_ne h_twoZint_ne
      exact h_prod_ne hLsq.symm

    /-- Identidad puntual de la recurrencia Newton–Raphson:
        para todo `n ∈ ω`, si `f := sqrtApproxSeq`, entonces
        `2 · (f(σn) · f(n)) = f(n) · f(n) + 2`.

        Sale de `f(σn) = (f(n) + 2/f(n)) / 2` multiplicando por `2·f(n)`
        y usando que `f(n) > 0` (en particular `f(n) ≠ 0`). -/
    private theorem sqrtApproxSeq_pointwise_identity (n : U) (hn : n ∈ (ω : U)) :
        mulQ (twoQ : U) (mulQ ((sqrtApproxSeq : U)⦅σ n⦆) ((sqrtApproxSeq : U)⦅n⦆)) =
        addQ (mulQ ((sqrtApproxSeq : U)⦅n⦆) ((sqrtApproxSeq : U)⦅n⦆)) (twoQ : U) := by
      have hf : IsSeqQ (sqrtApproxSeq : U) := sqrtApproxSeq_isSeqQ
      have hfn : (sqrtApproxSeq : U)⦅n⦆ ∈ (RatSet : U) :=
        seqTermQ_mem_RatSet (sqrtApproxSeq : U) n hf hn
      have hf_pos : isPositiveQ ((sqrtApproxSeq : U)⦅n⦆) := sqrtApproxSeq_pos n hn
      have hfn_ne : (sqrtApproxSeq : U)⦅n⦆ ≠ (zeroQ : U) := fun h => hf_pos.2 h.symm
      have h2 : (twoQ : U) ∈ (RatSet : U) := twoQ_mem
      have h2_ne : (twoQ : U) ≠ (zeroQ : U) := twoQ_ne_zeroQ
      have h2overFn : divQ (twoQ : U) ((sqrtApproxSeq : U)⦅n⦆) ∈ (RatSet : U) :=
        divQ_in_RatSet (twoQ : U) ((sqrtApproxSeq : U)⦅n⦆) h2 hfn
      have h_sum :
          addQ ((sqrtApproxSeq : U)⦅n⦆) (divQ (twoQ : U) ((sqrtApproxSeq : U)⦅n⦆))
            ∈ (RatSet : U) :=
        addQ_in_RatSet ((sqrtApproxSeq : U)⦅n⦆)
          (divQ (twoQ : U) ((sqrtApproxSeq : U)⦅n⦆)) hfn h2overFn
      have h_succ : (sqrtApproxSeq : U)⦅σ n⦆ =
          divQ (addQ ((sqrtApproxSeq : U)⦅n⦆)
            (divQ (twoQ : U) ((sqrtApproxSeq : U)⦅n⦆))) (twoQ : U) :=
        sqrtApproxSeq_apply_succ n hn
      rw [h_succ]
      rw [← mulQ_assoc (twoQ : U)
            (divQ (addQ ((sqrtApproxSeq : U)⦅n⦆)
              (divQ (twoQ : U) ((sqrtApproxSeq : U)⦅n⦆))) (twoQ : U))
            ((sqrtApproxSeq : U)⦅n⦆)
            h2 (divQ_in_RatSet _ _ h_sum h2) hfn]
      rw [mulQ_divQ_cancel
            (addQ ((sqrtApproxSeq : U)⦅n⦆)
              (divQ (twoQ : U) ((sqrtApproxSeq : U)⦅n⦆)))
            (twoQ : U) h_sum h2 h2_ne]
      rw [mulQ_addQ_distrib_right ((sqrtApproxSeq : U)⦅n⦆)
            (divQ (twoQ : U) ((sqrtApproxSeq : U)⦅n⦆))
            ((sqrtApproxSeq : U)⦅n⦆) hfn h2overFn hfn]
      rw [divQ_mulQ_cancel (twoQ : U) ((sqrtApproxSeq : U)⦅n⦆) h2 hfn hfn_ne]

    /-- La sucesión Newton–Raphson `sqrtApproxSeq` no tiene límite en ℚ.
        Esto demuestra que ℚ no es (secuencialmente) completo. -/
    theorem sqrtApproxSeq_not_convergent :
        ¬ ∃ L : U, (L ∈ (RatSet : U)) ∧ convergesToQ (sqrtApproxSeq : U) L := by
      sorry

  end Rat.SqrtIrrational

end ZFC

export ZFC.Rat.SqrtIrrational (
  sqrt2_irrational
  sqrtApproxSeq_not_convergent
)
