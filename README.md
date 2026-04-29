# ZfcSetTheory

[![Lean 4](https://img.shields.io/badge/Lean-v4.29.0-blue)](https://leanprover.github.io/)
[![Build Status](https://img.shields.io/badge/build-passing-brightgreen)](REFERENCE.md)
[![License](https://img.shields.io/badge/license-MIT-green)](LICENSE)
[![Modules](https://img.shields.io/badge/módulos-87-blue)](REFERENCE.md)
[![Sorry](https://img.shields.io/badge/sorry-0-brightgreen)](REFERENCE.md)

Una implementación formal de la **Teoría de Conjuntos de Zermelo-Fraenkel (ZFC)** en Lean 4, sin dependencias de Mathlib.

> **Estado actual** (2026-04-29): 87 módulos activos · **0 sorry** · 0 errores.
> Phase 6 (ℚ) 100% completa — 9 módulos. Phase 6.5 (Sucesiones en ℚ) — 6/7 módulos, 0 sorry.

---

## ¿Qué hace este proyecto?

Construye las matemáticas desde los axiomas de ZFC hacia arriba, en Lean 4 puro (sin Mathlib):

1. **Axiomas ZFC** — Extensionalidad, Vacío, Separación, Par, Unión, Potencia, Infinito
2. **Teoría de conjuntos** — Pares ordenados, producto cartesiano, relaciones, funciones, equipotencia
3. **Números naturales ℕ** — Ordinales de von Neumann con aritmética completa (+, ×, −, ÷, ^, GCD, LCM, factorial, binomio, TFA)
4. **Puente Peano ↔ von Neumann** — Isomorfismo ℕ_VN ↔ Peano.ℕ₀ con preservación de operaciones
5. **Secuencias finitas y conjuntos finitos** — Infraestructura para TFA y cardinalidad
6. **Álgebras de Boole** — Teorema de representación de Stone; correspondencia BR ↔ BA; cardinalidad 2^n
7. **Cardinalidad** — Cantor, Cantor-Schröder-Bernstein
8. **Enteros ℤ** — Construcción completa: +, −, ×, ÷ euclídea, ^, GCD, LCM, Bézout, TFA, valor absoluto, signo, orden total, inducción
9. **Racionales ℚ** — Construcción completa: equivalencia en ℤ×ℤ*, +, −, ×, ÷, |·|, orden total, embedding ℤ↪ℚ, propiedad arquimediana, axiomas de cuerpo
10. **Sucesiones en ℚ** — IsSeqQ, convergencia ε-N, límite único, aritmética de límites, sucesiones de Cauchy, acotamiento, monotonía; `nondecreasing_bounded_isCauchy` y `nonincreasing_bounded_isCauchy` por argumento arquimediano

---

## 🧱 Axiomas ZFC Implementados

| # | Axioma | Archivo | Estado |
|---|--------|---------|--------|
| 1 | **Extensionalidad** | `ZFC/Axiom/Extension.lean` | ✅ |
| 2 | **Existencia** (Conjunto Vacío) | `ZFC/Axiom/Existence.lean` | ✅ |
| 3 | **Especificación** (Separación) | `ZFC/Axiom/Specification.lean` | ✅ |
| 4 | **Par** | `ZFC/Axiom/Pairing.lean` | ✅ |
| 5 | **Unión** | `ZFC/Axiom/Union.lean` | ✅ |
| 6 | **Conjunto Potencia** | `ZFC/Axiom/PowerSet.lean` | ✅ |
| 7 | **Infinito** | `ZFC/Axiom/Infinity.lean` | ✅ |
| 8 | Reemplazo | — | 🔄 Futuro |
| 9 | Fundación | — | 🔄 Futuro |
| 10 | Elección | — | 🔄 Futuro |

---

## 📐 Módulos por Phase

### Phase 1–3: Fundamentos y Álgebra de Boole (✅ Completo)

| Módulo | Descripción |
|--------|-------------|
| `Core/Prelim.lean` | ExistsUnique, infraestructura básica |
| `SetOps/OrderedPair.lean` | Par de Kuratowski, fst/snd |
| `SetOps/CartesianProduct.lean` | A ×ₛ B, pertenencia, proyecciones |
| `SetOps/Relations.lean` | Equivalencia, orden parcial/lineal/estricto, clases de equivalencia |
| `SetOps/Functions.lean` | Funciones, inyectivas, suryectivas, biyectivas |
| `SetOps/FiniteSets.lean` | isFiniteSet, equipotencia refl/symm/trans |
| `SetOps/SetOrder.lean` | Retículos, órdenes parciales |
| `SetOps/SetStrictOrder.lean` | Órdenes estrictos |
| `Induction/Recursion.lean` | Teorema de Recursión sobre ω |
| `Nat/Basic.lean` | ω como ordinales de von Neumann |
| `Nat/Add.lean` | Suma en ω, puente fromPeano_add |
| `Nat/Mul.lean` | Multiplicación en ω, puente fromPeano_mul |
| `Nat/Sub.lean` | Sustracción saturada (monus) |
| `Nat/Div.lean` | División euclídea divOf/modOf |
| `Nat/Pow.lean` | Potenciación en ω |
| `Nat/Arith.lean` | Divisibilidad, GCD/LCM, Bézout nativo ZFC |
| `Nat/Factorial.lean` | Factorial vía Patrón B |
| `Nat/Gcd.lean` | GCD/LCM ZFC-nativo (algoritmo euclídeo) |
| `Nat/Primes.lean` | isPrime ZFC-nativo, TFA (existencia + unicidad) |
| `Nat/Binom.lean` | Coeficientes binomiales, regla de Pascal |
| `Nat/MaxMin.lean` | maxOf/minOf, 29 teoremas de retículo |
| `Nat/NewtonBinom.lean` | Teorema binomial de Newton |
| `Nat/WellFounded.lean` | Buen fundamento de ω |
| `Peano/Import.lean` | Isomorfismo ℕ_VN ↔ Peano.ℕ₀ |
| `Peano/FiniteSequences.lean` | isFinSeq, FinSeqSet, appendElem |
| `Peano/FiniteSequencesArith.lean` | seqSum, seqProd, familyProduct |
| `Peano/FiniteSequencesBridge.lean` | nth, dlistToSeq, isPrimeSeq, TFA nativo |
| `BoolAlg/Basic.lean` | Leyes fundamentales, idempotencia, absorción |
| `BoolAlg/Ring.lean` | Diferencia simétrica, propiedades de anillo booleano |
| `BoolAlg/PowerSetAlgebra.lean` | Complemento, De Morgan, distributividad |
| `BoolAlg/GenDeMorgan.lean` | Leyes de De Morgan para familias arbitrarias |
| `BoolAlg/GenDistributive.lean` | Leyes distributivas para familias arbitrarias |
| `BoolAlg/Atomic.lean` | 𝒫(A) es atómica; los singletons son los átomos |
| `BoolAlg/Complete.lean` | 𝒫(A) es retículo completo y AB completa atómica |
| `BoolAlg/FiniteCofinite.lean` | FinCofAlg(ω), contraejemplo de completitud |
| `BoolAlg/Representation.lean` | Toda BA completa atómica ≅ 𝒫(A) (Stone) |
| `BoolAlg/FiniteBA.lean` | Toda BA finita tiene cardinalidad 2^n |
| `BoolAlg/BoolRingBA.lean` | Correspondencia Anillo Booleano ↔ Álgebra Booleana |
| `Cardinal/Basic.lean` | Teorema de Cantor, Cantor-Schröder-Bernstein |
| `Cardinal/FinitePowerSet.lean` | |𝒫(F)| = 2^n para F finito |

### Phase 5: Enteros ℤ (✅ Completo — 190 exports, 0 sorry)

| Módulo | Exports clave |
|--------|--------------|
| `Int/Equiv.lean` | IntEquivRel, reflexividad, simetría, transitividad |
| `Int/Basic.lean` | IntSet, intClass, zeroZ, oneZ, intClass_eq_iff, tricotomía |
| `Int/Add.lean` | addZ, conmutatividad, asociatividad, identidades |
| `Int/Neg.lean` | negZ, subZ, inversos aditivos, involución, subZ_self |
| `Int/Mul.lean` | mulZ, conmutatividad, asociatividad, identidades, absorbente |
| `Int/Ring.lean` | distributividad, dominio de integridad, cancelación, difference_of_squares |
| `Int/Sub.lean` | subZ con identidades, cancelaciones, asociatividad mixta |
| `Int/Order.lean` | leZ, ltZ, orden total, square_nonneg, leZ_is_linear_order |
| `Int/DivMod.lean` | dividesZ, reflexividad, transitividad, one_dividesZ |
| `Int/Embedding.lean` | natToInt, inyección ω → ℤ, preserva +/×/≤, zigzag biyección ℤ ≃ ω |
| `Int/Abs.lean` | absZ, signZ, absZ_mulZ, signZ_mulZ_absZ, absZ_addZ_le, absZ_mulZ_nonneg |
| `Int/Div.lean` | gcdZ, modZ, quotZ, lcmZ, euclidean_divisionZ, bezoutZ, tfa_Z |
| `Int/Pow.lean` | powZ, powZ_add_exp, powZ_mul_base, powZ_powZ, powZ_negZ_odd |
| `Int/Induction.lean` | int_induction_abs, int_strong_induction_abs, int_descent, int_induction_neg |
| `Int/Units.lean` | isUnitZ, unitZ_iff (unidades = {oneZ, negZ oneZ}) |

### Phase 6: Racionales ℚ (✅ Completo — 0 sorry)

| Módulo | Exports clave |
|--------|---------------|
| `Rat/Equiv.lean` | NonZeroIntSet, RatBase, RatEquivRel, RatSet, RatEquivRel_is_equivalence |
| `Rat/Basic.lean` | ratClass, zeroQ, oneQ, ratClass_mem_RatSet, ratClass_eq_iff |
| `Rat/Add.lean` | addQ, addQ_comm, addQ_assoc, addQ_zeroQ_right, addQ_in_RatSet |
| `Rat/Neg.lean` | negQ, negQ_in_RatSet, negQ_addQ_right, negQ_negQ |
| `Rat/Mul.lean` | mulQ, invQ, divQ, mulQ_comm, mulQ_assoc, mulQ_oneQ, invQ_mem |
| `Rat/Abs.lean` | subQ, absQ, signQ, triángulo, interacción absQ/mulQ, archZ |
| `Rat/Order.lean` | leQ, ltQ, isPositiveQ, isNegativeQ, orden total, compatibilidad +/× |
| `Rat/Embedding.lean` | intToRat, homomorfismo +/−/×/≤/<, intToRat_injective, archQ |
| `Rat/Field.lean` | mulQ_eq_zero_iff, mulQ_left_cancel, invQ_invQ, invQ_mulQ, divQ_self, distribQ |

### Phase 6.5: Sucesiones en ℚ (🔄 En progreso — 6/7, 0 sorry)

| Módulo | Exports clave |
|--------|---------------|
| `Int/MaxMin.lean` | maxZ, minZ, 18 teoremas de retículo en ℤ |
| `Rat/MaxMin.lean` | maxQ, minQ, 18 teoremas de retículo en ℚ |
| `Rat/Sequences.lean` | IsSeqQ, constSeqQ, addSeqQ, negSeqQ, mulSeqQ |
| `Rat/Convergence.lean` | convergesToQ, hasLimitQ, IsSubseqOf, limit_unique, convergesToQ_add, convergesToQ_mul_bounded, subseq_convergent |
| `Rat/CauchyQ.lean` | IsCauchyQ, cauchy_of_convergentQ, cauchy_bounded, constSeqQ_isCauchy |
| `Rat/Monotone.lean` | isNondecreasingQ, isNonincreasingQ, isBoundedQ, nondecreasing_bounded_isCauchy, nonincreasing_bounded_isCauchy, convergent_isBounded |
| `Rat/SqrtApprox.lean` | *(no iniciado — prueba de incompletitud de ℚ)* |

---

## 🏆 Teoremas Destacados

### Teorema Fundamental de la Aritmética (TFA) — en ℕ y en ℤ

```lean
-- En ω (Nat/Primes.lean):
theorem exists_prime_factorization_ZFC (n : U) (hn : n ∈ (ω : U))
    (hn_ne : n ≠ ∅) (hn_nunit : n ≠ σ ∅) :
    ∃ ps : DList ℕ₀, PrimeList ps ∧ n = fromPeano (product_list ps)

-- En ℤ (Int/Div.lean):
theorem tfa_Z (z : U) (hz : z ∈ (IntSet : U)) (hz_ne : z ≠ zeroZ)
    (hz_unit : ¬isUnitZ z) :
    ∃ (u : U) (ps : DList ℕ₀),
      isUnitZ u ∧ PrimeList ps ∧
      z = mulZ u (natToInt (fromPeano (product_list ps)))
```

### Identidad de Bézout en ℤ

```lean
theorem bezoutZ (a b : U) (ha : a ∈ IntSet) (hb : b ∈ IntSet) :
    ∃ s t : U, s ∈ IntSet ∧ t ∈ IntSet ∧
      natToInt (gcdZ a b) = addZ (mulZ s a) (mulZ t b)
```

### Teorema de Representación de Stone

```lean
theorem Stone_representation (B : U) (hB : isCompleteAtomicBA B) :
    ∃ A : U, isBAIsomorphic B (PowerSetAlgebra A)
```

### Cantor-Schröder-Bernstein

```lean
theorem cantor_schroeder_bernstein (A B f g : U) ... :
    isInjective f A B → isInjective g B A → ∃ h, isBijective h A B
```

---

## 📁 Estructura del Proyecto

```text
ZfcSetTheory/
├── ZFC.lean                    # Módulo raíz
├── lakefile.lean               # Configuración Lake
├── lean-toolchain              # Lean v4.29.0
├── REFERENCE.md                # Referencia técnica completa (17000+ líneas)
├── NEXT-STEPS.md               # Hoja de ruta
└── ZFC/
    ├── Axiom/                  # 7 axiomas ZFC
    ├── Core/                   # Prelim (ExistsUnique)
    ├── SetOps/                 # Pares, cartesiano, relaciones, funciones, conjuntos finitos
    ├── Induction/              # Teorema de recursión
    ├── Nat/                    # ℕ completo (14 módulos)
    ├── Peano/                  # Puentes Peano ↔ von Neumann (4 módulos)
    ├── BoolAlg/                # Álgebras de Boole (11 módulos)
    ├── Cardinal/               # Cardinalidad (2 módulos)
    ├── Int/                    # ℤ completo (16 módulos, incl. MaxMin)
    └── Rat/                    # ℚ + Sucesiones (14 módulos)
```

---

## 📚 Documentación

| Documento | Contenido |
|-----------|-----------|
| [REFERENCE.md](REFERENCE.md) | Referencia técnica completa: 18000+ líneas, todas las definiciones y teoremas con firma Lean4, anotaciones `@importance` |
| [NEXT-STEPS.md](NEXT-STEPS.md) | Hoja de ruta detallada: Phase 6 (ℚ), Phase 7 (ℝ), futuro |
| [THOUGHTS.md](THOUGHTS.md) | Notas de diseño y reflexiones; qué está hecho, en progreso y en el futuro lejano |
| [NAMING-CONVENTIONS.md](NAMING-CONVENTIONS.md) | Convenciones de nombres estilo Mathlib |
| [CHANGELOG.md](CHANGELOG.md) | Historial de cambios |

---

## 🛠️ Instalación

```bash
git clone https://github.com/julian1c2a/ZfcSetTheory.git
cd ZfcSetTheory
lake build
```

**Requisitos**: Lean 4 v4.29.0 (via `lean-toolchain`), Lake. Sin dependencias de Mathlib.

---

## 📄 Licencia

MIT — ver [LICENSE](LICENSE).

## 👤 Autor

Julián Calderón Almendros

## 🙏 Referencias

- **"Razonando con Lean"** — José A. Alonso
- **Adrián GQ** ([@conjuntos_y_logica](https://www.youtube.com/@conjuntos_y_logica)) — cursos de teoría de conjuntos
- **"Axiomatic Set Theory"** — Patrick Suppes (1960/1972)
- **"Axiomatic Set Theory"** — Paul Bernays (1958)
- Asistencia IA: Claude (Anthropic) vía GitHub Copilot
