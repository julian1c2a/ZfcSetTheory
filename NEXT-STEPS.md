# Next Steps — ZfcSetTheory Project

**Last updated**: 2026-04-23

---

## Milestones completados

- ✅ **Aritmética en ω** (14 módulos): TFA, binomiales, maxmin, Newton, well-foundedness, GCD/LCM
- ✅ **Secuencias finitas** (3 módulos): isFinSeq, seqSum/seqProd, familyProduct, puente DList↔ZFC
- ✅ **Conjuntos finitos** (1 módulo): isFiniteSet, biyecciones, equipotencia
- ✅ **Cardinalidad** (2 módulos): Cantor, CSB, |𝒫(F)|=2^n
- ✅ **Álgebras de Boole** (11 módulos): Basic, Ring, PowerSetAlgebra, GenDeMorgan, GenDistributive, Atomic, Complete, Representation, FiniteCofinite, FiniteBA, BoolRingBA
- ✅ **Reorganización Fases 1–3**: namespaces `ZFC`, convenciones Mathlib (185 renames)
- ✅ **Anotaciones REFERENCE.md** (Phase 4): @axiom_system, @importance, ~280 teoremas anotados
- ✅ **Enteros ℤ** (Phase 5, 15 módulos): 190 exports, 0 sorry, 0 errores

**Estado**: 76 jobs, 0 sorry, 0 errores de compilación.

---

## Phase 5: Enteros ℤ — ✅ COMPLETA (2026-04-23)

15 archivos · 190 exports · 0 sorry

| Archivo | Exports | Temas cubiertos |
|---------|---------|-----------------|
| Equiv | 7 | IntEquivRel, reflexividad, simetría, transitividad, equivalencia |
| Basic | 15 | IntSet, intClass, zeroZ, oneZ, pertenencia, igualdad de clases, representantes canónicos, inyectividad, tricotomía |
| Add | 9 | addZ, grafo funcional, buena definición, clase, clausura, conmutatividad, asociatividad, identidades |
| Neg | 12 | negZ, subZ, buena definición, clausura, clase, inversos aditivos, involución, negZ_zero, homomorfismo, subZ_self |
| Mul | 15 | mulZ, grafo funcional, buena definición, clase, clausura, conmutatividad, asociatividad, identidades, absorbente, negación×producto |
| Ring | 9 | distributividad izq/der, mulZ_eq_zero_iff, cancelación izq/der, isUnitZ, unitZ_iff |
| Sub | 12 | subZ con identidades, inversos, cancelaciones, asociatividad mixta |
| DivMod | 14 | dividesZ, reflexividad, transitividad, zero, negación, multiplicación, one_dividesZ, add, sub |
| Order | 27 | leZ, ltZ, buena definición, reflexividad, transitividad, antisimetría, totalidad, compatibilidad +/×, tricotomía, signo de productos |
| Embedding | 16 | natToInt, grafo, clausura, función, inyectividad, preserva +/×/≤, refleja ≤, no suryectiva, zigzag biyección, equipotencia |
| Abs | 17 | absZ, signZ, clausura ω, eq_zero_iff, negZ, mulZ, sign values/closure/decomposition, mulZ sign, triangular, absZ_pos, absZ_mulZ_nonneg, absZ_subZ_le |
| Div | 25 | gcdZ, modZ, lcmZ, quotZ, clausura, conmutatividad, zero, modZ_lt_absZ, gcdZ divide izq/der, gcdZ_is_greatest, dividesZ_antisymm, gcdZ_assoc, lcmZ_zero_right/left, euclidean_divisionZ, bezoutZ, tfa_Z |
| Pow | 16 | powZ, eq/clausura/zero/succ/one, oneZ_powZ, zeroZ_powZ, powZ_add_exp, powZ_mul_base, powZ_negZ_sq, powZ_powZ, powZ_negZ_odd |
| Induction | 4 | int_induction_abs, int_strong_induction_abs, int_well_ordering_abs, int_induction_nonneg, int_descent, int_induction_neg |
| Units | 9 | (incluido en Ring) isUnitZ, unitZ_iff, unidades de ℤ son ±1 |

---

## Phase 6: Racionales ℚ — 🔄 En progreso

### Resumen de módulos

| # | Módulo | Estado | Contenido principal |
|---|--------|--------|---------------------|
| 1 | `Rat/Equiv.lean` | ✅ 16 exports | NonZeroIntSet, RatBase, RatEquivRel, reflexividad, simetría, transitividad, RatSet |
| 2 | `Rat/Basic.lean` | ✅ 13 exports | ratClass, zeroQ, oneQ, igualdad de clases, clase nula |
| 3 | `Rat/Add.lean` | ✅ 7 exports | addQ bien definida, grupo abeliano (ℚ, +) |
| 4 | `Rat/Neg.lean` | ✅ 7 exports | negQ, subQ, inverso aditivo |
| 5 | `Rat/Mul.lean` | ✅ 18 exports | mulQ bien definida, anillo; invQ (todo ≠ 0 es unidad); divQ; powQ_nat; powQ_int |
| 6 | `Rat/Order.lean` | ✅ 17 exports | leQ, ltQ, orden total bien definido, compatibilidad +/× |
| 7 | `Rat/Abs.lean` | 📋 Siguiente | absQ, signQ, desigualdad triangular |
| 8 | `Rat/Embedding.lean` | 📋 | intToRat: embedding de anillos ℤ→ℚ; preserva orden; Arquimediano; biyección ℚ≈ω |
| 9 | `Rat/Field.lean` | 📋 | ℚ es cuerpo ordenado; bundled theorems |
| 10 | `Rat/Sequences.lean` | 📋 | sucesiones f: ω → ℚ, convergencia, Cauchy, sucesión de Newton para √2 |
| 11 | `Rat/Computable.lean` | 🔮 | números computables como sucesiones de Cauchy + testigo de convergencia |
| 12 | `Rat/Algebraic.lean` | 🔮 | números algebraicos, raíces de polinomios sobre ℤ |

---

### Plan detallado — Primera parte

Los 7 objetivos del usuario se organizan así:

| Objetivo | Módulo principal |
|----------|-----------------|
| [1] Orden total lineal en ℚ, bien definido en clases | `Rat/Order.lean` |
| [2] Embedding ℤ↪ℚ preserva el orden | `Rat/Embedding.lean` |
| [2.1] Operaciones bien definidas respecto a las clases | `Rat/Add`, `Rat/Neg`, `Rat/Mul` |
| [2.2] Todo racional ≠ 0 es una unidad | `Rat/Mul.lean` |
| [3] Estructura de cuerpo en ℚ | `Rat/Field.lean` |
| [4] El embedding ℤ→ℚ respeta la estructura de anillo | `Rat/Embedding.lean` |
| [5] Propiedad Arquimediana en ℤ se preserva en ℚ | `Rat/Embedding.lean` |
| [6] Los racionales son densos | `Rat/Order.lean` |
| [7] Biyección ℚ ≈ ω (misma cardinalidad) | `Rat/Embedding.lean` |

---

#### Rat/Basic.lean — Definiciones fundamentales

**Dependencias**: `Rat/Equiv.lean`, `Int/Ring.lean`

**Definiciones**:

| # | Nombre | Descripción |
|---|--------|-------------|
| 1 | `ratClass a b` | La clase de equivalencia `[(a,b)]` en `RatSet` |
| 2 | `zeroQ` | `ratClass zeroZ oneZ` — cero de ℚ |
| 3 | `oneQ` | `ratClass oneZ oneZ` — uno de ℚ |

**Teoremas**:

| # | Nombre | Enunciado |
|---|--------|-----------|
| 1 | `ratClass_mem_RatSet` | `a ∈ IntSet → b ∈ NonZeroIntSet → ratClass a b ∈ RatSet` |
| 2 | `ratClass_eq_iff` | `ratClass a b = ratClass c d ↔ mulZ a d = mulZ b c` |
| 3 | `ratClass_ne_iff` | `ratClass a b ≠ ratClass c d ↔ mulZ a d ≠ mulZ b c` |
| 4 | `zeroQ_mem_RatSet` | `zeroQ ∈ RatSet` |
| 5 | `oneQ_mem_RatSet` | `oneQ ∈ RatSet` |
| 6 | `zeroQ_ne_oneQ` | `zeroQ ≠ oneQ` |
| 7 | `ratClass_eq_zeroQ_iff` | `ratClass a b = zeroQ ↔ a = zeroZ` (denominador irrelevante para ser cero) |

---

#### Rat/Add.lean — Suma y grupo abeliano (ℚ, +)

**Dependencias**: `Rat/Basic.lean`, `Int/Add.lean`, `Int/Mul.lean`

**Definiciones**:

| # | Nombre | Descripción |
|---|--------|-------------|
| 1 | `addQ_raw a b c d` | `ratClass (addZ (mulZ a d) (mulZ b c)) (mulZ b d)` — suma de representantes |
| 2 | `addQ_graph` | Grafo funcional de `addQ` vía `QuotientLift₂` |
| 3 | `addQ x y` | Suma en ℚ: `apply addQ_graph ⟨x, y⟩` |

**Teoremas** ([2.1] bien definición y propiedades):

| # | Nombre | Enunciado |
|---|--------|-----------|
| 1 | `mulZ_nonzero_of_nonzero` | `a ≠ zeroZ → b ≠ zeroZ → mulZ a b ≠ zeroZ` — clausura de ℤ\* bajo ×; necesario para que el denominador `mulZ b d` ∈ NonZeroIntSet |
| 2 | `addQ_raw_denom_nonzero` | `b ∈ NonZeroIntSet → d ∈ NonZeroIntSet → mulZ b d ∈ NonZeroIntSet` |
| 3 | `addQ_well_defined` | Si `(a,b)~(a',b')` y `(c,d)~(c',d')` entonces `addQ_raw a b c d ~ addQ_raw a' b' c' d'`. *Prueba*: expansión directa usando `mulZ_assoc`, `mulZ_comm`, y la hipótesis de equivalencia. |
| 4 | `addQ_class` | `addQ (ratClass a b) (ratClass c d) = ratClass (addZ (mulZ a d) (mulZ b c)) (mulZ b d)` |
| 5 | `addQ_in_RatSet` | `x y ∈ RatSet → addQ x y ∈ RatSet` |
| 6 | `addQ_comm` | `addQ x y = addQ y x` |
| 7 | `addQ_assoc` | `addQ (addQ x y) z = addQ x (addQ y z)` |
| 8 | `addQ_zero_left` | `addQ zeroQ x = x` |
| 9 | `addQ_zero_right` | `addQ x zeroQ = x` |

---

#### Rat/Neg.lean — Negación, sustracción

**Dependencias**: `Rat/Add.lean`, `Int/Neg.lean`

**Definiciones**:

| # | Nombre | Descripción |
|---|--------|-------------|
| 1 | `negQ x` | `negQ (ratClass a b) := ratClass (negZ a) b` — negar el numerador |
| 2 | `subQ x y` | `addQ x (negQ y)` |

**Teoremas** ([2.1] bien definición y propiedades):

| # | Nombre | Enunciado |
|---|--------|-----------|
| 1 | `negQ_well_defined` | Si `(a,b)~(c,d)` entonces `(negZ a, b)~(negZ c, d)`. *Prueba*: `mulZ (negZ a) d = negZ (mulZ a d) = negZ (mulZ b c) = mulZ (negZ b) c`... verificar signos. |
| 2 | `negQ_class` | `negQ (ratClass a b) = ratClass (negZ a) b` |
| 3 | `negQ_in_RatSet` | `x ∈ RatSet → negQ x ∈ RatSet` |
| 4 | `addQ_negQ_right` | `addQ x (negQ x) = zeroQ` |
| 5 | `addQ_negQ_left` | `addQ (negQ x) x = zeroQ` |
| 6 | `negQ_negQ` | `negQ (negQ x) = x` |
| 7 | `negQ_zeroQ` | `negQ zeroQ = zeroQ` |
| 8 | `negQ_addQ` | `negQ (addQ x y) = addQ (negQ x) (negQ y)` |
| 9 | `subQ_self` | `subQ x x = zeroQ` |
| 10 | `subQ_in_RatSet` | `x y ∈ RatSet → subQ x y ∈ RatSet` |

---

#### Rat/Mul.lean — Producto, inverso, división y exponenciación entera

**Dependencias**: `Rat/Neg.lean`, `Int/Mul.lean`, `Int/Ring.lean`, `Int/Pow.lean`

##### Producto

**Definiciones**:

| # | Nombre | Descripción |
|---|--------|-------------|
| 1 | `mulQ_raw a b c d` | `ratClass (mulZ a c) (mulZ b d)` |
| 2 | `mulQ_graph` | Grafo funcional vía `QuotientLift₂` |
| 3 | `mulQ x y` | Producto en ℚ |

**Teoremas** ([2.1] bien definición, anillo, sin divisores de cero):

| # | Nombre | Enunciado |
|---|--------|-----------|
| 1 | `mulQ_well_defined` | Si `(a,b)~(a',b')` y `(c,d)~(c',d')` entonces `(ac,bd)~(a'c',b'd')`. *Prueba*: `a·d=b·c` y `c·d'=d·c'` implican `(ac)·(b'd') = (bd)·(a'c')` por rearranjo con `mulZ_assoc/comm`. |
| 2 | `mulQ_class` | `mulQ (ratClass a b) (ratClass c d) = ratClass (mulZ a c) (mulZ b d)` |
| 3 | `mulQ_in_RatSet` | clausura |
| 4 | `mulQ_comm` | conmutatividad |
| 5 | `mulQ_assoc` | asociatividad |
| 6 | `mulQ_one_left` | `mulQ oneQ x = x` |
| 7 | `mulQ_one_right` | `mulQ x oneQ = x` |
| 8 | `mulQ_zero_left` | `mulQ zeroQ x = zeroQ` |
| 9 | `mulQ_zero_right` | `mulQ x zeroQ = zeroQ` |
| 10 | `mulQ_addQ_distrib_left` | `mulQ x (addQ y z) = addQ (mulQ x y) (mulQ x z)` |
| 11 | `mulQ_addQ_distrib_right` | `mulQ (addQ x y) z = addQ (mulQ x z) (mulQ y z)` |
| 12 | `mulQ_negQ_left` | `mulQ (negQ x) y = negQ (mulQ x y)` |
| 13 | `mulQ_negQ_right` | `mulQ x (negQ y) = negQ (mulQ x y)` |
| 14 | `mulQ_eq_zeroQ_iff` | `mulQ x y = zeroQ ↔ x = zeroQ ∨ y = zeroQ` (sin divisores de cero; se reduce a `mulZ_eq_zero_iff`) |

##### Inverso multiplicativo ([2.2] todo racional ≠ 0 es unidad)

**Estrategia**: `invQ (ratClass a b) := if a = zeroZ then zeroQ else ratClass b a`. El resultado es un elemento de `RatSet` porque si `a ≠ zeroZ` entonces `a ∈ NonZeroIntSet`. Bien definición: si `(a,b)~(c,d)` y `a ≠ zeroZ`, entonces `c ≠ zeroZ` (pues `a·d = b·c` y `a≠0`, `d≠0` implican `c≠0`), y `(b,a)~(d,c)` se verifica directamente.

**Definiciones**:

| # | Nombre | Descripción |
|---|--------|-------------|
| 4 | `invQ x` | `ratClass b a` si `x = ratClass a b` con `a ≠ zeroZ`; `zeroQ` si `x = zeroQ` (convención) |
| 5 | `divQ x y` | `mulQ x (invQ y)` — significativa cuando `y ≠ zeroQ` |

**Teoremas** ([2.2]):

| # | Nombre | Enunciado |
|---|--------|-----------|
| 15 | `invQ_well_defined` | Si `(a,b)~(c,d)` y `a ≠ zeroZ`, entonces `(b,a)~(d,c)`. *Prueba*: `a·d=b·c`, necesitamos `b·c = d·a`, lo cual es exactamente la hipótesis con los lados intercambiados. |
| 16 | `invQ_class` | `a ≠ zeroZ → invQ (ratClass a b) = ratClass b a` |
| 17 | `invQ_in_RatSet` | `x ∈ RatSet → invQ x ∈ RatSet` |
| 18 | `mulQ_invQ_right` | `x ∈ RatSet → x ≠ zeroQ → mulQ x (invQ x) = oneQ`. *Prueba*: `x = ratClass a b` con `a≠0`; `mulQ (ratClass a b) (ratClass b a) = ratClass (mulZ a b) (mulZ b a) = ratClass (mulZ a b) (mulZ a b) = oneQ`. |
| 19 | `mulQ_invQ_left` | `x ∈ RatSet → x ≠ zeroQ → mulQ (invQ x) x = oneQ` |
| 20 | `isUnitQ` | `∀ x ∈ RatSet, x ≠ zeroQ → ∃ y ∈ RatSet, mulQ x y = oneQ ∧ mulQ y x = oneQ` |
| 21 | `unitQ_iff` | `x ∈ RatSet → (∃ y, mulQ x y = oneQ) ↔ x ≠ zeroQ` — las unidades de ℚ son exactamente los no-cero |
| 22 | `invQ_invQ` | `x ≠ zeroQ → invQ (invQ x) = x` |
| 23 | `invQ_mulQ` | `x y ≠ zeroQ → invQ (mulQ x y) = mulQ (invQ x) (invQ y)` |
| 24 | `divQ_mulQ_cancel` | `y ≠ zeroQ → divQ (mulQ x y) y = x` |
| 25 | `mulQ_divQ_cancel` | `y ≠ zeroQ → mulQ y (divQ x y) = x` |

##### Exponenciación entera ([2.1] bien definida en clases)

**Definiciones**:

| # | Nombre | Descripción |
|---|--------|-------------|
| 6 | `powQ_nat x n` | `x^n` para `n ∈ ω`: `x^0 = oneQ`, `x^(σn) = mulQ x (x^n)`. Siempre definida. |
| 7 | `powQ_int x n` | `x^n` para `n ∈ IntSet`: si `n ≥ 0`, `powQ_nat x (absZ n)`; si `n < 0`, `invQ (powQ_nat x (absZ n))`. Requiere `x ≠ zeroQ` cuando `n < 0`. |

**Teoremas** (bien definición e identidades):

| # | Nombre | Enunciado |
|---|--------|-----------|
| 26 | `powQ_nat_in_RatSet` | `x ∈ RatSet → n ∈ ω → powQ_nat x n ∈ RatSet` |
| 27 | `powQ_nat_zero` | `powQ_nat x ∅ = oneQ` |
| 28 | `powQ_nat_succ` | `powQ_nat x (σ n) = mulQ x (powQ_nat x n)` |
| 29 | `powQ_nat_add_exp` | `powQ_nat x (add m n) = mulQ (powQ_nat x m) (powQ_nat x n)` |
| 30 | `powQ_nat_mul_exp` | `powQ_nat x (mul m n) = powQ_nat (powQ_nat x m) n` |
| 31 | `powQ_nat_well_defined` | Si `ratClass a b = ratClass c d` entonces `powQ_nat (ratClass a b) n = powQ_nat (ratClass c d) n` (bien definida en clases; sigue de `mulQ_well_defined` por inducción) |
| 32 | `powQ_int_in_RatSet` | `x ∈ RatSet → x ≠ zeroQ → n ∈ IntSet → powQ_int x n ∈ RatSet` |
| 33 | `powQ_int_nonneg` | `isNonnegZ n → powQ_int x n = powQ_nat x (absZ n)` |
| 34 | `powQ_int_neg` | `isNegativeZ n → x ≠ zeroQ → powQ_int x n = invQ (powQ_nat x (absZ n))` |
| 35 | `powQ_int_add_exp` | `x ≠ zeroQ → m n ∈ IntSet → powQ_int x (addZ m n) = mulQ (powQ_int x m) (powQ_int x n)` |

---

### [7] Valor absoluto en ℚ — `Rat/Abs.lean`

**Dependencias**: `Rat/Order.lean`, `Rat/Neg.lean`, `Int/Abs.lean`

**Definición**: `absQ x := if leQ zeroQ x then x else negQ x`

**Estrategia**: análoga a `absZ`. El signo es `signQ x := if x = zeroQ then zeroQ else if isPosQ x then oneQ else negQ oneQ`.

| # | Nombre | Enunciado |
|---|--------|-----------|
| 1 | `absQ_in_RatSet` | `x ∈ RatSet → absQ x ∈ RatSet` |
| 2 | `absQ_nonneg` | `x ∈ RatSet → leQ zeroQ (absQ x)` |
| 3 | `absQ_eq_zero_iff` | `x ∈ RatSet → (absQ x = zeroQ ↔ x = zeroQ)` |
| 4 | `absQ_negQ` | `x ∈ RatSet → absQ (negQ x) = absQ x` |
| 5 | `absQ_mulQ` | `x y ∈ RatSet → absQ (mulQ x y) = mulQ (absQ x) (absQ y)` |
| 6 | `absQ_triangle` | `x y ∈ RatSet → leQ (absQ (addQ x y)) (addQ (absQ x) (absQ y))` |
| 7 | `absQ_subQ_le` | `x y ∈ RatSet → leQ (absQ (subQ x y)) (addQ (absQ x) (absQ y))` |
| 8 | `absQ_pos` | `x ∈ RatSet → x ≠ zeroQ → ltQ zeroQ (absQ x)` |
| 9 | `signQ_in_RatSet` | `x ∈ RatSet → signQ x ∈ RatSet` |
| 10 | `signQ_mulQ_absQ` | `x ∈ RatSet → mulQ (signQ x) (absQ x) = x` |

---

### [10] Sucesiones en ℚ — `Rat/Sequences.lean`

**Dependencias**: `Rat/Abs.lean`, `Rat/Field.lean` (o al menos `Rat/Order.lean`), `Nat/Basic.lean`

**Motivación** (ADDENDUM 20:35/23-04-2026 de THOUGHTS.md): Antes de construir ℝ, construir sobre ℚ la teoría de sucesiones para motivar la completitud. La sucesión de Newton $f(n+1) = \frac{1}{2}(f(n) + \frac{2}{f(n)})$ con $f(0) = \frac{3}{2}$ es de Cauchy en ℚ, cumple $f(n)^2 \to 2$, pero no tiene límite en ℚ (ya que $\sqrt{2} \notin \mathbb{Q}$).

**Nota**: en THOUGHTS.md aparece $f(0) = \frac{2}{3}$ por errata tipográfica; el valor correcto es $f(0) = \frac{3}{2}$ (pues $f(0)^2 = \frac{9}{4} > 2$ como allí se indica).

#### Representación de sucesiones

Una sucesión de racionales se representa como función Lean `f : ℕ → U` con `hf : ∀ n, f n ∈ RatSet`. Esto evita el overhead de las funciones set-teóricas de `SetOps/Functions.lean` y es más adecuado para el uso analítico.

#### Definiciones

| # | Nombre | Tipo | Descripción |
|---|--------|------|-------------|
| 1 | `RatSeq` | `def` | `{f : ℕ → U // ∀ n, f n ∈ RatSet}` — tipo de sucesiones racionales |
| 2 | `convergesTo f L` | `Prop` | `L ∈ RatSet ∧ ∀ ε ∈ RatSet, ltQ zeroQ ε → ∃ N : ℕ, ∀ n ≥ N, ltQ (absQ (subQ (f n) L)) ε` |
| 3 | `isCauchy f` | `Prop` | `∀ ε ∈ RatSet, ltQ zeroQ ε → ∃ N : ℕ, ∀ m n ≥ N, ltQ (absQ (subQ (f m) (f n))) ε` |
| 4 | `convergesToZero f` | `Prop` | `convergesTo f zeroQ` (convergencia nula; a veces mal llamada "absoluta") |
| 5 | `newtonSqrt2` | `ℕ → U` | `newtonSqrt2 0 = ratClass oneZ (σ∅) ⋅ 3` (= 3/2); `newtonSqrt2 (n+1) = divQ (addQ (newtonSqrt2 n) (divQ twoQ (newtonSqrt2 n))) twoQ` |

#### Teoremas generales

| # | Nombre | Enunciado |
|---|--------|-----------|
| 1 | `convergesTo_unique` | Si `f → L` y `f → L'` entonces `L = L'` (unicidad del límite) |
| 2 | `convergent_is_cauchy` | `convergesTo f L → isCauchy f` |
| 3 | `cauchy_bounded` | Una sucesión de Cauchy está acotada: `isCauchy f → ∃ M ∈ RatSet, ∀ n, leQ (absQ (f n)) M` |
| 4 | `addSeq_converges` | Si `f → L` y `g → M` entonces `(n ↦ addQ (f n) (g n)) → addQ L M` |
| 5 | `mulSeq_converges` | Si `f → L` y `g → M` entonces `(n ↦ mulQ (f n) (g n)) → mulQ L M` |

#### Teoremas sobre la sucesión de Newton para √2

| # | Nombre | Enunciado |
|---|--------|-----------|
| 6 | `newtonSqrt2_mem_RatSet` | `∀ n, newtonSqrt2 n ∈ RatSet` |
| 7 | `newtonSqrt2_pos` | `∀ n, ltQ zeroQ (newtonSqrt2 n)` |
| 8 | `newtonSqrt2_sq_gt_two` | `∀ n, ltQ twoQ (mulQ (newtonSqrt2 n) (newtonSqrt2 n))` |
| 9 | `newtonSqrt2_decreasing` | `∀ n, ltQ (newtonSqrt2 (n+1)) (newtonSqrt2 n)` |
| 10 | `newtonSqrt2_sq_converges_to_two` | `convergesTo (fun n ↦ mulQ (newtonSqrt2 n) (newtonSqrt2 n)) twoQ` |
| 11 | `newtonSqrt2_is_cauchy` | `isCauchy newtonSqrt2` |
| 12 | `newtonSqrt2_no_limit_in_Q` | `¬ ∃ L ∈ RatSet, convergesTo newtonSqrt2 L` (usando `mulQ L L ≠ twoQ` para todo `L ∈ ℚ`, que requiere irracionalidad de √2 en ℚ) |

**Nota sobre irracionalidad**: `newtonSqrt2_no_limit_in_Q` requiere el lema `no_sqrt_two_in_Q : ¬ ∃ L ∈ RatSet, mulQ L L = twoQ`. Esto se prueba por el argumento clásico de paridad de numerador/denominador en forma irreducible. Puede ubicarse en `Rat/Field.lean` o en un lema auxiliar de `Rat/Sequences.lean`.

#### Sobre los cuerpos intermedios (pendiente lejano)

THOUGHTS.md propone construir cuerpos ordenados intermedios entre ℚ y ℝ:

- **Números computables**: sucesiones de Cauchy con testigo explícito de convergencia (función de módulo). Son un subanillo de ℝ, ordenado, arquimediano, pero no completo. Requiere noción de computabilidad (Church-Turing) — fuera del alcance actual.
- **Números constructibles** (cerrados bajo raíces cuadradas): campo de extensión de ℚ de grado potencia de 2. Requiere teoría de extensiones de cuerpos.
- **Números algebraicos** (raíces de polinomios sobre ℤ): requiere álgebra de polinomios (`Nat/Poly.lean` o similar) y el teorema de la raíz racional.

Estos tres cuerpos se documentan como objetivo **futuro** (Phase 6.5), posterior a `Rat/Sequences.lean` y a la construcción de ℝ.

---

### [1] Orden total lineal en ℚ — `Rat/Order.lean`

**Dependencias**: `Rat/Neg.lean`, `Rat/Add.lean`, `Int/Order.lean`

**Estrategia de definición**: Definir primero la positividad sobre representantes y probar que es independiente de la elección. Sea `isPosQ [(a,b)] :⟺ isPositiveZ (mulZ a b)` — es decir, el numerador y el denominador tienen el mismo signo (a/b > 0). Luego `leQ x y :⟺ isNonnegQ (subQ y x)`.

**Clave de bien definición**: Si `(a,b)~(c,d)` [i.e., `mulZ a d = mulZ b c`] y `isPositiveZ (mulZ a b)`, entonces `isPositiveZ (mulZ c d)`. *Prueba*: `(mulZ c d) · (mulZ a b) = (mulZ a c) · (mulZ b d)`. Por otro lado, `mulZ a b > 0` implica `a ≠ 0`, y de `a·d = b·c` con `d ≠ 0` se obtiene `c ≠ 0`, luego la igualdad cero es imposible. Y `(mulZ c d) · (mulZ a b) = (mulZ (mulZ a d) (mulZ b c)) / ...` — más precisamente, basta usar que `(c·d)·(a·b) = (a·d)·(b·c) = (b·c)²` ≥ 0 con igualdad solo si `b·c = 0`, imposible. Luego `c·d > 0`.

#### [1.1] Bien definición del orden respecto a las clases de equivalencia

**Definiciones**:

| # | Nombre | Tipo | Descripción |
|---|--------|------|-------------|
| 1 | `isPosQ x` | `Prop` | `∃ a b, x = ratClass a b ∧ isPositiveZ (mulZ a b)` |
| 2 | `isNonnegQ x` | `Prop` | `x = zeroQ ∨ isPosQ x` |
| 3 | `isNegQ x` | `Prop` | `isPosQ (negQ x)` |
| 4 | `isNonposQ x` | `Prop` | `x = zeroQ ∨ isNegQ x` |
| 5 | `leQ x y` | `Prop` | `isNonnegQ (subQ y x)` |
| 6 | `ltQ x y` | `Prop` | `leQ x y ∧ x ≠ y` |
| 7 | `leQ_rel` | `U` | Grafo set-teórico de `leQ` en `RatSet ×ₛ RatSet` (para `isRelationOn`) |

**Teoremas de bien definición**:

| # | Nombre | Enunciado |
|---|--------|-----------|
| 1 | `isPosQ_well_defined` | `ratClass a b = ratClass c d → isPositiveZ (mulZ a b) → isPositiveZ (mulZ c d)` |
| 2 | `isNonnegQ_well_defined` | `isNonnegQ` no depende del representante (sigue de `isPosQ_well_defined`) |
| 3 | `leQ_well_defined` | `leQ x y` no depende del representante elegido para `x` ni para `y` (sigue de `subQ` bien definida + `isNonnegQ_well_defined`) |

**Propiedades del orden (lineal total)**:

| # | Nombre | Enunciado |
|---|--------|-----------|
| 4 | `leQ_refl` | `x ∈ RatSet → leQ x x`. *Prueba*: `subQ x x = zeroQ`, que es `isNonnegQ`. |
| 5 | `leQ_antisymm` | `leQ x y → leQ y x → x = y`. *Prueba*: `isNonnegQ (y-x)` y `isNonnegQ (x-y)` con `y-x = negQ(x-y)`; ambos no-negativos implica ambos cero, i.e., `x = y`. |
| 6 | `leQ_trans` | `leQ x y → leQ y z → leQ x z`. *Prueba*: `z-x = (z-y)+(y-x)`, suma de no-negativos es no-negativo. |
| 7 | `leQ_total` | `x y ∈ RatSet → leQ x y ∨ leQ y x`. *Prueba*: tricotomía en ℤ sobre `mulZ (snd x_rep) (fst y_rep)` vs `mulZ (fst x_rep) (snd y_rep)`. |
| 8 | `leQ_is_linear_order` | `isLinearOrderOn leQ_rel RatSet` — agrupa reflexividad, antisimetría, transitividad, totalidad |
| 9 | `ltQ_is_strict_linear_order` | `isStrictLinearOrderOn ltQ_rel RatSet` |
| 10 | `trichotomyQ` | `x ∈ RatSet → isPosQ x ∨ x = zeroQ ∨ isNegQ x`, mutuamente exclusivos |

**Compatibilidad orden-operaciones**:

| # | Nombre | Enunciado |
|---|--------|-----------|
| 11 | `leQ_addQ_compat_right` | `leQ x y → leQ (addQ x z) (addQ y z)` |
| 12 | `leQ_addQ_compat_left` | `leQ x y → leQ (addQ z x) (addQ z y)` |
| 13 | `leQ_mulQ_nonneg` | `leQ x y → isNonnegQ z → leQ (mulQ x z) (mulQ y z)` |
| 14 | `leQ_mulQ_nonpos` | `leQ x y → isNonposQ z → leQ (mulQ y z) (mulQ x z)` — multipliar por no-positivo invierte |
| 15 | `isPosQ_mulQ_closed` | `isPosQ x → isPosQ y → isPosQ (mulQ x y)` |
| 16 | `isNegQ_mulQ_isPosQ` | `isNegQ x → isNegQ y → isPosQ (mulQ x y)` |
| 17 | `ltQ_irrefl` | `¬ ltQ x x` |
| 18 | `ltQ_trans` | `ltQ x y → ltQ y z → ltQ x z` |
| 19 | `invQ_pos` | `isPosQ x → isPosQ (invQ x)` — el inverso de un positivo es positivo |

#### [6] Densidad de ℚ (en `Rat/Order.lean`)

| # | Nombre | Enunciado |
|---|--------|-----------|
| 20 | `rationals_dense` | `x y ∈ RatSet → ltQ x y → ∃ z ∈ RatSet, ltQ x z ∧ ltQ z y`. *Prueba*: tomar `z = divQ (addQ x y) (intToRat (natToInt (σ (σ ∅))))` = (x+y)/2. Verificar `x < z` iff `x < (x+y)/2` iff `2x < x+y` iff `x < y`. ✓ |
| 21 | `no_min_pos_rational` | `¬ ∃ x ∈ RatSet, isPosQ x ∧ ∀ y ∈ RatSet, isPosQ y → leQ x y`. *Prueba*: si `x` fuera mínimo positivo, `x/2` sería positivo y estrictamente menor. |
| 22 | `infinite_rationals_between` | `x y ∈ RatSet → ltQ x y → ∀ n ∈ ω, ∃ z₁ ... zₙ ∈ RatSet, todos distintos entre sí y con ltQ x zᵢ y ltQ zᵢ y` — corolario de densidad |

---

### [2]+[4]+[5] Embedding ℤ ↪ ℚ — `Rat/Embedding.lean`

**Dependencias**: `Rat/Mul.lean`, `Rat/Order.lean`, `Int/Order.lean`, `Int/Embedding.lean`

**Definición**:

| # | Nombre | Descripción |
|---|--------|-------------|
| 1 | `intToRat_graph` | Grafo set-teórico `{⟨n, ratClass n oneZ⟩ | n ∈ IntSet}` |
| 2 | `intToRat n` | `ratClass n oneZ` — envía `n ∈ ℤ` a la fracción `n/1` |

#### [4] El embedding respeta la estructura de anillo

| # | Nombre | Enunciado |
|---|--------|-----------|
| 1 | `intToRat_mem_RatSet` | `n ∈ IntSet → intToRat n ∈ RatSet` |
| 2 | `intToRat_injective` | `m n ∈ IntSet → intToRat m = intToRat n → m = n` |
| 3 | `intToRat_zeroZ` | `intToRat zeroZ = zeroQ` |
| 4 | `intToRat_oneZ` | `intToRat oneZ = oneQ` |
| 5 | `intToRat_preserves_add` | `intToRat (addZ m n) = addQ (intToRat m) (intToRat n)` |
| 6 | `intToRat_preserves_neg` | `intToRat (negZ n) = negQ (intToRat n)` |
| 7 | `intToRat_preserves_sub` | `intToRat (subZ m n) = subQ (intToRat m) (intToRat n)` |
| 8 | `intToRat_preserves_mul` | `intToRat (mulZ m n) = mulQ (intToRat m) (intToRat n)` |
| 9 | `intToRat_is_ring_hom` | Sentencia compacta: `intToRat` es homomorfismo de anillos `(ℤ, +, ×, 0, 1) → (ℚ, +, ×, 0, 1)` |
| 10 | `intToRat_not_surjective` | `¬ ∀ x ∈ RatSet, ∃ n ∈ IntSet, intToRat n = x` (e.g., `ratClass oneZ (σ (σ ∅))` = 1/2 ∉ imagen) |

#### [2] El embedding preserva el orden de ℤ en ℚ

| # | Nombre | Enunciado |
|---|--------|-----------|
| 11 | `intToRat_preserves_leZ` | `m n ∈ IntSet → leZ m n → leQ (intToRat m) (intToRat n)` |
| 12 | `intToRat_reflects_leZ` | `m n ∈ IntSet → leQ (intToRat m) (intToRat n) → leZ m n` |
| 13 | `intToRat_preserves_ltZ` | `m n ∈ IntSet → ltZ m n → ltQ (intToRat m) (intToRat n)` |
| 14 | `intToRat_reflects_ltZ` | `m n ∈ IntSet → ltQ (intToRat m) (intToRat n) → ltZ m n` |
| 15 | `intToRat_is_order_embedding` | Sentencia compacta: `intToRat` es un embedding de órdenes estricto `ℤ → ℚ` |

#### [5] Propiedad Arquimediana en ℚ (trasladada desde ℤ vía el embedding)

**Pre-requisito**: propiedad Arquimediana en ℤ. Si no existe ya en `Int/Order.lean` o `Int/Induction.lean`, añadir allí:

- `archZ`: `m n ∈ IntSet → isPositiveZ n → ∃ k ∈ ω, leZ m (mulZ (natToInt k) n)`

**Teoremas**:

| # | Nombre | Enunciado |
|---|--------|-----------|
| 16 | `archQ` | `x y ∈ RatSet → isPosQ y → ∃ k ∈ ω, leQ x (mulQ (intToRat (natToInt k)) y)`. *Prueba*: sea `x = ratClass a b` y `y = ratClass c d` con `c·d > 0` y `b ∈ ℤ*`. Necesitamos `k` tal que `k·c/d ≥ a/b`, i.e., `k·b·c ≥ a·d` en ℤ (ajustando signos para que `b,d > 0`). Por `archZ` existe tal `k`. |
| 17 | `archQ_omega` | `x ∈ RatSet → ∃ n ∈ ω, leQ x (intToRat (natToInt n))` — todo racional está acotado superiormente por un natural (caso especial de `archQ` con `y = oneQ`) |
| 18 | `no_infinitesimals_Q` | `¬ ∃ x ∈ RatSet, isPosQ x ∧ ∀ n ∈ ω, n ≠ ∅ → leQ x (invQ (intToRat (natToInt n)))`. Es decir, no hay elementos positivos menores que `1/n` para todo `n ≥ 1`. *Prueba*: si existiera tal `x`, por `archQ` ∃ `k` con `k·x > 1`, luego `x > 1/k`, contradicción. |

---

### [3] Estructura de cuerpo en ℚ — `Rat/Field.lean`

**Dependencias**: `Rat/Mul.lean` (donde ya están `invQ`, `divQ`), `Rat/Order.lean`

Este módulo formaliza que `(ℚ, +, ×, −, ⁻¹, 0, 1)` es un **cuerpo ordenado** y agrupa los teoremas ya probados en teoremas compactos de estructura.

| # | Nombre | Enunciado |
|---|--------|-----------|
| 1 | `RatSet_is_add_comm_group` | `(RatSet, addQ, zeroQ, negQ)` es grupo abeliano: asociatividad, conmutatividad, identidad, inverso |
| 2 | `RatSet_is_comm_monoid_mul` | `(RatSet, mulQ, oneQ)` es monoide conmutativo: asociatividad, conmutatividad, identidad |
| 3 | `RatSet_is_comm_ring` | `(RatSet, addQ, mulQ, zeroQ, oneQ, negQ)` es anillo conmutativo: agrupa 1, 2, distributividad, `zeroQ_ne_oneQ` |
| 4 | `RatSet_is_integral_domain` | `mulQ x y = zeroQ → x = zeroQ ∨ y = zeroQ` — ℚ es dominio de integridad (ya en `mulQ_eq_zeroQ_iff`) |
| 5 | `RatSet_is_field` | `(RatSet, addQ, mulQ, zeroQ, oneQ, negQ, invQ)` es cuerpo conmutativo: además de anillo, todo no-cero tiene inverso. Agrupa `RatSet_is_comm_ring` + `mulQ_invQ_right` + `zeroQ_ne_oneQ`. |
| 6 | `RatSet_is_ordered_field` | `(ℚ, +, ×, ≤)` es cuerpo ordenado: agrupa `RatSet_is_field` + `leQ_is_linear_order` + `leQ_addQ_compat_right` + `leQ_mulQ_nonneg` |
| 7 | `divQ_class` | `b c ∈ NonZeroIntSet → divQ (ratClass a b) (ratClass c d) = ratClass (mulZ a d) (mulZ b c)` — regla de cómputo |
| 8 | `divQ_ne_zeroQ` | `x y ∈ RatSet → x ≠ zeroQ → y ≠ zeroQ → divQ x y ≠ zeroQ` |
| 9 | `divQ_self` | `x ≠ zeroQ → divQ x x = oneQ` |
| 10 | `divQ_addQ` | `z ≠ zeroQ → divQ (addQ x y) z = addQ (divQ x z) (divQ y z)` |

---

### [7] Biyección ℚ ≈ ω — `Rat/Embedding.lean`

**Estrategia**: Cantor-Bernstein (`CSB` de `Cardinal.Basic`) con:

1. Inyección `ω → ℚ`: composición `natToInt ; intToRat` (ambas inyectivas).
2. Inyección `ℚ → ω`: vía `RatBase ≈ ω` (por Cantor pairing en ℤ×ℤ*) y elección de representante canónico por `Classical.choice`.

| # | Nombre | Enunciado |
|---|--------|-----------|
| 1 | `NonZeroIntSet_equipotent_omega` | `isEquipotent NonZeroIntSet ω`. *Prueba*: `ℤ* ⊂ ℤ ≈ ω` e `ℤ* ≈ ℤ` (biyección zigzag restringida a ≠ 0). |
| 2 | `RatBase_equipotent_omega` | `isEquipotent RatBase ω`. *Prueba*: `RatBase = IntSet ×ₛ NonZeroIntSet ≈ ω × ω ≈ ω` vía Cantor pairing (disponible en `Cardinal.Basic` o `Nat.Arith`). |
| 3 | `omega_injection_to_RatSet` | `∃ f, isInjection f ω RatSet`. *Prueba*: `natToInt ; intToRat` es inyectiva (composición de inyecciones). |
| 4 | `RatSet_surjection_from_RatBase` | `∀ x ∈ RatSet, ∃ p ∈ RatBase, x = ratClass (fst p) (snd p)`. *Prueba*: por definición de `QuotientSet` y `EqClass_representative_exists`. |
| 5 | `RatSet_injection_to_omega` | `∃ f, isInjection f RatSet ω`. *Prueba*: por `Classical.choice` cada clase de equivalencia en `RatSet` tiene un representante en `RatBase`; la función `x ↦ biyección(representante(x))` es inyectiva (si dos clases tienen el mismo representante, son iguales). |
| 6 | `RatSet_equipotent_omega` | `isEquipotent RatSet ω`. *Prueba*: `CSB` con las inyecciones de los teoremas 3 y 5. **Conclusión**: ℚ es numerable. |

---

## Phase 7: Reales ℝ — 📋 Planificado

**Pre-requisito**: Phase 6 completa (ℚ funcional)

| Módulo | Contenido principal |
|--------|---------------------|
| `Real/CauchyEquiv.lean` | Equivalencia de sucesiones de Cauchy en ℚ (todo en ℚ, sin circularidad) |
| `Real/Basic.lean` | RealSet := QuotientSet CauchySeqSet CauchyEquivRel, zeroR, oneR |
| `Real/Arith.lean` | Suma, producto, negación componente a componente, buena definición via QuotientLift₂ |
| `Real/Field.lean` | Inverso multiplicativo (sucesiones eventualmente ≠ 0), ℝ es cuerpo |
| `Real/Order.lean` | leR formulado en ℚ, tricotomía, ℝ es cuerpo ordenado |
| `Real/Completeness.lean` | Propiedad del supremo, Bolzano-Weierstrass, completitud de Cauchy |
| `Real/Embedding.lean` | ratToReal: ℚ→ℝ, densidad de ℚ en ℝ, `|ℝ| = |𝒫(ω)|` |
| `Real/Sequences.lean` | Convergencia, Cauchy en ℝ, monotónas acotadas |
| `Real/Topology.lean` | Abiertos, cerrados, compactos, Heine-Borel |
| `Real/Continuity.lean` | Funciones continuas, Bolzano (TVI), Weierstrass |
| `Real/Differentiability.lean` | Derivada, reglas cadena/producto/cociente |
| `Real/Integration.lean` | Integral de Riemann (particiones, sumas sup/inf) |
| `Real/FTC.lean` | Teorema Fundamental del Cálculo |
| `Real/Series.lean` | Series, convergencia absoluta/condicional |
| `Real/SpecialFunctions.lean` | exp, log, sin, cos (via series de potencias) |

**Nota**: `x^r` para `r ∈ ℝ` requiere exp/log, que vienen después de Series.lean y Integration.lean.

---

## Futuro lejano

- **Álgebra abstracta**: grupos, anillos, cuerpos abstractos, módulos
- **Ordinales/Cardinales**: aritmética transfinita más allá de ω
- **Gödel**: incompletitud de Gödel (Rosser), numeración de Gödel, funciones recursivas representables en ZFC
- **Interfaces**: Aczel CZF, MK, compatibilidad con Mathlib

---

## Resumen de estado

| Phase | Estado | Módulos | Exports |
|-------|--------|---------|---------|
| 1–3: Estructura y SetOps | ✅ Completo | ~40 | — |
| 4: Anotaciones | ✅ Completo | — | — |
| 5: Enteros ℤ | ✅ Completo | 15 | 190 |
| 6: Racionales ℚ | 🔄 En progreso | 6/12 | 78 |
| 6.5: Cuerpos intermedios | 🔮 Futuro | 0/3 | — |
| 7: Reales ℝ | 📋 Planificado | 0/15 | — |
| Futuro | 🔮 Lejano | — | — |

---

*Última actualización: 2026-04-23. Phase 5 (ℤ) 100% completa. Phase 6 (ℚ): 6 módulos completados (Equiv, Basic, Add, Neg, Mul, Order — 78 exports, 0 sorry). Siguiente: Rat/Abs.lean. Nuevo: Rat/Sequences.lean planificado con sucesiones de Cauchy y sucesión de Newton para √2.*
