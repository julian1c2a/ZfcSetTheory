# Next Steps — ZfcSetTheory Project

**Last updated**: 2026-04-26

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
- ✅ **Racionales ℚ** (Phase 6, 9 módulos): `Equiv`, `Basic`, `Add`, `Neg`, `Mul`, `Order`, `Abs`, `Embedding`, `Field` — 0 sorry, 0 errores
- 🔄 **Sucesiones en ℚ** (Phase 6.5, 6 módulos compilan): `Int/MaxMin`, `Rat/MaxMin`, `Rat/Sequences`, `Rat/Convergence`, `Rat/CauchyQ`, `Rat/Monotone` — `cauchy_bounded`, `nondecreasing_bounded_isCauchy`, `nonincreasing_bounded_isCauchy`, `convergent_isBounded` demostrados sin sorry; ~2 sorry legítimos restantes (aritmética avanzada de límites en `Convergence.lean`)

**Estado**: 87 módulos, ~2 sorry legítimos (aritmética avanzada de límites en `Rat/Convergence.lean`), 0 errores de compilación.

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

## Phase 6: Racionales ℚ — ✅ COMPLETA (2026-04-26)

9 módulos · 0 sorry · 0 errores

| # | Módulo | Exports | Contenido principal |
|---|--------|---------|---------------------|
| 1 | `Rat/Equiv.lean` | 16 | NonZeroIntSet, RatBase, RatEquivRel, RatSet, relación de equivalencia |
| 2 | `Rat/Basic.lean` | 13 | ratClass, zeroQ, oneQ, ratClass_eq_iff, zeroQ_ne_oneQ |
| 3 | `Rat/Add.lean` | 7 | addQ bien definida, grupo abeliano (ℚ, +), addQ_comm/assoc/zero |
| 4 | `Rat/Neg.lean` | 7 | negQ, subQ, inverso aditivo, negQ_negQ, negQ_addQ_right |
| 5 | `Rat/Mul.lean` | 18 | mulQ, invQ, divQ; anillo conmutativo; invQ todo ≠ 0 es unidad; mulQ_comm/assoc/one |
| 6 | `Rat/Order.lean` | 17 | leQ, ltQ, isPositiveQ, isNegativeQ; orden total; compat +/×; densidad de ℚ |
| 7 | `Rat/Abs.lean` | 13 | subQ, absQ, signQ; desigualdad triangular; absQ_mulQ; signQ_mulQ_absQ; archZ |
| 8 | `Rat/Embedding.lean` | 15 | intToRat (n↦n/1); hom de anillos ordenados ℤ→ℚ; inyectividad; no suryectividad; archQ |
| 9 | `Rat/Field.lean` | 14 | mulQ_eq_zero_iff; cancelación; invQ_invQ; invQ_mulQ; divQ_self/one/cancel; distribQ |

---

## Phase 6.5: Sucesiones en ℚ — � En progreso

**Pre-requisito**: Phase 6 completa (ℚ cuerpo ordenado arquimediano)  
**Directorio**: `ZFC/Rat/` y `ZFC/Int/`

| # | Módulo | Exports clave | Estado |
|---|--------|---------------|--------|
| 0a | `Int/MaxMin.lean` | `maxZ`, `minZ`, 18 teoremas | ✅ 0 sorry |
| 0b | `Rat/MaxMin.lean` | `maxQ`, `minQ`, 18 teoremas | ✅ 0 sorry |
| 1 | `Rat/Sequences.lean` | `IsSeqQ`, `constSeqQ`, `addSeqQ`, `negSeqQ`, `mulSeqQ` | ✅ 0 sorry |
| 2 | `Rat/Convergence.lean` | `convergesToQ`, `limit_unique`, `convergesToQ_add`, `convergesToQ_mul_bounded`, `subseq_convergent`, `IsSubseqOf` | 🔄 2 sorry (aritmética avanzada de límites) |
| 3 | `Rat/CauchyQ.lean` | `IsCauchyQ`, `cauchy_of_convergentQ`, `cauchy_bounded`, `constSeqQ_isCauchy` | ✅ 0 sorry |
| 4 | `Rat/Monotone.lean` | `isNondecreasingQ`, `isBoundedQ`, `limit_le_of_bounded_above`, `convergent_isBounded`, `nondecreasing_bounded_isCauchy`, `nonincreasing_bounded_isCauchy` | ✅ 0 sorry |
| 5 | `Rat/SqrtApprox.lean` | `sqrtApprox`, `sqrtApprox_is_cauchy`, `sqrt2_irrational`, `sqrtApprox_not_convergent` | ❌ No iniciado |

**Teoremas clave de `Rat/Convergence.lean`** (plan detallado):

### Casos base

1. `convergesToQ_const` — la sucesión constante converge a su valor (**✅ probado**)
2. `limit_unique f L₁ L₂` — si f→L₁ y f→L₂ entonces L₁=L₂. (**✅ probado**)
   *Estrategia*: por contradicción; si L₁≠L₂ tomar ε=|L₁−L₂|/2 > 0;
   para n suficientemente grande `|L₁−L₂| ≤ |f(n)−L₁| + |f(n)−L₂| < ε+ε = |L₁−L₂|`;
   contradicción. Requiere `halfQ` (lema: ε>0 → ε/2 > 0) + `absQ_triangle`.

### Aritmética de límites

1. `convergesToQ_neg f L` — si f→L entonces (−f)→−L.
   *Estrategia*: `|(−f)(n)−(−L)| = |f(n)−L|`; usar el mismo N de f.
2. `convergesToQ_add f g L₁ L₂` — si f→L₁ y g→L₂ entonces (f+g)→L₁+L₂. (**✅ probado**)
   *Estrategia*: dado ε>0, tomar N₁ (para ε/2 sobre f) y N₂ (para ε/2 sobre g);
   para n≥max(N₁,N₂): `|(f+g)(n)−(L₁+L₂)| ≤ |f(n)−L₁| + |g(n)−L₂| < ε/2+ε/2 = ε`.
   Requiere `halfQ`, `maxOf`, `absQ_triangle`, `addQ_ltQ_ltQ`.
3. `convergesToQ_sub f g L₁ L₂` — si f→L₁ y g→L₂ entonces (f−g)→L₁−L₂.
   *Estrategia*: corolario de `convergesToQ_add` + `convergesToQ_neg`.
4. `convergesToQ_const_mul c f L` — si f→L entonces (c·f)→c·L (c ∈ ℚ fija).
   *Estrategia*: si c=0 trivial; si c≠0, dado ε>0 usar ε/|c| como umbral para f.
   Requiere `isPositiveQ_invQ` y `mulQ_absQ`.
5. `convergesToQ_mul_bounded f g L` — si f→0 y g es acotada entonces (f·g)→0. (**✅ probado**)
6. `convergesToQ_mul f g L₁ L₂` — si f→L₁ y g→L₂ entonces (f·g)→L₁·L₂.
   *Estrategia*: `f·g − L₁·L₂ = (f−L₁)·g + L₁·(g−L₂)`;
   usar `convergesToQ_mul_bounded` (para (f−L₁)·g, g acotada por `cauchy_bounded`)
   - `convergesToQ_const_mul` (para L₁·(g−L₂)).
   Requiere `cauchy_bounded` de `CauchyQ.lean`.
7. `convergesToQ_inv f L` — si f→L y L≠0 entonces (1/f)→1/L.
   *Estrategia*: mostrar que f(n)≠0 eventualmente; luego `1/f(n)−1/L = (L−f(n))/(L·f(n))`;
   acotar |L·f(n)| desde abajo por |L|/2 para n≥N.
   Requiere `archQ` para el control de denominadores.
8. `convergesToQ_div f g L₁ L₂` — si f→L₁, g→L₂, L₂≠0 entonces (f/g)→L₁/L₂.
    *Estrategia*: corolario de `convergesToQ_mul` + `convergesToQ_inv`.
9. `convergesToQ_abs f L` — si f→L entonces |f|→|L|.
    *Estrategia*: `||f(n)|−|L|| ≤ |f(n)−L|` (desigualdad triangular inversa).

### Reformulaciones equivalentes

1. `convergesToQ_zero_of_abs f` — |f|→0 ↔ f→0.
    *Estrategia*: `||f(n)|−0| = |f(n)| = |f(n)−0|`.
2. `convergesToQ_iff_abs f L` — f→L ↔ (n↦|f(n)−L|)→0.
    *Estrategia*: reformulación directa de la definición ε-N.

### Colas y equivalencias eventuales

1. `convergesToQ_tail f L k` — f→L ↔ (n↦f(n+k))→L para cualquier k∈ω.
    *Estrategia*: el mismo N funciona; para ≥k usar N' = maxOf N k.
2. `convergesToQ_of_eventually_eq f g L` — f(n)=g(n) para n≥N y f→L ⟹ g→L.
    *Estrategia*: el mismo ε-N de f funciona para g a partir del máximo de los dos N.

### Teorema del emparedado (squeeze)

1. `squeeze_theorem a f b L` — a(n)≤f(n)≤b(n), a→L, b→L ⟹ f→L.
    *Estrategia*: dado ε>0, tomar N tal que |a(n)−L|<ε y |b(n)−L|<ε para n≥N;
    entonces L−ε < a(n) ≤ f(n) ≤ b(n) < L+ε.
2. `convergesToQ_of_dominated f g L` — |f(n)−L|≤g(n) y g→0 ⟹ f→L.
    *Estrategia*: versión alternativa del squeeze con g como dominadora.

### Subsucesiones

1. `IsSubseqOf g f` — predicado: ∃ φ: ω→ω estrictamente creciente tal que g(n)=f(φ(n)) ∀n∈ω.
2. `strictly_increasing_ge φ n` — φ: ω→ω estrictamente creciente ⟹ φ(n)≥n (inducción).
3. `subseq_convergent f g L` — si f→L y g es subsucesión de f, entonces g→L.
    *Estrategia*: dado ε>0, tomar N de la convergencia de f; para n≥N, como φ es
    estrictamente creciente, φ(n)≥n≥N, así |g(n)−L|=|f(φ(n))−L|<ε.

### Acotamiento y monotonía (en `Rat/Monotone.lean`)

1. `nondecreasing_bounded_isCauchy` — gₙ no-decreciente + acotada superiormente ⟹ Cauchy. (**✅ probado** — demostración directa por propiedad arquimediana en ℚ; inducción + `archQ`; no requiere Real.Completeness)
2. `nonincreasing_bounded_isCauchy` — gₙ no-creciente + acotada inferiormente ⟹ Cauchy. (**✅ probado** — dual de `nondecreasing_bounded_isCauchy`; argumento arquimediano simétrico)
3. `limit_le_of_bounded_above f L M` — f→L, ∀n f(n)≤M ⟹ L≤M. (**✅ probado**)
4. `le_limit_of_bounded_below f L M` — f→L, ∀n M≤f(n) ⟹ M≤L. (**✅ probado**)
5. `convergent_isBounded f L` — f→L ⟹ f está acotada (superior e inferiormente). (**✅ probado** vía `cauchy_bounded f hf (cauchy_of_convergentQ f L hf hL hconv)`)

**Teoremas clave de `Rat/CauchyQ.lean`** (plan detallado):

### Casos base

1. `constSeqQ_isCauchy a` — la sucesión constante es de Cauchy (**✅ probado vía `cauchy_of_convergentQ`**)
2. `cauchy_of_convergentQ f L` — si f→L entonces f es de Cauchy. (**✅ probado**)
   *Estrategia*: dado ε>0, tomar N tal que ∀n≥N, |f(n)−L|<ε/2;
   para m,n≥N: `|f(m)−f(n)| ≤ |f(m)−L| + |L−f(n)| < ε/2+ε/2 = ε`.
   Requiere `halfQ`, `absQ_triangle_sub` (`|a−c|≤|a−b|+|b−c|`).
3. `cauchy_bounded f` — toda sucesión de Cauchy en ℚ está acotada. (**✅ probado** vía inducción con `maxQ` sobre segmento inicial [0,N₀])
   *Estrategia implementada*: ε=1; N₀ de Cauchy; Q(n) = ∃M, ∀k≤n, |f(k)|≤M; inducción en ω da Q(N₀); M = addQ M₀ oneQ; tricotomía n vs N₀.

### Aritmética de Cauchy

1. `cauchyQ_neg f` — f Cauchy ⟹ (−f) Cauchy.
   *Estrategia*: `|(−f)(m)−(−f)(n)| = |f(m)−f(n)|`; mismo N.
2. `cauchyQ_add f g` — f,g Cauchy ⟹ (f+g) Cauchy.
   *Estrategia*: dado ε>0, tomar Nf (para ε/2 sobre f) y Ng (para ε/2 sobre g);
   para m,n≥max(Nf,Ng): `|(f+g)(m)−(f+g)(n)| ≤ |f(m)−f(n)| + |g(m)−g(n)| < ε`.
3. `cauchyQ_sub f g` — f,g Cauchy ⟹ (f−g) Cauchy.
   *Estrategia*: corolario de `cauchyQ_add` + `cauchyQ_neg`.
4. `cauchyQ_const_mul c f` — c∈ℚ, f Cauchy ⟹ (c·f) Cauchy.
   *Estrategia*: si c=0 trivial; si c≠0, usar umbral ε/|c| para f.
5. `cauchyQ_mul f g` — f,g Cauchy ⟹ (f·g) Cauchy.
   *Estrategia*: `f(m)g(m)−f(n)g(n) = (f(m)−f(n))g(m) + f(n)(g(m)−g(n))`;
   acotar con `cauchy_bounded` para f y g. Requiere `cauchy_bounded`.

### Subsucesiones y Cauchy

1. `subseq_of_cauchyQ f g` — g subsucesión de f Cauchy ⟹ g Cauchy.
   *Estrategia*: el mismo N de f funciona porque φ es creciente.
2. `cauchyQ_of_convergent_subseq f g L` — f Cauchy + g subsucesión de f con g→L ⟹ f→L.
    *Estrategia*: dado ε>0, tomar Nf (Cauchy de f, umbral ε/2) y Ng (convergencia de g, umbral ε/2);
    para n≥max(Nf,Ng): |f(n)−L| ≤ |f(n)−f(φ(n))| + |f(φ(n))−L| < ε/2+ε/2.
    **Teorema clave para la completitud de ℝ.**

**Teoremas clave de `Rat/SqrtApprox.lean`** (prueba completa de incompletitud de ℚ):

1. `sqrtApprox_in_RatSet` — f(n) ∈ ℚ para todo n (inducción sobre la recurrencia)
2. `sqrtApprox_positive` — f(n) > 0 para todo n
3. `sqrtApprox_sq_gt_2` — f(n)² > 2 para todo n (identidad: f(n+1)²−2 = (f(n)²−2)²/(4f(n)²))
4. `sqrtApprox_decreasing` — f(n+1) < f(n) para todo n (monótona decreciente)
5. `sqrtApprox_is_cauchy` — IsCauchyQ sqrtApprox (convergencia cuadrática de Newton-Raphson)
6. `sqrt2_irrational` — ¬∃ p q : ℤ, q≠0 ∧ p·p = 2·(q·q) (irracionalidad de √2, argumento 2-ádico)
7. `sqrtApprox_not_convergent` — ¬∃ L∈ℚ, convergesToQ sqrtApprox L (**incompletitud de ℚ**)

---

## Phase 7: Cuerpos Ordenados Intermedios entre ℚ y ℝ — 📋 Planificado

**Pre-requisito**: Phase 6.5 completa (sucesiones de Cauchy en ℚ definidas y con ejemplos)  
**Motivación**: Entre ℚ y ℝ existen cuerpos ordenados que contienen ℚ pero no son completos. Su formalización ilustra el rol esencial de la propiedad del supremo en la construcción de ℝ.

### Phase 7a: Números Computables — `ZFC/Computable/`

| Módulo | Contenido principal |
|--------|---------------------|
| `Computable/Basic.lean` | `ComputSet`: pares (f, N) con f: ω→ℚ Cauchy y módulo uniforme 1/2^N; relación de equivalencia de Cauchy |
| `Computable/Arith.lean` | Suma, producto, negativo, inverso; (Computables, +, ·) es cuerpo ordenado |
| `Computable/Embedding.lean` | ℚ ↪ Computables (sucesiones constantes); inyectividad, preserva orden |
| `Computable/NotComplete.lean` | `sqrtApprox` es computable pero no tiene límite computable: incompletitud de Computables |

### Phase 7b: Números Constructibles — `ZFC/Constructible/`

| Módulo | Contenido principal |
|--------|---------------------|
| `Constructible/Basic.lean` | `ConstructSet`: cierre mínimo de ℚ bajo +, −, ·, ÷ y √(x) para x>0; cada elemento es algebraico de grado potencia de 2 |
| `Constructible/NotComplete.lean` | No completo: sucesión de Cauchy en ConstructSet sin límite constructible (ej. ∑ 1/n! ∉ ConstructSet) |

### Phase 7c: Números Radicales — `ZFC/Radical/`

| Módulo | Contenido principal |
|--------|---------------------|
| `Radical/Basic.lean` | `RadicalSet`: cierre de ℚ bajo +, −, ·, ÷ y raíces n-ésimas para cualquier n∈ℕ positivo |
| `Radical/NotComplete.lean` | No completo: existen sucesiones de Cauchy de radicales sin límite radical |

### Phase 7d: Números Algebraicos — `ZFC/Algebraic/`

| Módulo | Contenido principal |
|--------|---------------------|
| `Algebraic/Basic.lean` | `AlgebraicSet`: raíces de polinomios en ℤ[x]; cuerpo; contiene Constructible y Radical |
| `Algebraic/NotComplete.lean` | No completo: ∃ sucesión de Cauchy de algebraicos sin límite algebraico (ej. ∑ 1/n! = e ∉ Algebraic) |

---

## Phase 8: Reales ℝ — 📋 Planificado

**Pre-requisito**: Phase 6.5 completa (sucesiones de Cauchy en ℚ — base directa de la construcción de ℝ)

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
| 6: Racionales ℚ | ✅ Completo | 9 | 90 |
| 6.5: Sucesiones en ℚ | � En progreso | 6/7 | ~84 |
| 7a: Computables | 📋 Planificado | 0/4 | — |
| 7b: Constructibles | 📋 Planificado | 0/2 | — |
| 7c: Radicales | 📋 Planificado | 0/2 | — |
| 7d: Algebraicos | 📋 Planificado | 0/2 | — |
| 8: Reales ℝ | 📋 Planificado | 0/15 | — |
| Futuro | 🔮 Lejano | — | — |

---

*Última actualización: 2026-04-27. Phase 6.5 (Sucesiones en ℚ) en progreso: 6/7 módulos compilan (~84 exports adicionales); `cauchy_bounded` demostrado sin sorry; `Int/MaxMin` y `Rat/MaxMin` añadidos como soporte. 87 módulos activos en total, ~3 sorry legítimos (Real.Completeness). Pendiente: `Rat/SqrtApprox.lean` (prueba de incompletitud de ℚ como motivación de ℝ).*
