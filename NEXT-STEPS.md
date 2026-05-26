# Next Steps — ZfcSetTheory Project

**Last updated**: 2026-05-26

> Este documento detalla la hoja de ruta fase a fase (trabajo inmediato y próximos meses).
> Para la estrategia a largo plazo —embeddings entre sistemas formales, jerarquía
> Peano/ZFC/MK/TG/Categorías, plan de documentación y decisiones arquitectónicas—
> véase [PLANNING.md](PLANNING.md).
>
> El detalle teorema-a-teorema de las fases ya cerradas vive en [REFERENCE.md](REFERENCE.md)
> (proyección §3/§4/§6). Aquí solo se conserva el resumen y la planificación viva.

---

## Milestones completados

- ✅ **Aritmética en ω** (14 módulos): TFA, binomiales, maxmin, Newton, well-foundedness, GCD/LCM
- ✅ **Secuencias finitas** (3 módulos): isFinSeq, seqSum/seqProd, familyProduct, puente DList↔ZFC
- ✅ **Conjuntos finitos** (1 módulo): isFiniteSet, biyecciones, equipotencia
- ✅ **Cardinalidad** (2 módulos): Cantor, CSB, |𝒫(F)|=2^n
- ✅ **Álgebras de Boole** (11 módulos): Basic, Ring, PowerSetAlgebra, GenDeMorgan, GenDistributive, Atomic, Complete, Representation, FiniteCofinite, FiniteBA, BoolRingBA
- ✅ **Reorganización Fases 1–3**: namespaces `ZFC`, convenciones Mathlib (185 renames)
- ✅ **Enteros ℤ** (Phase 5, 15 módulos): 190 exports, 0 sorry, 0 errores
- ✅ **Racionales ℚ** (Phase 6, 9 módulos): `Equiv`, `Basic`, `Add`, `Neg`, `Mul`, `Order`, `Abs`, `Embedding`, `Field` — 0 sorry, 0 errores
- ✅ **Sucesiones en ℚ** (Phase 6.5, 7 módulos): `Int/MaxMin`, `Rat/MaxMin`, `Rat/Sequences`, `Rat/Convergence`, `Rat/CauchyQ`, `Rat/Monotone`, `Rat/SqrtApprox` — **0 sorry, 0 errores**.
- ✅ **Incompletitud secuencial de ℚ** (Phase 6.6, 1 módulo): `Rat/SqrtIrrational` — `sqrt2_irrational` y `sqrtApproxSeq_not_convergent` — **0 sorry**. Combinado con `sqrtApproxSeq_isCauchy`, demuestra que $(\mathbb{Q}, |\cdot|_\mathbb{Q})$ no es secuencialmente completo.
- ✅ **Tuplas ZFC** (Phase 7, 3 módulos): `SetOps/Tuple`, `SetOps/TupleOps`, `Rat/TupleSeq` — convención D9 (tupla de grado $n$ = función con dominio $\sigma n$), `seqSumQ`/`seqProdQ`. **0 sorry**.
- 🔶 **Exponenciación racional** (Phase 8, prerequisito): `Rat/Pow` — `powRatQ` ($x^n$) vía `RecursionTheoremWithStep`, leyes de exponentes $x^{n+m}=x^n x^m$ y $(xy)^n=x^n y^n$. **0 sorry**.

**Estado**: 93 módulos activos (+ barrel `Algebra` placeholder), **0 sorry**, **0 errores** (`lake build`: 114 jobs, verificado 2026-05-26).

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

## Phase 6.5: Sucesiones en ℚ — ✅ COMPLETA (2026-05-01)

**Pre-requisito**: Phase 6 completa (ℚ cuerpo ordenado arquimediano).
**Directorios**: `ZFC/Rat/` y `ZFC/Int/`. Detalle teorema-a-teorema proyectado en REFERENCE.md (§3.63–§3.68, §4.59–§4.66, §6.60–§6.67).

| # | Módulo | Exports clave | Estado |
|---|--------|---------------|--------|
| 0a | `Int/MaxMin.lean` | `maxZ`, `minZ`, 18 teoremas de retículo | ✅ |
| 0b | `Rat/MaxMin.lean` | `maxQ`, `minQ`, 18 teoremas de retículo | ✅ |
| 1 | `Rat/Sequences.lean` | `IsSeqQ`, `constSeqQ`, `addSeqQ`, `negSeqQ`, `mulSeqQ` | ✅ |
| 2 | `Rat/Convergence.lean` | `convergesToQ`, `limit_unique`, aritmética completa de límites (add/sub/mul/inv/div/abs/squeeze/subseq) | ✅ |
| 3 | `Rat/CauchyQ.lean` | `IsCauchyQ`, `cauchy_of_convergentQ`, `cauchy_bounded`, `CauchyEquivQ` (refl/symm/trans) | ✅ |
| 4 | `Rat/Monotone.lean` | `isNondecreasingQ`, `isBoundedQ`, `convergent_isBounded`, `nondecreasing/nonincreasing_bounded_isCauchy` | ✅ |
| 5 | `Rat/SqrtApprox.lean` | `twoQ`, `sqrtApproxSeq`, `sqrtApproxSeq_isCauchy`, `sqrtApproxSeq_sq_gt_two` | ✅ |
| 6 | `Rat/SqrtIrrational.lean` | `sqrt2_irrational`, `sqrtApproxSeq_not_convergent` (**ℚ no es secuencialmente completo**) | ✅ |

> **Nota**: `cauchyQ_of_convergent_subseq` (Cauchy + subsucesión convergente ⟹ convergente)
> y `convergesToQ_tail` están **implementados y exportados** (útiles para la completitud de ℝ en Phase 10).

---

## Phase 7: Tuplas e Infraestructura Algebraica — ✅ COMPLETA (2026-05-07)

**Motivación**: Antes de definir polinomios necesitamos un tipo de tupla finita bien fundada en ZFC puro (sin Mathlib). Una tupla de grado $n$ es una función $t: \sigma n \to \Omega$ (dominio $\{0,\ldots,n\}$, $n+1$ elementos).

| Módulo | Contenido principal | Estado |
| ------ | ------------------- | ------ |
| `SetOps/Tuple.lean` | `IsTuple t n Ω`, `tupleGraph`, `tuple_apply_mem`, `tupleGraph_isTuple`, `tupleGraph_apply`, `tuple_ext`, `zero_mem_sigma` | ✅ (11 exports) |
| `SetOps/TupleOps.lean` | `tupleHead`, `tupleLast`, `constTuple`, `tupleUpdate`, `tupleTail`, `concat` + `_isTuple`/`_apply` | ✅ (16 exports) |
| `Rat/TupleSeq.lean` | `seqSumQ`, `seqProdQ` vía `RecursionTheoremWithStep` sobre `RatSet`; función escalón guardada | ✅ (22 exports) |

**Convención D9**: grado $n$ $\Rightarrow$ dominio $\sigma n = \{0, \ldots, n\}$ ($n+1$ elementos), alineado con la codificación von Neumann de $\omega$.

> **Nota de documentación**: `Rat/TupleSeq.lean` está completo y **proyectado** en REFERENCE.md (§3.72/§4.70/§6.71).

---

## Phase 8: Monomios y Polinomios — 🔶 EN PROGRESO

**Pre-requisito**: Phase 7 (tuplas) + `Rat/Pow`. Barrel `ZFC/Algebra.lean` activo.

| Módulo | Contenido principal | Estado |
|--------|---------------------|--------|
| `Rat/Pow.lean` | `powRatQ x n = x^n` vía `RecursionTheoremWithStep`; `powRatQ_zero/succ/mem_RatSet/one`, `powRatQ_zero_base`, `powRatQ_one_base`, `powRatQ_add_exp`, `powRatQ_mul_base` (16 exports) | ✅ **COMPLETO** (prerequisito) |
| `Algebra/Monomial.lean` | Monomio: nulo = `∅` (centinela); no nulo = `⟨n,q⟩`, `n∈ω`, `q∈ℚ`, `q≠0`. `monomMk`, `IsMonom`, `monomCoeff`, `monomExp`, `monomDeg` (**grado WithBot ω**: `−∞↦∅`, `n↦σn`), `monomEval` (24 exports) | ✅ **COMPLETO** (proyección REFERENCE pendiente) |
| `Algebra/Polynomial.lean` | `IsPolyQ p n := IsTuple p n RatSet` (grado $\leq n$); `polyCoeff`, `polyEval p n x = seqSumQ (tupleGraph n RatSet (fun k => mulQ (p⦅k⦆) (powRatQ x k))) (σ n)`; `leadCoeff`, `IsMonic`, `IsRoot` | 🔜 **SIGUIENTE** |
| `Algebra/PolyArith.lean` | Suma, producto (convolución), negación de polinomios; $\mathbb{Q}[X]$ es dominio de integridad | 📋 Planificado |
| `Algebra/PolyDiv.lean` | Algoritmo de división de Euclides para polinomios; `polyGcd`; TFA en $\mathbb{Q}[X]$ | 📋 Planificado |

**Próximo paso inmediato**: crear `ZFC/Algebra/Polynomial.lean` (`namespace ZFC.Algebra.Polynomial`),
conectarlo al barrel `ZFC/Algebra.lean`. La evaluación reutilizará `powRatQ` (de `Rat/Pow`)
y `seqSumQ` (de `Rat/TupleSeq`), envolviendo `fun k => mulQ (p⦅k⦆) (powRatQ x k)` en `tupleGraph`.
Reto técnico: probar `p⦅k⦆·x^k ∈ RatSet` para `k ∈ σn` (de `IsPolyQ p n` + `powRatQ_mem_RatSet`).
Después: proyectar `Monomial` + `Polynomial` juntos en REFERENCE (`proyecta`).

---

## Phase 9: Cuerpos Ordenados Intermedios entre ℚ y ℝ — 📋 Planificado

**Pre-requisito**: Phase 6.5 completa (sucesiones de Cauchy en ℚ definidas y con ejemplos)
**Motivación**: Entre ℚ y ℝ existen cuerpos ordenados que contienen ℚ pero no son completos. Su formalización ilustra el rol esencial de la propiedad del supremo en la construcción de ℝ.

### Phase 9a: Números Computables — `ZFC/Computable/`

| Módulo | Contenido principal |
|--------|---------------------|
| `Computable/Basic.lean` | `ComputSet`: pares (f, N) con f: ω→ℚ Cauchy y módulo uniforme 1/2^N; relación de equivalencia de Cauchy |
| `Computable/Arith.lean` | Suma, producto, negativo, inverso; (Computables, +, ·) es cuerpo ordenado |
| `Computable/Embedding.lean` | ℚ ↪ Computables (sucesiones constantes); inyectividad, preserva orden |
| `Computable/NotComplete.lean` | `sqrtApprox` es computable pero no tiene límite computable: incompletitud de Computables |

### Phase 9b: Números Constructibles — `ZFC/Constructible/`

| Módulo | Contenido principal |
|--------|---------------------|
| `Constructible/Basic.lean` | `ConstructSet`: cierre mínimo de ℚ bajo +, −, ·, ÷ y √(x) para x>0; cada elemento es algebraico de grado potencia de 2 |
| `Constructible/NotComplete.lean` | No completo: sucesión de Cauchy en ConstructSet sin límite constructible (ej. ∑ 1/n! ∉ ConstructSet) |

### Phase 9c: Números Radicales — `ZFC/Radical/`

| Módulo | Contenido principal |
|--------|---------------------|
| `Radical/Basic.lean` | `RadicalSet`: cierre de ℚ bajo +, −, ·, ÷ y raíces n-ésimas para cualquier n∈ℕ positivo |
| `Radical/NotComplete.lean` | No completo: existen sucesiones de Cauchy de radicales sin límite radical |

### Phase 9d: Números Algebraicos — `ZFC/Algebraic/`

| Módulo | Contenido principal |
|--------|---------------------|
| `Algebraic/Basic.lean` | `AlgebraicSet`: raíces de polinomios en ℤ[x]; cuerpo; contiene Constructible y Radical |
| `Algebraic/NotComplete.lean` | No completo: ∃ sucesión de Cauchy de algebraicos sin límite algebraico (ej. ∑ 1/n! = e ∉ Algebraic) |

---

## Phase 10: Reales ℝ — 📋 Planificado

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
| 6.5: Sucesiones en ℚ | ✅ Completo | 7 | ~111 |
| 6.6: Incompletitud de ℚ | ✅ Completo | 1 | 2 |
| 7: Tuplas e infraestructura | ✅ Completo | 3 | ~49 |
| 8: Monomios y polinomios | 🔶 En progreso | 2/5 (Pow ✅, Monomial ✅) | 40 |
| 9a: Computables | 📋 Planificado | 0/4 | — |
| 9b: Constructibles | 📋 Planificado | 0/2 | — |
| 9c: Radicales | 📋 Planificado | 0/2 | — |
| 9d: Algebraicos | 📋 Planificado | 0/2 | — |
| 10: Reales ℝ | 📋 Planificado | 0/15 | — |
| Futuro | 🔮 Lejano | — | — |

---

*Última actualización: 2026-05-26 (sesión 15c). Phase 8 avanza: `Algebra/Monomial.lean` completo (24 exports, 0 sorry, compiló a la primera). Monomio nulo = `∅` (centinela), grado en codificación WithBot ω (`−∞↦∅`, `n↦σn`). Barrel `ZFC/Algebra.lean` activo. 95 archivos `.lean` bajo `ZFC/`, **0 sorry, 0 errores, 0 warnings ZFC** (115 jobs). Siguiente: `Algebra/Polynomial.lean`.*

*Actualización anterior: 2026-05-26 (sesión 15b). Cierre de gaps de proyección: `Rat/TupleSeq.lean` proyectado en REFERENCE.md (§3.72/§4.70/§6.71) + §3 de SqrtApprox/SqrtIrrational. Limpieza de código: docstring "Left as sorry" corregido en `Rat/Monotone.lean`; 0 warnings en ZFC (corregidas variables sin usar en Int/MaxMin, Rat/MaxMin, Convergence, CauchyQ y simp redundantes en los `_comm`). **0 sorry, 0 errores, 0 warnings ZFC** (114 jobs).*

*Actualización anterior: 2026-05-26 (sesión 15a). Phase 8 iniciada: `Rat/Pow.lean` completo (exponenciación racional, 16 exports, proyectado en REFERENCE.md §3.71/§4.69/§6.70). Barrel `ZFC/Algebra.lean` creado como placeholder y conectado a `ZFC.lean`. Limpieza de NEXT-STEPS: eliminados los planes teorema-a-teorema ya cumplidos de Phase 6.5 (ahora en REFERENCE.md), Phase 6.5 marcada COMPLETA. 93 módulos activos, **0 sorry, 0 errores** (114 jobs).*

*Actualización anterior: 2026-05-07 (sesión 13). Phase 7 (Tuplas) completada: SetOps/Tuple.lean + SetOps/TupleOps.lean + Rat/TupleSeq.lean. 92 módulos totales, **0 sorry, 0 errores**.*
