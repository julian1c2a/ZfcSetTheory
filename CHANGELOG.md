# Changelog

**Última actualización:** 2026-05-26
**Autor**: Julián Calderón Almendros

Todos los cambios notables de este proyecto serán documentados en este archivo.

El formato está basado en [Keep a Changelog](https://keepachangelog.com/es-ES/1.0.0/),
y este proyecto adhiere a [Semantic Versioning](https://semver.org/spec/v2.0.0.html).

## [Unreleased]

### Añadido (2026-05-26 — sesión 15c)

- **Phase 8 — `Algebra/Monomial.lean` (monomios sobre ℚ) — NUEVO (0 sorry)**:
  - Representación: monomio nulo = `∅` (centinela canónico; ningún par Kuratowski `⟨n,q⟩` es `∅`); monomio no nulo = `⟨n, q⟩` con exponente `n ∈ ω` y coeficiente `q ∈ ℚ`, `q ≠ 0`.
  - `monomMk n q` — constructor que normaliza coeficiente 0 al nulo canónico; `IsMonom`, `IsZeroMonom`.
  - **Grado con codificación WithBot ω** (decisión de diseño): `monomDeg` con `−∞ ↦ ∅` y `n ↦ σ n`, de modo que el orden `≼` de ω da el orden de grados con `∅` como fondo. `monomExp` = exponente literal (junk 0 para el nulo) usado en la evaluación.
  - `monomEval m x = monomCoeff m · x^(monomExp m)` vía `powRatQ`; correcto incluso para el nulo (el coeficiente 0 absorbe el exponente basura).
  - Lemas clave: `monomMk_isMonom`, `monomCoeff_mk` (incondicional), `monomExp_mk`, `monomDeg_mk`, clausuras (`monomCoeff_mem_RatSet`, `monomExp_mem_omega`, `monomDeg_mem_omega`), `monomEval_zero`, `monomEval_mk`, `monomEval_mem_RatSet`.
  - Namespace `ZFC.Algebra.Monomial` (exportado a `ZFC`, **24 exports**); barrel `ZFC/Algebra.lean` activado con `import ZFC.Algebra.Monomial`.
  - Compiló sin errores ni warnings al primer intento.
  - **Pendiente**: proyección en REFERENCE.md (se agrupará con `Algebra/Polynomial.lean`; registrado en §7.5).

- **Estado**: 95 archivos `.lean` bajo `ZFC/` (incl. 11 barrels) · **0 sorry · 0 errores · 0 warnings ZFC** (`lake build`: 115 jobs).

### Proyectado y corregido (2026-05-26 — sesión 15b)

- **Cierre de gaps de proyección en REFERENCE.md**:
  - **`Rat/TupleSeq.lean`** proyectado completo (Phase 7, antes sin documentar): §1.1 (fila), §3.72 (6 definiciones: `sumQStepFn`/`seqSumQFn`/`seqSumQ` + análogos de producto), §4.70 (16 teoremas: ecuaciones de recursión, clausura, singleton), §6.71 (22 exports), §7.2 (bullet). §7.5 queda vacío.
  - **`Rat/SqrtApprox.lean`**: añadido §3.73 con las definiciones públicas que faltaban (`twoQ`, `sqrtApproxSeq`).
  - **`Rat/SqrtIrrational.lean`**: añadido §3.74 (stub, sin definiciones públicas).

- **Limpieza de código (0 warnings en ZFC)**:
  - `Rat/Monotone.lean`: corregido el docstring obsoleto "Left as sorry" de `convergent_isBounded` (el teorema está probado vía `cauchy_bounded ∘ cauchy_of_convergentQ`).
  - `Int/MaxMin.lean` y `Rat/MaxMin.lean`: hipótesis de clausura sin usar prefijadas con `_` (`maxZ_leZ`/`leZ_minZ`/`leQ_maxQ_left`/`maxQ_leQ`/…) y eliminados los `if_pos hxy`/`if_pos hyx` redundantes en `maxZ_comm`/`minZ_comm`/`maxQ_comm`/`minQ_comm` (solo `heq` es necesario).
  - `Rat/Convergence.lean` (`subseq_convergent`, `absQ_le_of_bounds`) y `Rat/CauchyQ.lean` (`subseq_of_cauchyQ`, `cauchyQ_of_convergent_subseq`): hipótesis sin usar prefijadas con `_`.
  - Resultado: **0 warnings en módulos `ZFC/`** (queda 1 warning en la dependencia `PeanoNatLib`, fuera de este repo).

- **Verificación**: `cauchyQ_of_convergent_subseq` y `convergesToQ_tail` confirmados **implementados y exportados** (corrige una nota errónea previa en NEXT-STEPS).

- **Estado**: 93 módulos activos (+ barrel `Algebra`) · **0 sorry · 0 errores · 0 warnings ZFC** (`lake build`: 114 jobs).

### Añadido (2026-05-26 — sesión 15a)

- **Phase 8 iniciada — `Rat/Pow.lean` (exponenciación racional) — NUEVO (0 sorry)**:
  - `powRatQ x n = x^n` para $x \in \mathbb{Q}$, $n \in \omega$, vía `RecursionTheoremWithStep` sobre `RatSet` (base $1_\mathbb{Q}$, paso $\langle k, v\rangle \mapsto v \cdot x$).
  - Función escalón guardada `powRatQStepFn` (usa `if x ∈ RatSet then x else oneQ` para clausura sin hipótesis sobre $x$), análoga al patrón de `Rat/TupleSeq`.
  - `powRatQ_zero` ($x^\emptyset = 1_\mathbb{Q}$), `powRatQ_succ` ($x^{\sigma n} = x^n \cdot x$), `powRatQ_mem_RatSet` (clausura).
  - `powRatQ_one` ($x^{\sigma\emptyset} = x$), `powRatQ_zero_base` ($0_\mathbb{Q}^n = 0_\mathbb{Q}$ para $n \neq \emptyset$), `powRatQ_one_base` ($1_\mathbb{Q}^n = 1_\mathbb{Q}$).
  - `powRatQ_add_exp` ($x^{n+m} = x^n \cdot x^m$), `powRatQ_mul_base` ($(x\cdot y)^n = x^n \cdot y^n$).
  - Namespace `ZFC.Rat.Pow` (exportado a `ZFC`, **16 exports**); `ZFC/Rat.lean` barrel incluye `import ZFC.Rat.Pow`.

- **Barrel `ZFC/Algebra.lean` — NUEVO (placeholder Phase 8)**:
  - Archivo paraguas para la Phase 8 (monomios y polinomios); aún sin submódulos `Algebra/*` (imports comentados).
  - Conectado a la raíz `ZFC.lean` (`import ZFC.Algebra`).

- **Documentación sincronizada**:
  - **REFERENCE.md**: proyectado `Rat.Pow.lean` — §1.1 (fila), §3.71 (3 definiciones), §4.69 (13 teoremas), §6.70 (16 exports), §7.2 (bullet). Detectado y registrado en §7.5 que `Rat/TupleSeq.lean` sigue pendiente de proyectar.
  - **README.md**: badge 91 → 93 módulos, estado a 2026-05-26, sección Phase 8, árbol de directorios (Rat 18 módulos + `Algebra/`).
  - **NEXT-STEPS.md**: Phase 6.5 marcada COMPLETA, eliminados los planes teorema-a-teorema ya cumplidos (ahora en REFERENCE.md), Phase 8 promovida a 🔶 en progreso.
  - **Corrección detectada** (aplicada en sesión 15b): comentario obsoleto "Left as sorry" en `Rat/Monotone.lean:1070` — `convergent_isBounded` está probado vía `cauchy_bounded`.

- **Estado**: 93 módulos activos (+ barrel `Algebra`) · **0 sorry** · **0 errores** (`lake build`: 114 jobs, verificado 2026-05-26).

### Añadido (2026-05-07 — sesión 14)

- **Apply lemmas para tuplas (6 nuevos teoremas en `SetOps/TupleOps.lean`)**:
  - `constTuple_apply` — `(constTuple n a Ω)⦅i⦆ = a`.
  - `tupleUpdate_apply_eq` — índice actualizado devuelve el nuevo valor.
  - `tupleUpdate_apply_ne` — índice distinto devuelve el original.
  - `tupleTail_apply` — `(tupleTail t n Ω)⦅i⦆ = t⦅σ i⦆`.
  - `concat_apply_left` — índice del segmento izquierdo: `(concat ...)⦅j⦆ = t₁⦅j⦆`.
  - `concat_apply_right` — índice del segmento derecho: `(concat ...)⦅j⦆ = t₂⦅sub j (σ n₁)⦆`.
  - `TupleOps`: 10 → **16 exports**.

- **`Rat/TupleSeq.lean` — Sumas y productos de sucesiones racionales — NUEVO (0 sorry)**:
  - Implementa `seqSumQ` y `seqProdQ` mediante `RecursionTheoremWithStep` sobre `RatSet`.
  - Función escalón guardada: `sumQStepFn`/`prodQStepFn` son funciones `ω ×ₛ RatSet → RatSet` sin hipótesis sobre `t` (usa `if t⦅k⦆ ∈ RatSet then ... else zeroQ/oneQ` para el caso fuera de dominio).
  - `seqSumQ t ∅ = zeroQ` · `seqSumQ t (σ k) = addQ (seqSumQ t k) (t⦅k⦆)` cuando `t⦅k⦆ ∈ RatSet`.
  - `seqProdQ t ∅ = oneQ` · `seqProdQ t (σ k) = mulQ (seqProdQ t k) (t⦅k⦆)` cuando `t⦅k⦆ ∈ RatSet`.
  - `seqSumQ_mem_RatSet`, `seqProdQ_mem_RatSet` — clausura para cualquier `n ∈ ω`.
  - `seqSumQ_singleton`, `seqProdQ_singleton` — base de la inducción por tuplas.
  - Namespace `ZFC.Rat.TupleSeq` (exportado a `ZFC`, **22 exports**).
  - `ZFC/Rat.lean` barrel actualizado con `import ZFC.Rat.TupleSeq`.
  - **Estado**: 92 módulos · **0 sorry** · **0 errores de compilación** (verificado 2026-05-07).

### Añadido (2026-05-07 — sesión 13)

- **Phase 7 — Tuplas ZFC (Convención D9) — COMPLETA (0 sorry)**:
  - ✅ **`SetOps/Tuple.lean`** — Tuplas como funciones ZFC con dominio $\sigma n = \{0,\ldots,n\}$:
    - `IsTuple t n Ω` — predicado: $n \in \omega$ y $t$ es función con dominio $\sigma n$ y codominio $\Omega$.
    - `tupleGraph n Ω vals` — construcción de la gráfica desde función Lean: $\{ \langle i, \text{vals}(i) \rangle \mid i \in \sigma n \}$.
    - `tuple_apply_mem` — $t\langle i \rangle \in \Omega$ siempre que $i \in \sigma n$.
    - `tupleGraph_isTuple` — `tupleGraph` produce un `IsTuple` válido.
    - `tupleGraph_apply` — `(tupleGraph n Ω vals)⦅i⦆ = vals i`.
    - `tuple_ext` — extensionalidad: dos tuplas iguales en todos los índices son iguales como conjuntos ZFC.
    - `zero_mem_sigma` — $\emptyset \in \sigma n$ para todo $n \in \omega$ (el índice 0 siempre existe).
    - Namespace `ZFC.SetOps.Tuple` (exportado a `ZFC`, **11 exports**).
  - ✅ **`SetOps/TupleOps.lean`** — Operaciones sobre tuplas:
    - `tupleHead t` — primer elemento $t\langle\emptyset\rangle$.
    - `tupleLast t n` — último elemento $t\langle n \rangle$.
    - `constTuple n a Ω` — tupla constante; `constTuple_isTuple` demuestra validez.
    - `tupleUpdate t n Ω i v` — actualizar un índice; `tupleUpdate_isTuple` demuestra validez.
    - `tupleTail t n Ω` — cola (grado `predecessor n`, índices $1,\ldots,n$ renumerados); `tupleTail_isTuple` demuestra validez.
    - `concat t₁ n₁ t₂ n₂ Ω` — concatenación (grado $n_1 + \sigma n_2$); `concat_isTuple` demuestra validez. Lema aritmético clave: `sub_mem_sigma_of_not_in_sigma` (privado, usa tricotomía + `add_k_sub_k_Omega`).
    - Namespace `ZFC.SetOps.TupleOps` (exportado a `ZFC`, **10 exports**).
  - ✅ `ZFC/SetOps.lean` barrel actualizado con ambos módulos.
  - ✅ **REFERENCE.md** actualizado: §1.1 (2 filas), §1.2 (grupo 7-axiomas), §3.69–§3.70 (definiciones), §4.67–§4.68 (teoremas), §6.68–§6.69 (exports), §7.2 (entradas completas para SqrtApprox, SqrtIrrational, Tuple, TupleOps), §7.5 (91/91 módulos proyectados).
  - ✅ **NEXT-STEPS.md** actualizado: Phase 7 marcada ✅ COMPLETA, tabla de resumen actualizada (2/2 módulos, 21 exports).
  - **Estado**: 91 módulos · **0 sorry** · **0 errores de compilación** (verificado 2026-05-07).

### Añadido (2026-05-01 — sesión 11)

- **`Rat/SqrtIrrational.lean` — Incompletitud secuencial de $\mathbb{Q}$ COMPLETA (0 sorry)**:
  - ✅ `sqrt2_irrational` — $\nexists L \in \mathbb{Q},\ L^2 = 2$, vía descenso 2-ádico (`omega_descent_two_squares`).
  - ✅ `sqrtApproxSeq_not_convergent` — la sucesión Newton–Raphson de Cauchy no converge en $\mathbb{Q}$.
  - Estrategia: identidad puntual $2 \cdot f(\sigma n) \cdot f(n) = f(n)^2 + 2$ + paso al límite (`convergesToQ_tail/mul/add/const`, `convergesToQ_of_eventually_eq`, `limit_unique`) ⟹ $2 L^2 = L^2 + 2$ ⟹ $L^2 = 2$, contradicción con `sqrt2_irrational`.
  - **Corolario**: $(\mathbb{Q}, |\cdot|_\mathbb{Q})$ no es secuencialmente completo (combina `sqrtApproxSeq_isCauchy` con `sqrtApproxSeq_not_convergent`).
- **`Rat/SqrtApprox.lean` — Exposición pública de `twoQ`**:
  - `twoQ`, `twoQ_mem`, `twoQ_ne_zeroQ`, `twoQ_pos` añadidos a `export`.
- **`Rat/Convergence.lean` — Helpers para corrimientos**:
  - `tailSeqQ`, `tailSeqQ_isSeqQ`, `tailSeqQ_apply`, `convergesToQ_tail` (cola converge al mismo límite).

### Añadido (2026-04-29 — sesiones 9–10)

- **`Rat/Convergence.lean` — Aritmética completa de límites (9 nuevos teoremas)**:
  - ✅ `convergesToQ_sub` — convergencia de la resta
  - ✅ `convergesToQ_of_dominated` — dominación por sucesión que tiende a 0
  - ✅ `squeeze_theorem` — teorema del encaje (sandwich)
  - ✅ `convergesToQ_of_eventually_eq` — igualdad eventual preserva límite
  - ✅ `convergesToQ_const_mul` — múltiplo escalar (c·f → c·L)
  - ✅ `convergesToQ_abs` — convergencia del valor absoluto
  - ✅ `convergesToQ_zero_of_abs` — |f|→0 implica f→0
  - ✅ `convergesToQ_iff_abs` — f→L ↔ |f−L|→0
  - ✅ `convergesToQ_mul` — convergencia del producto (acotación inline, sin CauchyQ)
  - Helpers privados: `negQ_subQ`, `absQ_le_of_bounds`, `absQ_reverse_triangle`, `absSeqQ`, `isPositiveQ_of_ge_oneQ`
  - **Estado**: 17 exports · 0 sorry · módulo completamente terminado
  - **REFERENCE.md**: §3.66, §4.62 y §6.63 actualizados

### Añadido (2026-04-29 — sesión 8)

- **Phase 6.5 — 0 sorry confirmado (todos los teoremas demostrados)**:
  - ✅ Eliminados los 2 sorry de `Rat/Convergence.lean` (aritmética avanzada de límites)
  - ✅ Eliminado el 1 sorry de `Rat/Monotone.lean` (`convergent_isBounded`)
  - ✅ `convergent_isBounded` demostrado vía `cauchy_bounded ∘ cauchy_of_convergentQ`
  - ✅ `nondecreasing_bounded_isCauchy` y `nonincreasing_bounded_isCauchy` demostrados por argumento arquimediano directo (sin `Real.Completeness`)
  - **Estado**: 87 módulos · 0 sorry · 0 errores · Phase 6.5 al 6/7 módulos
- **Documentación actualizada**: REFERENCE.md, NEXT-STEPS.md, README.md — estado de sorry corregido en §3.66, §3.68, §4.64, §6.63, §6.65, §7.2, §7.4

### Añadido (2026-04-27)

- **Phase 6.5 — Sucesiones en ℚ (6/7 módulos, compilan)**:
  - ✅ `Int/MaxMin.lean` — `maxZ`, `minZ` desde `leZ`; 18 teoremas de retículo; 20 exports
  - ✅ `Rat/MaxMin.lean` — `maxQ`, `minQ` desde `leQ`; 18 teoremas de retículo; 20 exports
  - ✅ `Rat/Sequences.lean` — `IsSeqQ`, `constSeqQ`, `addSeqQ`, `negSeqQ`, `mulSeqQ`; clausura y aplicación; 14 exports
  - ✅ `Rat/Convergence.lean` — `convergesToQ` (def ε-N), `hasLimitQ`, `IsSubseqOf`; `convergesToQ_const`, `limit_unique`, `convergesToQ_add`, `convergesToQ_mul_bounded`, `subseq_convergent`; 8 exports
  - ✅ `Rat/CauchyQ.lean` — `IsCauchyQ`, `cauchy_of_convergentQ`, `cauchy_bounded` (por inducción en ω con `maxQ`), `constSeqQ_isCauchy`; 4 exports
  - ✅ `Rat/Monotone.lean` — 7 definiciones de monotonía/acotamiento; `nondecreasing_convergent_limit_ge`, `limit_le_of_bounded_above`, `convergent_isBounded`, `nondecreasing_bounded_isCauchy`, `nonincreasing_bounded_isCauchy`; 18 exports
  - ❌ `Rat/SqrtApprox.lean` — No iniciado (prueba de incompletitud de ℚ, motivación de ℝ)
  - **REFERENCE.md**: §3.63–3.68, §4.59–4.64, §6.60–6.65 proyectados (72 módulos totales)

### Añadido (2026-04-26)

- **Phase 6 (ℚ) — Completada**: 9 módulos, 0 sorry, 0 errores, 81 módulos activos en total
  - README.md, REFERENCE.md y NEXT-STEPS.md actualizados con estado definitivo
- **Nuevo módulo `Rat/Field.lean` — Axiomas de cuerpo de ℚ**:
  - ✅ 14 teoremas: `mulQ_eq_zero_iff`, `mulQ_ne_zeroQ`, `mulQ_left_cancel`, `mulQ_right_cancel`
  - ✅ `invQ_invQ` (doble inverso), `invQ_mulQ` (inverso del producto)
  - ✅ `divQ_self`, `divQ_one`, `divQ_mulQ_cancel`, `mulQ_divQ_cancel`
  - ✅ `negQ_mulQ_left`, `negQ_mulQ_right`
  - ✅ `mulQ_addQ_distrib_left`, `mulQ_addQ_distrib_right`
  - ✅ Namespace `ZFC.Rat.Field` (exportado a `ZFC`, 14 exports)
  - ✅ Proyectado en REFERENCE.md §3.62, §4.58, §6.59
- **Propiedad arquimediana**:
  - ✅ `archZ` (private) en `Rat/Embedding.lean` — ∀ z ∈ ℤ, ∃ n ∈ ω, z ≤ natToInt n
  - ✅ `archQ` — ∀ q ∈ ℚ, ∃ n ∈ ω, q ≤ intToRat(natToInt n)
- **Fix**: eliminados warnings de variables no usadas en `Int/Sub.lean`, `Int/DivMod.lean`, `Int/Div.lean`, `Int/Pow.lean` (prefijo `_`)
- **Refactor**: eliminado `patch_divOf.lean` (módulo obsoleto)
- **REFERENCE.md**: proyección de `Rat/Embedding.lean` (§3.61, §4.57, §6.58) y `Rat/Field.lean` (§3.62, §4.58, §6.59); §7.5: 64/64 módulos proyectados; 18000+ líneas

### Añadido (2026-04-25)

- **Nuevo módulo `Rat/Embedding.lean` — Embedding canónico ℤ ↪ ℚ**:
  - ✅ `intToRat (n : U) : U` — `noncomputable def`, mapea n ↦ ratClass n oneZ
  - ✅ `intToRat_mem_RatSet`, `intToRat_injective`
  - ✅ Preservación: `intToRat_zeroZ`, `intToRat_oneZ`, `intToRat_preserves_add/neg/sub/mul`
  - ✅ Orden: `intToRat_preserves_leZ/ltZ`, `intToRat_reflects_leZ/ltZ`
  - ✅ `intToRat_not_surjective` — 1/2 ∉ Im(ι)
  - ✅ Namespace `ZFC.Rat.Embedding` (exportado a `ZFC`, 15 exports)

### Añadido (2026-04-23)

- **Phase 5 (ℤ) — Marcada 100% completa**: 190 exports, 0 sorry, todos los ítems opcionales implementados
- **Phase 6 (ℚ) — Iniciada**: `Rat/Equiv.lean` con `RatEquivRel` sobre ℤ × ℤ* (NonZeroIntSet, RatBase, RatSet)
- **6 nuevos módulos ℚ completados en un solo día**:
  - ✅ `Rat/Basic.lean` — `ratClass`, `zeroQ`, `oneQ`; `ratClass_eq_iff`, `ratClass_ne_iff`, 13 exports
  - ✅ `Rat/Add.lean` — `addQ`; `addQ_comm`, `addQ_assoc`, `addQ_zeroQ_right`, 7 exports
  - ✅ `Rat/Neg.lean` — `negQ`; inverso aditivo, `negQ_negQ`, 7 exports
  - ✅ `Rat/Mul.lean` — `mulQ`, `invQ`, `divQ`; `mulQ_comm`, `mulQ_assoc`, `mulQ_oneQ`, `invQ_mulQ_right`, 18 exports
  - ✅ `Rat/Order.lean` — `leQ`, `ltQ`, `isPositiveQ`, `isNegativeQ`; orden total, compatibilidad con +/×, 17 exports
  - ✅ `Rat/Abs.lean` — `subQ`, `absQ`, `signQ`; desigualdad triangular, `absQ_mulQ`, `signQ_mulQ_absQ`, 13 exports
- **Refactor**: eliminados archivos obsoletos y pruebas no utilizadas (`_test_tactic.lean`, `test_*.lean`, etc.)
- **fix(`Int/Order`)**: `tauto` → `constructor` para compatibilidad con Lean v4.29.0

### Cambiado (2026-04-22)

- **Refactor mayor: renombrado `ZfcSetTheory/` → `ZFC/`**:
  - ✅ Directorio fuente renombrado de `ZfcSetTheory/` a `ZFC/`
  - ✅ Módulo raíz: `ZfcSetTheory.lean` → `ZFC.lean`
  - ✅ `lakefile.lean`: `lean_lib «ZFC»` (package sigue siendo `«ZfcSetTheory»`)
  - ✅ Todos los `import ZfcSetTheory.*` actualizados a `import ZFC.*`
  - ✅ Build limpio después del refactor
- **fix**: contaminación `DList.Mem` en `Nat/Gcd.lean`, `Nat/Primes.lean`, `Peano/FiniteSequencesBridge.lean`
- **Phase 5 (ℤ) — 13 ítems opcionales implementados**:
  - ✅ `Int/Units.lean` — `isUnitZ`, `unitZ_iff` (unidades de ℤ = {1, −1})
  - ✅ `Int/Div.lean` — `tfa_Z` (TFA en ℤ: toda z ≠ 0, ∉ ℤ× admite factorización prima única)
  - ✅ `bezoutZ` completado sin sorry (identidad de Bézout en ℤ)
  - ✅ Refactor de notación `∈` para evitar contaminación de `DList.Mem`
- **fix(`Induction/Recursion`)**: ajuste de importaciones y corrección de comentarios

### Añadido (2026-04-21)

- **`bezoutZ` — Identidad de Bézout en ℤ (0 sorry)**:
  - ✅ `bezoutZ (a b : U) : a ∈ IntSet → b ∈ IntSet → ∃ s t, natToInt (gcdZ a b) = s·a + t·b`
  - Prueba directa en ZFC nativo sin Mathlib, combinando `gcdZ` y `euclidean_divisionZ`

### Añadido (2026-04-10)

- **Phase 4: Sistema de Anotaciones en REFERENCE.md — Completado**:
  - ✅ `@axiom_system` — §1.2 "Axiomas ZFC por Módulo": tabla completa de 47 módulos clasificados por axiomas ZFC usados transitivamente (7 axiomas: Ext, Vac, Sep, Par, Uni, Pot, Inf)
  - ✅ `@importance` — Anotaciones high/medium/low para todos los teoremas:
    - §4.1–§4.18 (NEW §4): anotaciones per-theorem inline (`**Importancia**: high/medium/low`) — ~280+ teoremas
    - §4.19–§4.41 (NEW §4): bloques module-level (`**Importancia por sección/teorema**:`) — 23 módulos
    - §4.1–§4.7 (OLD §4): bloques per-theorem para Nat.Basic — 7 subsecciones, 22 teoremas
  - ✅ Criterios de importancia: high = resultado principal o usado por 3+ módulos; medium = usado por 1-2 módulos; low = auxiliar/interno
  - ✅ NEXT-STEPS.md actualizado: Phase 4 marcada como ✅ Complete

### Cambiado (2026-04-02)

- **Fase 3: Convención de nombres Mathlib (renombrado global)**:
  - ✅ 40 archivos .lean modificados, ~2300 líneas cambiadas
  - ✅ **Definiciones renombradas** (13 renames):
    - `subseteq` → `subset`, `subset` → `ssubset` (⊆/⊂ swap)
    - `SpecSet` → `sep`, `BinInter` → `inter`, `Difference` → `sdiff`
    - `BinUnion` → `union`, `UnionSet` → `sUnion`, `SymDiff` → `symmDiff`
    - `PowerSetOf` → `powerset`, `successor` → `succ`
    - `FunctionComposition` → `comp`, `IdFunction` → `idFn`, `InverseFunction` → `inv`
    - `ImageSet` → `image`, `PreimageSet` → `preimage`, `Restriction` → `restrict`, `DiagonalSet` → `diagSet`
  - ✅ **Predicados → UpperCamelCase** (5 renames):
    - `isNat` → `IsNat`, `isInductive` → `IsInductive`, `isInitialSegment` → `IsInitialSegment`
    - `isSingleValued` → `IsSingleValued`, `isFunctionFromTo` → `IsFunction`
    - `isTransitiveSet` → `IsTransitive` (hecho en Fase 3 de Extension.lean)
  - ✅ **Teoremas renombrados** (~90 patrones):
    - Patrón `_is_specified` → `mem_X_iff`: `SpecSet_is_specified` → `mem_sep_iff`, etc.
    - Propiedades algebraicas: `_commutative` → `_comm`, `_associative` → `_assoc`, `_idempotence` → `_self`
    - Naturales: `zero_is_nat` → `isNat_zero`, `nat_successor_is_nat` → `isNat_succ`, `successor_injective` → `succ_injective`, etc.
    - De Morgan: `DeMorgan_union` → `compl_union`, `DeMorgan_inter` → `compl_inter`
    - Absorción: `BinInter_absorb_union` → `inter_union_self`
    - Distributividad: `BinUnion_distrib_inter` → `union_inter_distrib_left`, etc.
  - ✅ **Compound names** actualizados en BoolAlg/: `SymDiff_*` → `symmDiff_*`, `PowerSet_*` → `powerset_*`, `UnionSet_*` → `sUnion_*`
  - ✅ `subseteq_antisymmetric` eliminado (redundante con `subset_antisymm`)
  - ✅ Todas las notaciones preservadas: ⊆ ⊂ ⊇ ⊃ ∩ \ ∪ △ 𝒫 ⋃
  - ✅ Build limpio: 71 jobs, 0 errores, 0 sorry
  - ✅ Proyección en REFERENCE.md: Completada (nombres Mathlib reflejados en 47/47 módulos)

- **Fase 2b: Alineación de sub-namespaces con estructura de directorios**:
  - ✅ 42 sub-namespaces renombrados para reflejar la jerarquía de directorios
  - ✅ Axiom: `ExtensionAxiom` → `Axiom.Extension`, etc. (7 archivos)
  - ✅ SetOps: `OrderedPairExtensions` → `SetOps.OrderedPair`, `CartesianProduct` → `SetOps.CartesianProduct`, etc. (7 archivos)
  - ✅ Nat: `NaturalNumbers` → `Nat.Basic`, `NaturalNumbersAdd` → `Nat.Add`, etc. (14 archivos)
  - ✅ BoolAlg: `BooleanAlgebra` → `BoolAlg.Basic`, `CompleteBooleanAlgebra` → `BoolAlg.Complete`, etc. (8 archivos)
  - ✅ Peano: `PeanoIsomorphism` → `Peano.Import`, `FiniteSequences` → `Peano.FiniteSequences`, etc. (4 archivos)
  - ✅ Cardinal: `Cardinality` → `Cardinal.Basic` (1 archivo)
  - ✅ Induction: `Recursion` → `Induction.Recursion` (1 archivo)
  - ✅ Actualizada documentación: 12 archivos .md
  - ✅ Build limpio: 71 jobs, 0 errores, 0 sorry

- **Fase 2a: Migración de namespace `SetUniverse` → `ZFC`**:
  - ✅ Renombrado `namespace SetUniverse` → `namespace ZFC` en 43 archivos .lean
  - ✅ Renombrado `end SetUniverse` → `end ZFC` en todos los archivos
  - ✅ Actualizadas todas las referencias `open ZFC.SubNamespace` y `export ZFC.SubNamespace`
  - ✅ Actualizada documentación: REFERENCE.md, DEPENDENCIES.md, CHANGELOG.md, CURRENT-STATUS-PROJECT.md, NAMING-CONVENTIONS.md, PLAN_IMPORT_PEANO.md, TEMPORAL.md
  - ✅ Build limpio: 71 jobs, 0 errores, 0 sorry

### Añadido (2026-04-01)

- **Nuevo módulo BoolAlg.Complete.lean — Álgebra booleana completa atómica**:
  - ✅ `isSupremumIn (L S x : U) : Prop` — supremo de S dentro del retículo L
  - ✅ `isInfimumIn (L S x : U) : Prop` — ínfimo de S dentro del retículo L
  - ✅ `isCompleteLattice (L : U) : Prop` — todo subconjunto de L tiene supremo e ínfimo en L
  - ✅ `isCompleteAtomicBA (A : U) : Prop` — 𝒫(A) es retículo completo y atómico
  - ✅ 11 teoremas: `supremumIn_unique`, `infimumIn_unique`, `UnionSet_subset_of_family`, `UnionSet_mem_PowerSet_of_family`, `UnionSet_is_supremumIn_PowerSet`, `interSet_subset_of_family`, `interSet_mem_PowerSet_of_family`, `interSet_is_infimumIn_PowerSet`, `universe_is_infimumIn_PowerSet_empty`, `PowerSet_is_complete_lattice`, `PowerSet_is_complete_atomic_BA`
  - ✅ Namespace `ZFC.BoolAlg.Complete` (exportado a `ZFC`, 15 exports)
  - ✅ Build limpio; 42/43 módulos compilados (módulo añadido antes de BoolAlg.FiniteCofinite)
  - ✅ Proyección en REFERENCE.md: Completada (§3.41 definiciones, §4.37 teoremas, §1.1 ✅ Completo)

- **Nuevo módulo BoolAlg.FiniteCofinite.lean — Álgebra finita/cofinita, contraejemplo no completo**:
  - ✅ `isCofinite (A X : U) : Prop` — predicado de cofinitud: A \ X es finito
  - ✅ `isFinCof (A X : U) : Prop` — X ⊆ A y (X finito o X cofinito en A)
  - ✅ `FinCofAlg (A : U) : U` — álgebra de subconjuntos finitos y cofinitos de A
  - ✅ `EvenSet : U` — {n ∈ ω | ∃ k ∈ ω, n = k+k}
  - ✅ 19 teoremas públicos en 4 secciones:
    - Clausura de finitud (3): `finite_subset`, `finite_union`, `Omega_not_finite`
    - Paridad (7): `double_injective`, `even_or_odd`, `even_ne_odd`, `EvenSet_is_specified`, `EvenSet_subset_Omega`, `EvenSet_infinite`, `OddSet_infinite`
    - Estructura de álgebra booleana (7): `FinCofAlg_is_specified`, `FinCofAlg_subset_PowerSet`, `FinCofAlg_empty`, `FinCofAlg_universe`, `FinCofAlg_complement`, `FinCofAlg_union`, `FinCofAlg_inter`
    - No completitud (2): `EvenSet_not_in_FinCofAlg`, `FinCofAlg_not_complete`
  - ✅ Namespace `ZFC.BoolAlg.FiniteCofinite` (exportado a `ZFC`, 22 exports)
  - ✅ Build limpio; 43/43 módulos compilados correctamente (0 sorry, 0 errores)
  - ✅ Proyectado en REFERENCE.md §3.40, §4.36, §6.37

- **REFERENCE.md — Proyección de BoolAlg.FiniteCofinite.lean + registro de BoolAlg.Complete.lean**:
  - ✅ §1.1: 2 filas añadidas (BoolAlg.Complete ✅ Completo, BoolAlg.FiniteCofinite ✅ Completo)
  - ✅ §3.40: 4 definiciones de BoolAlg.FiniteCofinite
  - ✅ §3.41: 4 definiciones de BoolAlg.Complete
  - ✅ §4.36: 19 teoremas en 4 secciones
  - ✅ §4.37: 11 teoremas de BoolAlg.Complete
  - ✅ §6.37: 22 exports de BoolAlg.FiniteCofinite
  - ✅ §7.2: BoolAlg.FiniteCofinite y BoolAlg.Complete añadidos a archivos completos

- **Nuevo módulo Peano.FiniteSequencesBridge.lean — Puente DList ↔ ZFC y TFA nativo**:
  - ✅ `nth (f n i : U) : U` — i-ésimo elemento de secuencia finita ZFC
  - ✅ `dlistToSeq (xs : DList ℕ₀) : U` — conversión DList Peano → secuencia finita ZFC
  - ✅ `dlistLen (xs : DList ℕ₀) : U` — longitud de DList como natural ZFC
  - ✅ `isPrimeSeq (f n : U) : Prop` — predicado de secuencia de primos
  - ✅ 15 teoremas públicos en 7 secciones: nth (5), seqProd recursion (3), seqProd extensionality (1), DList→ZFC bridge (4), seqProd correspondence (1), isPrimeSeq (1), TFA native (2)
  - ✅ `tfa_exists_native` — ∀ n ≥ 2, ∃ secuencia ZFC de primos cuyo producto es n
  - ✅ `tfa_unique_native` — unicidad de la factorización prima ZFC-nativa
  - ✅ Namespace `ZFC.Peano.FiniteSequencesBridge` (exportado a `ZFC`, 23 exports)
  - ✅ Build limpio; 41/41 módulos compilados correctamente (0 sorry, 0 errores)

- **REFERENCE.md — Proyección completa de Peano.FiniteSequencesBridge.lean**:
  - ✅ §1.1: 1 fila añadida (Peano.FiniteSequencesBridge)
  - ✅ §3.39: 4 definiciones (nth, dlistToSeq, dlistLen, isPrimeSeq)
  - ✅ §4.35: 15 teoremas en 7 secciones
  - ✅ §6.36: 23 exports
  - ✅ §7.2: Añadido a archivos completamente proyectados

### Añadido (2026-03-30)

- **Nuevo módulo Peano.FiniteSequencesArith.lean — Aritmética de secuencias finitas en ZFC**:
  - ✅ `sumStepFn (f : U) : U` — función de paso para sumación: ⟨k, v⟩ ↦ v + f(k)
  - ✅ `seqSumFn`, `seqSum (f n : U) : U` — Σ_{i<n} f(i) vía recursión ZFC
  - ✅ `prodStepFn (f : U) : U` — función de paso para producto: ⟨k, v⟩ ↦ v · f(k)
  - ✅ `seqProdFn`, `seqProd (f n : U) : U` — Π_{i<n} f(i) vía recursión ZFC
  - ✅ `familyProduct (F n : U) : U` — producto cartesiano Π_{i<n} F(i)
  - ✅ 18 teoremas públicos en 6 secciones: sumStepFn (3), seqSum (5), prodStepFn (3), seqProd (5), familyProduct (3), cardinalidad (2)
  - ✅ `card_product_two` — |A ×ₛ B| = |A| · |B| para conjuntos finitos
  - ✅ `card_familyProduct` — |Π_{i<n} F(i)| = Π_{i<n} |F(i)| (inducción ZFC completa)
  - ✅ 21 lemas privados auxiliares (no exportados)
  - ✅ Namespace `ZFC.Peano.FiniteSequencesArith` (exportado a `ZFC`, 33 exports)
  - ✅ Build limpio; 40/40 módulos compilados correctamente (0 sorry, 0 errores)

- **REFERENCE.md — Proyección completa de Peano.FiniteSequencesArith.lean**:
  - ✅ §1.1: 1 fila añadida (Peano.FiniteSequencesArith)
  - ✅ §3.38: 7 definiciones (sumStepFn, seqSumFn, seqSum, prodStepFn, seqProdFn, seqProd, familyProduct)
  - ✅ §4.34: 18 teoremas en 6 secciones
  - ✅ §6.35: 33 exports
  - ✅ §7.2: Añadido a archivos completamente proyectados

### Añadido (2026-03-29)

- **Nuevo módulo SetOps.FiniteSets.lean — Conjuntos finitos en ZFC**:
  - ✅ `isFiniteSet (A : U) : Prop` — predicado: ∃ n ∈ ω, A ≃ₛ n
  - ✅ Infraestructura de biyecciones (identidad, inversa, composición):
    - `id_is_function`, `id_is_injective`, `id_is_surjective`, `id_is_bijection`
    - `inverse_pair_iff`, `bijection_inverse_is_function`, `bijection_inverse_injective`, `bijection_inverse_surjective`, `bijection_inverse_is_bijection`
    - `comp_injective`, `comp_surjective`, `comp_bijection`
  - ✅ Equipotencia como relación de equivalencia: `equipotent_refl`, `equipotent_symm`, `equipotent_trans`
  - ✅ Propiedades de finitud: `empty_is_finite`, `nat_is_finite`, `singleton_is_finite`, `finite_equipotent`, `finite_union_singleton`
  - ✅ Namespace `ZFC.SetOps.FiniteSets` (exportado a `ZFC`, 22 exports)
  - ✅ Build limpio; 39/39 módulos compilados correctamente (0 sorry, 0 errores)

- **REFERENCE.md — Proyección completa de SetOps.FiniteSets.lean**:
  - ✅ §1.1: 1 fila añadida (SetOps.FiniteSets)
  - ✅ §3.37: 1 definición (isFiniteSet)
  - ✅ §4.33: 21 teoremas en 7 secciones
  - ✅ §6.34: 22 exports
  - ✅ §7.2: Añadido a archivos completamente proyectados

### Añadido (2026-03-27 10:00)

- **Nuevo módulo Peano.FiniteSequences.lean — Secuencias finitas en ZFC** (Patrón directo, sin bridge):
  - ✅ `isFinSeq (f n A : U) : Prop` — predicado: n ∈ ω ∧ f : n → A
  - ✅ `FinSeqSet (n A : U) : U` — conjunto de todas las n-secuencias en A (noncomputable)
  - ✅ `appendElem (f n a : U) : U` — extensión f ∪ {⟨n, a⟩} (noncomputable)
  - ✅ 8 teoremas del predicado central: `isFinSeq_in_Omega`, `isFinSeq_is_function`, `isFinSeq_domain`, `isFinSeq_subset`, `isFinSeq_unique_length`, `isFinSeq_apply_mem`, `isFinSeq_pair_mem`, `isFinSeq_ext`
  - ✅ 2 teoremas de FinSeqSet: `mem_FinSeqSet_iff`, `isFinSeq_mem_FinSeqSet`
  - ✅ 3 teoremas de secuencia vacía: `isFinSeq_empty`, `isFinSeq_zero_unique`, `FinSeqSet_zero`
  - ✅ 5 teoremas de appendElem: `appendElem_is_specified`, `isFinSeq_appendElem`, `appendElem_apply_last`, `appendElem_apply_prev`, `appendElem_inj`
  - ✅ 1 teorema de descomposición: `isFinSeq_restriction`
  - ✅ Namespace `ZFC.Peano.FiniteSequences` (sin export a `ZFC`)
  - ✅ Build limpio; 38/38 módulos compilados correctamente (0 sorry, 0 errores)

- **REFERENCE.md — Proyección completa de Peano.FiniteSequences.lean**:
  - ✅ §1.1: 1 fila añadida (Peano.FiniteSequences)
  - ✅ §3.36: 3 definiciones (isFinSeq, FinSeqSet, appendElem)
  - ✅ §4.32: 15 teoremas en 5 secciones
  - ✅ §6.33: documentación de namespace (sin exports)
  - ✅ §7.2: 1 entrada añadida a archivos completos

### Añadido (2026-03-26 14:00)

- **Nuevo módulo Nat.MaxMin.lean — Máximo y mínimo en ω** (Patrón B, bridge-only):
  - ✅ `maxOf (n m : U) : U` — máximo vía `fromPeano (Peano.MaxMin.max (toPeano n _) (toPeano m _))`
  - ✅ `minOf (n m : U) : U` — mínimo vía `fromPeano (Peano.MaxMin.min (toPeano n _) (toPeano m _))`
  - ✅ `fromPeano_max`, `fromPeano_min` — teoremas puente
  - ✅ 27 teoremas: idempotencia, conmutatividad, asociatividad, identidad/aniquilador con ∅, cotas sup/inf, caracterización vía ≤, max/min es uno de los argumentos, max=min⇔iguales
  - ✅ 31 exports al namespace `ZFC`
  - ✅ Build limpio; 37/37 módulos compilados correctamente

- **Nuevo módulo Nat.NewtonBinom.lean — Teorema binomial de Newton en ω** (Patrón B, bridge-only, 4 argumentos):
  - ✅ `binomTermOf (a b n k : U) : U` — C(n,k)·a^k·b^(n−k) vía `fromPeano (Peano.NewtonBinom.binomTerm ...)`
  - ✅ `fromPeano_binomTerm` — teorema puente con 4 argumentos (`congr 1` ×4)
  - ✅ 9 teoremas: valores concretos (k=0, k=n), expansión, separación de potencias n^(m+k)=n^m·n^k, Newton's binomial theorem (Peano→ZFC), Σ C(n,k)=2^n (Peano→ZFC), comparación de crecimiento existencial
  - ✅ **Decisión de diseño**: `finSum` (función de orden superior) no se transporta a ZFC; `newton_binom_peano` y `sum_binom_eq_pow_two_peano` usan tipos Peano con resultado aplicado vía `fromPeano`
  - ✅ 12 exports al namespace `ZFC`

- **Nuevo módulo Nat.WellFounded.lean — Buen fundamento y buena ordenación en ω** (Patrón B, bridge-only):
  - ✅ `acc_lt_Omega (n : U)` — accesibilidad bajo ∈ restringido a ω, delegando a `nat_mem_wf.apply n`
  - ✅ `well_ordering_Omega (P : U → Prop)` — principio de buena ordenación con unicidad: todo subconjunto no vacío de ω tiene un mínimo único, transportado desde `Peano.WellFounded.well_ordering_principle`
  - ✅ `well_ordering_Omega_exists` — forma simplificada sin unicidad
  - ✅ 3 exports al namespace `ZFC`

- **REFERENCE.md — Proyección completa de 3 módulos**:
  - ✅ §1.1: 3 filas añadidas (MaxMin, NewtonBinom, WellFounded)
  - ✅ §3.33 (MaxMin: 2 def), §3.34 (NewtonBinom: 1 def), §3.35 (WellFounded: 0 def)
  - ✅ §4.29 (MaxMin: 29 teoremas en 10 secciones), §4.30 (NewtonBinom: 10 teoremas en 8 secciones), §4.31 (WellFounded: 3 teoremas en 2 secciones)
  - ✅ §6.30 (31 exports), §6.31 (12 exports), §6.32 (3 exports)
  - ✅ §7.2: 3 entradas añadidas a archivos completos

### Añadido (2026-03-24 10:00)

- **Nuevo módulo Nat.Factorial.lean — Factorial en ω** (Patrón B, bridge-only):
  - ✅ `factorial (n : U) : U` — factorial de naturales de von Neumann via `fromPeano (Peano.Factorial.factorial (toPeano n hn))`
  - ✅ `fromPeano_factorial` — teorema puente con `Peano.Factorial.factorial`
  - ✅ 10 teoremas: `factorial_zero`, `factorial_one`, `factorial_two`, `factorial_succ`, `factorial_pos`, `factorial_ne_zero`, `factorial_ge_one`, `factorial_le_succ`, `factorial_le_mono`, `factorial_in_Omega`
  - ✅ Build limpio; 31/31 módulos compilados correctamente

- **REFERENCE.md — Proyección y corrección completa de 7 módulos**:
  - ✅ `BoolAlg.Atomic.lean`: completada proyección parcial; §3.12 (4 def), §4.7 (14 teoremas), §6.25 (19 exports); estado 🔶 Parcial → ✅ Completo
  - ✅ `BoolAlg.GenDeMorgan.lean`: corregida documentación incorrecta — §3.16 (1 def real vs. 3 ficticias anteriores), §4.11 (10 teoremas reales vs. 8 ficticios), §6.8 (8 exports reales)
  - ✅ `BoolAlg.GenDistributive.lean`: corregida documentación incorrecta — §3.17 (2 def reales vs. 5 ficticias anteriores), §4.12 (10 teoremas reales), §6.9 (12 exports reales)
  - ✅ `Induction.Recursion.lean`: expandido §6.17 con todos los exports de variantes step e CoV (anteriormente incompleto: ~15 entradas faltaban)
  - ✅ `SetOps.SetOrder.lean`, `SetOps.SetStrictOrder.lean`, `PeanoImport.lean`: verificados correctamente proyectados

### Añadido (2026-03-22 12:00)

- **Nuevo módulo Nat.Pow.lean — Potenciación en ω** (Patrón RecursiveFn):
  - ✅ `powFn (m : U) (hm : m ∈ ω) : U` — función de potenciación vía `RecursiveFn ω (σ ∅) (mulFn m hm)`
  - ✅ `pow (m n : U) : U` — potencia de naturales de von Neumann
  - ✅ `fromPeano_pow` — teorema puente con `Peano.Pow.pow`
  - ✅ 13 teoremas: `pow_zero`, `pow_succ`, `pow_eq`, `pow_in_Omega`, `zero_pow_Omega`, `one_pow_Omega`, `pow_one_Omega`, `pow_ne_zero_Omega`, `pow_two_Omega`, `pow_add_eq_mul_pow_Omega`, `mul_pow_Omega`, `pow_pow_eq_pow_mul_Omega`, `powFn_is_function`
  - ✅ 18 exports totales; build limpio

- **Nuevo módulo Nat.Arith.lean — Divisibilidad, GCD, LCM, Bézout** (Patrón RecursiveFn + Patrón B):
  - ✅ `divides (m n : U) : Prop` — predicado ZFC directo: ∃ k ∈ ω, n = m*k
  - ✅ `div (m n : U) : U` — cociente euclídeo nativo ZFC via `divMod_stepFn` (función paso en ω×ω)
  - ✅ `mod (m n : U) : U` — resto euclídeo nativo ZFC (mismo RecursiveFn)
  - ✅ `div_eq_divOf`/`mod_eq_modOf` — equivalencia con Pattern B de Nat.Div
  - ✅ `gcdOf (m n : U) : U` — MCD Pattern B via `Peano.Arith.gcd`
  - ✅ `lcmOf (m n : U) : U` — MCM Pattern B via `Peano.Arith.lcm`
  - ✅ `bezout_natform_Omega` — Bézout en forma substractiva: ∃ a b, a*m − b*n = gcd(m,n) ∨ a*n − b*m = gcd(m,n)
  - ✅ 13 propiedades de divisibilidad, 8 propiedades de gcd/lcm, 14 propiedades de div/mod nativo
  - ✅ 43 exports totales; build limpio (tras fix de ambigüedad σ con Nat.Basic.successor)

- **REFERENCE.md**: actualización completa
  - ✅ §1.1: Nat.Pow.lean y Nat.Arith.lean añadidos a tabla
  - ✅ §3.27-§3.28: nuevas secciones de definiciones
  - ✅ §4.23-§4.24: nuevas secciones de teoremas
  - ✅ §6.23-§6.24: nuevas secciones de exports
  - ✅ §7.2: lista de archivos completos actualizada

### Añadido (2026-03-21 12:00)

- **Nuevo módulo Nat.Sub.lean — Sustracción saturada en ω** (Patrón RecursiveFn):
  - ✅ `predecessorFn : U` — función predecesor para Recursión
  - ✅ `subFn (m : U) (hm : m ∈ ω) : U` — función de sustracción vía `RecursiveFn`
  - ✅ `sub (m n : U) : U` — sustracción saturada (monus) de naturales de von Neumann
  - ✅ `fromPeano_sub` — teorema puente con `Peano.Sub.sub`
  - ✅ 13 teoremas algebraicos

- **Nuevo módulo Nat.Div.lean — División euclídea en ω** (Patrón B):
  - ✅ `divOf (m n : U) : U` — cociente via isomorfismo
  - ✅ `modOf (m n : U) : U` — resto via isomorfismo
  - ✅ `divMod_eq_Omega`, `mod_lt_divisor_Omega`, `div_of_lt_Omega`, `mod_of_lt_Omega`, `div_le_self_Omega`

### Añadido (2026-03-08 14:00)

- **Nuevo módulo Nat.Add.lean — Suma en ω**:
  - ✅ `successorFn : U → U → U` — función sucesor para Recursión (no computable, proposicional)
  - ✅ `addFn (m : U) (hm : m ∈ ω) : U` — función de suma vía `RecursiveFn`
  - ✅ `add (m n : U) : U` — suma de naturales de von Neumann
  - ✅ `fromPeano_add` — teorema puente: `fromPeano (p + q) = add (fromPeano p) (fromPeano q)`
  - ✅ 16 teoremas algebraicos: `add_zero_Omega`, `zero_add_Omega`, `add_succ_Omega`, `succ_add_Omega`, `add_comm_Omega`, `add_assoc_Omega`, `add_left_cancel_Omega`, `add_right_cancel_Omega`, `add_pos_left_Omega`, `add_pos_right_Omega`, `le_then_exists_add_Omega`, `add_lt_of_lt_Omega`, `add_le_left_Omega`, `add_le_right_Omega`, `lt_add_of_pos_right_Omega`, `lt_add_of_pos_left_Omega`
  - ✅ Build: 28/28 módulos compilados correctamente

- **Nuevo módulo Nat.Mul.lean — Multiplicación en ω**:
  - ✅ `mulFn (m : U) (hm : m ∈ ω) : U` — función de multiplicación vía `RecursiveFn`
  - ✅ `mul (m n : U) : U` — multiplicación de naturales de von Neumann
  - ✅ `fromPeano_mul` — teorema puente: `fromPeano (p * q) = mul (fromPeano p) (fromPeano q)`
  - ✅ 13 teoremas algebraicos: `mul_zero_Omega`, `zero_mul_Omega`, `mul_succ`, `mul_comm_Omega`, `succ_mul_Omega`, `mul_one_Omega`, `one_mul_Omega`, `mul_assoc_Omega`, `mul_ldistr_Omega`, `mul_rdistr_Omega`, `mul_in_Omega`, `mul_lt_left_Omega`, `mul_le_left_Omega`
  - ✅ Build: 28/28 módulos compilados correctamente

- **PeanoImport.lean — Transporte de recursión con paso y puentes de orden** (extensión):
  - ✅ `recursion_transport_step` — transporta `RecursionTheoremWithStep` de ZFC a Peano
  - ✅ `recursion_transport_step_inv` — transporta `RecursionTheoremWithStep` de Peano a ZFC
  - ✅ `fromPeano_lt_iff` — `Lt p q ↔ (ΠZ p : U) ∈ (ΠZ q : U)`
  - ✅ `fromPeano_le_iff` — `Le p q ↔ (ΠZ p : U) ⊆ (ΠZ q : U)`
  - ✅ `succ_mem_succ_iff` — `σ m ∈ σ n ↔ m ∈ n` (para naturales en ω)

- **Cardinality.lean — 0 sorry confirmado**:
  - ✅ CSB_bijection_is_function completamente demostrado (sin sorry)
  - ✅ Estado actualizado en REFERENCE.md: 🔶 Parcial → ✅ Completo

- **REFERENCE.md**: actualización completa
  - ✅ §1.1: Nat.Add.lean y Nat.Mul.lean añadidos
  - ✅ §3.22: nueva sección Nat.Add (3 definiciones)
  - ✅ §3.23: nueva sección Nat.Mul (2 definiciones)
  - ✅ §4.17: PeanoImport ampliado (+5 teoremas)
  - ✅ §4.18: nueva sección Nat.Add (16 teoremas)
  - ✅ §4.19: nueva sección Nat.Mul (13 teoremas)
  - ✅ §5.11-5.12: notaciones ΠZ/ZΠ, add, mul
  - ✅ §6.15-6.17: exports PeanoImport, Nat.Add, Nat.Mul
  - ✅ §7.2: Cardinality movido de 7.3 a 7.2

- **ZfcSetTheory.lean** (módulo raíz): `import ZfcSetTheory.Nat.Mul` añadido

- **AIDER-AI-GUIDE.md**: actualizado con requisitos mejorados del proyecto PEANO
  - ✅ §0: documentación técnica (no usuario final)
  - ✅ §4.1-4.4: computabilidad, buena fundación, notación en definiciones
  - ✅ §11-14: definición de "proyectar", criterio de relevancia, exportabilidad
  - ✅ §20: sistema de bloqueo de archivos
  - ✅ Sección de versiones resumidas de CHANGELOG.md

### Añadido (2026-03-04 12:00)

- **Nuevo módulo PeanoImport.lean — Isomorfismo Von Neumann ↔ Peano**:
  - ✅ `fromPeano : Peano.ℕ₀ → U` — conversión estructural por recursión sobre `Peano.ℕ₀`
  - ✅ `toPeano : (n : U) → isNat n → Peano.ℕ₀` — inversión via `Classical.choose`
  - ✅ `fromPeano_is_nat` — `fromPeano` mapea a naturales de Von Neumann
  - ✅ `fromPeano_injective` — inyectividad de `fromPeano`
  - ✅ `fromPeano_surjective` — sobreyectividad (demostrada por inducción fuerte sobre ω)
  - ✅ `fromPeano_toPeano`, `toPeano_fromPeano` — inversas mutuas
  - ✅ `toPeano_injective`, `toPeano_surjective` — biyección completa
  - ✅ Dependencia externa `peanolib` añadida en `lakefile.lean`
  - ✅ Build: 28/28 módulos compilados correctamente (incluye peanolib)

- **Infinity.lean — `nat_mem_wf` demostrado sin sorry**:
  - ✅ `nat_mem_wf : WellFounded (fun a b : U => a ∈ ω ∧ b ∈ ω ∧ a ∈ b)` completamente probado
  - Estrategia: elementos fuera de ω son vacuosamente accesibles; elementos en ω por inducción fuerte usando `S = SpecSet ω (Acc R)`
  - ✅ Añadido a la lista de exports de `Infinity.lean`

- **Nat.Basic.lean — exports de predecessor ampliados**:
  - ✅ `predecessor`, `predecessor_of_successor`, `predecessor_is_nat`, `predecessor_mem` ahora en la lista de exports pública

- **Documentación actualizada (REFERENCE.md)**:
  - ✅ §1.1: PeanoImport.lean añadido a la tabla de módulos
  - ✅ §3.13: definición `predecessor` documentada
  - ✅ §3.21: nueva sección PeanoImport.lean (2 definiciones)
  - ✅ §4.9: `nat_mem_wf` documentado con nota de implementación
  - ✅ §4.17: nueva sección PeanoImport.lean (7 teoremas)

### Actualizado (2026-02-12 18:45)

- **Documentación Completa - Proyección de Nat.Basic.lean y Actualización de Markdown**:
  - ✅ Nat.Basic.lean completamente proyectado en REFERENCE.md (13 definiciones + 36 teoremas + 47 exportaciones)
  - ✅ Todos los archivos markdown del proyecto actualizados con timestamps ISO 8601 (YYYY-MM-DD HH:MM)
  - ✅ Información de autoría agregada a todos los archivos de documentación
  - ✅ Cumplimiento total con AIDER-AI-GUIDE.md (requisitos 10-11: timestamps y autoría)
  - ✅ REFERENCE.md: 5485 líneas de documentación técnica completa
  - ✅ Proyecto 100% documentado: Toda la información técnica disponible en REFERENCE.md sin necesidad de cargar archivos .lean

### Corregido (2026-02-12 17:35)

- **Recursion.lean - Todos los errores de tipo resueltos**:
  - Error 1 (líneas 148, 182, 310, 391): Reemplazado `Eq_of_OrderedPairs_given_projections` con `isOrderedPair_by_construction` para manejo correcto de proposiciones
  - Error 2 (líneas 224, 269, 292): Corregido uso de `subset_of_mem_successor` por `mem_successor_of_mem` con argumentos apropiados
  - Error 3 (líneas 322, 400): Reemplazado `mem_successor_iff` no existente con `successor_is_specified`
  - Error de tipo en ω: Corregido a `(ω : U)` para alineación correcta de tipos
  - Añadida sección de exportaciones: `function_domain_eq`, `isComputation`, `computation_uniqueness`
  - **Recursion.lean ahora compila sin errores de tipo** ✅
  - **Proyecto 100% completo: 0 `sorry` statements, 0 errores de compilación** ✅

### Corregido (2026-02-12 14:35)

- **Cardinality.lean - CSB_bijection_is_function reparado**:
  - Corregidas proyecciones en función `hg.2` sobre función universal
  - Arregladas aplicaciones de función `g` a valores en `B`
  - Utilización correcta de `ExistsUnique.unique` para destructuración
  - **CSB_bijection_is_function ahora compila sin errores** ✅
  - **Proyecto completo: 24/24 módulos compilados exitosamente** ✅

### Corregido (2026-02-12 14:52)

- **Functions.lean - Errores de compilación resueltos**:
  - Agregada definición faltante de `isSingleValued` (línea 62)
  - Corregida prueba de `injective_inverse_single_valued` con `simp only` específico
  - Actualizado export para incluir `isSingleValued`
  - **Functions.lean ahora compila sin errores** ✅

- **Relations.lean - InverseRel mejorado**:
  - Reordenadas definiciones: `domain`, `range`, `imag` ahora antes de `InverseRel`
  - Cambiada definición de `InverseRel` de `𝒫 (𝒫 (⋃(⋃ R)))` a `range R ×ₛ domain R`
  - Definición más precisa y coherente con `IdRel`
  - Resuelve error de tipo en `inverse_is_specified`

### Añadido (2026-02-11 15:30)

- **Infraestructura de Existencia Única**:
  - `ExistsUnique` personalizado en `Prelim.lean` (52 líneas)
  - Notación `∃! x, P` compatible con paréntesis y tipos explícitos
  - API completa: `.intro`, `.exists`, `.choose`, `.choose_spec`, `.unique`
  - Resuelve incompatibilidades con la implementación estándar de Lean 4

- **Domain y Range para Relaciones** en `SetOps.Relations.lean`:
  - `domain R` - Dominio correcto usando `⋃(⋃ R)` en lugar de `fst R`
  - `range R` - Rango correcto usando `⋃(⋃ R)` en lugar de `snd R`
  - `imag R` - Alias para `range`
  - `mem_domain` - Caracterización completa (sin `sorry`)
  - `mem_range` - Caracterización completa (sin `sorry`)
  - `mem_imag` - Caracterización completa (sin `sorry`)
  - Teoremas auxiliares: `pair_mem_implies_fst_in_domain`, etc.

### Cambiado

- **Actualización de isFunctionFromTo**:
  - Cambio de estructura ternaria a binaria: `isFunctionFromTo f A B` → `isFunctionFromTo f A`
  - Nueva definición: `(f ⊆ A ×ₛ B) ∧ (∀ x ∈ A, ∃! y, ⟨x,y⟩ ∈ f)`
  - Actualizadas todas las referencias en `Cardinal.Basic.lean`

- **Reorganización de Relations.lean**:
  - Definiciones correctas (`domain`, `range`) primero
  - Sección "Legacy Domain and Range" al final con `sorry` documentados
  - Explicaciones claras sobre problemas estructurales de versiones legacy

### Corregido

- 7 teoremas usando `∃!` actualizados a `ExistsUnique`:
  - `ExistsUniqueEmptySet` (Existence.lean)
  - `SpecificationUnique`, `BinInterUniqueSet`, `DifferenceUniqueSet` (Specification.lean)
  - `PairingUniqueSet` (Pairing.lean)
  - `UnionExistsUnique` (Union.lean)
  - `PowerSetExistsUnique` (PowerSet.lean)

- 3 `sorry` resueltos en Functions.lean:
  - `apply_mem` - Completamente probado
  - `apply_eq` - Completamente probado
  - `apply_id` - Completamente probado

### Documentación

- **CURRENT-STATUS-PROJECT.md**: Complete project status document
  - Executive summary with statistics
  - Recent achievements details
  - Status by file (24/25 without `sorry`, 1 with `sorry`)
  - Analysis of pending `sorry` in Recursion.lean
  - Architecture and dependency hierarchy
  - Decisiones de diseño importantes
  - Próximos pasos sugeridos con estimaciones de tiempo
  - Métricas de calidad y cobertura

### En desarrollo

- Resolver `inverse_is_specified` en Functions.lean (1 `sorry`)
- Resolver sorry en Cardinality.lean - teorema CSB (1 `sorry`)
- Completar paso inductivo en Recursion.lean (1 `sorry`)
- N-tuplas

---

## [0.8.0] - 2026-02-07 10:00

### Añadido

- **BoolAlg.PowerSetAlgebra.lean**: Álgebra del conjunto potencia
  - `Complement A X` - Complemento de X respecto a A (notación: `X^∁[ A ]`)
  - `ComplementFamily A F` - Familia de complementos
  - `double_complement` - (X^∁[A])^∁[A] = X (si X ⊆ A)
  - `complement_empty` - ∅^∁[A] = A
  - `complement_full` - A^∁[A] = ∅
  - De Morgan para familias: `DeMorgan_union_family`, `DeMorgan_inter_family`

- **BoolAlg.GenDeMorgan.lean**: Leyes de De Morgan generalizadas
  - `complement_union_eq_inter_complement` - A \ ⋃ F = ⋂ (ComplementFamily A F)
  - `complement_inter_eq_union_complement` - A \ ⋂ F = ⋃ (ComplementFamily A F)
  - Versiones duales e inversas

- **BoolAlg.GenDistributive.lean**: Leyes distributivas generalizadas
  - `DistribSet X F op` - Conjunto imagen { op(X, Y) | Y ∈ F }
  - `inter_union_distrib` - X ∩ (⋃ F) = ⋃ { X ∩ Y | Y ∈ F }
  - `union_inter_distrib` - X ∪ (⋂ F) = ⋂ { X ∪ Y | Y ∈ F }
  - Versiones conmutativas

- **BoolAlg.Atomic.lean**: Álgebra de Boole atómica
  - `isAtom A X` - X es un átomo en 𝒫(A)
  - `Atoms A` - Conjunto de todos los átomos
  - `isAtomic A` - 𝒫(A) es atómica
  - `singleton_is_atom` - {x} es átomo cuando x ∈ A
  - `atom_is_singleton` - Todo átomo es un singleton
  - `atom_iff_singleton` - Caracterización completa
  - `PowerSet_is_atomic` - 𝒫(A) es un álgebra de Boole atómica
  - `element_is_union_of_atoms` - Todo elemento es unión de átomos

---

## [0.7.0] - 2026-02-07 09:00

### Añadido

- **Relations.lean**: Nuevo módulo completo de relaciones
  - Propiedades: `isReflexiveOn`, `isSymmetricOn`, `isTransitiveOn`, etc.
  - Tipos: equivalencia, preorden, orden parcial, orden lineal, orden estricto
  - Relaciones bien fundadas y buenos órdenes
  - Construcciones: `EqClass`, `QuotientSet`, `IdRel`, `InverseRel`
  - ~20 teoremas sobre propiedades de relaciones y clases de equivalencia

### Cambiado

- **SetOps.CartesianProduct.lean**: Renombrado namespace `CartesianProductAxiom` → `SetOps.CartesianProduct`
  (no es un axioma, es una construcción derivada)

---

## [0.6.0] - 2026-02-07 08:00

### Añadido

- **OrderedPair.lean**: Nuevo módulo con extensiones del par ordenado
  - `OrderedPair_eq_of`: (a = c ∧ b = d) → ⟨a, b⟩ = ⟨c, d⟩
  - `OrderedPair_eq_iff`: ⟨a, b⟩ = ⟨c, d⟩ ↔ (a = c ∧ b = d)
  - `OrderedPair_in_PowerSet`: Si a ∈ A y b ∈ B, entonces ⟨a, b⟩ ∈ 𝒫(𝒫(A ∪ B))

### Cambiado

- Refactorizado `ParOrdenado.lean` → `OrderedPair.lean`
- Eliminada duplicación de código con `Pairing.lean`
- Actualizada documentación en README.md, DEPENDENCIES.md

---

## [0.5.0] - 2026-02-06 16:00

### Añadido

- **Potencia.lean**: Axioma del Conjunto Potencia (PowerSet)
  - `PowerSet`: Axioma ∀A ∃P ∀x (x ∈ P ↔ x ⊆ A)
  - `PowerSetOf (𝒫)`: Definición del conjunto potencia
  - `PowerSet_is_specified`: x ∈ 𝒫(A) ↔ x ⊆ A
  - `empty_mem_PowerSet`: ∅ ∈ 𝒫(A)
  - `self_mem_PowerSet`: A ∈ 𝒫(A)
  - `PowerSet_nonempty`: 𝒫(A) ≠ ∅
  - `PowerSet_empty`: 𝒫(∅) = {∅}
  - `PowerSet_mono`: A ⊆ B → 𝒫(A) ⊆ 𝒫(B)
  - `PowerSet_inter`: 𝒫(A ∩ B) = 𝒫(A) ∩ 𝒫(B)
  - `Union_PowerSet`: ⋃(𝒫(A)) = A

### Mejorado

- **Union.lean**: Nuevos teoremas
  - `BinUnion_assoc`: Asociatividad de unión binaria
  - `BinUnion_absorb_inter`: Ley de absorción

---

## [0.4.0] - 2026-02-05 14:30

### Añadido

- **SetOps.SetStrictOrder.lean**: Orden estricto completo
  - `strict_order_irreflexive`: ¬(A ⊂ A)
  - `strict_order_asymmetric`: A ⊂ B → ¬(B ⊂ A)
  - `strict_order_transitive`: A ⊂ B → B ⊂ C → A ⊂ C
  - `partial_to_strict_order`: Conversión de orden parcial a estricto

- **SetOps.SetOrder.lean**: Estructura de retículo
  - `isUpperBound`, `isLowerBound`, `isSupremum`, `isInfimum`
  - `inter_is_glb`: A ∩ B es el ínfimo
  - `union_is_lub`: A ∪ B es el supremo
  - Monotonía bilateral de ∩ y ∪

### Mejorado

- **BoolAlg.Basic.lean**: Nuevos teoremas de monotonía y equivalencias

---

## [0.3.0] - 2026-02-04 11:00

### Añadido

- **BoolAlg.Basic.lean**: Teoremas de álgebra booleana
  - Conmutatividad de ∪ y ∩
  - Idempotencia de ∪ y ∩
  - Identidad con ∅
  - Transitividad y reflexividad de ⊆
  - Monotonía de ∪ y ∩
  - `Subseteq_inter_eq`: A ⊆ B ↔ A ∩ B = A

- **Union.lean**: Operaciones binarias
  - `BinUnion`: Unión binaria A ∪ B
  - `SymDiff`: Diferencia simétrica A △ B
  - Teoremas: conmutatividad, idempotencia, identidades

---

## [0.2.0] - 2026-02-03 15:45

### Añadido

- **Pairing.lean**: Axioma de Par completo
  - `PairSet {a, b}`: Par no ordenado
  - `Singleton {a}`: Singleton
  - `OrderedPair ⟨a, b⟩`: Par ordenado (Kuratowski)
  - `fst`, `snd`: Proyecciones
  - `Eq_of_OrderedPairs_given_projections`: Inyectividad
  - Relaciones: reflexiva, simétrica, transitiva, equivalencia
  - Funciones: total, inyectiva, suryectiva, biyectiva

- **Union.lean**: Axioma de Unión
  - `UnionSet (⋃)`: Unión familiar
  - Teoremas de vaciedad y unicidad

---

## [0.1.0] - 2026-02-02 10:00

### Añadido

- **Prelim.lean**: Fundamentos
  - `ExistsUnique`: Predicado de existencia y unicidad
  - Constructor, proyección y testigo

- **Extension.lean**: Axioma de Extensionalidad
  - `ExtSet`: Dos conjuntos son iguales si tienen los mismos elementos
  - `subseteq (⊆)`, `subset (⊂)`, `disjoint (⟂)`
  - Propiedades de orden parcial

- **Existence.lean**: Axioma de Existencia
  - `EmptySet (∅)`: Conjunto vacío
  - Unicidad y propiedades básicas

- **Specification.lean**: Axioma de Especificación
  - `SpecSet`: Construcción por comprensión
  - `BinInter (∩)`: Intersección binaria
  - `Difference (\)`: Diferencia de conjuntos
  - Conmutatividad, asociatividad, idempotencia

---

## Convenciones de Versionado

- **MAJOR**: Cambios incompatibles en la API o nuevo axioma ZFC
- **MINOR**: Nueva funcionalidad compatible hacia atrás
- **PATCH**: Correcciones de errores compatibles hacia atrás

## Enlaces

- [Repositorio](https://github.com/julian1c2a/ZfcSetTheory)
- [Issues](https://github.com/julian1c2a/ZfcSetTheory/issues)
