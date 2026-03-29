# Changelog

**Última actualización:** 2026-03-27 10:00
**Autor**: Julián Calderón Almendros

Todos los cambios notables de este proyecto serán documentados en este archivo.

El formato está basado en [Keep a Changelog](https://keepachangelog.com/es-ES/1.0.0/),
y este proyecto adhiere a [Semantic Versioning](https://semver.org/spec/v2.0.0.html).

## [Unreleased]

### Añadido (2026-03-27 10:00)

- **Nuevo módulo FiniteSequences.lean — Secuencias finitas en ZFC** (Patrón directo, sin bridge):
  - ✅ `isFinSeq (f n A : U) : Prop` — predicado: n ∈ ω ∧ f : n → A
  - ✅ `FinSeqSet (n A : U) : U` — conjunto de todas las n-secuencias en A (noncomputable)
  - ✅ `appendElem (f n a : U) : U` — extensión f ∪ {⟨n, a⟩} (noncomputable)
  - ✅ 8 teoremas del predicado central: `isFinSeq_in_Omega`, `isFinSeq_is_function`, `isFinSeq_domain`, `isFinSeq_subset`, `isFinSeq_unique_length`, `isFinSeq_apply_mem`, `isFinSeq_pair_mem`, `isFinSeq_ext`
  - ✅ 2 teoremas de FinSeqSet: `mem_FinSeqSet_iff`, `isFinSeq_mem_FinSeqSet`
  - ✅ 3 teoremas de secuencia vacía: `isFinSeq_empty`, `isFinSeq_zero_unique`, `FinSeqSet_zero`
  - ✅ 5 teoremas de appendElem: `appendElem_is_specified`, `isFinSeq_appendElem`, `appendElem_apply_last`, `appendElem_apply_prev`, `appendElem_inj`
  - ✅ 1 teorema de descomposición: `isFinSeq_restriction`
  - ✅ Namespace `SetUniverse.FiniteSequences` (sin export a `SetUniverse`)
  - ✅ Build limpio; 38/38 módulos compilados correctamente (0 sorry, 0 errores)

- **REFERENCE.md — Proyección completa de FiniteSequences.lean**:
  - ✅ §1.1: 1 fila añadida (FiniteSequences)
  - ✅ §3.36: 3 definiciones (isFinSeq, FinSeqSet, appendElem)
  - ✅ §4.32: 15 teoremas en 5 secciones
  - ✅ §6.33: documentación de namespace (sin exports)
  - ✅ §7.2: 1 entrada añadida a archivos completos

### Añadido (2026-03-26 14:00)

- **Nuevo módulo NaturalNumbersMaxMin.lean — Máximo y mínimo en ω** (Patrón B, bridge-only):
  - ✅ `maxOf (n m : U) : U` — máximo vía `fromPeano (Peano.MaxMin.max (toPeano n _) (toPeano m _))`
  - ✅ `minOf (n m : U) : U` — mínimo vía `fromPeano (Peano.MaxMin.min (toPeano n _) (toPeano m _))`
  - ✅ `fromPeano_max`, `fromPeano_min` — teoremas puente
  - ✅ 27 teoremas: idempotencia, conmutatividad, asociatividad, identidad/aniquilador con ∅, cotas sup/inf, caracterización vía ≤, max/min es uno de los argumentos, max=min⇔iguales
  - ✅ 31 exports al namespace `SetUniverse`
  - ✅ Build limpio; 37/37 módulos compilados correctamente

- **Nuevo módulo NaturalNumbersNewtonBinom.lean — Teorema binomial de Newton en ω** (Patrón B, bridge-only, 4 argumentos):
  - ✅ `binomTermOf (a b n k : U) : U` — C(n,k)·a^k·b^(n−k) vía `fromPeano (Peano.NewtonBinom.binomTerm ...)`
  - ✅ `fromPeano_binomTerm` — teorema puente con 4 argumentos (`congr 1` ×4)
  - ✅ 9 teoremas: valores concretos (k=0, k=n), expansión, separación de potencias n^(m+k)=n^m·n^k, Newton's binomial theorem (Peano→ZFC), Σ C(n,k)=2^n (Peano→ZFC), comparación de crecimiento existencial
  - ✅ **Decisión de diseño**: `finSum` (función de orden superior) no se transporta a ZFC; `newton_binom_peano` y `sum_binom_eq_pow_two_peano` usan tipos Peano con resultado aplicado vía `fromPeano`
  - ✅ 12 exports al namespace `SetUniverse`

- **Nuevo módulo NaturalNumbersWellFounded.lean — Buen fundamento y buena ordenación en ω** (Patrón B, bridge-only):
  - ✅ `acc_lt_Omega (n : U)` — accesibilidad bajo ∈ restringido a ω, delegando a `nat_mem_wf.apply n`
  - ✅ `well_ordering_Omega (P : U → Prop)` — principio de buena ordenación con unicidad: todo subconjunto no vacío de ω tiene un mínimo único, transportado desde `Peano.WellFounded.well_ordering_principle`
  - ✅ `well_ordering_Omega_exists` — forma simplificada sin unicidad
  - ✅ 3 exports al namespace `SetUniverse`

- **REFERENCE.md — Proyección completa de 3 módulos**:
  - ✅ §1.1: 3 filas añadidas (MaxMin, NewtonBinom, WellFounded)
  - ✅ §3.33 (MaxMin: 2 def), §3.34 (NewtonBinom: 1 def), §3.35 (WellFounded: 0 def)
  - ✅ §4.29 (MaxMin: 29 teoremas en 10 secciones), §4.30 (NewtonBinom: 10 teoremas en 8 secciones), §4.31 (WellFounded: 3 teoremas en 2 secciones)
  - ✅ §6.30 (31 exports), §6.31 (12 exports), §6.32 (3 exports)
  - ✅ §7.2: 3 entradas añadidas a archivos completos

### Añadido (2026-03-24 10:00)

- **Nuevo módulo NaturalNumbersFactorial.lean — Factorial en ω** (Patrón B, bridge-only):
  - ✅ `factorial (n : U) : U` — factorial de naturales de von Neumann via `fromPeano (Peano.Factorial.factorial (toPeano n hn))`
  - ✅ `fromPeano_factorial` — teorema puente con `Peano.Factorial.factorial`
  - ✅ 10 teoremas: `factorial_zero`, `factorial_one`, `factorial_two`, `factorial_succ`, `factorial_pos`, `factorial_ne_zero`, `factorial_ge_one`, `factorial_le_succ`, `factorial_le_mono`, `factorial_in_Omega`
  - ✅ Build limpio; 31/31 módulos compilados correctamente

- **REFERENCE.md — Proyección y corrección completa de 7 módulos**:
  - ✅ `AtomicBooleanAlgebra.lean`: completada proyección parcial; §3.12 (4 def), §4.7 (14 teoremas), §6.25 (19 exports); estado 🔶 Parcial → ✅ Completo
  - ✅ `GeneralizedDeMorgan.lean`: corregida documentación incorrecta — §3.16 (1 def real vs. 3 ficticias anteriores), §4.11 (10 teoremas reales vs. 8 ficticios), §6.8 (8 exports reales)
  - ✅ `GeneralizedDistributive.lean`: corregida documentación incorrecta — §3.17 (2 def reales vs. 5 ficticias anteriores), §4.12 (10 teoremas reales), §6.9 (12 exports reales)
  - ✅ `Recursion.lean`: expandido §6.17 con todos los exports de variantes step e CoV (anteriormente incompleto: ~15 entradas faltaban)
  - ✅ `SetOrder.lean`, `SetStrictOrder.lean`, `PeanoImport.lean`: verificados correctamente proyectados

### Añadido (2026-03-22 12:00)

- **Nuevo módulo NaturalNumbersPow.lean — Potenciación en ω** (Patrón RecursiveFn):
  - ✅ `powFn (m : U) (hm : m ∈ ω) : U` — función de potenciación vía `RecursiveFn ω (σ ∅) (mulFn m hm)`
  - ✅ `pow (m n : U) : U` — potencia de naturales de von Neumann
  - ✅ `fromPeano_pow` — teorema puente con `Peano.Pow.pow`
  - ✅ 13 teoremas: `pow_zero`, `pow_succ`, `pow_eq`, `pow_in_Omega`, `zero_pow_Omega`, `one_pow_Omega`, `pow_one_Omega`, `pow_ne_zero_Omega`, `pow_two_Omega`, `pow_add_eq_mul_pow_Omega`, `mul_pow_Omega`, `pow_pow_eq_pow_mul_Omega`, `powFn_is_function`
  - ✅ 18 exports totales; build limpio

- **Nuevo módulo NaturalNumbersArith.lean — Divisibilidad, GCD, LCM, Bézout** (Patrón RecursiveFn + Patrón B):
  - ✅ `divides (m n : U) : Prop` — predicado ZFC directo: ∃ k ∈ ω, n = m*k
  - ✅ `div (m n : U) : U` — cociente euclídeo nativo ZFC via `divMod_stepFn` (función paso en ω×ω)
  - ✅ `mod (m n : U) : U` — resto euclídeo nativo ZFC (mismo RecursiveFn)
  - ✅ `div_eq_divOf`/`mod_eq_modOf` — equivalencia con Pattern B de NaturalNumbersDiv
  - ✅ `gcdOf (m n : U) : U` — MCD Pattern B via `Peano.Arith.gcd`
  - ✅ `lcmOf (m n : U) : U` — MCM Pattern B via `Peano.Arith.lcm`
  - ✅ `bezout_natform_Omega` — Bézout en forma substractiva: ∃ a b, a*m − b*n = gcd(m,n) ∨ a*n − b*m = gcd(m,n)
  - ✅ 13 propiedades de divisibilidad, 8 propiedades de gcd/lcm, 14 propiedades de div/mod nativo
  - ✅ 43 exports totales; build limpio (tras fix de ambigüedad σ con NaturalNumbers.successor)

- **REFERENCE.md**: actualización completa
  - ✅ §1.1: NaturalNumbersPow.lean y NaturalNumbersArith.lean añadidos a tabla
  - ✅ §3.27-§3.28: nuevas secciones de definiciones
  - ✅ §4.23-§4.24: nuevas secciones de teoremas
  - ✅ §6.23-§6.24: nuevas secciones de exports
  - ✅ §7.2: lista de archivos completos actualizada

### Añadido (2026-03-21 12:00)

- **Nuevo módulo NaturalNumbersSub.lean — Sustracción saturada en ω** (Patrón RecursiveFn):
  - ✅ `predecessorFn : U` — función predecesor para Recursión
  - ✅ `subFn (m : U) (hm : m ∈ ω) : U` — función de sustracción vía `RecursiveFn`
  - ✅ `sub (m n : U) : U` — sustracción saturada (monus) de naturales de von Neumann
  - ✅ `fromPeano_sub` — teorema puente con `Peano.Sub.sub`
  - ✅ 13 teoremas algebraicos

- **Nuevo módulo NaturalNumbersDiv.lean — División euclídea en ω** (Patrón B):
  - ✅ `divOf (m n : U) : U` — cociente via isomorfismo
  - ✅ `modOf (m n : U) : U` — resto via isomorfismo
  - ✅ `divMod_eq_Omega`, `mod_lt_divisor_Omega`, `div_of_lt_Omega`, `mod_of_lt_Omega`, `div_le_self_Omega`

### Añadido (2026-03-08 14:00)

- **Nuevo módulo NaturalNumbersAdd.lean — Suma en ω**:
  - ✅ `successorFn : U → U → U` — función sucesor para Recursión (no computable, proposicional)
  - ✅ `addFn (m : U) (hm : m ∈ ω) : U` — función de suma vía `RecursiveFn`
  - ✅ `add (m n : U) : U` — suma de naturales de von Neumann
  - ✅ `fromPeano_add` — teorema puente: `fromPeano (p + q) = add (fromPeano p) (fromPeano q)`
  - ✅ 16 teoremas algebraicos: `add_zero_Omega`, `zero_add_Omega`, `add_succ_Omega`, `succ_add_Omega`, `add_comm_Omega`, `add_assoc_Omega`, `add_left_cancel_Omega`, `add_right_cancel_Omega`, `add_pos_left_Omega`, `add_pos_right_Omega`, `le_then_exists_add_Omega`, `add_lt_of_lt_Omega`, `add_le_left_Omega`, `add_le_right_Omega`, `lt_add_of_pos_right_Omega`, `lt_add_of_pos_left_Omega`
  - ✅ Build: 28/28 módulos compilados correctamente

- **Nuevo módulo NaturalNumbersMul.lean — Multiplicación en ω**:
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
  - ✅ §1.1: NaturalNumbersAdd.lean y NaturalNumbersMul.lean añadidos
  - ✅ §3.22: nueva sección NaturalNumbersAdd (3 definiciones)
  - ✅ §3.23: nueva sección NaturalNumbersMul (2 definiciones)
  - ✅ §4.17: PeanoImport ampliado (+5 teoremas)
  - ✅ §4.18: nueva sección NaturalNumbersAdd (16 teoremas)
  - ✅ §4.19: nueva sección NaturalNumbersMul (13 teoremas)
  - ✅ §5.11-5.12: notaciones ΠZ/ZΠ, add, mul
  - ✅ §6.15-6.17: exports PeanoImport, NaturalNumbersAdd, NaturalNumbersMul
  - ✅ §7.2: Cardinality movido de 7.3 a 7.2

- **ZfcSetTheory.lean** (módulo raíz): `import ZfcSetTheory.NaturalNumbersMul` añadido

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

- **NaturalNumbers.lean — exports de predecessor ampliados**:
  - ✅ `predecessor`, `predecessor_of_successor`, `predecessor_is_nat`, `predecessor_mem` ahora en la lista de exports pública

- **Documentación actualizada (REFERENCE.md)**:
  - ✅ §1.1: PeanoImport.lean añadido a la tabla de módulos
  - ✅ §3.13: definición `predecessor` documentada
  - ✅ §3.21: nueva sección PeanoImport.lean (2 definiciones)
  - ✅ §4.9: `nat_mem_wf` documentado con nota de implementación
  - ✅ §4.17: nueva sección PeanoImport.lean (7 teoremas)

### Actualizado (2026-02-12 18:45)

- **Documentación Completa - Proyección de NaturalNumbers.lean y Actualización de Markdown**:
  - ✅ NaturalNumbers.lean completamente proyectado en REFERENCE.md (13 definiciones + 36 teoremas + 47 exportaciones)
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

- **Domain y Range para Relaciones** en `Relations.lean`:
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
  - Actualizadas todas las referencias en `Cardinality.lean`

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

- **PowerSetAlgebra.lean**: Álgebra del conjunto potencia
  - `Complement A X` - Complemento de X respecto a A (notación: `X^∁[ A ]`)
  - `ComplementFamily A F` - Familia de complementos
  - `double_complement` - (X^∁[A])^∁[A] = X (si X ⊆ A)
  - `complement_empty` - ∅^∁[A] = A
  - `complement_full` - A^∁[A] = ∅
  - De Morgan para familias: `DeMorgan_union_family`, `DeMorgan_inter_family`

- **GeneralizedDeMorgan.lean**: Leyes de De Morgan generalizadas
  - `complement_union_eq_inter_complement` - A \ ⋃ F = ⋂ (ComplementFamily A F)
  - `complement_inter_eq_union_complement` - A \ ⋂ F = ⋃ (ComplementFamily A F)
  - Versiones duales e inversas

- **GeneralizedDistributive.lean**: Leyes distributivas generalizadas
  - `DistribSet X F op` - Conjunto imagen { op(X, Y) | Y ∈ F }
  - `inter_union_distrib` - X ∩ (⋃ F) = ⋃ { X ∩ Y | Y ∈ F }
  - `union_inter_distrib` - X ∪ (⋂ F) = ⋂ { X ∪ Y | Y ∈ F }
  - Versiones conmutativas

- **AtomicBooleanAlgebra.lean**: Álgebra de Boole atómica
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

- **CartesianProduct.lean**: Renombrado namespace `CartesianProductAxiom` → `CartesianProduct`
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

- **SetStrictOrder.lean**: Orden estricto completo
  - `strict_order_irreflexive`: ¬(A ⊂ A)
  - `strict_order_asymmetric`: A ⊂ B → ¬(B ⊂ A)
  - `strict_order_transitive`: A ⊂ B → B ⊂ C → A ⊂ C
  - `partial_to_strict_order`: Conversión de orden parcial a estricto

- **SetOrder.lean**: Estructura de retículo
  - `isUpperBound`, `isLowerBound`, `isSupremum`, `isInfimum`
  - `inter_is_glb`: A ∩ B es el ínfimo
  - `union_is_lub`: A ∪ B es el supremo
  - Monotonía bilateral de ∩ y ∪

### Mejorado

- **BooleanAlgebra.lean**: Nuevos teoremas de monotonía y equivalencias

---

## [0.3.0] - 2026-02-04 11:00

### Añadido

- **BooleanAlgebra.lean**: Teoremas de álgebra booleana
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
