# Changelog

**Última actualización:** 2026-03-08 14:00
**Autor**: Julián Calderón Almendros

Todos los cambios notables de este proyecto serán documentados en este archivo.

El formato está basado en [Keep a Changelog](https://keepachangelog.com/es-ES/1.0.0/),
y este proyecto adhiere a [Semantic Versioning](https://semver.org/spec/v2.0.0.html).

## [Unreleased]

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
