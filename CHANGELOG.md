# Changelog

Todos los cambios notables de este proyecto serán documentados en este archivo.

El formato está basado en [Keep a Changelog](https://keepachangelog.com/es-ES/1.0.0/),
y este proyecto adhiere a [Semantic Versioning](https://semver.org/spec/v2.0.0.html).

## [Unreleased]

### En desarrollo

- Producto cartesiano A × B
- Teoremas adicionales de álgebra booleana (distributividad, De Morgan)

---

## [0.6.0] - 2026-02-07

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

## [0.5.0] - 2026-02-06

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

## [0.4.0] - 2026-02-05

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

## [0.3.0] - 2026-02-04

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

## [0.2.0] - 2026-02-03

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

## [0.1.0] - 2026-02-02

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
