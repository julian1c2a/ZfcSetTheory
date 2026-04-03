# Referencia Técnica - ZfcSetTheory

*Última actualización: 2026-04-02 17:53*
**Autor**: Julián Calderón Almendros

## 0. Guía de Convenciones de Nombres para el Estudioso

Este proyecto adopta convenciones de nombres estilo [Mathlib](https://leanprover-community.github.io/contribute/naming.html). A continuación se resumen las claves para leer y buscar teoremas.

### 0.1 Reglas de Capitalización

- **Teoremas/lemas** (Prop): `snake_case` — `union_comm`, `mem_powerset_iff`
- **Definiciones Prop** (predicados): `UpperCamelCase` — `IsNat`, `IsFunction`; en nombres de teoremas bajan a `lowerCamelCase`: `isNat_zero`
- **Funciones** (retornan `U`): `lowerCamelCase` — `powerset`, `union`, `sUnion`
- **Acrónimos**: como grupo — `ZFC` (namespace), `zfc` (en snake_case)

### 0.2 Diccionario de Símbolos → Palabras

| Símbolo | Nombre | | Símbolo | Nombre | | Símbolo | Nombre |
|---------|--------|---|---------|--------|---|---------|--------|
| ∈ | `mem` | | ∪ | `union` | | + | `add` |
| ∉ | `not_mem` | | ∩ | `inter` | | * | `mul` |
| ⊆ | `subset` | | ⋃ | `sUnion` | | - | `sub`/`neg` |
| ⊂ | `ssubset` | | ⋂ | `sInter` | | / | `div` |
| 𝒫 | `powerset` | | \ | `sdiff` | | ^ | `pow` |
| σ | `succ` | | △ | `symmDiff` | | ∣ | `dvd` |
| ∅ | `empty` | | ᶜ | `compl` | | ≤ | `le` |
| = | `eq` | | ⟂ | `disjoint` | | < | `lt` |
| ≠ | `ne` | | ↔ | `iff` | | 0 | `zero` |
| ¬ | `not` | | → | `of` | | 1 | `one` |

### 0.3 Estructura de Nombres de Teoremas

- **Conclusión primero**: `isNat_succ_of_isNat` — la conclusión (`isNat_succ`) va antes, las hipótesis (`of_isNat`) después con `_of_`
- **Bicondicionales**: sufijo `_iff` — `mem_powerset_iff` (∈ 𝒫 ↔ ⊆)
- **Direcciones de un iff**: `.mp` (→) y `.mpr` (←) — `mem_powerset_iff.mp`
- **Especificaciones**: `mem_X_iff` — `mem_succ_iff`, `mem_inter_iff`, `mem_union_iff`

### 0.4 Sufijos Axiomáticos

| Sufijo | Significado | | Sufijo | Significado |
|--------|------------|---|--------|------------|
| `_comm` | conmutatividad | | `_self` | op consigo mismo |
| `_assoc` | asociatividad | | `_left`/`_right` | variante lateral |
| `_refl` | reflexividad | | `_cancel` | cancelación |
| `_trans` | transitividad | | `_mono` | monotonía |
| `_antisymm` | antisimetría | | `_inj` | inyectividad (iff) |
| `_symm` | simetría | | `_injective` | inyectividad (pred) |

### 0.5 Estado de Migración de Nombres

✅ **Fase 3 completada** (abril 2026): Los nombres del proyecto han sido migrados a las convenciones Mathlib. Ejemplos de renombramientos aplicados: `BinUnion_commutative` → `union_comm`, `PowerSet_is_specified` → `mem_powerset_iff`, `ExtSet_wc` → `eq_of_subset_of_subset`, `subseteq` → `subset`, `subset` → `ssubset`, `SpecSet` → `sep`, `isNat` → `IsNat`. Algunos identificadores internos conservan su nombre original (e.g., `strict_order_transitive`, `CartesianProduct_is_specified`).

---

## 📋 Cumplimiento con AI-GUIDE.md

Este documento cumple con todos los requisitos especificados en [AI-GUIDE.md](AI-GUIDE.md):

✅ **(1)** Todos los módulos .lean documentados en sección 1.1
✅ **(2)** Dependencias entre módulos (tabla con columna de dependencias)
✅ **(3)** Espacios de nombres y relaciones (tabla con columna de namespace)
✅ **(4)** Axiomas con ubicación, namespace y orden de declaración (sección 2)
✅ **(5)** Axiomas y definiciones con:

- Nomenclatura matemática humana legible
- Firma Lean4 para uso en código
- Dependencias explícitas
✅ **(6)** Teoremas principales sin demostración con:
- Nomenclatura matemática humana legible
- Firma Lean4 para uso en código
- Dependencias explícitas
✅ **(7)** Solo contenido demostrado/construido (verificado 08-mar-2026)
✅ **(8)** Actualización continua al cargar archivos .lean
✅ **(9)** Suficiente como única referencia (no requiere cargar proyecto completo)

**Estado de verificación**: ✅ TODOS LOS MÓDULOS 100% COMPLETOS - 0 `sorry` activos
✅ **Nat.Mul.lean creado (0 sorry, multiplicación ZFC + puente fromPeano_mul + 8 propiedades algebraicas)** - Actualizado 2026-03-08 12:00
✅ **Nat.Add.lean ampliado (Sección 6: 6 nuevos teoremas de cancelación, positividad y orden)** - Actualizado 2026-03-08 12:00
✅ **PeanoImport.lean ampliado (Section 2: toPeano_zero/succ; Section 3: recursion_transport_step/inv; Section 4: orden ↔ membresía)** - Actualizado 2026-03-08 12:00
✅ **PeanoImport.lean completado (0 sorry, isomorfismo Von Neumann ↔ Peano, 100% proyectado)** - Actualizado 2026-03-04 12:00
✅ **Infinity.lean: nat_mem_wf demostrado (sin sorry, añadido a exports)** - Actualizado 2026-03-04 12:00
✅ **Nat.Basic.lean: predecessor y teoremas exportados** - Actualizado 2026-03-04 12:00
✅ **Nat.Basic.lean completado (0 sorry, 36 teoremas principales, 100% proyectado)** - Actualizado 2026-02-12 18:45
✅ **Recursion.lean completado (0 sorry, 0 errores de tipo)** - Actualizado 2026-03-05 10:00 (RecursionTheorem 100% demostrado sin sorry; añadidos 5 lemas auxiliares globales + RecursionComputations + computations_are_compatible)
✅ **Functions.lean completado (0 sorry)** - Actualizado 2026-02-12 14:52

---

## 1. Arquitectura del Proyecto

### 1.1 Módulos y Dependencias

| Archivo | Namespace | Dependencias | Estado Proyección |
|---------|-----------|--------------|-------------------|
| `Prelim.lean` | - | `Init.Classical` | ✅ Completo |
| `Extension.lean` | `ZFC.Axiom.Extension` | `Prelim` | ✅ Completo |
| `Existence.lean` | `ZFC.Axiom.Existence` | `Prelim`, `Extension` | ✅ Completo |
| `Specification.lean` | `ZFC.Axiom.Specification` | `Prelim`, `Extension`, `Existence` | ✅ Completo |
| `Pairing.lean` | `ZFC.Axiom.Pairing` | `Prelim`, `Extension`, `Existence`, `Specification` | ✅ Completo (2026-03-16) |
| `Union.lean` | `ZFC.Axiom.Union` | `Prelim`, `Extension`, `Existence`, `Specification`, `Pairing` | ✅ Completo |
| `PowerSet.lean` | `ZFC.Axiom.PowerSet` | `Prelim`, `Extension`, `Existence`, `Specification`, `Pairing`, `Union` | ✅ Completo |
| `BoolAlg.PowerSetAlgebra.lean` | `ZFC.BoolAlg.PowerSetAlgebra` | `PowerSet`, `BoolAlg.Basic` + anteriores | ✅ Completo |
| `OrderedPair.lean` | `ZFC.SetOps.OrderedPair` | Todos los anteriores + `PowerSet` | ✅ Completo |
| `SetOps.CartesianProduct.lean` | `ZFC.SetOps.CartesianProduct` | `OrderedPair` + anteriores | ✅ Completo |
| `SetOps.Relations.lean` | `ZFC.SetOps.Relations` | `SetOps.CartesianProduct` + anteriores | ✅ Completo |
| `SetOps.Functions.lean` | `ZFC.SetOps.Functions` | `SetOps.CartesianProduct`, `Relations` + anteriores | ✅ Completo |
| `BoolAlg.Basic.lean` | `ZFC.BoolAlg.Basic` | `Union`, `Specification`, `Pairing`, `Extension`, `Existence`, `Prelim` | ✅ Completo |
| `BoolAlg.Ring.lean` | `ZFC.BoolAlg.Ring` | `BoolAlg.PowerSetAlgebra` + anteriores | ✅ Completo |
| `BoolAlg.PowerSetAlgebra.lean` | `ZFC.BoolAlg.PowerSetAlgebra` | `PowerSet`, `BoolAlg.Basic` + anteriores | ✅ Completo |
| `BoolAlg.Atomic.lean` | `ZFC.BoolAlg.Atomic` | `BoolAlg.PowerSetAlgebra`, `SetOps.SetOrder`, `SetOps.SetStrictOrder` + anteriores | ✅ Completo (2026-03-24) |
| `Cardinal.Basic.lean` | `ZFC.Cardinal.Basic` | `Functions` + todos los anteriores | ✅ Completo (2026-03-16) |
| `Nat.Basic.lean` | `ZFC.Nat.Basic` | `Cardinality` + todos los anteriores | ✅ Completo |
| `Infinity.lean` | `ZFC.Axiom.Infinity` | `Nat.Basic` + todos los anteriores | ✅ Completo |
| `PeanoImport.lean` | `ZFC` | `Nat.Basic`, `Infinity`, `PeanoNatLib.PeanoNatAxioms` | ✅ Completo |
| `BoolAlg.GenDeMorgan.lean` | `ZFC.BoolAlg.GenDeMorgan` | `BoolAlg.PowerSetAlgebra` + anteriores | ✅ Completo |
| `BoolAlg.GenDistributive.lean` | `ZFC.BoolAlg.GenDistributive` | `BoolAlg.PowerSetAlgebra` + anteriores | ✅ Completo |
| `SetOps.SetOrder.lean` | `ZFC.SetOps.SetOrder` | `Relations` + anteriores | ✅ Completo |
| `SetOps.SetStrictOrder.lean` | `ZFC.SetOps.SetStrictOrder` | `SetOps.SetOrder` + anteriores | ✅ Completo |
| `Induction.Recursion.lean` | `ZFC.Induction.Recursion` | `Nat.Basic`, `Functions`, `Relations` + anteriores | ✅ Completo |
| `Nat.Add.lean` | `ZFC.Nat.Add` | `Nat.Basic`, `Infinity`, `Recursion`, `PeanoImport`, `PeanoNatLib.PeanoNatAdd` | ✅ Completo |
| `Nat.Mul.lean` | `ZFC.Nat.Mul` | `Nat.Basic`, `Infinity`, `Recursion`, `PeanoImport`, `Nat.Add`, `PeanoNatLib.PeanoNatMul` | ✅ Completo |
| `Nat.Sub.lean` | `ZFC.Nat.Sub` | `Nat.Basic`, `Infinity`, `Recursion`, `PeanoImport`, `Nat.Add`, `PeanoNatLib.PeanoNatSub` | ✅ Completo |
| `Nat.Div.lean` | `ZFC.Nat.Div` | `Nat.Basic`, `Infinity`, `Recursion`, `PeanoImport`, `Nat.Add`, `Nat.Mul`, `Nat.Sub`, `PeanoNatLib.PeanoNatDiv` | ✅ Completo |
| `Nat.Pow.lean` | `ZFC.Nat.Pow` | `Nat.Basic`, `Infinity`, `Recursion`, `PeanoImport`, `Nat.Mul`, `PeanoNatLib.PeanoNatPow` | ✅ Completo |
| `Nat.Arith.lean` | `ZFC.Nat.Arith` | `Nat.Basic`, `Infinity`, `Recursion`, `PeanoImport`, `Nat.Add`, `Nat.Mul`, `Nat.Sub`, `Nat.Div`, `PeanoNatLib.PeanoNatArith` | ✅ Completo |
| `Nat.Factorial.lean` | `ZFC.Nat.Factorial` | `Nat.Basic`, `Infinity`, `Recursion`, `PeanoImport`, `Nat.Mul`, `PeanoNatLib.PeanoNatFactorial` | ✅ Completo |
| `Nat.Gcd.lean` | `ZFC.Nat.Gcd` | `Nat.Basic`, `Infinity`, `Recursion`, `PeanoImport`, `Nat.Add`, `Nat.Mul`, `Nat.Sub`, `Nat.Div`, `Nat.Arith` | ✅ Completo |
| `Nat.Primes.lean` | `ZFC.Nat.Primes` | `Nat.Basic`, `Infinity`, `Recursion`, `PeanoImport`, `Nat.Add`, `Nat.Mul`, `Nat.Sub`, `Nat.Div`, `Nat.Arith`, `Nat.Gcd`, `PeanoNatLib.PeanoNatPrimes` | ✅ Completo |
| `Nat.Binom.lean` | `ZFC.Nat.Binom` | `Nat.Basic`, `Infinity`, `PeanoImport`, `Nat.Add`, `Nat.Mul`, `Nat.Sub`, `Nat.Factorial`, `PeanoNatLib.PeanoNatBinom` | ✅ Completo |
| `Nat.MaxMin.lean` | `ZFC.Nat.MaxMin` | `Nat.Basic`, `Infinity`, `PeanoImport`, `PeanoNatLib.PeanoNatMaxMin` | ✅ Completo |
| `Nat.NewtonBinom.lean` | `ZFC.Nat.NewtonBinom` | `Nat.Basic`, `Infinity`, `PeanoImport`, `Nat.Add`, `Nat.Mul`, `Nat.Sub`, `Nat.Pow`, `Nat.Binom`, `PeanoNatLib.PeanoNatNewtonBinom` | ✅ Completo |
| `Nat.WellFounded.lean` | `ZFC.Nat.WellFounded` | `Nat.Basic`, `Infinity`, `PeanoImport`, `PeanoNatLib.PeanoNatWellFounded` | ✅ Completo |
| `Peano.FiniteSequences.lean` | `ZFC.Peano.FiniteSequences` | `Nat.Add` + anteriores | ✅ Completo |
| `SetOps.FiniteSets.lean` | `ZFC.SetOps.FiniteSets` | `Nat.Basic`, `Infinity` + anteriores | ✅ Completo |
| `Peano.FiniteSequencesArith.lean` | `ZFC.Peano.FiniteSequencesArith` | `Nat.Mul`, `Peano.FiniteSequences`, `SetOps.FiniteSets` + anteriores | ✅ Completo |
| `Peano.FiniteSequencesBridge.lean` | `ZFC.Peano.FiniteSequencesBridge` | `Peano.FiniteSequencesArith`, `Nat.Primes` + anteriores | ✅ Completo |
| `BoolAlg.Complete.lean` | `ZFC.BoolAlg.Complete` | `BoolAlg.PowerSetAlgebra`, `BoolAlg.GenDeMorgan`, `SetOps.SetOrder`, `BoolAlg.Atomic` + anteriores | ✅ Completo |
| `BoolAlg.FiniteCofinite.lean` | `ZFC.BoolAlg.FiniteCofinite` | `BoolAlg.Complete`, `SetOps.FiniteSets`, `Nat.Add`, `Cardinality` + anteriores | ✅ Completo |
| `BoolAlg.Representation.lean` | `ZFC.BoolAlg.Representation` | `BoolAlg.Complete`, `BoolAlg.Atomic`, `Cardinal.Basic` + anteriores | ✅ Completo |
| `Cardinal.FinitePowerSet.lean` | `ZFC.Cardinal.FinitePowerSet` | `Cardinal.Basic`, `SetOps.FiniteSets`, `Nat.Mul`, `Nat.Pow` + anteriores | ✅ Completo |
| `BoolAlg.FiniteBA.lean` | `ZFC.BoolAlg.FiniteBA` | `Cardinal.FinitePowerSet`, `BoolAlg.Representation` + anteriores | ✅ Completo |
| `BoolAlg.BoolRingBA.lean` | `ZFC.BoolAlg.BoolRingBA` | `BoolAlg.Ring` + anteriores | ✅ Completo |

### 1.2 Axiomas ZFC por Módulo

Cada módulo usa transitivamente un subconjunto de los 7 axiomas ZFC del proyecto. Abreviaturas:

| Abrev. | Axioma | Módulo declarante |
|--------|--------|-------------------|
| **Ext** | Extensionalidad | `Axiom.Extension` |
| **Vac** | Conjunto Vacío | `Axiom.Existence` |
| **Sep** | Separación/Especificación | `Axiom.Specification` |
| **Par** | Pares | `Axiom.Pairing` |
| **Uni** | Unión | `Axiom.Union` |
| **Pot** | Conjunto Potencia | `Axiom.PowerSet` |
| **Inf** | Infinito | `Axiom.Infinity` |

#### Módulos por nivel axiomático

**0 axiomas** — `Core.Prelim` (solo declara la variable de tipo universo)

**1 axioma** {Ext} — `Axiom.Extension`

**2 axiomas** {Ext, Vac} — `Axiom.Existence`

**3 axiomas** {Ext, Vac, Sep} — `Axiom.Specification`

**4 axiomas** {Ext, Vac, Sep, Par} — `Axiom.Pairing`

**5 axiomas** {Ext, Vac, Sep, Par, Uni}:

- `Axiom.Union`
- `BoolAlg.Basic`
- `SetOps.SetOrder`
- `SetOps.SetStrictOrder`

**6 axiomas** {Ext, Vac, Sep, Par, Uni, Pot}:

- `Axiom.PowerSet`
- `SetOps.OrderedPair`
- `SetOps.CartesianProduct`
- `SetOps.Relations`
- `SetOps.Functions`
- `Cardinal.Basic`
- `Nat.Basic`
- `BoolAlg.PowerSetAlgebra`
- `BoolAlg.Ring`
- `BoolAlg.GenDeMorgan`
- `BoolAlg.GenDistributive`
- `BoolAlg.Atomic`
- `BoolAlg.Complete`
- `BoolAlg.BoolRingBA`
- `BoolAlg.Representation`

**7 axiomas** {Ext, Vac, Sep, Par, Uni, Pot, Inf} — todos:

- `Axiom.Infinity`
- `Induction.Recursion`
- `Peano.Import`
- `Peano.FiniteSequences`
- `Peano.FiniteSequencesArith`
- `Peano.FiniteSequencesBridge`
- `SetOps.FiniteSets`
- `Cardinal.FinitePowerSet`
- `Nat.Add`, `Nat.Mul`, `Nat.Sub`, `Nat.Div`, `Nat.Pow`
- `Nat.Arith`, `Nat.Factorial`, `Nat.Gcd`, `Nat.Primes`
- `Nat.Binom`, `Nat.MaxMin`, `Nat.NewtonBinom`, `Nat.WellFounded`
- `BoolAlg.FiniteCofinite`
- `BoolAlg.FiniteBA`

**Nota**: `BoolAlg.Representation` (teorema de Stone) usa solo 6 axiomas — no requiere Infinito. `BoolAlg.FiniteBA` sí requiere los 7 porque importa `Cardinal.FinitePowerSet`.

## 2. Axiomas ZFC Implementados

### 2.1 Axioma de Extensionalidad

**Ubicación**: `Extension.lean`, línea 15  
**Namespace**: `ZFC.Axiom.Extension`  
**Orden**: 1º axioma declarado

**Enunciado Matemático**: Dos conjuntos son iguales si y solo si tienen los mismos elementos.

**Firma Lean4**:

```lean
@[simp] axiom ExtSet (x y : U): (∀ (z: U), z ∈ x ↔ z ∈ y) → (x = y)
```

**Dependencias**: Ninguna (axioma primitivo)

### 2.2 Axioma de Existencia

**Ubicación**: `Existence.lean`, línea 12  
**Namespace**: `ZFC.Axiom.Existence`  
**Orden**: 2º axioma declarado

**Enunciado Matemático**: Existe un conjunto que no contiene ningún elemento (conjunto vacío).

**Firma Lean4**:

```lean
@[simp] axiom ExistsAnEmptySet : ∃ (x : U), ∀ (y : U), y ∉ x
```

**Dependencias**: `ExtSet` (para unicidad)

### 2.3 Axioma de Especificación

**Ubicación**: `Specification.lean`, línea 15  
**Namespace**: `ZFC.Axiom.Specification`  
**Orden**: 3º axioma declarado

**Enunciado Matemático**: Para cualquier conjunto A y propiedad P, existe un conjunto que contiene exactamente los elementos de A que satisfacen P.

**Firma Lean4**:

```lean
@[simp] axiom Specification (x : U) (P : U → Prop) :
  ∃ (y : U), ∀ (z : U), z ∈ y ↔ (z ∈ x ∧ P z)
```

**Dependencias**: `ExtSet`, `EmptySet`

### 2.4 Axioma de Par

**Ubicación**: `Pairing.lean`, línea 13  
**Namespace**: `ZFC.Axiom.Pairing`  
**Orden**: 4º axioma declarado

**Enunciado Matemático**: Para cualesquiera dos elementos a y b, existe un conjunto que contiene exactamente a y b.

**Firma Lean4**:

```lean
@[simp] axiom Pairing (x y : U) :
  ∃ (z : U), ∀ (w : U), w ∈ z ↔ (w = x ∨ w = y)
```

**Dependencias**: `ExtSet`, `sep`

### 2.5 Axioma de Unión

**Ubicación**: `Union.lean`, línea 14  
**Namespace**: `ZFC.Axiom.Union`  
**Orden**: 5º axioma declarado

**Enunciado Matemático**: Para cualquier familia de conjuntos F, existe un conjunto que contiene exactamente los elementos que pertenecen a algún conjunto de F.

**Firma Lean4**:

```lean
@[simp] axiom Union :
  ∀ (C : U), ∃ (UC : U), ∀ (x : U), x ∈ UC ↔ ∃ (y : U), y ∈ C ∧ x ∈ y
```

**Dependencias**: `ExtSet`, `PairSet`, `Singleton`

### 2.6 Axioma de Conjunto Potencia

**Ubicación**: `PowerSet.lean`, línea 22  
**Namespace**: `ZFC.Axiom.PowerSet`  
**Orden**: 6º axioma declarado

**Enunciado Matemático**: Para todo conjunto A, existe un conjunto P que contiene exactamente los subconjuntos de A: ∀A ∃P ∀x (x ∈ P ↔ x ⊆ A).

**Firma Lean4**:

```lean
@[simp] axiom PowerSet : ∀ (A : U), ∃ (P : U), ∀ (x : U), x ∈ P ↔ x ⊆ A
```

**Dependencias**: `ExtSet`, `subset`

### 2.7 Axioma de Infinito

**Ubicación**: `Infinity.lean`, línea 45  
**Namespace**: `ZFC.Axiom.Infinity`  
**Orden**: 6º axioma declarado

**Enunciado Matemático**: Existe un conjunto inductivo (que contiene ∅ y es cerrado bajo sucesores).

**Firma Lean4**:

```lean
axiom ExistsInductiveSet : ∃ (I : U), IsInductive I
```

**Dependencias**: `IsInductive` (de Nat.Basic.lean)

## 3. Definiciones Principales por Módulo

### 3.1 Prelim.lean

#### ExistsUnique

**Ubicación**: `Prelim.lean`, línea 12
**Orden**: 1ª definición

**Enunciado Matemático**: Existe un único elemento que satisface la propiedad P.

**Firma Lean4**:

```lean
def ExistsUnique {α : Sort u} (p : α → Prop) : Prop :=
  ∃ x, p x ∧ ∀ y, p y → y = x
```

**Dependencias**: Ninguna

**API completa**:

| Nombre ZFC (dot notation) | Alias Peano-compatible | Tipo |
|--------------------------|----------------------|------|
| `ExistsUnique.intro w hw h` | — | constructor |
| `ExistsUnique.exists h` | `ExistsUnique.exists h` | extrae `∃ x, p x` |
| `ExistsUnique.choose h` | `choose_unique h` | testigo `noncomputable` |
| `ExistsUnique.choose_spec h` | `choose_spec_unique h` | testigo satisface P |
| `ExistsUnique.unique h y hy` | `choose_uniq h hy` | unicidad: `y = choose` |

**Notas**:

- `choose_unique`, `choose_spec_unique`, `choose_uniq` son aliases top-level que replican la API de `Peano.PeanoNatLib` para unificación entre proyectos.
- La diferencia de estilo: ZFC usa dot-notation `h.choose`; Peano pasa `h` como argumento a `choose_unique h`.

### 3.2 Extension.lean

#### Pertenencia (mem)

**Ubicación**: `Extension.lean`, línea 10  
**Orden**: 1ª definición

**Enunciado Matemático**: Relación primitiva de pertenencia entre elementos y conjuntos.

**Firma Lean4**:

```lean
axiom mem (x y : U) : Prop
notation:50 lhs:51 " ∈ " rhs:51 => mem lhs rhs
```

**Dependencias**: Ninguna

#### Subconjunto (subset)

**Ubicación**: `Extension.lean`, línea 42  
**Orden**: 2ª definición

**Enunciado Matemático**: A es subconjunto de B si todo elemento de A está en B.

**Firma Lean4**:

```lean
@[simp] def subset (x y : U) : Prop := ∀ (z: U), z ∈ x → z ∈ y
notation:50 lhs:51 " ⊆ " rhs:51 => subset lhs rhs
```

**Dependencias**: `mem`

#### Conjuntos Disjuntos (disjoint)

**Ubicación**: `Extension.lean`, línea 118  
**Orden**: 4ª definición

**Enunciado Matemático**: Dos conjuntos son disjuntos si no tienen elementos en común.

**Firma Lean4**:

```lean
@[simp] def disjoint (x y : U) : Prop := ∀ z, z ∈ x → z ∉ y
notation:50 lhs:51 " ⟂ " rhs:51 => disjoint lhs rhs
```

**Dependencias**: `mem`

### 3.3 Existence.lean

#### Conjunto Vacío (EmptySet)

**Ubicación**: `Existence.lean`, línea 32  
**Orden**: 1ª definición principal

**Enunciado Matemático**: El único conjunto que no contiene elementos.

**Firma Lean4**:

```lean
@[simp] noncomputable def EmptySet : U := ExistsUniqueEmptySet.choose
notation " ∅ " => EmptySet
```

**Dependencias**: `ExistsAnEmptySet`, `ExtSet`

### 3.4 Specification.lean

#### Conjunto Especificado (sep)

**Ubicación**: `Specification.lean`, línea 35  
**Orden**: 1ª definición principal

**Enunciado Matemático**: El conjunto de elementos de A que satisfacen la propiedad P.

**Firma Lean4**:

```lean
@[simp] noncomputable def sep (x : U) (P : U → Prop) : U :=
  choose (SpecificationUnique x P)
notation " { " x " | " P " } " => sep x P
```

**Dependencias**: `Specification`, `ExtSet`

#### Intersección Binaria (inter)

**Ubicación**: `Specification.lean`, línea 44  
**Orden**: 2ª definición principal

**Enunciado Matemático**: El conjunto de elementos que pertenecen tanto a A como a B.

**Firma Lean4**:

```lean
@[simp] noncomputable def inter (x y : U) : U :=
  choose (SpecificationUnique x fun z => z ∈ y)
notation:50 lhs:51 " ∩ " rhs:51 => inter lhs rhs
```

**Dependencias**: `sep`

#### Diferencia (sdiff)

**Ubicación**: `Specification.lean`, línea 175  
**Orden**: 3ª definición principal

**Enunciado Matemático**: El conjunto de elementos que están en A pero no en B.

**Firma Lean4**:

```lean
@[simp] noncomputable def sdiff (x y : U) : U :=
  choose (SpecificationUnique x (fun z => z ∉ y))
notation:50 lhs:51 " \\ " rhs:51 => sdiff lhs rhs
```

**Dependencias**: `sep`

### 3.5 Pairing.lean

#### Par No Ordenado (PairSet)

**Ubicación**: `Pairing.lean`, línea 32  
**Orden**: 1ª definición principal

**Enunciado Matemático**: El conjunto que contiene exactamente los elementos a y b.

**Firma Lean4**:

```lean
@[simp] noncomputable def PairSet (x y : U) : U :=
  choose (PairingUniqueSet x y)
notation " { " x ", " y " } " => PairSet x y
```

**Dependencias**: `Pairing`, `ExtSet`

#### Singleton

**Ubicación**: `Pairing.lean`, línea 39  
**Orden**: 2ª definición principal

**Enunciado Matemático**: El conjunto que contiene únicamente el elemento a.

**Firma Lean4**:

```lean
@[simp] noncomputable def Singleton (x : U) : U := ({ x , x } : U)
notation " { " x " } " => Singleton x
```

**Dependencias**: `PairSet`

#### Predicado de Pertenencia a Intersección (member_inter)

**Ubicación**: `Pairing.lean`, línea 68  
**Orden**: 3ª definición principal

**Enunciado Matemático**: w es miembro de la intersección de v si w pertenece a todo conjunto y en v.

**Firma Lean4**:

```lean
@[simp] def member_inter (w v : U) : Prop :=
  ∀ (y : U), ( y ∈ w ) → ( v ∈ y )
```

**Dependencias**: `mem`

#### Intersección de Familia (interSet)

**Ubicación**: `Pairing.lean`, línea 73  
**Orden**: 4ª definición principal

**Enunciado Matemático**: La intersección de una familia de conjuntos w: ⋂ w = {v | ∀y ∈ w, v ∈ y}.

**Firma Lean4**:

```lean
@[simp] noncomputable def interSet (w : U) : U :=
  if h : ∃ y, y ∈ w then
    let y₀ := choose h
    sep y₀ (fun v => ∀ y, y ∈ w → v ∈ y)
  else
    ∅
notation:100 "⋂ " w => interSet w
```

**Dependencias**: `sep`, `EmptySet`, `Classical.choose`

**Notación**: `⋂ w` para `interSet w`

#### Par Ordenado (OrderedPair)

**Ubicación**: `Pairing.lean`, línea 95  
**Orden**: 5ª definición principal

**Enunciado Matemático**: El par ordenado de Kuratowski ⟨a,b⟩ = {{a}, {a,b}}.

**Firma Lean4**:

```lean
@[simp] noncomputable def OrderedPair (x y : U) : U
    := (({ (({ x }): U) , (({ x , y }): U) }): U)
notation " ⟨ " x " , " y " ⟩ " => OrderedPair x y
```

**Dependencias**: `PairSet`, `Singleton`

#### Predicado de Par Ordenado (isOrderedPair)

**Ubicación**: `Pairing.lean`, línea 103  
**Orden**: 6ª definición principal

**Enunciado Matemático**: w es un par ordenado si existen x, y tales que w = ⟨x, y⟩.

**Firma Lean4**:

```lean
@[simp] def isOrderedPair (w : U) : Prop :=
  ∃ (x y : U), w = (⟨ x , y ⟩  : U)
```

**Dependencias**: `OrderedPair`

#### Primera Proyección (fst)

**Ubicación**: `Pairing.lean`, línea 108  
**Orden**: 7ª definición principal

**Enunciado Matemático**: La primera proyección de un par ordenado: fst(w) = ⋂(⋂ w).

**Firma Lean4**:

```lean
@[simp] noncomputable def fst (w : U) : U := (⋂ (⋂ w))
```

**Dependencias**: `interSet`

#### Segunda Proyección (snd)

**Ubicación**: `Pairing.lean`, línea 111  
**Orden**: 8ª definición principal

**Enunciado Matemático**: La segunda proyección de un par ordenado: snd(w) se calcula según si w \ {⋂ w} es vacío o no.

**Firma Lean4**:

```lean
@[simp] noncomputable def snd (w : U) : U :=
  let I := ⋂ w
  let s := w \ {I}
  if h : s = ∅ then
    ⋂ I
  else
    have h_exists : ∃ y, y ∈ s := (nonempty_iff_exists_mem s).mp h
    let s_elem := choose h_exists
    let r := s_elem \ I
    ⋂ r
```

**Dependencias**: `interSet`, `sdiff`, `Singleton`, `Classical.choose`, `nonempty_iff_exists_mem`

### 3.5.1 Pairing.lean - Predicados de Relaciones y Funciones

#### Relación (isRelation)

**Ubicación**: `Pairing.lean`, línea 348  
**Orden**: 1º predicado

**Enunciado Matemático**: R es una relación si todo elemento de R es un par ordenado.

**Firma Lean4**:

```lean
noncomputable def isRelation (R : U) : Prop :=
  ∀ (z : U), (z ∈ R) ↔ (isOrderedPair z)
```

**Dependencias**: `isOrderedPair`

#### Relación en Conjunto (isRelation_in_Set)

**Ubicación**: `Pairing.lean`, línea 351  
**Orden**: 2º predicado

**Enunciado Matemático**: R es una relación en A × B si todo elemento de R es un par ordenado ⟨x,y⟩ con x ∈ A y y ∈ B.

**Firma Lean4**:

```lean
noncomputable def isRelation_in_Set (A B R : U) : Prop :=
  ∀ (z : U), z ∈ R → ∃ (x y : U), z = ⟨ x , y ⟩ ∧ x ∈ A ∧ y ∈ B
```

**Dependencias**: `OrderedPair`

#### Relación en Conjuntos (isRelation_in_Sets)

**Ubicación**: `Pairing.lean`, línea 354  
**Orden**: 3º predicado

**Enunciado Matemático**: R es una relación en A × B (versión implicativa).

**Firma Lean4**:

```lean
noncomputable def isRelation_in_Sets (A B R : U) : Prop :=
  ∀ (z : U), z ∈ R → ∃ (x y : U), z = ⟨ x , y ⟩ → x ∈ A ∧ y ∈ B
```

**Dependencias**: `OrderedPair`

#### Par Ordenado Inverso (ReverseOrderedPair)

**Ubicación**: `Pairing.lean`, línea 357  
**Orden**: 4º predicado

**Enunciado Matemático**: El par ordenado inverso de w: {snd w, fst w}.

**Firma Lean4**:

```lean
noncomputable def ReverseOrderedPair (w : U) : U := { snd w , fst w }
```

**Dependencias**: `fst`, `snd`, `PairSet`

#### Relación Inversa (isReverseRelation)

**Ubicación**: `Pairing.lean`, línea 359  
**Orden**: 5º predicado

**Enunciado Matemático**: R es la relación inversa de S si w ∈ R ↔ ReverseOrderedPair(w) ∈ S.

**Firma Lean4**:

```lean
noncomputable def isReverseRelation (R S : U) : Prop :=
  ∀ (w : U), w ∈ R ↔ (ReverseOrderedPair w) ∈ S
```

**Dependencias**: `ReverseOrderedPair`

#### Relación Identidad (isIdRelation)

**Ubicación**: `Pairing.lean`, línea 362  
**Orden**: 6º predicado

**Enunciado Matemático**: I es una relación identidad si fst(x) = snd(x) para todo x ∈ I.

**Firma Lean4**:

```lean
noncomputable def isIdRelation (I : U) : Prop :=
  ∀ (x : U), x ∈ I → fst x = snd x
```

**Dependencias**: `fst`, `snd`

#### En Composición (isInComposition)

**Ubicación**: `Pairing.lean`, línea 365  
**Orden**: 7º predicado

**Enunciado Matemático**: w está en la composición de R y S.

**Firma Lean4**:

```lean
noncomputable def isInComposition (R S w : U) : Prop :=
  ∃ (W : U), w ∈ W ↔ ∃ (r : U), r ∈ R → ∃ (s : U), s ∈ S → snd r = fst s ∧ w = ⟨ fst r , snd s ⟩
```

**Dependencias**: `fst`, `snd`, `OrderedPair`

#### Reflexiva (isReflexive)

**Ubicación**: `Pairing.lean`, línea 368  
**Orden**: 8º predicado

**Enunciado Matemático**: w es reflexiva si ⟨x,y⟩ ∈ w implica ⟨x,x⟩ ∈ w.

**Firma Lean4**:

```lean
noncomputable def isReflexive (w : U) : Prop :=
  ∃ (x y : U), ⟨ x , y ⟩ ∈ w → ⟨ x , x ⟩ ∈ w
```

**Dependencias**: `OrderedPair`

#### Reflexiva en Conjunto (isReflexive_in_Set)

**Ubicación**: `Pairing.lean`, línea 371  
**Orden**: 9º predicado

**Enunciado Matemático**: R es reflexiva en A si para todo x ∈ A, ⟨x,x⟩ ∈ R.

**Firma Lean4**:

```lean
noncomputable def isReflexive_in_Set ( A R : U ) : Prop :=
  ∃ (x : U), x ∈ A → ⟨ x , x ⟩ ∈ R
```

**Dependencias**: `OrderedPair`

#### Irreflexiva (isIReflexive)

**Ubicación**: `Pairing.lean`, línea 374  
**Orden**: 10º predicado

**Enunciado Matemático**: w es irreflexiva si ⟨x,x⟩ ∉ w para todo x.

**Firma Lean4**:

```lean
noncomputable def isIReflexive (w : U) : Prop :=
  ∀ (x : U), ⟨ x , x ⟩ ∉ w
```

**Dependencias**: `OrderedPair`

#### Simétrica (isSymmetric)

**Ubicación**: `Pairing.lean`, línea 377  
**Orden**: 11º predicado

**Enunciado Matemático**: w es simétrica si ⟨x,y⟩ ∈ w implica ⟨y,x⟩ ∈ w.

**Firma Lean4**:

```lean
noncomputable def isSymmetric (w : U) : Prop :=
  ∀ (x y : U), ⟨ x , y ⟩ ∈ w → ⟨ y , x ⟩ ∈ w
```

**Dependencias**: `OrderedPair`

#### Asimétrica (isAsymmetric)

**Ubicación**: `Pairing.lean`, línea 380  
**Orden**: 12º predicado

**Enunciado Matemático**: w es asimétrica si ⟨x,y⟩ ∈ w implica ⟨y,x⟩ ∉ w.

**Firma Lean4**:

```lean
noncomputable def isAsymmetric (w : U) : Prop :=
  ∀ (x y : U), ⟨ x , y ⟩ ∈ w → ⟨ y , x ⟩ ∉ w
```

**Dependencias**: `OrderedPair`

#### Antisimétrica (isAntiSymmetric)

**Ubicación**: `Pairing.lean`, línea 383  
**Orden**: 13º predicado

**Enunciado Matemático**: w es antisimétrica si ⟨x,y⟩ ∈ w y ⟨y,x⟩ ∈ w implica x = y.

**Firma Lean4**:

```lean
noncomputable def isAntiSymmetric (w : U) : Prop :=
  ∀ (x y : U), ⟨ x , y ⟩ ∈ w → ⟨ y , x ⟩ ∈ w → x = y
```

**Dependencias**: `OrderedPair`

#### Transitiva (isTransitive)

**Ubicación**: `Pairing.lean`, línea 386  
**Orden**: 14º predicado

**Enunciado Matemático**: w es transitiva si ⟨x,y⟩ ∈ w y ⟨y,z⟩ ∈ w implica ⟨x,z⟩ ∈ w.

**Firma Lean4**:

```lean
noncomputable def isTransitive (w : U) : Prop :=
  ∀ (x y z : U), ⟨ x , y ⟩ ∈ w → ⟨ y , z ⟩ ∈ w → ⟨ x , z ⟩ ∈ w
```

**Dependencias**: `OrderedPair`

#### Relación de Equivalencia (isEquivalenceRelation)

**Ubicación**: `Pairing.lean`, línea 389  
**Orden**: 15º predicado

**Enunciado Matemático**: w es una relación de equivalencia si es reflexiva, simétrica y transitiva.

**Firma Lean4**:

```lean
noncomputable def isEquivalenceRelation (w : U) : Prop :=
  isReflexive w ∧ isSymmetric w ∧ isTransitive w
```

**Dependencias**: `isReflexive`, `isSymmetric`, `isTransitive`

#### Relación de Equivalencia en Conjunto (isEquivalenceRelation_in_Set)

**Ubicación**: `Pairing.lean`, línea 392  
**Orden**: 16º predicado

**Enunciado Matemático**: R es una relación de equivalencia en A.

**Firma Lean4**:

```lean
noncomputable def isEquivalenceRelation_in_Set (A R : U) : Prop :=
  isReflexive_in_Set A R ∧ isSymmetric R ∧ isTransitive R
```

**Dependencias**: `isReflexive_in_Set`, `isSymmetric`, `isTransitive`

#### Orden Parcial (isPartialOrder)

**Ubicación**: `Pairing.lean`, línea 395  
**Orden**: 17º predicado

**Enunciado Matemático**: R es un orden parcial si es reflexiva, antisimétrica y transitiva.

**Firma Lean4**:

```lean
noncomputable def isPartialOrder (R : U) : Prop :=
  isReflexive R ∧ isAntiSymmetric R ∧ isTransitive R
```

**Dependencias**: `isReflexive`, `isAntiSymmetric`, `isTransitive`

#### Orden Estricto (isStrictOrder)

**Ubicación**: `Pairing.lean`, línea 398  
**Orden**: 18º predicado

**Enunciado Matemático**: R es un orden estricto si es asimétrica y transitiva.

**Firma Lean4**:

```lean
noncomputable def isStrictOrder (R : U) : Prop :=
  isAsymmetric R ∧ isTransitive R
```

**Dependencias**: `isAsymmetric`, `isTransitive`

#### Bien Definida (isWellDefined)

**Ubicación**: `Pairing.lean`, línea 401  
**Orden**: 19º predicado

**Enunciado Matemático**: R es bien definida si ⟨x,y₁⟩ ∈ R y ⟨x,y₂⟩ ∈ R implica y₁ = y₂.

**Firma Lean4**:

```lean
noncomputable def isWellDefined (R : U) : Prop :=
  ∀ (x y₁ y₂ : U), ⟨ x , y₁ ⟩ ∈ R → ⟨ x , y₂ ⟩ ∈ R → y₁ = y₂
```

**Dependencias**: `OrderedPair`

#### Orden Total (isTotalOrder)

**Ubicación**: `Pairing.lean`, línea 404  
**Orden**: 20º predicado

**Enunciado Matemático**: R es un orden total si es orden parcial y para x ≠ y, ⟨x,y⟩ ∈ R o ⟨y,x⟩ ∈ R.

**Firma Lean4**:

```lean
noncomputable def isTotalOrder (R : U) : Prop :=
  isPartialOrder R ∧ ∀ (x y : U), x ≠ y → ⟨ x , y ⟩ ∈ R ∨ ⟨ y , x ⟩ ∈ R
```

**Dependencias**: `isPartialOrder`, `OrderedPair`

#### Bien Fundada (isWellFounded)

**Ubicación**: `Pairing.lean`, línea 407  
**Orden**: 21º predicado

**Enunciado Matemático**: R es bien fundada si todo subconjunto no vacío tiene un elemento minimal.

**Firma Lean4**:

```lean
noncomputable def isWellFounded (R : U) : Prop :=
  ∀ (A : U), A ≠ ∅ → ∃ (x : U), x ∈ A ∧ ∀ (y : U), ⟨ y , x ⟩ ∈ R → y ∉ A
```

**Dependencias**: `EmptySet`, `OrderedPair`

#### Función (isFunction)

**Ubicación**: `Pairing.lean`, línea 410  
**Orden**: 22º predicado

**Enunciado Matemático**: R es una función en A si para todo x ∈ A existe único y tal que ⟨x,y⟩ ∈ R.

**Firma Lean4**:

```lean
noncomputable def isFunction (A R : U) : Prop :=
  ∀ (x : U), x ∈ A → ∃ (y₁ : U), ∀ (y₂ : U), ⟨ x , y₁ ⟩ ∈ R → ⟨ x , y₂ ⟩ ∈ R → y₁ = y₂
```

**Dependencias**: `OrderedPair`

#### Inyectiva (isInyective)

**Ubicación**: `Pairing.lean`, línea 413  
**Orden**: 23º predicado

**Enunciado Matemático**: R es inyectiva si ⟨x₁,y⟩ ∈ R y ⟨x₂,y⟩ ∈ R implica x₁ = x₂.

**Firma Lean4**:

```lean
noncomputable def isInyective (R : U) : Prop :=
  ∀ (x₁ x₂ : U), ∃ (y : U), ⟨ x₁ , y ⟩ ∈ R → ⟨ x₂ , y ⟩ ∈ R → x₁ = x₂
```

**Dependencias**: `OrderedPair`

#### Función Suryectiva (isSurjectiveFunction)

**Ubicación**: `Pairing.lean`, línea 416  
**Orden**: 24º predicado

**Enunciado Matemático**: R es suryectiva de A a B si para todo y ∈ B existe x ∈ A con ⟨x,y⟩ ∈ R.

**Firma Lean4**:

```lean
noncomputable def isSurjectiveFunction (A B R : U) : Prop :=
  ∀ (y : U), y ∈ B → ∃ (x : U), x ∈ A ∧ ⟨ x , y ⟩ ∈ R
```

**Dependencias**: `OrderedPair`

#### Función Biyectiva (isBijectiveFunction)

**Ubicación**: `Pairing.lean`, línea 419  
**Orden**: 25º predicado

**Enunciado Matemático**: R es biyectiva de A a B si es función, inyectiva y suryectiva.

**Firma Lean4**:

```lean
noncomputable def isBijectiveFunction (A B R : U) : Prop :=
  isFunction A R ∧ isInyective R ∧ isSurjectiveFunction A B R
```

**Dependencias**: `isFunction`, `isInyective`, `isSurjectiveFunction`

### 3.6 Union.lean

#### Unión de Familia (sUnion)

**Ubicación**: `Union.lean`, línea 35  
**Orden**: 1ª definición principal

**Enunciado Matemático**: El conjunto de todos los elementos que pertenecen a algún conjunto de la familia C.

**Firma Lean4**:

```lean
@[simp] noncomputable def sUnion (C : U) : U :=
  choose (sUnion_existsUnique C)
notation " ⋃ " C: 100 => sUnion C
```

**Dependencias**: `Union`, `ExtSet`

#### Unión Binaria (union)

**Ubicación**: `Union.lean`, línea 158  
**Orden**: 2ª definición principal

**Enunciado Matemático**: El conjunto de elementos que están en A o en B (o en ambos).

**Firma Lean4**:

```lean
noncomputable def union (A B : U) : U := sUnion (PairSet A B)
notation:50 lhs:51 " ∪ " rhs:51 => union lhs rhs
```

**Dependencias**: `sUnion`, `PairSet`

### 3.7 PowerSet.lean

#### Existencia Única del Conjunto Potencia (powersetExistsUnique)

**Ubicación**: `PowerSet.lean`, línea 28  
**Orden**: 1ª definición

**Enunciado Matemático**: Para todo conjunto A, existe un único conjunto P tal que x ∈ P ↔ x ⊆ A.

**Firma Lean4**:

```lean
@[simp] theorem powersetExistsUnique (A : U) :
  ∃! P, ∀ x : U, x ∈ P ↔ x ⊆ A
```

**Dependencias**: `PowerSet`, `ExtSet`

#### Conjunto Potencia (powerset)

**Ubicación**: `PowerSet.lean`, línea 40  
**Orden**: 2ª definición principal

**Enunciado Matemático**: El conjunto potencia de A, denotado 𝒫(A), es el conjunto de todos los subconjuntos de A.

**Firma Lean4**:

```lean
@[simp] noncomputable def powerset (A : U) : U :=
  (powersetExistsUnique A).choose
notation " 𝒫 " A: 100 => powerset A
```

**Dependencias**: `powersetExistsUnique`, `Classical.choose`

**Notación**: `𝒫 A` para `powerset A`

### 3.8 SetOps.CartesianProduct.lean

#### Producto Cartesiano (SetOps.CartesianProduct)

**Ubicación**: `SetOps.CartesianProduct.lean`, línea 25  
**Orden**: 1ª definición principal

**Enunciado Matemático**: El producto cartesiano A × B es el conjunto de todos los pares ordenados ⟨a,b⟩ donde a ∈ A y b ∈ B.

**Firma Lean4**:

```lean
noncomputable def SetOps.CartesianProduct (A B : U) : U :=
  sep (𝒫 (𝒫 (A ∪ B))) (fun p => isOrderedPair p ∧ fst p ∈ A ∧ snd p ∈ B)
notation:70 A:71 " ×ₛ " B:71 => SetOps.CartesianProduct A B
```

**Dependencias**: `sep`, `PowerSet`, `union`, `isOrderedPair`, `fst`, `snd`

### 3.9 Relations.lean

#### Relación en un Conjunto (isRelationOn)

**Ubicación**: `SetOps.Relations.lean`, línea 44  
**Orden**: 1ª definición principal

**Enunciado Matemático**: R es una relación en A si R ⊆ A × A.

**Firma Lean4**:

```lean
def isRelationOn (R A : U) : Prop := R ⊆ (A ×ₛ A)
```

**Dependencias**: `subset`, `SetOps.CartesianProduct`

#### Relación de A a B (isRelationFrom)

**Ubicación**: `SetOps.Relations.lean`, línea 47  
**Orden**: 2ª definición principal

**Enunciado Matemático**: R es una relación de A a B si R ⊆ A × B.

**Firma Lean4**:

```lean
def isRelationFrom (R A B : U) : Prop := R ⊆ (A ×ₛ B)
```

**Dependencias**: `subset`, `SetOps.CartesianProduct`

#### R Relaciona x con y (Related)

**Ubicación**: `SetOps.Relations.lean`, línea 50  
**Orden**: 3ª definición principal

**Enunciado Matemático**: R relaciona x con y si ⟨x, y⟩ ∈ R.

**Firma Lean4**:

```lean
def Related (R x y : U) : Prop := ⟨x, y⟩ ∈ R
```

**Dependencias**: `OrderedPair`, `mem`

#### Reflexividad (isReflexiveOn)

**Ubicación**: `SetOps.Relations.lean`, línea 54  
**Orden**: 4ª definición principal

**Enunciado Matemático**: R es reflexiva en A si ∀x ∈ A, (x,x) ∈ R.

**Firma Lean4**:

```lean
def isReflexiveOn (R A : U) : Prop :=
  ∀ x : U, x ∈ A → ⟨x, x⟩ ∈ R
```

**Dependencias**: `OrderedPair`

#### Irreflexividad (isIrreflexiveOn)

**Ubicación**: `SetOps.Relations.lean`, línea 58  
**Orden**: 5ª definición principal

**Enunciado Matemático**: R es irreflexiva en A si ∀x ∈ A, (x,x) ∉ R.

**Firma Lean4**:

```lean
def isIrreflexiveOn (R A : U) : Prop :=
  ∀ x : U, x ∈ A → ⟨x, x⟩ ∉ R
```

**Dependencias**: `OrderedPair`

#### Simetría (isSymmetricOn)

**Ubicación**: `SetOps.Relations.lean`, línea 62  
**Orden**: 6ª definición principal

**Enunciado Matemático**: R es simétrica en A si ∀x,y ∈ A, (x,y) ∈ R → (y,x) ∈ R.

**Firma Lean4**:

```lean
def isSymmetricOn (R A : U) : Prop :=
  ∀ x y : U, x ∈ A → y ∈ A → ⟨x, y⟩ ∈ R → ⟨y, x⟩ ∈ R
```

**Dependencias**: `OrderedPair`

#### Antisimetría (isAntiSymmetricOn)

**Ubicación**: `SetOps.Relations.lean`, línea 66  
**Orden**: 7ª definición principal

**Enunciado Matemático**: R es antisimétrica en A si ∀x,y ∈ A, (x,y) ∈ R ∧ (y,x) ∈ R → x = y.

**Firma Lean4**:

```lean
def isAntiSymmetricOn (R A : U) : Prop :=
  ∀ x y : U, x ∈ A → y ∈ A → ⟨x, y⟩ ∈ R → ⟨y, x⟩ ∈ R → x = y
```

**Dependencias**: `OrderedPair`

#### Asimetría (isAsymmetricOn)

**Ubicación**: `SetOps.Relations.lean`, línea 70  
**Orden**: 8ª definición principal

**Enunciado Matemático**: R es asimétrica en A si ∀x,y ∈ A, (x,y) ∈ R → (y,x) ∉ R.

**Firma Lean4**:

```lean
def isAsymmetricOn (R A : U) : Prop :=
  ∀ x y : U, x ∈ A → y ∈ A → ⟨x, y⟩ ∈ R → ⟨y, x⟩ ∉ R
```

**Dependencias**: `OrderedPair`

#### Transitividad (isTransitiveOn)

**Ubicación**: `SetOps.Relations.lean`, línea 74  
**Orden**: 9ª definición principal

**Enunciado Matemático**: R es transitiva en A si ∀x,y,z ∈ A, (x,y) ∈ R ∧ (y,z) ∈ R → (x,z) ∈ R.

**Firma Lean4**:

```lean
def isTransitiveOn (R A : U) : Prop :=
  ∀ x y z : U, x ∈ A → y ∈ A → z ∈ A → ⟨x, y⟩ ∈ R → ⟨y, z⟩ ∈ R → ⟨x, z⟩ ∈ R
```

**Dependencias**: `OrderedPair`

#### Conexidad (isConnectedOn)

**Ubicación**: `SetOps.Relations.lean`, línea 78  
**Orden**: 10ª definición principal

**Enunciado Matemático**: R es conexa (total) en A si ∀x≠y ∈ A, (x,y) ∈ R ∨ (y,x) ∈ R.

**Firma Lean4**:

```lean
def isConnectedOn (R A : U) : Prop :=
  ∀ x y : U, x ∈ A → y ∈ A → x ≠ y → ⟨x, y⟩ ∈ R ∨ ⟨y, x⟩ ∈ R
```

**Dependencias**: `OrderedPair`

#### Conexidad Fuerte (isStronglyConnectedOn)

**Ubicación**: `SetOps.Relations.lean`, línea 82  
**Orden**: 11ª definición principal

**Enunciado Matemático**: R es fuertemente conexa en A si ∀x,y ∈ A, (x,y) ∈ R ∨ (y,x) ∈ R.

**Firma Lean4**:

```lean
def isStronglyConnectedOn (R A : U) : Prop :=
  ∀ x y : U, x ∈ A → y ∈ A → ⟨x, y⟩ ∈ R ∨ ⟨y, x⟩ ∈ R
```

**Dependencias**: `OrderedPair`

#### Tricotomía (isTrichotomousOn)

**Ubicación**: `SetOps.Relations.lean`, línea 86  
**Orden**: 12ª definición principal

**Enunciado Matemático**: R es tricotómica en A si ∀x,y ∈ A, exactamente una de: x < y, x = y, y < x.

**Firma Lean4**:

```lean
def isTrichotomousOn (R A : U) : Prop :=
  ∀ x y : U, x ∈ A → y ∈ A →
    (⟨x, y⟩ ∈ R ∧ x ≠ y ∧ ⟨y, x⟩ ∉ R) ∨
    (⟨x, y⟩ ∉ R ∧ x = y ∧ ⟨y, x⟩ ∉ R) ∨
    (⟨x, y⟩ ∉ R ∧ x ≠ y ∧ ⟨y, x⟩ ∈ R)
```

**Dependencias**: `OrderedPair`

#### Relación de Equivalencia (isEquivalenceOn)

**Ubicación**: `SetOps.Relations.lean`, línea 94  
**Orden**: 13ª definición principal

**Enunciado Matemático**: R es relación de equivalencia en A si es reflexiva, simétrica y transitiva.

**Firma Lean4**:

```lean
def isEquivalenceOn (R A : U) : Prop :=
  isRelationOn R A ∧ isReflexiveOn R A ∧ isSymmetricOn R A ∧ isTransitiveOn R A
```

**Dependencias**: `isRelationOn`, `isReflexiveOn`, `isSymmetricOn`, `isTransitiveOn`

#### Preorden (isPreorderOn)

**Ubicación**: `SetOps.Relations.lean`, línea 98  
**Orden**: 14ª definición principal

**Enunciado Matemático**: R es un preorden en A si es reflexiva y transitiva.

**Firma Lean4**:

```lean
def isPreorderOn (R A : U) : Prop :=
  isRelationOn R A ∧ isReflexiveOn R A ∧ isTransitiveOn R A
```

**Dependencias**: `isRelationOn`, `isReflexiveOn`, `isTransitiveOn`

#### Orden Parcial (isPartialOrderOn)

**Ubicación**: `SetOps.Relations.lean`, línea 102  
**Orden**: 15ª definición principal

**Enunciado Matemático**: R es orden parcial en A si es reflexiva, antisimétrica y transitiva.

**Firma Lean4**:

```lean
def isPartialOrderOn (R A : U) : Prop :=
  isRelationOn R A ∧ isReflexiveOn R A ∧ isAntiSymmetricOn R A ∧ isTransitiveOn R A
```

**Dependencias**: `isRelationOn`, `isReflexiveOn`, `isAntiSymmetricOn`, `isTransitiveOn`

#### Orden Lineal (isLinearOrderOn)

**Ubicación**: `SetOps.Relations.lean`, línea 106  
**Orden**: 16ª definición principal

**Enunciado Matemático**: R es orden lineal (total) en A si es orden parcial y conexa.

**Firma Lean4**:

```lean
def isLinearOrderOn (R A : U) : Prop :=
  isPartialOrderOn R A ∧ isConnectedOn R A
```

**Dependencias**: `isPartialOrderOn`, `isConnectedOn`

#### Orden Estricto (isStrictOrderOn)

**Ubicación**: `SetOps.Relations.lean`, línea 110  
**Orden**: 17ª definición principal

**Enunciado Matemático**: R es orden estricto en A si es irreflexiva y transitiva.

**Firma Lean4**:

```lean
def isStrictOrderOn (R A : U) : Prop :=
  isRelationOn R A ∧ isIrreflexiveOn R A ∧ isTransitiveOn R A
```

**Dependencias**: `isRelationOn`, `isIrreflexiveOn`, `isTransitiveOn`

#### Orden Parcial Estricto (isStrictPartialOrderOn)

**Ubicación**: `SetOps.Relations.lean`, línea 114  
**Orden**: 18ª definición principal

**Enunciado Matemático**: R es orden parcial estricto en A si es asimétrica y transitiva.

**Firma Lean4**:

```lean
def isStrictPartialOrderOn (R A : U) : Prop :=
  isRelationOn R A ∧ isAsymmetricOn R A ∧ isTransitiveOn R A
```

**Dependencias**: `isRelationOn`, `isAsymmetricOn`, `isTransitiveOn`

#### Orden Lineal Estricto (isStrictLinearOrderOn)

**Ubicación**: `SetOps.Relations.lean`, línea 118  
**Orden**: 19ª definición principal

**Enunciado Matemático**: R es orden lineal estricto en A si es orden estricto y tricotómica.

**Firma Lean4**:

```lean
def isStrictLinearOrderOn (R A : U) : Prop :=
  isStrictOrderOn R A ∧ isTrichotomousOn R A
```

**Dependencias**: `isStrictOrderOn`, `isTrichotomousOn`

#### Bien Fundada (isWellFoundedOn)

**Ubicación**: `SetOps.Relations.lean`, línea 124  
**Orden**: 20ª definición principal

**Enunciado Matemático**: R es bien fundada en A si todo subconjunto no vacío tiene un elemento minimal.

**Firma Lean4**:

```lean
def isWellFoundedOn (R A : U) : Prop :=
  ∀ S : U, S ⊆ A → S ≠ ∅ → ∃ m : U, m ∈ S ∧ ∀ x : U, x ∈ S → ⟨x, m⟩ ∉ R
```

**Dependencias**: `subset`, `EmptySet`, `OrderedPair`

#### Buen Orden (isWellOrderOn)

**Ubicación**: `SetOps.Relations.lean`, línea 128  
**Orden**: 21ª definición principal

**Enunciado Matemático**: R es un buen orden en A si es orden lineal y bien fundada.

**Firma Lean4**:

```lean
def isWellOrderOn (R A : U) : Prop :=
  isLinearOrderOn R A ∧ isWellFoundedOn R A
```

**Dependencias**: `isLinearOrderOn`, `isWellFoundedOn`

#### Clase de Equivalencia (EqClass)

**Ubicación**: `SetOps.Relations.lean`, línea 134  
**Orden**: 22ª definición principal

**Enunciado Matemático**: La clase de equivalencia de a bajo R en A: {x ∈ A | (a,x) ∈ R}.

**Firma Lean4**:

```lean
noncomputable def EqClass (a R A : U) : U :=
  sep A (fun x => ⟨a, x⟩ ∈ R)
```

**Dependencias**: `sep`, `OrderedPair`

#### Conjunto Cociente (QuotientSet)

**Ubicación**: `SetOps.Relations.lean`, línea 138  
**Orden**: 23ª definición principal

**Enunciado Matemático**: El conjunto cociente A/R: el conjunto de todas las clases de equivalencia.

**Firma Lean4**:

```lean
noncomputable def QuotientSet (A R : U) : U :=
  sep (𝒫 A) (fun C => ∃ a : U, a ∈ A ∧ C = EqClass a R A)
```

**Dependencias**: `sep`, `PowerSet`, `EqClass`

#### Relación Identidad (IdRel)

**Ubicación**: `SetOps.Relations.lean`, línea 144  
**Orden**: 24ª definición principal

**Enunciado Matemático**: La relación identidad en A: {(x,x) | x ∈ A}.

**Firma Lean4**:

```lean
noncomputable def IdRel (A : U) : U :=
  sep (A ×ₛ A) (fun p => fst p = snd p)
```

**Dependencias**: `sep`, `SetOps.CartesianProduct`, `fst`, `snd`

#### Dominio de una Relación (domain)

**Ubicación**: `SetOps.Relations.lean`, línea 150  
**Orden**: 25ª definición principal

**Enunciado Matemático**: domain R = {x | ∃ y, ⟨x, y⟩ ∈ R}

**Firma Lean4**:

```lean
noncomputable def domain (R : U) : U :=
  sep (⋃(⋃ R)) (fun x => ∃ y, ⟨x, y⟩ ∈ R)
```

**Dependencias**: `sep`, `sUnion`, `OrderedPair`

#### Rango de una Relación (range)

**Ubicación**: `SetOps.Relations.lean`, línea 155  
**Orden**: 26ª definición principal

**Enunciado Matemático**: range R = {y | ∃ x, ⟨x, y⟩ ∈ R}

**Firma Lean4**:

```lean
noncomputable def range (R : U) : U :=
  sep (⋃(⋃ R)) (fun y => ∃ x, ⟨x, y⟩ ∈ R)
```

**Dependencias**: `sep`, `sUnion`, `OrderedPair`

#### Imagen de una Relación (imag)

**Ubicación**: `SetOps.Relations.lean`, línea 159  
**Orden**: 27ª definición principal

**Enunciado Matemático**: imag R = range R (alias para rango)

**Firma Lean4**:

```lean
noncomputable def imag (R : U) : U := range R
```

**Dependencias**: `range`

#### Relación Inversa (InverseRel)

**Ubicación**: `SetOps.Relations.lean`, línea 162  
**Orden**: 28ª definición principal

**Enunciado Matemático**: InverseRel R = {(y, x) | (x, y) ∈ R} (relación inversa)

**Firma Lean4**:

```lean
noncomputable def InverseRel (R : U) : U :=
  sep (range R ×ₛ domain R) (fun p => ⟨snd p, fst p⟩ ∈ R)
```

**Dependencias**: `sep`, `SetOps.CartesianProduct`, `range`, `domain`, `fst`, `snd`

**Nota Importante**: A partir de 2026-02-12 14:52, `InverseRel` usa el producto cartesiano correcto `range R ×ₛ domain R` en lugar de `𝒫 (𝒫 (⋃(⋃ R)))` para ser consistente con `IdRel`.

#### Dominio de una Relación (domain)

**Ubicación**: `SetOps.Relations.lean`, línea 176  
**Orden**: 11ª definición principal

**Enunciado Matemático**: domain R = {x | ∃ y, ⟨x, y⟩ ∈ R}

**Firma Lean4**:

```lean
noncomputable def domain (R : U) : U :=
  sep (⋃(⋃ R)) (fun x => ∃ y, ⟨x, y⟩ ∈ R)
```

**Dependencias**: `sep`, `sUnion`, `OrderedPair`

#### Rango de una Relación (range)

**Ubicación**: `SetOps.Relations.lean`, línea 181  
**Orden**: 12ª definición principal

**Enunciado Matemático**: range R = {y | ∃ x, ⟨x, y⟩ ∈ R}

**Firma Lean4**:

```lean
noncomputable def range (R : U) : U :=
  sep (⋃(⋃ R)) (fun y => ∃ x, ⟨x, y⟩ ∈ R)
```

**Dependencias**: `sep`, `sUnion`, `OrderedPair`

#### Imagen de una Relación (imag)

**Ubicación**: `SetOps.Relations.lean`, línea 185  
**Orden**: 13ª definición principal

**Enunciado Matemático**: imag R = range R (alias para rango)

**Firma Lean4**:

```lean
noncomputable def imag (R : U) : U := range R
```

**Dependencias**: `range`

### 3.10 Functions.lean

#### Función (IsFunction)

**Ubicación**: `SetOps.Functions.lean`, línea 32  
**Orden**: 1ª definición principal

**Enunciado Matemático**: f es una función de A a B si f ⊆ A × B, es total en A y es univaluada.

**Firma Lean4**:

```lean
def IsFunction (f A B : U) : Prop :=
  f ⊆ (A ×ₛ B) ∧
  (∀ x, x ∈ A → ∃ y, ⟨x, y⟩ ∈ f) ∧
  IsSingleValued f
```

**Dependencias**: `SetOps.CartesianProduct`, `IsSingleValued`

#### Univaluada (IsSingleValued)

**Ubicación**: `SetOps.Functions.lean`, línea 25  
**Orden**: 1ª definición principal

**Enunciado Matemático**: f es univaluada si cada x tiene a lo sumo un y tal que ⟨x,y⟩ ∈ f.

**Firma Lean4**:

```lean
def IsSingleValued (f : U) : Prop :=
  ∀ x y₁ y₂, ⟨x, y₁⟩ ∈ f → ⟨x, y₂⟩ ∈ f → y₁ = y₂
```

**Dependencias**: `OrderedPair`

#### Dominio (Dom)

**Ubicación**: `SetOps.Functions.lean`, línea 37  
**Orden**: 2ª definición principal

**Enunciado Matemático**: El dominio de f es el conjunto de primeras coordenadas: {x | ∃y, ⟨x,y⟩ ∈ f}.

**Firma Lean4**:

```lean
noncomputable def Dom (f : U) : U :=
  sep (⋃ (⋃ f)) (fun x => ∃ y, ⟨x, y⟩ ∈ f)
```

**Dependencias**: `sep`, `sUnion`

#### Rango (Ran)

**Ubicación**: `SetOps.Functions.lean`, línea 42  
**Orden**: 3ª definición principal

**Enunciado Matemático**: El rango de f es el conjunto de segundas coordenadas: {y | ∃x, ⟨x,y⟩ ∈ f}.

**Firma Lean4**:

```lean
noncomputable def Ran (f : U) : U :=
  sep (⋃ (⋃ f)) (fun y => ∃ x, ⟨x, y⟩ ∈ f)
```

**Dependencias**: `sep`, `sUnion`

#### Aplicación de Función (apply)

**Ubicación**: `SetOps.Functions.lean`, línea 58  
**Orden**: 4ª definición principal

**Enunciado Matemático**: f⦅x⦆ es el único y tal que ⟨x,y⟩ ∈ f.

**Firma Lean4**:

```lean
noncomputable def apply (f x : U) : U :=
  if h : ∃ y, ⟨x, y⟩ ∈ f then Classical.choose h else ∅
notation:max f "⦅" x "⦆" => apply f x
```

**Dependencias**: `Classical.choose`, `EmptySet`

#### Función Identidad (idFn)

**Ubicación**: `SetOps.Functions.lean`, línea 85  
**Orden**: 5ª definición principal

**Enunciado Matemático**: La función identidad en A: {⟨x,x⟩ | x ∈ A}.

**Firma Lean4**:

```lean
noncomputable def idFn (A : U) : U :=
  sep (A ×ₛ A) (fun p => ∃ x, x ∈ A ∧ p = ⟨x, x⟩)
notation:max "𝟙" A => idFn A
```

**Dependencias**: `sep`, `SetOps.CartesianProduct`, `OrderedPair`

#### Composición de Funciones (comp)

**Ubicación**: `SetOps.Functions.lean`, línea 125  
**Orden**: 6ª definición principal

**Enunciado Matemático**: La composición g ∘ f: {⟨x,z⟩ | ∃y, ⟨x,y⟩ ∈ f ∧ ⟨y,z⟩ ∈ g}.

**Firma Lean4**:

```lean
noncomputable def comp (g f : U) : U :=
  sep ((Dom f) ×ₛ (Ran g)) (fun p =>
    ∃ x z, p = ⟨x, z⟩ ∧ ∃ y, ⟨x, y⟩ ∈ f ∧ ⟨y, z⟩ ∈ g)
infixr:90 " ∘ₛ " => comp
```

**Dependencias**: `sep`, `Dom`, `Ran`, `OrderedPair`

#### Función Inversa (inv)

**Ubicación**: `SetOps.Functions.lean`, línea 129  
**Orden**: 7ª definición principal

**Enunciado Matemático**: La relación inversa: {⟨y,x⟩ | ⟨x,y⟩ ∈ f}.

**Firma Lean4**:

```lean
noncomputable def inv (f : U) : U := InverseRel f
notation:100 f "⁻¹" => inv f
```

**Dependencias**: `InverseRel`

#### Restricción de Función (restrict)

**Ubicación**: `SetOps.Functions.lean`, línea 157  
**Orden**: 8ª definición principal

**Enunciado Matemático**: La restricción de una relación f a un dominio C: f ↾ C = {p ∈ f | fst p ∈ C}.

**Firma Lean4**:

```lean
noncomputable def restrict (f C : U) : U :=
  sep f (fun p => fst p ∈ C)
notation:60 f " ↾ " C:61 => restrict f C
```

**Dependencias**: `sep`, `fst`

**Notación**: `f ↾ C` para `restrict f C`

#### Inyectividad (isInjective)

**Ubicación**: `SetOps.Functions.lean`, línea 222  
**Orden**: 9ª definición principal

**Enunciado Matemático**: f es inyectiva si diferentes entradas dan diferentes salidas.

**Firma Lean4**:

```lean
def isInjective (f : U) : Prop :=
  ∀ x₁ x₂ y, ⟨x₁, y⟩ ∈ f → ⟨x₂, y⟩ ∈ f → x₁ = x₂
```

**Dependencias**: `OrderedPair`

#### Suryectividad (isSurjectiveOnto)

**Ubicación**: `SetOps.Functions.lean`, línea 225  
**Orden**: 10ª definición principal

**Enunciado Matemático**: f es suryectiva en B si todo elemento de B está en el rango.

**Firma Lean4**:

```lean
def isSurjectiveOnto (f B : U) : Prop :=
  ∀ y, y ∈ B → ∃ x, ⟨x, y⟩ ∈ f
```

**Dependencias**: `OrderedPair`

#### Biyección (isBijection)

**Ubicación**: `SetOps.Functions.lean`, línea 228  
**Orden**: 11ª definición principal

**Enunciado Matemático**: f es biyección de A a B si es función, inyectiva y suryectiva.

**Firma Lean4**:

```lean
def isBijection (f A B : U) : Prop :=
  IsFunction f A B ∧ isInjective f ∧ isSurjectiveOnto f B
```

**Dependencias**: `IsFunction`, `isInjective`, `isSurjectiveOnto`

#### Equipotencia (isEquipotent)

**Ubicación**: `SetOps.Functions.lean`, línea 231  
**Orden**: 12ª definición principal

**Enunciado Matemático**: A y B son equipotentes si existe una biyección entre ellos.

**Firma Lean4**:

```lean
def isEquipotent (A B : U) : Prop := ∃ f, isBijection f A B
notation:50 A " ≃ₛ " B => isEquipotent A B
```

**Dependencias**: `isBijection`

#### Dominación (isDominatedBy)

**Ubicación**: `SetOps.Functions.lean`, línea 236  
**Orden**: 13ª definición principal

**Enunciado Matemático**: A es dominado por B si existe una inyección de A a B.

**Firma Lean4**:

```lean
def isDominatedBy (A B : U) : Prop :=
  ∃ f, IsFunction f A B ∧ isInjective f
notation:50 A " ≼ₛ " B => isDominatedBy A B
```

**Dependencias**: `IsFunction`, `isInjective`

#### Dominación Estricta (isStrictlyDominatedBy)

**Ubicación**: `SetOps.Functions.lean`, línea 241  
**Orden**: 14ª definición principal

**Enunciado Matemático**: A es estrictamente dominado por B si A ≼ B pero B ⊀ A.

**Firma Lean4**:

```lean
def isStrictlyDominatedBy (A B : U) : Prop :=
  (A ≼ₛ B) ∧ ¬(B ≼ₛ A)
notation:50 A " ≺ₛ " B => isStrictlyDominatedBy A B
```

**Dependencias**: `isDominatedBy`

#### Imagen Directa (image)

**Ubicación**: `SetOps.Functions.lean`, línea 207  
**Orden**: 15ª definición principal

**Enunciado Matemático**: La imagen directa f[X] = {y | ∃x ∈ X, ⟨x,y⟩ ∈ f}.

**Firma Lean4**:

```lean
noncomputable def image (f X : U) : U :=
  range (f ↾ X)
notation:90 f "[" X "]" => image f X
```

**Dependencias**: `range`, `restrict`

#### Imagen Inversa (preimage)

**Ubicación**: `SetOps.Functions.lean`, línea 212  
**Orden**: 16ª definición principal

**Enunciado Matemático**: La imagen inversa f⁻¹[Y] = {x | ∃y ∈ Y, ⟨x,y⟩ ∈ f}.

**Firma Lean4**:

```lean
noncomputable def preimage (f Y : U) : U :=
  sep (domain f) (fun x => ∃ y, ⟨x, y⟩ ∈ f ∧ y ∈ Y)
notation:90 f "⁻¹[" Y "]" => preimage f Y
```

**Dependencias**: `sep`, `domain`, `OrderedPair`

#### Inverso por Izquierda (hasLeftInverse)

**Ubicación**: `SetOps.Functions.lean` (no presente en el archivo actual)
**Orden**: Definición no encontrada en el archivo

**Enunciado Matemático**: f tiene inverso por izquierda g si g ∘ f = id en A.

**Firma Lean4**:

```lean
def hasLeftInverse (f A B g : U) : Prop :=
  IsFunction f A B ∧ IsFunction g B A ∧
  ∀ x, x ∈ A → g⦅f⦅x⦆⦆ = x
```

**Dependencias**: `IsFunction`, `apply`

#### Inverso por Derecha (hasRightInverse)

**Ubicación**: `SetOps.Functions.lean`, línea 225  
**Orden**: 12ª definición principal

**Enunciado Matemático**: f tiene inverso por derecha g si f ∘ g = id en B.

**Firma Lean4**:

```lean
def hasRightInverse (f A B g : U) : Prop :=
  IsFunction f A B ∧ IsFunction g B A ∧
  ∀ y, y ∈ B → f⦅g⦅y⦆⦆ = y
```

**Dependencias**: `IsFunction`, `apply`

#### Invertibilidad (isInvertible)

**Ubicación**: `SetOps.Functions.lean`, línea 245  
**Orden**: 13ª definición principal

**Enunciado Matemático**: f es invertible si tiene inverso bilateral.

**Firma Lean4**:

```lean
def isInvertible (f A B : U) : Prop :=
  ∃ g, hasLeftInverse f A B g ∧ hasRightInverse f A B g
```

**Dependencias**: `hasLeftInverse`, `hasRightInverse`

#### Imagen Directa (image)

**Ubicación**: `SetOps.Functions.lean`, línea 580  
**Orden**: 14ª definición principal

**Enunciado Matemático**: La imagen directa f[X] = {y | ∃x ∈ X, ⟨x,y⟩ ∈ f}.

**Firma Lean4**:

```lean
noncomputable def image (f X : U) : U :=
  sep (Ran f) (fun y => ∃ x, x ∈ X ∧ ⟨x, y⟩ ∈ f)
notation:max f "⦃" X "⦄" => image f X
```

**Dependencias**: `sep`, `Ran`, `OrderedPair`

#### Imagen Inversa (preimage)

**Ubicación**: `SetOps.Functions.lean`, línea 590  
**Orden**: 15ª definición principal

**Enunciado Matemático**: La imagen inversa f⁻¹[Y] = {x | ∃y ∈ Y, ⟨x,y⟩ ∈ f}.

**Firma Lean4**:

```lean
noncomputable def preimage (f Y : U) : U :=
  sep (Dom f) (fun x => ∃ y, y ∈ Y ∧ ⟨x, y⟩ ∈ f)
```

**Dependencias**: `sep`, `Dom`, `OrderedPair`

#### Equipotencia (isEquipotent)

**Ubicación**: `SetOps.Functions.lean`, línea 398  
**Orden**: 16ª definición principal

**Enunciado Matemático**: A y B son equipotentes si existe una biyección entre ellos.

**Firma Lean4**:

```lean
def isEquipotent (A B : U) : Prop := ∃ f, isBijection f A B
notation:50 A " ≃ₛ " B => isEquipotent A B
```

**Dependencias**: `isBijection`

#### Dominación (isDominatedBy)

**Ubicación**: `SetOps.Functions.lean`, línea 430  
**Orden**: 17ª definición principal

**Enunciado Matemático**: A es dominado por B si existe una inyección de A a B.

**Firma Lean4**:

```lean
def isDominatedBy (A B : U) : Prop :=
  ∃ f, IsFunction f A B ∧ isInjective f
notation:50 A " ≼ₛ " B => isDominatedBy A B
```

**Dependencias**: `IsFunction`, `isInjective`

#### Dominación Estricta (isStrictlyDominatedBy)

**Ubicación**: `SetOps.Functions.lean`, línea 465  
**Orden**: 18ª definición principal

**Enunciado Matemático**: A es estrictamente dominado por B si A ≼ B pero B ⊀ A.

**Firma Lean4**:

```lean
def isStrictlyDominatedBy (A B : U) : Prop :=
  (A ≼ₛ B) ∧ ¬(B ≼ₛ A)
notation:50 A " ≺ₛ " B => isStrictlyDominatedBy A B
```

**Dependencias**: `isDominatedBy`

### 3.11 BoolAlg.Basic.lean

#### Teorema de Absorción

**Ubicación**: `BoolAlg.Basic.lean`, línea 18  
**Orden**: 1º teorema principal

**Enunciado Matemático**: A ∪ (A ∩ B) = A.

**Firma Lean4**:

```lean
theorem union_inter_self (A B : U) : (A ∪ (A ∩ B)) = A
```

**Dependencias**: `union`, `inter`, `ExtSet`

#### Ley Distributiva

**Ubicación**: `BoolAlg.Basic.lean`, línea 32  
**Orden**: 2º teorema principal

**Enunciado Matemático**: A ∪ (B ∩ C) = (A ∪ B) ∩ (A ∪ C).

**Firma Lean4**:

```lean
theorem union_inter_distrib_left (A B C : U) :
  (A ∪ (B ∩ C)) = ((A ∪ B) ∩ (A ∪ C))
```

**Dependencias**: `union`, `inter`, `ExtSet`

### 3.12 BoolAlg.Atomic.lean

#### Átomo (isAtom)

**Ubicación**: `BoolAlg.Atomic.lean`, línea 32  
**Orden**: 1ª definición principal

**Enunciado Matemático**: X es un átomo en 𝒫(A) si X ≠ ∅ y no hay elementos estrictamente entre ∅ y X.

**Firma Lean4**:

```lean
def isAtom (A X : U) : Prop :=
  X ∈ 𝒫 A ∧ X ≠ ∅ ∧ ∀ Y, Y ∈ 𝒫 A → Y ⊂ X → Y = ∅
```

**Dependencias**: `PowerSet`, `EmptySet`, `ssubset`

#### Álgebra Atómica (isAtomic)

**Ubicación**: `BoolAlg.Atomic.lean`, línea 227
**Orden**: 2ª definición principal
**Computable**: No (Prop)

**Enunciado Matemático**: 𝒫(A) es atómica si todo subconjunto no vacío contiene un átomo.

**Firma Lean4**:

```lean
def isAtomic (A : U) : Prop :=
  ∀ X, X ∈ 𝒫 A → X ≠ ∅ → ∃ Y, isAtom A Y ∧ Y ⊆ X
```

**Dependencias**: `isAtom`, `PowerSet`, `EmptySet`

#### Familia de Átomos (Atoms)

**Ubicación**: `BoolAlg.Atomic.lean`, línea 201
**Orden**: 3ª definición principal
**Computable**: No (`noncomputable`)

**Enunciado Matemático**: Atoms(A) = { X ∈ 𝒫(A) | X es átomo en 𝒫(A) }.

**Firma Lean4**:

```lean
noncomputable def Atoms (A : U) : U :=
  sep (𝒫 A) (fun X => isAtom A X)
```

**Dependencias**: `isAtom`, `sep`, `PowerSet`

#### Átomo Debajo (atomBelow)

**Ubicación**: `BoolAlg.Atomic.lean`, línea 279
**Orden**: 4ª definición principal
**Computable**: No (Prop)

**Enunciado Matemático**: Y es un átomo de 𝒫(A) por debajo de X si Y es átomo en 𝒫(A) e Y ⊆ X.

**Firma Lean4**:

```lean
def atomBelow (A X Y : U) : Prop := isAtom A Y ∧ Y ⊆ X
```

**Dependencias**: `isAtom`, `ssubset`

### 3.13 Cardinality.lean

#### Conjunto Diagonal (diagSet)

**Ubicación**: `Cardinal.Basic.lean`, línea 37  
**Orden**: 1ª definición principal

**Enunciado Matemático**: El conjunto diagonal para la demostración de Cantor: { x ∈ A | x ∉ f⦅x⦆ }.

**Firma Lean4**:

```lean
noncomputable def diagSet (f A : U) : U :=
  sep A (fun x => x ∉ f⦅x⦆)
```

**Dependencias**: `sep`, `apply`

#### Función Singleton (singletonMap)

**Ubicación**: `Cardinal.Basic.lean`, línea 95  
**Orden**: 2ª definición principal

**Enunciado Matemático**: La inyección canónica de A en 𝒫(A): x ↦ {x}.

**Firma Lean4**:

```lean
noncomputable def singletonMap (A : U) : U :=
  sep (A ×ₛ 𝒫 A) (fun p => ∃ x, x ∈ A ∧ p = ⟨x, {x}⟩)
```

**Dependencias**: `sep`, `SetOps.CartesianProduct`, `PowerSet`, `OrderedPair`, `Singleton`

#### Diferencia de Conjuntos (SetDiff)

**Ubicación**: `Cardinal.Basic.lean`, línea 186  
**Orden**: 3ª definición principal

**Enunciado Matemático**: Diferencia de conjuntos: A \ B = { x ∈ A | x ∉ B }.

**Firma Lean4**:

```lean
noncomputable def SetDiff (A B : U) : U :=
  sep A (fun x => x ∉ B)
notation:70 A " ∖ " B => SetDiff A B
```

**Dependencias**: `sep`

**Notación**: `A ∖ B` para `SetDiff A B`

#### Núcleo CSB (CSB_core)

**Ubicación**: `Cardinal.Basic.lean`, línea 211  
**Orden**: 4ª definición principal

**Enunciado Matemático**: El núcleo CSB: intersección de todos los conjuntos cerrados bajo g ∘ f que contienen A \ g[B].

**Firma Lean4**:

```lean
noncomputable def CSB_core (f g A B : U) : U :=
  sep A (fun x => ∀ X, X ⊆ A → isCSB_closed f g A B X → x ∈ X)
```

**Dependencias**: `sep`, `isCSB_closed`, `subset`

#### Biyección CSB (CSB_bijection)

**Ubicación**: `Cardinal.Basic.lean`, línea 276  
**Orden**: 5ª definición principal

**Enunciado Matemático**: La biyección de Cantor-Schröder-Bernstein: h(x) = f(x) si x ∈ C, g⁻¹(x) si x ∉ C.

**Firma Lean4**:

```lean
noncomputable def CSB_bijection (f g A B : U) : U :=
  let C := CSB_core f g A B
  sep (A ×ₛ B) (fun p =>
    ∃ x y, p = ⟨x, y⟩ ∧ x ∈ A ∧
      ((x ∈ C ∧ y = f⦅x⦆) ∨ (x ∉ C ∧ ⟨y, x⟩ ∈ g)))
```

**Dependencias**: `CSB_core`, `sep`, `SetOps.CartesianProduct`, `OrderedPair`, `apply`

### 3.14 Nat.Basic.lean

#### Función Sucesor (succ)

**Ubicación**: `Nat.Basic.lean`, línea 45  
**Orden**: 1ª definición principal

**Enunciado Matemático**: La función sucesor σ(n) = n ∪ {n}.

**Firma Lean4**:

```lean
noncomputable def succ (n : U) : U := n ∪ {n}
notation "σ " n:90 => succ n
```

**Dependencias**: `union`, `Singleton`

#### Conjunto Inductivo (IsInductive)

**Ubicación**: `Nat.Basic.lean`, línea 56  
**Orden**: 2ª definición principal

**Enunciado Matemático**: I es inductivo si contiene al vacío y es cerrado bajo sucesores.

**Firma Lean4**:

```lean
def IsInductive (I : U) : Prop :=
  (∅ : U) ∈ I ∧ ∀ x, x ∈ I → (σ x) ∈ I
```

**Dependencias**: `EmptySet`, `succ`

#### Conjunto Transitivo (IsTransitive)

**Ubicación**: `Nat.Basic.lean`, línea 68  
**Orden**: 3ª definición principal

**Enunciado Matemático**: S es transitivo si cada elemento es también un subconjunto de S.

**Firma Lean4**:

```lean
def IsTransitive (S : U) : Prop :=
  ∀ x, x ∈ S → x ⊆ S
```

**Dependencias**: `subset`

#### Orden Estricto Guiado por Membresía (StrictOrderMembershipGuided)

**Ubicación**: `Nat.Basic.lean`, línea 78  
**Orden**: 4ª definición principal

**Enunciado Matemático**: El orden estricto inducido por la membresía: ∈[S] = {⟨x,y⟩ | x ∈ S ∧ y ∈ S ∧ x ∈ y}.

**Firma Lean4**:

```lean
noncomputable def StrictOrderMembershipGuided (S : U) : U :=
  sep (S ×ₛ S) (fun p => ∃ x y, p = ⟨x, y⟩ ∧ x ∈ y)
notation "∈[" S "]" => StrictOrderMembershipGuided S
```

**Dependencias**: `sep`, `SetOps.CartesianProduct`, `OrderedPair`

#### Orden Total Estricto Guiado por Membresía (isTotalStrictOrderMembershipGuided)

**Ubicación**: `Nat.Basic.lean`, línea 98  
**Orden**: 5ª definición principal

**Enunciado Matemático**: S tiene orden total estricto si es transitivo, asimétrico y tricotómico.

**Firma Lean4**:

```lean
def isTotalStrictOrderMembershipGuided (S : U) : Prop :=
  IsTransitive S ∧
  (∀ x y, x ∈ S → y ∈ S → x ∈ y → y ∉ x) ∧
  (∀ x y, x ∈ S → y ∈ S → (x ∈ y ∨ x = y ∨ y ∈ x))
```

**Dependencias**: `IsTransitive`

#### Bien Ordenado Guiado por Membresía (isWellOrderMembershipGuided)

**Ubicación**: `Nat.Basic.lean`, línea 110  
**Orden**: 6ª definición principal

**Enunciado Matemático**: S está bien ordenado si todo subconjunto no vacío tiene mínimo Y máximo.

**Firma Lean4**:

```lean
def isWellOrderMembershipGuided (S : U) : Prop :=
  ∀ T, T ⊆ S → T ≠ (∅ : U) →
    (∃ m, m ∈ T ∧ ∀ x, x ∈ T → (m = x ∨ m ∈ x)) ∧ -- Mínimo
    (∃ M, M ∈ T ∧ ∀ x, x ∈ T → (M = x ∨ x ∈ M))   -- Máximo
```

**Dependencias**: `subset`, `EmptySet`

#### Número Natural (IsNat)

**Ubicación**: `Nat.Basic.lean`, línea 125  
**Orden**: 7ª definición principal (DEFINICIÓN CENTRAL)

**Enunciado Matemático**: n es un número natural si es transitivo, tiene orden total estricto y está bien ordenado.

**Firma Lean4**:

```lean
def IsNat (n : U) : Prop :=
  IsTransitive n ∧
  isTotalStrictOrderMembershipGuided n ∧
  isWellOrderMembershipGuided n
```

**Dependencias**: `IsTransitive`, `isTotalStrictOrderMembershipGuided`, `isWellOrderMembershipGuided`

#### Segmento Inicial (IsInitialSegment)

**Ubicación**: `Nat.Basic.lean`, línea 1015  
**Orden**: 8ª definición principal

**Enunciado Matemático**: S es segmento inicial de n si S ⊆ n y es cerrado hacia abajo.

**Firma Lean4**:

```lean
def IsInitialSegment (S n : U) : Prop :=
  S ⊆ n ∧ ∀ x y, x ∈ S → y ∈ x → y ∈ S
```

**Dependencias**: `subset`

#### Naturales Específicos

**Ubicación**: `Nat.Basic.lean`, líneas 1350-1365  
**Orden**: 9ª-12ª definiciones principales

**Enunciado Matemático**: Construcción explícita de los primeros naturales.

**Firma Lean4**:

```lean
noncomputable def zero : U := (∅ : U)
noncomputable def one : U := σ (∅ : U)
noncomputable def two : U := σ one
noncomputable def three : U := σ two
```

**Dependencias**: `EmptySet`, `succ`

#### Naturales en Conjuntos Inductivos (zero/one/two/three_in_inductive)

**Ubicación**: `Nat.Basic.lean`, líneas 1372-1387  
**Orden**: 10ª-13ª teoremas

**Enunciado Matemático**: Los primeros naturales pertenecen a todo conjunto inductivo.

**Firma Lean4**:

```lean
theorem zero_in_inductive (I : U) (hI : IsInductive I) : (∅ : U) ∈ I := hI.1
theorem one_in_inductive (I : U) (hI : IsInductive I) : σ (∅ : U) ∈ I := by
  have h0 := zero_in_inductive I hI
  exact hI.2 ∅ h0
theorem two_in_inductive (I : U) (hI : IsInductive I) : σ (σ (∅ : U)) ∈ I := by
  have h1 := one_in_inductive I hI
  exact hI.2 (σ (∅ : U)) h1
theorem three_in_inductive (I : U) (hI : IsInductive I) : σ (σ (σ (∅ : U))) ∈ I := by
  have h2 := two_in_inductive I hI
  exact hI.2 (σ (σ (∅ : U))) h2
```

**Dependencias**: `IsInductive`, `succ`

#### Predecesor (predecessor)

**Ubicación**: `Nat.Basic.lean`
**Orden**: 14ª definición principal
**Namespace**: `ZFC.Nat.Basic`

**Enunciado Matemático**: El predecesor de un número natural n > 0 es el único k tal que σ k = n. Para n = ∅ (cero) devuelve ∅ por convención clásica.

**Firma Lean4**:

```lean
noncomputable def predecessor (n : U) : U :=
  if h : ∃ k : U, σ k = n then Classical.choose h else ∅
```

**Dependencias**: `succ`, `Classical.choose`

---

## 4. Teoremas Principales

### 4.1 Nat.Basic.lean - Teoremas de Propiedades Elementales

**Importancia por teorema**:

- `mem_succ_self`: medium — lema auxiliar del sucesor, usado internamente
- `subset_of_mem_succ`: medium — reformulación directa de `mem_succ_iff`
- `succ_preserves_transitivity`: high — preservación de estructura transitiva, clave para `isNat_succ`
- `isNat_zero`: high — caso base de la construcción de ℕ, pilar de inducción

#### Elemento Pertenece a su Sucesor (mem_succ_self)

**Ubicación**: `Nat.Basic.lean`, línea 355  
**Namespace**: `ZFC.Nat.Basic`

**Enunciado Matemático**: Para todo n, se tiene n ∈ σ(n). Este es el lema auxiliar fundamental del sucesor.

**Firma Lean4**:

```lean
theorem mem_succ_self (n : U) : n ∈ (σ n) := by
  rw [mem_succ_iff]
  exact Or.inr rfl
```

**Dependencias**: `mem_succ_iff`

#### Caracterización de Membresía en Sucesor (subset_of_mem_succ)

**Ubicación**: `Nat.Basic.lean`, línea 361  
**Namespace**: `ZFC.Nat.Basic`

**Enunciado Matemático**: x ∈ σ(n) ⟺ x ∈ n ∨ x = n

**Firma Lean4**:

```lean
theorem subset_of_mem_succ (n x : U) :
  x ∈ (σ n) → x ∈ n ∨ x = n := by
  intro hx
  rw [mem_succ_iff] at hx
  exact hx
```

**Dependencias**: `mem_succ_iff`

#### Preservación de Transitividad en Sucesores (succ_preserves_transitivity)

**Ubicación**: `Nat.Basic.lean`, línea 373  
**Namespace**: `ZFC.Nat.Basic`

**Enunciado Matemático**: Si n es transitivo, entonces σ(n) es transitivo.

**Firma Lean4**:

```lean
theorem succ_preserves_transitivity (n : U) (hn : IsTransitive n) :
  IsTransitive (σ n) := by
  -- Demostración por análisis de casos
  unfold IsTransitive at hn ⊢
  intro x hx y hy
  simp only [mem_succ_iff] at hx ⊢
  cases hx with
  | inl hx_in_n =>
    have hx_sub : x ⊆ n := hn x hx_in_n
    left; exact hx_sub y hy
  | inr hx_eq_n =>
    rw [hx_eq_n] at hy
    left; exact hy
```

**Dependencias**: `IsTransitive`, `mem_succ_iff`

#### Conjunto Vacío es Natural (isNat_zero)

**Ubicación**: `Nat.Basic.lean`, línea 441  
**Namespace**: `ZFC.Nat.Basic`

**Enunciado Matemático**: El conjunto vacío es un número natural.

**Firma Lean4**:

```lean
theorem isNat_zero : IsNat (∅ : U) := by
  unfold IsNat isTotalStrictOrderMembershipGuided isWellOrderMembershipGuided
  refine ⟨?_, ?_, ?_⟩
  -- Transitividad vacua
  unfold IsTransitive
  intro x hx; exfalso; exact EmptySet_is_empty x hx
  -- Orden total estricto (vacuamente)
  refine ⟨?_, ?_, ?_⟩
  -- ... (prueba vacua en todos los casos)
```

**Dependencias**: `IsNat`, `EmptySet_is_empty`

### 4.2 Nat.Basic.lean - Teoremas de Buena Fundación

**Importancia por teorema**:

- `not_mem_self`: high — irreflexividad de ∈ en naturales, pilar de buena fundación
- `not_mem_of_mem`: high — ausencia de 2-ciclos, usado en tricotomía e inyectividad
- `nat_no_three_cycle`: medium — extensión a 3-ciclos, consecuencia de los anteriores

#### Irreflexividad de Membresía (not_mem_self)

**Ubicación**: `Nat.Basic.lean`, línea 674  
**Namespace**: `ZFC.Nat.Basic`

**Enunciado Matemático**: Para todo número natural n, se tiene n ∉ n (sin usar Axioma de Regularidad).

**Firma Lean4**:

```lean
theorem not_mem_self (n : U) :
  IsNat n → n ∉ n := by
  intro ⟨_, ⟨_, hasym, _⟩, _⟩ hn_mem
  have : n ∉ n := hasym n n hn_mem hn_mem hn_mem
  exact this hn_mem
```

**Dependencias**: `IsNat`, `isTotalStrictOrderMembershipGuided`

#### Ausencia de Ciclos de Dos Elementos (not_mem_of_mem)

**Ubicación**: `Nat.Basic.lean`, línea 692  
**Namespace**: `ZFC.Nat.Basic`

**Enunciado Matemático**: No existen números naturales x, y con x ∈ y ∧ y ∈ x.

**Firma Lean4**:

```lean
theorem not_mem_of_mem (x y : U) :
  IsNat x → IsNat y → ¬(x ∈ y ∧ y ∈ x) := by
  intro hx hy hmem
  obtain ⟨hxy, hyx⟩ := hmem
  by_cases h_eq : x = y
  · rw [h_eq] at hxy
    exact not_mem_self y hy hxy
  · have ⟨_, ⟨_, y_asym, _⟩, _⟩ := hy
    have y_trans : IsTransitive y := hy.1
    have x_sub_y : x ⊆ y := y_trans x hxy
    have y_in_y : y ∈ y := x_sub_y y hyx
    exact not_mem_self y hy y_in_y
```

**Dependencias**: `IsNat`, `not_mem_self`

#### Ausencia de Ciclos de Tres Elementos (nat_no_three_cycle)

**Ubicación**: `Nat.Basic.lean`, línea 715  
**Namespace**: `ZFC.Nat.Basic`

**Enunciado Matemático**: No existen números naturales x, y, z formando un ciclo x ∈ y ∧ y ∈ z ∧ z ∈ x.

**Firma Lean4**:

```lean
theorem nat_no_three_cycle (x y z : U) :
  IsNat x → IsNat y → IsNat z → ¬(x ∈ y ∧ y ∈ z ∧ z ∈ x) := by
  intro hx hy hz hmem
  obtain ⟨hxy, hyz, hzx⟩ := hmem
  have x_trans : IsTransitive x := hx.1
  have z_sub_x : z ⊆ x := x_trans z hzx
  have hyx : y ∈ x := z_sub_x y hyz
  exact not_mem_of_mem x y hx hy ⟨hxy, hyx⟩
```

**Dependencias**: `IsNat`, `IsTransitive`, `not_mem_of_mem`

### 4.3 Nat.Basic.lean - Teoremas de Herencia Estructural

**Importancia por teorema**:

- `nat_element_is_transitive`: high — componente de `nat_element_is_nat`
- `nat_element_has_strict_total_order`: high — componente de `nat_element_is_nat`
- `nat_element_has_well_order`: high — componente de `nat_element_is_nat`
- `nat_element_is_nat`: high — **teorema fundamental**: m ∈ n → IsNat m, base de la jerarquía

#### Elementos de Naturales son Transitivos (nat_element_is_transitive)

**Ubicación**: `Nat.Basic.lean`, línea 747  
**Namespace**: `ZFC.Nat.Basic`

**Enunciado Matemático**: Si n es natural y m ∈ n, entonces m es transitivo.

**Firma Lean4**:

```lean
theorem nat_element_is_transitive (n m : U)
  (hn : IsNat n) (hm_in_n : m ∈ n) :
  IsTransitive m := by
  -- Demostración por tricotomía y análisis de casos exhaustivo
  obtain ⟨hn_trans, ⟨hn_self, hn_asym, hn_trich⟩, hn_wo⟩ := hn
  have hn_reconstructed : IsNat n := ⟨hn_trans, ⟨hn_self, hn_asym, hn_trich⟩, hn_wo⟩
  unfold IsTransitive at hn_trans ⊢
  intro k hk_in_m
  have hm_sub_n : m ⊆ n := hn_trans m hm_in_n
  have hk_in_n : k ∈ n := hm_sub_n k hk_in_m
  have hk_sub_n : k ⊆ n := hn_trans k hk_in_n
  intro l hl_in_k
  -- ... (análisis completo de tricotomía)
```

**Dependencias**: `IsNat`, `IsTransitive`, `isTotalStrictOrderMembershipGuided`

#### Elementos de Naturales Tienen Orden Total (nat_element_has_strict_total_order)

**Ubicación**: `Nat.Basic.lean`, línea 870  
**Namespace**: `ZFC.Nat.Basic`

**Enunciado Matemático**: Si n es natural y m ∈ n, entonces m tiene orden total estricto.

**Firma Lean4**:

```lean
theorem nat_element_has_strict_total_order (n m : U)
  (hn : IsNat n) (hm_in_n : m ∈ n) :
  isTotalStrictOrderMembershipGuided m := by
  obtain ⟨hn_trans, ⟨hn_self, hn_asym, hn_trich⟩, hn_wo⟩ := hn
  have hn_reconstructed : IsNat n := ⟨hn_trans, ⟨hn_self, hn_asym, hn_trich⟩, hn_wo⟩
  unfold isTotalStrictOrderMembershipGuided
  have hm_sub_n : m ⊆ n := hn_trans m hm_in_n
  refine ⟨?_, ?_, ?_⟩
  · exact nat_element_is_transitive n m hn_reconstructed hm_in_n
  · intro x y hx_in_m hy_in_m hxy
    have hx_in_n : x ∈ n := hm_sub_n x hx_in_m
    have hy_in_n : y ∈ n := hm_sub_n y hy_in_m
    exact hn_asym x y hx_in_n hy_in_n hxy
  · intro x y hx_in_m hy_in_m
    have hx_in_n : x ∈ n := hm_sub_n x hx_in_m
    have hy_in_n : y ∈ n := hm_sub_n y hy_in_m
    have htrich_n : x ∈ y ∨ x = y ∨ y ∈ x := hn_trich x y hx_in_n hy_in_n
    exact htrich_n
```

**Dependencias**: `IsNat`, `isTotalStrictOrderMembershipGuided`, `nat_element_is_transitive`

#### Elementos de Naturales Están Bien Ordenados (nat_element_has_well_order)

**Ubicación**: `Nat.Basic.lean`, línea 928  
**Namespace**: `ZFC.Nat.Basic`

**Enunciado Matemático**: Si n es natural y m ∈ n, entonces m está bien ordenado (con mínimo y máximo).

**Firma Lean4**:

```lean
theorem nat_element_has_well_order (n m : U)
  (hn : IsNat n) (hm_in_n : m ∈ n) :
  isWellOrderMembershipGuided m := by
  obtain ⟨hn_trans, ⟨hn_self, hn_asym, hn_trich⟩, hn_wo⟩ := hn
  unfold isWellOrderMembershipGuided
  have hm_sub_n : m ⊆ n := hn_trans m hm_in_n
  intro T hT_sub_m hT_ne_empty
  have hT_sub_n : T ⊆ n := by
    intro x hx_in_T
    have hx_in_m : x ∈ m := hT_sub_m x hx_in_T
    exact hm_sub_n x hx_in_m
  obtain ⟨min, hmin_in_T, hmin_is_min⟩ := (hn_wo T hT_sub_n hT_ne_empty).1
  obtain ⟨max, hmax_in_T, hmax_is_max⟩ := (hn_wo T hT_sub_n hT_ne_empty).2
  constructor
  · exact ⟨min, hmin_in_T, hmin_is_min⟩
  · exact ⟨max, hmax_in_T, hmax_is_max⟩
```

**Dependencias**: `IsNat`, `isWellOrderMembershipGuided`

#### Teorema Fundamental: Elementos de Naturales son Naturales (nat_element_is_nat)

**Ubicación**: `Nat.Basic.lean`, línea 948  
**Namespace**: `ZFC.Nat.Basic`

**Enunciado Matemático**: Si n es natural y m ∈ n, entonces m es natural. Esto es el **teorema fundamental** que establece la jerarquía de naturales.

**Firma Lean4**:

```lean
theorem nat_element_is_nat (n m : U) :
  IsNat n → m ∈ n → IsNat m := by
  intro hn hm_in_n
  unfold IsNat
  refine ⟨?_, ?_, ?_⟩
  · exact nat_element_is_transitive n m hn hm_in_n
  · exact nat_element_has_strict_total_order n m hn hm_in_n
  · exact nat_element_has_well_order n m hn hm_in_n
```

**Dependencias**: `IsNat`, `nat_element_is_transitive`, `nat_element_has_strict_total_order`, `nat_element_has_well_order`

### 4.4 Nat.Basic.lean - Teoremas de Clausura bajo Sucesores

**Importancia por teorema**:

- `ne_succ_self`: medium — propiedad auxiliar: n ≠ σ(n)
- `succ_of_nat_has_strict_total_order`: medium — componente técnico de `isNat_succ`
- `isNat_succ`: high — **teorema clave**: clausura de ℕ bajo sucesor, axioma de Peano

#### El Sucesor No es Igual al Natural Original (ne_succ_self)

**Ubicación**: `Nat.Basic.lean`, línea 961  
**Namespace**: `ZFC.Nat.Basic`

**Enunciado Matemático**: Para todo natural n, se tiene n ≠ σ(n).

**Firma Lean4**:

```lean
theorem ne_succ_self (n : U) (hn : IsNat n) : n ≠ σ n := by
  intro h_eq
  have : n ∈ σ n := mem_succ_self n
  rw [←h_eq] at this
  exact not_mem_self n hn this
```

**Dependencias**: `IsNat`, `mem_succ_self`, `not_mem_self`

#### El Sucesor del Vacío tiene Orden Total (succ_of_nat_has_strict_total_order)

**Ubicación**: `Nat.Basic.lean`, línea 1005  
**Namespace**: `ZFC.Nat.Basic`

**Enunciado Matemático**: Si n es natural, entonces σ(n) tiene orden total estricto.

**Firma Lean4**:

```lean
theorem succ_of_nat_has_strict_total_order (n : U) (hn : IsNat n) :
  isTotalStrictOrderMembershipGuided (σ n) := by
  obtain ⟨hn_trans, ⟨hn_trans_self, hn_asym, hn_trich⟩, hn_wo⟩ := hn
  unfold isTotalStrictOrderMembershipGuided
  -- ... (análisis de casos para elementos en σ n)
```

**Dependencias**: `IsNat`, `isTotalStrictOrderMembershipGuided`, `mem_succ_iff`

#### Teorema Principal: El Sucesor de un Natural es Natural (isNat_succ)

**Ubicación**: `Nat.Basic.lean`, línea 1076  
**Namespace**: `ZFC.Nat.Basic`

**Enunciado Matemático**: Si n es natural, entonces σ(n) es natural. **Teorema clave de clausura inductiva.**

**Firma Lean4**:

```lean
theorem isNat_succ (n : U) (hn : IsNat n) : IsNat (σ n) := by
  obtain ⟨hn_trans, ⟨hn_trans_self, hn_asym, hn_trich⟩, hn_wo⟩ := hn
  have hn_reconstructed : IsNat n := ⟨hn_trans, ⟨hn_trans_self, hn_asym, hn_trich⟩, hn_wo⟩
  refine ⟨?_, ?_, ?_⟩
  · exact succ_of_nat_is_transitive n hn_reconstructed
  · exact succ_of_nat_has_strict_total_order n hn_reconstructed
  · unfold isWellOrderMembershipGuided
    intro A hA_sub hA_nonempty
    -- Proyecto A ∩ n para encontrar mínimo
    let B := A ∩ n
    have h_min : (∃ m, m ∈ A ∧ ∀ x, x ∈ A → m = x ∨ m ∈ x) := by
      by_cases hB_empty : B = (∅ : U)
      · -- Si B es vacío, A = {n}
        have hA_eq_n : A = {n} := by
          -- ... prueba de que es un singleton
        exists n; rw [hA_eq_n]
        constructor
        · apply (Singleton_is_specified n n).mpr rfl
        · intro x hx; rw [Singleton_is_specified] at hx; left; exact hx.symm
      · -- Si B no es vacío, usa mínimo de n
        have hB_sub_n : B ⊆ n := inter_subset A n |>.2
        have hB_nonempty : B ≠ (∅ : U) := hB_empty
        obtain ⟨m, hm_in_B, hm_min⟩ := (hn_wo B hB_sub_n hB_nonempty).1
        exists m
        -- ... resto de la prueba
    have h_max : (∃ M, M ∈ A ∧ ∀ x, x ∈ A → M = x ∨ x ∈ M) := by
      by_cases hn_in_A : n ∈ A
      · exists n
        constructor; exact hn_in_A
        intro x hx_in_A
        have hx_succ := hA_sub x hx_in_A
        rw [mem_succ_iff] at hx_succ
        cases hx_succ with
        | inl hx_n => right; exact hx_n
        | inr hx_eq_n => left; exact hx_eq_n.symm
      · -- n ∉ A, entonces A ⊆ n
        have hA_sub_n : A ⊆ n := by
          intro x hx
          have hx_succ := hA_sub x hx
          rw [mem_succ_iff] at hx_succ
          cases hx_succ with
          | inl hx_n => exact hx_n
          | inr hx_eq_n => rw [hx_eq_n] at hx; contradiction
        obtain ⟨M, hM_in_A, hM_max⟩ := (hn_wo A hA_sub_n hA_nonempty).2
        refine ⟨M, hM_in_A, hM_max⟩
    constructor; exact h_min; exact h_max
```

**Dependencias**: `IsNat`, `mem_succ_iff`, `inter_subset`

### 4.5 Nat.Basic.lean - Teoremas de Tricotomía y Orden

**Importancia por teorema**:

- `trichotomy`: high — resultado principal de orden en naturales, usado en toda la aritmética
- `mem_trans`: medium — transitividad de ∈, consecuencia directa de IsTransitive
- `mem_asymm`: medium — asimetría derivada de `not_mem_of_mem`
- `nat_subset_mem_or_eq`: high — equivalencia ⊆ ↔ ∈ ∨ =, clave para orden
- `succ_injective`: high — inyectividad del sucesor, axioma de Peano

#### Tricotomía entre Números Naturales (trichotomy)

**Ubicación**: `Nat.Basic.lean`, línea 1245  
**Namespace**: `ZFC.Nat.Basic`

**Enunciado Matemático**: Para cualesquiera dos números naturales n y m, se cumple exactamente una de: n ∈ m, n = m, ó m ∈ n.

**Firma Lean4**:

```lean
theorem trichotomy (n m : U) (hn : IsNat n) (hm : IsNat m) :
  n ∈ m ∨ n = m ∨ m ∈ n := by
  let k := n ∩ m
  have hk_init := inter_nat_is_initial_segment n m hn hm
  have hk_init_n : IsInitialSegment k n := hk_init.1
  have hk_init_m : IsInitialSegment k m := hk_init.2
  have h_n_cases := initial_segment_of_nat_is_eq_or_mem n k hn hk_init_n
  have h_m_cases := initial_segment_of_nat_is_eq_or_mem m k hm hk_init_m
  -- Combina casos para obtener tricotomía
  cases h_n_cases with
  | inl hk_eq_n =>
    cases h_m_cases with
    | inl hk_eq_m =>
      right; left; rw [←hk_eq_n, hk_eq_m]
    | inr hk_in_m =>
      left; rw [←hk_eq_n]; exact hk_in_m
  | inr hk_in_n =>
    cases h_m_cases with
    | inl hk_eq_m =>
      right; right; rw [←hk_eq_m]; exact hk_in_n
    | inr hk_in_m =>
      exfalso
      have hk_in_k : k ∈ k := (mem_inter_iff n m k).mpr ⟨hk_in_n, hk_in_m⟩
      have hk_nat : IsNat k := nat_element_is_nat n k hn hk_in_n
      exact not_mem_self k hk_nat hk_in_k
```

**Dependencias**: `IsNat`, `IsInitialSegment`, `initial_segment_of_nat_is_eq_or_mem`, `inter_nat_is_initial_segment`, `nat_element_is_nat`, `not_mem_self`

#### Transitividad de Membresía (mem_trans)

**Ubicación**: `Nat.Basic.lean`, línea 1301  
**Namespace**: `ZFC.Nat.Basic`

**Enunciado Matemático**: Si n ∈ m y m ∈ k (todos naturales), entonces n ∈ k.

**Firma Lean4**:

```lean
theorem mem_trans (n m k : U) (_hn : IsNat n) (_hm : IsNat m) (hk : IsNat k)
  (hnm : n ∈ m) (hmk : m ∈ k) : n ∈ k := by
  have hm_sub_k : m ⊆ k := hk.1 m hmk
  exact hm_sub_k n hnm
```

**Dependencias**: `IsNat`, `IsTransitive`

#### Asimetría de Membresía (mem_asymm)

**Ubicación**: `Nat.Basic.lean`, línea 1313  
**Namespace**: `ZFC.Nat.Basic`

**Enunciado Matemático**: Si n ∈ m (ambos naturales), entonces m ∉ n.

**Firma Lean4**:

```lean
theorem mem_asymm (n m : U) (hn : IsNat n) (hm : IsNat m)
  (hnm : n ∈ m) : m ∉ n := by
  intro hmn
  exact not_mem_of_mem n m hn hm ⟨hnm, hmn⟩
```

**Dependencias**: `IsNat`, `not_mem_of_mem`

#### Subconjunto Implica Membresía u Igualdad (nat_subset_mem_or_eq)

**Ubicación**: `Nat.Basic.lean`, línea 1333  
**Namespace**: `ZFC.Nat.Basic`

**Enunciado Matemático**: Si n ⊆ m (ambos naturales), entonces n ∈ m ∨ n = m.

**Firma Lean4**:

```lean
theorem nat_subset_mem_or_eq
  (n m : U) (hn : IsNat n) (hm : IsNat m) (h_sub : n ⊆ m) :
  n ∈ m ∨ n = m := by
  have h_trich := trichotomy n m hn hm
  cases h_trich with
  | inl h => left; exact h
  | inr h => cases h with
    | inl h => right; exact h
    | inr h_m_in_n =>
      exfalso
      have h_m_sub : m ⊆ n := hn.1 m h_m_in_n
      have h_eq : n = m := eq_of_subset_of_subset h_sub h_m_sub
      rw [h_eq] at h_m_in_n
      exact not_mem_self m hm h_m_in_n
```

**Dependencias**: `IsNat`, `trichotomy`, `eq_of_subset_of_subset`

#### El Sucesor es Inyectivo (succ_injective)

**Ubicación**: `Nat.Basic.lean`, línea 1351  
**Namespace**: `ZFC.Nat.Basic`

**Enunciado Matemático**: Si σ(n) = σ(m), entonces n = m.

**Firma Lean4**:

```lean
theorem succ_injective (n m : U) (hn : IsNat n) (hm : IsNat m)
  (h_eq : σ n = σ m) : n = m := by
  have hn_in_succ_n : n ∈ σ n := mem_succ_self n
  rw [h_eq] at hn_in_succ_n
  rw [mem_succ_iff] at hn_in_succ_n
  have hm_in_succ_m : m ∈ σ m := mem_succ_self m
  rw [←h_eq] at hm_in_succ_m
  rw [mem_succ_iff] at hm_in_succ_m
  cases hn_in_succ_n with
  | inl hn_in_m =>
    cases hm_in_succ_m with
    | inl hm_in_n =>
      exfalso; exact not_mem_of_mem n m hn hm ⟨hn_in_m, hm_in_n⟩
    | inr hm_eq_n => exact hm_eq_n.symm
  | inr hn_eq_m => exact hn_eq_m
```

**Dependencias**: `IsNat`, `mem_succ_self`, `mem_succ_iff`, `not_mem_of_mem`

### 4.6 Nat.Basic.lean - Teoremas de Finitud

**Importancia por teorema**:

- `eq_zero_or_exists_succ`: high — dicotomía fundamental: n = ∅ ∨ ∃k, n = σ(k)
- `zero_mem_of_nat_nonempty`: high — ∅ ∈ n sin Axioma de Regularidad, resultado profundo
- `nat_has_max`: high — caracterización de naturales como ordinales finitos

#### Todo Natural es Cero o Sucesor (eq_zero_or_exists_succ)

**Ubicación**: `Nat.Basic.lean`, línea 1377  
**Namespace**: `ZFC.Nat.Basic`

**Enunciado Matemático**: Para todo número natural n, se tiene n = ∅ ó ∃k, n = σ(k).

**Firma Lean4**:

```lean
theorem eq_zero_or_exists_succ (n : U) (hn : IsNat n) :
  n = ∅ ∨ ∃ k, n = σ k := by
  by_cases h_zero : n = ∅
  · left; exact h_zero
  · right
    obtain ⟨hn_trans, hn_order, hn_wo⟩ := hn
    have hn_reconstructed : IsNat n := ⟨hn_trans, hn_order, hn_wo⟩
    obtain ⟨M, hM_in, hM_max⟩ := (hn_wo n (subset_refl n) h_zero).2
    exists M
    apply ExtSet
    intro x
    constructor
    · intro hx
      cases hM_max x hx with
      | inl h_eq => rw [mem_succ_iff]; right; exact h_eq.symm
      | inr h_mem => rw [mem_succ_iff]; left; exact h_mem
    · intro hx
      rw [mem_succ_iff] at hx
      cases hx with
      | inl hx_M => exact hn_trans M hM_in x hx_M
      | inr hx_eq => rw [hx_eq]; exact hM_in
```

**Dependencias**: `IsNat`, `mem_succ_iff`, `ExtSet`, `subset_refl`

#### Teorema Fundamental: Vacío Pertenece a Todo Natural No Vacío (zero_mem_of_nat_nonempty)

**Ubicación**: `Nat.Basic.lean`, línea 1398  
**Namespace**: `ZFC.Nat.Basic`

**Enunciado Matemático**: Si n es un número natural no vacío, entonces ∅ ∈ n.

**Nota**: Este teorema se prueba **sin usar el Axioma de Regularidad**, solo mediante regresión imposible en la jerarquía de von Neumann.

**Firma Lean4**:

```lean
theorem zero_mem_of_nat_nonempty (n : U) (hn : IsNat n) (h_ne : n ≠ ∅) : (∅ : U) ∈ n := by
  obtain ⟨hn_trans, hn_order, hn_wo⟩ := hn
  have hn_reconstructed : IsNat n := ⟨hn_trans, hn_order, hn_wo⟩
  obtain ⟨m, hm_in_n, hm_min⟩ := (hn_wo n (subset_refl n) h_ne).1
  by_cases h_m_eq : m = ∅
  · rw [←h_m_eq]; exact hm_in_n
  · have hm_nat : IsNat m := nat_element_is_nat n m hn_reconstructed hm_in_n
    obtain ⟨hn_trans_m, hn_order_m, hn_wo_m⟩ := hm_nat
    obtain ⟨m', hm'_in_m, hm'_min⟩ := (hn_wo_m m (subset_refl m) h_m_eq).1
    have hm'_in_n : m' ∈ n := hn_trans m hm_in_n m' hm'_in_m
    have hm_nat : IsNat m := ⟨hn_trans_m, hn_order_m, hn_wo_m⟩
    match hm_min m' hm'_in_n with
      | Or.inl h_eq =>
        exfalso
        rw [←h_eq] at hm'_in_m
        exact not_mem_self m hm_nat hm'_in_m
      | Or.inr h_m_in_m' =>
        exfalso
        exact not_mem_of_mem m' m
          (nat_element_is_nat m m' hm_nat hm'_in_m)
          hm_nat
          ⟨hm'_in_m, h_m_in_m'⟩
```

**Dependencias**: `IsNat`, `nat_element_is_nat`, `not_mem_self`, `not_mem_of_mem`

#### Teorema de Finitud: Máximo en Subconjuntos (nat_has_max)

**Ubicación**: `Nat.Basic.lean`, línea 1296  
**Namespace**: `ZFC.Nat.Basic`

**Enunciado Matemático**: Todo subconjunto no vacío de un número natural tiene un elemento máximo. **Teorema que caracteriza los naturales como ordinales finitos.**

**Firma Lean4**:

```lean
theorem nat_has_max (n T : U) (hn : IsNat n) (hT_sub : T ⊆ n) (hT_ne : T ≠ ∅) :
  ∃ max, max ∈ T ∧ ∀ x, x ∈ T → (x ∈ max ∨ x = max) := by
  let Mx := sep T (fun x => ¬∃ y, y ∈ T ∧ x ∈ y ∧ x ≠ y)
  by_cases hMx : Mx ≠ ∅
  · -- Si hay elementos maximales
    have hMx_sub : Mx ⊆ T := by
      intro x hx; rw [mem_sep_iff] at hx; exact hx.1
    have hMx_sub_n : Mx ⊆ n := by
      intro x hx; have : x ∈ T := hMx_sub x hx; exact hT_sub x this
    obtain ⟨max, hmax_in_Mx, _⟩ := (hn.2.2 Mx hMx_sub_n hMx).1
    exists max
    have hmax_in_T : max ∈ T := hMx_sub max hmax_in_Mx
    refine ⟨hmax_in_T, ?_⟩
    intro x hx_in_T
    have hx_in_n : x ∈ n := hT_sub x hx_in_T
    have hmax_in_n : max ∈ n := hT_sub max hmax_in_T
    have htrich := hn.2.1.2.2 x max hx_in_n hmax_in_n
    cases htrich with
    | inl h => left; exact h
    | inr h => cases h with
      | inl h => right; exact h
      | inr h =>
        exfalso
        have hmax_maximal : ¬∃ y, y ∈ T ∧ max ∈ y ∧ max ≠ y := by
          rw [mem_sep_iff] at hmax_in_Mx
          exact hmax_in_Mx.2
        apply hmax_maximal
        exists x
        refine ⟨hx_in_T, h, ?_⟩
        intro h_eq
        have h_max_in_max : max ∈ max := h_eq ▸ h
        exact not_mem_self max (nat_element_is_nat n max hn hmax_in_n) h_max_in_max
  · -- Si no hay elementos maximales, usar máximo de T en n
    have hMx_empty : Mx = ∅ := not_not.mp hMx
    obtain ⟨M, hM_in_T, hM_is_max⟩ := (hn.2.2 T hT_sub hT_ne).2
    have hM_in_Mx : M ∈ Mx := by
      rw [mem_sep_iff]
      refine ⟨hM_in_T, ?_⟩
      intro ⟨y, hy_in_T, hM_in_y, hM_ne_y⟩
      have h_y_vs_M := hM_is_max y hy_in_T
      cases h_y_vs_M with
      | inl h_y_eq_M => exact hM_ne_y h_y_eq_M
      | inr h_y_in_M =>
        have hM_in_n : M ∈ n := hT_sub M hM_in_T
        have hy_in_n : y ∈ n := hT_sub y hy_in_T
        have h_asym := hn.2.1.2.1 M y hM_in_n hy_in_n hM_in_y
        exact h_asym h_y_in_M
    exfalso
    rw [hMx_empty] at hM_in_Mx
    exact EmptySet_is_empty M hM_in_Mx
```

**Dependencias**: `IsNat`, `mem_sep_iff`, `isTotalStrictOrderMembershipGuided`, `nat_element_is_nat`, `not_mem_self`

### 4.7 Nat.Basic.lean - Teoremas sobre Conjuntos Inductivos

**Importancia por teorema**:

- `nat_in_inductive_set`: high — todo natural pertenece a todo conjunto inductivo, base para ω

#### Todo Natural Pertenece a Conjuntos Inductivos (nat_in_inductive_set)

**Ubicación**: `Nat.Basic.lean`, línea 1550  
**Namespace**: `ZFC.Nat.Basic`

**Enunciado Matemático**: Si n es un número natural e I es un conjunto inductivo, entonces n ∈ I.

**Firma Lean4**:

```lean
theorem nat_in_inductive_set (n : U) (hn : IsNat n) (I : U) (hI : IsInductive I) :
  n ∈ I := by
  cases eq_zero_or_exists_succ n hn with
  | inl h_zero =>
    rw [h_zero]; exact hI.1
  | inr h_succ =>
    obtain ⟨k, hk_eq⟩ := h_succ
    have hk_in_n : k ∈ n := by rw [hk_eq]; exact mem_succ_self k
    have h_sub : n ⊆ I := nat_subset_inductive_set n hn I hI
    have hk_in_I : k ∈ I := h_sub k hk_in_n
    have h_succ_in : σ k ∈ I := hI.2 k hk_in_I
    rw [hk_eq]; exact h_succ_in
```

**Dependencias**: `IsNat`, `IsInductive`, `eq_zero_or_exists_succ`, `nat_subset_inductive_set`, `mem_succ_self`

---

### 3.15 Infinity.lean

#### Conjunto Inductivo Testigo (WitnessInductiveSet)

**Ubicación**: `Infinity.lean`, línea 55  
**Orden**: 1ª definición principal

**Enunciado Matemático**: Selección de un conjunto inductivo específico garantizado por el axioma.

**Firma Lean4**:

```lean
noncomputable def WitnessInductiveSet : U := ExistsInductiveSet.choose
```

**Dependencias**: `ExistsInductiveSet`

#### Conjunto Omega (Omega)

**Ubicación**: `Infinity.lean`, línea 64  
**Orden**: 2ª definición principal (DEFINICIÓN CENTRAL)

**Enunciado Matemático**: El conjunto de todos los números naturales, definido como la intersección de todos los conjuntos inductivos.

**Firma Lean4**:

```lean
noncomputable def Omega : U :=
  sep WitnessInductiveSet (fun x =>
    ∀ (J : U), J ⊆ WitnessInductiveSet → IsInductive J → x ∈ J)
notation "ω" => Omega
```

**Dependencias**: `sep`, `WitnessInductiveSet`, `IsInductive`

### 3.16 BoolAlg.GenDeMorgan.lean

#### Familia de Complementos (ComplementFamily)

**Ubicación**: `BoolAlg.GenDeMorgan.lean`, línea 50
**Orden**: 1ª definición principal
**Computable**: No (`noncomputable`)

**Enunciado Matemático**: Dado un universo A y una familia F de subconjuntos de A, ComplementFamily(A, F) = { A \ X | X ∈ F } ⊆ 𝒫(A).

**Firma Lean4**:

```lean
noncomputable def ComplementFamily (A F : U) : U :=
  sep (𝒫 A) (fun Y => ∃ X, X ∈ F ∧ Y = sdiff A X)
```

**Dependencias**: `sep`, `PowerSet`, `sdiff`

### 3.17 BoolAlg.GenDistributive.lean

#### Familia de Intersecciones (IntersectFamily)

**Ubicación**: `BoolAlg.GenDistributive.lean`, línea 52
**Orden**: 1ª definición principal
**Computable**: No (`noncomputable`)

**Enunciado Matemático**: IntersectFamily(A, F) = { A ∩ X | X ∈ F } ⊆ 𝒫(A).

**Firma Lean4**:

```lean
noncomputable def IntersectFamily (A F : U) : U :=
  sep (𝒫 A) (fun Y => ∃ X, X ∈ F ∧ Y = inter A X)
```

**Dependencias**: `sep`, `PowerSet`, `inter`

#### Familia de Uniones (UnionFamily)

**Ubicación**: `BoolAlg.GenDistributive.lean`, línea 74
**Orden**: 2ª definición principal
**Computable**: No (`noncomputable`)

**Enunciado Matemático**: UnionFamily(A, F) = { A ∪ X | X ∈ F } ⊆ 𝒫(A ∪ ⋃F).

**Firma Lean4**:

```lean
noncomputable def UnionFamily (A F : U) : U :=
  sep (𝒫 (A ∪ (⋃ F))) (fun Y => ∃ X, X ∈ F ∧ Y = union A X)
```

**Dependencias**: `sep`, `PowerSet`, `union`, `sUnion`

### 3.18 SetOps.SetOrder.lean

#### Cota Superior (isUpperBound)

**Ubicación**: `SetOps.SetOrder.lean`, línea 35  
**Orden**: 1ª definición principal

**Enunciado Matemático**: x es cota superior de S si todo elemento de S es subconjunto de x.

**Firma Lean4**:

```lean
def isUpperBound (S x : U) : Prop :=
  ∀ y, y ∈ S → y ⊆ x
```

**Dependencias**: `subset`

#### Cota Inferior (isLowerBound)

**Ubicación**: `SetOps.SetOrder.lean`, línea 39  
**Orden**: 2ª definición principal

**Enunciado Matemático**: x es cota inferior de S si x es subconjunto de todo elemento de S.

**Firma Lean4**:

```lean
def isLowerBound (S x : U) : Prop :=
  ∀ y, y ∈ S → x ⊆ y
```

**Dependencias**: `subset`

#### Supremo (isSupremum)

**Ubicación**: `SetOps.SetOrder.lean`, línea 43  
**Orden**: 3ª definición principal

**Enunciado Matemático**: x es supremo de S si es cota superior y la menor de todas las cotas superiores.

**Firma Lean4**:

```lean
def isSupremum (S x : U) : Prop :=
  isUpperBound S x ∧ ∀ z, isUpperBound S z → x ⊆ z
```

**Dependencias**: `isUpperBound`, `subset`

#### Ínfimo (isInfimum)

**Ubicación**: `SetOps.SetOrder.lean`, línea 47  
**Orden**: 4ª definición principal

**Enunciado Matemático**: x es ínfimo de S si es cota inferior y la mayor de todas las cotas inferiores.

**Firma Lean4**:

```lean
def isInfimum (S x : U) : Prop :=
  isLowerBound S x ∧ ∀ z, isLowerBound S z → z ⊆ x
```

**Dependencias**: `isLowerBound`, `subset`

#### Acotado Superiormente (isBoundedAbove)

**Ubicación**: `SetOps.SetOrder.lean`, línea 51  
**Orden**: 5ª definición principal

**Enunciado Matemático**: S está acotado superiormente si existe una cota superior.

**Firma Lean4**:

```lean
def isBoundedAbove (S : U) : Prop :=
  ∃ x, isUpperBound S x
```

**Dependencias**: `isUpperBound`

#### Acotado Inferiormente (isBoundedBelow)

**Ubicación**: `SetOps.SetOrder.lean`, línea 55  
**Orden**: 6ª definición principal

**Enunciado Matemático**: S está acotado inferiormente si existe una cota inferior.

**Firma Lean4**:

```lean
def isBoundedBelow (S : U) : Prop :=
  ∃ x, isLowerBound S x
```

**Dependencias**: `isLowerBound`

### 3.19 SetOps.SetStrictOrder.lean

*Nota: Este módulo no introduce nuevas definiciones principales, sino que establece propiedades del orden estricto ⊂ definido en `Extension.lean`.*

#### Orden Estricto (ssubset)

**Ubicación**: `Extension.lean`, línea 46 (definición implícita)  
**Orden**: Definición heredada

**Enunciado Matemático**: A ⊂ B si A ⊆ B y A ≠ B.

**Firma Lean4**:

```lean
-- Definición implícita: A ⊂ B ↔ (A ⊆ B ∧ A ≠ B)
notation:50 lhs:51 " ⊂ " rhs:51 => (lhs ⊆ rhs ∧ lhs ≠ rhs)
```

**Dependencias**: `subset`

### 3.20 OrderedPair.lean (Extensiones)

*Nota: Las definiciones principales del par ordenado están en `Pairing.lean`. Este módulo agrega teoremas adicionales.*

#### Igualdad de Pares Ordenados (Directa) (OrderedPair_eq_of)

**Ubicación**: `OrderedPair.lean`, línea 25  
**Orden**: 1ª definición adicional

**Enunciado Matemático**: Si a = c y b = d, entonces ⟨a,b⟩ = ⟨c,d⟩.

**Firma Lean4**:

```lean
theorem OrderedPair_eq_of (a b c d : U) :
  (a = c ∧ b = d) → ⟨a, b⟩ = ⟨c, d⟩
```

**Dependencias**: `OrderedPair`

#### Caracterización Completa de Igualdad (OrderedPair_eq_iff)

**Ubicación**: `OrderedPair.lean`, línea 32  
**Orden**: 2ª definición adicional

**Enunciado Matemático**: ⟨a,b⟩ = ⟨c,d⟩ si y solo si a = c y b = d.

**Firma Lean4**:

```lean
theorem OrderedPair_eq_iff (a b c d : U) :
  ⟨a, b⟩ = ⟨c, d⟩ ↔ (a = c ∧ b = d)
```

**Dependencias**: `OrderedPair`, `Eq_of_OrderedPairs_given_projections`, `OrderedPair_eq_of`

#### Pertenencia en Conjunto Potencia (OrderedPair_in_powerset)

**Ubicación**: `OrderedPair.lean`, línea 42  
**Orden**: 3ª definición adicional

**Enunciado Matemático**: Si a ∈ A y b ∈ B, entonces ⟨a,b⟩ ∈ 𝒫(𝒫(A ∪ B)).

**Firma Lean4**:

```lean
theorem OrderedPair_in_powerset (a b A B : U)
  (ha : a ∈ A) (hb : b ∈ B) :
    ⟨a, b⟩ ∈ 𝒫 (𝒫 (A ∪ B))
```

**Dependencias**: `OrderedPair`, `PowerSet`, `union`, `Singleton`, `PairSet`

### 3.21 BoolAlg.PowerSetAlgebra.lean

#### Complemento (Complement)

**Ubicación**: `BoolAlg.PowerSetAlgebra.lean`, línea 68  
**Orden**: 1ª definición principal

**Enunciado Matemático**: El complemento de X relativo al universo A es A \ X.

**Firma Lean4**:

```lean
noncomputable def Complement (A X : U) : U := A \ X
notation:max X:max " ^∁[ " A:max " ]" => Complement A X
```

**Dependencias**: `sdiff`

### 3.22 PeanoImport.lean

**Módulo**: `ZfcSetTheory.PeanoImport`
**Namespace**: `ZFC` (sub-namespace `ZFC.Peano.Import`)
**Dependencias**: `ZfcSetTheory.Nat.Basic`, `ZfcSetTheory.Infinity`, `PeanoNatLib.PeanoNatAxioms`, `PeanoNatLib.PeanoNatStrictOrder`, `PeanoNatLib.PeanoNatOrder`
**Librería externa**: `peanolib` — ver el [repositorio Peano en GitHub](https://github.com/julian1c2a/Peano) para la referencia técnica completa del proyecto Peano.
**Descripción**: Establece el isomorfismo completo entre los números naturales de Von Neumann y los de Peano. Contiene cuatro secciones: (1) la biyección `fromPeano`/`toPeano` con inyectividad, sobreyectividad e inversas; (2) compatibilidad con la estructura algebraica básica (`toPeano_zero`, `toPeano_succ`); (3) transporte de los teoremas de recursión (simple y con paso) entre los dos mundos; (4) puentes de orden: `fromPeano_lt_iff` y `fromPeano_le_iff` que identifican el orden estricto de Peano con la membresía en ω. **Notación**: `ΠZ p` para `fromPeano p`, `ZΠ n hn` para `toPeano n hn`.

**Abre los namespaces**: `Classical`, `ZFC.Axiom.Extension`, `ZFC.Axiom.Existence`, `ZFC.Axiom.Specification`, `ZFC.Axiom.Pairing`, `ZFC.Axiom.Union`, `ZFC.Axiom.PowerSet`, `ZFC.SetOps.OrderedPair`, `ZFC.SetOps.CartesianProduct`, `ZFC.SetOps.Relations`, `ZFC.SetOps.Functions`, `ZFC.Cardinal.Basic`, `ZFC.Nat.Basic`

#### Conversión Peano → Von Neumann (fromPeano)

**Ubicación**: `PeanoImport.lean`, línea 35
**Orden**: 1ª definición principal

**Enunciado Matemático**: Convierte un número natural de Peano `p : Peano.ℕ₀` en su representación de Von Neumann: `fromPeano(0) = ∅`, `fromPeano(succ p) = σ(fromPeano(p))`.

**Firma Lean4**:

```lean
noncomputable def fromPeano : Peano.ℕ₀ → U
  | Peano.ℕ₀.zero    => (∅ : U)
  | Peano.ℕ₀.succ n' => succ (fromPeano n')
```

**Dependencias**: `EmptySet`, `succ`, `Peano.ℕ₀`

#### Conversión Von Neumann → Peano (toPeano)

**Ubicación**: `PeanoImport.lean`, línea 96
**Orden**: 2ª definición principal

**Enunciado Matemático**: Convierte un número natural de Von Neumann `n : U` (con prueba `hn : IsNat n`) en su representante de Peano, usando elección clásica sobre `fromPeano_surjective`.

**Firma Lean4**:

```lean
noncomputable def toPeano (n : U) (hn : IsNat n) : Peano.ℕ₀ :=
  Classical.choose (fromPeano_surjective n hn)
```

**Dependencias**: `fromPeano_surjective`, `Classical.choose`, `IsNat`

### 3.23 Nat.Add.lean

**Módulo**: `ZfcSetTheory.Nat.Add`
**Namespace**: `ZFC.Nat.Add`
**Dependencias**: `Nat.Basic`, `Infinity`, `Recursion`, `PeanoImport`, `PeanoNatLib.PeanoNatAdd`
**Actualizado**: 2026-03-08 12:00
**Descripción**: Define la suma en ω mediante el Teorema de Recursión. Fijado m ∈ ω, `addFn m hm` es la función recursiva con base m y paso `succFn`. La suma se extiende sin argumento de prueba (`add m n` con valor por defecto ∅ si m ∉ ω). El teorema puente `fromPeano_add` conecta con `Peano.Add.add`, permitiendo transportar todos los teoremas algebraicos de Peano.

**Abre los namespaces**: `Classical`, todos los de ZFC hasta `Axiom.Infinity`. **No abre** `Peano.Import` para evitar ambigüedad de la notación `ΠZ`.

#### Función sucesor como conjunto ZFC (succFn)

**Ubicación**: `Nat.Add.lean`, línea 66
**Orden**: 1ª definición

**Enunciado Matemático**: `succFn = {⟨n, σ n⟩ | n ∈ ω} ⊆ ω ×ₛ ω`. Es la función ZFC que representa el sucesor.

**Firma Lean4**:

```lean
noncomputable def succFn : U :=
  sep (ω ×ₛ ω) (fun p => ∃ n, n ∈ (ω : U) ∧ p = ⟨n, σ n⟩)
```

**Dependencias**: `sep`, `ω`, `SetOps.CartesianProduct`, `OrderedPair`, `succ`

#### Función de adición fijado m (addFn)

**Ubicación**: `Nat.Add.lean`, línea 109
**Orden**: 2ª definición

**Enunciado Matemático**: `addFn m hm` es la única función ZFC `F : ω → ω` con `F(∅) = m` y `F(σ n) = σ(F(n))`, construida vía `RecursiveFn`.

**Firma Lean4**:

```lean
noncomputable def addFn (m : U) (hm : m ∈ (ω : U)) : U :=
  RecursiveFn ω m succFn hm succFn_is_function
```

**Dependencias**: `RecursiveFn`, `succFn`, `succFn_is_function`

#### Suma en ω (add)

**Ubicación**: `Nat.Add.lean`, línea 120
**Orden**: 3ª definición

**Enunciado Matemático**: `add m n = (addFn m hm)(n)` si `m ∈ ω`, y `∅` en otro caso. No lleva argumento de prueba para evitar dependencias en reescrituras algebraicas.

**Firma Lean4**:

```lean
noncomputable def add (m n : U) : U :=
  if h : m ∈ (ω : U) then apply (addFn m h) n else ∅
```

**Dependencias**: `addFn`, `apply`

---

### 3.24 Nat.Mul.lean

**Módulo**: `ZfcSetTheory.Nat.Mul`
**Namespace**: `ZFC.Nat.Mul`
**Dependencias**: `Nat.Basic`, `Infinity`, `Recursion`, `PeanoImport`, `Nat.Add`, `PeanoNatLib.PeanoNatMul`
**Actualizado**: 2026-03-08 12:00
**Descripción**: Define la multiplicación en ω mediante el Teorema de Recursión. Fijado m ∈ ω, `mulFn m hm` es la función recursiva con base ∅ y paso `addFn m hm` (cada paso de sucesor añade m). Así `mul m ∅ = ∅` y `mul m (σ n) = add m (mul m n)`. El teorema puente `fromPeano_mul` usa commutativity de la suma para adaptarse al orden de `Peano.Mul.mul_succ`.

#### Función de multiplicación fijado m (mulFn)

**Ubicación**: `Nat.Mul.lean`, línea 69
**Orden**: 1ª definición

**Enunciado Matemático**: `mulFn m hm` es la única función ZFC `F : ω → ω` con `F(∅) = ∅` y `F(σ n) = m + F(n)`, construida vía `RecursiveFn`.

**Firma Lean4**:

```lean
noncomputable def mulFn (m : U) (hm : m ∈ (ω : U)) : U :=
  RecursiveFn ω ∅ (addFn m hm) zero_in_Omega (addFn_is_function m hm)
```

**Dependencias**: `RecursiveFn`, `addFn`, `addFn_is_function`, `zero_in_Omega`

#### Multiplicación en ω (mul)

**Ubicación**: `Nat.Mul.lean`, línea 80
**Orden**: 2ª definición

**Enunciado Matemático**: `mul m n = (mulFn m hm)(n)` si `m ∈ ω`, y `∅` en otro caso. No lleva argumento de prueba.

**Firma Lean4**:

```lean
noncomputable def mul (m n : U) : U :=
  if h : m ∈ (ω : U) then apply (mulFn m h) n else ∅
```

**Dependencias**: `mulFn`, `apply`

---

### 3.25 Nat.Sub.lean

**Módulo**: `ZfcSetTheory.Nat.Sub`
**Namespace**: `ZFC.Nat.Sub`
**Dependencias**: `Nat.Basic`, `Infinity`, `Recursion`, `PeanoImport`, `Nat.Add`, `PeanoNatLib.PeanoNatSub`
**Actualizado**: 2026-03-21
**Descripción**: Define la sustracción saturada (monus) en ω mediante el Teorema de Recursión con `predecessorFn` como función de paso. Fijado m ∈ ω, `subFn m hm` aplica el predecesor n veces a m, saturando en ∅. El teorema puente `fromPeano_sub` se prueba por inducción usando el lema auxiliar `peano_sub_succ_tau : sub p (σ q) = τ (sub p q)` (válido incondicionalmente).

#### Función predecesora ZFC (predecessorFn)

**Ubicación**: `Nat.Sub.lean`, línea 73
**Orden**: 1ª definición

**Enunciado Matemático**: `predecessorFn = {⟨n, predecessor n⟩ | n ∈ ω} ⊆ ω ×ₛ ω`. Dado que `predecessor (σ n) = n` y `predecessor ∅ = ∅`, representa el predecesor saturado.

**Firma Lean4**:

```lean
noncomputable def predecessorFn : U :=
  sep (ω ×ₛ ω) (fun p => ∃ n, n ∈ (ω : U) ∧ p = ⟨n, predecessor n⟩)
```

**Dependencias**: `sep`, `SetOps.CartesianProduct`, `predecessor`

#### Función de sustracción fijado m (subFn)

**Ubicación**: `Nat.Sub.lean`, línea 122
**Orden**: 2ª definición

**Enunciado Matemático**: `subFn m hm` es la única función ZFC `F : ω → ω` con `F(∅) = m` y `F(σ n) = predecessor(F(n))`, construida vía `RecursiveFn`.

**Firma Lean4**:

```lean
noncomputable def subFn (m : U) (hm : m ∈ (ω : U)) : U :=
  RecursiveFn ω m predecessorFn hm predecessorFn_is_function
```

**Dependencias**: `RecursiveFn`, `predecessorFn`, `predecessorFn_is_function`

#### Sustracción saturada en ω (sub)

**Ubicación**: `Nat.Sub.lean`, línea 133
**Orden**: 3ª definición

**Enunciado Matemático**: `sub m n = (subFn m hm)(n)` si `m ∈ ω`, y `∅` en otro caso. No lleva argumento de prueba.

**Firma Lean4**:

```lean
noncomputable def sub (m n : U) : U :=
  if h : m ∈ (ω : U) then apply (subFn m h) n else ∅
```

**Dependencias**: `subFn`, `apply`

---

### 3.26 Nat.Div.lean

**Módulo**: `ZfcSetTheory.Nat.Div`
**Namespace**: `ZFC.Nat.Div`
**Dependencias**: `Nat.Basic`, `Infinity`, `Recursion`, `PeanoImport`, `Nat.Add`, `Nat.Mul`, `Nat.Sub`, `PeanoNatLib.PeanoNatDiv`
**Actualizado**: 2026-03-21
**Descripción**: Define la división euclídea (cociente y resto) en ω mediante Patrón B (bridge-only). Levanta `Peano.Div.div` y `Peano.Div.mod` directamente via el isomorfismo `fromPeano`/`toPeano`. El helper privado `toPeano_proof_irrel` garantiza que el resultado de `toPeano n h` no depende del testigo `h : IsNat n`.

#### Cociente euclídeo (divOf)

**Ubicación**: `Nat.Div.lean`, línea 91
**Orden**: 1ª definición

**Enunciado Matemático**: `divOf m n = ⌊m / n⌋` para `m, n ∈ ω`, definido por transporte del Peano `Peano.Div.div (toPeano m _) (toPeano n _)`.

**Firma Lean4**:

```lean
noncomputable def divOf (m n : U) : U :=
  if hm : m ∈ (ω : U) then
    if hn : n ∈ (ω : U) then
      fromPeano (Peano.Div.div
        (toPeano m (mem_Omega_is_Nat m hm))
        (toPeano n (mem_Omega_is_Nat n hn)))
    else ∅
  else ∅
```

**Dependencias**: `fromPeano`, `toPeano`, `Peano.Div.div`, `mem_Omega_is_Nat`

#### Resto euclídeo (modOf)

**Ubicación**: `Nat.Div.lean`, línea 102
**Orden**: 2ª definición

**Enunciado Matemático**: `modOf m n = m mod n` para `m, n ∈ ω`, análogo a `divOf` con `Peano.Div.mod`.

**Firma Lean4**:

```lean
noncomputable def modOf (m n : U) : U :=
  if hm : m ∈ (ω : U) then
    if hn : n ∈ (ω : U) then
      fromPeano (Peano.Div.mod
        (toPeano m (mem_Omega_is_Nat m hm))
        (toPeano n (mem_Omega_is_Nat n hn)))
    else ∅
  else ∅
```

**Dependencias**: `fromPeano`, `toPeano`, `Peano.Div.mod`, `mem_Omega_is_Nat`

### 3.27 Nat.Pow.lean

**Módulo**: `ZfcSetTheory.Nat.Pow`
**Namespace**: `ZFC.Nat.Pow`
**Dependencias**: `Nat.Basic`, `Infinity`, `Recursion`, `PeanoImport`, `Nat.Mul`, `PeanoNatLib.PeanoNatPow`
**Actualizado**: 2026-03-22
**Descripción**: Define la potenciación `pow m n = mⁿ` en ω mediante Patrón RecursiveFn. Usa `mulFn m hm` como función de paso: `powFn m = RecursiveFn ω (σ ∅) (mulFn m hm) ...`. El teorema puente `fromPeano_pow` establece compatibilidad con `Peano.Pow.pow`.

#### Función auxiliar de potenciación (powFn)

**Ubicación**: `Nat.Pow.lean`, línea 70
**Orden**: 1ª definición

**Enunciado Matemático**: `powFn m` es la función recursiva en ω con valor inicial `1 = σ ∅` y paso de recursión `mulFn m hm`. Satisface: `powFn m ⦅∅⦆ = 1` y `powFn m ⦅σ n⦆ = m * powFn m ⦅n⦆`.

**Firma Lean4**:

```lean
noncomputable def powFn (m : U) (hm : m ∈ (ω : U)) : U :=
  RecursiveFn ω (σ (∅ : U)) (mulFn m hm) (succ_in_Omega ∅ zero_in_Omega) (mulFn_is_function m hm)
```

**Dependencias**: `RecursiveFn`, `mulFn`, `mulFn_is_function`, `succ_in_Omega`

#### Potenciación (pow)

**Ubicación**: `Nat.Pow.lean`, línea 85
**Orden**: 2ª definición

**Enunciado Matemático**: `pow m n = mⁿ` para `m ∈ ω`. Devuelve `∅` si `m ∉ ω`.

**Firma Lean4**:

```lean
noncomputable def pow (m n : U) : U :=
  if h : m ∈ (ω : U) then apply (powFn m h) n else ∅
```

**Dependencias**: `powFn`, `apply`

---

### 3.28 Nat.Arith.lean

**Módulo**: `ZfcSetTheory.Nat.Arith`
**Namespace**: `ZFC.Nat.Arith`
**Dependencias**: `Nat.Basic`, `Infinity`, `Recursion`, `PeanoImport`, `Nat.Add`, `Nat.Mul`, `Nat.Sub`, `Nat.Div`, `PeanoNatLib.PeanoNatArith`
**Actualizado**: 2026-03-22
**Descripción**: Define divisibilidad en ZFC directamente y construye `div`/`mod` nativos con Patrón RecursiveFn (función de paso `divMod_stepFn`). Conecta con `divOf`/`modOf` mediante unicidad de la división euclídea. Define `gcdOf`/`lcmOf` con Patrón B (bridge-only). Prueba el teorema de Bézout (forma substractiva). No incluye Teorema Fundamental de la Aritmética (FTA se aplaza para módulo futuro de primalidad).

#### Predicado de divisibilidad (divides)

**Ubicación**: `Nat.Arith.lean`, línea 68
**Orden**: 1ª definición

**Enunciado Matemático**: `divides m n` iff ∃ k ∈ ω tal que n = m * k.

**Firma Lean4**:

```lean
def divides (m n : U) : Prop := ∃ k : U, k ∈ (ω : U) ∧ n = mul m k
```

**Dependencias**: `mul`, `ω`

#### División euclídea nativa ZFC (div)

**Ubicación**: `Nat.Arith.lean`, línea 377
**Orden**: 2ª definición pública

**Enunciado Matemático**: `div m n = ⌊m / n⌋` definido vía `RecursiveFn` en ω×ω con función de paso `divMod_stepFn n`.

**Firma Lean4**:

```lean
noncomputable def div (m n : U) : U :=
  if hm : m ∈ (ω : U) then
    if hn : n ∈ (ω : U) then fst (apply (divModFn n hn) m)
    else ∅
  else ∅
```

**Dependencias**: `divModFn` (privado), `fst`, `apply`

#### Resto euclídeo nativo ZFC (mod)

**Ubicación**: `Nat.Arith.lean`, línea 385
**Orden**: 3ª definición pública

**Firma Lean4**:

```lean
noncomputable def mod (m n : U) : U :=
  if hm : m ∈ (ω : U) then
    if hn : n ∈ (ω : U) then snd (apply (divModFn n hn) m)
    else ∅
  else ∅
```

**Dependencias**: `divModFn` (privado), `snd`, `apply`

#### MCD (gcdOf)

**Ubicación**: `Nat.Arith.lean`, línea 640
**Orden**: 4ª definición pública

**Enunciado Matemático**: `gcdOf m n = mcd(m, n)` definido por Patrón B vía isomorfismo.

**Firma Lean4**:

```lean
noncomputable def gcdOf (m n : U) : U :=
  if hm : m ∈ (ω : U) then
    if hn : n ∈ (ω : U) then
      fromPeano (Peano.Arith.gcd
        (toPeano m (mem_Omega_is_Nat m hm))
        (toPeano n (mem_Omega_is_Nat n hn)))
    else ∅
  else ∅
```

**Dependencias**: `fromPeano`, `toPeano`, `Peano.Arith.gcd`

#### MCM (lcmOf)

**Ubicación**: `Nat.Arith.lean`, línea 649
**Orden**: 5ª definición pública

**Firma Lean4**:

```lean
noncomputable def lcmOf (m n : U) : U :=
  if hm : m ∈ (ω : U) then
    if hn : n ∈ (ω : U) then
      fromPeano (Peano.Arith.lcm
        (toPeano m (mem_Omega_is_Nat m hm))
        (toPeano n (mem_Omega_is_Nat n hn)))
    else ∅
  else ∅
```

**Dependencias**: `fromPeano`, `toPeano`, `Peano.Arith.lcm`

### 3.29 Nat.Factorial.lean

**Módulo**: `ZfcSetTheory.Nat.Factorial`
**Namespace**: `ZFC.Nat.Factorial`
**Dependencias**: `Nat.Basic`, `Infinity`, `Recursion`, `PeanoImport`, `Nat.Mul`, `PeanoNatLib.PeanoNatFactorial`
**Actualizado**: 2026-03-24
**Descripción**: Define la función factorial `factorialOf n = n!` en ω mediante Patrón B (bridge-only). Levanta `Peano.Factorial.factorial` directamente via el isomorfismo `fromPeano`/`toPeano`. El helper privado `toPeano_proof_irrel` garantiza que el resultado de `toPeano n h` no depende del testigo `h : IsNat n`.

#### Factorial (factorialOf)

**Ubicación**: `Nat.Factorial.lean`, línea 76
**Orden**: Única definición pública

**Enunciado Matemático**: `factorialOf n = n!` para `n ∈ ω`, definido por transporte del Peano `Peano.Factorial.factorial (toPeano n _)`. Devuelve `∅` si `n ∉ ω`.

**Firma Lean4**:

```lean
noncomputable def factorialOf (n : U) : U :=
  if hn : n ∈ (ω : U) then
    fromPeano (Peano.Factorial.factorial (toPeano n (mem_Omega_is_Nat n hn)))
  else ∅
```

**Dependencias**: `fromPeano`, `toPeano`, `Peano.Factorial.factorial`, `mem_Omega_is_Nat`

### 3.30 Nat.Gcd.lean

**Módulo**: `ZfcSetTheory.Nat.Gcd`
**Namespace**: `ZFC.Nat.Gcd`
**Dependencias**: `Nat.Basic`, `Infinity`, `Recursion`, `PeanoImport`, `Nat.Add`, `Nat.Mul`, `Nat.Sub`, `Nat.Div`, `Nat.Arith`
**Actualizado**: 2026-03-24
**Descripción**: GCD y LCM ZFC-nativos en ω. El GCD se define ejecutando σ b pasos del algoritmo euclídeo sobre pares ⟨a, b⟩ → ⟨b, a mod b⟩ mediante `RecursiveFn` en ω ×ₛ ω. Se demuestra convergencia por inducción fuerte en b. Un teorema puente `gcd_eq_gcdOf` conecta con `gcdOf` (Patrón B de Nat.Arith). El LCM se define como `divOf (mul a b) (gcd a b)` y se conecta vía `lcm_eq_lcmOf`.

#### GCD (gcd)

**Ubicación**: `Nat.Gcd.lean`, §6
**Orden**: 1ª definición pública

**Enunciado Matemático**: `gcd(a, b)` = primera componente de la iteración σ b-ésima del paso euclídeo ⟨a, b⟩ → ⟨b, a mod b⟩. Devuelve ∅ si a ∉ ω o b ∉ ω.

**Firma Lean4**:

```lean
noncomputable def gcd (a b : U) : U :=
  if ha : a ∈ (ω : U) then
    if hb : b ∈ (ω : U) then
      fst (apply (euclidFn a b ha hb) (σ b))
    else ∅
  else ∅
```

**Dependencias**: `RecursiveFn`, `euclid_stepFn` (privada), `fst`, `σ`, `ω`
**Computabilidad**: No computable (usa `Classical.choice`)

#### LCM (lcm)

**Ubicación**: `Nat.Gcd.lean`, §10
**Orden**: 2ª definición pública

**Enunciado Matemático**: `lcm(a, b) = (a · b) / gcd(a, b)`. Devuelve ∅ si a ∉ ω o b ∉ ω.

**Firma Lean4**:

```lean
noncomputable def lcm (a b : U) : U :=
  if ha : a ∈ (ω : U) then
    if hb : b ∈ (ω : U) then
      divOf (mul a b) (gcd a b)
    else ∅
  else ∅
```

**Dependencias**: `divOf`, `mul`, `gcd`, `ω`
**Computabilidad**: No computable

### 3.31 Nat.Primes.lean

**Módulo**: `ZfcSetTheory.Nat.Primes`
**Namespace**: `ZFC.Nat.Primes`
**Dependencias**: `Nat.Arith`, `Nat.Gcd`, `PeanoNatLib.PeanoNatPrimes`
**Estrategia**: Enfoque A — `DList ℕ₀` permanece en el lado Peano; la definición ZFC-nativa `isPrime` se puente vía `fromPeano_prime`.

#### isPrime

**Ubicación**: `Nat.Primes.lean`, §1
**Orden**: 1ª definición pública

**Enunciado Matemático**: `p` es ZFC-primo si: `p ∈ ω`, `p ≠ ∅`, `p ≠ σ ∅`, y para todo `a, b ∈ ω`: `p ∣ a·b → p ∣ a ∨ p ∣ b`.

**Firma Lean4**:

```lean
def isPrime (p : U) : Prop :=
  p ∈ (ω : U) ∧ p ≠ (∅ : U) ∧ p ≠ σ (∅ : U) ∧
  ∀ a b : U, a ∈ (ω : U) → b ∈ (ω : U) →
    divides p (mul a b) → divides p a ∨ divides p b
```

**Dependencias**: `ω`, `divides`, `mul`
**Computabilidad**: No computable (Prop)

### 3.32 Nat.Binom.lean

**Módulo**: `ZfcSetTheory.Nat.Binom`
**Namespace**: `ZFC.Nat.Binom`
**Dependencias**: `Nat.Add`, `Nat.Mul`, `Nat.Sub`, `Nat.Factorial`, `PeanoNatLib.PeanoNatBinom`
**Estrategia**: Patrón B (bridge-only) — Coeficientes binomiales levantados directamente del isomorfismo Peano.

#### binomOf

**Ubicación**: `Nat.Binom.lean`, §0
**Orden**: 1ª definición pública

**Enunciado Matemático**: C(n, k) en ω, levantado desde Peano vía el isomorfismo. Devuelve ∅ si n ∉ ω o k ∉ ω.

**Firma Lean4**:

```lean
noncomputable def binomOf (n k : U) : U :=
  if hn : n ∈ (ω : U) then
    if hk : k ∈ (ω : U) then
      fromPeano (Peano.Binom.binom
        (toPeano n (mem_Omega_is_Nat n hn))
        (toPeano k (mem_Omega_is_Nat k hk)))
    else ∅
  else ∅
```

**Dependencias**: `fromPeano`, `toPeano`, `mem_Omega_is_Nat`, `Peano.Binom.binom`, `ω`
**Computabilidad**: No computable

### 3.33 Nat.MaxMin.lean

**Módulo**: `ZfcSetTheory.Nat.MaxMin`
**Namespace**: `ZFC.Nat.MaxMin`
**Dependencias**: `Nat.Basic`, `Infinity`, `PeanoImport`, `PeanoNatLib.PeanoNatMaxMin`
**Estrategia**: Patrón B (bridge-only) — Máximo y mínimo levantados directamente del isomorfismo Peano.

#### maxOf

**Ubicación**: `Nat.MaxMin.lean`, §0
**Orden**: 1ª definición pública

**Enunciado Matemático**: max(n, m) en ω, levantado desde Peano vía el isomorfismo. Devuelve ∅ si n ∉ ω o m ∉ ω.

**Firma Lean4**:

```lean
noncomputable def maxOf (n m : U) : U :=
  if hn : n ∈ (ω : U) then
    if hm : m ∈ (ω : U) then
      fromPeano (Peano.MaxMin.max
        (toPeano n (mem_Omega_is_Nat n hn))
        (toPeano m (mem_Omega_is_Nat m hm)))
    else ∅
  else ∅
```

**Dependencias**: `fromPeano`, `toPeano`, `mem_Omega_is_Nat`, `Peano.MaxMin.max`, `ω`
**Computabilidad**: No computable

#### minOf

**Ubicación**: `Nat.MaxMin.lean`, §0
**Orden**: 2ª definición pública

**Enunciado Matemático**: min(n, m) en ω, levantado desde Peano vía el isomorfismo. Devuelve ∅ si n ∉ ω o m ∉ ω.

**Firma Lean4**:

```lean
noncomputable def minOf (n m : U) : U :=
  if hn : n ∈ (ω : U) then
    if hm : m ∈ (ω : U) then
      fromPeano (Peano.MaxMin.min
        (toPeano n (mem_Omega_is_Nat n hn))
        (toPeano m (mem_Omega_is_Nat m hm)))
    else ∅
  else ∅
```

**Dependencias**: `fromPeano`, `toPeano`, `mem_Omega_is_Nat`, `Peano.MaxMin.min`, `ω`
**Computabilidad**: No computable

### 3.34 Nat.NewtonBinom.lean

**Módulo**: `ZfcSetTheory.Nat.NewtonBinom`
**Namespace**: `ZFC.Nat.NewtonBinom`
**Dependencias**: `Nat.Add`, `Nat.Mul`, `Nat.Sub`, `Nat.Pow`, `Nat.Binom`, `PeanoNatLib.PeanoNatNewtonBinom`
**Estrategia**: Patrón B (bridge-only) — Término binomial con 4 argumentos levantado del isomorfismo Peano. `finSum` no se transporta (función de orden superior); Newton's binomial theorem y sum=2^n se enuncian a nivel Peano con resultado transportado vía `fromPeano`.

#### binomTermOf

**Ubicación**: `Nat.NewtonBinom.lean`, §0
**Orden**: 1ª definición pública

**Enunciado Matemático**: C(n,k) · a^k · b^(n−k) en ω, levantado desde Peano vía el isomorfismo con 4 argumentos. Devuelve ∅ si algún argumento no está en ω.

**Firma Lean4**:

```lean
noncomputable def binomTermOf (a b n k : U) : U :=
  if ha : a ∈ (ω : U) then
    if hb : b ∈ (ω : U) then
      if hn : n ∈ (ω : U) then
        if hk : k ∈ (ω : U) then
          fromPeano (Peano.NewtonBinom.binomTerm
            (toPeano a (mem_Omega_is_Nat a ha))
            (toPeano b (mem_Omega_is_Nat b hb))
            (toPeano n (mem_Omega_is_Nat n hn))
            (toPeano k (mem_Omega_is_Nat k hk)))
        else ∅
      else ∅
    else ∅
  else ∅
```

**Dependencias**: `fromPeano`, `toPeano`, `mem_Omega_is_Nat`, `Peano.NewtonBinom.binomTerm`, `ω`
**Computabilidad**: No computable

### 3.35 Nat.WellFounded.lean

**Módulo**: `ZfcSetTheory.Nat.WellFounded`
**Namespace**: `ZFC.Nat.WellFounded`
**Dependencias**: `Nat.Basic`, `Infinity`, `PeanoImport`, `PeanoNatLib.PeanoNatWellFounded`
**Estrategia**: Patrón B (bridge-only) — Buen fundamento ya existe como `nat_mem_wf` en ZFC; este módulo añade el principio de buena ordenación transportado desde Peano.

*(Este módulo no tiene definiciones públicas — solo teoremas.)*

---

### 3.36 Peano.FiniteSequences.lean

**Módulo**: `ZfcSetTheory.Peano.FiniteSequences`
**Namespace**: `ZFC.Peano.FiniteSequences`
**Dependencias**: `Nat.Add` + anteriores (usa `Functions`, `Nat.Basic`, `SetOps.CartesianProduct`, `Infinity`, etc.)

#### Definición: `isFinSeq`

**Enunciado Matemático**: $\text{isFinSeq}(f, n, A) \iff n \in \omega \land f : n \to A$

```lean
def isFinSeq (f n A : U) : Prop :=
  n ∈ ω ∧ IsFunction f n A
```

**Dependencias**: `IsFunction`, `ω`
**Computabilidad**: Computable (predicado proposicional)

#### Definición: `FinSeqSet`

**Enunciado Matemático**: $\text{FinSeqSet}(n, A) = \{ f \in \mathcal{P}(n \times_s A) \mid n \in \omega \land f : n \to A \}$

```lean
noncomputable def FinSeqSet (n A : U) : U :=
  sep (𝒫(n ×ₛ A)) (fun f => n ∈ ω ∧ IsFunction f n A)
```

**Dependencias**: `sep`, `𝒫`, `×ₛ`, `IsFunction`, `ω`
**Computabilidad**: No computable

#### Definición: `appendElem`

**Enunciado Matemático**: $\text{appendElem}(f, n, a) = f \cup \{\langle n, a \rangle\}$

```lean
noncomputable def appendElem (f n a : U) : U := f ∪ {⟨n, a⟩}
```

**Dependencias**: `union`, `Singleton`, `OrderedPair`
**Computabilidad**: No computable

---

### 3.37 SetOps.FiniteSets.lean

**Módulo**: `ZfcSetTheory.SetOps.FiniteSets`
**Namespace**: `ZFC.SetOps.FiniteSets` (exportado a `ZFC`)
**Dependencias**: `Nat.Basic`, `Infinity` + anteriores (usa `Functions`, `Cardinality`, `Relations`, `SetOps.CartesianProduct`, etc.)

#### Definición: `isFiniteSet`

**Enunciado Matemático**: $\text{isFiniteSet}(A) \iff \exists n \in \omega,\; A \simeq_s n$

```lean
def isFiniteSet (A : U) : Prop := ∃ n, n ∈ ω ∧ A ≃ₛ n
```

**Dependencias**: `ω`, `isEquipotent` (≃ₛ)
**Computabilidad**: Computable (predicado proposicional)

---

### 3.38 Peano.FiniteSequencesArith.lean

**Módulo**: `ZfcSetTheory.Peano.FiniteSequencesArith`
**Namespace**: `ZFC.Peano.FiniteSequencesArith` (exportado a `ZFC`)
**Dependencias**: `Nat.Mul`, `Peano.FiniteSequences`, `SetOps.FiniteSets` + anteriores

#### Definición: `sumStepFn`

**Enunciado Matemático**: Función de paso para sumación: $\langle k, v \rangle \mapsto v + f(k)$, construida como subconjunto de $(\omega \times_s \omega) \times_s \omega$.

```lean
noncomputable def sumStepFn (f : U) : U :=
  sep ((ω ×ₛ ω) ×ₛ ω)
    (fun p => ∃ k v, k ∈ (ω : U) ∧ v ∈ (ω : U) ∧
      p = ⟨⟨k, v⟩, add v (f⦅k⦆)⟩)
```

**Dependencias**: `sep`, `ω`, `add`, `apply`
**Computabilidad**: Noncomputable

#### Definición: `seqSumFn`

**Enunciado Matemático**: Función de sumación: dado $f$, $\text{seqSumFn}(f)$ es la única $F : \omega \to \omega$ que satisface $F(\emptyset) = \emptyset$ y $F(\sigma k) = F(k) + f(k)$.

```lean
noncomputable def seqSumFn (f : U) (hf : isFinSeq f (domain f) ω) : U :=
  Classical.choose (ExistsUnique.exists
    (RecursionTheoremWithStep (ω : U) ∅ (sumStepFn f)
      zero_in_Omega (sumStepFn_is_function hf)))
```

**Dependencias**: `RecursionTheoremWithStep`, `sumStepFn`, `isFinSeq`
**Computabilidad**: Noncomputable

#### Definición: `seqSum`

**Enunciado Matemático**: Suma de una secuencia finita numérica: $\text{seqSum}(f, n) = \sum_{i<n} f(i)$.

```lean
noncomputable def seqSum (f n : U) : U :=
  if h : isFinSeq f (domain f) ω then
    apply (seqSumFn f h) n
  else ∅
```

**Dependencias**: `seqSumFn`, `isFinSeq`, `apply`
**Computabilidad**: Noncomputable

#### Definición: `prodStepFn`

**Enunciado Matemático**: Función de paso para producto: $\langle k, v \rangle \mapsto v \cdot f(k)$, construida como subconjunto de $(\omega \times_s \omega) \times_s \omega$.

```lean
noncomputable def prodStepFn (f : U) : U :=
  sep ((ω ×ₛ ω) ×ₛ ω)
    (fun p => ∃ k v, k ∈ (ω : U) ∧ v ∈ (ω : U) ∧
      p = ⟨⟨k, v⟩, mul v (f⦅k⦆)⟩)
```

**Dependencias**: `sep`, `ω`, `mul`, `apply`
**Computabilidad**: Noncomputable

#### Definición: `seqProdFn`

**Enunciado Matemático**: Función de producto: dado $f$, $\text{seqProdFn}(f)$ es la única $F : \omega \to \omega$ con $F(\emptyset) = \sigma\emptyset$ y $F(\sigma k) = F(k) \cdot f(k)$.

```lean
noncomputable def seqProdFn (f : U) (hf : isFinSeq f (domain f) ω) : U :=
  Classical.choose (ExistsUnique.exists
    (RecursionTheoremWithStep (ω : U) (σ ∅) (prodStepFn f)
      (succ_in_Omega ∅ zero_in_Omega) (prodStepFn_is_function hf)))
```

**Dependencias**: `RecursionTheoremWithStep`, `prodStepFn`, `isFinSeq`
**Computabilidad**: Noncomputable

#### Definición: `seqProd`

**Enunciado Matemático**: Producto de una secuencia finita numérica: $\text{seqProd}(f, n) = \prod_{i<n} f(i)$.

```lean
noncomputable def seqProd (f n : U) : U :=
  if h : isFinSeq f (domain f) ω then
    apply (seqProdFn f h) n
  else ∅
```

**Dependencias**: `seqProdFn`, `isFinSeq`, `apply`
**Computabilidad**: Noncomputable

#### Definición: `familyProduct`

**Enunciado Matemático**: Producto cartesiano de una familia $F : n \to \text{Sets}$: $\prod_{i<n} F(i) = \{g : n \to \bigcup(\text{range}\,F) \mid \forall i \in n,\; g(i) \in F(i)\}$.

```lean
noncomputable def familyProduct (F n : U) : U :=
  sep (FinSeqSet n (⋃ (image F n)))
    (fun g => ∀ i, i ∈ n → g⦅i⦆ ∈ F⦅i⦆)
```

**Dependencias**: `sep`, `FinSeqSet`, `image`, `apply`
**Computabilidad**: Noncomputable

### 3.39 Peano.FiniteSequencesBridge.lean

**Módulo**: `ZfcSetTheory.Peano.FiniteSequencesBridge`
**Namespace**: `ZFC.Peano.FiniteSequencesBridge` (exportado a `ZFC`)
**Dependencias**: `Peano.FiniteSequencesArith`, `Nat.Primes` + anteriores

#### Definición: `nth`

**Enunciado Matemático**: Acceso al elemento en el índice $i$ de una secuencia finita $f$. Wrapper nombrado para `apply f i` = `f⦅i⦆`.

```lean
noncomputable def nth (f i : U) : U := f⦅i⦆
```

**Dependencias**: `apply`
**Computabilidad**: Noncomputable

#### Definición: `dlistToSeq`

**Enunciado Matemático**: Convierte una `DList ℕ₀` (lista de Peano) en una secuencia finita ZFC en $\omega$. Los elementos se colocan en orden inverso: la cabeza del DList va al último índice. Definición recursiva vía `appendElem`.

```lean
noncomputable def dlistToSeq : DList Peano.ℕ₀ → U
  | .nil       => (∅ : U)
  | .cons x xs =>
      appendElem (dlistToSeq xs) (fromPeano (DList.length xs)) (fromPeano x)
```

**Dependencias**: `appendElem`, `fromPeano`, `DList`
**Computabilidad**: Noncomputable

#### Definición: `dlistLen`

**Enunciado Matemático**: Longitud ZFC de un DList convertido: $\text{dlistLen}(ps) = \text{fromPeano}(\text{length}(ps))$.

```lean
noncomputable def dlistLen (ps : DList Peano.ℕ₀) : U :=
  fromPeano (DList.length ps)
```

**Dependencias**: `fromPeano`, `DList.length`
**Computabilidad**: Noncomputable

#### Definición: `isPrimeSeq`

**Enunciado Matemático**: Predicado: $f$ es una secuencia finita de primos de longitud $k$:
$$\text{isPrimeSeq}(f, k) \iff \text{isFinSeq}(f, k, \omega) \land \forall i \in k,\; \text{isPrime}(f(i))$$

```lean
def isPrimeSeq (f k : U) : Prop :=
  isFinSeq f k ω ∧ ∀ i, i ∈ k → isPrime (f⦅i⦆)
```

**Dependencias**: `isFinSeq`, `isPrime`, `apply`
**Computabilidad**: Computable (es Prop)

### 3.40 BoolAlg.FiniteCofinite.lean

**Módulo**: `ZfcSetTheory.BoolAlg.FiniteCofinite`
**Namespace**: `ZFC.BoolAlg.FiniteCofinite` (exportado a `ZFC`)
**Dependencias**: `BoolAlg.Complete`, `SetOps.FiniteSets`, `Nat.Add`, `Cardinality` + anteriores

#### Definición: `isCofinite`

**Enunciado Matemático**: $X$ es cofinito en $A$: $A \setminus X$ es un conjunto finito.
$$\text{isCofinite}(A, X) \iff \text{isFiniteSet}(A \setminus X)$$

```lean
def isCofinite (A X : U) : Prop := isFiniteSet (A \ X)
```

**Dependencias**: `isFiniteSet`, `sdiff`
**Computabilidad**: Computable (es Prop)

#### Definición: `isFinCof`

**Enunciado Matemático**: $X$ es finito o cofinito en $A$: $X \subset A$ y ($X$ finito $\lor$ $X$ cofinito en $A$).
$$\text{isFinCof}(A, X) \iff X \subset A \land (\text{isFiniteSet}(X) \lor \text{isCofinite}(A, X))$$

```lean
def isFinCof (A X : U) : Prop := X ⊆ A ∧ (isFiniteSet X ∨ isCofinite A X)
```

**Dependencias**: `isFiniteSet`, `isCofinite`
**Computabilidad**: Computable (es Prop)

#### Definición: `FinCofAlg`

**Enunciado Matemático**: El álgebra finita/cofinita de $A$: todos los subconjuntos de $A$ que son finitos o cofinitos.
$$\text{FinCofAlg}(A) = \{X \in \mathcal{P}(A) \mid \text{isFiniteSet}(X) \lor \text{isCofinite}(A, X)\}$$

```lean
noncomputable def FinCofAlg (A : U) : U :=
  sep (𝒫 A) (fun X => isFiniteSet X ∨ isCofinite A X)
```

**Dependencias**: `sep`, `PowerSet`, `isFiniteSet`, `isCofinite`
**Computabilidad**: Noncomputable

#### Definición: `EvenSet`

**Enunciado Matemático**: El conjunto de números naturales pares:
$$\text{EvenSet} = \{n \in \omega \mid \exists k \in \omega,\; n = k + k\}$$

```lean
noncomputable def EvenSet : U :=
  sep (ω : U) (fun n => ∃ k, k ∈ (ω : U) ∧ n = add k k)
```

**Dependencias**: `sep`, `ω`, `add`
**Computabilidad**: Noncomputable

### 3.41 BoolAlg.Complete.lean

#### Supremo Relativizado (isSupremumIn)

**Ubicación**: `BoolAlg.Complete.lean`, línea 69
**Orden**: 1ª definición principal
**Computable**: Sí (es Prop)

**Enunciado Matemático**: $x$ es el supremo de $S$ dentro del retículo $L$ (ordenado por $\subset$) si:

1. $x \in L$
2. $\forall y \in S,\; y \subset x$ (cota superior)
3. $\forall z \in L,\; (\forall y \in S,\; y \subset z) \Rightarrow x \subset z$ (mínima cota superior)

**Firma Lean4**:

```lean
def isSupremumIn (L S x : U) : Prop :=
  x ∈ L ∧ (∀ y, y ∈ S → y ⊆ x) ∧ (∀ z, z ∈ L → (∀ y, y ∈ S → y ⊆ z) → x ⊆ z)
```

**Dependencias**: `mem`, `subset`

#### Ínfimo Relativizado (isInfimumIn)

**Ubicación**: `BoolAlg.Complete.lean`, línea 73
**Orden**: 2ª definición principal
**Computable**: Sí (es Prop)

**Enunciado Matemático**: $x$ es el ínfimo de $S$ dentro del retículo $L$ (ordenado por $\subset$) si:

1. $x \in L$
2. $\forall y \in S,\; x \subset y$ (cota inferior)
3. $\forall z \in L,\; (\forall y \in S,\; z \subset y) \Rightarrow z \subset x$ (máxima cota inferior)

**Firma Lean4**:

```lean
def isInfimumIn (L S x : U) : Prop :=
  x ∈ L ∧ (∀ y, y ∈ S → x ⊆ y) ∧ (∀ z, z ∈ L → (∀ y, y ∈ S → z ⊆ y) → z ⊆ x)
```

**Dependencias**: `mem`, `subset`

#### Retículo Completo (isCompleteLattice)

**Ubicación**: `BoolAlg.Complete.lean`, línea 77
**Orden**: 3ª definición principal
**Computable**: Sí (es Prop)

**Enunciado Matemático**: $L$ es un retículo completo si todo subconjunto $S \subset L$ tiene supremo e ínfimo en $L$:
$$\forall S \subset L,\; (\exists x,\; \text{isSupremumIn}(L, S, x)) \land (\exists x,\; \text{isInfimumIn}(L, S, x))$$

**Firma Lean4**:

```lean
def isCompleteLattice (L : U) : Prop :=
  ∀ S, S ⊆ L → (∃ x, isSupremumIn L S x) ∧ (∃ x, isInfimumIn L S x)
```

**Dependencias**: `isSupremumIn`, `isInfimumIn`, `subset`

#### Álgebra Booleana Completa Atómica (isCompleteAtomicBA)

**Ubicación**: `BoolAlg.Complete.lean`, línea 192
**Orden**: 4ª definición principal
**Computable**: Sí (es Prop)

**Enunciado Matemático**: $\mathcal{P}(A)$ es un álgebra booleana completa atómica si es retículo completo y atómica:
$$\text{isCompleteAtomicBA}(A) \iff \text{isCompleteLattice}(\mathcal{P}(A)) \land \text{isAtomic}(A)$$

**Firma Lean4**:

```lean
def isCompleteAtomicBA (A : U) : Prop :=
  isCompleteLattice (𝒫 A) ∧ isAtomic A
```

**Dependencias**: `isCompleteLattice`, `isAtomic`, `PowerSet`

### 3.42 BoolAlg.FiniteBA.lean

**Módulo**: `ZfcSetTheory.BoolAlg.FiniteBA`
**Namespace**: `ZFC.BoolAlg.FiniteBA`
**Dependencias**: `Cardinal.FinitePowerSet`, `BoolAlg.Representation`
**Estrategia**: Combina finiteness + atoms + powerset_cardinality para probar |𝒫(A)| = 2^n.

*(Este módulo no tiene definiciones públicas — solo teoremas.)*

### 3.43 BoolAlg.BoolRingBA.lean

**Módulo**: `ZfcSetTheory.BoolAlg.BoolRingBA`
**Namespace**: `ZFC.BoolAlg.BoolRingBA`
**Dependencias**: `BoolAlg.Ring`
**Estrategia**: Establece la correspondencia formal (functor) entre el anillo booleano (△, ∩) y el álgebra booleana (∪, ∩, ^∁) sobre 𝒫(A), con round-trip theorems.

*(Este módulo no tiene definiciones públicas — solo teoremas.)*

---

### 3.44 BoolAlg.Representation.lean

**Módulo**: `ZfcSetTheory.BoolAlg.Representation`
**Namespace**: `ZFC.BoolAlg.Representation`
**Dependencias**: `BoolAlg.Complete`, `BoolAlg.Atomic`, `BoolAlg.GenDeMorgan`, `BoolAlg.GenDistributive`, `Cardinal.Basic`, `SetOps.Functions`
**Estrategia**: Prueba el teorema de representación de Stone (forma concreta): toda BA completa atómica sobre 𝒫(A) es canónicamente isomorfa a 𝒫(Atoms A) vía el mapa X ↦ {Y ∈ Atoms(A) | Y ⊆ X}. Demuestra que a ↦ {a} es una biyección A ↔ Atoms(A) y que el mapa levantado preserva ∪, ∩ y complemento.

#### atomsSingletonMap (atomsSingletonMap)

**Ubicación**: `BoolAlg.Representation.lean`, línea 99
**Orden**: 1ª definición

**Descripción Matemática**: Mapa singleton restringido al codominio Atoms(A): $a \mapsto \{a\}$, definido como $\{⟨a, \{a\}⟩ \mid a \in A\} \subseteq A \times_s \text{Atoms}(A)$.

**Firma Lean4**:

```lean
noncomputable def atomsSingletonMap (A : U) : U :=
  sep (A ×ₛ Atoms A) (fun p => ∃ x, x ∈ A ∧ p = ⟨x, ({x} : U)⟩)
```

#### atomsBelow (atomsBelow)

**Ubicación**: `BoolAlg.Representation.lean`, línea 177
**Orden**: 2ª definición

**Descripción Matemática**: La familia de átomos por debajo de un subconjunto $X \subseteq A$: $\text{atomsBelow}(A, X) = \{Y \in \text{Atoms}(A) \mid Y \subseteq X\}$.

**Firma Lean4**:

```lean
noncomputable def atomsBelow (A X : U) : U :=
  sep (Atoms A) (fun Y => Y ⊆ X)
```

#### atomsBelowMap (atomsBelowMap)

**Ubicación**: `BoolAlg.Representation.lean`, línea 215
**Orden**: 3ª definición

**Descripción Matemática**: Función ZFC $X \mapsto \text{atomsBelow}(A, X)$ de $\mathcal{P}(A)$ a $\mathcal{P}(\text{Atoms}(A))$, definida como $\{⟨X, \text{atomsBelow}(A,X)⟩ \mid X \in \mathcal{P}(A)\}$.

**Firma Lean4**:

```lean
noncomputable def atomsBelowMap (A : U) : U :=
  sep (𝒫 A ×ₛ 𝒫 (Atoms A)) (fun p =>
    ∃ W, W ∈ 𝒫 A ∧ p = ⟨W, atomsBelow A W⟩)
```

---

### 3.45 Cardinal.FinitePowerSet.lean

**Módulo**: `ZfcSetTheory.Cardinal.FinitePowerSet`
**Namespace**: `ZFC.Cardinal.FinitePowerSet`
**Dependencias**: `SetOps.FiniteSets`, `Nat.Pow`, `BoolAlg.FiniteCofinite`
**Estrategia**: Demuestra que para conjuntos finitos, la cardinalidad del conjunto potencia es una potencia de 2: si $|F| = n$ entonces $|\mathcal{P}(F)| = 2^n$. Descompone $\mathcal{P}(B \cup \{a\})$ en dos mitades disjuntas equipotentes a $\mathcal{P}(B)$.

#### removeElemMap (removeElemMap)

**Ubicación**: `Cardinal.FinitePowerSet.lean`, línea 298
**Orden**: 1ª definición

**Descripción Matemática**: Función ZFC $S \mapsto S \setminus \{a\}$ desde $\{S \in \mathcal{P}(A) \mid a \in S\}$ hacia $\mathcal{P}(A \setminus \{a\})$.

**Firma Lean4**:

```lean
noncomputable def removeElemMap (A a : U) : U :=
  sep (sep (𝒫 A) (fun S => a ∈ S) ×ₛ 𝒫 (sdiff A {a}))
    (fun p => ∃ S, S ∈ 𝒫 A ∧ a ∈ S ∧ p = ⟨S, sdiff S {a}⟩)
```

---

## 4. Teoremas Principales por Módulo

### 4.1 Extension.lean

#### Igualdad por Subconjuntos

**Ubicación**: `Extension.lean`, línea 56  
**Orden**: 1º teorema principal

**Enunciado Matemático**: Si A ⊆ B y B ⊆ A, entonces A = B.

**Firma Lean4**:

```lean
@[simp] theorem subset_antisymm (x y : U) :
  (x ⊆ y) → (y ⊆ x) → (x = y)
```

**Dependencias**: `ExtSet`, `subset`
**Importancia**: high

### 4.2 Pairing.lean

#### No Vacío si y solo si Existe Elemento (nonempty_iff_exists_mem)

**Ubicación**: `Pairing.lean`, línea 88  
**Orden**: 1º teorema auxiliar

**Enunciado Matemático**: w ≠ ∅ ↔ ∃y, y ∈ w.

**Firma Lean4**:

```lean
@[simp] theorem nonempty_iff_exists_mem (w : U) : w ≠ ∅ ↔ ∃ y, y ∈ w
```

**Dependencias**: `EmptySet`, `ExtSet`, `EmptySet_is_empty`
**Importancia**: high

#### Intersección de Singleton (interSet_of_singleton)

**Ubicación**: `Pairing.lean`, línea 101  
**Orden**: 2º teorema auxiliar

**Enunciado Matemático**: ⋂{A} = A.

**Firma Lean4**:

```lean
@[simp] theorem interSet_of_singleton (A : U) : (⋂ { A }) = A
```

**Dependencias**: `interSet`, `Singleton`, `mem_sep_iff`, `Singleton_is_specified`
**Importancia**: medium

#### Elemento Único de Singleton (is_singleton_unique_elem)

**Ubicación**: `Pairing.lean`, línea 158  
**Orden**: 3º teorema auxiliar

**Enunciado Matemático**: Si s = {a}, entonces todo x ∈ s satisface x = a.

**Firma Lean4**:

```lean
theorem is_singleton_unique_elem (s a : U) :
  s = {a} → ∀ x, x ∈ s → x = a
```

**Dependencias**: `Singleton`, `Singleton_is_specified`
**Importancia**: low

#### Par Igual a Singleton (pair_set_eq_singleton)

**Ubicación**: `Pairing.lean`, línea 164  
**Orden**: 4º teorema auxiliar

**Enunciado Matemático**: {x, x} = {x}.

**Firma Lean4**:

```lean
theorem pair_set_eq_singleton (x : U) :
  ({x, x} : U) = ({x} : U)
```

**Dependencias**: `PairSet`, `Singleton`, `ExtSet`, `PairSet_is_specified`, `Singleton_is_specified`
**Importancia**: low

#### Par Ordenado de Elemento Consigo Mismo (ordered_pair_self_eq_singleton_singleton)

**Ubicación**: `Pairing.lean`, línea 171  
**Orden**: 5º teorema auxiliar

**Enunciado Matemático**: ⟨x, x⟩ = {{x}}.

**Firma Lean4**:

```lean
theorem ordered_pair_self_eq_singleton_singleton (x : U) :
  (⟨x, x⟩ : U) = ({{x}} : U)
```

**Dependencias**: `OrderedPair`, `pair_set_eq_singleton`
**Importancia**: low

#### Diferencia de Par Ordenado con Singleton (diff_ordered_pair_neq)

**Ubicación**: `Pairing.lean`, línea 177  
**Orden**: 6º teorema auxiliar

**Enunciado Matemático**: Si x ≠ y, entonces ⟨x, y⟩ \ {{x}} = {{x, y}}.

**Firma Lean4**:

```lean
theorem diff_ordered_pair_neq (x y : U) (h_neq : x ≠ y) :
  ((⟨x, y⟩ : U) \ ({{x}} : U)) = {{x, y}}
```

**Dependencias**: `OrderedPair`, `sdiff`, `Singleton`, `mem_sdiff_iff`, `OrderedPair_is_specified`, `Singleton_is_specified`
**Importancia**: low

#### Diferencia de Par con Singleton (diff_pair_singleton)

**Ubicación**: `Pairing.lean`, línea 203  
**Orden**: 7º teorema auxiliar

**Enunciado Matemático**: Si x ≠ y, entonces {x, y} \ {x} = {y}.

**Firma Lean4**:

```lean
theorem diff_pair_singleton (x y : U) (h_neq : x ≠ y) :
  (({x, y} : U) \ ({x} : U)) = ({y} : U)
```

**Dependencias**: `PairSet`, `Singleton`, `sdiff`, `ExtSet`, `mem_sdiff_iff`, `PairSet_is_specified`, `Singleton_is_specified`
**Importancia**: low

#### Idempotencia de Or en Membresía (auxiliary_idempotence_of_or_in)

**Ubicación**: `Pairing.lean`, línea 227  
**Orden**: 8º teorema auxiliar

**Enunciado Matemático**: x ∈ y ↔ x ∈ y ∨ x ∈ y.

**Firma Lean4**:

```lean
theorem auxiliary_idempotence_of_or_in (x y : U) :
  x ∈ y ↔ x ∈ y ∨ x ∈ y
```

**Dependencias**: Ninguna (lógica proposicional)
**Importancia**: low

#### Idempotencia de Or en Igualdad (auxiliary_idempotence_of_or_eq)

**Ubicación**: `Pairing.lean`, línea 237  
**Orden**: 9º teorema auxiliar

**Enunciado Matemático**: x = y ↔ x = y ∨ x = y.

**Firma Lean4**:

```lean
theorem auxiliary_idempotence_of_or_eq (x y : U) :
  x = y ↔ x = y ∨ x = y
```

**Dependencias**: Ninguna (lógica proposicional)
**Importancia**: low

#### Membresía en Par Ordenado con Igualdad (ordered_pair_eq_mem)

**Ubicación**: `Pairing.lean`, línea 247  
**Orden**: 10º teorema auxiliar

**Enunciado Matemático**: Si x = y, entonces todo z ∈ ⟨x, y⟩ satisface z = {y}.

**Firma Lean4**:

```lean
theorem ordered_pair_eq_mem (x y : U) (h_eq : x = y) :
  ∀ (z : U), z ∈ (⟨x, y⟩ : U) → z = ({y} : U)
```

**Dependencias**: `OrderedPair`, `Singleton`, `inter_of_ordered_pair`, `OrderedPair_is_specified`, `Singleton_is_specified`
**Importancia**: low

#### Diferencia de Par con Intersección (diff_pair_sing_inter)

**Ubicación**: `Pairing.lean`, línea 271  
**Orden**: 11º teorema auxiliar

**Enunciado Matemático**: Si x = y, entonces ⟨x, y⟩ \ {⋂ ⟨x, y⟩} = ∅.

**Firma Lean4**:

```lean
theorem diff_pair_sing_inter (x y : U) :
  (x = y) → (((⟨x, y⟩ : U) \ ({(⋂ (⟨x, y⟩ : U))})) = (∅ : U))
```

**Dependencias**: `OrderedPair`, `interSet`, `sdiff`, `Singleton`, `inter_of_ordered_pair`, `ordered_pair_self_eq_singleton_singleton`, `sdiff_self`
**Importancia**: low

#### Corrección de fst (fst_of_ordered_pair)

**Ubicación**: `Pairing.lean`, línea 286  
**Orden**: 1º teorema principal

**Enunciado Matemático**: La primera proyección de un par ordenado es el primer elemento: fst(⟨x, y⟩) = x.

**Firma Lean4**:

```lean
@[simp] theorem fst_of_ordered_pair (x y : U) : fst (⟨x, y⟩ : U) = x
```

**Dependencias**: `fst`, `OrderedPair`, `inter_of_ordered_pair`, `interSet_of_singleton`
**Importancia**: high

#### Membresía en Par Ordenado con Desigualdad (ordered_pair_neq_mem)

**Ubicación**: `Pairing.lean`, línea 287  
**Orden**: 12º teorema auxiliar

**Enunciado Matemático**: Todo z ∈ ⟨x, y⟩ satisface z = {x, y} o z = {x}.

**Firma Lean4**:

```lean
theorem ordered_pair_neq_mem (x y : U) :
  ∀ (z : U), (z ∈ (⟨x, y⟩ : U)) → (z = ({x, y} : U) ∨ (z = ({x} : U)))
```

**Dependencias**: `OrderedPair`, `PairSet`, `Singleton`, `OrderedPair_is_specified`
**Importancia**: low

#### Intersección de Par Ordenado (inter_of_ordered_pair)

**Ubicación**: `Pairing.lean`, línea 293  
**Orden**: 13º teorema auxiliar

**Enunciado Matemático**: ⋂ ⟨x, y⟩ = {x}.

**Firma Lean4**:

```lean
theorem inter_of_ordered_pair (x y : U) : (⋂ ⟨x, y⟩) = {x}
```

**Dependencias**: `interSet`, `OrderedPair`, `Singleton`, `ExtSet`, `OrderedPair_is_specified`, `Singleton_is_specified`, `PairSet_is_specified`
**Importancia**: medium

#### Intersección de Par Ordenado con Desigualdad (inter_of_ordered_pair_neq_mem)

**Ubicación**: `Pairing.lean`, línea 295  
**Orden**: 14º teorema auxiliar

**Enunciado Matemático**: Si x ≠ y, entonces ⟨x, y⟩ \ {⋂ ⟨x, y⟩} = {{x, y}}.

**Firma Lean4**:

```lean
theorem inter_of_ordered_pair_neq_mem (x y : U) (h_eq : x ≠ y) :
  (((⟨x, y⟩ : U)  \ ({((⋂ (⟨x, y⟩ : U)) : U)} : U)  : U) = ({{x, y}} : U))
```

**Dependencias**: `OrderedPair`, `interSet`, `sdiff`, `Singleton`, `ExtSet`, `inter_of_ordered_pair`, `mem_sdiff_iff`, `OrderedPair_is_specified`, `Singleton_is_specified`
**Importancia**: low

#### Segunda Proyección con Igualdad (snd_of_ordered_pair_eq)

**Ubicación**: `Pairing.lean`, línea 318  
**Orden**: 15º teorema auxiliar

**Enunciado Matemático**: Si x = y, entonces snd(⟨x, y⟩) = y.

**Firma Lean4**:

```lean
theorem snd_of_ordered_pair_eq (x y : U) (h_eq : x = y) :
  snd ⟨x, y⟩ = y
```

**Dependencias**: `snd`, `OrderedPair`, `diff_pair_sing_inter`, `inter_of_ordered_pair`, `interSet_of_singleton`
**Importancia**: medium

#### Corrección de snd (snd_of_ordered_pair)

**Ubicación**: `Pairing.lean`, línea 325  
**Orden**: 2º teorema principal

**Enunciado Matemático**: La segunda proyección de un par ordenado es el segundo elemento: snd(⟨x, y⟩) = y.

**Firma Lean4**:

```lean
@[simp] theorem snd_of_ordered_pair (x y : U) : snd ⟨x, y⟩ = y
```

**Dependencias**: `snd`, `OrderedPair`, `snd_of_ordered_pair_eq`, `diff_ordered_pair_neq`, `diff_pair_singleton`, `inter_of_ordered_pair`, `interSet_of_singleton`, `is_singleton_unique_elem`, `nonempty_iff_exists_mem`
**Importancia**: high

#### Par Ordenado Bien Construido (OrderedPairSet_is_WellConstructed)

**Ubicación**: `Pairing.lean`, línea 336  
**Orden**: 3º teorema principal

**Enunciado Matemático**: Si w es un par ordenado, entonces w = ⟨fst w, snd w⟩.

**Firma Lean4**:

```lean
@[simp] theorem OrderedPairSet_is_WellConstructed (w : U) :
  (isOrderedPair w) → w = (⟨ fst w, snd w ⟩ : U)
```

**Dependencias**: `isOrderedPair`, `fst`, `snd`, `OrderedPair`, `fst_of_ordered_pair`, `snd_of_ordered_pair`
**Importancia**: high

#### Igualdad de Pares Ordenados por Proyecciones (Eq_of_OrderedPairs_given_projections)

**Ubicación**: `Pairing.lean`, línea 344  
**Orden**: 4º teorema principal

**Enunciado Matemático**: Si ⟨a, b⟩ = ⟨c, d⟩, entonces a = c y b = d.

**Firma Lean4**:

```lean
theorem Eq_of_OrderedPairs_given_projections (a b c d : U) :
  (⟨a, b⟩ : U) = (⟨c, d⟩ : U) → a = c ∧ b = d
```

**Dependencias**: `OrderedPair`, `fst`, `snd`, `fst_of_ordered_pair`, `snd_of_ordered_pair`
**Importancia**: high

#### Igualdad de Pares Ordenados (Eq_OrderedPairs)

**Ubicación**: `Pairing.lean`, línea 357  
**Orden**: 5º teorema principal

**Enunciado Matemático**: Para pares ordenados w y v, (fst w = fst v ∧ snd w = snd v) ↔ w = v.

**Firma Lean4**:

```lean
theorem Eq_OrderedPairs (w v : U) :
  isOrderedPair w → isOrderedPair v → ((fst w = fst v ∧ snd w = snd v) ↔ (w = v))
```

**Dependencias**: `isOrderedPair`, `fst`, `snd`, `fst_of_ordered_pair`, `snd_of_ordered_pair`, `Eq_of_OrderedPairs_given_projections`
**Importancia**: high

#### Equivalencia de Predicados de Par Ordenado (isOrderedPair_equiv_isOrderedPair_concept)

**Ubicación**: `Pairing.lean`, línea 380  
**Orden**: 6º teorema principal

**Enunciado Matemático**: isOrderedPair w ↔ ∃x y, w = ⟨x, y⟩.

**Firma Lean4**:

```lean
theorem isOrderedPair_equiv_isOrderedPair_concept (w : U) :
  isOrderedPair w ↔ ∃ (x y : U), w = ⟨ x , y ⟩
```

**Dependencias**: `isOrderedPair`, `OrderedPair`
**Importancia**: medium

#### Par Ordenado por Construcción (isOrderedPair_by_construction)

**Ubicación**: `Pairing.lean`, línea 388  
**Orden**: 7º teorema principal

**Enunciado Matemático**: isOrderedPair w ↔ w = ⟨fst w, snd w⟩.

**Firma Lean4**:

```lean
theorem isOrderedPair_by_construction (w : U) :
  isOrderedPair w ↔ (w = (⟨ fst w , snd w ⟩ : U))
```

**Dependencias**: `isOrderedPair`, `fst`, `snd`, `OrderedPair`, `OrderedPairSet_is_WellConstructed`
**Importancia**: medium

### 4.3 PowerSet.lean - Teoremas Principales

#### Especificación del Conjunto Potencia (mem_powerset_iff)

**Ubicación**: `PowerSet.lean`, línea 47  
**Orden**: 1º teorema de especificación

**Enunciado Matemático**: x ∈ 𝒫(A) ↔ x ⊆ A.

**Firma Lean4**:

```lean
@[simp] theorem mem_powerset_iff (A x : U) : x ∈ (𝒫 A) ↔ x ⊆ A
```

**Dependencias**: `powerset`, `powersetExistsUnique`
**Importancia**: high

#### Unicidad del Conjunto Potencia (powerset_eq_iff)

**Ubicación**: `PowerSet.lean`, línea 53  
**Orden**: 2º teorema de especificación

**Enunciado Matemático**: (∀x, x ∈ P ↔ x ⊆ A) ↔ P = 𝒫(A).

**Firma Lean4**:

```lean
@[simp] theorem powerset_eq_iff (A P : U) :
  (∀ (x : U), x ∈ P ↔ x ⊆ A) ↔ (P = 𝒫 A)
```

**Dependencias**: `ExtSet`, `mem_powerset_iff`
**Importancia**: medium

#### El Vacío Pertenece a Todo Conjunto Potencia (empty_mem_powerset)

**Ubicación**: `PowerSet.lean`, línea 68  
**Orden**: 1º teorema de propiedades básicas

**Enunciado Matemático**: ∅ ∈ 𝒫(A) para todo A.

**Firma Lean4**:

```lean
theorem empty_mem_powerset (A : U) : ∅ ∈ (𝒫 A)
```

**Dependencias**: `mem_powerset_iff`, `EmptySet_subseteq_any`
**Importancia**: medium

#### Todo Conjunto Pertenece a su Conjunto Potencia (self_mem_powerset)

**Ubicación**: `PowerSet.lean`, línea 75  
**Orden**: 2º teorema de propiedades básicas

**Enunciado Matemático**: A ∈ 𝒫(A) para todo A.

**Firma Lean4**:

```lean
theorem self_mem_powerset (A : U) : A ∈ (𝒫 A)
```

**Dependencias**: `mem_powerset_iff`, `subset_refl`
**Importancia**: medium

#### El Conjunto Potencia Nunca es Vacío (powerset_nonempty)

**Ubicación**: `PowerSet.lean`, línea 82  
**Orden**: 3º teorema de propiedades básicas

**Enunciado Matemático**: 𝒫(A) ≠ ∅ para todo A.

**Firma Lean4**:

```lean
theorem powerset_nonempty (A : U) : (𝒫 A) ≠ ∅
```

**Dependencias**: `empty_mem_powerset`, `EmptySet_is_empty`
**Importancia**: medium

#### Conjunto Potencia del Vacío (powerset_empty)

**Ubicación**: `PowerSet.lean`, línea 91  
**Orden**: 4º teorema de propiedades básicas

**Enunciado Matemático**: 𝒫(∅) = {∅}.

**Firma Lean4**:

```lean
theorem powerset_empty : (𝒫 (∅ : U)) = ({∅} : U)
```

**Dependencias**: `ExtSet`, `mem_powerset_iff`, `Singleton_is_specified`, `EmptySet_is_empty`
**Importancia**: low

#### Monotonicidad del Conjunto Potencia (powerset_mono)

**Ubicación**: `PowerSet.lean`, línea 111  
**Orden**: 1º teorema de relaciones con subconjuntos

**Enunciado Matemático**: Si A ⊆ B, entonces 𝒫(A) ⊆ 𝒫(B).

**Firma Lean4**:

```lean
theorem powerset_mono (A B : U) (h : A ⊆ B) : (𝒫 A) ⊆ (𝒫 B)
```

**Dependencias**: `mem_powerset_iff`, `subset_trans`
**Importancia**: high

#### Caracterización Bidireccional de Monotonicidad (powerset_mono_iff)

**Ubicación**: `PowerSet.lean`, línea 119  
**Orden**: 2º teorema de relaciones con subconjuntos

**Enunciado Matemático**: 𝒫(A) ⊆ 𝒫(B) ↔ A ⊆ B.

**Firma Lean4**:

```lean
theorem powerset_mono_iff (A B : U) : (𝒫 A) ⊆ (𝒫 B) ↔ A ⊆ B
```

**Dependencias**: `powerset_mono`, `self_mem_powerset`, `mem_powerset_iff`
**Importancia**: medium

#### Intersección de Conjuntos Potencia (powerset_inter)

**Ubicación**: `PowerSet.lean`, línea 138  
**Orden**: 1º teorema de relaciones con unión/intersección

**Enunciado Matemático**: 𝒫(A) ∩ 𝒫(B) = 𝒫(A ∩ B).

**Firma Lean4**:

```lean
theorem powerset_inter (A B : U) : ((𝒫 A) ∩ (𝒫 B)) = (𝒫 (A ∩ B))
```

**Dependencias**: `ExtSet`, `mem_inter_iff`, `mem_powerset_iff`
**Importancia**: medium

#### Unión de Conjuntos Potencia (powerset_union_subset)

**Ubicación**: `PowerSet.lean`, línea 165  
**Orden**: 2º teorema de relaciones con unión/intersección

**Enunciado Matemático**: 𝒫(A) ∪ 𝒫(B) ⊆ 𝒫(A ∪ B) (la igualdad NO vale en general).

**Firma Lean4**:

```lean
theorem powerset_union_subset (A B : U) : ((𝒫 A) ∪ (𝒫 B)) ⊆ (𝒫 (A ∪ B))
```

**Dependencias**: `mem_union_iff`, `mem_powerset_iff`
**Importancia**: medium

#### Subconjunto en Conjunto Potencia de Unión (subset_powerset_sUnion)

**Ubicación**: `PowerSet.lean`, línea 181  
**Orden**: 1º teorema de relaciones con unión generalizada

**Enunciado Matemático**: A ⊆ 𝒫(⋃ A) para cualquier familia A.

**Firma Lean4**:

```lean
theorem subset_powerset_sUnion (A : U) : A ⊆ (𝒫 (⋃ A))
```

**Dependencias**: `mem_powerset_iff`, `mem_sUnion_iff`
**Importancia**: medium

#### Unión del Conjunto Potencia (sUnion_powerset)

**Ubicación**: `PowerSet.lean`, línea 189  
**Orden**: 2º teorema de relaciones con unión generalizada

**Enunciado Matemático**: ⋃ 𝒫(A) = A.

**Firma Lean4**:

```lean
theorem sUnion_powerset (A : U) : ⋃ (𝒫 A) = A
```

**Dependencias**: `ExtSet`, `mem_sUnion_iff`, `mem_powerset_iff`, `Singleton_is_specified`
**Importancia**: medium

### 4.4 SetOps.CartesianProduct.lean

#### Caracterización del Producto

**Ubicación**: `SetOps.CartesianProduct.lean`, línea 30  
**Orden**: 1º teorema principal

**Enunciado Matemático**: p ∈ A × B ↔ (isOrderedPair p ∧ fst p ∈ A ∧ snd p ∈ B).

**Firma Lean4**:

```lean
theorem CartesianProduct_is_specified (A B p : U) :
  p ∈ (A ×ₛ B) ↔ (isOrderedPair p ∧ fst p ∈ A ∧ snd p ∈ B)
```

**Dependencias**: `sep`, `PowerSet`, `OrderedPair`
**Importancia**: high

#### Caracterización con Par Ordenado Explícito

**Ubicación**: `SetOps.CartesianProduct.lean`, línea 50  
**Orden**: 2º teorema principal

**Enunciado Matemático**: ⟨a,b⟩ ∈ A × B ↔ (a ∈ A ∧ b ∈ B).

**Firma Lean4**:

```lean
theorem OrderedPair_mem_CartesianProduct (a b A B : U) :
  ⟨ a , b ⟩ ∈ (A ×ₛ B) ↔ (a ∈ A ∧ b ∈ B)
```

**Dependencias**: `CartesianProduct_is_specified`, `fst_of_ordered_pair`, `snd_of_ordered_pair`
**Importancia**: high

#### Producto con Conjunto Vacío (Izquierda)

**Ubicación**: `SetOps.CartesianProduct.lean`, línea 62  
**Orden**: 3º teorema principal

**Enunciado Matemático**: ∅ × B = ∅.

**Firma Lean4**:

```lean
theorem CartesianProduct_empty_left (B : U) :
  (∅ ×ₛ B) = ∅
```

**Dependencias**: `ExtSet`, `CartesianProduct_is_specified`, `EmptySet_is_empty`
**Importancia**: medium

#### Producto con Conjunto Vacío (Derecha)

**Ubicación**: `SetOps.CartesianProduct.lean`, línea 72  
**Orden**: 4º teorema principal

**Enunciado Matemático**: A × ∅ = ∅.

**Firma Lean4**:

```lean
theorem CartesianProduct_empty_right (A : U) :
  (A ×ₛ ∅) = ∅
```

**Dependencias**: `ExtSet`, `CartesianProduct_is_specified`, `EmptySet_is_empty`
**Importancia**: medium

#### Monotonicidad del Producto Cartesiano

**Ubicación**: `SetOps.CartesianProduct.lean`, línea 82  
**Orden**: 5º teorema principal

**Enunciado Matemático**: Si A ⊆ A' y B ⊆ B', entonces A × B ⊆ A' × B'.

**Firma Lean4**:

```lean
theorem CartesianProduct_mono (A A' B B' : U)
  (hA : A ⊆ A') (hB : B ⊆ B') :
    (A ×ₛ B) ⊆ (A' ×ₛ B')
```

**Dependencias**: `CartesianProduct_is_specified`, `subset`
**Importancia**: high

#### Distributividad con Unión (Izquierda)

**Ubicación**: `SetOps.CartesianProduct.lean`, línea 89  
**Orden**: 6º teorema principal

**Enunciado Matemático**: (A ∪ B) × C = (A × C) ∪ (B × C).

**Firma Lean4**:

```lean
theorem CartesianProduct_distrib_union_left (A B C : U) :
  ((A ∪ B) ×ₛ C) = ((A ×ₛ C) ∪ (B ×ₛ C))
```

**Dependencias**: `ExtSet`, `CartesianProduct_is_specified`, `mem_union_iff`
**Importancia**: medium

#### Distributividad con Unión (Derecha)

**Ubicación**: `SetOps.CartesianProduct.lean`, línea 115  
**Orden**: 7º teorema principal

**Enunciado Matemático**: A × (B ∪ C) = (A × B) ∪ (A × C).

**Firma Lean4**:

```lean
theorem CartesianProduct_distrib_union_right (A B C : U) :
  (A ×ₛ (B ∪ C)) = ((A ×ₛ B) ∪ (A ×ₛ C))
```

**Dependencias**: `ExtSet`, `CartesianProduct_is_specified`, `mem_union_iff`
**Importancia**: medium

#### Distributividad con Intersección (Izquierda)

**Ubicación**: `SetOps.CartesianProduct.lean`, línea 141  
**Orden**: 8º teorema principal

**Enunciado Matemático**: (A ∩ B) × C = (A × C) ∩ (B × C).

**Firma Lean4**:

```lean
theorem CartesianProduct_distrib_inter_left (A B C : U) :
  ((A ∩ B) ×ₛ C) = ((A ×ₛ C) ∩ (B ×ₛ C))
```

**Dependencias**: `ExtSet`, `CartesianProduct_is_specified`, `mem_inter_iff`
**Importancia**: medium

#### Distributividad con Intersección (Derecha)

**Ubicación**: `SetOps.CartesianProduct.lean`, línea 165  
**Orden**: 9º teorema principal

**Enunciado Matemático**: A × (B ∩ C) = (A × B) ∩ (A × C).

**Firma Lean4**:

```lean
theorem CartesianProduct_distrib_inter_right (A B C : U) :
  (A ×ₛ (B ∩ C)) = ((A ×ₛ B) ∩ (A ×ₛ C))
```

**Dependencias**: `ExtSet`, `CartesianProduct_is_specified`, `mem_inter_iff`
**Importancia**: medium

### 4.5 Relations.lean

#### La Asimetría Implica Irreflexividad

**Ubicación**: `SetOps.Relations.lean`, línea 168  
**Orden**: 1º teorema principal

**Enunciado Matemático**: Si R es asimétrica en A, entonces R es irreflexiva en A.

**Firma Lean4**:

```lean
theorem Asymmetric_implies_Irreflexive (R A : U) :
    isAsymmetricOn R A → isIrreflexiveOn R A
```

**Dependencias**: `isAsymmetricOn`, `isIrreflexiveOn`
**Importancia**: medium

#### Un Orden Estricto es Irreflexivo

**Ubicación**: `SetOps.Relations.lean`, línea 173  
**Orden**: 2º teorema principal

**Enunciado Matemático**: Si R es un orden estricto en A, entonces R es irreflexiva en A.

**Firma Lean4**:

```lean
theorem StrictOrder_is_Irreflexive (R A : U) :
    isStrictOrderOn R A → isIrreflexiveOn R A
```

**Dependencias**: `isStrictOrderOn`, `isIrreflexiveOn`
**Importancia**: medium

#### Un Orden Parcial Estricto es Irreflexivo

**Ubicación**: `SetOps.Relations.lean`, línea 178  
**Orden**: 3º teorema principal

**Enunciado Matemático**: Si R es un orden parcial estricto en A, entonces R es irreflexiva en A.

**Firma Lean4**:

```lean
theorem StrictPartialOrder_is_Irreflexive (R A : U) :
    isStrictPartialOrderOn R A → isIrreflexiveOn R A
```

**Dependencias**: `isStrictPartialOrderOn`, `isIrreflexiveOn`, `Asymmetric_implies_Irreflexive`
**Importancia**: low

#### Irreflexiva y Transitiva Implica Asimétrica

**Ubicación**: `SetOps.Relations.lean`, línea 183  
**Orden**: 4º teorema principal

**Enunciado Matemático**: Si R es irreflexiva y transitiva en A, entonces R es asimétrica en A.

**Firma Lean4**:

```lean
theorem Irreflexive_Transitive_implies_Asymmetric (R A : U) :
    isIrreflexiveOn R A → isTransitiveOn R A →
    isAsymmetricOn R A
```

**Dependencias**: `isIrreflexiveOn`, `isTransitiveOn`, `isAsymmetricOn`
**Importancia**: medium

#### Asimetría Equivale a Irreflexividad más Antisimetría

**Ubicación**: `SetOps.Relations.lean`, línea 189  
**Orden**: 5º teorema principal

**Enunciado Matemático**: Para relaciones transitivas, asimetría es equivalente a irreflexividad más antisimetría.

**Firma Lean4**:

```lean
theorem Asymmetric_iff_Irreflexive_and_AntiSymmetric (R A : U)
    (hTrans : isTransitiveOn R A) :
    isAsymmetricOn R A ↔ isIrreflexiveOn R A ∧ isAntiSymmetricOn R A
```

**Dependencias**: `isAsymmetricOn`, `isIrreflexiveOn`, `isAntiSymmetricOn`, `isTransitiveOn`
**Importancia**: medium

#### Orden Parcial con Conexidad es Orden Lineal

**Ubicación**: `SetOps.Relations.lean`, línea 200  
**Orden**: 6º teorema principal

**Enunciado Matemático**: Un orden parcial con conexidad es un orden lineal.

**Firma Lean4**:

```lean
theorem PartialOrder_Connected_is_LinearOrder (R A : U) :
    isPartialOrderOn R A → isConnectedOn R A → isLinearOrderOn R A
```

**Dependencias**: `isPartialOrderOn`, `isConnectedOn`, `isLinearOrderOn`
**Importancia**: high

#### Orden Lineal: Elementos Comparables

**Ubicación**: `SetOps.Relations.lean`, línea 204  
**Orden**: 7º teorema principal

**Enunciado Matemático**: En un orden lineal, cualesquiera dos elementos son comparables.

**Firma Lean4**:

```lean
theorem LinearOrder_comparable (R A : U) (hLO : isLinearOrderOn R A)
    (x y : U) (hxA : x ∈ A) (hyA : y ∈ A) :
    ⟨x, y⟩ ∈ R ∨ ⟨y, x⟩ ∈ R
```

**Dependencias**: `isLinearOrderOn`, `OrderedPair`
**Importancia**: medium

#### Orden Estricto con Conexidad es Tricotómico

**Ubicación**: `SetOps.Relations.lean`, línea 215  
**Orden**: 8º teorema principal

**Enunciado Matemático**: Un orden estricto con conexidad es tricotómico.

**Firma Lean4**:

```lean
theorem StrictOrder_Connected_is_Trichotomous (R A : U)
    (hStrict : isStrictOrderOn R A) (hConn : isConnectedOn R A) :
    isTrichotomousOn R A
```

**Dependencias**: `isStrictOrderOn`, `isConnectedOn`, `isTrichotomousOn`, `Irreflexive_Transitive_implies_Asymmetric`
**Importancia**: high

#### Orden Lineal Estricto Equivale a Orden Estricto Conexo

**Ubicación**: `SetOps.Relations.lean`, línea 242  
**Orden**: 9º teorema principal

**Enunciado Matemático**: Un orden lineal estricto es equivalente a un orden estricto que es conexo.

**Firma Lean4**:

```lean
theorem StrictLinearOrder_iff_StrictOrder_Connected (R A : U) :
    isStrictLinearOrderOn R A ↔ isStrictOrderOn R A ∧ isConnectedOn R A
```

**Dependencias**: `isStrictLinearOrderOn`, `isStrictOrderOn`, `isConnectedOn`, `StrictOrder_Connected_is_Trichotomous`
**Importancia**: high

#### Pertenencia en Relación Identidad

**Ubicación**: `SetOps.Relations.lean`, línea 258  
**Orden**: 10º teorema principal

**Enunciado Matemático**: ⟨x, y⟩ ∈ IdRel A ↔ x ∈ A ∧ x = y.

**Firma Lean4**:

```lean
theorem mem_IdRel (A x y : U) :
    ⟨x, y⟩ ∈ IdRel A ↔ x ∈ A ∧ x = y
```

**Dependencias**: `IdRel`, `mem_sep_iff`, `OrderedPair_mem_CartesianProduct`, `fst_of_ordered_pair`, `snd_of_ordered_pair`
**Importancia**: high

#### La Relación Identidad es de Equivalencia

**Ubicación**: `SetOps.Relations.lean`, línea 271  
**Orden**: 11º teorema principal

**Enunciado Matemático**: La relación identidad IdRel A es una relación de equivalencia en A.

**Firma Lean4**:

```lean
theorem IdRel_is_Equivalence (A : U) :
    isEquivalenceOn (IdRel A) A
```

**Dependencias**: `IdRel`, `isEquivalenceOn`, `mem_IdRel`
**Importancia**: medium

#### Pertenencia en Clase de Equivalencia

**Ubicación**: `SetOps.Relations.lean`, línea 289  
**Orden**: 12º teorema principal

**Enunciado Matemático**: x ∈ EqClass a R A ↔ x ∈ A ∧ ⟨a,x⟩ ∈ R.

**Firma Lean4**:

```lean
theorem mem_EqClass (a R A x : U) :
    x ∈ EqClass a R A ↔ x ∈ A ∧ ⟨a, x⟩ ∈ R
```

**Dependencias**: `EqClass`, `mem_sep_iff`
**Importancia**: high

#### Elemento en su Propia Clase de Equivalencia

**Ubicación**: `SetOps.Relations.lean`, línea 294  
**Orden**: 13º teorema principal

**Enunciado Matemático**: Para una relación de equivalencia, a está en su propia clase de equivalencia.

**Firma Lean4**:

```lean
theorem EqClass_mem_self (R A a : U)
    (hEq : isEquivalenceOn R A) (haA : a ∈ A) :
    a ∈ EqClass a R A
```

**Dependencias**: `EqClass`, `isEquivalenceOn`, `mem_EqClass`
**Importancia**: medium

#### Relacionados Pertenecen a la Misma Clase

**Ubicación**: `SetOps.Relations.lean`, línea 301  
**Orden**: 14º teorema principal

**Enunciado Matemático**: Si (a, b) ∈ R y b ∈ A, entonces b ∈ EqClass a R A.

**Firma Lean4**:

```lean
theorem mem_EqClass_of_Related (R A a b : U)
    (_ : isEquivalenceOn R A) (hbA : b ∈ A) (hab : ⟨a, b⟩ ∈ R) :
    b ∈ EqClass a R A
```

**Dependencias**: `EqClass`, `isEquivalenceOn`, `mem_EqClass`
**Importancia**: medium

#### Pertenencia Implica Relación

**Ubicación**: `SetOps.Relations.lean`, línea 308  
**Orden**: 15º teorema principal

**Enunciado Matemático**: Si b ∈ EqClass a R A, entonces (a, b) ∈ R.

**Firma Lean4**:

```lean
theorem Related_of_mem_EqClass (R A a b : U)
    (_ : isEquivalenceOn R A) (hb : b ∈ EqClass a R A) :
    ⟨a, b⟩ ∈ R
```

**Dependencias**: `EqClass`, `isEquivalenceOn`, `mem_EqClass`
**Importancia**: medium

#### Caracterización de Pertenencia a Clase

**Ubicación**: `SetOps.Relations.lean`, línea 314  
**Orden**: 16º teorema principal

**Enunciado Matemático**: Para relaciones de equivalencia, b ∈ EqClass a R A ↔ (a, b) ∈ R.

**Firma Lean4**:

```lean
theorem mem_EqClass_iff (R A a b : U)
    (hEq : isEquivalenceOn R A) (hbA : b ∈ A) :
    b ∈ EqClass a R A ↔ ⟨a, b⟩ ∈ R
```

**Dependencias**: `EqClass`, `isEquivalenceOn`, `mem_EqClass`, `Related_of_mem_EqClass`, `mem_EqClass_of_Related`
**Importancia**: high

#### Igualdad de Clases de Equivalencia

**Ubicación**: `SetOps.Relations.lean`, línea 321  
**Orden**: 17º teorema principal

**Enunciado Matemático**: Para relaciones de equivalencia, EqClass a R A = EqClass b R A ↔ ⟨a,b⟩ ∈ R.

**Firma Lean4**:

```lean
theorem EqClass_eq_iff (R A a b : U)
    (hEq : isEquivalenceOn R A) (haA : a ∈ A) (hbA : b ∈ A) :
    EqClass a R A = EqClass b R A ↔ ⟨a, b⟩ ∈ R
```

**Dependencias**: `EqClass`, `isEquivalenceOn`, `ExtSet`
**Importancia**: high

#### Las Clases de Equivalencia Particionan el Conjunto

**Ubicación**: `SetOps.Relations.lean`, línea 352  
**Orden**: 18º teorema principal

**Enunciado Matemático**: Las clases de equivalencia son iguales o disjuntas.

**Firma Lean4**:

```lean
theorem EqClass_eq_or_disjoint (R A a b : U)
    (hEq : isEquivalenceOn R A) (haA : a ∈ A) (hbA : b ∈ A) :
    EqClass a R A = EqClass b R A ∨ inter (EqClass a R A) (EqClass b R A) = ∅
```

**Dependencias**: `EqClass`, `isEquivalenceOn`, `inter`, `EmptySet`
**Importancia**: high

#### Caracterización de Pertenencia al Dominio

**Ubicación**: `SetOps.Relations.lean`, línea 386  
**Orden**: 19º teorema principal

**Enunciado Matemático**: x es miembro del dominio de R si y solo si existe y tal que ⟨x, y⟩ ∈ R.

**Firma Lean4**:

```lean
theorem mem_domain (R x : U) :
    x ∈ domain R ↔ ∃ y, ⟨x, y⟩ ∈ R
```

**Dependencias**: `domain`, `mem_sep_iff`
**Importancia**: high

#### Caracterización de Pertenencia al Rango

**Ubicación**: `SetOps.Relations.lean`, línea 403  
**Orden**: 20º teorema principal

**Enunciado Matemático**: y es miembro del rango de R si y solo si existe x tal que ⟨x, y⟩ ∈ R.

**Firma Lean4**:

```lean
theorem mem_range (R y : U) :
    y ∈ range R ↔ ∃ x, ⟨x, y⟩ ∈ R
```

**Dependencias**: `range`, `mem_sep_iff`
**Importancia**: high

#### Caracterización de Pertenencia a la Imagen

**Ubicación**: `SetOps.Relations.lean`, línea 420  
**Orden**: 21º teorema principal

**Enunciado Matemático**: y es miembro de la imagen de R si y solo si existe x tal que ⟨x, y⟩ ∈ R.

**Firma Lean4**:

```lean
theorem mem_imag (R y : U) :
    y ∈ imag R ↔ ∃ x, ⟨x, y⟩ ∈ R
```

**Dependencias**: `imag`, `mem_range`
**Importancia**: medium

#### Par en Relación Implica Primera Componente en Dominio

**Ubicación**: `SetOps.Relations.lean`, línea 424  
**Orden**: 22º teorema principal

**Enunciado Matemático**: Si ⟨x, y⟩ ∈ R, entonces x ∈ domain R.

**Firma Lean4**:

```lean
theorem pair_mem_implies_fst_in_domain (R x y : U) :
    ⟨x, y⟩ ∈ R → x ∈ domain R
```

**Dependencias**: `domain`, `mem_domain`
**Importancia**: medium

#### Par en Relación Implica Segunda Componente en Rango

**Ubicación**: `SetOps.Relations.lean`, línea 429  
**Orden**: 23º teorema principal

**Enunciado Matemático**: Si ⟨x, y⟩ ∈ R, entonces y ∈ range R.

**Firma Lean4**:

```lean
theorem pair_mem_implies_snd_in_range (R x y : U) :
    ⟨x, y⟩ ∈ R → y ∈ range R
```

**Dependencias**: `range`, `mem_range`
**Importancia**: medium

#### Par en Relación Implica Segunda Componente en Imagen

**Ubicación**: `SetOps.Relations.lean`, línea 434  
**Orden**: 24º teorema principal

**Enunciado Matemático**: Si ⟨x, y⟩ ∈ R, entonces y ∈ imag R.

**Firma Lean4**:

```lean
theorem pair_mem_implies_snd_in_imag (R x y : U) :
    ⟨x, y⟩ ∈ R → y ∈ imag R
```

**Dependencias**: `imag`, `mem_imag`
**Importancia**: medium

### 4.6 Functions.lean

#### Especificación del Dominio

**Ubicación**: `SetOps.Functions.lean`, línea 47  
**Orden**: 1º teorema principal

**Enunciado Matemático**: x ∈ Dom f ↔ ∃y, ⟨x,y⟩ ∈ f.

**Firma Lean4**:

```lean
theorem Dom_is_specified (f x : U) :
    x ∈ Dom f ↔ ∃ y, ⟨x, y⟩ ∈ f
```

**Dependencias**: `Dom`, `mem_sep_iff`
**Importancia**: high

#### Especificación del Rango

**Ubicación**: `SetOps.Functions.lean`, línea 58  
**Orden**: 2º teorema principal

**Enunciado Matemático**: y ∈ Ran f ↔ ∃x, ⟨x,y⟩ ∈ f.

**Firma Lean4**:

```lean
theorem Ran_is_specified (f y : U) :
    y ∈ Ran f ↔ ∃ x, ⟨x, y⟩ ∈ f
```

**Dependencias**: `Ran`, `mem_sep_iff`
**Importancia**: high

#### Corrección de la Aplicación

**Ubicación**: `SetOps.Functions.lean`, línea 70  
**Orden**: 3º teorema principal

**Enunciado Matemático**: Si f es univaluada y ⟨x,y⟩ ∈ f, entonces f⦅x⦆ = y.

**Firma Lean4**:

```lean
theorem apply_eq (f x y : U) (hf : IsSingleValued f) (hxy : ⟨x, y⟩ ∈ f) :
    f⦅x⦆ = y
```

**Dependencias**: `apply`, `IsSingleValued`, `Classical.choose_spec`
**Importancia**: high

#### Aplicación da Membresía

**Ubicación**: `SetOps.Functions.lean`, línea 78  
**Orden**: 4º teorema principal

**Enunciado Matemático**: Si x ∈ Dom f y f es univaluada, entonces ⟨x, f⦅x⦆⟩ ∈ f.

**Firma Lean4**:

```lean
theorem apply_mem (f x : U) (hf : IsSingleValued f) (hx : x ∈ Dom f) :
    ⟨x, f⦅x⦆⟩ ∈ f
```

**Dependencias**: `apply`, `Dom_is_specified`, `apply_eq`
**Importancia**: high

#### Especificación de Función Identidad

**Ubicación**: `SetOps.Functions.lean`, línea 90  
**Orden**: 5º teorema principal

**Enunciado Matemático**: ⟨x,y⟩ ∈ 𝟙 A ↔ x ∈ A ∧ x = y.

**Firma Lean4**:

```lean
theorem idFn_is_specified (A x y : U) :
    ⟨x, y⟩ ∈ (𝟙 A) ↔ x ∈ A ∧ x = y
```

**Dependencias**: `idFn`, `mem_sep_iff`, `OrderedPair_eq_iff`
**Importancia**: medium

#### Identidad es Univaluada

**Ubicación**: `SetOps.Functions.lean`, línea 102  
**Orden**: 6º teorema principal

**Enunciado Matemático**: 𝟙 A es univaluada.

**Firma Lean4**:

```lean
theorem idFn_single_valued (A : U) : IsSingleValued (𝟙 A)
```

**Dependencias**: `idFn`, `IsSingleValued`, `idFn_is_specified`
**Importancia**: medium

#### Identidad es Función

**Ubicación**: `SetOps.Functions.lean`, línea 107  
**Orden**: 7º teorema principal

**Enunciado Matemático**: 𝟙 A es función de A a A.

**Firma Lean4**:

```lean
theorem idFn_is_function (A : U) : IsFunction (𝟙 A) A A
```

**Dependencias**: `idFn`, `IsFunction`, `idFn_single_valued`
**Importancia**: medium

#### Aplicación de Identidad

**Ubicación**: `SetOps.Functions.lean`, línea 115  
**Orden**: 8º teorema principal

**Enunciado Matemático**: (𝟙 A)⦅x⦆ = x para x ∈ A.

**Firma Lean4**:

```lean
theorem apply_id (A x : U) (hx : x ∈ A) : (𝟙 A)⦅x⦆ = x
```

**Dependencias**: `apply_eq`, `idFn_single_valued`, `idFn_is_specified`
**Importancia**: medium

#### Especificación de Composición

**Ubicación**: `SetOps.Functions.lean`, línea 135  
**Orden**: 9º teorema principal

**Enunciado Matemático**: ⟨x,z⟩ ∈ g ∘ₛ f ↔ ∃y, ⟨x,y⟩ ∈ f ∧ ⟨y,z⟩ ∈ g.

**Firma Lean4**:

```lean
theorem comp_is_specified (g f x z : U) :
    ⟨x, z⟩ ∈ (g ∘ₛ f) ↔ ∃ y, ⟨x, y⟩ ∈ f ∧ ⟨y, z⟩ ∈ g
```

**Dependencias**: `comp`, `mem_sep_iff`, `OrderedPair_eq_iff`
**Importancia**: high

#### Composición Preserva Univaluación

**Ubicación**: `SetOps.Functions.lean`, línea 147  
**Orden**: 10º teorema principal

**Enunciado Matemático**: Si f y g son univaluadas, entonces g ∘ₛ f es univaluada.

**Firma Lean4**:

```lean
theorem comp_single_valued (g f : U) (hf : IsSingleValued f) (hg : IsSingleValued g) :
    IsSingleValued (g ∘ₛ f)
```

**Dependencias**: `IsSingleValued`, `comp_is_specified`
**Importancia**: medium

#### Composición de Funciones es Función

**Ubicación**: `SetOps.Functions.lean`, línea 155  
**Orden**: 11º teorema principal

**Enunciado Matemático**: Si f: A → B y g: B → C son funciones, entonces g ∘ₛ f: A → C es función.

**Firma Lean4**:

```lean
theorem comp_is_function (f g A B C : U)
    (hf : IsFunction f A B) (hg : IsFunction g B C) :
    IsFunction (g ∘ₛ f) A C
```

**Dependencias**: `IsFunction`, `comp_single_valued`, `comp_is_specified`
**Importancia**: high

#### Composición con Identidad (Derecha)

**Ubicación**: `SetOps.Functions.lean`, línea 175  
**Orden**: 12º teorema principal

**Enunciado Matemático**: f ∘ₛ 𝟙 A = f para f: A → B.

**Firma Lean4**:

```lean
theorem comp_id_right (f A B : U) (hf : IsFunction f A B) :
    (f ∘ₛ 𝟙 A) = f
```

**Dependencias**: `comp`, `idFn`, `ExtSet`
**Importancia**: medium

#### Composición con Identidad (Izquierda)

**Ubicación**: `SetOps.Functions.lean`, línea 190  
**Orden**: 13º teorema principal

**Enunciado Matemático**: 𝟙 B ∘ₛ f = f para f: A → B.

**Firma Lean4**:

```lean
theorem comp_id_left (f A B : U) (hf : IsFunction f A B) :
    ((𝟙 B) ∘ₛ f) = f
```

**Dependencias**: `comp`, `idFn`, `ExtSet`
**Importancia**: medium

#### Especificación de Función Inversa

**Ubicación**: `SetOps.Functions.lean`, línea 135  
**Orden**: 14º teorema principal

**Enunciado Matemático**: p ∈ f⁻¹ ↔ isOrderedPair p ∧ ⟨snd p, fst p⟩ ∈ f.

**Firma Lean4**:

```lean
theorem inverse_is_specified (f p : U) :
    p ∈ f⁻¹ ↔ isOrderedPair p ∧ ⟨snd p, fst p⟩ ∈ f
```

**Dependencias**: `inv`, `InverseRel`, `mem_sep_iff`
**Importancia**: high

#### Especificación de Restricción (mem_restrict_iff)

**Ubicación**: `SetOps.Functions.lean`, línea 162  
**Orden**: 15º teorema principal

**Enunciado Matemático**: p ∈ (f ↾ C) ↔ p ∈ f ∧ fst p ∈ C.

**Firma Lean4**:

```lean
theorem mem_restrict_iff (f C p : U) :
    p ∈ (f ↾ C) ↔ p ∈ f ∧ fst p ∈ C
```

**Dependencias**: `restrict`, `mem_sep_iff`
**Importancia**: medium

#### Restricción es Subconjunto (restrict_subset)

**Ubicación**: `SetOps.Functions.lean`, línea 167  
**Orden**: 16º teorema principal

**Enunciado Matemático**: (f ↾ C) ⊆ f.

**Firma Lean4**:

```lean
theorem restrict_subset (f C : U) : (f ↾ C) ⊆ f
```

**Dependencias**: `restrict`, `mem_restrict_iff`
**Importancia**: low

#### Restricción de Función es Función (restrict_is_function)

**Ubicación**: `SetOps.Functions.lean`, línea 172  
**Orden**: 17º teorema principal

**Enunciado Matemático**: Si f: A → B y C ⊆ A, entonces (f ↾ C): C → B.

**Firma Lean4**:

```lean
theorem restrict_is_function (f A B C : U)
    (hf : IsFunction f A B) (hC : C ⊆ A) :
    IsFunction (f ↾ C) C B
```

**Dependencias**: `restrict`, `IsFunction`, `mem_restrict_iff`, `CartesianProduct_is_specified`
**Importancia**: medium

#### Aplicación de Restricción (restrict_apply)

**Ubicación**: `SetOps.Functions.lean`, línea 192  
**Orden**: 18º teorema principal

**Enunciado Matemático**: Para x ∈ C, (f ↾ C)⦅x⦆ = f⦅x⦆.

**Firma Lean4**:

```lean
theorem restrict_apply (f C x : U) (hx : x ∈ C) :
    apply (f ↾ C) x = apply f x
```

**Dependencias**: `restrict`, `apply`, `mem_restrict_iff`, `fst_of_ordered_pair`
**Importancia**: medium

#### Inyectiva Implica Inversa Univaluada

**Ubicación**: `SetOps.Functions.lean`, línea 251  
**Orden**: 19º teorema principal

**Enunciado Matemático**: Si f es inyectiva, entonces f⁻¹ es univaluada.

**Firma Lean4**:

```lean
theorem injective_inverse_single_valued (f : U) (hf : isInjective f) :
    IsSingleValued (f⁻¹)
```

**Dependencias**: `isInjective`, `IsSingleValued`, `inverse_is_specified`, `fst_of_ordered_pair`, `snd_of_ordered_pair`
**Importancia**: medium

#### Univaluada Implica Inversa Inyectiva

**Ubicación**: `SetOps.Functions.lean`, línea 223  
**Orden**: 16º teorema principal

**Enunciado Matemático**: Si f es univaluada, entonces f⁻¹ˢ es inyectiva.

**Firma Lean4**:

```lean
theorem single_valued_inverse_injective (f : U) (hf : IsSingleValued f) :
    isInjective (f⁻¹ˢ)
```

**Dependencias**: `IsSingleValued`, `isInjective`, `inverse_is_specified`
**Importancia**: medium

#### Caracterización de Inyectividad

**Ubicación**: `SetOps.Functions.lean`, línea 250  
**Orden**: 17º teorema principal

**Enunciado Matemático**: f es inyectiva ↔ f⁻¹ˢ es univaluada.

**Firma Lean4**:

```lean
theorem injective_iff_inverse_functional (f : U) :
    isInjective f ↔ IsSingleValued (f⁻¹ˢ)
```

**Dependencias**: `isInjective`, `IsSingleValued`, `injective_inverse_single_valued`
**Importancia**: high

#### Inyectividad y Aplicación

**Ubicación**: `SetOps.Functions.lean`, línea 258  
**Orden**: 18º teorema principal

**Enunciado Matemático**: Para función inyectiva, f⦅x₁⦆ = f⦅x₂⦆ → x₁ = x₂.

**Firma Lean4**:

```lean
theorem injective_apply_eq (f A B x₁ x₂ : U)
    (hf : IsFunction f A B) (hinj : isInjective f)
    (hx₁ : x₁ ∈ A) (hx₂ : x₂ ∈ A) (heq : f⦅x₁⦆ = f⦅x₂⦆) : x₁ = x₂
```

**Dependencias**: `isInjective`, `IsFunction`, `apply_eq`
**Importancia**: high

#### Caracterización de Suryectividad

**Ubicación**: `SetOps.Functions.lean`, línea 270  
**Orden**: 19º teorema principal

**Enunciado Matemático**: f es suryectiva en B ↔ Ran f = B.

**Firma Lean4**:

```lean
theorem surjective_iff_range_eq (f A B : U) (hf : IsFunction f A B) :
    isSurjectiveOnto f B ↔ Ran f = B
```

**Dependencias**: `isSurjectiveOnto`, `Ran`, `ExtSet`
**Importancia**: high

#### Suryectiva Implica Inversa Total

**Ubicación**: `SetOps.Functions.lean`, línea 285  
**Orden**: 20º teorema principal

**Enunciado Matemático**: Si f: A → B es suryectiva, entonces f⁻¹ˢ es total en B.

**Firma Lean4**:

```lean
theorem surjective_inverse_total (f A B : U)
    (_ : IsFunction f A B) (hsurj : isSurjectiveOnto f B) :
    ∀ y, y ∈ B → ∃ x, ⟨y, x⟩ ∈ f⁻¹ˢ
```

**Dependencias**: `isSurjectiveOnto`, `inverse_is_specified`
**Importancia**: medium

#### Biyección Implica Inversa es Función

**Ubicación**: `SetOps.Functions.lean`, línea 295  
**Orden**: 21º teorema principal

**Enunciado Matemático**: Si f: A → B es biyección, entonces f⁻¹ˢ: B → A es función.

**Firma Lean4**:

```lean
theorem bijection_inverse_is_function (f A B : U) (hbij : isBijection f A B) :
    IsFunction (f⁻¹ˢ) B A
```

**Dependencias**: `isBijection`, `IsFunction`, `injective_inverse_single_valued`
**Importancia**: high

#### Biyección: Composición con Inversa (Derecha)

**Ubicación**: `SetOps.Functions.lean`, línea 310  
**Orden**: 22º teorema principal

**Enunciado Matemático**: Para biyección f: A → B, (f⁻¹ˢ)⦅f⦅x⦆⦆ = x para x ∈ A.

**Firma Lean4**:

```lean
theorem bijection_comp_inverse_right (f A B : U) (hbij : isBijection f A B) :
    ∀ x, x ∈ A → (f⁻¹ˢ)⦅f⦅x⦆⦆ = x
```

**Dependencias**: `isBijection`, `apply_eq`, `inverse_is_specified`
**Importancia**: high

#### Biyección: Composición con Inversa (Izquierda)

**Ubicación**: `SetOps.Functions.lean`, línea 325  
**Orden**: 23º teorema principal

**Enunciado Matemático**: Para biyección f: A → B, f⦅(f⁻¹ˢ)⦅y⦆⦆ = y para y ∈ B.

**Firma Lean4**:

```lean
theorem bijection_comp_inverse_left (f A B : U) (hbij : isBijection f A B) :
    ∀ y, y ∈ B → f⦅(f⁻¹ˢ)⦅y⦆⦆ = y
```

**Dependencias**: `isBijection`, `apply_eq`, `inverse_is_specified`
**Importancia**: high

#### Inversa de Inversa

**Ubicación**: `SetOps.Functions.lean`, línea 340  
**Orden**: 24º teorema principal

**Enunciado Matemático**: Para f ⊆ A ×ₛ B, (f⁻¹ˢ)⁻¹ˢ = f.

**Firma Lean4**:

```lean
theorem inverse_inverse (f A B : U) (hf : f ⊆ A ×ₛ B) : (f⁻¹ˢ)⁻¹ˢ = f
```

**Dependencias**: `inv`, `ExtSet`, `inverse_is_specified`
**Importancia**: medium

#### Biyección Implica Invertibilidad

**Ubicación**: `SetOps.Functions.lean`, línea 365  
**Orden**: 25º teorema principal

**Enunciado Matemático**: Si f: A → B es biyección, entonces f es invertible.

**Firma Lean4**:

```lean
theorem bijection_implies_invertible (f A B : U) (hbij : isBijection f A B) :
    isInvertible f A B
```

**Dependencias**: `isBijection`, `isInvertible`, `bijection_inverse_is_function`
**Importancia**: high

#### Inverso Izquierdo Implica Inyectividad

**Ubicación**: `SetOps.Functions.lean`, línea 375  
**Orden**: 26º teorema principal

**Enunciado Matemático**: Si f tiene inverso por izquierda, entonces f es inyectiva.

**Firma Lean4**:

```lean
theorem left_invertible_implies_injective (f A B : U)
    (hf : IsFunction f A B) (hleft : isLeftInvertible f A B) :
    isInjective f
```

**Dependencias**: `isLeftInvertible`, `isInjective`, `apply_eq`
**Importancia**: medium

#### Inverso Derecho Implica Suryectividad

**Ubicación**: `SetOps.Functions.lean`, línea 395  
**Orden**: 27º teorema principal

**Enunciado Matemático**: Si f tiene inverso por derecha, entonces f es suryectiva.

**Firma Lean4**:

```lean
theorem right_invertible_implies_surjective (f A B : U)
    (hf : IsFunction f A B) (hright : isRightInvertible f A B) :
    isSurjectiveOnto f B
```

**Dependencias**: `isRightInvertible`, `isSurjectiveOnto`, `apply_mem`
**Importancia**: medium

#### Invertibilidad Implica Biyección

**Ubicación**: `SetOps.Functions.lean`, línea 415  
**Orden**: 28º teorema principal

**Enunciado Matemático**: Si f es invertible, entonces f es biyección.

**Firma Lean4**:

```lean
theorem invertible_implies_bijection (f A B : U)
    (hf : IsFunction f A B) (hinv : isInvertible f A B) :
    isBijection f A B
```

**Dependencias**: `isInvertible`, `isBijection`, `left_invertible_implies_injective`
**Importancia**: medium

#### Equivalencia Biyección-Invertibilidad

**Ubicación**: `SetOps.Functions.lean`, línea 425  
**Orden**: 29º teorema principal (TEOREMA CENTRAL)

**Enunciado Matemático**: f: A → B es biyección ↔ f es invertible.

**Firma Lean4**:

```lean
theorem bijection_iff_invertible (f A B : U) (hf : IsFunction f A B) :
    isBijection f A B ↔ isInvertible f A B
```

**Dependencias**: `isBijection`, `isInvertible`, `bijection_implies_invertible`
**Importancia**: high

#### Inversa de Biyección es Biyección

**Ubicación**: `SetOps.Functions.lean`, línea 405  
**Orden**: 30º teorema principal

**Enunciado Matemático**: Si f: A → B es biyección, entonces f⁻¹ˢ: B → A es biyección.

**Firma Lean4**:

```lean
theorem inverse_is_bijection (f A B : U) (hbij : isBijection f A B) :
    isBijection (f⁻¹ˢ) B A
```

**Dependencias**: `isBijection`, `inv`, `single_valued_inverse_injective`
**Importancia**: high

#### Equipotencia es Reflexiva

**Ubicación**: `SetOps.Functions.lean`, línea 435  
**Orden**: 31º teorema principal

**Enunciado Matemático**: A ≃ₛ A.

**Firma Lean4**:

```lean
theorem equipotent_refl (A : U) : A ≃ₛ A
```

**Dependencias**: `isEquipotent`, `idFn`, `id_is_bijection`
**Importancia**: high

#### Equipotencia es Simétrica

**Ubicación**: `SetOps.Functions.lean`, línea 440  
**Orden**: 32º teorema principal

**Enunciado Matemático**: A ≃ₛ B → B ≃ₛ A.

**Firma Lean4**:

```lean
theorem equipotent_symm (A B : U) (h : A ≃ₛ B) : B ≃ₛ A
```

**Dependencias**: `isEquipotent`, `inverse_is_bijection`
**Importancia**: high

#### Equipotencia es Transitiva

**Ubicación**: `SetOps.Functions.lean`, línea 445  
**Orden**: 33º teorema principal

**Enunciado Matemático**: A ≃ₛ B → B ≃ₛ C → A ≃ₛ C.

**Firma Lean4**:

```lean
theorem equipotent_trans (A B C : U) (hab : A ≃ₛ B) (hbc : B ≃ₛ C) : A ≃ₛ C
```

**Dependencias**: `isEquipotent`, `comp_bijection`
**Importancia**: high

#### Equipotencia es Relación de Equivalencia

**Ubicación**: `SetOps.Functions.lean`, línea 450  
**Orden**: 34º teorema principal

**Enunciado Matemático**: ≃ₛ es reflexiva, simétrica y transitiva.

**Firma Lean4**:

```lean
theorem equipotent_is_equivalence :
    (∀ (A : U), isEquipotent A A) ∧
    (∀ (A B : U), isEquipotent A B → isEquipotent B A) ∧
    (∀ (A B C : U), isEquipotent A B → isEquipotent B C → isEquipotent A C)
```

**Dependencias**: `equipotent_refl`, `equipotent_symm`, `equipotent_trans`
**Importancia**: high

#### Identidad es Inyectiva

**Ubicación**: `SetOps.Functions.lean`, línea 455  
**Orden**: 35º teorema principal

**Enunciado Matemático**: 𝟙 A es inyectiva.

**Firma Lean4**:

```lean
theorem id_is_injective (A : U) : isInjective (𝟙 A)
```

**Dependencias**: `isInjective`, `idFn_is_specified`
**Importancia**: low

#### Dominación es Reflexiva

**Ubicación**: `SetOps.Functions.lean`, línea 460  
**Orden**: 36º teorema principal

**Enunciado Matemático**: A ≼ₛ A.

**Firma Lean4**:

```lean
theorem dominated_refl (A : U) : A ≼ₛ A
```

**Dependencias**: `isDominatedBy`, `idFn_is_function`, `id_is_injective`
**Importancia**: medium

#### Dominación es Transitiva

**Ubicación**: `SetOps.Functions.lean`, línea 465  
**Orden**: 37º teorema principal

**Enunciado Matemático**: A ≼ₛ B → B ≼ₛ C → A ≼ₛ C.

**Firma Lean4**:

```lean
theorem dominated_trans (A B C : U) (hab : A ≼ₛ B) (hbc : B ≼ₛ C) : A ≼ₛ C
```

**Dependencias**: `isDominatedBy`, `comp_is_function`, `comp_injective`
**Importancia**: medium

#### Dominación es Preorden

**Ubicación**: `SetOps.Functions.lean`, línea 475  
**Orden**: 38º teorema principal

**Enunciado Matemático**: ≼ₛ es reflexiva y transitiva.

**Firma Lean4**:

```lean
theorem dominated_is_preorder :
    (∀ (A : U), isDominatedBy A A) ∧
    (∀ (A B C : U), isDominatedBy A B → isDominatedBy B C → isDominatedBy A C)
```

**Dependencias**: `dominated_refl`, `dominated_trans`
**Importancia**: medium

#### Equipotencia Implica Dominación Bilateral

**Ubicación**: `SetOps.Functions.lean`, línea 480  
**Orden**: 39º teorema principal

**Enunciado Matemático**: A ≃ₛ B → (A ≼ₛ B ∧ B ≼ₛ A).

**Firma Lean4**:

```lean
theorem equipotent_implies_dominated_both (A B : U) (h : A ≃ₛ B) :
    (A ≼ₛ B) ∧ (B ≼ₛ A)
```

**Dependencias**: `isEquipotent`, `isDominatedBy`, `inverse_is_bijection`
**Importancia**: medium

#### Dominación Estricta es Irreflexiva

**Ubicación**: `SetOps.Functions.lean`, línea 490  
**Orden**: 40º teorema principal

**Enunciado Matemático**: ¬(A ≺ₛ A).

**Firma Lean4**:

```lean
theorem strict_dominated_irrefl (A : U) : ¬(A ≺ₛ A)
```

**Dependencias**: `isStrictlyDominatedBy`, `dominated_refl`
**Importancia**: low

#### Dominación Estricta es Transitiva

**Ubicación**: `SetOps.Functions.lean`, línea 495  
**Orden**: 41º teorema principal

**Enunciado Matemático**: A ≺ₛ B → B ≺ₛ C → A ≺ₛ C.

**Firma Lean4**:

```lean
theorem strict_dominated_trans (A B C : U)
    (hab : A ≺ₛ B) (hbc : B ≺ₛ C) : A ≺ₛ C
```

**Dependencias**: `isStrictlyDominatedBy`, `dominated_trans`
**Importancia**: medium

#### Composición de Inyectivas es Inyectiva

**Ubicación**: `SetOps.Functions.lean`, línea 505  
**Orden**: 42º teorema principal

**Enunciado Matemático**: Si f y g son inyectivas, entonces g ∘ₛ f es inyectiva.

**Firma Lean4**:

```lean
theorem comp_injective (f g : U) (hinj_f : isInjective f) (hinj_g : isInjective g) :
    isInjective (g ∘ₛ f)
```

**Dependencias**: `isInjective`, `comp_is_specified`
**Importancia**: high

#### Composición de Suryectivas es Suryectiva

**Ubicación**: `SetOps.Functions.lean`, línea 515  
**Orden**: 43º teorema principal

**Enunciado Matemático**: Si f y g son suryectivas, entonces g ∘ₛ f es suryectiva.

**Firma Lean4**:

```lean
theorem comp_surjective (f g A B C : U)
    (_ : IsFunction f A B) (hg : IsFunction g B C)
    (hsurj_f : isSurjectiveOnto f B) (hsurj_g : isSurjectiveOnto g C) :
    isSurjectiveOnto (g ∘ₛ f) C
```

**Dependencias**: `isSurjectiveOnto`, `comp_is_specified`
**Importancia**: medium

#### Composición de Biyecciones es Biyección

**Ubicación**: `SetOps.Functions.lean`, línea 530  
**Orden**: 44º teorema principal

**Enunciado Matemático**: Si f y g son biyecciones, entonces g ∘ₛ f es biyección.

**Firma Lean4**:

```lean
theorem comp_bijection (f g A B C : U)
    (hf : IsFunction f A B) (hg : IsFunction g B C)
    (hbij_f : isBijection f A B) (hbij_g : isBijection g B C) :
    isBijection (g ∘ₛ f) A C
```

**Dependencias**: `isBijection`, `comp_is_function`, `comp_injective`, `comp_surjective`
**Importancia**: high

#### Identidad es Biyección

**Ubicación**: `SetOps.Functions.lean`, línea 540  
**Orden**: 45º teorema principal

**Enunciado Matemático**: 𝟙 A es biyección de A a A.

**Firma Lean4**:

```lean
theorem id_is_bijection (A : U) : isBijection (𝟙 A) A A
```

**Dependencias**: `isBijection`, `idFn_is_function`, `id_is_injective`
**Importancia**: medium

#### Especificación de Imagen Directa

**Ubicación**: `SetOps.Functions.lean`, línea 590  
**Orden**: 46º teorema principal

**Enunciado Matemático**: y ∈ f⦃X⦄ ↔ ∃x, x ∈ X ∧ ⟨x,y⟩ ∈ f.

**Firma Lean4**:

```lean
theorem image_is_specified (f X y : U) :
    y ∈ f⦃X⦄ ↔ ∃ x, x ∈ X ∧ ⟨x, y⟩ ∈ f
```

**Dependencias**: `image`, `mem_sep_iff`
**Importancia**: high

#### Especificación de Imagen Inversa

**Ubicación**: `SetOps.Functions.lean`, línea 600  
**Orden**: 47º teorema principal

**Enunciado Matemático**: x ∈ preimage f Y ↔ ∃y, y ∈ Y ∧ ⟨x,y⟩ ∈ f.

**Firma Lean4**:

```lean
theorem preimage_is_specified (f Y x : U) :
    x ∈ preimage f Y ↔ ∃ y, y ∈ Y ∧ ⟨x, y⟩ ∈ f
```

**Dependencias**: `preimage`, `mem_sep_iff`
**Importancia**: high

#### Imagen del Conjunto Vacío

**Ubicación**: `SetOps.Functions.lean`, línea 610  
**Orden**: 48º teorema principal

**Enunciado Matemático**: f⦃∅⦄ = ∅.

**Firma Lean4**:

```lean
theorem image_empty (f : U) : f⦃∅⦄ = ∅
```

**Dependencias**: `image`, `ExtSet`, `EmptySet_is_empty`
**Importancia**: low

#### Imagen Preserva Subconjuntos

**Ubicación**: `SetOps.Functions.lean`, línea 620  
**Orden**: 49º teorema principal

**Enunciado Matemático**: Si X ⊆ Y, entonces f⦃X⦄ ⊆ f⦃Y⦄.

**Firma Lean4**:

```lean
theorem image_mono (f X Y : U) (h : X ⊆ Y) : f⦃X⦄ ⊆ f⦃Y⦄
```

**Dependencias**: `image`, `subset`, `image_is_specified`
**Importancia**: medium

#### Imagen de Unión

**Ubicación**: `SetOps.Functions.lean`, línea 625  
**Orden**: 50º teorema principal

**Enunciado Matemático**: f⦃X ∪ Y⦄ = f⦃X⦄ ∪ f⦃Y⦄.

**Firma Lean4**:

```lean
theorem image_union (f X Y : U) : f⦃union X Y⦄ = union (f⦃X⦄) (f⦃Y⦄)
```

**Dependencias**: `image`, `union`, `ExtSet`, `mem_union_iff`
**Importancia**: medium

#### Imagen Inversa de Unión

**Ubicación**: `SetOps.Functions.lean`, línea 645  
**Orden**: 51º teorema principal

**Enunciado Matemático**: preimage f (X ∪ Y) = preimage f X ∪ preimage f Y.

**Firma Lean4**:

```lean
theorem preimage_union (f X Y : U) :
    preimage f (union X Y) = union (preimage f X) (preimage f Y)
```

**Dependencias**: `preimage`, `union`, `ExtSet`, `preimage_is_specified`
**Importancia**: medium

#### Imagen Inversa de Intersección (Inclusión)

**Ubicación**: `SetOps.Functions.lean`, línea 665  
**Orden**: 52º teorema principal

**Enunciado Matemático**: preimage f (X ∩ Y) ⊆ preimage f X ∩ preimage f Y.

**Firma Lean4**:

```lean
theorem preimage_inter_subset (f X Y : U) :
    preimage f (inter X Y) ⊆ inter (preimage f X) (preimage f Y)
```

**Dependencias**: `preimage`, `inter`, `subset`, `preimage_is_specified`
**Importancia**: low

#### Imagen Inversa de Intersección (Igualdad para Univaluadas)

**Ubicación**: `SetOps.Functions.lean`, línea 675  
**Orden**: 53º teorema principal

**Enunciado Matemático**: Para f univaluada, preimage f (X ∩ Y) = preimage f X ∩ preimage f Y.

**Firma Lean4**:

```lean
theorem preimage_inter_eq (f X Y : U) (hf : IsSingleValued f) :
    preimage f (inter X Y) = inter (preimage f X) (preimage f Y)
```

**Dependencias**: `preimage`, `inter`, `IsSingleValued`, `preimage_inter_subset`
**Importancia**: medium

#### Teorema de Cantor-Schröder-Bernstein

**Ubicación**: `SetOps.Functions.lean`, línea 580  
**Orden**: 54º teorema principal (TEOREMA FUNDAMENTAL)

**Enunciado Matemático**: Si A ≼ B y B ≼ A, entonces A ≃ B.

**Firma Lean4**:

```lean
theorem cantor_schroeder_bernstein (A B : U)
    (hab : isDominatedBy A B) (hba : isDominatedBy B A) :
    isEquipotent A B
```

**Dependencias**: `isDominatedBy`, `isEquipotent`, `CSB_bijection`
**Importancia**: high

### 4.7 BoolAlg.Atomic.lean

#### Caracterización Alternativa de Átomo (isAtom_alt)

**Ubicación**: `BoolAlg.Atomic.lean`, línea 62
**Orden**: 1º teorema

**Enunciado Matemático**: X es átomo en 𝒫(A) ↔ X ∈ 𝒫(A) ∧ X ≠ ∅ ∧ ∀ Y ⊆ X, Y = ∅ ∨ Y = X.

**Firma Lean4**:

```lean
theorem isAtom_alt (A X : U) :
    isAtom A X ↔ X ∈ 𝒫 A ∧ X ≠ ∅ ∧ ∀ Y, Y ⊆ X → Y = ∅ ∨ Y = X
```

**Dependencias**: `isAtom`, `PowerSet`
**Importancia**: medium

#### Singleton como Subconjunto (singleton_subset)

**Ubicación**: `BoolAlg.Atomic.lean`, línea 86
**Orden**: 2º teorema

**Enunciado Matemático**: x ∈ A → {x} ⊆ A.

**Firma Lean4**:

```lean
theorem singleton_subset (A x : U) (hx : x ∈ A) : {x} ⊆ A
```

**Dependencias**: `Singleton_is_specified`
**Importancia**: high

#### Singleton en Conjunto Potencia (singleton_mem_powerset)

**Ubicación**: `BoolAlg.Atomic.lean`, línea 93
**Orden**: 3º teorema

**Enunciado Matemático**: x ∈ A → {x} ∈ 𝒫(A).

**Firma Lean4**:

```lean
theorem singleton_mem_powerset (A x : U) (hx : x ∈ A) : {x} ∈ 𝒫 A
```

**Dependencias**: `singleton_subset`, `mem_powerset_iff`
**Importancia**: medium

#### Singleton No Vacío (singleton_nonempty)

**Ubicación**: `BoolAlg.Atomic.lean`, línea 98
**Orden**: 4º teorema

**Enunciado Matemático**: {x} ≠ ∅.

**Firma Lean4**:

```lean
theorem singleton_nonempty (x : U) : {x} ≠ ∅
```

**Dependencias**: `Singleton_is_specified`, `EmptySet_is_empty`
**Importancia**: medium

#### Subconjuntos de un Singleton (subset_singleton)

**Ubicación**: `BoolAlg.Atomic.lean`, línea 105
**Orden**: 5º teorema

**Enunciado Matemático**: Y ⊆ {x} → Y = ∅ ∨ Y = {x}.

**Firma Lean4**:

```lean
theorem subset_singleton (x Y : U) (hY : Y ⊆ {x}) : Y = ∅ ∨ Y = {x}
```

**Dependencias**: `Singleton_is_specified`, `nonempty_iff_exists_mem`, `ExtSet`
**Importancia**: medium

#### Los Singletons son Átomos (singleton_is_atom)

**Ubicación**: `BoolAlg.Atomic.lean`, línea 127
**Orden**: 6º teorema

**Enunciado Matemático**: x ∈ A → {x} es átomo en 𝒫(A).

**Firma Lean4**:

```lean
theorem singleton_is_atom (A x : U) (hx : x ∈ A) : isAtom A {x}
```

**Dependencias**: `isAtom_alt`, `singleton_mem_powerset`, `singleton_nonempty`, `subset_singleton`
**Importancia**: high

#### Elemento Único de un Átomo (atom_has_unique_element)

**Ubicación**: `BoolAlg.Atomic.lean`, línea 136
**Orden**: 7º teorema

**Enunciado Matemático**: Si X es átomo en 𝒫(A), entonces ∃! z, z ∈ X.

**Firma Lean4**:

```lean
theorem atom_has_unique_element (A X : U) (hAtom : isAtom A X) :
    ∃ z, z ∈ X ∧ ∀ y, y ∈ X → y = z
```

**Dependencias**: `isAtom_alt`, `nonempty_iff_exists_mem`, `singleton_nonempty`
**Importancia**: medium

#### Los Átomos son Singletons (atom_is_singleton)

**Ubicación**: `BoolAlg.Atomic.lean`, línea 166
**Orden**: 8º teorema

**Enunciado Matemático**: Todo átomo en 𝒫(A) es de la forma {x} con x ∈ A.

**Firma Lean4**:

```lean
theorem atom_is_singleton (A X : U) (hAtom : isAtom A X) :
    ∃ x, x ∈ A ∧ X = {x}
```

**Dependencias**: `isAtom_alt`, `atom_has_unique_element`, `mem_powerset_iff`, `ExtSet`
**Importancia**: high

#### Caracterización de Átomos (atom_iff_singleton)

**Ubicación**: `BoolAlg.Atomic.lean`, línea 190
**Orden**: 9º teorema

**Enunciado Matemático**: X es átomo en 𝒫(A) ↔ ∃ x ∈ A, X = {x}.

**Firma Lean4**:

```lean
theorem atom_iff_singleton (A X : U) :
    isAtom A X ↔ ∃ x, x ∈ A ∧ X = {x}
```

**Dependencias**: `atom_is_singleton`, `singleton_is_atom`
**Importancia**: high

#### Especificación de Atoms (Atoms_is_specified)

**Ubicación**: `BoolAlg.Atomic.lean`, línea 205
**Orden**: 10º teorema

**Enunciado Matemático**: X ∈ Atoms(A) ↔ X ∈ 𝒫(A) ∧ X es átomo en 𝒫(A).

**Firma Lean4**:

```lean
theorem Atoms_is_specified (A X : U) :
    X ∈ Atoms A ↔ X ∈ 𝒫 A ∧ isAtom A X
```

**Dependencias**: `Atoms`, `mem_sep_iff`
**Importancia**: medium

#### Atoms son los Singletons (Atoms_eq_singletons)

**Ubicación**: `BoolAlg.Atomic.lean`, línea 211
**Orden**: 11º teorema

**Enunciado Matemático**: X ∈ Atoms(A) ↔ ∃ x ∈ A, X = {x}.

**Firma Lean4**:

```lean
theorem Atoms_eq_singletons (A X : U) :
    X ∈ Atoms A ↔ ∃ x, x ∈ A ∧ X = {x}
```

**Dependencias**: `Atoms_is_specified`, `atom_iff_singleton`, `singleton_mem_powerset`
**Importancia**: high

#### 𝒫(A) es Atómica (powerset_is_atomic)

**Ubicación**: `BoolAlg.Atomic.lean`, línea 231
**Orden**: 12º teorema

**Enunciado Matemático**: Para todo conjunto A, 𝒫(A) es una álgebra de Boole atómica.

**Firma Lean4**:

```lean
theorem powerset_is_atomic (A : U) : isAtomic A
```

**Dependencias**: `isAtomic`, `nonempty_iff_exists_mem`, `mem_powerset_iff`, `singleton_is_atom`, `Singleton_is_specified`
**Importancia**: high

#### Elemento como Unión de Átomos (element_is_union_of_atoms)

**Ubicación**: `BoolAlg.Atomic.lean`, línea 248
**Orden**: 13º teorema

**Enunciado Matemático**: Si X ∈ 𝒫(A), entonces X = ⋃ { Y ∈ Atoms(A) | Y ⊆ X }.

**Firma Lean4**:

```lean
theorem element_is_union_of_atoms (A X : U) (hX : X ∈ 𝒫 A) :
    X = ⋃ (sep (Atoms A) (fun Y => Y ⊆ X))
```

**Dependencias**: `Atoms`, `Atoms_is_specified`, `singleton_is_atom`, `singleton_mem_powerset`, `mem_sUnion_iff`, `mem_sep_iff`, `ExtSet`
**Importancia**: high

#### Singleton Debajo iff Membresía (singleton_below_iff)

**Ubicación**: `BoolAlg.Atomic.lean`, línea 282
**Orden**: 14º teorema

**Enunciado Matemático**: x ∈ A → (atomBelow A X {x} ↔ x ∈ X).

**Firma Lean4**:

```lean
theorem singleton_below_iff (A X x : U) (hx : x ∈ A) :
    atomBelow A X {x} ↔ x ∈ X
```

**Dependencias**: `atomBelow`, `singleton_is_atom`, `Singleton_is_specified`
**Importancia**: medium

### 4.8 Cardinality.lean

#### Caracterización del Conjunto Diagonal (mem_diagSet_iff)

**Ubicación**: `Cardinal.Basic.lean`, línea 42  
**Orden**: 1º teorema auxiliar

**Enunciado Matemático**: x ∈ diagSet f A ↔ x ∈ A ∧ x ∉ f⦅x⦆.

**Firma Lean4**:

```lean
theorem mem_diagSet_iff (f A x : U) :
    x ∈ diagSet f A ↔ x ∈ A ∧ x ∉ f⦅x⦆
```

**Dependencias**: `diagSet`, `mem_sep_iff`
**Importancia**: low

#### El Conjunto Diagonal es Subconjunto (diagSet_subset)

**Ubicación**: `Cardinal.Basic.lean`, línea 47  
**Orden**: 2º teorema auxiliar

**Enunciado Matemático**: diagSet f A ⊆ A.

**Firma Lean4**:

```lean
theorem diagSet_subset (f A : U) : diagSet f A ⊆ A
```

**Dependencias**: `diagSet`, `mem_diagSet_iff`
**Importancia**: low

#### El Conjunto Diagonal está en el Conjunto Potencia (diagSet_in_powerset)

**Ubicación**: `Cardinal.Basic.lean`, línea 52  
**Orden**: 3º teorema auxiliar

**Enunciado Matemático**: diagSet f A ∈ 𝒫 A.

**Firma Lean4**:

```lean
theorem diagSet_in_powerset (f A : U) : diagSet f A ∈ 𝒫 A
```

**Dependencias**: `diagSet`, `mem_powerset_iff`, `diagSet_subset`
**Importancia**: low

#### El Conjunto Diagonal no está en el Rango (diagSet_not_in_range)

**Ubicación**: `Cardinal.Basic.lean`, línea 57  
**Orden**: 4º teorema auxiliar (lema clave)

**Enunciado Matemático**: No existe d ∈ A tal que f⦅d⦆ = diagSet f A.

**Firma Lean4**:

```lean
theorem diagSet_not_in_range (f A : U) :
    ¬∃ d, d ∈ A ∧ f⦅d⦆ = diagSet f A
```

**Dependencias**: `diagSet`, `mem_diagSet_iff`, `Classical.byContradiction`
**Importancia**: medium

#### Teorema de Cantor (cantor_no_surjection)

**Ubicación**: `Cardinal.Basic.lean`, línea 78  
**Orden**: 1º teorema principal (TEOREMA FUNDAMENTAL)

**Enunciado Matemático**: No existe suryección de A a 𝒫(A).

**Firma Lean4**:

```lean
theorem cantor_no_surjection (f A : U) (hf : IsFunction f A (𝒫 A)) :
  ¬isSurjectiveOnto f (𝒫 A)
```

**Dependencias**: `diagSet`, `diagSet_not_in_range`, `IsFunction`, `isSurjectiveOnto`
**Importancia**: high

#### No hay Biyección de A a 𝒫(A) (cantor_no_bijection)

**Ubicación**: `Cardinal.Basic.lean`, línea 90  
**Orden**: 2º teorema principal

**Enunciado Matemático**: No existe biyección de A a 𝒫(A).

**Firma Lean4**:

```lean
theorem cantor_no_bijection (f A : U) (hf : IsFunction f A (𝒫 A)) :
    ¬isBijection f A (𝒫 A)
```

**Dependencias**: `cantor_no_surjection`, `isBijection`
**Importancia**: high

#### Caracterización de singletonMap (singletonMap_is_specified)

**Ubicación**: `Cardinal.Basic.lean`, línea 100  
**Orden**: 5º teorema auxiliar

**Enunciado Matemático**: ⟨x, y⟩ ∈ singletonMap A ↔ x ∈ A ∧ y = {x}.

**Firma Lean4**:

```lean
theorem singletonMap_is_specified (A x y : U) :
    ⟨x, y⟩ ∈ singletonMap A ↔ x ∈ A ∧ y = {x}
```

**Dependencias**: `singletonMap`, `mem_sep_iff`, `Eq_of_OrderedPairs_given_projections`
**Importancia**: medium

#### singletonMap es Función (singletonMap_is_function)

**Ubicación**: `Cardinal.Basic.lean`, línea 112  
**Orden**: 6º teorema auxiliar

**Enunciado Matemático**: singletonMap A es función de A a 𝒫(A).

**Firma Lean4**:

```lean
theorem singletonMap_is_function (A : U) : IsFunction (singletonMap A) A (𝒫 A)
```

**Dependencias**: `singletonMap`, `singletonMap_is_specified`, `IsFunction`
**Importancia**: medium

#### singletonMap es Inyectiva (singletonMap_is_injective)

**Ubicación**: `Cardinal.Basic.lean`, línea 125  
**Orden**: 7º teorema auxiliar

**Enunciado Matemático**: singletonMap A es inyectiva.

**Firma Lean4**:

```lean
theorem singletonMap_is_injective (A : U) : isInjective (singletonMap A)
```

**Dependencias**: `singletonMap`, `singletonMap_is_specified`, `isInjective`, `Singleton_is_specified`
**Importancia**: medium

#### A es Dominado por 𝒫(A) (A_dominated_by_powerset)

**Ubicación**: `Cardinal.Basic.lean`, línea 136  
**Orden**: 3º teorema principal

**Enunciado Matemático**: A ≼ₛ 𝒫(A).

**Firma Lean4**:

```lean
theorem A_dominated_by_powerset (A : U) : isDominatedBy A (𝒫 A)
```

**Dependencias**: `singletonMap`, `singletonMap_is_function`, `singletonMap_is_injective`, `isDominatedBy`
**Importancia**: high

#### 𝒫(A) no Domina a A (powerset_not_dominated_by_A)

**Ubicación**: `Cardinal.Basic.lean`, línea 140  
**Orden**: 4º teorema principal

**Enunciado Matemático**: ¬(𝒫(A) ≼ₛ A).

**Firma Lean4**:

```lean
theorem powerset_not_dominated_by_A (A : U) : ¬isDominatedBy (𝒫 A) A
```

**Dependencias**: `isDominatedBy`, `sep`, `Classical.byContradiction`
**Importancia**: high

#### Dominación Estricta de Cantor (cantor_strict_dominance)

**Ubicación**: `Cardinal.Basic.lean`, línea 180  
**Orden**: 5º teorema principal (FORMA CARDINAL)

**Enunciado Matemático**: A ≺ₛ 𝒫(A).

**Firma Lean4**:

```lean
theorem cantor_strict_dominance (A : U) : isStrictlyDominatedBy A (𝒫 A)
```

**Dependencias**: `A_dominated_by_powerset`, `powerset_not_dominated_by_A`, `isStrictlyDominatedBy`
**Importancia**: high

#### A y 𝒫(A) no son Equipotentes (cantor_not_equipotent)

**Ubicación**: `Cardinal.Basic.lean`, línea 183  
**Orden**: 6º teorema principal

**Enunciado Matemático**: ¬(A ≃ₛ 𝒫(A)).

**Firma Lean4**:

```lean
theorem cantor_not_equipotent (A : U) : ¬isEquipotent A (𝒫 A)
```

**Dependencias**: `isEquipotent`, `cantor_no_bijection`
**Importancia**: high

#### Caracterización de SetDiff (SetDiff_is_specified)

**Ubicación**: `Cardinal.Basic.lean`, línea 191  
**Orden**: 8º teorema auxiliar

**Enunciado Matemático**: x ∈ (A ∖ B) ↔ x ∈ A ∧ x ∉ B.

**Firma Lean4**:

```lean
theorem SetDiff_is_specified (A B x : U) :
    x ∈ (A ∖ B) ↔ x ∈ A ∧ x ∉ B
```

**Dependencias**: `SetDiff`, `mem_sep_iff`
**Importancia**: medium

#### SetDiff es Subconjunto (SetDiff_subset)

**Ubicación**: `Cardinal.Basic.lean`, línea 196  
**Orden**: 9º teorema auxiliar

**Enunciado Matemático**: (A ∖ B) ⊆ A.

**Firma Lean4**:

```lean
theorem SetDiff_subset (A B : U) : (A ∖ B) ⊆ A
```

**Dependencias**: `SetDiff`, `SetDiff_is_specified`
**Importancia**: low

#### CSB_core es Subconjunto (CSB_core_subset)

**Ubicación**: `Cardinal.Basic.lean`, línea 216  
**Orden**: 10º teorema auxiliar

**Enunciado Matemático**: CSB_core f g A B ⊆ A.

**Firma Lean4**:

```lean
theorem CSB_core_subset (f g A B : U) : CSB_core f g A B ⊆ A
```

**Dependencias**: `CSB_core`, `mem_sep_iff`
**Importancia**: low

#### CSB_core Contiene la Base (CSB_core_contains_base)

**Ubicación**: `Cardinal.Basic.lean`, línea 223  
**Orden**: 11º teorema auxiliar

**Enunciado Matemático**: (A ∖ image g B) ⊆ CSB_core f g A B.

**Firma Lean4**:

```lean
theorem CSB_core_contains_base (f g A B : U) :
    (A ∖ image g B) ⊆ CSB_core f g A B
```

**Dependencias**: `CSB_core`, `SetDiff`, `image`, `mem_sep_iff`
**Importancia**: low

#### CSB_core es Cerrado (CSB_core_closed)

**Ubicación**: `Cardinal.Basic.lean`, línea 234  
**Orden**: 12º teorema auxiliar

**Enunciado Matemático**: Si x ∈ CSB_core f g A B, entonces g⦅f⦅x⦆⦆ ∈ CSB_core f g A B.

**Firma Lean4**:

```lean
theorem CSB_core_closed (f g A B : U)
    (hf : IsFunction f A B) (hg : IsFunction g B A) :
    ∀ x, x ∈ CSB_core f g A B → g⦅f⦅x⦆⦆ ∈ CSB_core f g A B
```

**Dependencias**: `CSB_core`, `IsFunction`, `apply`, `mem_sep_iff`
**Importancia**: medium

#### Complemento de CSB_core está en Imagen (CSB_complement_in_image)

**Ubicación**: `Cardinal.Basic.lean`, línea 256  
**Orden**: 13º teorema auxiliar

**Enunciado Matemático**: Si x ∈ A y x ∉ CSB_core f g A B, entonces x ∈ image g B.

**Firma Lean4**:

```lean
theorem CSB_complement_in_image (f g A B x : U)
    (_ : IsFunction f A B) (_ : IsFunction g B A)
    (hx_A : x ∈ A) (hx_not : x ∉ CSB_core f g A B) :
    x ∈ image g B
```

**Dependencias**: `CSB_core`, `image`, `CSB_core_contains_base`, `SetDiff`, `Classical.byContradiction`
**Importancia**: medium

#### Caracterización de CSB_bijection (CSB_bijection_is_specified)

**Ubicación**: `Cardinal.Basic.lean`, línea 285  
**Orden**: 14º teorema auxiliar

**Enunciado Matemático**: ⟨x, y⟩ ∈ CSB_bijection f g A B ↔ x ∈ A ∧ y ∈ B ∧ ((x ∈ CSB_core f g A B ∧ y = f⦅x⦆) ∨ (x ∉ CSB_core f g A B ∧ ⟨y, x⟩ ∈ g)).

**Firma Lean4**:

```lean
theorem CSB_bijection_is_specified (f g A B x y : U) :
    ⟨x, y⟩ ∈ CSB_bijection f g A B ↔
      x ∈ A ∧ y ∈ B ∧
      ((x ∈ CSB_core f g A B ∧ y = f⦅x⦆) ∨
       (x ∉ CSB_core f g A B ∧ ⟨y, x⟩ ∈ g))
```

**Dependencias**: `CSB_bijection`, `CSB_core`, `mem_sep_iff`, `OrderedPair_mem_CartesianProduct`, `Eq_of_OrderedPairs_given_projections`
**Importancia**: medium

#### CSB_bijection es Función (CSB_bijection_is_function)

**Ubicación**: `Cardinal.Basic.lean`, línea 302  
**Orden**: 15º teorema auxiliar

**Enunciado Matemático**: CSB_bijection f g A B es función de A a B.

**Firma Lean4**:

```lean
theorem CSB_bijection_is_function (f g A B : U)
    (hf : IsFunction f A B) (hg : IsFunction g B A)
    (_ : isInjective f) (hg_inj : isInjective g) :
    IsFunction (CSB_bijection f g A B) A B
```

**Dependencias**: `CSB_bijection`, `CSB_bijection_is_specified`, `CSB_core_closed`, `CSB_complement_in_image`, `IsFunction`, `ExistsUnique`
**Importancia**: medium

#### CSB_bijection es Inyectiva (CSB_bijection_is_injective)

**Ubicación**: `Cardinal.Basic.lean`, línea 351  
**Orden**: 16º teorema auxiliar

**Enunciado Matemático**: CSB_bijection f g A B es inyectiva.

**Firma Lean4**:

```lean
theorem CSB_bijection_is_injective (f g A B : U)
    (hf : IsFunction f A B) (hg : IsFunction g B A) (hf_inj : isInjective f) :
    isInjective (CSB_bijection f g A B)
```

**Dependencias**: `CSB_bijection`, `CSB_bijection_is_specified`, `CSB_core`, `CSB_core_closed`, `isInjective`, `apply_eq`
**Importancia**: medium

#### CSB_bijection es Suryectiva (CSB_bijection_is_surjective)

**Ubicación**: `Cardinal.Basic.lean`, línea 393  
**Orden**: 17º teorema auxiliar

**Enunciado Matemático**: CSB_bijection f g A B es suryectiva en B.

**Firma Lean4**:

```lean
theorem CSB_bijection_is_surjective (f g A B : U)
    (hf : IsFunction f A B) (hg : IsFunction g B A)
    (_ : isInjective f) (hg_inj : isInjective g) :
    isSurjectiveOnto (CSB_bijection f g A B) B
```

**Dependencias**: `CSB_bijection`, `CSB_bijection_is_specified`, `CSB_core`, `image`, `isSurjectiveOnto`, `Classical.byContradiction`
**Importancia**: medium

#### CSB_bijection es Biyección (CSB_bijection_is_bijection)

**Ubicación**: `Cardinal.Basic.lean`, línea 476  
**Orden**: 18º teorema auxiliar

**Enunciado Matemático**: CSB_bijection f g A B es biyección de A a B.

**Firma Lean4**:

```lean
theorem CSB_bijection_is_bijection (f g A B : U)
    (hf : IsFunction f A B) (hg : IsFunction g B A)
    (hf_inj : isInjective f) (hg_inj : isInjective g) :
    isBijection (CSB_bijection f g A B) A B
```

**Dependencias**: `CSB_bijection_is_function`, `CSB_bijection_is_injective`, `CSB_bijection_is_surjective`, `isBijection`
**Importancia**: high

#### Teorema de Cantor-Schröder-Bernstein (cantor_schroeder_bernstein)

**Ubicación**: `Cardinal.Basic.lean`, línea 483  
**Orden**: 7º teorema principal (TEOREMA FUNDAMENTAL)

**Enunciado Matemático**: Si A ≼ₛ B y B ≼ₛ A, entonces A ≃ₛ B.

**Firma Lean4**:

```lean
theorem cantor_schroeder_bernstein (A B : U)
    (hab : isDominatedBy A B) (hba : isDominatedBy B A) :
    isEquipotent A B
```

**Dependencias**: `CSB_bijection`, `CSB_bijection_is_bijection`, `isDominatedBy`, `isEquipotent`
**Importancia**: high

#### Antisimetría de Dominación (dominated_antisymm)

**Ubicación**: `Cardinal.Basic.lean`, línea 490  
**Orden**: 8º teorema principal

**Enunciado Matemático**: ≼ₛ es antisimétrica módulo equipotencia.

**Firma Lean4**:

```lean
theorem dominated_antisymm (A B : U) :
    isDominatedBy A B → isDominatedBy B A → isEquipotent A B
```

**Dependencias**: `cantor_schroeder_bernstein`
**Importancia**: high

### 4.9 Nat.Basic.lean

#### El Conjunto Vacío es Natural

**Ubicación**: `Nat.Basic.lean`, línea 145  
**Orden**: 1º teorema principal (TEOREMA BASE)

**Enunciado Matemático**: ∅ es un número natural.

**Firma Lean4**:

```lean
theorem isNat_zero : IsNat (∅ : U)
```

**Dependencias**: `IsNat`, `EmptySet`
**Importancia**: high

#### Irreflexividad de Naturales

**Ubicación**: `Nat.Basic.lean`, línea 280  
**Orden**: 2º teorema principal

**Enunciado Matemático**: Ningún número natural es miembro de sí mismo.

**Firma Lean4**:

```lean
theorem not_mem_self (n : U) :
  IsNat n → n ∉ n
```

**Dependencias**: `IsNat`, `isTotalStrictOrderMembershipGuided`

#### Ausencia de Ciclos de Dos Elementos

**Ubicación**: `Nat.Basic.lean`, línea 295  
**Orden**: 3º teorema principal

**Enunciado Matemático**: No existen ciclos de membresía de dos elementos entre naturales.

**Firma Lean4**:

```lean
theorem not_mem_of_mem (x y : U) :
  IsNat x → IsNat y → ¬(x ∈ y ∧ y ∈ x)
```

**Dependencias**: `IsNat`, `not_mem_self`
**Importancia**: medium

#### Ausencia de Ciclos de Tres Elementos

**Ubicación**: `Nat.Basic.lean`, línea 320  
**Orden**: 4º teorema principal

**Enunciado Matemático**: No existen ciclos de membresía de tres elementos entre naturales.

**Firma Lean4**:

```lean
theorem nat_no_three_cycle (x y z : U) :
  IsNat x → IsNat y → IsNat z → ¬(x ∈ y ∧ y ∈ z ∧ z ∈ x)
```

**Dependencias**: `IsNat`, `not_mem_of_mem`
**Importancia**: low

#### Elementos de Naturales son Naturales

**Ubicación**: `Nat.Basic.lean`, línea 520  
**Orden**: 5º teorema principal (TEOREMA FUNDAMENTAL)

**Enunciado Matemático**: Todo elemento de un número natural es un número natural.

**Firma Lean4**:

```lean
theorem nat_element_is_nat (n m : U) :
  IsNat n → m ∈ n → IsNat m
```

**Dependencias**: `IsNat`, `nat_element_is_transitive`, `nat_element_has_strict_total_order`, `nat_element_has_well_order`
**Importancia**: high

#### El Sucesor de un Natural es Natural

**Ubicación**: `Nat.Basic.lean`, línea 680  
**Orden**: 6º teorema principal (CLAUSURA BAJO SUCESORES)

**Enunciado Matemático**: Si n es natural, entonces σ(n) es natural.

**Firma Lean4**:

```lean
theorem isNat_succ (n : U) (hn : IsNat n) : IsNat (σ n)
```

**Dependencias**: `IsNat`, `succ`, `succ_of_nat_is_transitive`, `succ_of_nat_has_strict_total_order`
**Importancia**: high

#### Tricotomía entre Naturales

**Ubicación**: `Nat.Basic.lean`, línea 1080  
**Orden**: 7º teorema principal (TRICOTOMÍA COMPLETA)

**Enunciado Matemático**: Dados dos naturales n y m, se cumple exactamente una: n ∈ m, n = m, o m ∈ n.

**Firma Lean4**:

```lean
theorem trichotomy (n m : U) (hn : IsNat n) (hm : IsNat m) :
  n ∈ m ∨ n = m ∨ m ∈ n
```

**Dependencias**: `IsNat`, `initial_segment_of_nat_is_eq_or_mem`, `inter_nat_is_initial_segment`
**Importancia**: high

#### Segmento Inicial es Igual o Elemento

**Ubicación**: `Nat.Basic.lean`, línea 1025  
**Orden**: 8º teorema principal

**Enunciado Matemático**: Un segmento inicial de un natural n es igual a n o es un elemento de n.

**Firma Lean4**:

```lean
theorem initial_segment_of_nat_is_eq_or_mem (n S : U)
  (hn : IsNat n) (h_init : IsInitialSegment S n) :
  S = n ∨ S ∈ n
```

**Dependencias**: `IsNat`, `IsInitialSegment`, `isWellOrderMembershipGuided`
**Importancia**: medium

#### Inyectividad del Sucesor

**Ubicación**: `Nat.Basic.lean`, línea 1200  
**Orden**: 9º teorema principal

**Enunciado Matemático**: El sucesor es inyectivo: σ(n) = σ(m) → n = m.

**Firma Lean4**:

```lean
theorem succ_injective (n m : U) (hn : IsNat n) (hm : IsNat m)
  (h_eq : σ n = σ m) : n = m
```

**Dependencias**: `succ`, `IsNat`, `not_mem_of_mem`
**Importancia**: high

#### Todo Natural es Cero o Sucesor

**Ubicación**: `Nat.Basic.lean`, línea 1250  
**Orden**: 10º teorema principal

**Enunciado Matemático**: Todo número natural es 0 o sucesor de otro natural.

**Firma Lean4**:

```lean
theorem eq_zero_or_exists_succ (n : U) (hn : IsNat n) :
  n = ∅ ∨ ∃ k, n = σ k
```

**Dependencias**: `IsNat`, `EmptySet`, `succ`, `isWellOrderMembershipGuided`
**Importancia**: high

#### Naturales en Conjuntos Inductivos

**Ubicación**: `Nat.Basic.lean`, línea 1320  
**Orden**: 11º teorema principal

**Enunciado Matemático**: Todo número natural pertenece a cualquier conjunto inductivo.

**Firma Lean4**:

```lean
theorem nat_in_inductive_set (n : U) (hn : IsNat n) (I : U) (hI : IsInductive I) :
  n ∈ I
```

**Dependencias**: `IsNat`, `IsInductive`, `eq_zero_or_exists_succ`, `nat_subset_inductive_set`
**Importancia**: high

#### Caracterización de Finitud

**Ubicación**: `Nat.Basic.lean`, línea 850  
**Orden**: 12º teorema principal (TEOREMA DE FINITUD)

**Enunciado Matemático**: Todo subconjunto no vacío de un natural tiene elemento máximo.

**Firma Lean4**:

```lean
theorem nat_has_max (n T : U) (hn : IsNat n) (hT_sub : T ⊆ n) (hT_ne : T ≠ ∅) :
  ∃ max, max ∈ T ∧ ∀ x, x ∈ T → (x ∈ max ∨ x = max)
```

**Dependencias**: `IsNat`, `isWellOrderMembershipGuided`, `not_mem_self`
**Importancia**: high

### 4.10 Infinity.lean

#### Omega es Inductivo

**Ubicación**: `Infinity.lean`, línea 95  
**Orden**: 1º teorema principal (TEOREMA BASE)

**Enunciado Matemático**: ω es un conjunto inductivo.

**Firma Lean4**:

```lean
theorem Omega_is_inductive : IsInductive (ω : U)
```

**Dependencias**: `Omega`, `IsInductive`, `zero_in_Omega`, `succ_in_Omega`
**Importancia**: high

#### Minimalidad de Omega

**Ubicación**: `Infinity.lean`, línea 100  
**Orden**: 2º teorema principal (PROPIEDAD FUNDAMENTAL)

**Enunciado Matemático**: ω es subconjunto de cualquier conjunto inductivo K.

**Firma Lean4**:

```lean
theorem Omega_subset_all_inductive (K : U) (hK : IsInductive K) : ω ⊆ K
```

**Dependencias**: `Omega`, `IsInductive`, `inter`
**Importancia**: high

#### Principio de Inducción Matemática

**Ubicación**: `Infinity.lean`, línea 125  
**Orden**: 3º teorema principal (INDUCCIÓN DÉBIL)

**Enunciado Matemático**: Si S ⊆ ω, 0 ∈ S y S es cerrado bajo sucesores, entonces S = ω.

**Firma Lean4**:

```lean
theorem induction_principle (S : U) (hS_sub : S ⊆ ω)
  (h_zero : (∅ : U) ∈ S)
  (h_succ : ∀ n, n ∈ S → σ n ∈ S) :
  S = ω
```

**Dependencias**: `Omega`, `eq_of_subset_of_subset`, `Omega_subset_all_inductive`
**Importancia**: high

#### Elementos de Omega son Naturales

**Ubicación**: `Infinity.lean`, línea 140  
**Orden**: 4º teorema principal

**Enunciado Matemático**: Todo elemento de ω es un número natural.

**Firma Lean4**:

```lean
theorem mem_Omega_is_Nat (n : U) (hn : n ∈ ω) : IsNat n
```

**Dependencias**: `Omega`, `IsNat`, `induction_principle`, `isNat_zero`, `isNat_succ`
**Importancia**: high

#### Naturales Pertenecen a Omega

**Ubicación**: `Infinity.lean`, línea 165  
**Orden**: 5º teorema principal

**Enunciado Matemático**: Todo número natural pertenece a ω.

**Firma Lean4**:

```lean
theorem Nat_in_Omega (n : U) (hn : IsNat n) : n ∈ ω
```

**Dependencias**: `IsNat`, `Omega`, `nat_in_inductive_set`, `Omega_is_inductive`
**Importancia**: high

#### Caracterización Completa de Naturales

**Ubicación**: `Infinity.lean`, línea 170  
**Orden**: 6º teorema principal (TEOREMA CENTRAL)

**Enunciado Matemático**: n es natural si y solo si n ∈ ω.

**Firma Lean4**:

```lean
theorem Nat_iff_mem_Omega (n : U) : IsNat n ↔ n ∈ ω
```

**Dependencias**: `IsNat`, `Omega`, `Nat_in_Omega`, `mem_Omega_is_Nat`
**Importancia**: high

#### Principio de Inducción Fuerte

**Ubicación**: `Infinity.lean`, línea 175  
**Orden**: 7º teorema principal (INDUCCIÓN COMPLETA)

**Enunciado Matemático**: Si para todo n ∈ ω, (∀m ∈ n, m ∈ S) → n ∈ S, entonces S = ω.

**Firma Lean4**:

```lean
theorem strong_induction_principle (S : U) (hS_sub : S ⊆ ω)
  (h_strong : ∀ n, n ∈ ω → (∀ m, m ∈ n → m ∈ S) → n ∈ S) :
  S = ω
```

**Dependencias**: `Omega`, `sep`, `mem_succ_iff`, `induction_principle`
**Importancia**: high

#### Omega es Transitivo

**Ubicación**: `Infinity.lean`, línea 210  
**Orden**: 8º teorema principal

**Enunciado Matemático**: ω es un conjunto transitivo.

**Firma Lean4**:

```lean
theorem Omega_is_transitive : IsTransitive (ω : U)
```

**Dependencias**: `Omega`, `IsTransitive`, `mem_Omega_is_Nat`, `nat_element_is_nat`, `Nat_in_Omega`
**Importancia**: medium

#### Omega tiene Orden Total

**Ubicación**: `Infinity.lean`, línea 220  
**Orden**: 9º teorema principal

**Enunciado Matemático**: ω tiene un orden total estricto guiado por membresía.

**Firma Lean4**:

```lean
theorem Omega_has_total_order : isTotalStrictOrderMembershipGuided (ω : U)
```

**Dependencias**: `Omega`, `isTotalStrictOrderMembershipGuided`, `Omega_is_transitive`, `mem_Omega_is_Nat`, `trichotomy`
**Importancia**: medium

#### Omega no tiene Máximo

**Ubicación**: `Infinity.lean`, línea 235  
**Orden**: 10º teorema principal (TEOREMA DE INFINITUD)

**Enunciado Matemático**: ω no tiene elemento máximo (caracteriza la infinitud).

**Firma Lean4**:

```lean
theorem Omega_no_maximum : ∀ n : U, n ∈ ω → ∃ m : U, m ∈ ω ∧ n ∈ m
```

**Dependencias**: `Omega`, `succ`, `succ_in_Omega`, `mem_succ_self`
**Importancia**: high

#### Buena Fundación de la Membresía en ω

**Ubicación**: `Infinity.lean`, línea 247  
**Orden**: 11º teorema principal (TEOREMA DE BUENA FUNDACIÓN)

**Enunciado Matemático**: La relación de membresía restringida a ω es bien fundada: R(a, b) ⟺ a ∈ ω ∧ b ∈ ω ∧ a ∈ b es bien fundada (toda cadena descendente termina).

**Firma Lean4**:

```lean
theorem nat_mem_wf : WellFounded (fun a b : U => a ∈ ω ∧ b ∈ ω ∧ a ∈ b)
```

**Dependencias**: `Omega`, `strong_induction_principle`, `sep`, `Acc`
**Importancia**: high

**Nota de implementación**: Los elementos fuera de ω son vacuosamente accesibles (ningún `y` satisface `R y a` si `a ∉ ω`). Los elementos de ω se prueban accesibles por inducción fuerte sobre ω, construyendo `S = sep ω (Acc R)` y aplicando `strong_induction_principle`.

#### Transitividad del Orden Estricto en ω

**Ubicación**: `Infinity.lean`, línea 263  
**Orden**: 12º teorema principal

**Enunciado Matemático**: El orden estricto ≺ en ω es transitivo: si n ≺ m y m ≺ k, entonces n ≺ k.

**Firma Lean4**:

```lean
theorem natLt_trans {n m k : U} (hn : IsNat n) (hm : IsNat m) (hk : IsNat k)
    (h₁ : n ≺ m) (h₂ : m ≺ k) : n ≺ k
```

**Dependencias**: `mem_trans`, `IsNat`
**Importancia**: medium

#### Asimetría del Orden Estricto en ω

**Ubicación**: `Infinity.lean`, línea 268  
**Orden**: 13º teorema principal

**Enunciado Matemático**: El orden estricto ≺ en ω es asimétrico: si n ≺ m, entonces ¬(m ≺ n).

**Firma Lean4**:

```lean
theorem natLt_asymm {n m : U} (hn : IsNat n) (hm : IsNat m)
    (h : n ≺ m) : ¬(m ≺ n)
```

**Dependencias**: `mem_asymm`, `IsNat`
**Importancia**: medium

#### Tricotomía del Orden Estricto en ω

**Ubicación**: `Infinity.lean`, línea 273  
**Orden**: 14º teorema principal

**Enunciado Matemático**: Para cualesquiera dos naturales n, m, se cumple exactamente una de: n ≺ m, n = m, o m ≺ n.

**Firma Lean4**:

```lean
theorem natLt_trichotomy (n m : U) (hn : IsNat n) (hm : IsNat m) :
    n ≺ m ∨ n = m ∨ m ≺ n
```

**Dependencias**: `trichotomy`, `IsNat`
**Importancia**: medium

#### Reflexividad del Orden No Estricto en ω

**Ubicación**: `Infinity.lean`, línea 277  
**Orden**: 15º teorema principal

**Enunciado Matemático**: El orden no estricto ≼ es reflexivo: n ≼ n para todo n.

**Firma Lean4**:

```lean
theorem natLe_refl (n : U) : n ≼ n
```

**Dependencias**: Ninguna (definición directa)
**Importancia**: medium

#### Transitividad del Orden No Estricto en ω

**Ubicación**: `Infinity.lean`, línea 280  
**Orden**: 16º teorema principal

**Enunciado Matemático**: El orden no estricto ≼ es transitivo: si n ≼ m y m ≼ k, entonces n ≼ k.

**Firma Lean4**:

```lean
theorem natLe_trans {n m k : U} (hn : IsNat n) (hm : IsNat m) (hk : IsNat k)
    (h₁ : n ≼ m) (h₂ : m ≼ k) : n ≼ k
```

**Dependencias**: `mem_trans`, `IsNat`
**Importancia**: medium

#### Todo Subconjunto No Vacío de ω tiene Mínimo

**Ubicación**: `Infinity.lean`, línea 289  
**Orden**: 17º teorema principal (PROPIEDAD DE BUEN ORDEN)

**Enunciado Matemático**: Todo subconjunto no vacío T de ω tiene un elemento mínimo respecto al orden ≼.

**Firma Lean4**:

```lean
theorem Omega_has_min (T : U) (hT_sub : T ⊆ (ω : U)) (hT_ne : T ≠ ∅) :
    ∃ n, n ∈ T ∧ ∀ m, m ∈ T → n ≼ m
```

**Dependencias**: `Omega`, `strong_induction_principle`, `sep`, `trichotomy`, `mem_Omega_is_Nat`
**Importancia**: high

### 4.11 BoolAlg.GenDeMorgan.lean

#### Especificación de ComplementFamily (ComplementFamily_is_specified)

**Ubicación**: `BoolAlg.GenDeMorgan.lean`, línea 54
**Orden**: 1º teorema

**Enunciado Matemático**: Y ∈ ComplementFamily(A, F) ↔ Y ⊆ A ∧ ∃ X ∈ F, Y = A \ X.

**Firma Lean4**:

```lean
theorem ComplementFamily_is_specified (A F Y : U) :
    Y ∈ ComplementFamily A F ↔ Y ⊆ A ∧ ∃ X, X ∈ F ∧ Y = sdiff A X
```

**Dependencias**: `ComplementFamily`, `mem_sep_iff`, `mem_powerset_iff`
**Importancia**: medium

#### Complemento pertenece a ComplementFamily (complement_mem_ComplementFamily)

**Ubicación**: `BoolAlg.GenDeMorgan.lean`, línea 60
**Orden**: 2º teorema

**Enunciado Matemático**: X ∈ F → A \ X ∈ ComplementFamily(A, F).

**Firma Lean4**:

```lean
theorem complement_mem_ComplementFamily (A F X : U) (hX : X ∈ F) :
    sdiff A X ∈ ComplementFamily A F
```

**Dependencias**: `ComplementFamily_is_specified`, `mem_sdiff_iff`
**Importancia**: medium

#### Membresía en intersección generalizada (interSet_mem_iff)

**Ubicación**: `BoolAlg.GenDeMorgan.lean`, línea 72
**Orden**: 3º teorema

**Enunciado Matemático**: F ≠ ∅ → (z ∈ ⋂ F ↔ ∀ X ∈ F, z ∈ X).

**Firma Lean4**:

```lean
theorem interSet_mem_iff (F z : U) (hF : F ≠ ∅) :
    z ∈ (⋂ F) ↔ ∀ X, X ∈ F → z ∈ X
```

**Dependencias**: `interSet`, `mem_sep_iff`, `nonempty_iff_exists_mem`
**Importancia**: high

#### Primera Ley de De Morgan Generalizada (inter_complement_eq_complement_union)

**Ubicación**: `BoolAlg.GenDeMorgan.lean`, línea 90
**Orden**: 4º teorema (LEY FUNDAMENTAL)

**Enunciado Matemático**: F ≠ ∅, ∀ X ∈ F, X ⊆ A → ⋂(ComplementFamily(A, F)) = A \ ⋃F.

**Firma Lean4**:

```lean
theorem inter_complement_eq_complement_union (A F : U)
    (hF_nonempty : F ≠ ∅) (_hF_subsets : ∀ X, X ∈ F → X ⊆ A) :
    (⋂ (ComplementFamily A F)) = sdiff A (⋃ F)
```

**Dependencias**: `ComplementFamily`, `interSet_mem_iff`, `complement_mem_ComplementFamily`, `mem_sdiff_iff`, `mem_sUnion_iff`, `ExtSet`
**Importancia**: high

#### Segunda Ley de De Morgan Generalizada (union_complement_eq_complement_inter)

**Ubicación**: `BoolAlg.GenDeMorgan.lean`, línea 148
**Orden**: 5º teorema (LEY DUAL)

**Enunciado Matemático**: F ≠ ∅, ∀ X ∈ F, X ⊆ A → ⋃(ComplementFamily(A, F)) = A \ ⋂F.

**Firma Lean4**:

```lean
theorem union_complement_eq_complement_inter (A F : U)
    (hF_nonempty : F ≠ ∅) (_hF_subsets : ∀ X, X ∈ F → X ⊆ A) :
    (⋃ (ComplementFamily A F)) = sdiff A (⋂ F)
```

**Dependencias**: `ComplementFamily`, `interSet_mem_iff`, `mem_sdiff_iff`, `mem_sUnion_iff`, `ExtSet`
**Importancia**: high

#### Doble complemento (double_complement)

**Ubicación**: `BoolAlg.GenDeMorgan.lean`, línea 195
**Orden**: 6º teorema

**Enunciado Matemático**: B ⊆ A → A \ (A \ B) = B.

**Firma Lean4**:

```lean
theorem double_complement (A B : U) (hB_sub : B ⊆ A) :
    sdiff A (sdiff A B) = B
```

**Dependencias**: `mem_sdiff_iff`, `ExtSet`, `Classical.byContradiction`
**Importancia**: high

#### Unión de subconjuntos (union_subsets)

**Ubicación**: `BoolAlg.GenDeMorgan.lean`, línea 215
**Orden**: 7º teorema

**Enunciado Matemático**: (∀ X ∈ F, X ⊆ A) → ⋃F ⊆ A.

**Firma Lean4**:

```lean
theorem union_subsets (F A : U) (hF_subsets : ∀ X, X ∈ F → X ⊆ A) :
    (⋃ F) ⊆ A
```

**Dependencias**: `mem_sUnion_iff`
**Importancia**: medium

#### Complemento de la intersección del complemento es la unión (complement_inter_complement_eq_union)

**Ubicación**: `BoolAlg.GenDeMorgan.lean`, línea 224
**Orden**: 8º teorema

**Enunciado Matemático**: F ≠ ∅, ∀ X ∈ F, X ⊆ A → A \ ⋂(ComplementFamily(A,F)) = ⋃F.

**Firma Lean4**:

```lean
theorem complement_inter_complement_eq_union (A F : U)
    (hF_nonempty : F ≠ ∅) (hF_subsets : ∀ X, X ∈ F → X ⊆ A) :
    sdiff A (⋂ (ComplementFamily A F)) = ⋃ F
```

**Dependencias**: `inter_complement_eq_complement_union`, `double_complement`, `union_subsets`
**Importancia**: medium

#### Intersección de subconjuntos (inter_subsets)

**Ubicación**: `BoolAlg.GenDeMorgan.lean`, línea 234
**Orden**: 9º teorema

**Enunciado Matemático**: F ≠ ∅, ∀ X ∈ F, X ⊆ A → ⋂F ⊆ A.

**Firma Lean4**:

```lean
theorem inter_subsets (F A : U) (hF_nonempty : F ≠ ∅) (hF_subsets : ∀ X, X ∈ F → X ⊆ A) :
    (⋂ F) ⊆ A
```

**Dependencias**: `interSet_mem_iff`, `nonempty_iff_exists_mem`
**Importancia**: medium

#### Complemento de la unión del complemento es la intersección (complement_union_complement_eq_inter)

**Ubicación**: `BoolAlg.GenDeMorgan.lean`, línea 244
**Orden**: 10º teorema

**Enunciado Matemático**: F ≠ ∅, ∀ X ∈ F, X ⊆ A → A \ ⋃(ComplementFamily(A,F)) = ⋂F.

**Firma Lean4**:

```lean
theorem complement_union_complement_eq_inter (A F : U)
    (hF_nonempty : F ≠ ∅) (hF_subsets : ∀ X, X ∈ F → X ⊆ A) :
    sdiff A (⋃ (ComplementFamily A F)) = (⋂ F)
```

**Dependencias**: `union_complement_eq_complement_inter`, `double_complement`, `inter_subsets`
**Importancia**: medium

### 4.12 BoolAlg.GenDistributive.lean

#### Especificación de IntersectFamily (IntersectFamily_is_specified)

**Ubicación**: `BoolAlg.GenDistributive.lean`, línea 56
**Orden**: 1º teorema

**Enunciado Matemático**: Y ∈ IntersectFamily(A, F) ↔ Y ⊆ A ∧ ∃ X ∈ F, Y = A ∩ X.

**Firma Lean4**:

```lean
theorem IntersectFamily_is_specified (A F Y : U) :
    Y ∈ IntersectFamily A F ↔ Y ⊆ A ∧ ∃ X, X ∈ F ∧ Y = inter A X
```

**Dependencias**: `IntersectFamily`, `mem_sep_iff`, `mem_powerset_iff`
**Importancia**: medium

#### Intersección pertenece a IntersectFamily (intersect_mem_IntersectFamily)

**Ubicación**: `BoolAlg.GenDistributive.lean`, línea 62
**Orden**: 2º teorema

**Enunciado Matemático**: X ∈ F → A ∩ X ∈ IntersectFamily(A, F).

**Firma Lean4**:

```lean
theorem intersect_mem_IntersectFamily (A F X : U) (hX : X ∈ F) :
    inter A X ∈ IntersectFamily A F
```

**Dependencias**: `IntersectFamily_is_specified`, `mem_inter_iff`
**Importancia**: medium

#### Especificación de UnionFamily (UnionFamily_is_specified)

**Ubicación**: `BoolAlg.GenDistributive.lean`, línea 78
**Orden**: 3º teorema

**Enunciado Matemático**: Y ∈ UnionFamily(A, F) ↔ Y ⊆ A ∪ ⋃F ∧ ∃ X ∈ F, Y = A ∪ X.

**Firma Lean4**:

```lean
theorem UnionFamily_is_specified (A F Y : U) :
    Y ∈ UnionFamily A F ↔ Y ⊆ union A (⋃ F) ∧ ∃ X, X ∈ F ∧ Y = union A X
```

**Dependencias**: `UnionFamily`, `mem_sep_iff`, `mem_powerset_iff`
**Importancia**: medium

#### Unión pertenece a UnionFamily (union_mem_UnionFamily)

**Ubicación**: `BoolAlg.GenDistributive.lean`, línea 84
**Orden**: 4º teorema

**Enunciado Matemático**: X ∈ F → A ∪ X ∈ UnionFamily(A, F).

**Firma Lean4**:

```lean
theorem union_mem_UnionFamily (A F X : U) (hX : X ∈ F) :
    union A X ∈ UnionFamily A F
```

**Dependencias**: `UnionFamily_is_specified`, `mem_union_iff`, `mem_sUnion_iff`
**Importancia**: medium

#### Primera Ley Distributiva Generalizada (inter_distrib_union)

**Ubicación**: `BoolAlg.GenDistributive.lean`, línea 102
**Orden**: 5º teorema (LEY FUNDAMENTAL)

**Enunciado Matemático**: A ∩ (⋃F) = ⋃(IntersectFamily(A, F)).

**Firma Lean4**:

```lean
theorem inter_distrib_union (A F : U) :
    inter A (⋃ F) = (⋃ (IntersectFamily A F))
```

**Dependencias**: `IntersectFamily_is_specified`, `intersect_mem_IntersectFamily`, `mem_inter_iff`, `mem_sUnion_iff`, `ExtSet`
**Importancia**: high

#### IntersectFamily no vacía (IntersectFamily_nonempty)

**Ubicación**: `BoolAlg.GenDistributive.lean`, línea 139
**Orden**: 6º teorema

**Enunciado Matemático**: F ≠ ∅ → IntersectFamily(A, F) ≠ ∅.

**Firma Lean4**:

```lean
theorem IntersectFamily_nonempty (A F : U) (hF : F ≠ ∅) :
    IntersectFamily A F ≠ ∅
```

**Dependencias**: `intersect_mem_IntersectFamily`, `nonempty_iff_exists_mem`, `EmptySet_is_empty`
**Importancia**: low

#### UnionFamily no vacía (UnionFamily_nonempty)

**Ubicación**: `BoolAlg.GenDistributive.lean`, línea 150
**Orden**: 7º teorema

**Enunciado Matemático**: F ≠ ∅ → UnionFamily(A, F) ≠ ∅.

**Firma Lean4**:

```lean
theorem UnionFamily_nonempty (A F : U) (hF : F ≠ ∅) :
    UnionFamily A F ≠ ∅
```

**Dependencias**: `union_mem_UnionFamily`, `nonempty_iff_exists_mem`, `EmptySet_is_empty`
**Importancia**: low

#### Segunda Ley Distributiva Generalizada (union_distrib_inter)

**Ubicación**: `BoolAlg.GenDistributive.lean`, línea 163
**Orden**: 8º teorema (LEY DUAL)

**Enunciado Matemático**: F ≠ ∅ → A ∪ (⋂F) = ⋂(UnionFamily(A, F)).

**Firma Lean4**:

```lean
theorem union_distrib_inter (A F : U) (hF : F ≠ ∅) :
    union A (⋂ F) = (⋂ (UnionFamily A F))
```

**Dependencias**: `UnionFamily_nonempty`, `interSet_mem_iff`, `union_mem_UnionFamily`, `UnionFamily_is_specified`, `mem_union_iff`, `ExtSet`
**Importancia**: high

#### Distributividad conmutada de intersección (union_inter_distrib)

**Ubicación**: `BoolAlg.GenDistributive.lean`, línea 207
**Orden**: 9º teorema

**Enunciado Matemático**: (⋃F) ∩ A = ⋃(IntersectFamily(A, F)).

**Firma Lean4**:

```lean
theorem union_inter_distrib (A F : U) :
    inter (⋃ F) A = (⋃ (IntersectFamily A F))
```

**Dependencias**: `inter_distrib_union`, `inter_comm`
**Importancia**: low

#### Distributividad conmutada de unión (inter_union_distrib)

**Ubicación**: `BoolAlg.GenDistributive.lean`, línea 214
**Orden**: 10º teorema

**Enunciado Matemático**: F ≠ ∅ → (⋂F) ∪ A = ⋂(UnionFamily(A, F)).

**Firma Lean4**:

```lean
theorem inter_union_distrib (A F : U) (hF : F ≠ ∅) :
    union (⋂ F) A = (⋂ (UnionFamily A F))
```

**Dependencias**: `union_distrib_inter`, `union_comm`
**Importancia**: low

### 4.13 SetOps.SetOrder.lean

#### El Vacío es Mínimo Global

**Ubicación**: `SetOps.SetOrder.lean`, línea 18  
**Orden**: 1º teorema principal (TEOREMA BASE)

**Enunciado Matemático**: ∅ es subconjunto de cualquier conjunto.

**Firma Lean4**:

```lean
theorem empty_is_minimum (x : U) : ∅ ⊆ x
```

**Dependencias**: `EmptySet`, `subset`, `EmptySet_is_empty`
**Importancia**: high

#### Unicidad del Mínimo Global

**Ubicación**: `SetOps.SetOrder.lean`, línea 23  
**Orden**: 2º teorema principal

**Enunciado Matemático**: Si x es subconjunto de todo conjunto, entonces x = ∅.

**Firma Lean4**:

```lean
theorem empty_is_unique_minimum (x : U) :
  (∀ y, x ⊆ y) → x = ∅
```

**Dependencias**: `subset`, `EmptySet`, `subset_antisymm`
**Importancia**: medium

#### Toda Familia está Acotada Inferiormente

**Ubicación**: `SetOps.SetOrder.lean`, línea 59  
**Orden**: 3º teorema principal

**Enunciado Matemático**: Cualquier familia S está acotada inferiormente (por ∅).

**Firma Lean4**:

```lean
theorem any_family_bounded_below (S : U) : isBoundedBelow S
```

**Dependencias**: `isBoundedBelow`, `empty_is_minimum`
**Importancia**: medium

#### La Intersección es Greatest Lower Bound

**Ubicación**: `SetOps.SetOrder.lean`, línea 64  
**Orden**: 4º teorema principal (TEOREMA FUNDAMENTAL)

**Enunciado Matemático**: A ∩ B es el mayor elemento que es subconjunto de ambos A y B.

**Firma Lean4**:

```lean
theorem inter_is_glb (A B : U) :
  (∀ x, (x ⊆ A ∧ x ⊆ B) → x ⊆ (A ∩ B)) ∧
  (∀ z, (∀ x, (x ⊆ A ∧ x ⊆ B) → x ⊆ z) → (A ∩ B) ⊆ z)
```

**Dependencias**: `inter`, `subset`, `mem_inter_iff`, `inter_subset`
**Importancia**: high

#### La Unión es Least Upper Bound

**Ubicación**: `SetOps.SetOrder.lean`, línea 76  
**Orden**: 5º teorema principal (TEOREMA DUAL)

**Enunciado Matemático**: A ∪ B es el menor elemento que contiene tanto A como B.

**Firma Lean4**:

```lean
theorem union_is_lub (A B : U) :
  (∀ x, (A ⊆ x ∧ B ⊆ x) → (A ∪ B) ⊆ x) ∧
  (∀ z, (∀ x, (A ⊆ x ∧ B ⊆ x) → z ⊆ x) → z ⊆ (A ∪ B))
```

**Dependencias**: `union`, `subset`, `mem_union_iff`
**Importancia**: high

#### Reflexividad del Orden

**Ubicación**: `SetOps.SetOrder.lean`, línea 91  
**Orden**: 6º teorema principal

**Enunciado Matemático**: La relación ⊆ es reflexiva.

**Firma Lean4**:

```lean
theorem order_reflexive (x : U) : x ⊆ x
```

**Dependencias**: `subset`, `subset_refl`
**Importancia**: medium

#### Transitividad del Orden

**Ubicación**: `SetOps.SetOrder.lean`, línea 94  
**Orden**: 7º teorema principal

**Enunciado Matemático**: La relación ⊆ es transitiva.

**Firma Lean4**:

```lean
theorem order_transitive (x y z : U) : x ⊆ y → y ⊆ z → x ⊆ z
```

**Dependencias**: `subset`, `subset_trans`
**Importancia**: medium

#### Antisimetría del Orden

**Ubicación**: `SetOps.SetOrder.lean`, línea 97  
**Orden**: 8º teorema principal

**Enunciado Matemático**: La relación ⊆ es antisimétrica.

**Firma Lean4**:

```lean
theorem order_antisymmetric (x y : U) : x ⊆ y → y ⊆ x → x = y
```

**Dependencias**: `subset`, `subset_antisymm`

#### Monotonicidad de la Unión (Izquierda)

**Ubicación**: `SetOps.SetOrder.lean`, línea 100  
**Orden**: 9º teorema principal

**Enunciado Matemático**: Si A ⊆ B, entonces A ∪ C ⊆ B ∪ C.

**Firma Lean4**:

```lean
theorem union_monotone_left (A B C : U) :
  A ⊆ B → (A ∪ C) ⊆ (B ∪ C)
```

**Dependencias**: `subset`, `union`, `mem_union_iff`

#### Monotonicidad de la Unión (Derecha)

**Ubicación**: `SetOps.SetOrder.lean`, línea 108  
**Orden**: 10º teorema principal

**Enunciado Matemático**: Si A ⊆ B, entonces C ∪ A ⊆ C ∪ B.

**Firma Lean4**:

```lean
theorem union_monotone_right (A B C : U) :
  A ⊆ B → (C ∪ A) ⊆ (C ∪ B)
```

**Dependencias**: `subset`, `union`, `mem_union_iff`

#### Monotonicidad de la Intersección (Izquierda)

**Ubicación**: `SetOps.SetOrder.lean`, línea 116  
**Orden**: 11º teorema principal

**Enunciado Matemático**: Si A ⊆ B, entonces A ∩ C ⊆ B ∩ C.

**Firma Lean4**:

```lean
theorem inter_monotone_left (A B C : U) :
  A ⊆ B → (A ∩ C) ⊆ (B ∩ C)
```

**Dependencias**: `subset`, `inter`, `mem_inter_iff`

#### Monotonicidad de la Intersección (Derecha)

**Ubicación**: `SetOps.SetOrder.lean`, línea 123  
**Orden**: 12º teorema principal

**Enunciado Matemático**: Si A ⊆ B, entonces C ∩ A ⊆ C ∩ B.

**Firma Lean4**:

```lean
theorem inter_monotone_right (A B C : U) :
  A ⊆ B → (C ∩ A) ⊆ (C ∩ B)
```

**Dependencias**: `subset`, `inter`, `mem_inter_iff`
**Importancia**: medium

### 4.14 SetOps.SetStrictOrder.lean

#### Orden Estricto Implica Orden Parcial

**Ubicación**: `SetOps.SetStrictOrder.lean`, línea 15  
**Orden**: 1º teorema principal (TEOREMA BASE)

**Enunciado Matemático**: Si A ⊂ B, entonces A ⊆ B.

**Firma Lean4**:

```lean
theorem subset_subseteq (x y : U) :
  x ⊂ y → x ⊆ y
```

**Dependencias**: `ssubset`, `subset`
**Importancia**: medium

#### Caracterización del Orden Estricto

**Ubicación**: `SetOps.SetStrictOrder.lean`, línea 20  
**Orden**: 2º teorema principal

**Enunciado Matemático**: A ⊆ B si y solo si A ⊂ B o A = B.

**Firma Lean4**:

```lean
theorem subseteq_subset_or_eq (x y : U) :
  x ⊆ y → (x ⊂ y ∨ x = y)
```

**Dependencias**: `subset`, `ssubset`
**Importancia**: medium

#### Irreflexividad del Orden Estricto

**Ubicación**: `SetOps.SetStrictOrder.lean`, línea 26  
**Orden**: 3º teorema principal (PROPIEDAD FUNDAMENTAL)

**Enunciado Matemático**: Ningún conjunto es subconjunto estricto de sí mismo.

**Firma Lean4**:

```lean
theorem strict_order_irreflexive (x : U) : ¬(x ⊂ x)
```

**Dependencias**: `ssubset`
**Importancia**: high

#### Asimetría del Orden Estricto

**Ubicación**: `SetOps.SetStrictOrder.lean`, línea 30  
**Orden**: 4º teorema principal

**Enunciado Matemático**: Si A ⊂ B, entonces B ⊄ A.

**Firma Lean4**:

```lean
theorem strict_order_asymmetric (x y : U) : x ⊂ y → ¬(y ⊂ x)
```

**Dependencias**: `ssubset`, `subset_antisymm`
**Importancia**: medium

#### Transitividad del Orden Estricto

**Ubicación**: `SetOps.SetStrictOrder.lean`, línea 37  
**Orden**: 5º teorema principal

**Enunciado Matemático**: Si A ⊂ B y B ⊂ C, entonces A ⊂ C.

**Firma Lean4**:

```lean
theorem strict_order_transitive (x y z : U) : x ⊂ y → y ⊂ z → x ⊂ z
```

**Dependencias**: `ssubset`, `order_transitive`, `subset_antisymm`
**Importancia**: medium

#### Transitividad Mixta (Izquierda)

**Ubicación**: `SetOps.SetStrictOrder.lean`, línea 48  
**Orden**: 6º teorema principal

**Enunciado Matemático**: Si A ⊆ B y B ⊂ C, entonces A ⊂ C.

**Firma Lean4**:

```lean
theorem subset_transitive_mixed_left (x y z : U) :
  (x ⊆ y) → (y ⊂ z) → (x ⊂ z)
```

**Dependencias**: `subset`, `ssubset`, `order_transitive`, `subset_antisymm`
**Importancia**: medium

#### Transitividad Mixta (Derecha)

**Ubicación**: `SetOps.SetStrictOrder.lean`, línea 58  
**Orden**: 7º teorema principal

**Enunciado Matemático**: Si A ⊂ B y B ⊆ C, entonces A ⊂ C.

**Firma Lean4**:

```lean
theorem subset_transitive_mixed_right (x y z : U) :
  (x ⊂ y) → (y ⊆ z) → (x ⊂ z)
```

**Dependencias**: `ssubset`, `subset`, `order_transitive`, `subset_antisymm`
**Importancia**: medium

#### Equivalencia entre Órdenes

**Ubicación**: `SetOps.SetStrictOrder.lean`, línea 68  
**Orden**: 8º teorema principal (TEOREMA CENTRAL)

**Enunciado Matemático**: (A ⊆ B ∧ A ≠ B) ↔ A ⊂ B.

**Firma Lean4**:

```lean
theorem partial_to_strict_order (x y : U) :
  ((x ⊆ y) ∧ (x ≠ y)) ↔ x ⊂ y
```

**Dependencias**: `subset`, `ssubset`
**Importancia**: high

#### Tricotomía Parcial

**Ubicación**: `SetOps.SetStrictOrder.lean`, línea 78  
**Orden**: 9º teorema principal

**Enunciado Matemático**: Para cualesquiera A, B: A ⊂ B ∨ A = B ∨ B ⊂ A ∨ (A ⊄ B ∧ B ⊄ A).

**Firma Lean4**:

```lean
theorem strict_order_trichotomy_partial (x y : U) :
  x ⊂ y ∨ x = y ∨ y ⊂ x ∨ (¬(x ⊆ y) ∧ ¬(y ⊆ x))
```

**Dependencias**: `ssubset`, `subset`
**Importancia**: medium

#### El Vacío es Estrictamente Menor que Cualquier No Vacío

**Ubicación**: `SetOps.SetStrictOrder.lean`, línea 87  
**Orden**: 10º teorema principal

**Enunciado Matemático**: Si A ≠ ∅, entonces ∅ ⊂ A.

**Firma Lean4**:

```lean
theorem empty_strict_subset_nonempty (x : U) :
  x ≠ ∅ → ∅ ⊂ x
```

**Dependencias**: `EmptySet`, `ssubset`, `empty_is_minimum`
**Importancia**: medium

#### Existencia de Elemento Diferenciador

**Ubicación**: `SetOps.SetStrictOrder.lean`, línea 93  
**Orden**: 11º teorema principal (TEOREMA DE DIFERENCIACIÓN)

**Enunciado Matemático**: Si A ⊂ B, entonces existe z tal que z ∈ B y z ∉ A.

**Firma Lean4**:

```lean
theorem strict_subset_nonempty (x y : U) :
  x ⊂ y → ∃ z, z ∈ y ∧ z ∉ x
```

**Dependencias**: `ssubset`, `order_antisymmetric`, `Classical.byContradiction`
**Importancia**: high

### 4.15 OrderedPair.lean (Extensiones)

#### Igualdad Directa de Pares Ordenados

**Ubicación**: `OrderedPair.lean`, línea 25  
**Orden**: 1º teorema adicional

**Enunciado Matemático**: Si a = c y b = d, entonces ⟨a,b⟩ = ⟨c,d⟩.

**Firma Lean4**:

```lean
theorem OrderedPair_eq_of (a b c d : U) :
  (a = c ∧ b = d) → ⟨a, b⟩ = ⟨c, d⟩
```

**Dependencias**: `OrderedPair`
**Importancia**: low

#### Caracterización Bidireccional de Igualdad

**Ubicación**: `OrderedPair.lean`, línea 32  
**Orden**: 2º teorema adicional (TEOREMA CENTRAL)

**Enunciado Matemático**: ⟨a,b⟩ = ⟨c,d⟩ si y solo si a = c y b = d.

**Firma Lean4**:

```lean
theorem OrderedPair_eq_iff (a b c d : U) :
  ⟨a, b⟩ = ⟨c, d⟩ ↔ (a = c ∧ b = d)
```

**Dependencias**: `OrderedPair`, `Eq_of_OrderedPairs_given_projections`, `OrderedPair_eq_of`
**Importancia**: high

#### Inclusión en Conjunto Potencia Doble

**Ubicación**: `OrderedPair.lean`, línea 42  
**Orden**: 3º teorema adicional

**Enunciado Matemático**: Si a ∈ A y b ∈ B, entonces ⟨a,b⟩ ∈ 𝒫(𝒫(A ∪ B)).

**Firma Lean4**:

```lean
theorem OrderedPair_in_powerset (a b A B : U)
  (ha : a ∈ A) (hb : b ∈ B) :
    ⟨a, b⟩ ∈ 𝒫 (𝒫 (A ∪ B))
```

**Dependencias**: `OrderedPair`, `PowerSet`, `union`, `Singleton`, `PairSet`
**Importancia**: medium

### 4.16 BoolAlg.Ring.lean

#### symmDiff es Conmutativa

**Ubicación**: `BoolAlg.Ring.lean`, línea 59  
**Orden**: 1º teorema principal

**Enunciado Matemático**: A △ B = B △ A.

**Firma Lean4**:

```lean
theorem symmDiff_is_comm (X Y : U) :
  symmDiff X Y = symmDiff Y X
```

**Dependencias**: `symmDiff`, `symmDiff_comm`
**Importancia**: medium

#### symmDiff Identidad con Vacío

**Ubicación**: `BoolAlg.Ring.lean`, línea 73  
**Orden**: 2º teorema principal

**Enunciado Matemático**: X △ ∅ = X.

**Firma Lean4**:

```lean
theorem symmDiff_empty_identity (X : U) :
  symmDiff X ∅ = X
```

**Dependencias**: `symmDiff`, `symmDiff_comm`, `empty_symmDiff`
**Importancia**: medium

#### symmDiff Inverso

**Ubicación**: `BoolAlg.Ring.lean`, línea 79  
**Orden**: 3º teorema principal

**Enunciado Matemático**: X △ X = ∅.

**Firma Lean4**:

```lean
theorem symmDiff_inverse (X : U) :
  symmDiff X X = ∅
```

**Dependencias**: `symmDiff`, `symmDiff_self`
**Importancia**: medium

#### symmDiff es Asociativa

**Ubicación**: `BoolAlg.Ring.lean`, línea 86  
**Orden**: 4º teorema principal (PROPIEDAD FUNDAMENTAL)

**Enunciado Matemático**: (X △ Y) △ Z = X △ (Y △ Z).

**Firma Lean4**:

```lean
theorem symmDiff_assoc (X Y Z : U) :
  symmDiff (symmDiff X Y) Z = symmDiff X (symmDiff Y Z)
```

**Dependencias**: `symmDiff`, `ExtSet`
**Importancia**: high

#### Distributividad de Intersección sobre symmDiff

**Ubicación**: `BoolAlg.Ring.lean`, línea 180  
**Orden**: 5º teorema principal

**Enunciado Matemático**: X ∩ (Y △ Z) = (X ∩ Y) △ (X ∩ Z).

**Firma Lean4**:

```lean
theorem symmDiff_inter_distrib (X Y Z : U) :
    inter X (symmDiff Y Z) = symmDiff (inter X Y) (inter X Z)
```

**Dependencias**: `symmDiff`, `inter`, `ExtSet`
**Importancia**: high

#### symmDiff de Subconjuntos es Subconjunto

**Ubicación**: `BoolAlg.Ring.lean`, línea 240  
**Orden**: 6º teorema principal

**Enunciado Matemático**: Si X, Y ⊆ A, entonces X △ Y ⊆ A.

**Firma Lean4**:

```lean
theorem symmDiff_mem_powerset (A X Y : U) (hX : X ∈ 𝒫 A) (hY : Y ∈ 𝒫 A) :
    symmDiff X Y ∈ 𝒫 A
```

**Dependencias**: `symmDiff`, `PowerSet`
**Importancia**: medium

#### symmDiff como Unión de Diferencias

**Ubicación**: `BoolAlg.Ring.lean`, línea 251  
**Orden**: 7º teorema principal

**Enunciado Matemático**: X △ Y = (X \ Y) ∪ (Y \ X).

**Firma Lean4**:

```lean
theorem symmDiff_eq_union_diff (X Y : U) :
  symmDiff X Y = union (X \ Y) (Y \ X)
```

**Dependencias**: `symmDiff`, `union`, `sdiff`
**Importancia**: medium

#### symmDiff usando Complemento

**Ubicación**: `BoolAlg.Ring.lean`, línea 257  
**Orden**: 8º teorema principal

**Enunciado Matemático**: Para X, Y ⊆ A: X △ Y = (X ∪ Y) ∩ (X ∩ Y)^∁[A].

**Firma Lean4**:

```lean
theorem symmDiff_as_complement (A X Y : U) (hX : X ⊆ A) (hY : Y ⊆ A) :
    symmDiff X Y = inter (union X Y) ((inter X Y)^∁[ A ])
```

**Dependencias**: `symmDiff`, `inter`, `union`, `Complement`
**Importancia**: medium

#### symmDiff igual a X implica Y Vacío

**Ubicación**: `BoolAlg.Ring.lean`, línea 288  
**Orden**: 9º teorema principal

**Enunciado Matemático**: X △ Y = X ↔ Y = ∅.

**Firma Lean4**:

```lean
theorem symmDiff_eq_self_iff_empty (X Y : U) : symmDiff X Y = X ↔ Y = ∅
```

**Dependencias**: `symmDiff`, `EmptySet`, `ExtSet`
**Importancia**: medium

### 4.17 BoolAlg.PowerSetAlgebra.lean

#### Especificación del Complemento

**Ubicación**: `BoolAlg.PowerSetAlgebra.lean`, línea 73  
**Orden**: 1º teorema principal

**Enunciado Matemático**: z ∈ X^∁[A] ↔ z ∈ A ∧ z ∉ X.

**Firma Lean4**:

```lean
theorem Complement_is_specified (A X z : U) : z ∈ (X ^∁[ A ]) ↔ z ∈ A ∧ z ∉ X
```

**Dependencias**: `Complement`, `sdiff`
**Importancia**: high

#### Unión de Subconjuntos es Subconjunto

**Ubicación**: `BoolAlg.PowerSetAlgebra.lean`, línea 80  
**Orden**: 2º teorema principal

**Enunciado Matemático**: Si X, Y ∈ 𝒫(A), entonces X ∪ Y ∈ 𝒫(A).

**Firma Lean4**:

```lean
theorem union_mem_powerset (A X Y : U) (hX : X ∈ 𝒫 A) (hY : Y ∈ 𝒫 A) :
    union X Y ∈ 𝒫 A
```

**Dependencias**: `PowerSet`, `union`
**Importancia**: medium

#### Intersección con Universo

**Ubicación**: `BoolAlg.PowerSetAlgebra.lean`, línea 115  
**Orden**: 3º teorema principal

**Enunciado Matemático**: Para X ⊆ A: X ∩ A = X.

**Firma Lean4**:

```lean
theorem powerset_inter_universe (A X : U) (hX : X ⊆ A) : inter X A = X
```

**Dependencias**: `inter`, `subset`, `ExtSet`
**Importancia**: medium

#### Unión con Complemento

**Ubicación**: `BoolAlg.PowerSetAlgebra.lean`, línea 132  
**Orden**: 4º teorema principal

**Enunciado Matemático**: Para X ⊆ A: X ∪ X^∁[A] = A.

**Firma Lean4**:

```lean
theorem powerset_union_complement (A X : U) (hX : X ⊆ A) : union X (X ^∁[ A ]) = A
```

**Dependencias**: `union`, `Complement`, `ExtSet`
**Importancia**: high

#### Intersección con Complemento

**Ubicación**: `BoolAlg.PowerSetAlgebra.lean`, línea 147  
**Orden**: 5º teorema principal

**Enunciado Matemático**: X ∩ X^∁[A] = ∅.

**Firma Lean4**:

```lean
theorem powerset_inter_complement (A X : U) : inter X (X ^∁[ A ]) = ∅
```

**Dependencias**: `inter`, `Complement`, `EmptySet`
**Importancia**: high

#### Distributiva: Unión sobre Intersección

**Ubicación**: `BoolAlg.PowerSetAlgebra.lean`, línea 158  
**Orden**: 6º teorema principal (LEY DISTRIBUTIVA)

**Enunciado Matemático**: X ∪ (Y ∩ Z) = (X ∪ Y) ∩ (X ∪ Z).

**Firma Lean4**:

```lean
theorem powerset_union_distrib_inter (X Y Z : U) :
    union X (inter Y Z) = inter (union X Y) (union X Z)
```

**Dependencias**: `union`, `inter`, `ExtSet`
**Importancia**: high

#### Distributiva: Intersección sobre Unión

**Ubicación**: `BoolAlg.PowerSetAlgebra.lean`, línea 183  
**Orden**: 7º teorema principal (LEY DISTRIBUTIVA DUAL)

**Enunciado Matemático**: X ∩ (Y ∪ Z) = (X ∩ Y) ∪ (X ∩ Z).

**Firma Lean4**:

```lean
theorem powerset_inter_distrib_union (X Y Z : U) :
    inter X (union Y Z) = union (inter X Y) (inter X Z)
```

**Dependencias**: `inter`, `union`, `ExtSet`
**Importancia**: high

#### De Morgan: Complemento de Unión

**Ubicación**: `BoolAlg.PowerSetAlgebra.lean`, línea 207  
**Orden**: 8º teorema principal (LEY DE DE MORGAN)

**Enunciado Matemático**: (X ∪ Y)^∁[A] = X^∁[A] ∩ Y^∁[A].

**Firma Lean4**:

```lean
theorem powerset_compl_union (A X Y : U) :
    (union X Y) ^∁[ A ] = inter (X ^∁[ A ]) (Y ^∁[ A ])
```

**Dependencias**: `Complement`, `union`, `inter`, `ExtSet`
**Importancia**: high

#### De Morgan: Complemento de Intersección

**Ubicación**: `BoolAlg.PowerSetAlgebra.lean`, línea 230  
**Orden**: 9º teorema principal (LEY DE DE MORGAN DUAL)

**Enunciado Matemático**: (X ∩ Y)^∁[A] = X^∁[A] ∪ Y^∁[A].

**Firma Lean4**:

```lean
theorem powerset_compl_inter (A X Y : U) :
    (inter X Y) ^∁[ A ] = union (X ^∁[ A ]) (Y ^∁[ A ])
```

**Dependencias**: `Complement`, `inter`, `union`, `ExtSet`
**Importancia**: high

#### Complemento de Subconjunto es Subconjunto (complement_mem_powerset)

**Ubicación**: `BoolAlg.PowerSetAlgebra.lean`, línea 97  
**Orden**: 3º teorema de clausura

**Enunciado Matemático**: Si X ∈ 𝒫(A), entonces X^∁[A] ∈ 𝒫(A).

**Firma Lean4**:

```lean
theorem complement_mem_powerset (A X : U) (_hX : X ∈ 𝒫 A) :
    (X ^∁[ A ]) ∈ 𝒫 A
```

**Dependencias**: `mem_powerset_iff`, `Complement_is_specified`
**Importancia**: medium

#### El Vacío está en Todo Conjunto Potencia (empty_in_powerset)

**Ubicación**: `BoolAlg.PowerSetAlgebra.lean`, línea 103  
**Orden**: 4º teorema de clausura (alias)

**Enunciado Matemático**: ∅ ∈ 𝒫(A) para todo A.

**Firma Lean4**:

```lean
theorem empty_in_powerset (A : U) : ∅ ∈ 𝒫 A
```

**Dependencias**: `empty_mem_powerset`
**Importancia**: low

**Nota**: Alias de `empty_mem_powerset` de PowerSet.lean.

#### El Universo está en su Conjunto Potencia (universe_in_PowerSet)

**Ubicación**: `BoolAlg.PowerSetAlgebra.lean`, línea 106  
**Orden**: 5º teorema de clausura (alias)

**Enunciado Matemático**: A ∈ 𝒫(A) para todo A.

**Firma Lean4**:

```lean
theorem universe_in_PowerSet (A : U) : A ∈ 𝒫 A
```

**Dependencias**: `self_mem_powerset`
**Importancia**: low

**Nota**: Alias de `self_mem_powerset` de PowerSet.lean.

#### Doble Complemento

**Ubicación**: `BoolAlg.PowerSetAlgebra.lean`, línea 283  
**Orden**: 10º teorema principal (INVOLUTIVIDAD)

**Enunciado Matemático**: Para X ⊆ A: (X^∁[A])^∁[A] = X.

**Firma Lean4**:

```lean
theorem powerset_double_complement (A X : U) (hX : X ⊆ A) :
    (X ^∁[ A ]) ^∁[ A ] = X
```

**Dependencias**: `Complement`, `subset`, `ExtSet`
**Importancia**: high

#### Absorción: Unión e Intersección

**Ubicación**: `BoolAlg.PowerSetAlgebra.lean`, línea 302  
**Orden**: 11º teorema principal

**Enunciado Matemático**: X ∪ (X ∩ Y) = X.

**Firma Lean4**:

```lean
theorem powerset_absorb_union_inter (X Y : U) : union X (inter X Y) = X
```

**Dependencias**: `union`, `inter`, `ExtSet`
**Importancia**: medium

#### Absorción: Intersección y Unión (powerset_absorb_inter_union)

**Ubicación**: `BoolAlg.PowerSetAlgebra.lean`, línea 316  
**Orden**: 12º teorema principal

**Enunciado Matemático**: X ∩ (X ∪ Y) = X.

**Firma Lean4**:

```lean
theorem powerset_absorb_inter_union (X Y : U) : inter X (union X Y) = X
```

**Dependencias**: `inter`, `union`, `ExtSet`
**Importancia**: medium

#### Idempotencia de Unión

**Ubicación**: `BoolAlg.PowerSetAlgebra.lean`, línea 322  
**Orden**: 13º teorema principal

**Enunciado Matemático**: X ∪ X = X.

**Firma Lean4**:

```lean
theorem powerset_union_idempotent (X : U) : union X X = X
```

**Dependencias**: `union`, `union_self`
**Importancia**: low

#### Idempotencia de Intersección

**Ubicación**: `BoolAlg.PowerSetAlgebra.lean`, línea 326  
**Orden**: 14º teorema principal

**Enunciado Matemático**: X ∩ X = X.

**Firma Lean4**:

```lean
theorem powerset_inter_idempotent (X : U) : inter X X = X
```

**Dependencias**: `inter`, `inter_self`
**Importancia**: low

#### Conmutatividad de Unión (powerset_union_comm)

**Ubicación**: `BoolAlg.PowerSetAlgebra.lean`, línea 331  
**Orden**: 15º teorema principal

**Enunciado Matemático**: X ∪ Y = Y ∪ X.

**Firma Lean4**:

```lean
theorem powerset_union_comm (X Y : U) : union X Y = union Y X
```

**Dependencias**: `union_comm`
**Importancia**: low

#### Conmutatividad de Intersección (powerset_inter_comm)

**Ubicación**: `BoolAlg.PowerSetAlgebra.lean`, línea 334  
**Orden**: 16º teorema principal

**Enunciado Matemático**: X ∩ Y = Y ∩ X.

**Firma Lean4**:

```lean
theorem powerset_inter_comm (X Y : U) : inter X Y = inter Y X
```

**Dependencias**: `inter_comm`
**Importancia**: low

#### Asociatividad de Unión (powerset_union_assoc)

**Ubicación**: `BoolAlg.PowerSetAlgebra.lean`, línea 339  
**Orden**: 17º teorema principal

**Enunciado Matemático**: X ∪ (Y ∪ Z) = (X ∪ Y) ∪ Z.

**Firma Lean4**:

```lean
theorem powerset_union_assoc (X Y Z : U) : union X (union Y Z) = union (union X Y) Z
```

**Dependencias**: `union_assoc`
**Importancia**: low

#### Asociatividad de Intersección (powerset_inter_assoc)

**Ubicación**: `BoolAlg.PowerSetAlgebra.lean`, línea 343  
**Orden**: 18º teorema principal

**Enunciado Matemático**: X ∩ (Y ∩ Z) = (X ∩ Y) ∩ Z.

**Firma Lean4**:

```lean
theorem powerset_inter_assoc (X Y Z : U) : inter X (inter Y Z) = inter (inter X Y) Z
```

**Dependencias**: `inter_assoc`
**Importancia**: low

#### Aniquilación: Intersección con Vacío (powerset_inter_empty)

**Ubicación**: `BoolAlg.PowerSetAlgebra.lean`, línea 348  
**Orden**: 19º teorema principal

**Enunciado Matemático**: X ∩ ∅ = ∅.

**Firma Lean4**:

```lean
theorem powerset_inter_empty (X : U) : inter X ∅ = ∅
```

**Dependencias**: `inter_empty`
**Importancia**: low

#### Aniquilación: Vacío e Intersección (powerset_empty_inter)

**Ubicación**: `BoolAlg.PowerSetAlgebra.lean`, línea 351  
**Orden**: 20º teorema principal

**Enunciado Matemático**: ∅ ∩ X = ∅.

**Firma Lean4**:

```lean
theorem powerset_empty_inter (X : U) : inter ∅ X = ∅
```

**Dependencias**: `inter_comm`, `inter_empty`
**Importancia**: low

#### Complemento del Vacío

**Ubicación**: `BoolAlg.PowerSetAlgebra.lean`, línea 356  
**Orden**: 21º teorema principal

**Enunciado Matemático**: ∅^∁[A] = A.

**Firma Lean4**:

```lean
theorem powerset_complement_empty (A : U) : (∅ ^∁[ A ]) = A
```

**Dependencias**: `Complement`, `EmptySet`, `sdiff_empty`
**Importancia**: medium

#### Complemento del Universo

**Ubicación**: `BoolAlg.PowerSetAlgebra.lean`, línea 361  
**Orden**: 22º teorema principal

**Enunciado Matemático**: A^∁[A] = ∅.

**Firma Lean4**:

```lean
theorem powerset_complement_universe (A : U) : (A ^∁[ A ]) = ∅
```

**Dependencias**: `Complement`, `EmptySet`, `sdiff_self`
**Importancia**: medium

### 4.18 PeanoImport.lean

**Módulo**: `ZfcSetTheory.PeanoImport`
**Namespace**: `ZFC`
**Actualizado**: 2026-03-04 12:00

#### fromPeano mapea Peano en Von Neumann (fromPeano_is_nat)

**Ubicación**: `PeanoImport.lean`, línea 40
**Orden**: 1º teorema principal

**Enunciado Matemático**: Para todo `p : Peano.ℕ₀`, `fromPeano(p)` es un número natural de Von Neumann: `IsNat(fromPeano(p))`.

**Firma Lean4**:

```lean
theorem fromPeano_is_nat (n : Peano.ℕ₀) : IsNat (fromPeano (U := U) n)
```

**Dependencias**: `fromPeano`, `IsNat`, `isNat_zero`, `isNat_succ`
**Importancia**: high

#### fromPeano es Inyectiva (fromPeano_injective)

**Ubicación**: `PeanoImport.lean`, línea 46
**Orden**: 2º teorema principal

**Enunciado Matemático**: `fromPeano` es inyectiva: si `fromPeano(m) = fromPeano(n)` entonces `m = n`.

**Firma Lean4**:

```lean
theorem fromPeano_injective : Function.Injective (fromPeano (U := U))
```

**Dependencias**: `fromPeano`, `succ_nonempty`, `succ_injective`, `fromPeano_is_nat`
**Importancia**: high

**Nota de implementación**: `Function.Injective` usa ligadores estrictos-implícitos `⦃⦄`; en la hipótesis de inducción `ih : ∀ ⦃b⦄, fromPeano m' = fromPeano b → m' = b`, Lean infiere `b` del tipo de la prueba, por lo que se usa `ih proof` (no `ih n' proof`). `succ_injective` requiere argumentos `IsNat` explícitos.

#### fromPeano es Sobreyectiva (fromPeano_surjective)

**Ubicación**: `PeanoImport.lean`, línea 71
**Orden**: 3º teorema principal

**Enunciado Matemático**: Todo número natural de Von Neumann está en la imagen de `fromPeano`: si `IsNat(n)` entonces existe `p : Peano.ℕ₀` tal que `fromPeano(p) = n`.

**Firma Lean4**:

```lean
theorem fromPeano_surjective (n : U) (hn : IsNat n) :
    ∃ p : Peano.ℕ₀, fromPeano (U := U) p = n
```

**Dependencias**: `fromPeano`, `IsNat`, `strong_induction_principle`, `sep`, `Nat_in_Omega`, `mem_Omega_is_Nat`, `eq_zero_or_exists_succ`, `mem_succ_self`
**Importancia**: high

**Nota de implementación**: Demostrado por inducción fuerte sobre `S = sep ω (fun m => ∃ p, fromPeano p = m)`, aplicando `strong_induction_principle`.

#### fromPeano(toPeano(n)) = n (fromPeano_toPeano)

**Ubicación**: `PeanoImport.lean`, línea 100
**Orden**: 4º teorema principal

**Enunciado Matemático**: `toPeano` es sección derecha de `fromPeano`: para todo Von Neumann natural `n`, `fromPeano(toPeano(n, hn)) = n`.

**Firma Lean4**:

```lean
theorem fromPeano_toPeano (n : U) (hn : IsNat n) :
    fromPeano (U := U) (toPeano n hn) = n
```

**Dependencias**: `fromPeano`, `toPeano`, `fromPeano_surjective`, `Classical.choose_spec`
**Importancia**: high

#### toPeano(fromPeano(p)) = p (toPeano_fromPeano)

**Ubicación**: `PeanoImport.lean`, línea 105
**Orden**: 5º teorema principal

**Enunciado Matemático**: `toPeano` es sección izquierda de `fromPeano`: para todo Peano natural `p`, `toPeano(fromPeano(p), _) = p`.

**Firma Lean4**:

```lean
theorem toPeano_fromPeano (p : Peano.ℕ₀) :
    toPeano (fromPeano (U := U) p) (fromPeano_is_nat p) = p
```

**Dependencias**: `toPeano`, `fromPeano`, `fromPeano_injective`, `fromPeano_toPeano`, `fromPeano_is_nat`
**Importancia**: high

#### toPeano es Inyectiva (toPeano_injective)

**Ubicación**: `PeanoImport.lean`, línea 110
**Orden**: 6º teorema principal

**Enunciado Matemático**: `toPeano` es inyectiva en los naturales de Von Neumann: si `toPeano(m, hm) = toPeano(n, hn)` entonces `m = n`.

**Firma Lean4**:

```lean
theorem toPeano_injective {m n : U} (hm : IsNat m) (hn : IsNat n)
    (h : toPeano m hm = toPeano n hn) : m = n
```

**Dependencias**: `toPeano`, `fromPeano_toPeano`
**Importancia**: medium

#### toPeano es Sobreyectiva (toPeano_surjective)

**Ubicación**: `PeanoImport.lean`, línea 115
**Orden**: 7º teorema principal

**Enunciado Matemático**: `toPeano` es sobreyectiva: para todo Peano natural `p` existe un Von Neumann natural `n` tal que `toPeano(n, _) = p`.

**Firma Lean4**:

```lean
theorem toPeano_surjective (p : Peano.ℕ₀) :
    ∃ (n : U) (hn : IsNat n), toPeano n hn = p
```

**Dependencias**: `toPeano`, `fromPeano`, `fromPeano_is_nat`, `toPeano_fromPeano`
**Importancia**: medium

#### toPeano lleva ∅ a zero (toPeano_zero)

**Ubicación**: `PeanoImport.lean`, línea 147
**Orden**: 8º teorema principal

**Enunciado Matemático**: `toPeano(∅, isNat_zero) = Peano.ℕ₀.zero`.

**Firma Lean4**:

```lean
theorem toPeano_zero : toPeano (∅ : U) isNat_zero = Peano.ℕ₀.zero
```

**Dependencias**: `toPeano`, `fromPeano_injective`, `fromPeano_toPeano`, `isNat_zero`
**Importancia**: medium

#### toPeano preserva sucesor (toPeano_succ)

**Ubicación**: `PeanoImport.lean`, línea 155
**Orden**: 9º teorema principal

**Enunciado Matemático**: `toPeano(σ n, _) = Peano.ℕ₀.succ(toPeano(n, hn))` para todo Von Neumann natural n.

**Firma Lean4**:

```lean
theorem toPeano_succ (n : U) (hn : IsNat n) :
    toPeano (σ n) (isNat_succ n hn) = Peano.ℕ₀.succ (toPeano n hn)
```

**Dependencias**: `toPeano`, `fromPeano_injective`, `fromPeano_toPeano`, `isNat_succ`
**Importancia**: medium

#### Transporte de recursión VN → Peano, simple (recursion_transport)

**Ubicación**: `PeanoImport.lean`, línea 176
**Orden**: 10º teorema principal

**Enunciado Matemático**: Si `F : ω → U` satisface `F(∅) = a` y `F(σ n) = g(F(n))` para todo `n ∈ ω`, entonces `f := F ∘ ΠZ` satisface `f(𝟘) = a` y `f(σ p) = g(f(p))` para todo `p : Peano.ℕ₀`.

**Firma Lean4**:

```lean
theorem recursion_transport (F a g : U)
    (hF_zero : apply F (∅ : U) = a)
    (hF_succ : ∀ n, n ∈ ω → apply F (σ n) = apply g (apply F n)) :
    let f : Peano.ℕ₀ → U := fun p => apply F (ΠZ p : U)
    f Peano.ℕ₀.zero = a ∧ ∀ p, f (Peano.ℕ₀.succ p) = apply g (f p)
```

**Dependencias**: `fromPeano`, `Nat_in_Omega`, `fromPeano_is_nat`
**Importancia**: high

#### Transporte de recursión Peano → VN, simple (recursion_transport_inv)

**Ubicación**: `PeanoImport.lean`, línea 192
**Orden**: 11º teorema principal

**Enunciado Matemático**: Si `f : Peano.ℕ₀ → U` satisface `f(𝟘) = a` y `f(σ p) = g(f(p))`, entonces `f ∘ ZΠ` satisface la recursión en ω: `f(ZΠ(∅)) = a` y `f(ZΠ(σ n)) = g(f(ZΠ(n)))`.

**Firma Lean4**:

```lean
theorem recursion_transport_inv (a g : U) (f : Peano.ℕ₀ → U)
    (hf_zero : f Peano.ℕ₀.zero = a)
    (hf_succ : ∀ p, f (Peano.ℕ₀.succ p) = apply g (f p)) :
    f (ZΠ (∅ : U) isNat_zero) = a ∧
    ∀ (n : U) (hn : n ∈ ω),
      f (ZΠ (σ n) (isNat_succ n (mem_Omega_is_Nat n hn))) =
      apply g (f (ZΠ n (mem_Omega_is_Nat n hn)))
```

**Dependencias**: `toPeano`, `toPeano_zero`, `toPeano_succ`
**Importancia**: high

#### Transporte de recursión VN → Peano, con paso (recursion_transport_step)

**Ubicación**: `PeanoImport.lean`, línea 209
**Orden**: 12º teorema principal

**Enunciado Matemático**: Variante de `recursion_transport` para `RecursionTheoremWithStep`. Si `F(∅) = a` y `F(σ n) = g(⟨n, F(n)⟩)` (la función de paso recibe el índice actual), entonces `f := F ∘ ΠZ` satisface `f(𝟘) = a` y `f(σ p) = g(⟨ΠZ p, f(p)⟩)`.

**Firma Lean4**:

```lean
theorem recursion_transport_step (F a g : U)
    (hF_zero : apply F (∅ : U) = a)
    (hF_succ : ∀ n, n ∈ ω → apply F (σ n) = apply g ⟨n, apply F n⟩) :
    let f : Peano.ℕ₀ → U := fun p => apply F (ΠZ p : U)
    f Peano.ℕ₀.zero = a ∧ ∀ p, f (Peano.ℕ₀.succ p) = apply g ⟨(ΠZ p : U), f p⟩
```

**Dependencias**: `fromPeano`, `Nat_in_Omega`, `fromPeano_is_nat`
**Importancia**: high

#### Transporte de recursión Peano → VN, con paso (recursion_transport_step_inv)

**Ubicación**: `PeanoImport.lean`, línea 222
**Orden**: 13º teorema principal

**Enunciado Matemático**: Variante de `recursion_transport_inv` para `RecursionTheoremWithStep`. Si `f(σ p) = g(⟨ΠZ p, f(p)⟩)`, entonces `f(ZΠ(σ n)) = g(⟨n, f(ZΠ(n))⟩)` para todo `n ∈ ω`.

**Firma Lean4**:

```lean
theorem recursion_transport_step_inv (a g : U) (f : Peano.ℕ₀ → U)
    (hf_zero : f Peano.ℕ₀.zero = a)
    (hf_succ : ∀ p, f (Peano.ℕ₀.succ p) = apply g ⟨(ΠZ p : U), f p⟩) :
    f (ZΠ (∅ : U) isNat_zero) = a ∧
    ∀ (n : U) (hn : n ∈ ω),
      f (ZΠ (σ n) (isNat_succ n (mem_Omega_is_Nat n hn))) =
      apply g ⟨n, f (ZΠ n (mem_Omega_is_Nat n hn))⟩
```

**Dependencias**: `toPeano_zero`, `toPeano_succ`, `fromPeano_toPeano`
**Importancia**: high

#### El sucesor preserva y refleja la membresía (succ_mem_succ_iff)

**Ubicación**: `PeanoImport.lean`, línea 242
**Orden**: 14º teorema principal

**Enunciado Matemático**: Para números naturales de Von Neumann, `n ∈ m ↔ σ n ∈ σ m`.

**Firma Lean4**:

```lean
theorem succ_mem_succ_iff (n m : U) (hn : IsNat n) (hm : IsNat m) :
    n ∈ m ↔ σ n ∈ σ m
```

**Dependencias**: `trichotomy`, `nat_subset_mem_or_eq`, `isNat_succ`, `succ_injective`, `not_mem_self`, `mem_succ_iff`, `mem_succ_of_mem`
**Importancia**: high

#### fromPeano preserva el orden estricto ↔ membresía (fromPeano_lt_iff)

**Ubicación**: `PeanoImport.lean`, línea 279
**Orden**: 15º teorema principal

**Enunciado Matemático**: `Peano.StrictOrder.Lt p q ↔ (ΠZ p : U) ∈ (ΠZ q : U)`. El orden estricto de Peano corresponde exactamente a la membresía entre Von Neumann naturales.

**Firma Lean4**:

```lean
theorem fromPeano_lt_iff (p q : Peano.ℕ₀) :
    Peano.StrictOrder.Lt p q ↔ (fromPeano p : U) ∈ (fromPeano q : U)
```

**Dependencias**: `succ_mem_succ_iff`, `fromPeano_is_nat`, `Peano.StrictOrder.lt_def`
**Importancia**: high

#### fromPeano preserva el orden débil ↔ membresía o igualdad (fromPeano_le_iff)

**Ubicación**: `PeanoImport.lean`, línea 307
**Orden**: 16º teorema principal

**Enunciado Matemático**: `Peano.Order.Le p q ↔ (ΠZ p : U) ∈ (ΠZ q : U) ∨ (ΠZ p : U) = (ΠZ q : U)`. El orden débil de Peano corresponde a la membresía o igualdad en Von Neumann.

**Firma Lean4**:

```lean
theorem fromPeano_le_iff (p q : Peano.ℕ₀) :
    Peano.Order.Le p q ↔ (fromPeano p : U) ∈ (fromPeano q : U) ∨ (fromPeano p : U) = (fromPeano q : U)
```

**Dependencias**: `fromPeano_lt_iff`, `fromPeano_injective`, `fromPeano_toPeano`, `Peano.Order.le_def`
**Importancia**: high

---

### 4.19 Nat.Add.lean

**Módulo**: `ZfcSetTheory.Nat.Add`
**Namespace**: `ZFC.Nat.Add`
**Actualizado**: 2026-03-08 12:00

**Importancia por sección**:

- Sección 1 (succFn): medium — infraestructura recursiva
- Sección 2 (addFn/add): medium — infraestructura recursiva
- Sección 3 (ecuaciones de recursión): high — definición recursiva fundamental (add_zero, add_succ)
- Sección 4 (teorema puente): high — fromPeano_add, clave para transporte
- Sección 5 (propiedades algebraicas): high — conmutatividad, asociatividad, identidad izquierda
- Sección 6 (propiedades adicionales): medium — cancelación, monotonía

#### Sección 1: succFn

| Nombre | Descripción matemática | Firma Lean4 |
|--------|----------------------|-------------|
| `mem_succFn` | `⟨n, σ n⟩ ∈ succFn` para todo n ∈ ω | `theorem mem_succFn (n : U) (hn : n ∈ (ω : U)) : (⟨n, σ n⟩ : U) ∈ (succFn : U)` |
| `succFn_is_function` | `succFn` es función de ω en ω | `theorem succFn_is_function : IsFunction (succFn : U) ω ω` |
| `succFn_apply` | Aplicar `succFn` a n ∈ ω da σ n | `theorem succFn_apply (n : U) (hn : n ∈ (ω : U)) : apply (succFn : U) n = σ n` |

#### Sección 2: addFn y add

| Nombre | Descripción matemática | Firma Lean4 |
|--------|----------------------|-------------|
| `addFn_is_function` | `addFn m hm` es función de ω en ω | `theorem addFn_is_function (m : U) (hm : m ∈ (ω : U)) : IsFunction (addFn m hm) ω ω` |
| `add_eq` | Si m ∈ ω, `add m n = apply (addFn m hm) n` | `theorem add_eq (m n : U) (hm : m ∈ (ω : U)) : add m n = apply (addFn m hm) n` |
| `add_in_Omega` | `add m n ∈ ω` para m, n ∈ ω | `theorem add_in_Omega (m n : U) (hm : m ∈ (ω : U)) (hn : n ∈ (ω : U)) : add m n ∈ ω` |

#### Sección 3: Ecuaciones de recursión

| Nombre | Descripción matemática | Firma Lean4 |
|--------|----------------------|-------------|
| `add_zero` | m + ∅ = m (identidad derecha del cero) | `theorem add_zero (m : U) (hm : m ∈ (ω : U)) : add m ∅ = m` |
| `add_succ` | m + σ n = σ(m + n) | `theorem add_succ (m n : U) (hm : m ∈ (ω : U)) (hn : n ∈ (ω : U)) : add m (σ n) = σ (add m n)` |

#### Sección 4: Teorema puente

| Nombre | Descripción matemática | Firma Lean4 |
|--------|----------------------|-------------|
| `fromPeano_add` | `fromPeano(p + q) = add(fromPeano p)(fromPeano q)` | `theorem fromPeano_add (p q : Peano.ℕ₀) : (fromPeano (Peano.Add.add p q) : U) = add (fromPeano p) (fromPeano q)` |

**Descripción**: Demostrado por inducción sobre q. Caso base usa `add_zero`; paso inductivo usa `add_succ` y `succFn_apply`. Permite transportar automáticamente todos los teoremas de `PeanoNatAdd`.

**Dependencias**: `add_zero`, `add_succ`, `fromPeano`, `Nat_in_Omega`, `fromPeano_is_nat`, `succ`

#### Sección 5: Propiedades algebraicas

| Nombre | Descripción matemática | Firma Lean4 |
|--------|----------------------|-------------|
| `zero_add` | ∅ + n = n (identidad izquierda) | `theorem zero_add (n : U) (hn : n ∈ (ω : U)) : add ∅ n = n` |
| `add_comm_Omega` | m + n = n + m (conmutatividad) | `theorem add_comm_Omega (m n : U) (hm : m ∈ (ω : U)) (hn : n ∈ (ω : U)) : add m n = add n m` |
| `add_assoc_Omega` | (m + n) + k = m + (n + k) (asociatividad) | `theorem add_assoc_Omega (m n k : U) (hm : m ∈ (ω : U)) (hn : n ∈ (ω : U)) (hk : k ∈ (ω : U)) : add (add m n) k = add m (add n k)` |

#### Sección 6: Propiedades adicionales

| Nombre | Descripción matemática | Firma Lean4 |
|--------|----------------------|-------------|
| `succ_add_Omega` | σ m + n = σ(m + n) | `theorem succ_add_Omega (m n : U) (hm : m ∈ (ω : U)) (hn : n ∈ (ω : U)) : add (σ m) n = σ (add m n)` |
| `add_left_cancel_Omega` | m + n = m + k → n = k (cancelación izquierda) | `theorem add_left_cancel_Omega (m n k : U) (hm : m ∈ (ω : U)) (hn : n ∈ (ω : U)) (hk : k ∈ (ω : U)) (h : add m n = add m k) : n = k` |
| `add_right_cancel_Omega` | n + m = k + m → n = k (cancelación derecha) | `theorem add_right_cancel_Omega (m n k : U) (hm : m ∈ (ω : U)) (hn : n ∈ (ω : U)) (hk : k ∈ (ω : U)) (h : add n m = add k m) : n = k` |
| `add_pos_left_Omega` | m ≠ ∅ → n ∈ add n m (n < n + m cuando m > 0) | `theorem add_pos_left_Omega (m n : U) (hm : m ∈ (ω : U)) (hn : n ∈ (ω : U)) (hm_ne : m ≠ ∅) : n ∈ add n m` |
| `le_then_exists_add_Omega` | m ≤ n → ∃ k ∈ ω, n = m + k | `theorem le_then_exists_add_Omega (m n : U) (hm : m ∈ (ω : U)) (hn : n ∈ (ω : U)) (h : m ∈ n ∨ m = n) : ∃ k, k ∈ (ω : U) ∧ n = add m k` |
| `add_lt_of_lt_Omega` | n ∈ k → m + n ∈ m + k (monotonía estricta) | `theorem add_lt_of_lt_Omega (m n k : U) (hm : m ∈ (ω : U)) (hn : n ∈ (ω : U)) (hk : k ∈ (ω : U)) (h : n ∈ k) : add m n ∈ add m k` |

**Patrón de demostración**: Para todos los teoremas de secciones 5 y 6: `fromPeano_surjective` + `subst` normaliza a `fromPeano p/q/r`, luego `fromPeano_add` convierte entre ZFC y Peano, luego `congrArg fromPeano (Peano.Add.teorema ...)` cierra el objetivo.

**Dependencias para Sección 6**: `fromPeano_surjective`, `fromPeano_add`, `fromPeano_lt_iff`, `fromPeano_le_iff`, `fromPeano_injective`, `Peano.Add.add_cancelation`, `Peano.Add.lt_self_add_r`, `Peano.Add.le_then_exists_add`, `Peano.Add.add_lt_add_left_iff`, `Nat_in_Omega`, `fromPeano_is_nat`

---

### 4.20 Nat.Mul.lean

**Módulo**: `ZfcSetTheory.Nat.Mul`
**Namespace**: `ZFC.Nat.Mul`
**Actualizado**: 2026-03-08 12:00

**Importancia por sección**:

- Sección 1 (mulFn/mul): medium — infraestructura recursiva
- Sección 2 (ecuaciones de recursión): high — definición recursiva fundamental (mul_zero, mul_succ)
- Sección 3 (teorema puente): high — fromPeano_mul, clave para transporte
- Sección 4 (propiedades algebraicas): high — conmutatividad, asociatividad, distributividad

#### Sección 1: mulFn y mul

| Nombre | Descripción matemática | Firma Lean4 |
|--------|----------------------|-------------|
| `mulFn_is_function` | `mulFn m hm` es función de ω en ω | `theorem mulFn_is_function (m : U) (hm : m ∈ (ω : U)) : IsFunction (mulFn m hm) ω ω` |
| `mul_eq` | Si m ∈ ω, `mul m n = apply (mulFn m hm) n` | `theorem mul_eq (m n : U) (hm : m ∈ (ω : U)) : mul m n = apply (mulFn m hm) n` |
| `mul_in_Omega` | `mul m n ∈ ω` para m, n ∈ ω | `theorem mul_in_Omega (m n : U) (hm : m ∈ (ω : U)) (hn : n ∈ (ω : U)) : mul m n ∈ ω` |

#### Sección 2: Ecuaciones de recursión

| Nombre | Descripción matemática | Firma Lean4 |
|--------|----------------------|-------------|
| `mul_zero` | m · ∅ = ∅ (aniquilador derecho) | `theorem mul_zero (m : U) (hm : m ∈ (ω : U)) : mul m ∅ = ∅` |
| `mul_succ` | m · σ n = m + m · n | `theorem mul_succ (m n : U) (hm : m ∈ (ω : U)) (hn : n ∈ (ω : U)) : mul m (σ n) = add m (mul m n)` |

**Nota sobre `mul_succ`**: El orden es `m + m·n` (no `m·n + m` como en Peano). La diferencia se resuelve con `add_comm_Omega` en el teorema puente.

#### Sección 3: Teorema puente

| Nombre | Descripción matemática | Firma Lean4 |
|--------|----------------------|-------------|
| `fromPeano_mul` | `fromPeano(p · q) = mul(fromPeano p)(fromPeano q)` | `theorem fromPeano_mul (p q : Peano.ℕ₀) : (fromPeano (Peano.Mul.mul p q) : U) = mul (fromPeano p) (fromPeano q)` |

**Descripción**: Demostrado por inducción sobre q. Caso base usa `mul_zero`; paso inductivo usa `mul_succ`, `fromPeano_add`, y `add_comm_Omega` (necesaria porque Peano da `(p·q') + p` mientras ZFC da `p + (p·q')`).

**Dependencias**: `mul_zero`, `mul_succ`, `fromPeano_add`, `add_comm_Omega`, `mul_in_Omega`, `fromPeano`, `Nat_in_Omega`, `fromPeano_is_nat`, `Peano.Mul.mul_zero`, `Peano.Mul.mul_succ`

#### Sección 4: Propiedades algebraicas

| Nombre | Descripción matemática | Firma Lean4 |
|--------|----------------------|-------------|
| `zero_mul_Omega` | ∅ · n = ∅ (aniquilador izquierdo) | `theorem zero_mul_Omega (n : U) (hn : n ∈ (ω : U)) : mul ∅ n = ∅` |
| `mul_comm_Omega` | m · n = n · m (conmutatividad) | `theorem mul_comm_Omega (m n : U) (hm : m ∈ (ω : U)) (hn : n ∈ (ω : U)) : mul m n = mul n m` |
| `succ_mul_Omega` | σ m · n = m · n + n | `theorem succ_mul_Omega (m n : U) (hm : m ∈ (ω : U)) (hn : n ∈ (ω : U)) : mul (σ m) n = add (mul m n) n` |
| `mul_one_Omega` | m · σ ∅ = m (identidad derecha) | `theorem mul_one_Omega (m : U) (hm : m ∈ (ω : U)) : mul m (σ (∅ : U)) = m` |
| `one_mul_Omega` | σ ∅ · m = m (identidad izquierda) | `theorem one_mul_Omega (m : U) (hm : m ∈ (ω : U)) : mul (σ (∅ : U)) m = m` |
| `mul_assoc_Omega` | (m · n) · k = m · (n · k) (asociatividad) | `theorem mul_assoc_Omega (m n k : U) (hm : m ∈ (ω : U)) (hn : n ∈ (ω : U)) (hk : k ∈ (ω : U)) : mul (mul m n) k = mul m (mul n k)` |
| `mul_ldistr_Omega` | m · (n + k) = m · n + m · k (distributividad izquierda) | `theorem mul_ldistr_Omega (m n k : U) (hm : m ∈ (ω : U)) (hn : n ∈ (ω : U)) (hk : k ∈ (ω : U)) : mul m (add n k) = add (mul m n) (mul m k)` |
| `mul_rdistr_Omega` | (m + n) · k = m · k + n · k (distributividad derecha) | `theorem mul_rdistr_Omega (m n k : U) (hm : m ∈ (ω : U)) (hn : n ∈ (ω : U)) (hk : k ∈ (ω : U)) : mul (add m n) k = add (mul m k) (mul n k)` |

**Patrón de demostración**: Igual que en Nat.Add: `fromPeano_surjective` + `subst` + `fromPeano_mul`/`fromPeano_add` + `congrArg fromPeano (Peano.Mul.teorema ...)`.

**Dependencias para Sección 4**: `fromPeano_surjective`, `fromPeano_mul`, `fromPeano_add`, `Peano.Mul.zero_mul`, `Peano.Mul.mul_comm`, `Peano.Mul.succ_mul`, `Peano.Mul.mul_one`, `Peano.Mul.one_mul`, `Peano.Mul.mul_assoc`, `Peano.Mul.mul_ldistr`, `Peano.Mul.mul_rdistr`, `Nat_in_Omega`, `fromPeano_is_nat`

---

### 4.21 Nat.Sub.lean

**Módulo**: `ZfcSetTheory.Nat.Sub`
**Namespace**: `ZFC.Nat.Sub`
**Actualizado**: 2026-03-21

**Importancia por sección**:

- Sección 0 (predecessorFn): medium — infraestructura
- Sección 1 (subFn/sub): medium — infraestructura recursiva
- Sección 2 (ecuaciones de recursión): high — definición recursiva fundamental (sub_zero, sub_succ)
- Sección 4 (teorema puente): high — fromPeano_sub, clave para transporte
- Sección 5 (propiedades algebraicas): high — cancelación, positividad, sub_self

#### Sección 0: predecessorFn

| Nombre | Descripción matemática | Firma Lean4 |
|--------|----------------------|-------------|
| `mem_predecessorFn` | `⟨n, predecessor n⟩ ∈ predecessorFn` para n ∈ ω | `theorem mem_predecessorFn (n : U) (hn : n ∈ (ω : U)) : (⟨n, predecessor n⟩ : U) ∈ (predecessorFn : U)` |
| `predecessorFn_is_function` | `predecessorFn` es función de ω en ω | `theorem predecessorFn_is_function : IsFunction (predecessorFn : U) ω ω` |
| `predecessorFn_apply` | Aplicar `predecessorFn` a n ∈ ω da `predecessor n` | `theorem predecessorFn_apply (n : U) (hn : n ∈ (ω : U)) : apply (predecessorFn : U) n = predecessor n` |

#### Sección 1: subFn y sub

| Nombre | Descripción matemática | Firma Lean4 |
|--------|----------------------|-------------|
| `subFn_is_function` | `subFn m hm` es función de ω en ω | `theorem subFn_is_function (m : U) (hm : m ∈ (ω : U)) : IsFunction (subFn m hm) ω ω` |
| `sub_eq` | Si m ∈ ω, `sub m n = apply (subFn m hm) n` | `theorem sub_eq (m n : U) (hm : m ∈ (ω : U)) : sub m n = apply (subFn m hm) n` |
| `sub_in_Omega` | `sub m n ∈ ω` para m, n ∈ ω | `theorem sub_in_Omega (m n : U) (hm : m ∈ (ω : U)) (hn : n ∈ (ω : U)) : sub m n ∈ ω` |

#### Sección 2: Ecuaciones de recursión

| Nombre | Descripción matemática | Firma Lean4 |
|--------|----------------------|-------------|
| `sub_zero` | m - ∅ = m (identidad derecha) | `theorem sub_zero (m : U) (hm : m ∈ (ω : U)) : sub m ∅ = m` |
| `sub_succ` | m - σ n = predecessor (m - n) | `theorem sub_succ (m n : U) (hm : m ∈ (ω : U)) (hn : n ∈ (ω : U)) : sub m (σ n) = predecessor (sub m n)` |

**Nota sobre `sub_succ`**: La saturación en ∅ se garantiza automáticamente porque `predecessor ∅ = ∅`.

#### Sección 4: Teorema puente

| Nombre | Descripción matemática | Firma Lean4 |
|--------|----------------------|-------------|
| `fromPeano_sub` | `fromPeano(p - q) = sub(fromPeano p)(fromPeano q)` | `theorem fromPeano_sub (p q : Peano.ℕ₀) : (fromPeano (Peano.Sub.sub p q) : U) = sub (fromPeano p) (fromPeano q)` |

**Descripción**: Demostrado por inducción sobre q. Usa el lema privado `peano_sub_succ_tau : Peano.Sub.sub p (σ q) = Peano.τ (Peano.Sub.sub p q)` (válido incondicionalmente: cuando σq ≤ p usa `succ_sub`; cuando σq > p ambos lados son 0) y `predecessor_fromPeano_eq_tau : predecessor (fromPeano x) = fromPeano (τ x)`.

**Dependencias**: `sub_zero`, `sub_succ`, `predecessor_fromPeano_eq_tau`, `Nat_in_Omega`, `fromPeano_is_nat`, `Peano.Sub.succ_sub`, `Peano.Sub.sub_self`, `Peano.Order.nle_then_gt_wp`, `Peano.Order.lt_succ_iff_le`, `Peano.Order.le_antisymm`, `predecessor_of_succ`

#### Sección 5: Propiedades algebraicas

| Nombre | Descripción matemática | Firma Lean4 |
|--------|----------------------|-------------|
| `zero_sub_Omega` | ∅ - n = ∅ (sustraer de cero siempre da cero) | `theorem zero_sub_Omega (n : U) (hn : n ∈ (ω : U)) : sub ∅ n = ∅` |
| `sub_self_Omega` | m - m = ∅ (todo natural menos sí mismo es cero) | `theorem sub_self_Omega (m : U) (hm : m ∈ (ω : U)) : sub m m = ∅` |
| `sub_succ_succ_Omega` | σm - σn = m - n (cancelar sucesores) | `theorem sub_succ_succ_Omega (m n : U) (hm : m ∈ (ω : U)) (hn : n ∈ (ω : U)) : sub (σ m) (σ n) = sub m n` |
| `sub_k_add_k_Omega` | (m + n) - n = m (substraer lo sumado cancela) | `theorem sub_k_add_k_Omega (m n : U) (hm : m ∈ (ω : U)) (hn : n ∈ (ω : U)) : sub (add m n) n = m` |
| `add_k_sub_k_Omega` | n ≤ m → (m - n) + n = m (sumar lo restado recupera) | `theorem add_k_sub_k_Omega (m n : U) (hm : m ∈ (ω : U)) (hn : n ∈ (ω : U)) (h_le : n ∈ m ∨ n = m) : add (sub m n) n = m` |
| `sub_le_self_Omega` | m - n ≤ m (la sustracción no excede el minuendo) | `theorem sub_le_self_Omega (m n : U) (hm : m ∈ (ω : U)) (hn : n ∈ (ω : U)) : sub m n ∈ m ∨ sub m n = m` |
| `sub_pos_iff_lt_Omega` | m - n ≠ ∅ ↔ n ∈ m (positivo iff estrictamente menor) | `theorem sub_pos_iff_lt_Omega (m n : U) (hm : m ∈ (ω : U)) (hn : n ∈ (ω : U)) : sub m n ≠ ∅ ↔ n ∈ m` |

**Patrón de demostración**: `fromPeano_surjective` + `subst` + `fromPeano_sub`/`fromPeano_add` + `congrArg fromPeano (Peano.Sub.teorema ...)`.

**Dependencias para Sección 5**: `fromPeano_surjective`, `fromPeano_sub`, `fromPeano_add`, `fromPeano_le_iff`, `fromPeano_lt_iff`, `fromPeano_injective`, `Peano.Sub.sub_le_self`, `Peano.Sub.sub_self`, `Peano.Sub.sub_succ_succ_eq`, `Peano.Sub.sub_k_add_k`, `Peano.Sub.add_k_sub_k`, `Peano.Sub.sub_pos_iff_lt`, `Peano.Sub.lt_b_a_then_sub_a_b_neq_0`, `Peano.Order.zero_le`, `Peano.Order.le_zero_eq`, `Peano.Order.succ_le_succ_iff`, `Nat_in_Omega`, `fromPeano_is_nat`

---

### 4.22 Nat.Div.lean

**Módulo**: `ZfcSetTheory.Nat.Div`
**Namespace**: `ZFC.Nat.Div`
**Actualizado**: 2026-03-21

**Importancia por sección**:

- Sección 1 (clausura en ω): medium — infraestructura
- Sección 2 (teoremas puente): high — fromPeano_div, fromPeano_mod
- Sección 3 (propiedades algebraicas): high — divMod_eq, mod_lt_divisor, div/mod_of_lt

#### Sección 1: Clausura en ω

| Nombre | Descripción matemática | Firma Lean4 |
|--------|----------------------|-------------|
| `divOf_in_Omega` | `divOf m n ∈ ω` para m, n ∈ ω | `theorem divOf_in_Omega (m n : U) (hm : m ∈ (ω : U)) (hn : n ∈ (ω : U)) : divOf m n ∈ ω` |
| `modOf_in_Omega` | `modOf m n ∈ ω` para m, n ∈ ω | `theorem modOf_in_Omega (m n : U) (hm : m ∈ (ω : U)) (hn : n ∈ (ω : U)) : modOf m n ∈ ω` |

#### Sección 2: Teoremas puente

| Nombre | Descripción matemática | Firma Lean4 |
|--------|----------------------|-------------|
| `fromPeano_div` | `fromPeano (div p q) = divOf (fromPeano p) (fromPeano q)` | `theorem fromPeano_div (p q : Peano.ℕ₀) : (fromPeano (Peano.Div.div p q) : U) = divOf (fromPeano p) (fromPeano q)` |
| `fromPeano_mod` | `fromPeano (mod p q) = modOf (fromPeano p) (fromPeano q)` | `theorem fromPeano_mod (p q : Peano.ℕ₀) : (fromPeano (Peano.Div.mod p q) : U) = modOf (fromPeano p) (fromPeano q)` |

**Descripción**: Demostrados con `simp only [divOf/modOf, dif_pos ...]` + `congr 1; congr 1` para aislar los argumentos de `toPeano`, luego `toPeano_proof_irrel` (para cambiar el testigo de `IsNat`) y `toPeano_fromPeano` (para simplificar `toPeano (fromPeano p) _ = p`).

#### Sección 3: Propiedades algebraicas

| Nombre | Descripción matemática | Firma Lean4 |
|--------|----------------------|-------------|
| `divMod_eq_Omega` | n ≠ ∅ → m = (divOf m n) · n + modOf m n | `theorem divMod_eq_Omega (m n : U) (hm : m ∈ (ω : U)) (hn : n ∈ (ω : U)) (h_n_neq_zero : n ≠ ∅) : m = add (mul (divOf m n) n) (modOf m n)` |
| `mod_lt_divisor_Omega` | n ≠ ∅ → modOf m n ∈ n (resto estrictamente menor que divisor) | `theorem mod_lt_divisor_Omega (m n : U) (hm : m ∈ (ω : U)) (hn : n ∈ (ω : U)) (h_n_neq_zero : n ≠ ∅) : modOf m n ∈ n` |
| `div_of_lt_Omega` | m ∈ n → divOf m n = ∅ (dividendo < divisor ⟹ cociente = 0) | `theorem div_of_lt_Omega (m n : U) (hm : m ∈ (ω : U)) (hn : n ∈ (ω : U)) (h_lt : m ∈ n) : divOf m n = ∅` |
| `mod_of_lt_Omega` | m ∈ n → modOf m n = m (dividendo < divisor ⟹ resto = dividendo) | `theorem mod_of_lt_Omega (m n : U) (hm : m ∈ (ω : U)) (hn : n ∈ (ω : U)) (h_lt : m ∈ n) : modOf m n = m` |
| `div_le_self_Omega` | n ≠ ∅ → divOf m n ∈ m ∨ divOf m n = m (cociente ≤ dividendo) | `theorem div_le_self_Omega (m n : U) (hm : m ∈ (ω : U)) (hn : n ∈ (ω : U)) (h_n_neq_zero : n ≠ ∅) : divOf m n ∈ m ∨ divOf m n = m` |

**Patrón de demostración**: `fromPeano_surjective` + `subst` + `fromPeano_div`/`fromPeano_mod`/`fromPeano_mul`/`fromPeano_add` + teoremas de `Peano.Div`.

**Dependencias**: `fromPeano_surjective`, `fromPeano_div`, `fromPeano_mod`, `fromPeano_mul`, `fromPeano_add`, `fromPeano_lt_iff`, `fromPeano_le_iff`, `fromPeano_injective`, `fromPeano_zero_is_empty` (privado), `toPeano_fromPeano`, `isNat_zero`, `Peano.Div.divMod_eq`, `Peano.Div.mod_lt_divisor`, `Peano.Div.div_of_lt`, `Peano.Div.mod_of_lt`, `Peano.Div.div_le_self`, `Nat_in_Omega`, `fromPeano_is_nat`

---

### 4.23 Nat.Pow.lean

**Importancia por grupo**:

- Infraestructura (powFn_is_function, pow_eq, pow_in_Omega): medium
- Ecuaciones de recursión (pow_zero, pow_succ): high — definición recursiva fundamental
- Teorema puente (fromPeano_pow): high — clave para transporte
- Propiedades algebraicas (pow_add_eq_mul_pow, mul_pow, pow_pow_eq_pow_mul): high — leyes de exponentes
- Propiedades básicas (zero_pow, one_pow, pow_one, pow_ne_zero, pow_two): medium

| Teorema | Enunciado Matemático | Firma Lean4 |
|---------|---------------------|-------------|
| `powFn_is_function` | powFn m es función ω → ω | `theorem powFn_is_function (m : U) (hm : m ∈ (ω : U)) : IsFunction (powFn m hm) ω ω` |
| `pow_eq` | pow m n = powFn m ⦅n⦆ (para m ∈ ω) | `theorem pow_eq (m n : U) (hm : m ∈ (ω : U)) : pow m n = apply (powFn m hm) n` |
| `pow_in_Omega` | m, n ∈ ω → pow m n ∈ ω | `theorem pow_in_Omega (m n : U) (hm : m ∈ (ω : U)) (hn : n ∈ (ω : U)) : pow m n ∈ (ω : U)` |
| `pow_zero` | m⁰ = 1 | `theorem pow_zero (m : U) (hm : m ∈ (ω : U)) : pow m ∅ = σ ∅` |
| `pow_succ` | m^(σ n) = m * mⁿ | `theorem pow_succ (m n : U) (hm : m ∈ (ω : U)) (hn : n ∈ (ω : U)) : pow m (σ n) = mul m (pow m n)` |
| `fromPeano_pow` | Puente: fromPeano(p^q) = pow(fromPeano p)(fromPeano q) | `theorem fromPeano_pow (p q : Peano.ℕ₀) : (fromPeano (Peano.Pow.pow p q) : U) = pow (fromPeano p) (fromPeano q)` |
| `zero_pow_Omega` | 0^n = 0 para n ≠ 0 | `theorem zero_pow_Omega (n : U) (hn : n ∈ (ω : U)) (hn_ne : n ≠ ∅) : pow ∅ n = ∅` |
| `one_pow_Omega` | 1^n = 1 | `theorem one_pow_Omega (n : U) (hn : n ∈ (ω : U)) : pow (σ ∅) n = σ ∅` |
| `pow_one_Omega` | m^1 = m | `theorem pow_one_Omega (m : U) (hm : m ∈ (ω : U)) : pow m (σ ∅) = m` |
| `pow_ne_zero_Omega` | m ≠ 0 → m^n ≠ 0 | `theorem pow_ne_zero_Omega {m : U} (hm : m ∈ (ω : U)) (hm_ne : m ≠ ∅) (n : U) (hn : n ∈ (ω : U)) : pow m n ≠ ∅` |
| `pow_two_Omega` | m² = m * m | `theorem pow_two_Omega (m : U) (hm : m ∈ (ω : U)) : pow m (σ (σ ∅)) = mul m m` |
| `pow_add_eq_mul_pow_Omega` | m^(n+k) = m^n * m^k | `theorem pow_add_eq_mul_pow_Omega (m n k : U) (...) : pow m (add n k) = mul (pow m n) (pow m k)` |
| `mul_pow_Omega` | (m*n)^k = m^k* n^k | `theorem mul_pow_Omega (m n k : U) (...) : pow (mul m n) k = mul (pow m k) (pow n k)` |
| `pow_pow_eq_pow_mul_Omega` | (m^n)^k = m^(n*k) | `theorem pow_pow_eq_pow_mul_Omega (m n k : U) (...) : pow (pow m n) k = pow m (mul n k)` |

**Dependencias**: `RecursiveFn_zero`, `RecursiveFn_succ`, `fromPeano_pow`, `fromPeano_mul`, `Peano.Pow.*`, `mul_in_Omega`, `mul_comm_Omega`, `mul_assoc_Omega`

---

### 4.24 Nat.Arith.lean

**Importancia por sección**:

- Sección 0-2 (divisibilidad): high — teoría de divisibilidad completa (reflexividad, transitividad, antisimetría)
- Sección 2.5 (div/mod nativos ZFC): medium — implementación alternativa con divModFn
- Sección 3-6 (gcdOf, lcmOf, Bézout): high — teoría de números: MCD, MCM e identidad de Bézout

#### Sección 0-2: Divisibilidad

| Teorema | Enunciado Matemático | Firma Lean4 |
|---------|---------------------|-------------|
| `fromPeano_divides` | Puente: Peano.Divides p q ↔ divides(fromPeano p)(fromPeano q) | `theorem fromPeano_divides (p q : Peano.ℕ₀) : Peano.Arith.Divides p q ↔ divides (fromPeano p : U) (fromPeano q)` |
| `divides_refl_Omega` | m ∣ m | `theorem divides_refl_Omega (m : U) (hm : m ∈ (ω : U)) : divides m m` |
| `one_divides_Omega` | 1 ∣ m | `theorem one_divides_Omega (m : U) (hm : m ∈ (ω : U)) : divides (σ ∅) m` |
| `divides_zero_Omega` | m ∣ 0 | `theorem divides_zero_Omega (m : U) (hm : m ∈ (ω : U)) : divides m ∅` |
| `zero_divides_iff_Omega` | 0 ∣ n ↔ n = 0 | `theorem zero_divides_iff_Omega (n : U) (hn : n ∈ (ω : U)) : divides ∅ n ↔ n = ∅` |
| `divides_trans_Omega` | m ∣ n ∧ n ∣ k → m ∣ k | `theorem divides_trans_Omega (m n k : U) (hm hn hk) : divides m n → divides n k → divides m k` |
| `divides_mul_right_Omega` | m ∣ n → m ∣ n*k | `theorem divides_mul_right_Omega (m n k : U) (hm hn hk) : divides m n → divides m (mul n k)` |
| `divides_mul_left_Omega` | m ∣ n → m ∣ k*n | `theorem divides_mul_left_Omega (m n k : U) (hm hn hk) : divides m n → divides m (mul k n)` |
| `divides_add_Omega` | m ∣ n ∧ m ∣ k → m ∣ n+k | `theorem divides_add_Omega (m n k : U) (hm hn hk) : divides m n → divides m k → divides m (add n k)` |
| `divides_sub_Omega` | n < m ∧ k ∣ m ∧ k ∣ n → k ∣ m−n | `theorem divides_sub_Omega (m n k : U) (hm hn hk) (h_lt : n ∈ m) (hdm hdm) : divides k (sub m n)` |
| `divides_modOf_Omega` | k ∣ m ∧ k ∣ n → k ∣ (m mod n) | `theorem divides_modOf_Omega (m n k : U) (hm hn hk) (hdm hdn) : divides k (modOf m n)` |
| `divides_le_Omega` | m ∣ n ∧ n ≠ 0 → m ≤ n | `theorem divides_le_Omega (m n : U) (hm hn) : divides m n → n ≠ ∅ → m ∈ n ∨ m = n` |
| `antisymm_divides_Omega` | m ∣ n ∧ n ∣ m → m = n | `theorem antisymm_divides_Omega (m n : U) (hm hn) : divides m n → divides n m → m = n` |

#### Sección 2.5: div/mod nativos ZFC

| Teorema | Enunciado Matemático | Firma Lean4 |
|---------|---------------------|-------------|
| `div_eq` | div m n = fst(divModFn n ⦅m⦆) | `theorem div_eq (m n : U) (hm : m ∈ (ω : U)) (hn : n ∈ (ω : U)) : div m n = fst (apply (divModFn n hn) m)` |
| `mod_eq` | mod m n = snd(divModFn n ⦅m⦆) | `theorem mod_eq (m n : U) (hm hn) : mod m n = snd (apply (divModFn n hn) m)` |
| `div_in_Omega` | div m n ∈ ω | `theorem div_in_Omega (m n : U) (hm hn) : div m n ∈ (ω : U)` |
| `mod_in_Omega` | mod m n ∈ ω | `theorem mod_in_Omega (m n : U) (hm hn) : mod m n ∈ (ω : U)` |
| `div_zero_left` | div 0 n = 0 | `theorem div_zero_left (n : U) (hn : n ∈ (ω : U)) : div ∅ n = ∅` |
| `mod_zero_left` | mod 0 n = 0 | `theorem mod_zero_left (n : U) (hn : n ∈ (ω : U)) : mod ∅ n = ∅` |
| `div_succ_wrap` | σ(mod m n) = n → div(σ m) n = σ(div m n) | `theorem div_succ_wrap (m n : U) (hm hn) (h : σ (mod m n) = n) : div (σ m) n = σ (div m n)` |
| `mod_succ_wrap` | σ(mod m n) = n → mod(σ m) n = 0 | `theorem mod_succ_wrap (m n : U) (hm hn) (h : σ (mod m n) = n) : mod (σ m) n = ∅` |
| `div_succ_continue` | σ(mod m n) ≠ n → div(σ m) n = div m n | `theorem div_succ_continue (m n : U) (hm hn) (h : σ (mod m n) ≠ n) : div (σ m) n = div m n` |
| `mod_succ_continue` | σ(mod m n) ≠ n → mod(σ m) n = σ(mod m n) | `theorem mod_succ_continue (m n : U) (hm hn) (h : σ (mod m n) ≠ n) : mod (σ m) n = σ (mod m n)` |
| `divMod_eq_ZFC` | n ≠ 0 → m = div(m,n)*n + mod(m,n) | `theorem divMod_eq_ZFC (m n : U) (hm hn) (h : n ≠ ∅) : m = add (mul (div m n) n) (mod m n)` |
| `mod_lt_divisor_ZFC` | n ≠ 0 → mod m n ∈ n | `theorem mod_lt_divisor_ZFC (m n : U) (hm hn) (h : n ≠ ∅) : mod m n ∈ n` |
| `div_eq_divOf` | n ≠ 0 → div m n = divOf m n | `theorem div_eq_divOf (m n : U) (hm hn) (h_pos : n ≠ ∅) : div m n = divOf m n` |
| `mod_eq_modOf` | n ≠ 0 → mod m n = modOf m n | `theorem mod_eq_modOf (m n : U) (hm hn) (h_pos : n ≠ ∅) : mod m n = modOf m n` |

#### Sección 3-6: gcdOf, lcmOf, Bézout

| Teorema | Enunciado Matemático | Firma Lean4 |
|---------|---------------------|-------------|
| `gcdOf_in_Omega` | gcdOf m n ∈ ω | `theorem gcdOf_in_Omega (m n : U) (hm hn) : gcdOf m n ∈ (ω : U)` |
| `lcmOf_in_Omega` | lcmOf m n ∈ ω | `theorem lcmOf_in_Omega (m n : U) (hm hn) : lcmOf m n ∈ (ω : U)` |
| `fromPeano_gcd` | Puente: fromPeano(gcd p q) = gcdOf(fromPeano p)(fromPeano q) | `theorem fromPeano_gcd (p q : Peano.ℕ₀) : (fromPeano (Peano.Arith.gcd p q) : U) = gcdOf (fromPeano p) (fromPeano q)` |
| `fromPeano_lcm` | Puente: fromPeano(lcm p q) = lcmOf(fromPeano p)(fromPeano q) | `theorem fromPeano_lcm (p q : Peano.ℕ₀) : (fromPeano (Peano.Arith.lcm p q) : U) = lcmOf (fromPeano p) (fromPeano q)` |
| `gcdOf_divides_left_Omega` | gcd(m,n) ∣ m | `theorem gcdOf_divides_left_Omega (m n : U) (hm hn) : divides (gcdOf m n) m` |
| `gcdOf_divides_right_Omega` | gcd(m,n) ∣ n | `theorem gcdOf_divides_right_Omega (m n : U) (hm hn) : divides (gcdOf m n) n` |
| `gcdOf_greatest_Omega` | k ∣ m ∧ k ∣ n → k ∣ gcd(m,n) | `theorem gcdOf_greatest_Omega (m n k : U) (hm hn hk) : divides k m → divides k n → divides k (gcdOf m n)` |
| `gcdOf_comm_Omega` | gcd(m,n) = gcd(n,m) | `theorem gcdOf_comm_Omega (m n : U) (hm hn) : gcdOf m n = gcdOf n m` |
| `lcmOf_multiple_left_Omega` | m ∣ lcm(m,n) | `theorem lcmOf_multiple_left_Omega (m n : U) (hm hn) : divides m (lcmOf m n)` |
| `lcmOf_multiple_right_Omega` | n ∣ lcm(m,n) | `theorem lcmOf_multiple_right_Omega (m n : U) (hm hn) : divides n (lcmOf m n)` |
| `lcmOf_comm_Omega` | lcm(m,n) = lcm(n,m) | `theorem lcmOf_comm_Omega (m n : U) (hm hn) : lcmOf m n = lcmOf n m` |
| `bezout_natform_Omega` | ∃ a b, a*m − b*n = gcd(m,n) ∨ a*n − b*m = gcd(m,n) | `theorem bezout_natform_Omega (m n : U) (hm hn) : ∃ mp np : U, (mp ∈ ω ∧ np ∈ ω) ∧ (sub (mul mp m) (mul np n) = gcdOf m n ∨ sub (mul np n) (mul mp m) = gcdOf m n)` |

**Dependencias**: `fromPeano_surjective`, `fromPeano_injective`, `fromPeano_mul`, `fromPeano_add`, `fromPeano_sub`, `fromPeano_mod`, `fromPeano_le_iff`, `fromPeano_lt_iff`, `Peano.Arith.*`, `divides`, `mul`, `add`, `sub`, `modOf`, `gcdOf`, `lcmOf`

### 4.25 Nat.Factorial.lean

**Módulo**: `ZfcSetTheory.Nat.Factorial`
**Namespace**: `ZFC.Nat.Factorial`
**Actualizado**: 2026-03-24

**Importancia por sección**:

- Sección 1 (clausura en ω): medium — infraestructura
- Sección 2 (teorema puente): high — fromPeano_factorial
- Sección 3 (valores concretos y recursión): high — factorial_zero, factorial_succ
- Sección 4 (positividad y cotas): medium — factorialOf_ne_zero, monotonía

#### Sección 1: Clausura en ω

| Nombre | Descripción matemática | Firma Lean4 |
|--------|----------------------|-------------|
| `factorialOf_in_Omega` | `factorialOf n ∈ ω` para n ∈ ω | `theorem factorialOf_in_Omega (n : U) (hn : n ∈ (ω : U)) : factorialOf n ∈ (ω : U)` |

#### Sección 2: Teorema puente

| Nombre | Descripción matemática | Firma Lean4 |
|--------|----------------------|-------------|
| `fromPeano_factorial` | `fromPeano (factorial p) = factorialOf (fromPeano p)` | `theorem fromPeano_factorial (p : Peano.ℕ₀) : (fromPeano (Peano.Factorial.factorial p) : U) = factorialOf (fromPeano p)` |

**Descripción**: Demostrado con `simp only [factorialOf, dif_pos ...]` + `congrArg` para aislar los argumentos de `toPeano`, luego `toPeano_proof_irrel` y `toPeano_fromPeano`.

#### Sección 3: Valores concretos y ecuación de recursión

| Nombre | Descripción matemática | Firma Lean4 |
|--------|----------------------|-------------|
| `factorialOf_zero` | 0! = 1 | `theorem factorialOf_zero : factorialOf (∅ : U) = σ (∅ : U)` |
| `factorialOf_succ` | (σ n)! = n! · (σ n) | `theorem factorialOf_succ (n : U) (hn : n ∈ (ω : U)) : factorialOf (Nat.Basic.succ n) = mul (factorialOf n) (Nat.Basic.succ n)` |
| `factorialOf_one` | 1! = 1 | `theorem factorialOf_one : factorialOf (σ (∅ : U)) = σ (∅ : U)` |
| `factorialOf_two` | 2! = 2 | `theorem factorialOf_two : factorialOf (σ (σ (∅ : U))) = σ (σ (∅ : U))` |

#### Sección 4: Positividad y cotas

| Nombre | Descripción matemática | Firma Lean4 |
|--------|----------------------|-------------|
| `factorialOf_ne_zero` | n! ≠ 0 | `theorem factorialOf_ne_zero (n : U) (hn : n ∈ (ω : U)) : factorialOf n ≠ ∅` |
| `factorialOf_pos` | 0 < n! (i.e. ∅ ∈ n!) | `theorem factorialOf_pos (n : U) (hn : n ∈ (ω : U)) : (∅ : U) ∈ factorialOf n` |
| `factorialOf_ge_one` | 1 ≤ n! (i.e. σ ∅ ∈ n! ∨ σ ∅ = n!) | `theorem factorialOf_ge_one (n : U) (hn : n ∈ (ω : U)) : σ (∅ : U) ∈ factorialOf n ∨ σ (∅ : U) = factorialOf n` |
| `factorialOf_le_succ` | n! ≤ (n+1)! | `theorem factorialOf_le_succ (n : U) (hn : n ∈ (ω : U)) : factorialOf n ∈ factorialOf (Nat.Basic.succ n) ∨ factorialOf n = factorialOf (Nat.Basic.succ n)` |
| `factorialOf_le_mono` | m ≤ n → m! ≤ n! | `theorem factorialOf_le_mono {m n : U} (hm : m ∈ (ω : U)) (hn : n ∈ (ω : U)) (h_le : m ∈ n ∨ m = n) : factorialOf m ∈ factorialOf n ∨ factorialOf m = factorialOf n` |

**Patrón de demostración**: `fromPeano_surjective` + `subst` + `fromPeano_factorial` + teoremas de `Peano.Factorial`.

**Dependencias**: `fromPeano_surjective`, `fromPeano_injective`, `fromPeano_factorial`, `fromPeano_mul`, `fromPeano_le_iff`, `fromPeano_lt_iff`, `toPeano_proof_irrel`, `toPeano_fromPeano`, `toPeano_zero`, `Peano.Factorial.*`, `Nat_in_Omega`, `fromPeano_is_nat`, `mul_one_Omega`, `one_mul_Omega`, `zero_in_Omega`, `succ_in_Omega`

### 4.26 Nat.Gcd.lean

**Módulo**: `ZfcSetTheory.Nat.Gcd`
**Namespace**: `ZFC.Nat.Gcd`
**Actualizado**: 2026-03-24

**Importancia por sección**:

- Sección 1 (clausura en ω): medium — infraestructura
- Sección 2 (ecuaciones del algoritmo euclídeo): high — gcd_zero, gcd_pos_step
- Sección 3 (teoremas puente): high — gcd_eq_gcdOf, lcm_eq_lcmOf
- Sección 4 (propiedades de divisibilidad del GCD): high — gcd_divides, gcd_greatest
- Sección 5 (propiedades del LCM): high — lcm_multiple, lcm_comm

#### Sección 1: Clausura en ω

| Nombre | Descripción matemática | Firma Lean4 |
|--------|----------------------|-------------|
| `gcd_in_Omega` | gcd(a, b) ∈ ω | `theorem gcd_in_Omega (a b : U) (ha : a ∈ (ω : U)) (hb : b ∈ (ω : U)) : gcd a b ∈ (ω : U)` |
| `lcm_in_Omega` | lcm(a, b) ∈ ω | `theorem lcm_in_Omega (a b : U) (ha : a ∈ (ω : U)) (hb : b ∈ (ω : U)) : lcm a b ∈ (ω : U)` |

#### Sección 2: Ecuaciones del algoritmo euclídeo

| Nombre | Descripción matemática | Firma Lean4 |
|--------|----------------------|-------------|
| `gcd_zero` | gcd(a, 0) = a | `theorem gcd_zero (a : U) (ha : a ∈ (ω : U)) : gcd a ∅ = a` |
| `gcd_pos_step` | b ≠ 0 → gcd(a, b) = gcd(b, a mod b) | `theorem gcd_pos_step (a b : U) (ha : a ∈ (ω : U)) (hb : b ∈ (ω : U)) (hb_pos : b ≠ ∅) : gcd a b = gcd b (mod a b)` |

#### Sección 3: Teoremas puente

| Nombre | Descripción matemática | Firma Lean4 |
|--------|----------------------|-------------|
| `gcd_eq_gcdOf` | gcd(a, b) = gcdOf(a, b) | `theorem gcd_eq_gcdOf (a b : U) (ha : a ∈ (ω : U)) (hb : b ∈ (ω : U)) : gcd a b = gcdOf a b` |
| `lcm_eq_lcmOf` | lcm(a, b) = lcmOf(a, b) | `theorem lcm_eq_lcmOf (a b : U) (ha : a ∈ (ω : U)) (hb : b ∈ (ω : U)) : lcm a b = lcmOf a b` |

**Descripción**: `gcd_eq_gcdOf` se demuestra por inducción fuerte en b con `strong_induction_principle`. Caso base via `gcd_zero` y `gcdOf_zero_right`. Paso inductivo via `gcd_pos_step`, la hipótesis de inducción para `mod a b ∈ b`, y `gcdOf_pos_step`. `lcm_eq_lcmOf` usa `fromPeano_surjective` + bridges aritméticos.

#### Sección 4: Propiedades de divisibilidad del GCD

| Nombre | Descripción matemática | Firma Lean4 |
|--------|----------------------|-------------|
| `gcd_divides_left_Omega` | gcd(a, b) ∣ a | `theorem gcd_divides_left_Omega (a b : U) (ha : a ∈ (ω : U)) (hb : b ∈ (ω : U)) : divides (gcd a b) a` |
| `gcd_divides_right_Omega` | gcd(a, b) ∣ b | `theorem gcd_divides_right_Omega (a b : U) (ha : a ∈ (ω : U)) (hb : b ∈ (ω : U)) : divides (gcd a b) b` |
| `gcd_greatest_Omega` | k ∣ a ∧ k ∣ b → k ∣ gcd(a, b) | `theorem gcd_greatest_Omega (a b k : U) (ha : a ∈ (ω : U)) (hb : b ∈ (ω : U)) (hk : k ∈ (ω : U)) (hka : divides k a) (hkb : divides k b) : divides k (gcd a b)` |
| `gcd_comm_Omega` | gcd(a, b) = gcd(b, a) | `theorem gcd_comm_Omega (a b : U) (ha : a ∈ (ω : U)) (hb : b ∈ (ω : U)) : gcd a b = gcd b a` |

#### Sección 5: Propiedades del LCM

| Nombre | Descripción matemática | Firma Lean4 |
|--------|----------------------|-------------|
| `lcm_multiple_left_Omega` | a ∣ lcm(a, b) | `theorem lcm_multiple_left_Omega (a b : U) (ha : a ∈ (ω : U)) (hb : b ∈ (ω : U)) : divides a (lcm a b)` |
| `lcm_multiple_right_Omega` | b ∣ lcm(a, b) | `theorem lcm_multiple_right_Omega (a b : U) (ha : a ∈ (ω : U)) (hb : b ∈ (ω : U)) : divides b (lcm a b)` |
| `lcm_comm_Omega` | lcm(a, b) = lcm(b, a) | `theorem lcm_comm_Omega (a b : U) (ha : a ∈ (ω : U)) (hb : b ∈ (ω : U)) : lcm a b = lcm b a` |

**Patrón de demostración (§4-§5)**: Vía `gcd_eq_gcdOf`/`lcm_eq_lcmOf` reduciendo a las propiedades ya probadas de `gcdOf`/`lcmOf` en Nat.Arith.

**Dependencias**: `gcdOf`, `gcdOf_divides_left_Omega`, `gcdOf_divides_right_Omega`, `gcdOf_greatest_Omega`, `gcdOf_comm_Omega`, `lcmOf`, `lcmOf_in_Omega`, `lcmOf_multiple_left_Omega`, `lcmOf_multiple_right_Omega`, `lcmOf_comm_Omega`, `fromPeano_surjective`, `fromPeano_gcd`, `fromPeano_lcm`, `fromPeano_mul`, `fromPeano_div`, `divides_refl_Omega`, `divides_zero_Omega`, `antisymm_divides_Omega`, `divides_modOf_Omega`, `divides_add_Omega`, `divides_mul_left_Omega`, `mod_in_Omega`, `mod_lt_divisor_ZFC`, `mod_eq_modOf`, `divMod_eq_ZFC`, `strong_induction_principle`, `RecursiveFn`, `euclid_stable_add`, `euclidFn_shift`

---

### 4.27 Nat.Primes.lean

**Módulo**: `ZfcSetTheory.Nat.Primes`
**Namespace**: `ZFC.Nat.Primes`

**Importancia por sección**:

- Sección 1 (teorema puente): high — fromPeano_prime, equivalencia Peano↔ZFC
- Sección 2 (propiedades básicas de isPrime): high — isPrime_ne_zero, isPrime_ge_two, prime_divisors
- Sección 3 (existencia de divisor primo): high — exists_prime_divisor_ZFC
- Sección 4 (TFA existencia): high — Teorema Fundamental de la Aritmética (existencia)
- Sección 5 (TFA unicidad): high — Teorema Fundamental de la Aritmética (unicidad)

#### Sección 1: Teorema puente

| Nombre | Descripción matemática | Firma Lean4 |
|--------|----------------------|-------------|
| `fromPeano_prime` | Prime p ↔ isPrime (fromPeano p) | `theorem fromPeano_prime (p : Peano.ℕ₀) : Peano.Arith.Prime p ↔ isPrime (fromPeano p : U)` |

**Patrón de demostración**: Enfoque A — dirección `→` descompone `Peano.Arith.Prime` en sus tres componentes y los convierte vía `fromPeano_zero_eq`/`fromPeano_one_eq` (injectividad) y `fromPeano_divides`+`fromPeano_mul`+`fromPeano_surjective` (divisibilidad). Dirección `←` aplica las mismas herramientas en sentido inverso.

**Dependencias**: `fromPeano_injective`, `fromPeano_surjective`, `fromPeano_mul`, `fromPeano_divides`, `Nat_in_Omega`, `fromPeano_is_nat`, `mem_Omega_is_Nat`

#### Sección 2: Propiedades básicas de isPrime

| Nombre | Descripción matemática | Firma Lean4 |
|--------|----------------------|-------------|
| `isPrime_in_Omega` | isPrime p → p ∈ ω | `theorem isPrime_in_Omega (p : U) (hp : isPrime p) : p ∈ (ω : U)` |
| `isPrime_ne_zero` | isPrime p → p ≠ ∅ | `theorem isPrime_ne_zero (p : U) (hp : isPrime p) : p ≠ (∅ : U)` |
| `isPrime_ne_one` | isPrime p → p ≠ σ ∅ | `theorem isPrime_ne_one (p : U) (hp : isPrime p) : p ≠ σ (∅ : U)` |
| `isPrime_ge_two` | isPrime p → σ(σ ∅) ≤ p | `theorem isPrime_ge_two (p : U) (hp : isPrime p) : σ (σ (∅ : U)) ∈ p ∨ σ (σ (∅ : U)) = p` |
| `isPrime_prime_divisors` | isPrime p ∧ d ∣ p → d = σ ∅ ∨ d = p | `theorem isPrime_prime_divisors (p d : U) (hp : isPrime p) (hd : d ∈ (ω : U)) (hdvd : divides d p) : d = σ (∅ : U) ∨ d = p` |

**Dependencias**: `fromPeano_surjective`, `fromPeano_prime`, `prime_ge_two`, `prime_divisors`, `fromPeano_le_iff`, `fromPeano_divides`, `fromPeano_injective`, `fromPeano_one_eq`

#### Sección 3: Existencia de divisor primo

| Nombre | Descripción matemática | Firma Lean4 |
|--------|----------------------|-------------|
| `exists_prime_divisor_ZFC` | ∀ n ∈ ω, 2 ≤ n → ∃ p primo que divide n | `theorem exists_prime_divisor_ZFC (n : U) (hn : n ∈ (ω : U)) (h_ge_2 : σ (σ (∅ : U)) ∈ n ∨ σ (σ (∅ : U)) = n) : ∃ p : U, isPrime p ∧ divides p n` |

**Dependencias**: `fromPeano_surjective`, `fromPeano_le_iff`, `fromPeano_two_eq`, `exists_prime_divisor`, `fromPeano_prime`, `fromPeano_divides`

#### Sección 4: TFA — Existencia de factorización prima (Enfoque A)

| Nombre | Descripción matemática | Firma Lean4 |
|--------|----------------------|-------------|
| `exists_prime_factorization_ZFC` | ∀ n ∈ ω, 2 ≤ n → ∃ ps : DList ℕ₀ de primos con ΠZ(∏ ps) = n | `theorem exists_prime_factorization_ZFC (n : U) (hn : n ∈ (ω : U)) (h_ge_2 : σ (σ (∅ : U)) ∈ n ∨ σ (σ (∅ : U)) = n) : ∃ ps : DList ℕ₀, PrimeList ps ∧ (fromPeano (product_list ps) : U) = n` |

**Dependencias**: `fromPeano_surjective`, `fromPeano_le_iff`, `exists_prime_factorization`, `fromPeano_injective`

#### Sección 5: TFA — Unicidad de factorización prima (Enfoque A)

| Nombre | Descripción matemática | Firma Lean4 |
|--------|----------------------|-------------|
| `unique_prime_factorization_ZFC` | Dos listas de primos con igual producto ZFC tienen la misma multiplicidad de cada primo | `theorem unique_prime_factorization_ZFC (ps qs : DList ℕ₀) (hps : PrimeList ps) (hqs : PrimeList qs) (h_prod : (fromPeano (product_list ps) : U) = fromPeano (product_list qs)) (p : Peano.ℕ₀) (hp : Peano.Arith.Prime p) : DList.length (DList.filter (fun q => decide (q = p)) ps) = DList.length (DList.filter (fun q => decide (q = p)) qs)` |

**Dependencias**: `fromPeano_injective`, `unique_prime_factorization`

---

### 4.28 Nat.Binom.lean

**Módulo**: `ZfcSetTheory.Nat.Binom`
**Namespace**: `ZFC.Nat.Binom`

**Importancia por sección**:

- Sección 1 (clausura en ω): medium — infraestructura
- Sección 2 (teorema puente): high — fromPeano_binom
- Sección 3 (valores concretos): medium — C(0,0), C(σn,0), C(0,σk)
- Sección 4 (regla de Pascal): high — recursión binomial fundamental
- Sección 5 (propiedades algebraicas): medium — C(n,0), C(n,1), C(n,n)
- Sección 6 (anulación y positividad): medium — binomOf_eq_zero_of_gt, binomOf_pos
- Sección 7 (conexión con factorial): high — C(n,k)·k!·(n−k)! = n!

#### Sección 1: Clausura en ω

| Nombre | Descripción matemática | Firma Lean4 |
|--------|----------------------|-------------|
| `binomOf_in_Omega` | C(n,k) ∈ ω | `theorem binomOf_in_Omega (n k : U) (hn : n ∈ (ω : U)) (hk : k ∈ (ω : U)) : binomOf n k ∈ (ω : U)` |

**Dependencias**: `Nat_in_Omega`, `fromPeano_is_nat`

#### Sección 2: Teorema puente

| Nombre | Descripción matemática | Firma Lean4 |
|--------|----------------------|-------------|
| `fromPeano_binom` | ΠZ(C(p, q)) = binomOf(ΠZ p, ΠZ q) | `theorem fromPeano_binom (p q : Peano.ℕ₀) : (fromPeano (Peano.Binom.binom p q) : U) = binomOf (fromPeano p) (fromPeano q)` |

**Patrón de demostración**: `simp only [binomOf, dif_pos ...]` + `congr 1; congr 1` + dos `toPeano_proof_irrel`/`toPeano_fromPeano` (patrón estándar Patrón B con dos argumentos, idéntico a `fromPeano_div`).

**Dependencias**: `toPeano_proof_irrel`, `toPeano_fromPeano`, `Nat_in_Omega`, `fromPeano_is_nat`, `mem_Omega_is_Nat`

#### Sección 3: Valores concretos

| Nombre | Descripción matemática | Firma Lean4 |
|--------|----------------------|-------------|
| `binomOf_zero_zero` | C(0, 0) = 1 | `theorem binomOf_zero_zero : binomOf (∅ : U) ∅ = σ (∅ : U)` |
| `binomOf_succ_zero` | C(σ n, 0) = 1 | `theorem binomOf_succ_zero (n : U) (hn : n ∈ (ω : U)) : binomOf (σ n) ∅ = σ (∅ : U)` |
| `binomOf_zero_succ` | C(0, σ k) = 0 | `theorem binomOf_zero_succ (k : U) (hk : k ∈ (ω : U)) : binomOf (∅ : U) (σ k) = ∅` |

**Dependencias**: `zero_in_Omega`, `toPeano_proof_irrel`, `toPeano_zero`, `fromPeano_surjective`, `mem_Omega_is_Nat`, `Peano.Binom.binom_zero_zero`, `Peano.Binom.binom_succ_zero`, `Peano.Binom.binom_zero_succ`

#### Sección 4: Regla de Pascal

| Nombre | Descripción matemática | Firma Lean4 |
|--------|----------------------|-------------|
| `binomOf_pascal` | C(σ n, σ k) = C(n, k) + C(n, σ k) | `theorem binomOf_pascal (n k : U) (hn : n ∈ (ω : U)) (hk : k ∈ (ω : U)) : binomOf (σ n) (σ k) = add (binomOf n k) (binomOf n (σ k))` |

**Patrón de demostración**: `fromPeano_surjective` para obtener `p, q` Peano → `← fromPeano_binom` (×3) + `Peano.Binom.binom_pascal` + `fromPeano_add`.

**Dependencias**: `fromPeano_surjective`, `fromPeano_binom`, `fromPeano_add`, `Peano.Binom.binom_pascal`

#### Sección 5: Propiedades algebraicas

| Nombre | Descripción matemática | Firma Lean4 |
|--------|----------------------|-------------|
| `binomOf_n_zero` | C(n, 0) = 1 | `theorem binomOf_n_zero (n : U) (hn : n ∈ (ω : U)) : binomOf n ∅ = σ (∅ : U)` |
| `binomOf_n_one` | C(n, 1) = n | `theorem binomOf_n_one (n : U) (hn : n ∈ (ω : U)) : binomOf n (σ (∅ : U)) = n` |
| `binomOf_self` | C(n, n) = 1 | `theorem binomOf_self (n : U) (hn : n ∈ (ω : U)) : binomOf n n = σ (∅ : U)` |
| `binomOf_succ_n_by_n` | C(σ n, n) = σ n | `theorem binomOf_succ_n_by_n (n : U) (hn : n ∈ (ω : U)) : binomOf (σ n) n = σ n` |

**Dependencias**: `fromPeano_surjective`, `fromPeano_binom`, `Peano.Binom.binom_n_zero`, `Peano.Binom.binom_n_one`, `Peano.Binom.binom_self`, `Peano.Binom.binom_succ_n_by_n`

#### Sección 6: Anulación y positividad

| Nombre | Descripción matemática | Firma Lean4 |
|--------|----------------------|-------------|
| `binomOf_eq_zero_of_gt` | n < k → C(n, k) = 0 | `theorem binomOf_eq_zero_of_gt {n k : U} (hn : n ∈ (ω : U)) (hk : k ∈ (ω : U)) (h : n ∈ k) : binomOf n k = ∅` |
| `binomOf_pos` | k ≤ n → 0 < C(n, k) | `theorem binomOf_pos {n k : U} (hn : n ∈ (ω : U)) (hk : k ∈ (ω : U)) (h : k ∈ n ∨ k = n) : (∅ : U) ∈ binomOf n k` |

**Dependencias**: `fromPeano_surjective`, `fromPeano_binom`, `fromPeano_lt_iff`, `fromPeano_le_iff`, `Peano.Binom.binom_eq_zero_of_gt`, `Peano.Binom.binom_pos`

#### Sección 7: Conexión con factorial

| Nombre | Descripción matemática | Firma Lean4 |
|--------|----------------------|-------------|
| `binomOf_mul_factorials` | C(n,k) · k! · (n−k)! = n! | `theorem binomOf_mul_factorials {n k : U} (hn : n ∈ (ω : U)) (hk : k ∈ (ω : U)) (h_le : k ∈ n ∨ k = n) : mul (mul (binomOf n k) (factorialOf k)) (factorialOf (sub n k)) = factorialOf n` |

**Patrón de demostración**: `fromPeano_surjective` → cadena completa de `← fromPeano_binom`, `← fromPeano_factorial`, `← fromPeano_sub`, `← fromPeano_mul` (×2), `← fromPeano_factorial` → `congrArg fromPeano (Peano.Binom.binom_mul_factorials ...)`.

**Dependencias**: `fromPeano_surjective`, `fromPeano_binom`, `fromPeano_factorial`, `fromPeano_sub`, `fromPeano_mul`, `fromPeano_le_iff`, `Peano.Binom.binom_mul_factorials`

### 4.29 Nat.MaxMin.lean

**Módulo**: `ZfcSetTheory.Nat.MaxMin`
**Namespace**: `ZFC.Nat.MaxMin`

**Importancia por sección**:

- Sección 1 (clausura en ω): medium — infraestructura
- Sección 2 (teoremas puente): high — fromPeano_max, fromPeano_min
- Sección 3 (idempotencia): medium — max(n,n)=n, min(n,n)=n
- Sección 4 (conmutatividad): high — max_comm, min_comm
- Sección 5 (asociatividad): high — max_assoc, min_assoc
- Sección 6 (identidad/aniquilador con ∅): medium — max/min con cero
- Sección 7 (cotas superior/inferior): high — propiedades de retículo
- Sección 8 (caracterización vía ≤): medium — max_eq_right, min_eq_left
- Sección 9 (max/min es argumento): medium — maxOf_is_any, minOf_is_any
- Sección 10 (max=min sii iguales): medium — eq_iff_maxOf_eq_minOf

#### Sección 1: Clausura en ω

| Nombre | Descripción matemática | Firma Lean4 |
|--------|----------------------|-------------|
| `maxOf_in_Omega` | max(n, m) ∈ ω | `theorem maxOf_in_Omega (n m : U) (hn : n ∈ (ω : U)) (hm : m ∈ (ω : U)) : maxOf n m ∈ (ω : U)` |
| `minOf_in_Omega` | min(n, m) ∈ ω | `theorem minOf_in_Omega (n m : U) (hn : n ∈ (ω : U)) (hm : m ∈ (ω : U)) : minOf n m ∈ (ω : U)` |

**Dependencias**: `Nat_in_Omega`, `fromPeano_is_nat`

#### Sección 2: Teoremas puente

| Nombre | Descripción matemática | Firma Lean4 |
|--------|----------------------|-------------|
| `fromPeano_max` | ΠZ(max(p, q)) = maxOf(ΠZ p, ΠZ q) | `theorem fromPeano_max (p q : Peano.ℕ₀) : (fromPeano (Peano.MaxMin.max p q) : U) = maxOf (fromPeano p) (fromPeano q)` |
| `fromPeano_min` | ΠZ(min(p, q)) = minOf(ΠZ p, ΠZ q) | `theorem fromPeano_min (p q : Peano.ℕ₀) : (fromPeano (Peano.MaxMin.min p q) : U) = minOf (fromPeano p) (fromPeano q)` |

**Patrón de demostración**: `simp only [maxOf/minOf, dif_pos ...]` + `congr 1; congr 1` + dos `toPeano_proof_irrel`/`toPeano_fromPeano` (patrón estándar Patrón B con dos argumentos).

**Dependencias**: `toPeano_proof_irrel`, `toPeano_fromPeano`, `Nat_in_Omega`, `fromPeano_is_nat`, `mem_Omega_is_Nat`

#### Sección 3: Idempotencia

| Nombre | Descripción matemática | Firma Lean4 |
|--------|----------------------|-------------|
| `maxOf_idem` | max(n, n) = n | `theorem maxOf_idem (n : U) (hn : n ∈ (ω : U)) : maxOf n n = n` |
| `minOf_idem` | min(n, n) = n | `theorem minOf_idem (n : U) (hn : n ∈ (ω : U)) : minOf n n = n` |

**Dependencias**: `fromPeano_surjective`, `fromPeano_max`, `fromPeano_min`, `Peano.MaxMin.max_idem`, `Peano.MaxMin.min_idem`

#### Sección 4: Conmutatividad

| Nombre | Descripción matemática | Firma Lean4 |
|--------|----------------------|-------------|
| `maxOf_comm` | max(n, m) = max(m, n) | `theorem maxOf_comm (n m : U) (hn : n ∈ (ω : U)) (hm : m ∈ (ω : U)) : maxOf n m = maxOf m n` |
| `minOf_comm` | min(n, m) = min(m, n) | `theorem minOf_comm (n m : U) (hn : n ∈ (ω : U)) (hm : m ∈ (ω : U)) : minOf n m = minOf m n` |

**Dependencias**: `fromPeano_surjective`, `fromPeano_max`, `fromPeano_min`, `Peano.MaxMin.max_comm`, `Peano.MaxMin.min_comm`

#### Sección 5: Asociatividad

| Nombre | Descripción matemática | Firma Lean4 |
|--------|----------------------|-------------|
| `maxOf_assoc` | max(max(n, m), k) = max(n, max(m, k)) | `theorem maxOf_assoc (n m k : U) (hn : n ∈ (ω : U)) (hm : m ∈ (ω : U)) (hk : k ∈ (ω : U)) : maxOf (maxOf n m) k = maxOf n (maxOf m k)` |
| `minOf_assoc` | min(min(n, m), k) = min(n, min(m, k)) | `theorem minOf_assoc (n m k : U) (hn : n ∈ (ω : U)) (hm : m ∈ (ω : U)) (hk : k ∈ (ω : U)) : minOf (minOf n m) k = minOf n (minOf m k)` |

**Patrón de demostración**: `fromPeano_surjective` para 3 variables → `← fromPeano_max/min` (×4) + `Peano.MaxMin.max_assoc`/`min_assoc`.

**Dependencias**: `fromPeano_surjective`, `fromPeano_max`, `fromPeano_min`, `Peano.MaxMin.max_assoc`, `Peano.MaxMin.min_assoc`

#### Sección 6: Identidad/Aniquilador con ∅

| Nombre | Descripción matemática | Firma Lean4 |
|--------|----------------------|-------------|
| `maxOf_zero_left` | max(∅, n) = n | `theorem maxOf_zero_left (n : U) (hn : n ∈ (ω : U)) : maxOf (∅ : U) n = n` |
| `maxOf_zero_right` | max(n, ∅) = n | `theorem maxOf_zero_right (n : U) (hn : n ∈ (ω : U)) : maxOf n (∅ : U) = n` |
| `minOf_zero_left` | min(∅, n) = ∅ | `theorem minOf_zero_left (n : U) (hn : n ∈ (ω : U)) : minOf (∅ : U) n = ∅` |
| `minOf_zero_right` | min(n, ∅) = ∅ | `theorem minOf_zero_right (n : U) (hn : n ∈ (ω : U)) : minOf n (∅ : U) = ∅` |

**Dependencias**: `fromPeano_surjective`, `fromPeano_max`, `fromPeano_min`, `Peano.MaxMin.max_not_0`, `Peano.MaxMin.max_0_not`, `Peano.MaxMin.min_abs_0`, `Peano.MaxMin.min_0_abs`

#### Sección 7: Cotas superior/inferior

| Nombre | Descripción matemática | Firma Lean4 |
|--------|----------------------|-------------|
| `le_maxOf_left` | n ≤ max(n, m) | `theorem le_maxOf_left (n m : U) (hn : n ∈ (ω : U)) (hm : m ∈ (ω : U)) : n ∈ maxOf n m ∨ n = maxOf n m` |
| `le_maxOf_right` | m ≤ max(n, m) | `theorem le_maxOf_right (n m : U) (hn : n ∈ (ω : U)) (hm : m ∈ (ω : U)) : m ∈ maxOf n m ∨ m = maxOf n m` |
| `maxOf_le` | n ≤ k ∧ m ≤ k → max(n, m) ≤ k | `theorem maxOf_le (n m k : U) (hn : n ∈ (ω : U)) (hm : m ∈ (ω : U)) (hk : k ∈ (ω : U)) (h_n_le_k : n ∈ k ∨ n = k) (h_m_le_k : m ∈ k ∨ m = k) : maxOf n m ∈ k ∨ maxOf n m = k` |
| `minOf_le_left` | min(n, m) ≤ n | `theorem minOf_le_left (n m : U) (hn : n ∈ (ω : U)) (hm : m ∈ (ω : U)) : minOf n m ∈ n ∨ minOf n m = n` |
| `minOf_le_right` | min(n, m) ≤ m | `theorem minOf_le_right (n m : U) (hn : n ∈ (ω : U)) (hm : m ∈ (ω : U)) : minOf n m ∈ m ∨ minOf n m = m` |
| `le_minOf` | k ≤ n ∧ k ≤ m → k ≤ min(n, m) | `theorem le_minOf (k n m : U) (hk : k ∈ (ω : U)) (hn : n ∈ (ω : U)) (hm : m ∈ (ω : U)) (h_k_le_n : k ∈ n ∨ k = n) (h_k_le_m : k ∈ m ∨ k = m) : k ∈ minOf n m ∨ k = minOf n m` |

**Patrón de demostración**: `fromPeano_surjective` → `← fromPeano_max/min` → `fromPeano_le_iff` en ambas direcciones + lema Peano correspondiente.

**Dependencias**: `fromPeano_surjective`, `fromPeano_max`, `fromPeano_min`, `fromPeano_le_iff`, `Peano.MaxMin.le_max_left`, `Peano.MaxMin.le_max_right`, `Peano.MaxMin.max_le`, `Peano.MaxMin.min_le_left`, `Peano.MaxMin.min_le_right`, `Peano.MaxMin.le_min`

#### Sección 8: Caracterización vía ≤

| Nombre | Descripción matemática | Firma Lean4 |
|--------|----------------------|-------------|
| `maxOf_eq_right` | n ≤ m → max(n, m) = m | `theorem maxOf_eq_right (n m : U) (hn : n ∈ (ω : U)) (hm : m ∈ (ω : U)) (h_le : n ∈ m ∨ n = m) : maxOf n m = m` |
| `maxOf_eq_left` | m ≤ n → max(n, m) = n | `theorem maxOf_eq_left (n m : U) (hn : n ∈ (ω : U)) (hm : m ∈ (ω : U)) (h_le : m ∈ n ∨ m = n) : maxOf n m = n` |
| `minOf_eq_left` | n ≤ m → min(n, m) = n | `theorem minOf_eq_left (n m : U) (hn : n ∈ (ω : U)) (hm : m ∈ (ω : U)) (h_le : n ∈ m ∨ n = m) : minOf n m = n` |
| `minOf_eq_right` | m ≤ n → min(n, m) = m | `theorem minOf_eq_right (n m : U) (hn : n ∈ (ω : U)) (hm : m ∈ (ω : U)) (h_le : m ∈ n ∨ m = n) : minOf n m = m` |

**Patrón de demostración**: `fromPeano_surjective` → `← fromPeano_max/min` → `congrArg fromPeano (Peano.MaxMin.le_then_max/min_eq_... ...)`.

**Dependencias**: `fromPeano_surjective`, `fromPeano_max`, `fromPeano_min`, `fromPeano_le_iff`, `Peano.MaxMin.le_then_max_eq_right`, `Peano.MaxMin.le_then_max_eq_left`, `Peano.MaxMin.le_then_min_eq_left`, `Peano.MaxMin.le_then_min_eq_right`

#### Sección 9: max/min es uno de los argumentos

| Nombre | Descripción matemática | Firma Lean4 |
|--------|----------------------|-------------|
| `maxOf_is_any` | max(n, m) = n ∨ max(n, m) = m | `theorem maxOf_is_any (n m : U) (hn : n ∈ (ω : U)) (hm : m ∈ (ω : U)) : maxOf n m = n ∨ maxOf n m = m` |
| `minOf_is_any` | min(n, m) = n ∨ min(n, m) = m | `theorem minOf_is_any (n m : U) (hn : n ∈ (ω : U)) (hm : m ∈ (ω : U)) : minOf n m = n ∨ minOf n m = m` |

**Dependencias**: `fromPeano_surjective`, `fromPeano_max`, `fromPeano_min`, `Peano.MaxMin.max_is_any`, `Peano.MaxMin.min_is_any`

#### Sección 10: max = min sii iguales

| Nombre | Descripción matemática | Firma Lean4 |
|--------|----------------------|-------------|
| `eq_iff_maxOf_eq_minOf` | n = m ↔ max(n, m) = min(n, m) | `theorem eq_iff_maxOf_eq_minOf (n m : U) (hn : n ∈ (ω : U)) (hm : m ∈ (ω : U)) : n = m ↔ maxOf n m = minOf n m` |

**Patrón de demostración**: `fromPeano_surjective` → `← fromPeano_max`, `← fromPeano_min` → `fromPeano_injective` en ambos sentidos + `Peano.MaxMin.eq_then_eq_max_min` / `Peano.MaxMin.eq_max_min_then_eq`.

**Dependencias**: `fromPeano_surjective`, `fromPeano_max`, `fromPeano_min`, `fromPeano_injective`, `Peano.MaxMin.eq_then_eq_max_min`, `Peano.MaxMin.eq_max_min_then_eq`

### 4.30 Nat.NewtonBinom.lean

**Módulo**: `ZfcSetTheory.Nat.NewtonBinom`
**Namespace**: `ZFC.Nat.NewtonBinom`

**Importancia por sección**:

- Sección 1 (clausura en ω): medium — infraestructura
- Sección 2 (teorema puente): high — fromPeano_binomTerm
- Sección 3 (valores concretos): medium — binomTermOf_zero, binomTermOf_self
- Sección 4 (expansión): high — binomTermOf_eq = C(n,k)·a^k·b^(n−k)
- Sección 5 (separación de potencias): medium — pow_add_split_Omega
- Sección 6 (teorema binomial de Newton): high — resultado principal (a+b)^n
- Sección 7 (suma coeficientes binomiales = 2^n): high — corolario clásico
- Sección 8 (comparación existencial de crecimiento): medium — resultado auxiliar

#### Sección 1: Clausura en ω

| Nombre | Descripción matemática | Firma Lean4 |
|--------|----------------------|-------------|
| `binomTermOf_in_Omega` | C(n,k)·a^k·b^(n−k) ∈ ω | `theorem binomTermOf_in_Omega (a b n k : U) (ha : a ∈ (ω : U)) (hb : b ∈ (ω : U)) (hn : n ∈ (ω : U)) (hk : k ∈ (ω : U)) : binomTermOf a b n k ∈ (ω : U)` |

**Dependencias**: `Nat_in_Omega`, `fromPeano_is_nat`

#### Sección 2: Teorema puente

| Nombre | Descripción matemática | Firma Lean4 |
|--------|----------------------|-------------|
| `fromPeano_binomTerm` | ΠZ(binomTerm(p,q,r,s)) = binomTermOf(ΠZ p, ΠZ q, ΠZ r, ΠZ s) | `theorem fromPeano_binomTerm (p q r s : Peano.ℕ₀) : (fromPeano (Peano.NewtonBinom.binomTerm p q r s) : U) = binomTermOf (fromPeano p) (fromPeano q) (fromPeano r) (fromPeano s)` |

**Patrón de demostración**: `simp only [binomTermOf, dif_pos ...]` + `congr 1; congr 1; congr 1; congr 1` + cuatro `toPeano_proof_irrel`/`toPeano_fromPeano` (Patrón B con 4 argumentos).

**Dependencias**: `toPeano_proof_irrel`, `toPeano_fromPeano`, `Nat_in_Omega`, `fromPeano_is_nat`, `mem_Omega_is_Nat`

#### Sección 3: Valores concretos

| Nombre | Descripción matemática | Firma Lean4 |
|--------|----------------------|-------------|
| `binomTermOf_zero` | binomTerm(a, b, n, 0) = b^n | `theorem binomTermOf_zero (a b n : U) (ha : a ∈ (ω : U)) (hb : b ∈ (ω : U)) (hn : n ∈ (ω : U)) : binomTermOf a b n ∅ = pow b n` |
| `binomTermOf_self` | binomTerm(a, b, n, n) = a^n | `theorem binomTermOf_self (a b n : U) (ha : a ∈ (ω : U)) (hb : b ∈ (ω : U)) (hn : n ∈ (ω : U)) : binomTermOf a b n n = pow a n` |

**Dependencias**: `fromPeano_surjective`, `fromPeano_binomTerm`, `fromPeano_pow`, `Peano.NewtonBinom.binomTerm_zero`, `Peano.NewtonBinom.binomTerm_self`

#### Sección 4: Expansión

| Nombre | Descripción matemática | Firma Lean4 |
|--------|----------------------|-------------|
| `binomTermOf_eq` | binomTerm(a,b,n,k) = C(n,k)·a^k·b^(n−k) | `theorem binomTermOf_eq (a b n k : U) (ha : a ∈ (ω : U)) (hb : b ∈ (ω : U)) (hn : n ∈ (ω : U)) (hk : k ∈ (ω : U)) : binomTermOf a b n k = mul (mul (binomOf n k) (pow a k)) (pow b (sub n k))` |

**Patrón de demostración**: `fromPeano_surjective` (×4) → `← fromPeano_binomTerm` → `show` explícito → cadena de `← fromPeano_binom`, `← fromPeano_pow`, `← fromPeano_sub`, `← fromPeano_mul` (×2) → `rfl`.

**Dependencias**: `fromPeano_surjective`, `fromPeano_binomTerm`, `fromPeano_binom`, `fromPeano_pow`, `fromPeano_sub`, `fromPeano_mul`

#### Sección 5: Separación de potencias

| Nombre | Descripción matemática | Firma Lean4 |
|--------|----------------------|-------------|
| `pow_add_split_Omega` | n^(m+k) = n^m · n^k | `theorem pow_add_split_Omega (n m k : U) (hn : n ∈ (ω : U)) (hm : m ∈ (ω : U)) (hk : k ∈ (ω : U)) : pow n (add m k) = mul (pow n m) (pow n k)` |

**Patrón de demostración**: `fromPeano_surjective` (×3) → cadena de `← fromPeano_add/pow/mul` → `congrArg fromPeano (Peano.NewtonBinom.pow_add_split ...)`.

**Dependencias**: `fromPeano_surjective`, `fromPeano_add`, `fromPeano_pow`, `fromPeano_mul`, `Peano.NewtonBinom.pow_add_split`

#### Sección 6: Teorema binomial de Newton (nivel Peano)

| Nombre | Descripción matemática | Firma Lean4 |
|--------|----------------------|-------------|
| `newton_binom_peano` | (a+b)^n = Σ_{k≤n} C(n,k)·a^k·b^(n−k) | `theorem newton_binom_peano (a b : Peano.ℕ₀) (n : Peano.ℕ₀) : pow (add (fromPeano a : U) (fromPeano b)) (fromPeano n) = (fromPeano (Peano.NewtonBinom.finSum (Peano.NewtonBinom.binomTerm a b n) n) : U)` |

**Nota**: Teorema enunciado a nivel Peano con resultado transportado a ZFC vía `fromPeano`. `finSum` no se transporta directamente por ser una función de orden superior.

**Dependencias**: `fromPeano_add`, `fromPeano_pow`, `Peano.NewtonBinom.newton_binom`

#### Sección 7: Suma de coeficientes binomiales = 2^n

| Nombre | Descripción matemática | Firma Lean4 |
|--------|----------------------|-------------|
| `sum_binom_eq_pow_two_peano` | Σ_{k≤n} C(n,k) = 2^n | `theorem sum_binom_eq_pow_two_peano (n : Peano.ℕ₀) : (fromPeano (Peano.NewtonBinom.finSum (fun k => Peano.Binom.binom n k) n) : U) = pow (σ (σ (∅ : U))) (fromPeano n)` |

**Nota**: Teorema enunciado a nivel Peano con resultado transportado a ZFC vía `fromPeano`. 2 se codifica como `σ (σ ∅)`.

**Dependencias**: `fromPeano_pow`, `Peano.NewtonBinom.sum_binom_eq_pow_two`

#### Sección 8: Comparación existencial de crecimiento

| Nombre | Descripción matemática | Firma Lean4 |
|--------|----------------------|-------------|
| `exists_nm_growth_Omega` | ∃ n m ∈ ω, ∀ k ≥ 1, (n+k)^m < n^(m+k) | `theorem exists_nm_growth_Omega : ∃ n m : U, n ∈ (ω : U) ∧ m ∈ (ω : U) ∧ ∀ k : U, k ∈ (ω : U) → (σ (∅ : U)) ∈ k ∨ σ (∅ : U) = k → pow (add n k) m ∈ pow n (add m k)` |

**Patrón de demostración**: `Peano.NewtonBinom.exists_nm_growth` → testigos `fromPeano pn`, `fromPeano pm` → `fromPeano_surjective` para k → cadena de `← fromPeano_add/pow` → `fromPeano_lt_iff` + `fromPeano_le_iff`.

**Dependencias**: `fromPeano_surjective`, `fromPeano_add`, `fromPeano_pow`, `fromPeano_lt_iff`, `fromPeano_le_iff`, `Peano.NewtonBinom.exists_nm_growth`

### 4.31 Nat.WellFounded.lean

**Módulo**: `ZfcSetTheory.Nat.WellFounded`
**Namespace**: `ZFC.Nat.WellFounded`

**Importancia por sección**:

- Sección 1 (buen fundamento): high — acc_lt_Omega, accesibilidad de ω
- Sección 2 (principio de buena ordenación): high — well_ordering_Omega, resultado principal

#### Sección 1: Buen fundamento

| Nombre | Descripción matemática | Firma Lean4 |
|--------|----------------------|-------------|
| `acc_lt_Omega` | Todo n ∈ ω es accesible bajo ∈ restringido a ω | `theorem acc_lt_Omega (n : U) (_hn : n ∈ (ω : U)) : Acc (fun a b : U => a ∈ ω ∧ b ∈ ω ∧ a ∈ b) n` |

**Patrón de demostración**: Prueba en modo término delegando a `nat_mem_wf.apply n`.

**Dependencias**: `nat_mem_wf`

#### Sección 2: Principio de buena ordenación

| Nombre | Descripción matemática | Firma Lean4 |
|--------|----------------------|-------------|
| `well_ordering_Omega` | Todo subconjunto no vacío de ω tiene un mínimo único | `theorem well_ordering_Omega (P : U → Prop) (h_nonempty : ∃ k : U, k ∈ (ω : U) ∧ P k) : ∃ n : U, n ∈ (ω : U) ∧ P n ∧ (∀ m : U, m ∈ (ω : U) → P m → (n ∈ m ∨ n = m)) ∧ (∀ n' : U, n' ∈ (ω : U) → P n' → (∀ m : U, m ∈ (ω : U) → P m → (n' ∈ m ∨ n' = m)) → n' = n)` |
| `well_ordering_Omega_exists` | Forma simplificada sin unicidad | `theorem well_ordering_Omega_exists (P : U → Prop) (h_nonempty : ∃ k : U, k ∈ (ω : U) ∧ P k) : ∃ n : U, n ∈ (ω : U) ∧ P n ∧ ∀ m : U, m ∈ (ω : U) → P m → (n ∈ m ∨ n = m)` |

**Patrón de demostración** (`well_ordering_Omega`): Define `Q : Peano.ℕ₀ → Prop := fun p => P (fromPeano p)` → `fromPeano_surjective` para testigo → `Peano.WellFounded.well_ordering_principle Q` → transporta minimidad vía `fromPeano_le_iff` y unicidad vía `congrArg fromPeano`.

**Patrón de demostración** (`well_ordering_Omega_exists`): Extrae los 4 componentes de `well_ordering_Omega` y descarta la unicidad.

**Dependencias**: `fromPeano_surjective`, `fromPeano_le_iff`, `fromPeano_injective`, `Nat_in_Omega`, `fromPeano_is_nat`, `mem_Omega_is_Nat`, `Peano.WellFounded.well_ordering_principle`, `nat_mem_wf`

---

### 4.32 Peano.FiniteSequences.lean

**Módulo**: `ZfcSetTheory.Peano.FiniteSequences`
**Namespace**: `ZFC.Peano.FiniteSequences`
**Dependencias del módulo**: `Nat.Add` + anteriores

**Importancia por sección**:

- Sección 1 (predicado isFinSeq): high — predicado central, extensionalidad
- Sección 2 (FinSeqSet): medium — construcción del conjunto
- Sección 3 (secuencia vacía): medium — isFinSeq_empty, FinSeqSet_zero
- Sección 4 (appendElem): high — construcción clave para secuencias
- Sección 5 (descomposición): medium — isFinSeq_restriction

#### Sección 1: Predicado central (isFinSeq)

| Nombre | Descripción matemática | Firma Lean4 |
|--------|----------------------|-------------|
| `isFinSeq_in_Omega` | $\text{isFinSeq}(f,n,A) \Rightarrow n \in \omega$ | `theorem isFinSeq_in_Omega {f n A : U} (h : isFinSeq f n A) : n ∈ ω` |
| `isFinSeq_is_function` | $\text{isFinSeq}(f,n,A) \Rightarrow f : n \to A$ | `theorem isFinSeq_is_function {f n A : U} (h : isFinSeq f n A) : IsFunction f n A` |
| `isFinSeq_domain` | $\text{isFinSeq}(f,n,A) \Rightarrow \text{dom}(f) = n$ | `theorem isFinSeq_domain {f n A : U} (h : isFinSeq f n A) : domain f = n` |
| `isFinSeq_subset` | $\text{isFinSeq}(f,n,A) \Rightarrow f \subset n \times_s A$ | `theorem isFinSeq_subset {f n A : U} (h : isFinSeq f n A) : f ⊆ n ×ₛ A` |
| `isFinSeq_unique_length` | $f : n \to A \land f : m \to A \Rightarrow n = m$ | `theorem isFinSeq_unique_length {f n m A : U} (hn : isFinSeq f n A) (hm : isFinSeq f m A) : n = m` |
| `isFinSeq_apply_mem` | $\text{isFinSeq}(f,n,A) \land i \in n \Rightarrow f(i) \in A$ | `theorem isFinSeq_apply_mem {f n A i : U} (h : isFinSeq f n A) (hi : i ∈ n) : f⦅i⦆ ∈ A` |
| `isFinSeq_pair_mem` | $\text{isFinSeq}(f,n,A) \land i \in n \Rightarrow \langle i, f(i) \rangle \in f$ | `theorem isFinSeq_pair_mem {f n A i : U} (h : isFinSeq f n A) (hi : i ∈ n) : ⟨i, f⦅i⦆⟩ ∈ f` |
| `isFinSeq_ext` | $f,g : n \to A \land (\forall i \in n,\; f(i) = g(i)) \Rightarrow f = g$ | `theorem isFinSeq_ext {f g n A : U} (hf : isFinSeq f n A) (hg : isFinSeq g n A) (hval : ∀ i, i ∈ n → f⦅i⦆ = g⦅i⦆) : f = g` |

**Dependencias**: `IsFunction`, `function_domain_eq`, `apply_mem`, `apply_eq`, `CartesianProduct_is_specified`, `OrderedPair_mem_CartesianProduct`, `eq_of_subset_of_subset`, `isOrderedPair_by_construction`, `ω`

#### Sección 2: FinSeqSet

| Nombre | Descripción matemática | Firma Lean4 |
|--------|----------------------|-------------|
| `mem_FinSeqSet_iff` | $f \in \text{FinSeqSet}(n,A) \iff \text{isFinSeq}(f,n,A)$ | `theorem mem_FinSeqSet_iff {f n A : U} : f ∈ FinSeqSet n A ↔ isFinSeq f n A` |
| `isFinSeq_mem_FinSeqSet` | $\text{isFinSeq}(f,n,A) \Rightarrow f \in \text{FinSeqSet}(n,A)$ | `theorem isFinSeq_mem_FinSeqSet {f n A : U} (h : isFinSeq f n A) : f ∈ FinSeqSet n A` |

**Dependencias**: `mem_sep_iff`, `mem_powerset_iff`, `isFinSeq`

#### Sección 3: Secuencia vacía

| Nombre | Descripción matemática | Firma Lean4 |
|--------|----------------------|-------------|
| `isFinSeq_empty` | $\emptyset : \emptyset \to A$ es una 0-secuencia válida | `theorem isFinSeq_empty (A : U) : isFinSeq (∅ : U) (∅ : U) A` |
| `isFinSeq_zero_unique` | $f : \emptyset \to A \Rightarrow f = \emptyset$ | `theorem isFinSeq_zero_unique {f A : U} (h : isFinSeq f ∅ A) : f = ∅` |
| `FinSeqSet_zero` | $\text{FinSeqSet}(\emptyset, A) = \{\emptyset\}$ | `theorem FinSeqSet_zero (A : U) : FinSeqSet (∅ : U) A = {(∅ : U)}` |

**Dependencias**: `zero_in_Omega`, `EmptySet_is_empty`, `CartesianProduct_empty_left`, `eq_of_subset_of_subset`, `ExtSet`, `Singleton_is_specified`, `mem_FinSeqSet_iff`

#### Sección 4: appendElem

| Nombre | Descripción matemática | Firma Lean4 |
|--------|----------------------|-------------|
| `appendElem_is_specified` | $x \in \text{appendElem}(f,n,a) \iff x \in f \lor x = \langle n, a \rangle$ | `theorem appendElem_is_specified {f n a x : U} : x ∈ appendElem f n a ↔ x ∈ f ∨ x = ⟨n, a⟩` |
| `isFinSeq_appendElem` | $f : n \to A \land a \in A \Rightarrow \text{appendElem}(f,n,a) : \sigma(n) \to A$ | `theorem isFinSeq_appendElem {f n A a : U} (hf : isFinSeq f n A) (ha : a ∈ A) : isFinSeq (appendElem f n a) (σ n) A` |
| `appendElem_apply_last` | $(f \cup \{\langle n, a \rangle\})(n) = a$ | `theorem appendElem_apply_last {f n A a : U} (hf : isFinSeq f n A) : (appendElem f n a)⦅n⦆ = a` |
| `appendElem_apply_prev` | $i \in n \Rightarrow (f \cup \{\langle n, a \rangle\})(i) = f(i)$ | `theorem appendElem_apply_prev {f n A a i : U} (hf : isFinSeq f n A) (hi : i ∈ n) : (appendElem f n a)⦅i⦆ = f⦅i⦆` |
| `appendElem_inj` | $\text{appendElem}(f,n,a) = \text{appendElem}(f,n,b) \Rightarrow a = b$ | `theorem appendElem_inj {f n A a b : U} (hf : isFinSeq f n A) (h : appendElem f n a = appendElem f n b) : a = b` |

**Dependencias**: `mem_union_iff`, `Singleton_is_specified`, `mem_succ_iff`, `mem_succ_self`, `not_mem_self`, `mem_Omega_is_Nat`, `isNat_succ`, `Nat_in_Omega`, `CartesianProduct_is_specified`, `OrderedPair_mem_CartesianProduct`, `Eq_of_OrderedPairs_given_projections`, `apply_mem`, `apply_eq`, `mem_domain`, `isFinSeq_domain`

#### Sección 5: Descomposición

| Nombre | Descripción matemática | Firma Lean4 |
|--------|----------------------|-------------|
| `isFinSeq_restriction` | $f : \sigma(n) \to A \Rightarrow f{\upharpoonright}_n : n \to A$ | `theorem isFinSeq_restriction {f n A : U} (h : isFinSeq f (σ n) A) : isFinSeq (f ↾ n) n A` |

**Patrón de demostración**: Extrae `IsNat (σ n)` de `h.1`, deduce `IsNat n` por `nat_element_is_nat`, aplica `restrict_is_function` con `n ⊆ σ n` (por `nat_subset_succ`).

**Dependencias**: `mem_Omega_is_Nat`, `nat_element_is_nat`, `Nat_in_Omega`, `mem_succ_self`, `restrict_is_function`, `nat_subset_succ`

---

### 4.33 SetOps.FiniteSets.lean

**Módulo**: `ZfcSetTheory.SetOps.FiniteSets`
**Namespace**: `ZFC.SetOps.FiniteSets`
**Dependencias del módulo**: `Nat.Basic`, `Infinity` + anteriores

**Importancia por sección**:

- Sección 1 (biyección identidad, equipotent_refl): high — fundacional
- Sección 2 (propiedades básicas de finitud): medium — empty_is_finite, nat_is_finite
- Sección 3 (biyección inversa, equipotent_symm): high — fundacional
- Sección 4 (composición, equipotent_trans): high — fundacional
- Sección 5 (clausura bajo equipotencia): medium — finite_equipotent
- Sección 6 (singleton finito): medium — singleton_is_finite
- Sección 7 (adjunción de elemento): high — finite_union_singleton, construcción clave

#### Sección 1: Biyección identidad y equipotencia reflexiva

| Nombre | Descripción matemática | Firma Lean4 |
|--------|----------------------|-------------|
| `id_is_function` | $\mathbb{1}_A : A \to A$ | `theorem id_is_function (A : U) : IsFunction (idFn A) A A` |
| `id_is_injective` | $\mathbb{1}_A$ es inyectiva | `theorem id_is_injective (A : U) : isInjective (idFn A)` |
| `id_is_surjective` | $\mathbb{1}_A$ es suryectiva sobre $A$ | `theorem id_is_surjective (A : U) : isSurjectiveOnto (idFn A) A` |
| `id_is_bijection` | $\mathbb{1}_A$ es biyección de $A$ a $A$ | `theorem id_is_bijection (A : U) : isBijection (idFn A) A A` |
| `equipotent_refl` | $A \simeq_s A$ | `theorem equipotent_refl (A : U) : A ≃ₛ A` |

**Dependencias**: `idFn`, `IdRel`, `mem_IdRel`, `mem_sep_iff`

#### Sección 2: Propiedades básicas de finitud

| Nombre | Descripción matemática | Firma Lean4 |
|--------|----------------------|-------------|
| `empty_is_finite` | $\emptyset$ es finito | `theorem empty_is_finite : isFiniteSet (∅ : U)` |
| `nat_is_finite` | $n \in \omega \Rightarrow n$ es finito | `theorem nat_is_finite {n : U} (hn : n ∈ ω) : isFiniteSet n` |

**Dependencias**: `zero_in_Omega`, `equipotent_refl`

#### Sección 3: Biyección inversa y equipotencia simétrica

| Nombre | Descripción matemática | Firma Lean4 |
|--------|----------------------|-------------|
| `inverse_pair_iff` | $\langle y,x \rangle \in f^{-1} \iff \langle x,y \rangle \in f$ | `theorem inverse_pair_iff (f x y : U) : ⟨y, x⟩ ∈ f⁻¹ ↔ ⟨x, y⟩ ∈ f` |
| `bijection_inverse_is_function` | $f : A \xrightarrow{\sim} B \Rightarrow f^{-1} : B \to A$ | `theorem bijection_inverse_is_function {f A B : U} (hbij : isBijection f A B) : IsFunction (f⁻¹) B A` |
| `bijection_inverse_injective` | $f$ biyección $\Rightarrow f^{-1}$ inyectiva | `theorem bijection_inverse_injective {f A B : U} (hbij : isBijection f A B) : isInjective (f⁻¹)` |
| `bijection_inverse_surjective` | $f : A \xrightarrow{\sim} B \Rightarrow f^{-1}$ suryectiva sobre $A$ | `theorem bijection_inverse_surjective {f A B : U} (hbij : isBijection f A B) : isSurjectiveOnto (f⁻¹) A` |
| `bijection_inverse_is_bijection` | $f : A \xrightarrow{\sim} B \Rightarrow f^{-1} : B \xrightarrow{\sim} A$ | `theorem bijection_inverse_is_bijection {f A B : U} (hbij : isBijection f A B) : isBijection (f⁻¹) B A` |
| `equipotent_symm` | $A \simeq_s B \Rightarrow B \simeq_s A$ | `theorem equipotent_symm {A B : U} (h : A ≃ₛ B) : B ≃ₛ A` |

**Dependencias**: `inverse_is_specified`, `isOrderedPair_by_construction`, `OrderedPair_mem_CartesianProduct`, `injective_inverse_single_valued`, `snd_of_ordered_pair`, `fst_of_ordered_pair`

#### Sección 4: Composición y equipotencia transitiva

| Nombre | Descripción matemática | Firma Lean4 |
|--------|----------------------|-------------|
| `comp_injective` | $f,g$ inyectivas $\Rightarrow g \circ f$ inyectiva | `theorem comp_injective {f g : U} (hf_inj : isInjective f) (hg_inj : isInjective g) : isInjective (g ∘ f)` |
| `comp_surjective` | $f : A \twoheadrightarrow B,\; g : B \twoheadrightarrow C \Rightarrow g \circ f$ suryectiva sobre $C$ | `theorem comp_surjective {f g A B C : U} (_hf : IsFunction f A B) (hg : IsFunction g B C) (hsurj_f : isSurjectiveOnto f B) (hsurj_g : isSurjectiveOnto g C) : isSurjectiveOnto (g ∘ f) C` |
| `comp_bijection` | $f : A \xrightarrow{\sim} B,\; g : B \xrightarrow{\sim} C \Rightarrow g \circ f : A \xrightarrow{\sim} C$ | `theorem comp_bijection {f g A B C : U} (hf_bij : isBijection f A B) (hg_bij : isBijection g B C) : isBijection (g ∘ f) A C` |
| `equipotent_trans` | $A \simeq_s B \land B \simeq_s C \Rightarrow A \simeq_s C$ | `theorem equipotent_trans {A B C : U} (hab : A ≃ₛ B) (hbc : B ≃ₛ C) : A ≃ₛ C` |

**Dependencias**: `comp_is_specified`, `Eq_of_OrderedPairs_given_projections`, `comp_is_function`

#### Sección 5: Clausura bajo equipotencia

| Nombre | Descripción matemática | Firma Lean4 |
|--------|----------------------|-------------|
| `finite_equipotent` | $A$ finito $\land A \simeq_s B \Rightarrow B$ finito | `theorem finite_equipotent {A B : U} (hA : isFiniteSet A) (hab : A ≃ₛ B) : isFiniteSet B` |

**Dependencias**: `equipotent_symm`, `equipotent_trans`

#### Sección 6: Singleton finito

| Nombre | Descripción matemática | Firma Lean4 |
|--------|----------------------|-------------|
| `singleton_is_finite` | $\{a\}$ es finito ($\{a\} \simeq_s \sigma\emptyset$) | `theorem singleton_is_finite (a : U) : isFiniteSet ({a} : U)` |

**Patrón de demostración**: Construye la biyección explícita $f = \{\langle a, \emptyset \rangle\} : \{a\} \to \sigma\emptyset = \{∅\}$.

**Dependencias**: `Nat_in_Omega`, `isNat_succ`, `isNat_zero`, `Singleton_is_specified`, `mem_succ_self`, `Eq_of_OrderedPairs_given_projections`, `mem_succ_iff`, `EmptySet_is_empty`

#### Sección 7: Adjunción de elemento

| Nombre | Descripción matemática | Firma Lean4 |
|--------|----------------------|-------------|
| `finite_union_singleton` | $A$ finito $\land a \notin A \Rightarrow A \cup \{a\}$ finito | `theorem finite_union_singleton {A a : U} (hA : isFiniteSet A) (ha : a ∉ A) : isFiniteSet (A ∪ {a})` |

**Patrón de demostración**: Si $f : A \xrightarrow{\sim} n$ con $n \in \omega$, construye $g = f \cup \{\langle a, n \rangle\} : A \cup \{a\} \xrightarrow{\sim} \sigma n$. Demuestra función, inyectividad (usando $a \notin A$ y $n \notin n$) y suryectividad por casos sobre $\sigma n$.

**Dependencias**: `mem_Omega_is_Nat`, `isNat_succ`, `Nat_in_Omega`, `mem_union_iff`, `Singleton_is_specified`, `CartesianProduct_is_specified`, `OrderedPair_mem_CartesianProduct`, `Eq_of_OrderedPairs_given_projections`, `mem_succ_iff`, `not_mem_self`, `mem_succ_self`

---

### 4.34 Peano.FiniteSequencesArith.lean

**Módulo**: `ZfcSetTheory.Peano.FiniteSequencesArith`
**Namespace**: `ZFC.Peano.FiniteSequencesArith`
**Dependencias del módulo**: `Nat.Mul`, `Peano.FiniteSequences`, `SetOps.FiniteSets` + anteriores

**Importancia por sección**:

- Sección 1 (función de paso para sumación): medium — infraestructura
- Sección 2 (sumación de secuencias): high — seqSum_zero, seqSum_succ
- Sección 3 (función de paso para producto): medium — infraestructura
- Sección 4 (producto numérico de secuencias): high — seqProd_zero, seqProd_succ
- Sección 5 (producto cartesiano de familia): high — familyProduct, producto cartesiano generalizado
- Sección 6 (cardinalidad del producto): high — card_product_two, card_familyProduct

#### Sección 1: Función de paso para sumación

| Nombre | Descripción matemática | Firma Lean4 |
|--------|----------------------|-------------|
| `mem_sumStepFn` | $p \in \text{sumStepFn}(f) \iff p \in (\omega \times_s \omega) \times_s \omega \land \exists k\,v \in \omega,\; p = \langle\langle k,v\rangle, v + f(k)\rangle$ | `theorem mem_sumStepFn {f p : U} : p ∈ sumStepFn f ↔ (p ∈ (ω ×ₛ ω) ×ₛ ω ∧ ∃ k v, k ∈ (ω : U) ∧ v ∈ (ω : U) ∧ p = ⟨⟨k, v⟩, add v (f⦅k⦆)⟩)` |
| `sumStepFn_is_function` | $\text{sumStepFn}(f) : \omega \times_s \omega \to \omega$ | `theorem sumStepFn_is_function {f n : U} (hf : isFinSeq f n ω) : IsFunction (sumStepFn f) (ω ×ₛ ω) ω` |
| `sumStepFn_apply` | $\text{sumStepFn}(f)(\langle k,v \rangle) = v + f(k)$ | `theorem sumStepFn_apply {f n k v : U} (hf : isFinSeq f n ω) (hk : k ∈ (ω : U)) (hv : v ∈ (ω : U)) : (sumStepFn f)⦅⟨k, v⟩⦆ = add v (f⦅k⦆)` |

**Dependencias**: `mem_sep_iff`, `CartesianProduct_is_specified`, `add_in_Omega`, `apply_eq`

#### Sección 2: Sumación de secuencias

| Nombre | Descripción matemática | Firma Lean4 |
|--------|----------------------|-------------|
| `seqSumFn_is_function` | $\text{seqSumFn}(f) : \omega \to \omega$ | `theorem seqSumFn_is_function {f : U} (hf : isFinSeq f (domain f) ω) : IsFunction (seqSumFn f hf) ω ω` |
| `seqSum_zero` | $\text{seqSum}(f, \emptyset) = \emptyset$ (suma vacía = 0) | `theorem seqSum_zero {f : U} (hf : isFinSeq f ∅ ω) : seqSum f ∅ = ∅` |
| `seqSum_succ` | $\text{seqSum}(f, \sigma k) = \text{seqSum}(f, k) + f(k)$ | `theorem seqSum_succ {f k : U} (hf : isFinSeq f (σ k) ω) (hk : k ∈ (ω : U)) : seqSum f (σ k) = add (seqSum f k) (f⦅k⦆)` |
| `seqSum_in_Omega` | $\text{seqSum}(f, n) \in \omega$ | `theorem seqSum_in_Omega {f n : U} (hf : isFinSeq f n ω) : seqSum f n ∈ ω` |
| `seqSum_singleton` | $\text{seqSum}(f, \sigma\emptyset) = f(\emptyset)$ | `theorem seqSum_singleton {f : U} (hf : isFinSeq f (σ ∅) ω) : seqSum f (σ ∅) = f⦅∅⦆` |

**Dependencias**: `RecursionTheoremWithStep`, `sumStepFn_is_function`, `sumStepFn_apply`, `zero_add`

#### Sección 3: Función de paso para producto

| Nombre | Descripción matemática | Firma Lean4 |
|--------|----------------------|-------------|
| `mem_prodStepFn` | $p \in \text{prodStepFn}(f) \iff p \in (\omega \times_s \omega) \times_s \omega \land \exists k\,v \in \omega,\; p = \langle\langle k,v\rangle, v \cdot f(k)\rangle$ | `theorem mem_prodStepFn {f p : U} : p ∈ prodStepFn f ↔ (p ∈ (ω ×ₛ ω) ×ₛ ω ∧ ∃ k v, k ∈ (ω : U) ∧ v ∈ (ω : U) ∧ p = ⟨⟨k, v⟩, mul v (f⦅k⦆)⟩)` |
| `prodStepFn_is_function` | $\text{prodStepFn}(f) : \omega \times_s \omega \to \omega$ | `theorem prodStepFn_is_function {f n : U} (hf : isFinSeq f n ω) : IsFunction (prodStepFn f) (ω ×ₛ ω) ω` |
| `prodStepFn_apply` | $\text{prodStepFn}(f)(\langle k,v \rangle) = v \cdot f(k)$ | `theorem prodStepFn_apply {f n k v : U} (hf : isFinSeq f n ω) (hk : k ∈ (ω : U)) (hv : v ∈ (ω : U)) : (prodStepFn f)⦅⟨k, v⟩⦆ = mul v (f⦅k⦆)` |

**Dependencias**: `mem_sep_iff`, `CartesianProduct_is_specified`, `mul_in_Omega`, `apply_eq`

#### Sección 4: Producto numérico de secuencias

| Nombre | Descripción matemática | Firma Lean4 |
|--------|----------------------|-------------|
| `seqProdFn_is_function` | $\text{seqProdFn}(f) : \omega \to \omega$ | `theorem seqProdFn_is_function {f : U} (hf : isFinSeq f (domain f) ω) : IsFunction (seqProdFn f hf) ω ω` |
| `seqProd_zero` | $\text{seqProd}(f, \emptyset) = \sigma\emptyset$ (producto vacío = 1) | `theorem seqProd_zero {f : U} (hf : isFinSeq f ∅ ω) : seqProd f ∅ = (σ (∅ : U))` |
| `seqProd_succ` | $\text{seqProd}(f, \sigma k) = \text{seqProd}(f, k) \cdot f(k)$ | `theorem seqProd_succ {f k : U} (hf : isFinSeq f (σ k) ω) (hk : k ∈ (ω : U)) : seqProd f (σ k) = mul (seqProd f k) (f⦅k⦆)` |
| `seqProd_in_Omega` | $\text{seqProd}(f, n) \in \omega$ | `theorem seqProd_in_Omega {f n : U} (hf : isFinSeq f n ω) : seqProd f n ∈ ω` |
| `seqProd_singleton` | $\text{seqProd}(f, \sigma\emptyset) = f(\emptyset)$ | `theorem seqProd_singleton {f : U} (hf : isFinSeq f (σ ∅) ω) : seqProd f (σ ∅) = f⦅∅⦆` |

**Dependencias**: `RecursionTheoremWithStep`, `prodStepFn_is_function`, `prodStepFn_apply`, `one_mul_Omega`

#### Sección 5: Producto cartesiano de una familia

| Nombre | Descripción matemática | Firma Lean4 |
|--------|----------------------|-------------|
| `mem_familyProduct` | $g \in \prod_{i<n} F(i) \iff g \in \text{FinSeqSet}(n, \bigcup\text{Im}(F,n)) \land \forall i \in n,\; g(i) \in F(i)$ | `theorem mem_familyProduct {F n g : U} : g ∈ familyProduct F n ↔ (g ∈ FinSeqSet n (⋃ (image F n)) ∧ ∀ i, i ∈ n → g⦅i⦆ ∈ F⦅i⦆)` |
| `familyProduct_zero` | $\prod_{i<\emptyset} F(i) = \{\emptyset\}$ (producto vacío = singleton de función vacía) | `theorem familyProduct_zero (F : U) : familyProduct F (∅ : U) = ({∅} : U)` |
| `familyProduct_succ_char` | $g \in \prod_{i<\sigma n} F(i) \Rightarrow (g{\upharpoonright}n) \in \prod_{i<n} F(i) \land g(n) \in F(n)$ | `theorem familyProduct_succ_char {F n : U} (hn : n ∈ (ω : U)) (hF : isFinSeq F (σ n) (⋃ (image F (σ n)))) : ∀ g, g ∈ familyProduct F (σ n) → (g ↾ n) ∈ familyProduct F n ∧ g⦅n⦆ ∈ F⦅n⦆` |

**Dependencias**: `mem_sep_iff`, `FinSeqSet`, `isFinSeq_restriction`, `restrict_apply`

#### Sección 6: Teorema de cardinalidad del producto

| Nombre | Descripción matemática | Firma Lean4 |
|--------|----------------------|-------------|
| `card_product_two` | $A \simeq_s n \land B \simeq_s m \Rightarrow A \times_s B \simeq_s n \cdot m$ | `theorem card_product_two {A B n m : U} (hn : n ∈ (ω : U)) (hm : m ∈ (ω : U)) (hA : A ≃ₛ n) (hB : B ≃ₛ m) : (A ×ₛ B) ≃ₛ mul n m` |
| `card_familyProduct` | $\forall i \in n,\; F(i) \simeq_s c(i) \Rightarrow \prod_{i<n} F(i) \simeq_s \prod_{i<n} c(i)$ | `theorem card_familyProduct {F c n : U} (hn : n ∈ (ω : U)) (hF : isFinSeq F n (⋃ (image F n))) (hc : isFinSeq c n ω) (hcard : ∀ i, i ∈ n → F⦅i⦆ ≃ₛ c⦅i⦆) : familyProduct F n ≃ₛ seqProd c n` |

**Patrón de demostración**: Inducción ZFC sobre $\omega$ (sep + induction_principle). `card_product_two` usa doble inducción sobre $m$ con `disjoint_union_equip` y `product_singleton_equip` como lemas privados. `card_familyProduct` usa inducción simple con `familyProduct_succ_decomp` (biyección privada) y `card_product_two` en el paso inductivo.

**Dependencias**: `induction_principle`, `equipotent_refl`, `equipotent_symm`, `equipotent_trans`, `CartesianProduct_distrib_union_right`, `isFinSeq_restriction`, `seqProd_restriction`, `familyProduct_restriction`

### 4.35 Peano.FiniteSequencesBridge.lean

**Módulo**: `ZfcSetTheory.Peano.FiniteSequencesBridge`
**Namespace**: `ZFC.Peano.FiniteSequencesBridge`
**Dependencias del módulo**: `Peano.FiniteSequencesArith`, `Nat.Primes` + anteriores

**Importancia por sección**:

- Sección 1 (nth — acceso a elementos): medium — alias de apply
- Sección 2 (recursión general de seqProd): medium — versiones genéricas
- Sección 3 (extensionalidad de seqProd): medium — seqProd_ext
- Sección 4 (DList → ZFC bridge): high — dlistToSeq, puente DList↔secuencias ZFC
- Sección 5 (correspondencia de seqProd): high — dlistToSeq_seqProd
- Sección 6 (isPrimeSeq y conversión): high — dlistToSeq_isPrimeSeq
- Sección 7 (TFA con secuencias ZFC-nativas): high — resultado principal

#### Sección 1: nth — Acceso a elementos

| Nombre | Descripción matemática | Firma Lean4 |
|--------|----------------------|-------------|
| `nth_eq_apply` | $\text{nth}(f, i) = f(i)$ | `theorem nth_eq_apply (f i : U) : nth f i = f⦅i⦆` |
| `nth_mem` | $\text{isFinSeq}(f,n,A) \land i \in n \Rightarrow \text{nth}(f,i) \in A$ | `theorem nth_mem {f n A i : U} (h : isFinSeq f n A) (hi : i ∈ n) : nth f i ∈ A` |
| `nth_appendElem_last` | $\text{nth}(\text{appendElem}(f,n,a), n) = a$ | `theorem nth_appendElem_last {f n A a : U} (hf : isFinSeq f n A) : nth (appendElem f n a) n = a` |
| `nth_appendElem_prev` | $i \in n \Rightarrow \text{nth}(\text{appendElem}(f,n,a), i) = \text{nth}(f, i)$ | `theorem nth_appendElem_prev {f n A a i : U} (hf : isFinSeq f n A) (hi : i ∈ n) : nth (appendElem f n a) i = nth f i` |

**Dependencias**: `apply`, `isFinSeq_apply_mem`, `appendElem_apply_last`, `appendElem_apply_prev`

#### Sección 2: Recursión general de seqProd

| Nombre | Descripción matemática | Firma Lean4 |
|--------|----------------------|-------------|
| `seqProd_zero_gen` | $\text{seqProd}(f, \emptyset) = \sigma\emptyset$ (versión general) | `theorem seqProd_zero_gen {f : U} (hf : isFinSeq f (domain f) ω) : seqProd f ∅ = σ (∅ : U)` |
| `seqProd_succ_gen` | $\text{seqProd}(f, \sigma k) = \text{seqProd}(f, k) \cdot f(k)$ (versión general) | `theorem seqProd_succ_gen {f : U} (hf : isFinSeq f (domain f) ω) (k : U) (hk : k ∈ (ω : U)) : seqProd f (σ k) = mul (seqProd f k) (f⦅k⦆)` |
| `seqProd_in_Omega_gen` | $\text{seqProd}(f, k) \in \omega$ (versión general) | `theorem seqProd_in_Omega_gen {f : U} (hf : isFinSeq f (domain f) ω) (k : U) (hk : k ∈ (ω : U)) : seqProd f k ∈ (ω : U)` |

**Dependencias**: `RecursionTheoremWithStep`, `seqProdFn`, `prodStepFn_apply`

#### Sección 3: Extensionalidad de seqProd

| Nombre | Descripción matemática | Firma Lean4 |
|--------|----------------------|-------------|
| `seqProd_ext` | $(\forall i \in n,\; f(i) = g(i)) \Rightarrow \text{seqProd}(f,n) = \text{seqProd}(g,n)$ | `theorem seqProd_ext {f g : U} (hf : isFinSeq f (domain f) ω) (hg : isFinSeq g (domain g) ω) (n : U) (hn : n ∈ (ω : U)) (h_agree : ∀ i, i ∈ n → f⦅i⦆ = g⦅i⦆) : seqProd f n = seqProd g n` |

**Patrón de demostración**: Inducción ZFC sobre $\omega$ (sep + induction_principle). Usa `seqProd_zero_gen` y `seqProd_succ_gen` en los casos base e inductivo.

#### Sección 4: DList → ZFC bridge

| Nombre | Descripción matemática | Firma Lean4 |
|--------|----------------------|-------------|
| `dlistToSeq_isFinSeq` | $\text{dlistToSeq}(ps)$ es secuencia finita en $\omega$ de longitud $\text{dlistLen}(ps)$ | `theorem dlistToSeq_isFinSeq : (ps : DList Peano.ℕ₀) → isFinSeq (dlistToSeq ps : U) (dlistLen ps) (ω : U)` |
| `dlistToSeq_domain` | $\text{domain}(\text{dlistToSeq}(ps)) = \text{dlistLen}(ps)$ | `theorem dlistToSeq_domain (ps : DList Peano.ℕ₀) : domain (dlistToSeq ps : U) = dlistLen ps` |
| `dlistToSeq_isFinSeq_domain` | $\text{isFinSeq}(\text{dlistToSeq}(ps), \text{domain}(\text{dlistToSeq}(ps)), \omega)$ | `theorem dlistToSeq_isFinSeq_domain (ps : DList Peano.ℕ₀) : isFinSeq (dlistToSeq ps : U) (domain (dlistToSeq ps)) (ω : U)` |
| `dlistToSeq_seqLength` | $\text{seqLength}(\text{dlistToSeq}(ps)) = \text{dlistLen}(ps)$ | `theorem dlistToSeq_seqLength (ps : DList Peano.ℕ₀) : seqLength (dlistToSeq ps : U) = dlistLen ps` |
| `dlistLen_in_Omega` | $\text{dlistLen}(ps) \in \omega$ | `theorem dlistLen_in_Omega (ps : DList Peano.ℕ₀) : (dlistLen ps : U) ∈ (ω : U)` |
| `dlistToSeq_apply_last` | $(\text{dlistToSeq}(\text{cons}\;x\;xs))({\text{dlistLen}(xs)}) = \text{fromPeano}(x)$ | `theorem dlistToSeq_apply_last (x : Peano.ℕ₀) (xs : DList Peano.ℕ₀) : (dlistToSeq (.cons x xs) : U)⦅dlistLen xs⦆ = (fromPeano x : U)` |
| `dlistToSeq_apply_prev` | $i \in \text{dlistLen}(xs) \Rightarrow (\text{dlistToSeq}(\text{cons}\;x\;xs))(i) = (\text{dlistToSeq}(xs))(i)$ | `theorem dlistToSeq_apply_prev (x : Peano.ℕ₀) (xs : DList Peano.ℕ₀) (i : U) (hi : i ∈ (dlistLen xs : U)) : (dlistToSeq (.cons x xs) : U)⦅i⦆ = (dlistToSeq xs : U)⦅i⦆` |

**Dependencias**: `appendElem`, `appendElem_apply_last`, `appendElem_apply_prev`, `isFinSeq_appendElem`, `fromPeano_is_nat`, `seqLength_eq`

#### Sección 5: Correspondencia de seqProd

| Nombre | Descripción matemática | Firma Lean4 |
|--------|----------------------|-------------|
| `dlistToSeq_seqProd` | $\text{seqProd}(\text{dlistToSeq}(ps), \text{dlistLen}(ps)) = \text{fromPeano}(\text{product\_list}(ps))$ | `theorem dlistToSeq_seqProd : (ps : DList Peano.ℕ₀) → seqProd (dlistToSeq ps : U) (dlistLen ps) = (fromPeano (product_list ps) : U)` |

**Patrón de demostración**: Recursión sobre `DList`. Caso nil: `seqProd_zero` + axiomas de `product_list`. Caso cons: `seqProd_succ_gen` + `dlistToSeq_apply_last` + `seqProd_ext` + hipótesis inductiva + `product_cons` + `fromPeano_mul` + `mul_comm`.

#### Sección 6: isPrimeSeq y conversión de DList

| Nombre | Descripción matemática | Firma Lean4 |
|--------|----------------------|-------------|
| `dlistToSeq_isPrimeSeq` | $\text{PrimeList}(ps) \Rightarrow \text{isPrimeSeq}(\text{dlistToSeq}(ps), \text{dlistLen}(ps))$ | `theorem dlistToSeq_isPrimeSeq : (ps : DList Peano.ℕ₀) → PrimeList ps → isPrimeSeq (dlistToSeq ps : U) (dlistLen ps)` |

**Dependencias**: `dlistToSeq_isFinSeq`, `mem_succ_iff`, `dlistToSeq_apply_last`, `dlistToSeq_apply_prev`, `fromPeano_prime`

#### Sección 7: TFA con secuencias ZFC-nativas

| Nombre | Descripción matemática | Firma Lean4 |
|--------|----------------------|-------------|
| `exists_prime_factorization_native` | $n \in \omega \land n \ge 2 \Rightarrow \exists f\,k,\; \text{isPrimeSeq}(f,k) \land \text{seqProd}(f,k) = n$ | `theorem exists_prime_factorization_native (n : U) (hn : n ∈ (ω : U)) (h_ge2 : σ (σ (∅ : U)) ∈ n ∨ σ (σ (∅ : U)) = n) : ∃ f k : U, isPrimeSeq f k ∧ seqProd f k = n` |
| `unique_prime_factorization_native` | Unicidad: dos DList primos con mismo seqProd tienen misma multiplicidad por primo | `theorem unique_prime_factorization_native (ps qs : DList Peano.ℕ₀) (hps : PrimeList ps) (hqs : PrimeList qs) (h_prod : seqProd (dlistToSeq ps : U) (dlistLen ps) = seqProd (dlistToSeq qs : U) (dlistLen qs)) (p : Peano.ℕ₀) (hp : Peano.Arith.Prime p) : DList.length (DList.filter (fun q => decide (q = p)) ps) = DList.length (DList.filter (fun q => decide (q = p)) qs)` |

**Dependencias**: `exists_prime_factorization_ZFC`, `unique_prime_factorization_ZFC`, `dlistToSeq_isPrimeSeq`, `dlistToSeq_seqProd`

### 4.36 BoolAlg.FiniteCofinite.lean

**Módulo**: `ZfcSetTheory.BoolAlg.FiniteCofinite`
**Namespace**: `ZFC.BoolAlg.FiniteCofinite`
**Dependencias del módulo**: `BoolAlg.Complete`, `SetOps.FiniteSets`, `Nat.Add`, `Cardinality` + anteriores

**Importancia por sección**:

- Sección 1 (clausura de conjuntos finitos): high — finite_subset, finite_union, Omega_not_finite
- Sección 2 (paridad en ω): high — even_or_odd, double_injective, EvenSet_infinite
- Sección 3 (estructura de álgebra booleana): high — FinCofAlg cerrada bajo ∪, ∩, complemento
- Sección 4 (no es retículo completo): high — FinCofAlg_not_complete, resultado negativo principal

#### Sección 1: Clausura de conjuntos finitos

| Nombre | Descripción matemática | Firma Lean4 |
|--------|----------------------|-------------|
| `finite_subset` | $\text{isFiniteSet}(A) \land B \subset A \Rightarrow \text{isFiniteSet}(B)$ | `theorem finite_subset {A B : U} (hA : isFiniteSet A) (hB : B ⊆ A) : isFiniteSet B` |
| `finite_union` | $\text{isFiniteSet}(A) \land \text{isFiniteSet}(B) \Rightarrow \text{isFiniteSet}(A \cup B)$ | `theorem finite_union {A B : U} (hA : isFiniteSet A) (hB : isFiniteSet B) : isFiniteSet (A ∪ B)` |
| `Omega_not_finite` | $\neg\text{isFiniteSet}(\omega)$ | `theorem Omega_not_finite : ¬isFiniteSet (ω : U)` |

**Dependencias**: `isFiniteSet`, `equipotent_comm`, `no_injection_succ_to_nat`, `strong_induction_principle`, `induction_principle`, `empty_is_finite`, `finite_union_singleton`

#### Sección 2: Paridad en ω

| Nombre | Descripción matemática | Firma Lean4 |
|--------|----------------------|-------------|
| `even_ne_odd` | $\forall k \in \omega,\; \forall j \in \omega,\; k+k \neq \sigma(j+j)$ | `theorem even_ne_odd : ∀ k, k ∈ (ω : U) → ∀ j, j ∈ (ω : U) → add k k ≠ σ (add j j)` |
| `even_or_odd` | $\forall n \in \omega,\; (\exists k \in \omega,\; n = k+k) \lor (\exists k \in \omega,\; n = \sigma(k+k))$ | `theorem even_or_odd (n : U) (hn : n ∈ ω) : (∃ k, k ∈ (ω : U) ∧ n = add k k) ∨ (∃ k, k ∈ (ω : U) ∧ n = σ (add k k))` |
| `double_injective` | $\forall k, j \in \omega,\; k+k = j+j \Rightarrow k = j$ | `theorem double_injective : ∀ k, k ∈ (ω : U) → ∀ j, j ∈ (ω : U) → add k k = add j j → k = j` |
| `EvenSet_is_specified` | $n \in \text{EvenSet} \iff n \in \omega \land \exists k \in \omega,\; n = k+k$ | `theorem EvenSet_is_specified (n : U) : n ∈ (EvenSet : U) ↔ n ∈ (ω : U) ∧ ∃ k, k ∈ (ω : U) ∧ n = add k k` |
| `EvenSet_subset_Omega` | $\text{EvenSet} \subset \omega$ | `theorem EvenSet_subset_Omega : (EvenSet : U) ⊆ ω` |
| `EvenSet_infinite` | $\neg\text{isFiniteSet}(\text{EvenSet})$ | `theorem EvenSet_infinite : ¬isFiniteSet (EvenSet : U)` |
| `OddSet_infinite` | $\neg\text{isFiniteSet}(\omega \setminus \text{EvenSet})$ | `theorem OddSet_infinite : ¬isFiniteSet (sdiff (ω : U) (EvenSet : U))` |

**Dependencias**: `add`, `add_succ`, `add_comm_Omega`, `add_zero`, `succ_injective`, `succ_nonempty`, `induction_principle`, `no_injection_succ_to_nat`

#### Sección 3: Estructura de álgebra booleana

| Nombre | Descripción matemática | Firma Lean4 |
|--------|----------------------|-------------|
| `FinCofAlg_is_specified` | $X \in \text{FinCofAlg}(A) \iff X \in \mathcal{P}(A) \land (\text{isFiniteSet}(X) \lor \text{isCofinite}(A, X))$ | `theorem FinCofAlg_is_specified (A X : U) : X ∈ FinCofAlg A ↔ X ∈ 𝒫 A ∧ (isFiniteSet X ∨ isCofinite A X)` |
| `FinCofAlg_subset_powerset` | $\text{FinCofAlg}(A) \subset \mathcal{P}(A)$ | `theorem FinCofAlg_subset_powerset (A : U) : FinCofAlg A ⊆ 𝒫 A` |
| `FinCofAlg_empty` | $\emptyset \in \text{FinCofAlg}(A)$ | `theorem FinCofAlg_empty (A : U) : (∅ : U) ∈ FinCofAlg A` |
| `FinCofAlg_universe` | $A \in \text{FinCofAlg}(A)$ | `theorem FinCofAlg_universe (A : U) : A ∈ FinCofAlg A` |
| `FinCofAlg_complement` | $X \in \text{FinCofAlg}(A) \Rightarrow X^{\complement[A]} \in \text{FinCofAlg}(A)$ | `theorem FinCofAlg_complement (A X : U) (hX : X ∈ FinCofAlg A) : (X ^∁[ A ]) ∈ FinCofAlg A` |
| `FinCofAlg_union` | $X, Y \in \text{FinCofAlg}(A) \Rightarrow X \cup Y \in \text{FinCofAlg}(A)$ | `theorem FinCofAlg_union (A X Y : U) (hX : X ∈ FinCofAlg A) (hY : Y ∈ FinCofAlg A) : (X ∪ Y) ∈ FinCofAlg A` |
| `FinCofAlg_inter` | $X, Y \in \text{FinCofAlg}(A) \Rightarrow X \cap Y \in \text{FinCofAlg}(A)$ | `theorem FinCofAlg_inter (A X Y : U) (hX : X ∈ FinCofAlg A) (hY : Y ∈ FinCofAlg A) : (X ∩ Y) ∈ FinCofAlg A` |

**Dependencias**: `mem_sep_iff`, `mem_powerset_iff`, `empty_is_finite`, `empty_mem_powerset`, `self_mem_powerset`, `sdiff_self`, `complement_mem_powerset`, `Complement_is_specified`, `union_mem_powerset`, `inter_mem_powerset`, `finite_subset`, `finite_union`

#### Sección 4: No es retículo completo

| Nombre | Descripción matemática | Firma Lean4 |
|--------|----------------------|-------------|
| `EvenSet_not_in_FinCofAlg` | $\text{EvenSet} \notin \text{FinCofAlg}(\omega)$ | `theorem EvenSet_not_in_FinCofAlg : (EvenSet : U) ∉ FinCofAlg (ω : U)` |
| `FinCofAlg_not_complete` | $\neg\text{isCompleteLattice}(\text{FinCofAlg}(\omega))$ | `theorem FinCofAlg_not_complete : ¬isCompleteLattice (FinCofAlg (ω : U))` |

**Dependencias**: `EvenSet_infinite`, `OddSet_infinite`, `isCompleteLattice`, `singleton_is_finite`, `FinCofAlg_subset_powerset`, `mem_powerset_iff`

**Patrón de demostración de `FinCofAlg_not_complete`**: Por contradicción. Se define $S = \{\{x\} \mid x \in \text{EvenSet}\} \subset \text{FinCofAlg}(\omega)$. Si FinCofAlg fuera completo, $S$ tendría un supremo $Z \in \text{FinCofAlg}(\omega)$. Entonces $\text{EvenSet} \subset Z$ pero $Z \neq \text{EvenSet}$ (pues $\text{EvenSet} \notin \text{FinCofAlg}$), así que $\exists z \in Z \setminus \text{EvenSet}$. Se construye $Z' = Z \setminus \{z\}$, que es cofinito (y por tanto $\in \text{FinCofAlg}$) y sigue siendo cota superior de $S$. Pero entonces $Z \subset Z'$ por minimalidad, contradiciendo $z \in Z \setminus Z'$.

### 4.37 BoolAlg.Complete.lean

**Importancia por teorema**:

- supremumIn_unique: medium — unicidad del supremo
- infimumIn_unique: medium — unicidad del ínfimo
- sUnion_subset_of_family: low — lema auxiliar
- sUnion_mem_powerset_of_family: low — lema auxiliar
- sUnion_is_supremumIn_powerset: high — ⋃S es el supremo en 𝒫(A)
- interSet_subset_of_family: low — lema auxiliar
- interSet_mem_powerset_of_family: low — lema auxiliar
- interSet_is_infimumIn_powerset: high — ⋂S es el ínfimo en 𝒫(A)
- universe_is_infimumIn_powerset_empty: medium — caso especial familia vacía
- powerset_is_complete_lattice: high — teorema fundamental
- powerset_is_complete_atomic_BA: high — corolario culminante

#### Unicidad del Supremo (supremumIn_unique)

**Ubicación**: `BoolAlg.Complete.lean`, línea 83
**Orden**: 1º teorema

**Enunciado Matemático**: Si $x$ e $y$ son ambos supremos de $S$ en $L$, entonces $x = y$.

**Firma Lean4**:

```lean
theorem supremumIn_unique (L S x y : U)
    (hx : isSupremumIn L S x) (hy : isSupremumIn L S y) :
    x = y
```

**Dependencias**: `isSupremumIn`, `order_antisymmetric`

#### Unicidad del Ínfimo (infimumIn_unique)

**Ubicación**: `BoolAlg.Complete.lean`, línea 90
**Orden**: 2º teorema

**Enunciado Matemático**: Si $x$ e $y$ son ambos ínfimos de $S$ en $L$, entonces $x = y$.

**Firma Lean4**:

```lean
theorem infimumIn_unique (L S x y : U)
    (hx : isInfimumIn L S x) (hy : isInfimumIn L S y) :
    x = y
```

**Dependencias**: `isInfimumIn`, `order_antisymmetric`

#### Unión de Familia Acotada (sUnion_subset_of_family)

**Ubicación**: `BoolAlg.Complete.lean`, línea 99
**Orden**: 3º teorema

**Enunciado Matemático**: Si $F \subset \mathcal{P}(A)$, entonces $\bigcup F \subset A$.

**Firma Lean4**:

```lean
theorem sUnion_subset_of_family (A F : U) (hF : F ⊆ 𝒫 A) :
    ⋃ F ⊆ A
```

**Dependencias**: `mem_sUnion_iff`, `mem_powerset_iff`

#### Unión de Familia en Conjunto Potencia (sUnion_mem_powerset_of_family)

**Ubicación**: `BoolAlg.Complete.lean`, línea 107
**Orden**: 4º teorema

**Enunciado Matemático**: Si $S \subset \mathcal{P}(A)$, entonces $\bigcup S \in \mathcal{P}(A)$.

**Firma Lean4**:

```lean
theorem sUnion_mem_powerset_of_family (A S : U) (hS : S ⊆ 𝒫 A) :
    ⋃ S ∈ 𝒫 A
```

**Dependencias**: `mem_powerset_iff`, `sUnion_subset_of_family`

#### Unión como Supremo en 𝒫(A) (sUnion_is_supremumIn_powerset)

**Ubicación**: `BoolAlg.Complete.lean`, línea 112
**Orden**: 5º teorema (TEOREMA PRINCIPAL: supremo)

**Enunciado Matemático**: Si $S \subset \mathcal{P}(A)$, entonces $\bigcup S$ es el supremo de $S$ en $\mathcal{P}(A)$.

**Firma Lean4**:

```lean
theorem sUnion_is_supremumIn_powerset (A S : U) (hS : S ⊆ 𝒫 A) :
    isSupremumIn (𝒫 A) S (⋃ S)
```

**Dependencias**: `sUnion_mem_powerset_of_family`, `mem_sUnion_iff`

**Patrón de demostración**: Para la cota superior, cada $X \in S$ satisface $X \subset \bigcup S$ por definición de $\bigcup$. Para la minimalidad, si $z$ es cota superior de $S$, cada $w \in \bigcup S$ pertenece a algún $X \in S$, y por tanto $w \in z$ por la cota.

#### Intersección de Familia Acotada (interSet_subset_of_family)

**Ubicación**: `BoolAlg.Complete.lean`, línea 127
**Orden**: 6º teorema

**Enunciado Matemático**: Si $F \subset \mathcal{P}(A)$ y $F \neq \emptyset$, entonces $\bigcap F \subset A$.

**Firma Lean4**:

```lean
theorem interSet_subset_of_family (A F : U) (hF : F ⊆ 𝒫 A) (hne : F ≠ ∅) :
    (⋂ F) ⊆ A
```

**Dependencias**: `nonempty_iff_exists_mem`, `interSet_mem_iff`, `mem_powerset_iff`

#### Intersección de Familia en Conjunto Potencia (interSet_mem_powerset_of_family)

**Ubicación**: `BoolAlg.Complete.lean`, línea 136
**Orden**: 7º teorema

**Enunciado Matemático**: Si $S \subset \mathcal{P}(A)$ y $S \neq \emptyset$, entonces $\bigcap S \in \mathcal{P}(A)$.

**Firma Lean4**:

```lean
theorem interSet_mem_powerset_of_family (A S : U) (hS : S ⊆ 𝒫 A) (hne : S ≠ ∅) :
    (⋂ S) ∈ 𝒫 A
```

**Dependencias**: `mem_powerset_iff`, `interSet_subset_of_family`

#### Intersección como Ínfimo en 𝒫(A) (interSet_is_infimumIn_powerset)

**Ubicación**: `BoolAlg.Complete.lean`, línea 141
**Orden**: 8º teorema (TEOREMA PRINCIPAL: ínfimo no vacío)

**Enunciado Matemático**: Si $S \subset \mathcal{P}(A)$ y $S \neq \emptyset$, entonces $\bigcap S$ es el ínfimo de $S$ en $\mathcal{P}(A)$.

**Firma Lean4**:

```lean
theorem interSet_is_infimumIn_powerset (A S : U) (hS : S ⊆ 𝒫 A) (hne : S ≠ ∅) :
    isInfimumIn (𝒫 A) S (⋂ S)
```

**Dependencias**: `interSet_mem_powerset_of_family`, `interSet_mem_iff`

**Patrón de demostración**: Para la cota inferior, $\bigcap S \subset X$ para cada $X \in S$ por definición de $\bigcap$. Para la maximalidad, si $z$ es cota inferior de $S$, cada $w \in z$ pertenece a todos los $X \in S$, y por tanto $w \in \bigcap S$.

#### Ínfimo de la Familia Vacía (universe_is_infimumIn_powerset_empty)

**Ubicación**: `BoolAlg.Complete.lean`, línea 155
**Orden**: 9º teorema (CASO ESPECIAL: familia vacía)

**Enunciado Matemático**: $A$ es el ínfimo de $\emptyset$ en $\mathcal{P}(A)$.

**Firma Lean4**:

```lean
theorem universe_is_infimumIn_powerset_empty (A : U) :
    isInfimumIn (𝒫 A) ∅ A
```

**Dependencias**: `self_mem_powerset`, `EmptySet_is_empty`, `mem_powerset_iff`

**Patrón de demostración**: La cota inferior es vacuamente verdadera ($\forall Y \in \emptyset$ es vacuo). Para la maximalidad, si $z \in \mathcal{P}(A)$, entonces $z \subset A$ por definición de $\mathcal{P}$.

#### Retículo Completo de 𝒫(A) (powerset_is_complete_lattice)

**Ubicación**: `BoolAlg.Complete.lean`, línea 166
**Orden**: 10º teorema (TEOREMA FUNDAMENTAL)

**Enunciado Matemático**: Para todo conjunto $A$, $\mathcal{P}(A)$ es un retículo completo.

**Firma Lean4**:

```lean
theorem powerset_is_complete_lattice (A : U) : isCompleteLattice (𝒫 A)
```

**Dependencias**: `sUnion_is_supremumIn_powerset`, `interSet_is_infimumIn_powerset`, `universe_is_infimumIn_powerset_empty`

**Patrón de demostración**: Dado $S \subset \mathcal{P}(A)$: el supremo es siempre $\bigcup S$; para el ínfimo se distingue $S = \emptyset$ (ínfimo = $A$) de $S \neq \emptyset$ (ínfimo = $\bigcap S$).

#### 𝒫(A) es Álgebra Booleana Completa Atómica (powerset_is_complete_atomic_BA)

**Ubicación**: `BoolAlg.Complete.lean`, línea 183
**Orden**: 11º teorema (COROLARIO CULMINANTE)

**Enunciado Matemático**: Para todo conjunto $A$, $\mathcal{P}(A)$ es un álgebra booleana completa atómica.

**Firma Lean4**:

```lean
theorem powerset_is_complete_atomic_BA (A : U) : isCompleteAtomicBA A
```

**Dependencias**: `powerset_is_complete_lattice`, `powerset_is_atomic`

**Patrón de demostración**: Directa: combina `powerset_is_complete_lattice` (retículo completo) con `powerset_is_atomic` (de `BoolAlg.Atomic.lean`, atomicidad).

### 4.38 BoolAlg.FiniteBA.lean

**Importancia por teorema**:

- atoms_equipotent_base: medium — inversa de A_equipotent_Atoms
- finite_atoms_of_finite: medium — clausura de finitud
- finite_of_finite_atoms: medium — clausura de finitud
- BA_cardinality_via_atoms: high — |𝒫(A)| = 2^n vía átomos
- finite_powerset_is_finite: high — 𝒫(A) finito si A finito
- finite_BA_cardinality: high — resultado principal |𝒫(A)| = 2^n
- finite_BA_cardinality_atoms: high — con testigo de átomos
- finite_complete_atomic_BA: high — corolario culminante

#### Átomos Equipotentes a la Base (atoms_equipotent_base)

**Ubicación**: `BoolAlg.FiniteBA.lean`, línea 52
**Orden**: 1º teorema

**Enunciado Matemático**: $\text{Atoms}(A) \simeq_s A$ (inversa de `A_equipotent_Atoms`).

**Firma Lean4**:

```lean
theorem atoms_equipotent_base (A : U) : Atoms A ≃ₛ A
```

**Dependencias**: `equipotent_symm`, `A_equipotent_Atoms`

#### Finitud de Átomos (finite_atoms_of_finite)

**Ubicación**: `BoolAlg.FiniteBA.lean`, línea 56
**Orden**: 2º teorema

**Enunciado Matemático**: Si $A$ es finito, entonces $\text{Atoms}(A)$ es finito.

**Firma Lean4**:

```lean
theorem finite_atoms_of_finite {A : U} (hA : isFiniteSet A) :
    isFiniteSet (Atoms A)
```

**Dependencias**: `finite_equipotent`, `A_equipotent_Atoms`

#### Finitud desde Átomos (finite_of_finite_atoms)

**Ubicación**: `BoolAlg.FiniteBA.lean`, línea 61
**Orden**: 3º teorema

**Enunciado Matemático**: Si $\text{Atoms}(A)$ es finito, entonces $A$ es finito.

**Firma Lean4**:

```lean
theorem finite_of_finite_atoms {A : U} (hAt : isFiniteSet (Atoms A)) :
    isFiniteSet A
```

**Dependencias**: `finite_equipotent`, `atoms_equipotent_base`

#### Cardinalidad vía Átomos (BA_cardinality_via_atoms)

**Ubicación**: `BoolAlg.FiniteBA.lean`, línea 72
**Orden**: 4º teorema

**Enunciado Matemático**: Si $\text{Atoms}(A) \simeq_s n$ con $n \in \omega$, entonces $\mathcal{P}(A) \simeq_s 2^n$. Demostración vía teorema de representación: $\mathcal{P}(A) \simeq_s \mathcal{P}(\text{Atoms}(A)) \simeq_s 2^n$.

**Firma Lean4**:

```lean
theorem BA_cardinality_via_atoms {A n : U} (hn : n ∈ ω)
    (hAtoms : Atoms A ≃ₛ n) :
    𝒫 A ≃ₛ pow (σ (σ (∅ : U))) n
```

**Dependencias**: `equipotent_trans`, `representation_equipotent`, `powerset_cardinality`

#### Finitud del Conjunto Potencia (finite_powerset_is_finite)

**Ubicación**: `BoolAlg.FiniteBA.lean`, línea 82
**Orden**: 5º teorema

**Enunciado Matemático**: Si $A$ es finito, entonces $\mathcal{P}(A)$ es finito.

**Firma Lean4**:

```lean
theorem finite_powerset_is_finite {A : U} (hA : isFiniteSet A) :
    isFiniteSet (𝒫 A)
```

**Dependencias**: `pow_in_Omega`, `powerset_cardinality`

**Patrón de demostración**: De $A \simeq_s n$ con $n \in \omega$ se obtiene $\mathcal{P}(A) \simeq_s 2^n$ con $2^n \in \omega$.

#### Cardinalidad de BA Finita (finite_BA_cardinality)

**Ubicación**: `BoolAlg.FiniteBA.lean`, línea 93
**Orden**: 6º teorema (TEOREMA PRINCIPAL)

**Enunciado Matemático**: Toda álgebra booleana finita $\mathcal{P}(A)$ tiene cardinalidad $2^n$ para algún $n \in \omega$:
$$A \text{ finito} \Rightarrow \exists n \in \omega,\; \mathcal{P}(A) \simeq_s 2^n$$

**Firma Lean4**:

```lean
theorem finite_BA_cardinality {A : U} (hA : isFiniteSet A) :
    ∃ n, n ∈ ω ∧ 𝒫 A ≃ₛ pow (σ (σ (∅ : U))) n
```

**Dependencias**: `powerset_cardinality`

#### Cardinalidad de BA Finita con Átomos (finite_BA_cardinality_atoms)

**Ubicación**: `BoolAlg.FiniteBA.lean`, línea 101
**Orden**: 7º teorema

**Enunciado Matemático**: Toda álgebra booleana finita $\mathcal{P}(A)$ tiene cardinalidad $2^n$ donde $n$ es el número de átomos:
$$A \text{ finito} \Rightarrow \exists n \in \omega,\; \text{Atoms}(A) \simeq_s n \land \mathcal{P}(A) \simeq_s 2^n$$

**Firma Lean4**:

```lean
theorem finite_BA_cardinality_atoms {A : U} (hA : isFiniteSet A) :
    ∃ n, n ∈ ω ∧ Atoms A ≃ₛ n ∧ 𝒫 A ≃ₛ pow (σ (σ (∅ : U))) n
```

**Dependencias**: `atoms_equipotent_base`, `BA_cardinality_via_atoms`

#### BA Finita Completa Atómica (finite_complete_atomic_BA)

**Ubicación**: `BoolAlg.FiniteBA.lean`, línea 113
**Orden**: 8º teorema (COROLARIO CULMINANTE)

**Enunciado Matemático**: Si $A$ es finito, entonces $\mathcal{P}(A)$ es un álgebra booleana completa atómica con cardinalidad $2^n$.

**Firma Lean4**:

```lean
theorem finite_complete_atomic_BA {A : U} (hA : isFiniteSet A) :
    isCompleteAtomicBA A ∧ ∃ n, n ∈ ω ∧ 𝒫 A ≃ₛ pow (σ (σ (∅ : U))) n
```

**Dependencias**: `powerset_is_complete_atomic_BA`, `finite_BA_cardinality`

### 4.39 BoolAlg.BoolRingBA.lean

**Importancia por teorema**:

- ring_join_eq_union: high — identidad clave BR→BA (X△Y△(X∩Y) = X∪Y)
- ring_compl_eq_complement: high — identidad clave BR→BA (A△X = X^c)
- BA_symmDiff_eq_ring_add: high — identidad clave BA→BR
- BA_ring_BA_join: medium — round-trip BA→BR→BA
- BA_ring_BA_complement: medium — round-trip BA→BR→BA
- BA_ring_BA_meet: low — trivial (rfl)
- ring_BA_ring_add: medium — round-trip BR→BA→BR
- ring_BA_ring_mul: low — trivial (rfl)
- symmDiff_via_complement: medium — X△Y = (X∪Y)∩(X∩Y)^c
- ring_char_two: medium — X△X = ∅
- ring_idempotent: medium — X∩X = X
- complement_involution: medium — (X^c)^c = X
- ring_add_complement_eq_universe: medium — X△X^c = A

#### Recuperación del Join (ring_join_eq_union)

**Ubicación**: `BoolAlg.BoolRingBA.lean`, línea 59
**Orden**: 1º teorema (IDENTIDAD CLAVE BR→BA)

**Enunciado Matemático**: $X \triangle Y \triangle (X \cap Y) = X \cup Y$. El join del álgebra booleana se recupera de las operaciones del anillo.

**Firma Lean4**:

```lean
theorem ring_join_eq_union (X Y : U) :
    symmDiff (symmDiff X Y) (inter X Y) = union X Y
```

**Dependencias**: `mem_symmDiff_iff`, `mem_union_iff`, `mem_inter_iff`, `subset_antisymm`

#### Recuperación del Complemento (ring_compl_eq_complement)

**Ubicación**: `BoolAlg.BoolRingBA.lean`, línea 103
**Orden**: 2º teorema (IDENTIDAD CLAVE BR→BA)

**Enunciado Matemático**: Si $X \subseteq A$, entonces $A \triangle X = X^{\complement[A]}$. El complemento del BA se recupera como suma con la identidad multiplicativa.

**Firma Lean4**:

```lean
theorem ring_compl_eq_complement {A X : U} (hX : X ⊆ A) :
    symmDiff A X = Complement A X
```

**Dependencias**: `mem_symmDiff_iff`, `Complement_is_specified`, `subset_antisymm`

#### Recuperación de la Suma (BA_symmDiff_eq_ring_add)

**Ubicación**: `BoolAlg.BoolRingBA.lean`, línea 126
**Orden**: 3º teorema (IDENTIDAD CLAVE BA→BR)

**Enunciado Matemático**: Si $X, Y \subseteq A$, entonces $(X \cap Y^{\complement[A]}) \cup (X^{\complement[A]} \cap Y) = X \triangle Y$. La suma del anillo se recupera de las operaciones del BA.

**Firma Lean4**:

```lean
theorem BA_symmDiff_eq_ring_add {A X Y : U} (hX : X ⊆ A) (hY : Y ⊆ A) :
    union (inter X (Complement A Y)) (inter (Complement A X) Y) =
    symmDiff X Y
```

**Dependencias**: `mem_union_iff`, `mem_inter_iff`, `mem_symmDiff_iff`, `Complement_is_specified`, `subset_antisymm`

#### Round-Trip BA→BR→BA Join (BA_ring_BA_join)

**Ubicación**: `BoolAlg.BoolRingBA.lean`, línea 160
**Orden**: 4º teorema (ROUND-TRIP)

**Enunciado Matemático**: Para $X, Y \in \mathcal{P}(A)$: $X \triangle Y \triangle (X \cap Y) = X \cup Y$.

**Firma Lean4**:

```lean
theorem BA_ring_BA_join {A X Y : U}
    (_hX : X ∈ 𝒫 A) (_hY : Y ∈ 𝒫 A) :
    symmDiff (symmDiff X Y) (inter X Y) = union X Y
```

**Dependencias**: `ring_join_eq_union`

#### Round-Trip BA→BR→BA Complemento (BA_ring_BA_complement)

**Ubicación**: `BoolAlg.BoolRingBA.lean`, línea 168
**Orden**: 5º teorema (ROUND-TRIP)

**Enunciado Matemático**: Para $X \in \mathcal{P}(A)$: $A \triangle X = X^{\complement[A]}$.

**Firma Lean4**:

```lean
theorem BA_ring_BA_complement {A X : U} (hX : X ∈ 𝒫 A) :
    symmDiff A X = Complement A X
```

**Dependencias**: `ring_compl_eq_complement`, `mem_powerset_iff`

#### Round-Trip BA→BR→BA Meet (BA_ring_BA_meet)

**Ubicación**: `BoolAlg.BoolRingBA.lean`, línea 175
**Orden**: 6º teorema (ROUND-TRIP, trivial)

**Enunciado Matemático**: $X \cap Y = X \cap Y$ (meet es intersección en ambas estructuras).

**Firma Lean4**:

```lean
theorem BA_ring_BA_meet {A X Y : U}
    (_hX : X ∈ 𝒫 A) (_hY : Y ∈ 𝒫 A) :
    inter X Y = inter X Y
```

**Dependencias**: (ninguna — `rfl`)

#### Round-Trip BR→BA→BR Suma (ring_BA_ring_add)

**Ubicación**: `BoolAlg.BoolRingBA.lean`, línea 182
**Orden**: 7º teorema (ROUND-TRIP)

**Enunciado Matemático**: Para $X, Y \in \mathcal{P}(A)$: $(X \cap Y^{\complement[A]}) \cup (X^{\complement[A]} \cap Y) = X \triangle Y$.

**Firma Lean4**:

```lean
theorem ring_BA_ring_add {A X Y : U}
    (hX : X ∈ 𝒫 A) (hY : Y ∈ 𝒫 A) :
    union (inter X (Complement A Y)) (inter (Complement A X) Y) =
    symmDiff X Y
```

**Dependencias**: `BA_symmDiff_eq_ring_add`, `mem_powerset_iff`

#### Round-Trip BR→BA→BR Multiplicación (ring_BA_ring_mul)

**Ubicación**: `BoolAlg.BoolRingBA.lean`, línea 191
**Orden**: 8º teorema (ROUND-TRIP, trivial)

**Enunciado Matemático**: $X \cap Y = X \cap Y$ (multiplicación es intersección en ambas estructuras).

**Firma Lean4**:

```lean
theorem ring_BA_ring_mul {A X Y : U}
    (_hX : X ∈ 𝒫 A) (_hY : Y ∈ 𝒫 A) :
    inter X Y = inter X Y
```

**Dependencias**: (ninguna — `rfl`)

#### Diferencia Simétrica vía Complemento (symmDiff_via_complement)

**Ubicación**: `BoolAlg.BoolRingBA.lean`, línea 201
**Orden**: 9º teorema

**Enunciado Matemático**: Si $X, Y \subseteq A$, entonces $X \triangle Y = (X \cup Y) \cap (X \cap Y)^{\complement[A]}$.

**Firma Lean4**:

```lean
theorem symmDiff_via_complement {A X Y : U} (hX : X ⊆ A) (hY : Y ⊆ A) :
    symmDiff X Y =
    inter (union X Y) (Complement A (inter X Y))
```

**Dependencias**: `symmDiff_as_complement`

#### Característica 2 del Anillo (ring_char_two)

**Ubicación**: `BoolAlg.BoolRingBA.lean`, línea 207
**Orden**: 10º teorema

**Enunciado Matemático**: $X \triangle X = \emptyset$ (todo elemento es su propio inverso aditivo).

**Firma Lean4**:

```lean
theorem ring_char_two (X : U) : symmDiff X X = (∅ : U)
```

**Dependencias**: `symmDiff_inverse`

#### Idempotencia del Anillo (ring_idempotent)

**Ubicación**: `BoolAlg.BoolRingBA.lean`, línea 212
**Orden**: 11º teorema

**Enunciado Matemático**: $X \cap X = X$ (todo elemento es idempotente bajo multiplicación).

**Firma Lean4**:

```lean
theorem ring_idempotent (X : U) : inter X X = X
```

**Dependencias**: `powerset_inter_idempotent`

#### Involución del Complemento (complement_involution)

**Ubicación**: `BoolAlg.BoolRingBA.lean`, línea 217
**Orden**: 12º teorema

**Enunciado Matemático**: Si $X \subseteq A$, entonces $(X^{\complement[A]})^{\complement[A]} = X$.

**Firma Lean4**:

```lean
theorem complement_involution {A X : U} (hX : X ⊆ A) :
    Complement A (Complement A X) = X
```

**Dependencias**: `powerset_double_complement`

#### Suma con Complemento da Universo (ring_add_complement_eq_universe)

**Ubicación**: `BoolAlg.BoolRingBA.lean`, línea 222
**Orden**: 13º teorema

**Enunciado Matemático**: Si $X \subseteq A$, entonces $X \triangle X^{\complement[A]} = A$.

**Firma Lean4**:

```lean
theorem ring_add_complement_eq_universe {A X : U} (hX : X ⊆ A) :
    symmDiff X (Complement A X) = A
```

**Dependencias**: `mem_symmDiff_iff`, `Complement_is_specified`, `subset_antisymm`

---

### 4.40 BoolAlg.Representation.lean

**Importancia por teorema**:

- atomsSingletonMap_spec: medium — especificación del mapa
- atomsSingletonMap_is_function: medium — construcción
- atomsSingletonMap_is_injective: medium — construcción
- atomsSingletonMap_is_surjective: medium — construcción
- atomsSingletonMap_is_bijection: high — a ↔ {a} es biyección
- A_equipotent_Atoms: high — A ≃ₛ Atoms(A)
- mem_atomsBelow_iff: medium — especificación
- atomsBelow_mem_powerset_Atoms: low — auxiliar
- atomsBelow_eq_singletons_in: medium — caracterización
- atomsBelowMap_spec: medium — especificación
- atomsBelowMap_is_function: medium — construcción
- union_atomsBelow_eq: high — lema clave: ⋃atomsBelow(A,X) = X
- atomsBelowMap_is_injective: high — inyectividad del mapa de representación
- atomsBelow_of_union: high — inversa de atomsBelow
- union_atoms_mem_powerset: low — auxiliar
- atomsBelowMap_is_surjective: high — suryectividad del mapa
- atomsBelowMap_is_bijection: high — biyección 𝒫(A) ↔ 𝒫(Atoms(A))
- representation_equipotent: high — 𝒫(A) ≃ₛ 𝒫(Atoms(A))
- atomsBelowMap_preserves_empty: medium — preserva vacío
- atomsBelowMap_preserves_universe: medium — preserva universo
- atomsBelowMap_preserves_union: high — preserva unión
- atomsBelowMap_preserves_inter: high — preserva intersección
- atomsBelowMap_preserves_complement: high — preserva complemento
- representation_theorem: high — RESULTADO PRINCIPAL (isomorfismo completo de BA)

#### Especificación de atomsSingletonMap (atomsSingletonMap_spec)

**Ubicación**: `BoolAlg.Representation.lean`, línea 103
**Orden**: 1º teorema

**Enunciado Matemático**: $⟨a, Y⟩ \in \text{atomsSingletonMap}(A) \iff a \in A \land Y = \{a\}$.

**Firma Lean4**:

```lean
theorem atomsSingletonMap_spec (A a Y : U) :
    ⟨a, Y⟩ ∈ atomsSingletonMap A ↔ a ∈ A ∧ Y = ({a} : U)
```

**Dependencias**: `atomsSingletonMap`, `mem_sep_iff`, `Eq_of_OrderedPairs_given_projections`

#### atomsSingletonMap es función (atomsSingletonMap_is_function)

**Ubicación**: `BoolAlg.Representation.lean`, línea 125
**Orden**: 2º teorema

**Enunciado Matemático**: $\text{atomsSingletonMap}(A)$ es una función de $A$ a $\text{Atoms}(A)$.

**Firma Lean4**:

```lean
theorem atomsSingletonMap_is_function (A : U) :
    IsFunction (atomsSingletonMap A) A (Atoms A)
```

**Dependencias**: `atomsSingletonMap`, `atomsSingletonMap_spec`

#### atomsSingletonMap es inyectiva (atomsSingletonMap_is_injective)

**Ubicación**: `BoolAlg.Representation.lean`, línea 142
**Orden**: 3º teorema

**Enunciado Matemático**: Si $\{a_1\} = \{a_2\}$ entonces $a_1 = a_2$; es decir, $a \mapsto \{a\}$ es inyectiva.

**Firma Lean4**:

```lean
theorem atomsSingletonMap_is_injective (A : U) :
    isInjective (atomsSingletonMap A)
```

**Dependencias**: `atomsSingletonMap_spec`, `Singleton_is_specified`

#### atomsSingletonMap es suryectiva (atomsSingletonMap_is_surjective)

**Ubicación**: `BoolAlg.Representation.lean`, línea 153
**Orden**: 4º teorema

**Enunciado Matemático**: Todo átomo $Y \in \text{Atoms}(A)$ es de la forma $\{a\}$ para algún $a \in A$.

**Firma Lean4**:

```lean
theorem atomsSingletonMap_is_surjective (A : U) :
    isSurjectiveOnto (atomsSingletonMap A) (Atoms A)
```

**Dependencias**: `Atoms_eq_singletons`, `atomsSingletonMap_spec`

#### atomsSingletonMap es biyección (atomsSingletonMap_is_bijection)

**Ubicación**: `BoolAlg.Representation.lean`, línea 162
**Orden**: 5º teorema

**Enunciado Matemático**: $a \mapsto \{a\}$ es una biyección $A \leftrightarrow \text{Atoms}(A)$.

**Firma Lean4**:

```lean
theorem atomsSingletonMap_is_bijection (A : U) :
    isBijection (atomsSingletonMap A) A (Atoms A)
```

**Dependencias**: `atomsSingletonMap_is_function`, `atomsSingletonMap_is_injective`, `atomsSingletonMap_is_surjective`

#### A equipotente a Atoms(A) (A_equipotent_Atoms)

**Ubicación**: `BoolAlg.Representation.lean`, línea 169
**Orden**: 6º teorema

**Enunciado Matemático**: $A \simeq_s \text{Atoms}(A)$.

**Firma Lean4**:

```lean
theorem A_equipotent_Atoms (A : U) : isEquipotent A (Atoms A)
```

**Dependencias**: `atomsSingletonMap`, `atomsSingletonMap_is_bijection`

#### Especificación de atomsBelow (mem_atomsBelow_iff)

**Ubicación**: `BoolAlg.Representation.lean`, línea 181
**Orden**: 7º teorema

**Enunciado Matemático**: $Y \in \text{atomsBelow}(A, X) \iff Y \in \text{Atoms}(A) \land Y \subseteq X$.

**Firma Lean4**:

```lean
theorem mem_atomsBelow_iff (A X Y : U) :
    Y ∈ atomsBelow A X ↔ Y ∈ Atoms A ∧ Y ⊆ X
```

**Dependencias**: `atomsBelow`, `mem_sep_iff`

#### atomsBelow pertenece a 𝒫(Atoms A) (atomsBelow_mem_powerset_Atoms)

**Ubicación**: `BoolAlg.Representation.lean`, línea 187
**Orden**: 8º teorema

**Enunciado Matemático**: $\text{atomsBelow}(A, X) \in \mathcal{P}(\text{Atoms}(A))$.

**Firma Lean4**:

```lean
theorem atomsBelow_mem_powerset_Atoms (A X : U) :
    atomsBelow A X ∈ 𝒫 (Atoms A)
```

**Dependencias**: `mem_atomsBelow_iff`, `mem_powerset_iff`

#### Caracterización de atomsBelow como singletons (atomsBelow_eq_singletons_in)

**Ubicación**: `BoolAlg.Representation.lean`, línea 194
**Orden**: 9º teorema

**Enunciado Matemático**: Si $X \in \mathcal{P}(A)$, entonces $Y \in \text{atomsBelow}(A, X) \iff \exists a \in X,\; Y = \{a\}$.

**Firma Lean4**:

```lean
theorem atomsBelow_eq_singletons_in (A X : U) (hX : X ∈ 𝒫 A) :
    ∀ Y, Y ∈ atomsBelow A X ↔ ∃ a, a ∈ X ∧ Y = ({a} : U)
```

**Dependencias**: `mem_atomsBelow_iff`, `Atoms_eq_singletons`, `mem_powerset_iff`

#### Especificación de atomsBelowMap (atomsBelowMap_spec)

**Ubicación**: `BoolAlg.Representation.lean`, línea 223
**Orden**: 10º teorema

**Enunciado Matemático**: $⟨X, F⟩ \in \text{atomsBelowMap}(A) \iff X \in \mathcal{P}(A) \land F = \text{atomsBelow}(A, X)$.

**Firma Lean4**:

```lean
theorem atomsBelowMap_spec (A X F : U) :
    ⟨X, F⟩ ∈ atomsBelowMap A ↔ X ∈ 𝒫 A ∧ F = atomsBelow A X
```

**Dependencias**: `atomsBelowMap`, `mem_sep_iff`, `Eq_of_OrderedPairs_given_projections`

#### atomsBelowMap es función (atomsBelowMap_is_function)

**Ubicación**: `BoolAlg.Representation.lean`, línea 240
**Orden**: 11º teorema

**Enunciado Matemático**: $\text{atomsBelowMap}(A)$ es una función $\mathcal{P}(A) \to \mathcal{P}(\text{Atoms}(A))$.

**Firma Lean4**:

```lean
theorem atomsBelowMap_is_function (A : U) :
    IsFunction (atomsBelowMap A) (𝒫 A) (𝒫 (Atoms A))
```

**Dependencias**: `atomsBelowMap`, `atomsBelowMap_spec`, `atomsBelow_mem_powerset_Atoms`

#### Lema clave: unión reconstruye X (union_atomsBelow_eq)

**Ubicación**: `BoolAlg.Representation.lean`, línea 259
**Orden**: 12º teorema

**Enunciado Matemático**: Si $X \in \mathcal{P}(A)$, entonces $\bigcup \text{atomsBelow}(A, X) = X$.

**Firma Lean4**:

```lean
theorem union_atomsBelow_eq (A X : U) (hX : X ∈ 𝒫 A) :
    ⋃ (atomsBelow A X) = X
```

**Dependencias**: `element_is_union_of_atoms`

#### atomsBelowMap es inyectiva (atomsBelowMap_is_injective)

**Ubicación**: `BoolAlg.Representation.lean`, línea 263
**Orden**: 13º teorema

**Enunciado Matemático**: El mapa $X \mapsto \text{atomsBelow}(A, X)$ es inyectivo.

**Firma Lean4**:

```lean
theorem atomsBelowMap_is_injective (A : U) :
    isInjective (atomsBelowMap A)
```

**Dependencias**: `atomsBelowMap_spec`, `union_atomsBelow_eq`

#### Inversa de atomsBelow vía unión (atomsBelow_of_union)

**Ubicación**: `BoolAlg.Representation.lean`, línea 279
**Orden**: 14º teorema

**Enunciado Matemático**: Si $F \subseteq \text{Atoms}(A)$, entonces $\text{atomsBelow}(A, \bigcup F) = F$.

**Firma Lean4**:

```lean
theorem atomsBelow_of_union (A F : U) (hF : F ⊆ Atoms A) :
    atomsBelow A (⋃ F) = F
```

**Dependencias**: `mem_atomsBelow_iff`, `Atoms_eq_singletons`, `mem_sUnion_iff`

#### Unión de átomos en 𝒫(A) (union_atoms_mem_powerset)

**Ubicación**: `BoolAlg.Representation.lean`, línea 312
**Orden**: 15º teorema

**Enunciado Matemático**: Si $F \subseteq \text{Atoms}(A)$, entonces $\bigcup F \in \mathcal{P}(A)$.

**Firma Lean4**:

```lean
theorem union_atoms_mem_powerset (A F : U) (hF : F ⊆ Atoms A) :
    ⋃ F ∈ 𝒫 A
```

**Dependencias**: `mem_sUnion_iff`, `Atoms_is_specified`, `mem_powerset_iff`

#### atomsBelowMap es suryectiva (atomsBelowMap_is_surjective)

**Ubicación**: `BoolAlg.Representation.lean`, línea 323
**Orden**: 16º teorema

**Enunciado Matemático**: El mapa $X \mapsto \text{atomsBelow}(A, X)$ es suryectivo sobre $\mathcal{P}(\text{Atoms}(A))$.

**Firma Lean4**:

```lean
theorem atomsBelowMap_is_surjective (A : U) :
    isSurjectiveOnto (atomsBelowMap A) (𝒫 (Atoms A))
```

**Dependencias**: `union_atoms_mem_powerset`, `atomsBelowMap_spec`, `atomsBelow_of_union`

#### Teorema de Representación — biyección (atomsBelowMap_is_bijection)

**Ubicación**: `BoolAlg.Representation.lean`, línea 337
**Orden**: 17º teorema

**Enunciado Matemático**: $\text{atomsBelowMap}(A)$ es una biyección $\mathcal{P}(A) \leftrightarrow \mathcal{P}(\text{Atoms}(A))$.

**Firma Lean4**:

```lean
theorem atomsBelowMap_is_bijection (A : U) :
    isBijection (atomsBelowMap A) (𝒫 A) (𝒫 (Atoms A))
```

**Dependencias**: `atomsBelowMap_is_function`, `atomsBelowMap_is_injective`, `atomsBelowMap_is_surjective`

#### Teorema de Representación — equipotencia (representation_equipotent)

**Ubicación**: `BoolAlg.Representation.lean`, línea 344
**Orden**: 18º teorema

**Enunciado Matemático**: $\mathcal{P}(A) \simeq_s \mathcal{P}(\text{Atoms}(A))$.

**Firma Lean4**:

```lean
theorem representation_equipotent (A : U) :
    isEquipotent (𝒫 A) (𝒫 (Atoms A))
```

**Dependencias**: `atomsBelowMap`, `atomsBelowMap_is_bijection`

#### Φ preserva vacío (atomsBelowMap_preserves_empty)

**Ubicación**: `BoolAlg.Representation.lean`, línea 352
**Orden**: 19º teorema

**Enunciado Matemático**: $\Phi(\emptyset) = \emptyset$: el mapa envía el elemento mínimo al elemento mínimo.

**Firma Lean4**:

```lean
theorem atomsBelowMap_preserves_empty (A : U) :
    atomsBelow A ∅ = ∅
```

**Dependencias**: `mem_atomsBelow_iff`, `Atoms_eq_singletons`, `EmptySet_is_empty`

#### Φ preserva universo (atomsBelowMap_preserves_universe)

**Ubicación**: `BoolAlg.Representation.lean`, línea 371
**Orden**: 20º teorema

**Enunciado Matemático**: $\Phi(A) = \text{Atoms}(A)$: el mapa envía el elemento máximo al elemento máximo.

**Firma Lean4**:

```lean
theorem atomsBelowMap_preserves_universe (A : U) :
    atomsBelow A A = Atoms A
```

**Dependencias**: `mem_atomsBelow_iff`, `Atoms_eq_singletons`

#### Φ preserva unión (atomsBelowMap_preserves_union)

**Ubicación**: `BoolAlg.Representation.lean`, línea 390
**Orden**: 21º teorema

**Enunciado Matemático**: $\Phi(X \cup Y) = \Phi(X) \cup \Phi(Y)$.

**Firma Lean4**:

```lean
theorem atomsBelowMap_preserves_union (A X Y : U) (_hX : X ∈ 𝒫 A) (_hY : Y ∈ 𝒫 A) :
    atomsBelow A (union X Y) = union (atomsBelow A X) (atomsBelow A Y)
```

**Dependencias**: `mem_atomsBelow_iff`, `Atoms_eq_singletons`, `mem_union_iff`

#### Φ preserva intersección (atomsBelowMap_preserves_inter)

**Ubicación**: `BoolAlg.Representation.lean`, línea 424
**Orden**: 22º teorema

**Enunciado Matemático**: $\Phi(X \cap Y) = \Phi(X) \cap \Phi(Y)$.

**Firma Lean4**:

```lean
theorem atomsBelowMap_preserves_inter (A X Y : U) (_hX : X ∈ 𝒫 A) (_hY : Y ∈ 𝒫 A) :
    atomsBelow A (inter X Y) = inter (atomsBelow A X) (atomsBelow A Y)
```

**Dependencias**: `mem_atomsBelow_iff`, `mem_inter_iff`

#### Φ preserva complemento (atomsBelowMap_preserves_complement)

**Ubicación**: `BoolAlg.Representation.lean`, línea 446
**Orden**: 23º teorema

**Enunciado Matemático**: $\Phi(X^{\complement[A]}) = \Phi(X)^{\complement[\text{Atoms}(A)]}$.

**Firma Lean4**:

```lean
theorem atomsBelowMap_preserves_complement (A X : U) (_hX : X ∈ 𝒫 A) :
    atomsBelow A (Complement A X) = Complement (Atoms A) (atomsBelow A X)
```

**Dependencias**: `mem_atomsBelow_iff`, `Atoms_eq_singletons`, `Complement_is_specified`

#### Teorema de Representación Completo (representation_theorem)

**Ubicación**: `BoolAlg.Representation.lean`, línea 497
**Orden**: 24º teorema (RESULTADO PRINCIPAL)

**Enunciado Matemático**: Para todo conjunto $A$, el álgebra booleana completa atómica $\mathcal{P}(A)$ es isomorfa (como álgebra booleana) a $\mathcal{P}(\text{Atoms}(A))$ vía la biyección $\text{atomsBelowMap}$, que preserva $\cup$, $\cap$ y complemento.

**Firma Lean4**:

```lean
theorem representation_theorem (A : U) :
    isBijection (atomsBelowMap A) (𝒫 A) (𝒫 (Atoms A)) ∧
    (∀ X Y, X ∈ 𝒫 A → Y ∈ 𝒫 A →
      atomsBelow A (union X Y) = union (atomsBelow A X) (atomsBelow A Y)) ∧
    (∀ X Y, X ∈ 𝒫 A → Y ∈ 𝒫 A →
      atomsBelow A (inter X Y) = inter (atomsBelow A X) (atomsBelow A Y)) ∧
    (∀ X, X ∈ 𝒫 A →
      atomsBelow A (Complement A X) = Complement (Atoms A) (atomsBelow A X))
```

**Dependencias**: `atomsBelowMap_is_bijection`, `atomsBelowMap_preserves_union`, `atomsBelowMap_preserves_inter`, `atomsBelowMap_preserves_complement`

---

### 4.41 Cardinal.FinitePowerSet.lean

**Importancia por teorema**:

- equipotent_union_singleton: high — A≃n ∧ a∉A ⇒ A∪{a}≃σn
- sdiff_singleton_union: medium — (A\{a})∪{a} = A
- union_sdiff_cancel: medium — (B∪{a})\{a} = B
- union_singleton_sdiff_cancel: medium — alias
- disjoint_union_equipotent: high — cardinalidad de unión disjunta
- removeElemMap_is_specified: medium — especificación
- removeElemMap_is_bijection: high — biyección para halving del powerset
- powerset_without_elem: medium — mitad sin a
- powerset_halves_disjoint: medium — mitades disjuntas
- powerset_halves_union: medium — mitades cubren
- mul_two_eq_double: low — lema aritmético auxiliar
- powerset_cardinality: high — RESULTADO PRINCIPAL |𝒫(A)| = 2^n

#### Extensión de biyección por un elemento (equipotent_union_singleton)

**Ubicación**: `Cardinal.FinitePowerSet.lean`, línea 59
**Orden**: 1º teorema

**Enunciado Matemático**: Si $A \simeq_s n$ con $n \in \omega$ y $a \notin A$, entonces $A \cup \{a\} \simeq_s \sigma(n)$.

**Firma Lean4**:

```lean
theorem equipotent_union_singleton {A a n : U} (hn : n ∈ ω)
    (hAn : A ≃ₛ n) (ha : a ∉ A) : (union A {a}) ≃ₛ σ n
```

**Dependencias**: `mem_succ_iff`, `mem_succ_self`, `not_mem_self`

#### Reconstrucción A \ {a} ∪ {a} = A (sdiff_singleton_union)

**Ubicación**: `Cardinal.FinitePowerSet.lean`, línea 172
**Orden**: 2º teorema

**Enunciado Matemático**: Si $a \in A$, entonces $(A \setminus \{a\}) \cup \{a\} = A$.

**Firma Lean4**:

```lean
theorem sdiff_singleton_union {A a : U} (ha : a ∈ A) :
    union (sdiff A {a}) {a} = A
```

**Dependencias**: `mem_union_iff`, `mem_sdiff_iff`, `Singleton_is_specified`, `ExtSet`

#### Cancelación de unión-diferencia (union_sdiff_cancel)

**Ubicación**: `Cardinal.FinitePowerSet.lean`, línea 185
**Orden**: 3º teorema

**Enunciado Matemático**: Si $a \notin B$, entonces $(B \cup \{a\}) \setminus \{a\} = B$.

**Firma Lean4**:

```lean
theorem union_sdiff_cancel {B a : U} (ha : a ∉ B) :
    sdiff (union B {a}) {a} = B
```

**Dependencias**: `mem_sdiff_iff`, `mem_union_iff`, `Singleton_is_specified`, `ExtSet`

#### Cancelación unión-singleton-diferencia (union_singleton_sdiff_cancel)

**Ubicación**: `Cardinal.FinitePowerSet.lean`, línea 199
**Orden**: 4º teorema

**Enunciado Matemático**: Si $a \notin T$, entonces $(T \cup \{a\}) \setminus \{a\} = T$.

**Firma Lean4**:

```lean
theorem union_singleton_sdiff_cancel {T a : U} (ha : a ∉ T) :
    sdiff (union T {a}) {a} = T
```

**Dependencias**: `union_sdiff_cancel`

#### Cardinalidad de unión disjunta (disjoint_union_equipotent)

**Ubicación**: `Cardinal.FinitePowerSet.lean`, línea 208
**Orden**: 5º teorema

**Enunciado Matemático**: Si $A \simeq_s m$, $B \simeq_s n$, $m, n \in \omega$ y $A \cap B = \emptyset$, entonces $A \cup B \simeq_s \text{add}(m, n)$.

**Firma Lean4**:

```lean
theorem disjoint_union_equipotent {A B m n : U} (hm : m ∈ ω) (hn : n ∈ ω)
    (hAm : A ≃ₛ m) (hBn : B ≃ₛ n) (hdisj : ∀ x, x ∈ A → x ∉ B) :
    (union A B) ≃ₛ add m n
```

**Dependencias**: `equipotent_union_singleton`, `induction_principle`, `add_zero`, `add_succ`, `remove_element_bijection`, `union_with_remove`

#### Especificación de removeElemMap (removeElemMap_is_specified)

**Ubicación**: `Cardinal.FinitePowerSet.lean`, línea 303
**Orden**: 6º teorema

**Enunciado Matemático**: $⟨S, T⟩ \in \text{removeElemMap}(A, a) \iff S \in \mathcal{P}(A) \land a \in S \land T = S \setminus \{a\}$.

**Firma Lean4**:

```lean
theorem removeElemMap_is_specified (A a S T : U) :
    ⟨S, T⟩ ∈ removeElemMap A a ↔
    S ∈ 𝒫 A ∧ a ∈ S ∧ T = sdiff S {a}
```

**Dependencias**: `removeElemMap`, `mem_sep_iff`, `Eq_of_OrderedPairs_given_projections`

#### removeElemMap es biyección (removeElemMap_is_bijection)

**Ubicación**: `Cardinal.FinitePowerSet.lean`, línea 326
**Orden**: 7º teorema

**Enunciado Matemático**: Si $a \in A$, $\text{removeElemMap}(A, a)$ es una biyección $\{S \in \mathcal{P}(A) \mid a \in S\} \leftrightarrow \mathcal{P}(A \setminus \{a\})$.

**Firma Lean4**:

```lean
theorem removeElemMap_is_bijection (A a : U) (ha : a ∈ A) :
    isBijection (removeElemMap A a)
      (sep (𝒫 A) (fun S => a ∈ S)) (𝒫 (sdiff A {a}))
```

**Dependencias**: `removeElemMap_is_specified`, `sdiff_singleton_union`, `union_singleton_sdiff_cancel`

#### Mitad "sin a" del powerset (powerset_without_elem)

**Ubicación**: `Cardinal.FinitePowerSet.lean`, línea 263
**Orden**: 8º teorema

**Enunciado Matemático**: Si $a \notin B$, entonces $\{S \in \mathcal{P}(B \cup \{a\}) \mid a \notin S\} = \mathcal{P}(B)$.

**Firma Lean4**:

```lean
theorem powerset_without_elem {B a : U} (ha : a ∉ B) :
    sep (𝒫 (union B {a})) (fun S => a ∉ S) = 𝒫 B
```

**Dependencias**: `mem_sep_iff`, `mem_powerset_iff`, `mem_union_iff`, `Singleton_is_specified`

#### Mitades del powerset son disjuntas (powerset_halves_disjoint)

**Ubicación**: `Cardinal.FinitePowerSet.lean`, línea 284
**Orden**: 9º teorema

**Enunciado Matemático**: Las mitades de $\mathcal{P}(A)$ divididas por un elemento $a$ son disjuntas.

**Firma Lean4**:

```lean
theorem powerset_halves_disjoint (A a : U) :
    ∀ S, S ∈ sep (𝒫 A) (fun S => a ∉ S) →
    S ∉ sep (𝒫 A) (fun S => a ∈ S)
```

**Dependencias**: `mem_sep_iff`

#### Mitades del powerset cubren (powerset_halves_union)

**Ubicación**: `Cardinal.FinitePowerSet.lean`, línea 291
**Orden**: 10º teorema

**Enunciado Matemático**: Las mitades de $\mathcal{P}(A)$ divididas por un elemento $a$ cubren todo $\mathcal{P}(A)$.

**Firma Lean4**:

```lean
theorem powerset_halves_union (A a : U) :
    union (sep (𝒫 A) (fun S => a ∉ S)) (sep (𝒫 A) (fun S => a ∈ S)) = 𝒫 A
```

**Dependencias**: `mem_union_iff`, `mem_sep_iff`, `ExtSet`

#### Identidad aritmética mul 2 m = add m m (mul_two_eq_double)

**Ubicación**: `Cardinal.FinitePowerSet.lean`, línea 418
**Orden**: 11º teorema

**Enunciado Matemático**: $\text{mul}(\sigma(\sigma(\emptyset)), m) = \text{add}(m, m)$ para $m \in \omega$.

**Firma Lean4**:

```lean
theorem mul_two_eq_double (m : U) (hm : m ∈ ω) :
    mul (σ (σ (∅ : U))) m = add m m
```

**Dependencias**: `mul_comm_Omega`, `mul_succ`, `mul_zero`, `add_zero`

#### Cardinalidad del conjunto potencia finito (powerset_cardinality)

**Ubicación**: `Cardinal.FinitePowerSet.lean`, línea 431
**Orden**: 12º teorema (RESULTADO PRINCIPAL)

**Enunciado Matemático**: Si $A \simeq_s n$ con $n \in \omega$, entonces $\mathcal{P}(A) \simeq_s 2^n$ (donde $2 = \sigma(\sigma(\emptyset))$).

**Firma Lean4**:

```lean
theorem powerset_cardinality {A n : U} (hn : n ∈ ω) (hAn : A ≃ₛ n) :
    𝒫 A ≃ₛ pow (σ (σ (∅ : U))) n
```

**Dependencias**: `induction_principle`, `equipotent_empty_is_empty`, `pow_zero`, `pow_succ`, `remove_element_bijection`, `powerset_without_elem`, `removeElemMap_is_bijection`, `powerset_halves_disjoint`, `powerset_halves_union`, `disjoint_union_equipotent`, `mul_two_eq_double`, `equipotent_trans`

---

## 5. Notación y Sintaxis

### 5.1 Operadores Básicos

- `x ∈ A` - Pertenencia (`mem`)
- `A ⊆ B` - Subconjunto (`subset`)
- `A ⊂ B` - Subconjunto propio (`ssubset`)
- `A ⟂ B` - Conjuntos disjuntos (`disjoint`)
- `∅` - Conjunto vacío (`EmptySet`)

### 5.2 Construcciones de Conjuntos

- `{a}` - Singleton (`Singleton`)
- `{a, b}` - Par no ordenado (`PairSet`)
- `⋂ w` - Intersección de familia (`interSet`)
- `⟨a, b⟩` - Par ordenado (`OrderedPair`)
- `A ×ₛ B` - Producto cartesiano (`SetOps.CartesianProduct`)

### 5.3 Operaciones Binarias

- `A ∪ B` - Unión binaria (`union`)
- `A ∩ B` - Intersección binaria (`inter`)
- `A \ B` - Diferencia (`sdiff`)
- `A △ B` - Diferencia simétrica (`symmDiff`)

### 5.4 Funciones

- `f⦅x⦆` - Aplicación de función (`apply`)
- `𝟙 A` - Función identidad (`idFn`)
- `g ∘ f` - Composición (`comp`)
- `f⁻¹` - Función inversa (`inv`)
- `f ↾ C` - Restricción de f a dominio C (`restrict`)
- `f[X]` - Imagen directa (`image`)
- `f⁻¹[Y]` - Imagen inversa (`preimage`)
- `A ≃ₛ B` - Equipotencia (`isEquipotent`)
- `A ≼ₛ B` - Dominación (`isDominatedBy`)
- `A ≺ₛ B` - Dominación estricta (`isStrictlyDominatedBy`)

### 5.5 Números Naturales

- `σ n` - Función sucesor (`succ`)
- `∈[S]` - Orden estricto guiado por membresía (`StrictOrderMembershipGuided`)
- `0`, `1`, `2`, `3` - Naturales específicos (`zero`, `one`, `two`, `three`)

### 5.6 Conjunto Potencia

- `𝒫 A` - Conjunto potencia de A (`powerset`)

### 5.7 Infinito

- `ω` - Conjunto de todos los números naturales (`Omega`)
- `n ≺ m` - Orden estricto en ω: `n ∈ m` (scoped notation)
- `n ≼ m` - Orden no estricto en ω: `n ∈ m ∨ n = m` (scoped notation)

### 5.12 Isomorfismo Peano ↔ Von Neumann

- `ΠZ p` - Conversión Peano → Von Neumann: `fromPeano p` (`scoped notation "ΠZ"`)
- `ZΠ n hn` - Conversión Von Neumann → Peano: `toPeano n hn` (`scoped notation "ZΠ"`)

**Uso**: Ambas notaciones están disponibles con `open ZFC` (son `scoped`). No se abren en `Nat.Add`/`Nat.Mul` para evitar ambigüedad.

### 5.13 Aritmética en ω

- `add m n` - Suma en ω (`Nat.Add.add`); requiere `open ZFC.Nat.Add` o export
- `mul m n` - Producto en ω (`Nat.Mul.mul`); requiere `open ZFC.Nat.Mul` o export

### 5.8 De Morgan Generalizado

- `A \\ᶠ F` - Familia de complementos (`ComplementFamily`)

### 5.9 Distributividad Generalizada

- `⋂ F` - Intersección generalizada (`GeneralizedIntersection`)
- `X ∩ᶠ F` - Familia de intersecciones (`IntersectionImageFamily`)
- `X ∪ᶠ F` - Familia de uniones (`UnionImageFamily`)

### 5.10 Órdenes Parciales

- Conceptos de orden: cotas superiores/inferiores, supremo/ínfimo
- Propiedades de orden: reflexividad, transitividad, antisimetría
- Monotonicidad de operaciones de conjuntos

### 5.11 Órdenes Estrictos

- `A ⊂ B` - Subconjunto estricto (orden estricto)
- Propiedades: irreflexividad, asimetría, transitividad
- Transitividad mixta entre ⊆ y ⊂
- Tricotomía parcial y elemento diferenciador

## 6. Exports por Módulo

### 6.1 Extension.lean

```lean
export ZFC.Axiom.Extension (
    ExtSet ExtSetReverse eq_of_subset_of_subset subset_antisymm
    subset subset_refl subset_trans subset_antisymm
    disjoint disjoint_comm disjoint_elim disjoint_elim_wc
    ssubset_irrefl ssubset_asymm ssubset_trans
)
```

### 6.2 Relations.lean

```lean
export ZFC.SetOps.Relations (
    isRelationOn isRelationFrom Related
    isReflexiveOn isIrreflexiveOn isSymmetricOn
    isAntiSymmetricOn isAsymmetricOn isTransitiveOn
    isConnectedOn isStronglyConnectedOn isTrichotomousOn
    isEquivalenceOn isPreorderOn isPartialOrderOn
    isLinearOrderOn isStrictOrderOn isStrictPartialOrderOn
    isStrictLinearOrderOn isWellFoundedOn isWellOrderOn
    EqClass QuotientSet IdRel InverseRel
    Asymmetric_implies_Irreflexive StrictOrder_is_Irreflexive
    StrictPartialOrder_is_Irreflexive
    Irreflexive_Transitive_implies_Asymmetric
    Asymmetric_iff_Irreflexive_and_AntiSymmetric
    PartialOrder_Connected_is_LinearOrder
    LinearOrder_comparable
    StrictOrder_Connected_is_Trichotomous
    StrictLinearOrder_iff_StrictOrder_Connected
    mem_IdRel IdRel_is_Equivalence mem_EqClass
    EqClass_mem_self mem_EqClass_of_Related
    Related_of_mem_EqClass mem_EqClass_iff
    EqClass_eq_iff EqClass_eq_or_disjoint
    domain range imag
    mem_domain mem_range mem_imag
    pair_mem_implies_fst_in_domain
    pair_mem_implies_snd_in_range
    pair_mem_implies_snd_in_imag
)
```

### 6.3 PowerSet.lean

```lean
export ZFC.Axiom.PowerSet (
  PowerSet
  powersetExistsUnique
  powerset
  mem_powerset_iff
  powerset_eq_iff
  empty_mem_powerset
  self_mem_powerset
  powerset_nonempty
  powerset_empty
  powerset_mono
  powerset_mono_iff
  powerset_inter
  powerset_union_subset
  subset_powerset_sUnion
  sUnion_powerset
)
```

### 6.4 Functions.lean

```lean
export Functions (
  IsSingleValued
  IsFunction
  apply apply_mem apply_eq
  comp comp_is_specified comp_is_function
  idFn apply_id
  inv inverse_is_specified
  restrict mem_restrict_iff restrict_subset restrict_is_function restrict_apply
  image preimage
  isInjective isSurjectiveOnto isBijection
  isEquipotent isDominatedBy isStrictlyDominatedBy
  injective_inverse_single_valued
)
````

Ahora actualizo el timestamp en REFERENCE.md:

REFERENCE.md

````markdown
<<<<<<< SEARCH
*Última actualización: 2026-03-16 16:30*
```

### 6.5 Cardinality.lean

```lean
export Cardinality (
  diagSet mem_diagSet_iff diagSet_subset diagSet_in_powerset
  diagSet_not_in_range
  cantor_no_surjection cantor_no_bijection cantor_not_equipotent
  singletonMap singletonMap_is_specified singletonMap_is_function singletonMap_is_injective
  A_dominated_by_powerset powerset_not_dominated_by_A cantor_strict_dominance
  SetDiff SetDiff_is_specified SetDiff_subset
  CSB_core CSB_core_subset CSB_core_contains_base CSB_core_closed
  CSB_bijection CSB_bijection_is_specified
  CSB_bijection_is_function CSB_bijection_is_injective CSB_bijection_is_surjective
  CSB_bijection_is_bijection
  cantor_schroeder_bernstein dominated_antisymm
)
```

### 6.6 Nat.Basic.lean

```lean
export Nat.Basic (
  -- Core definitions
  succ mem_succ_iff
  IsInductive IsTransitive
  StrictOrderMembershipGuided mem_StrictOrderMembershipGuided
  isTotalStrictOrderMembershipGuided isWellOrderMembershipGuided
  IsNat
  -- Basic theorems
  isNat_zero mem_succ_self subset_of_mem_succ
  succ_preserves_transitivity transitive_element_subset
  -- Well-foundedness properties
  not_mem_self not_mem_of_mem nat_no_three_cycle
  nat_element_is_transitive nat_element_has_strict_total_order
  nat_element_has_well_order nat_element_is_nat
  ne_succ_self succ_of_nat_is_transitive
  succ_of_nat_has_strict_total_order isNat_succ
  no_nat_between
  -- Initial segments and trichotomy
  IsInitialSegment initial_segment_of_nat_is_eq_or_mem
  inter_nat_is_initial_segment nat_subset_mem_or_eq
  trichotomy mem_trans mem_asymm
  nat_is_initial_segment nat_element_trichotomy
  succ_injective succ_nonempty mem_succ_of_mem
  -- Nat is Zero or Succ
  eq_zero_or_exists_succ nat_subset_inductive_set nat_in_inductive_set
  -- Naturales específicos en conjuntos inductivos
  zero_in_inductive one_in_inductive two_in_inductive three_in_inductive
  nat_has_max
  -- Examples
  zero one two three zero_eq one_eq two_eq three_eq
)
```

### 6.7 Infinity.lean

```lean
export Axiom.Infinity (
  -- Axioma y definición
  ExistsInductiveSet
  Omega
  -- Propiedades básicas
  Omega_is_inductive
  Omega_subset_all_inductive
  zero_in_Omega
  succ_in_Omega
  -- Principios de inducción
  induction_principle
  strong_induction_principle
  -- Caracterización de naturales
  mem_Omega_is_Nat
  Nat_in_Omega
  Nat_iff_mem_Omega
  -- Propiedades estructurales
  Omega_is_transitive
  Omega_element_is_transitive
  Omega_has_total_order
  Omega_no_maximum
  -- Buena fundación
  nat_mem_wf
  -- Orden en ω (≺ y ≼)
  natLt_trans
  natLt_asymm
  natLt_trichotomy
  natLe_refl
  natLe_trans
  Omega_has_min
)
```

### 6.8 BoolAlg.GenDeMorgan.lean

**Namespace**: `ZFC.BoolAlg.GenDeMorgan` (exportado a `ZFC`)
**Última modificación**: 2026-03-24
**Dependencias**: `BoolAlg.PowerSetAlgebra`, `Union`, `Specification` + anteriores

```lean
export BoolAlg.GenDeMorgan (
  -- Definición
  ComplementFamily
  -- Especificación y membresía
  ComplementFamily_is_specified
  complement_mem_ComplementFamily
  -- Auxiliar de intersección generalizada
  interSet_mem_iff
  -- Leyes de De Morgan generalizadas
  inter_complement_eq_complement_union
  union_complement_eq_complement_inter
  -- Formas doble-complemento
  complement_inter_complement_eq_union
  complement_union_complement_eq_inter
)
```

### 6.9 BoolAlg.GenDistributive.lean

**Namespace**: `ZFC.BoolAlg.GenDistributive` (exportado a `ZFC`)
**Última modificación**: 2026-03-24
**Dependencias**: `BoolAlg.GenDeMorgan`, `BoolAlg.PowerSetAlgebra` + anteriores

```lean
export BoolAlg.GenDistributive (
  -- Definiciones
  IntersectFamily
  UnionFamily
  -- Especificación y membresía
  IntersectFamily_is_specified
  intersect_mem_IntersectFamily
  UnionFamily_is_specified
  union_mem_UnionFamily
  -- Leyes distributivas generalizadas
  inter_distrib_union
  union_distrib_inter
  -- Propiedades de familias
  IntersectFamily_nonempty
  UnionFamily_nonempty
  -- Formas conmutadas
  union_inter_distrib
  inter_union_distrib
)
```

### 6.10 BoolAlg.Ring.lean

```lean
export ZFC.BoolAlg.Ring (
    symmDiff_is_comm
    symmDiff_empty_identity
    symmDiff_identity_empty
    symmDiff_inverse
    symmDiff_assoc
    symmDiff_inter_distrib
    symmDiff_inter_distrib_right
    symmDiff_mem_powerset
    symmDiff_eq_union_diff
    symmDiff_as_complement
    symmDiff_eq_self_iff_empty
)
```

### 6.11 BoolAlg.PowerSetAlgebra.lean

```lean
export ZFC.BoolAlg.PowerSetAlgebra (
    Complement
    Complement_is_specified
    union_mem_powerset
    inter_mem_powerset
    complement_mem_powerset
    empty_in_powerset
    universe_in_PowerSet
    powerset_union_empty
    powerset_empty_union
    powerset_inter_universe
    powerset_universe_inter
    powerset_union_complement
    powerset_inter_complement
    powerset_union_distrib_inter
    powerset_inter_distrib_union
    powerset_compl_union
    powerset_compl_inter
    powerset_absorb_union_inter
    powerset_absorb_inter_union
    powerset_double_complement
    powerset_union_idempotent
    powerset_inter_idempotent
    powerset_union_comm
    powerset_inter_comm
    powerset_union_assoc
    powerset_inter_assoc
    powerset_inter_empty
    powerset_empty_inter
    powerset_complement_empty
    powerset_complement_universe
)
```

### 6.12 SetOps.SetOrder.lean

```lean
export SetOps.SetOrder (
  -- Core definitions
  isUpperBound isLowerBound isSupremum isInfimum
  isBoundedAbove isBoundedBelow
  -- Fundamental theorems
  empty_is_minimum empty_is_unique_minimum
  any_family_bounded_below
  inter_is_glb union_is_lub
  -- Order properties
  order_reflexive order_transitive order_antisymmetric
  -- Monotonicity
  union_monotone_left union_monotone_right
  inter_monotone_left inter_monotone_right
)
```

### 6.13 SetOps.SetStrictOrder.lean

```lean
export SetOps.SetStrictOrder (
  -- Basic properties
  subset_subseteq subseteq_subset_or_eq
  -- Strict order properties
  strict_order_irreflexive strict_order_asymmetric strict_order_transitive
  -- Mixed transitivity
  subset_transitive_mixed_left subset_transitive_mixed_right
  -- Order equivalence
  partial_to_strict_order strict_implies_partial
  -- Trichotomy and differentiation
  strict_order_trichotomy_partial empty_strict_subset_nonempty
  strict_subset_nonempty
)
```

### 6.14 Nat.Basic.lean

```lean
export Nat.Basic (
  -- Definiciones de orden-epsilón
  succ
  mem_succ_iff
  IsInductive
  IsTransitive
  StrictOrderMembershipGuided
  mem_StrictOrderMembershipGuided
  isTotalStrictOrderMembershipGuided
  isWellOrderMembershipGuided
  IsNat
  -- Propiedades elementales
  isNat_zero
  mem_succ_self
  subset_of_mem_succ
  mem_succ_of_mem
  succ_preserves_transitivity
  transitive_element_subset
  -- Teoremas de buena fundación
  not_mem_self
  not_mem_of_mem
  nat_no_three_cycle
  -- Propiedades estructurales (heredabilidad)
  nat_element_is_transitive
  nat_element_has_strict_total_order
  nat_element_has_well_order
  nat_element_is_nat
  -- Clausura bajo sucesores
  ne_succ_self
  succ_of_nat_is_transitive
  succ_of_nat_has_strict_total_order
  isNat_succ
  succ_injective
  succ_nonempty
  -- Segmentos iniciales y tricotomía
  IsInitialSegment
  initial_segment_of_nat_is_eq_or_mem
  inter_nat_is_initial_segment
  nat_subset_mem_or_eq
  trichotomy
  mem_trans
  mem_asymm
  nat_is_initial_segment
  nat_element_trichotomy
  no_nat_between
  -- Finitud y conjunto vacío
  nat_has_max
  eq_zero_or_exists_succ
  zero_mem_of_nat_nonempty
  -- Conjuntos inductivos
  nat_subset_inductive_set
  nat_in_inductive_set
  zero_in_inductive
  one_in_inductive
  two_in_inductive
  three_in_inductive
  -- Ejemplos concretos
  zero
  one
  two
  three
  zero_eq
  one_eq
  two_eq
  three_eq
)
```

### 6.15 OrderedPair.lean (Extensiones)

```lean
export SetOps.OrderedPair (
  OrderedPair_eq_of
  OrderedPair_eq_iff
  OrderedPair_in_powerset
)
```

### 6.16 SetOps.CartesianProduct.lean

```lean
export SetOps.CartesianProduct (
  SetOps.CartesianProduct
  CartesianProduct_is_specified
  OrderedPair_mem_CartesianProduct
  CartesianProduct_empty_left
  CartesianProduct_empty_right
  CartesianProduct_mono
  CartesianProduct_distrib_union_left
  CartesianProduct_distrib_union_right
  CartesianProduct_distrib_inter_left
  CartesianProduct_distrib_inter_right
)
```

### 6.17 Recursion.lean

**Namespace**: `ZFC.Induction.Recursion`
**Última modificación**: 2026-03-05
**Dependencias**: `Nat.Basic`, `Functions`, `Relations`, `SetOps.CartesianProduct`, `OrderedPair`, `Union`, `PowerSet` + anteriores

#### Sección 0: Lemas Auxiliares Locales

| Nombre | Descripción matemática | Firma Lean 4 |
|--------|----------------------|--------------|
| `function_domain_eq` | Si f : A → B entonces dom(f) = A | `function_domain_eq (f A B : U) (h : IsFunction f A B) : domain f = A` |
| `mem_succ_iff_local` | x ∈ σ n ↔ x ∈ n ∨ x = n | `mem_succ_iff_local (n x : U) : x ∈ σ n ↔ x ∈ n ∨ x = n` |
| `subset_succ_local` | n ⊆ σ n | `subset_succ_local (n : U) : n ⊆ σ n` |
| `zero_in_succ_nat` | ∅ ∈ σ n para todo n ∈ ω | `zero_in_succ_nat (n : U) (hn : n ∈ ω) : (∅ : U) ∈ σ n` |
| `succ_mem_succ_of_mem` | Si k ∈ n (ambos naturales) entonces σ k ∈ σ n | `succ_mem_succ_of_mem (k n : U) (hk_nat : IsNat k) (hn_nat : IsNat n) (hk : k ∈ n) : σ k ∈ σ n` |

#### Sección 1: Definición de Cómputo Local

**Definición** (`isComputation`): Un conjunto f es un *cómputo de longitud n* para la función recursiva con base a ∈ A y paso g : A → A si f : σ n → A, f(∅) = a, y ∀ k ∈ n, f(σ k) = g(f(k)).

```lean
def isComputation (n : U) (f : U) (A : U) (a : U) (g : U) : Prop :=
  IsFunction f (σ n) A ∧
  (apply f (∅ : U) = a) ∧
  (∀ k, k ∈ n → apply f (σ k) = apply g (apply f k))
```

**Dependencias de construcción**: `IsFunction`, `apply`, `succ` (σ)

| Nombre | Descripción matemática | Firma Lean 4 |
|--------|----------------------|--------------|
| `restriction_is_computation` | La restricción de un cómputo de longitud σ n a σ n es un cómputo de longitud n | `restriction_is_computation (A a g n : U) (hn : n ∈ ω) : ∀ f, isComputation (σ n) f A a g → isComputation n (restrict f (σ n)) A a g` |

#### Sección 2: Unicidad Local

| Nombre | Descripción matemática | Firma Lean 4 |
|--------|----------------------|--------------|
| `computation_uniqueness` | Para cada n ∈ ω, el cómputo de longitud n es único: si f₁ y f₂ son cómputos de longitud n para (A, a, g), entonces f₁ = f₂ | `computation_uniqueness (A a g : U) : ∀ n, n ∈ ω → ∀ f₁ f₂, isComputation n f₁ A a g → isComputation n f₂ A a g → f₁ = f₂` |

**Dependencias**: `induction_principle`, `ExtSet`, `apply_eq`, `apply_mem`, `OrderedPairSet_is_WellConstructed`, `mem_restrict_iff`, `restrict_subset`, `restriction_is_computation`

#### Sección 3: Compatibilidad y Uniones

**Definiciones**:

```lean
-- Dos funciones son compatibles si coinciden en la intersección de sus dominios
def areCompatible (f g : U) : Prop :=
  ∀ x, x ∈ ((domain f) ∩ (domain g)) → apply f x = apply g x

-- Una familia de funciones es un sistema compatible si son compatibles a pares
def isCompatibleSystem (F : U) : Prop :=
  ∀ f g, f ∈ F → g ∈ F → areCompatible f g
```

| Nombre | Descripción matemática | Firma Lean 4 |
|--------|----------------------|--------------|
| `union_compatible_is_function` | La unión de un sistema compatible de funciones es monovaluada | `union_compatible_is_function (F : U) (h_funcs : ∀ f, f ∈ F → ∃ A B, IsFunction f A B) (h_compat : isCompatibleSystem F) : IsSingleValued (⋃ F)` |

**Dependencias**: `mem_sUnion_iff`, `mem_inter_iff`, `apply_eq`, `mem_domain`

#### Sección 4: Existencia Local (Inducción)

| Nombre | Descripción matemática | Firma Lean 4 |
|--------|----------------------|--------------|
| `computation_existence` | Para todo n ∈ ω, existe un cómputo de longitud n | `computation_existence (A a g : U) (ha : a ∈ A) (hg : IsFunction g A A) : ∀ n, n ∈ ω → ∃ f, isComputation n f A a g` |

**Dependencias**: `induction_principle`, `Singleton`, `mem_union_iff`, `Singleton_is_specified`, `apply_eq`, `apply_mem`, `Eq_of_OrderedPairs_given_projections`

#### Sección 5: Lemas de Compatibilidad Global

| Nombre | Descripción matemática | Firma Lean 4 |
|--------|----------------------|--------------|
| `succ_subset_omega` | Para todo n ∈ ω, σ n ⊆ ω | `succ_subset_omega (n : U) (hn : n ∈ ω) : (σ n) ⊆ ω` |
| `computation_subset_omega_times_A` | Todo cómputo de longitud n ∈ ω es subconjunto de ω ×ₛ A | `computation_subset_omega_times_A (A a g n : U) (hn : n ∈ ω) (f : U) (hf : isComputation n f A a g) : f ⊆ ω ×ₛ A` |
| `succ_subset_succ_of_mem` | Si n₁ ∈ n₂ (con n₂ natural), entonces σ n₁ ⊆ σ n₂ | `succ_subset_succ_of_mem (n₁ n₂ : U) (hn₂_nat : IsNat n₂) (h : n₁ ∈ n₂) : σ n₁ ⊆ σ n₂` |
| `restriction_computation_general` | Si n₁ ∈ n₂ y f es cómputo de longitud n₂, entonces f restringido a σ n₁ es cómputo de longitud n₁ | `restriction_computation_general (A a g n₁ n₂ : U) (hn₁ : n₁ ∈ ω) (hn₂_nat : IsNat n₂) (hlt : n₁ ∈ n₂) (f : U) (hf : isComputation n₂ f A a g) : isComputation n₁ (restrict f (σ n₁)) A a g` |

**Definición** (`RecursionComputations`): El conjunto de todos los cómputos válidos para (A, a, g): el conjunto de funciones f ∈ 𝒫(ω ×ₛ A) tales que existe n ∈ ω con f un cómputo de longitud n.

```lean
noncomputable def RecursionComputations (A a g : U) : U :=
  sep (𝒫 (ω ×ₛ A)) (fun f => ∃ n, (n ∈ ω) ∧ (isComputation n f A a g))
```

**Dependencias de construcción**: `sep`, `PowerSet` (𝒫), `SetOps.CartesianProduct` (×ₛ), `isComputation`, `ω`

| Nombre | Descripción matemática | Firma Lean 4 |
|--------|----------------------|--------------|
| `computations_are_compatible` | Los cómputos en RecursionComputations A a g son compatibles a pares (isCompatibleSystem) | `computations_are_compatible (A a g : U) : isCompatibleSystem (RecursionComputations A a g)` |

**Dependencias de `computations_are_compatible`**: `mem_sep_iff`, `mem_inter_iff`, `trichotomy`, `restriction_computation_general`, `computation_uniqueness`, `restrict_apply`, `function_domain_eq`

#### Sección 6: Teorema de Recursión (Global)

| Nombre | Descripción matemática | Firma Lean 4 |
|--------|----------------------|--------------|
| `RecursionTheorem` | **Teorema de Recursión**: Para todo conjunto A, a ∈ A y g : A → A, existe una única función F : ω → A tal que F(∅) = a y F(σ n) = g(F(n)) para todo n ∈ ω | `RecursionTheorem (A a g : U) (ha : a ∈ A) (hg : IsFunction g A A) : ∃! F, IsFunction F ω A ∧ (apply F (∅ : U) = a) ∧ (∀ n, n ∈ ω → apply F (σ n) = apply g (apply F n))` |

**Descripción de la construcción**: F = ⋃(RecursionComputations A a g). La función F es la unión de todos los cómputos locales. La monovaluación sigue de `computations_are_compatible` + `union_compatible_is_function`. La unicidad se demuestra por inducción sobre ω usando `induction_principle`.

**Dependencias**: `RecursionComputations`, `computations_are_compatible`, `union_compatible_is_function`, `computation_existence`, `computation_subset_omega_times_A`, `induction_principle`, `ExtSet`, `apply_eq`, `apply_mem`, `OrderedPairSet_is_WellConstructed`, `mem_sep_iff`, `mem_powerset_iff`, `mem_sUnion_iff`

#### Exports de Recursion.lean

```lean
export Recursion (
  function_domain_eq
  mem_succ_iff_local
  subset_succ_local
  zero_in_succ_nat
  succ_mem_succ_of_mem
  isComputation
  restriction_is_computation
  computation_uniqueness
  areCompatible
  isCompatibleSystem
  union_compatible_is_function
  computation_existence
  succ_subset_omega
  computation_subset_omega_times_A
  succ_subset_succ_of_mem
  restriction_computation_general
  RecursionComputations
  computations_are_compatible
  RecursionTheorem
  -- Computation (step-indexed variant: g : ω ×ₛ A → A)
  isComputationStep
  restriction_is_computation_step
  restriction_computation_general_step
  computation_uniqueness_step
  computation_existence_step
  RecursionComputationsStep
  computations_are_compatible_step
  RecursionTheoremWithStep
  -- Computation (course-of-values: g : 𝒫(ω ×ₛ A) → A)
  isComputationCoV
  restriction_is_computation_cov
  restriction_computation_general_cov
  computation_uniqueness_cov
  computation_existence_cov
  RecursionComputationsCoV
  computations_are_compatible_cov
  RecursionCourseOfValues
  -- Canonical recursive function
  RecursiveFn
  RecursiveFn_is_function
  RecursiveFn_zero
  RecursiveFn_succ
  RecursiveFn_unique
)
```

### 6.18 PeanoImport.lean

**Namespace**: `ZFC.Peano.Import` (exportado a `ZFC`)
**Última modificación**: 2026-03-08

```lean
export Peano.Import (
  -- Definiciones
  fromPeano
  toPeano
  -- Sección 1: Biyección
  fromPeano_is_nat
  fromPeano_injective
  fromPeano_surjective
  fromPeano_toPeano
  toPeano_fromPeano
  toPeano_injective
  toPeano_surjective
  -- Sección 2: Compatibilidad algebraica básica
  toPeano_zero
  toPeano_succ
  -- Sección 3: Transporte de recursión
  recursion_transport
  recursion_transport_inv
  recursion_transport_step
  recursion_transport_step_inv
  -- Sección 4: Puentes de orden
  succ_mem_succ_iff
  fromPeano_lt_iff
  fromPeano_le_iff
)
-- Notaciones scoped en ZFC:
-- scoped notation "ΠZ" => Peano.Import.fromPeano
-- scoped notation "ZΠ" => Peano.Import.toPeano
```

### 6.19 Nat.Add.lean

**Namespace**: `ZFC.Nat.Add` (exportado a `ZFC`)
**Última modificación**: 2026-03-08
**Dependencias**: `Nat.Basic`, `Infinity`, `Recursion`, `PeanoImport`, `PeanoNatLib.PeanoNatAdd`

```lean
export Nat.Add (
  -- Sección 1: succFn
  succFn
  mem_succFn
  succFn_is_function
  succFn_apply
  -- Sección 2: addFn y add
  addFn
  addFn_is_function
  add
  add_eq
  add_in_Omega
  -- Sección 3: ecuaciones de recursión
  add_zero
  add_succ
  -- Sección 4: puente
  fromPeano_add
  -- Sección 5: propiedades algebraicas
  zero_add
  add_comm_Omega
  add_assoc_Omega
  -- Sección 6: propiedades adicionales
  succ_add_Omega
  add_left_cancel_Omega
  add_right_cancel_Omega
  add_pos_left_Omega
  le_then_exists_add_Omega
  add_lt_of_lt_Omega
)
```

### 6.20 Nat.Mul.lean

**Namespace**: `ZFC.Nat.Mul` (exportado a `ZFC`)
**Última modificación**: 2026-03-08
**Dependencias**: `Nat.Basic`, `Infinity`, `Recursion`, `PeanoImport`, `Nat.Add`, `PeanoNatLib.PeanoNatMul`

```lean
export Nat.Mul (
  -- Sección 1: mulFn y mul
  mulFn
  mulFn_is_function
  mul
  mul_eq
  mul_in_Omega
  -- Sección 2: ecuaciones de recursión
  mul_zero
  mul_succ
  -- Sección 3: puente
  fromPeano_mul
  -- Sección 4: propiedades algebraicas
  zero_mul_Omega
  mul_comm_Omega
  succ_mul_Omega
  mul_one_Omega
  one_mul_Omega
  mul_assoc_Omega
  mul_ldistr_Omega
  mul_rdistr_Omega
)
```

### 6.21 Nat.Sub.lean

**Namespace**: `ZFC.Nat.Sub` (exportado a `ZFC`)
**Última modificación**: 2026-03-21
**Dependencias**: `Nat.Basic`, `Infinity`, `Recursion`, `PeanoImport`, `Nat.Add`, `PeanoNatLib.PeanoNatSub`

```lean
export Nat.Sub (
  -- Sección 0: predecessorFn
  predecessorFn
  mem_predecessorFn
  predecessorFn_is_function
  predecessorFn_apply
  -- Sección 1: sub
  subFn
  subFn_is_function
  sub
  sub_eq
  sub_in_Omega
  -- Sección 2: ecuaciones de recursión
  sub_zero
  sub_succ
  -- Sección 4: puente
  fromPeano_sub
  -- Sección 5: propiedades algebraicas
  zero_sub_Omega
  sub_self_Omega
  sub_succ_succ_Omega
  sub_k_add_k_Omega
  add_k_sub_k_Omega
  sub_le_self_Omega
  sub_pos_iff_lt_Omega
)
```

### 6.22 Nat.Div.lean

**Namespace**: `ZFC.Nat.Div` (exportado a `ZFC`)
**Última modificación**: 2026-03-21
**Dependencias**: `Nat.Basic`, `Infinity`, `Recursion`, `PeanoImport`, `Nat.Add`, `Nat.Mul`, `Nat.Sub`, `PeanoNatLib.PeanoNatDiv`

```lean
export Nat.Div (
  -- Sección 0: definiciones
  divOf
  modOf
  -- Sección 1: clausura
  divOf_in_Omega
  modOf_in_Omega
  -- Sección 2: teoremas puente
  fromPeano_div
  fromPeano_mod
  -- Sección 3: propiedades algebraicas
  divMod_eq_Omega
  mod_lt_divisor_Omega
  div_of_lt_Omega
  mod_of_lt_Omega
  div_le_self_Omega
)
```

### 6.23 Nat.Pow.lean

**Namespace**: `ZFC.Nat.Pow` (exportado a `ZFC`)
**Última modificación**: 2026-03-22
**Dependencias**: `Nat.Basic`, `Infinity`, `Recursion`, `PeanoImport`, `Nat.Mul`, `PeanoNatLib.PeanoNatPow`

```lean
export Nat.Pow (
  -- Sección 1: powFn y pow
  powFn
  powFn_is_function
  pow
  pow_eq
  pow_in_Omega
  -- Sección 2: ecuaciones de recursión
  pow_zero
  pow_succ
  -- Sección 3: puente
  fromPeano_pow
  -- Sección 4: propiedades algebraicas
  zero_pow_Omega
  one_pow_Omega
  pow_one_Omega
  pow_ne_zero_Omega
  pow_two_Omega
  pow_add_eq_mul_pow_Omega
  mul_pow_Omega
  pow_pow_eq_pow_mul_Omega
)
```

### 6.24 Nat.Arith.lean

**Namespace**: `ZFC.Nat.Arith` (exportado a `ZFC`)
**Última modificación**: 2026-03-22
**Dependencias**: `Nat.Basic`, `Infinity`, `Recursion`, `PeanoImport`, `Nat.Add`, `Nat.Mul`, `Nat.Sub`, `Nat.Div`, `PeanoNatLib.PeanoNatArith`

```lean
export Nat.Arith (
  -- Sección 0: predicado de divisibilidad
  divides
  -- Sección 1: puente
  fromPeano_divides
  -- Sección 2: propiedades básicas de divisibilidad
  divides_refl_Omega
  one_divides_Omega
  divides_zero_Omega
  zero_divides_iff_Omega
  divides_trans_Omega
  divides_mul_right_Omega
  divides_mul_left_Omega
  divides_add_Omega
  divides_sub_Omega
  divides_modOf_Omega
  divides_le_Omega
  antisymm_divides_Omega
  -- Sección 2.5: div/mod nativos ZFC
  div
  mod
  div_eq
  mod_eq
  div_in_Omega
  mod_in_Omega
  div_zero_left
  mod_zero_left
  div_succ_wrap
  mod_succ_wrap
  div_succ_continue
  mod_succ_continue
  divMod_eq_ZFC
  mod_lt_divisor_ZFC
  div_eq_divOf
  mod_eq_modOf
  -- Sección 3: definiciones gcdOf, lcmOf
  gcdOf
  lcmOf
  gcdOf_in_Omega
  lcmOf_in_Omega
  -- Sección 4: puente para gcd/lcm
  fromPeano_gcd
  fromPeano_lcm
  -- Sección 5: propiedades de gcdOf
  gcdOf_divides_left_Omega
  gcdOf_divides_right_Omega
  gcdOf_greatest_Omega
  gcdOf_comm_Omega
  -- Sección 6: propiedades de lcmOf
  lcmOf_multiple_left_Omega
  lcmOf_multiple_right_Omega
  lcmOf_comm_Omega
  -- Sección 7: Bézout
  bezout_natform_Omega
)
```

### 6.25 BoolAlg.Atomic.lean

**Namespace**: `ZFC.BoolAlg.Atomic` (exportado a `ZFC`)
**Última modificación**: 2026-03-24
**Dependencias**: `BoolAlg.PowerSetAlgebra`, `SetOps.SetOrder`, `SetOps.SetStrictOrder` + anteriores

```lean
export BoolAlg.Atomic (
  -- Definiciones
  isAtom
  isAtomic
  Atoms
  atomBelow
  -- Caracterizaciones de átomo
  isAtom_alt
  atom_iff_singleton
  -- Auxiliares sobre singletons
  singleton_subset
  singleton_mem_powerset
  singleton_nonempty
  subset_singleton
  -- Teoremas principales
  singleton_is_atom
  atom_has_unique_element
  atom_is_singleton
  -- Familia de átomos
  Atoms_is_specified
  Atoms_eq_singletons
  -- Atomicidad
  powerset_is_atomic
  element_is_union_of_atoms
  -- Relación átomo-debajo
  singleton_below_iff
)
```

### 6.26 Nat.Factorial.lean

**Namespace**: `ZFC.Nat.Factorial` (exportado a `ZFC`)
**Última modificación**: 2026-03-24
**Dependencias**: `Nat.Basic`, `Infinity`, `Recursion`, `PeanoImport`, `Nat.Mul`, `PeanoNatLib.PeanoNatFactorial`

```lean
export Nat.Factorial (
  -- Sección 0: definición
  factorialOf
  -- Sección 1: clausura
  factorialOf_in_Omega
  -- Sección 2: puente
  fromPeano_factorial
  -- Sección 3: valores concretos y recursión
  factorialOf_zero
  factorialOf_one
  factorialOf_two
  factorialOf_succ
  -- Sección 4: positividad y cotas
  factorialOf_ne_zero
  factorialOf_pos
  factorialOf_ge_one
  factorialOf_le_succ
  factorialOf_le_mono
)
```

### 6.27 Nat.Gcd.lean

**Namespace**: `ZFC.Nat.Gcd` (exportado a `ZFC`)
**Última modificación**: 2026-03-24
**Dependencias**: `Nat.Basic`, `Infinity`, `Recursion`, `PeanoImport`, `Nat.Add`, `Nat.Mul`, `Nat.Sub`, `Nat.Div`, `Nat.Arith`

```lean
export Nat.Gcd (
  -- Definiciones
  gcd
  lcm
  -- GCD propiedades básicas
  gcd_in_Omega
  gcd_zero
  gcd_pos_step
  gcd_eq_gcdOf
  -- GCD divisibilidad
  gcd_divides_left_Omega
  gcd_divides_right_Omega
  gcd_greatest_Omega
  gcd_comm_Omega
  -- LCM propiedades
  lcm_in_Omega
  lcm_eq_lcmOf
  lcm_multiple_left_Omega
  lcm_multiple_right_Omega
  lcm_comm_Omega
)
```

### 6.28 Nat.Primes.lean

**Namespace**: `ZFC.Nat.Primes` (exportado a `ZFC`)
**Última modificación**: 2026-03-25
**Dependencias**: `Nat.Arith`, `Nat.Gcd`, `PeanoNatLib.PeanoNatPrimes`

```lean
export Nat.Primes (
  -- Definición
  isPrime
  -- Teorema puente
  fromPeano_prime
  -- Propiedades básicas
  isPrime_in_Omega
  isPrime_ne_zero
  isPrime_ne_one
  isPrime_ge_two
  isPrime_prime_divisors
  -- Existencia de divisor primo
  exists_prime_divisor_ZFC
  -- Teorema Fundamental de la Aritmética (Enfoque A)
  exists_prime_factorization_ZFC
  unique_prime_factorization_ZFC
)
```

### 6.29 Nat.Binom.lean

**Namespace**: `ZFC.Nat.Binom` (exportado a `ZFC`)
**Última modificación**: 2026-03-25
**Dependencias**: `Nat.Add`, `Nat.Mul`, `Nat.Sub`, `Nat.Factorial`, `PeanoNatLib.PeanoNatBinom`

```lean
export Nat.Binom (
  -- §0: definition
  binomOf
  -- §1: closure
  binomOf_in_Omega
  -- §2: bridge
  fromPeano_binom
  -- §3: concrete values
  binomOf_zero_zero
  binomOf_succ_zero
  binomOf_zero_succ
  -- §4: Pascal's rule
  binomOf_pascal
  -- §5: algebraic properties
  binomOf_n_zero
  binomOf_n_one
  binomOf_self
  binomOf_succ_n_by_n
  -- §6: vanishing and positivity
  binomOf_eq_zero_of_gt
  binomOf_pos
  -- §7: factorial connection
  binomOf_mul_factorials
)
```

### 6.30 Nat.MaxMin.lean

**Namespace**: `ZFC.Nat.MaxMin` (exportado a `ZFC`)
**Última modificación**: 2026-03-26
**Dependencias**: `Nat.Basic`, `Infinity`, `PeanoImport`, `PeanoNatLib.PeanoNatMaxMin`

```lean
export Nat.MaxMin (
  -- §0: definitions
  maxOf
  minOf
  -- §1: closure
  maxOf_in_Omega
  minOf_in_Omega
  -- §2: bridge
  fromPeano_max
  fromPeano_min
  -- §3: idempotence
  maxOf_idem
  minOf_idem
  -- §4: commutativity
  maxOf_comm
  minOf_comm
  -- §5: associativity
  maxOf_assoc
  minOf_assoc
  -- §6: identity/annihilator with ∅
  maxOf_zero_left
  maxOf_zero_right
  minOf_zero_left
  minOf_zero_right
  -- §7: upper/lower bound
  le_maxOf_left
  le_maxOf_right
  maxOf_le
  minOf_le_left
  minOf_le_right
  le_minOf
  -- §8: characterization via ≤
  maxOf_eq_right
  maxOf_eq_left
  minOf_eq_left
  minOf_eq_right
  -- §9: max/min is one of the arguments
  maxOf_is_any
  minOf_is_any
  -- §10: max = min iff equal
  eq_iff_maxOf_eq_minOf
)
```

### 6.31 Nat.NewtonBinom.lean

**Namespace**: `ZFC.Nat.NewtonBinom` (exportado a `ZFC`)
**Última modificación**: 2026-03-26
**Dependencias**: `Nat.Add`, `Nat.Mul`, `Nat.Sub`, `Nat.Pow`, `Nat.Binom`, `PeanoNatLib.PeanoNatNewtonBinom`

```lean
export Nat.NewtonBinom (
  -- §0: definition
  binomTermOf
  -- §1: closure
  binomTermOf_in_Omega
  -- §2: bridge
  fromPeano_binomTerm
  -- §3: concrete values
  binomTermOf_zero
  binomTermOf_self
  -- §4: expansion
  binomTermOf_eq
  -- §5: power splitting
  pow_add_split_Omega
  -- §6: Newton's binomial theorem
  newton_binom_peano
  -- §7: sum of binomial coefficients
  sum_binom_eq_pow_two_peano
  -- §8: growth comparison
  exists_nm_growth_Omega
)
```

### 6.32 Nat.WellFounded.lean

**Namespace**: `ZFC.Nat.WellFounded` (exportado a `ZFC`)
**Última modificación**: 2026-03-26
**Dependencias**: `Nat.Basic`, `Infinity`, `PeanoImport`, `PeanoNatLib.PeanoNatWellFounded`

```lean
export Nat.WellFounded (
  -- §0: well-foundedness
  acc_lt_Omega
  -- §1: well-ordering principle
  well_ordering_Omega
  well_ordering_Omega_exists
)
```

### 6.33 Peano.FiniteSequences.lean

**Namespace**: `ZFC.Peano.FiniteSequences` (sin export a `ZFC`)
**Última modificación**: 2026-03-27
**Dependencias**: `Nat.Add` + anteriores

*(Este módulo no exporta al namespace `ZFC`. Todas las definiciones y teoremas se acceden vía `open ZFC.Peano.FiniteSequences` o con nombre cualificado `Peano.FiniteSequences.isFinSeq`, etc.)*

**Contenido del namespace** (3 definiciones, 15 teoremas):
- `isFinSeq`, `FinSeqSet`, `appendElem`
- `isFinSeq_in_Omega`, `isFinSeq_is_function`, `isFinSeq_domain`, `isFinSeq_subset`, `isFinSeq_unique_length`, `isFinSeq_apply_mem`, `isFinSeq_pair_mem`, `isFinSeq_ext`
- `mem_FinSeqSet_iff`, `isFinSeq_mem_FinSeqSet`
- `isFinSeq_empty`, `isFinSeq_zero_unique`, `FinSeqSet_zero`
- `appendElem_is_specified`, `isFinSeq_appendElem`, `appendElem_apply_last`, `appendElem_apply_prev`, `appendElem_inj`
- `isFinSeq_restriction`

### 6.34 SetOps.FiniteSets.lean

**Namespace**: `ZFC.SetOps.FiniteSets` (exportado a `ZFC`)
**Última modificación**: 2026-03-29
**Dependencias**: `Nat.Basic`, `Infinity` + anteriores

```lean
export SetOps.FiniteSets (
  -- Identity bijection
  id_is_function id_is_injective id_is_surjective id_is_bijection
  equipotent_refl
  -- Definition
  isFiniteSet
  -- Basic properties
  empty_is_finite nat_is_finite
  -- Inverse bijection
  inverse_pair_iff
  bijection_inverse_is_function bijection_inverse_injective
  bijection_inverse_surjective bijection_inverse_is_bijection
  equipotent_symm
  -- Composition
  comp_injective comp_surjective comp_bijection
  equipotent_trans
  -- Closure
  finite_equipotent
  -- Singleton
  singleton_is_finite
  -- Adding an element
  finite_union_singleton
)
```

### 6.35 Peano.FiniteSequencesArith.lean

**Namespace**: `ZFC.Peano.FiniteSequencesArith` (exportado a `ZFC`)
**Última modificación**: 2026-03-30
**Dependencias**: `Nat.Mul`, `Peano.FiniteSequences`, `SetOps.FiniteSets` + anteriores

```lean
export Peano.FiniteSequencesArith (
  -- Section 1: Summation step function
  sumStepFn mem_sumStepFn sumStepFn_is_function sumStepFn_apply
  -- Section 2: Summation
  seqSumFn seqSumFn_is_function seqSum seqSum_zero seqSum_succ seqSum_in_Omega seqSum_singleton
  -- Section 3: Product step function
  prodStepFn prodStepFn_is_function prodStepFn_apply
  -- Section 4: Numeric product
  seqProdFn seqProdFn_is_function seqProd seqProd_zero seqProd_succ seqProd_in_Omega seqProd_singleton
  -- Section 5: Cartesian product of a family
  familyProduct mem_familyProduct familyProduct_zero familyProduct_succ_char
  -- Section 6: Cardinality product theorem
  card_product_two card_familyProduct
)
```

### 6.36 Peano.FiniteSequencesBridge.lean

**Namespace**: `ZFC.Peano.FiniteSequencesBridge` (exportado a `ZFC`)
**Última modificación**: 2026-03-30
**Dependencias**: `Peano.FiniteSequencesArith`, `Nat.Primes` + anteriores

```lean
export Peano.FiniteSequencesBridge (
    -- §1: nth
    nth
    nth_eq_apply
    nth_mem
    nth_appendElem_last
    nth_appendElem_prev
    -- §2: General seqProd recursion
    seqProd_zero_gen
    seqProd_succ_gen
    seqProd_in_Omega_gen
    -- §3: seqProd extensionality
    seqProd_ext
    -- §4: DList → ZFC bridge
    dlistToSeq
    dlistLen
    dlistToSeq_isFinSeq
    dlistToSeq_domain
    dlistToSeq_isFinSeq_domain
    dlistToSeq_seqLength
    dlistLen_in_Omega
    dlistToSeq_apply_last
    dlistToSeq_apply_prev
    -- §5: seqProd correspondence
    dlistToSeq_seqProd
    -- §6: isPrimeSeq
    isPrimeSeq
    dlistToSeq_isPrimeSeq
    -- §7: TFA native
    exists_prime_factorization_native
    unique_prime_factorization_native
)
```

### 6.37 BoolAlg.FiniteCofinite.lean

**Namespace**: `ZFC.BoolAlg.FiniteCofinite` (exportado a `ZFC`)
**Última modificación**: 2026-04-01
**Dependencias**: `BoolAlg.Complete`, `SetOps.FiniteSets`, `Nat.Add`, `Cardinality` + anteriores

```lean
export BoolAlg.FiniteCofinite (
    -- Finite set closure
    finite_subset finite_union Omega_not_finite
    -- Parity
    double_injective
    EvenSet EvenSet_is_specified EvenSet_subset_Omega
    even_or_odd even_ne_odd
    EvenSet_infinite OddSet_infinite
    -- Definitions
    isCofinite isFinCof FinCofAlg FinCofAlg_is_specified
    FinCofAlg_subset_powerset
    -- Boolean algebra closure
    FinCofAlg_empty FinCofAlg_universe
    FinCofAlg_complement FinCofAlg_union FinCofAlg_inter
    -- Not complete
    EvenSet_not_in_FinCofAlg
    FinCofAlg_not_complete
)
```

### 6.38 BoolAlg.Complete.lean

**Namespace**: `ZFC.BoolAlg.Complete` (exportado a `ZFC`)
**Última modificación**: 2026-04-07
**Dependencias**: `BoolAlg.PowerSetAlgebra`, `BoolAlg.GenDeMorgan`, `SetOps.SetOrder`, `BoolAlg.Atomic` + anteriores

```lean
export BoolAlg.Complete (
    -- Definiciones
    isSupremumIn isInfimumIn isCompleteLattice
    isCompleteAtomicBA
    -- Unicidad
    supremumIn_unique infimumIn_unique
    -- Supremo en 𝒫(A)
    sUnion_subset_of_family
    sUnion_mem_powerset_of_family
    sUnion_is_supremumIn_powerset
    -- Ínfimo en 𝒫(A)
    interSet_subset_of_family
    interSet_mem_powerset_of_family
    interSet_is_infimumIn_powerset
    universe_is_infimumIn_powerset_empty
    -- Completitud
    powerset_is_complete_lattice
    powerset_is_complete_atomic_BA
)
```

### 6.39 BoolAlg.FiniteBA.lean

**Namespace**: `ZFC.BoolAlg.FiniteBA` (exportado a `ZFC`)
**Última modificación**: 2026-04-02
**Dependencias**: `Cardinal.FinitePowerSet`, `BoolAlg.Representation` + anteriores

```lean
export BoolAlg.FiniteBA (
    atoms_equipotent_base
    finite_atoms_of_finite
    finite_of_finite_atoms
    BA_cardinality_via_atoms
    finite_powerset_is_finite
    finite_BA_cardinality
    finite_BA_cardinality_atoms
    finite_complete_atomic_BA
)
```

### 6.40 BoolAlg.BoolRingBA.lean

**Namespace**: `ZFC.BoolAlg.BoolRingBA` (exportado a `ZFC`)
**Última modificación**: 2026-04-02
**Dependencias**: `BoolAlg.Ring` + anteriores

```lean
export BoolAlg.BoolRingBA (
    ring_join_eq_union
    ring_compl_eq_complement
    BA_symmDiff_eq_ring_add
    BA_ring_BA_join
    BA_ring_BA_complement
    BA_ring_BA_meet
    ring_BA_ring_add
    ring_BA_ring_mul
    symmDiff_via_complement
    ring_char_two
    ring_idempotent
    complement_involution
    ring_add_complement_eq_universe
)
```

### 6.41 BoolAlg.Representation.lean

**Namespace**: `ZFC.BoolAlg.Representation` (exportado a `ZFC`)
**Última modificación**: 2026-04-02
**Dependencias**: `BoolAlg.Complete`, `BoolAlg.Atomic`, `BoolAlg.GenDeMorgan`, `BoolAlg.GenDistributive`, `Cardinal.Basic`, `SetOps.Functions` + anteriores

```lean
export BoolAlg.Representation (
    atomsSingletonMap
    atomsSingletonMap_spec
    atomsSingletonMap_is_function
    atomsSingletonMap_is_injective
    atomsSingletonMap_is_surjective
    atomsSingletonMap_is_bijection
    A_equipotent_Atoms
    atomsBelow
    mem_atomsBelow_iff
    atomsBelow_mem_powerset_Atoms
    atomsBelow_eq_singletons_in
    atomsBelowMap
    atomsBelowMap_spec
    atomsBelowMap_is_function
    atomsBelowMap_is_injective
    atomsBelowMap_is_surjective
    atomsBelowMap_is_bijection
    representation_equipotent
    union_atomsBelow_eq
    atomsBelow_of_union
    union_atoms_mem_powerset
    atomsBelowMap_preserves_empty
    atomsBelowMap_preserves_universe
    atomsBelowMap_preserves_union
    atomsBelowMap_preserves_inter
    atomsBelowMap_preserves_complement
    representation_theorem
)
```

### 6.42 Cardinal.FinitePowerSet.lean

**Namespace**: `ZFC.Cardinal.FinitePowerSet` (exportado a `ZFC`)
**Última modificación**: 2026-04-02
**Dependencias**: `SetOps.FiniteSets`, `Nat.Pow`, `BoolAlg.FiniteCofinite` + anteriores

```lean
export Cardinal.FinitePowerSet (
    equipotent_union_singleton
    sdiff_singleton_union
    union_sdiff_cancel
    union_singleton_sdiff_cancel
    disjoint_union_equipotent
    removeElemMap
    removeElemMap_is_specified
    removeElemMap_is_bijection
    powerset_without_elem
    powerset_halves_disjoint
    powerset_halves_union
    mul_two_eq_double
    powerset_cardinality
)
```

## 7. Estado de Proyección por Módulo

### 7.1 Leyenda de Estados

- ✅ **Completo**: Todas las definiciones, teoremas y exports están proyectados
- 🔶 **Parcial**: Solo algunas definiciones/teoremas principales están proyectados
- ❌ **No proyectado**: El archivo no está documentado en este REFERENCE.md

### 7.2 Archivos Completamente Proyectados

Los siguientes archivos están **completamente documentados** con todas sus definiciones, teoremas y exports:

- `Prelim.lean` - ExistsUnique
- `Extension.lean` - Extensionalidad, subconjuntos, disjunción
- `Existence.lean` - Conjunto vacío
- `Specification.lean` - Especificación, intersección, diferencia
- `Pairing.lean` - Pares, singletons, pares ordenados
- `Union.lean` - Uniones familiares y binarias
- `PowerSet.lean` - Axioma y operaciones de conjunto potencia
- `BoolAlg.Basic.lean` - Teoremas de álgebra booleana
- `BoolAlg.Ring.lean` - Estructura de anillo booleano: symmDiff como suma, intersección como producto, leyes de asociatividad y distributividad
- `BoolAlg.PowerSetAlgebra.lean` - Álgebra booleana de conjuntos potencia: complemento, leyes de De Morgan, distributividad, absorción, idempotencia
- `Nat.Basic.lean` - Números naturales como ordinales de von Neumann
- `Infinity.lean` - Axioma de infinito y conjunto ω de todos los naturales
- `BoolAlg.GenDeMorgan.lean` - Leyes de De Morgan generalizadas para familias de conjuntos
- `BoolAlg.GenDistributive.lean` - Leyes distributivas generalizadas para familias de conjuntos
- `SetOps.SetOrder.lean` - Teoría de órdenes parciales, cotas, supremos e ínfimos
- `SetOps.SetStrictOrder.lean` - Teoría de órdenes estrictos, irreflexividad, asimetría y transitividad
- `OrderedPair.lean` - Extensiones del par ordenado de Kuratowski, igualdad y propiedades
- `SetOps.CartesianProduct.lean` - Producto cartesiano A ×ₛ B, propiedades distributivas y monotonicidad
- `SetOps.Functions.lean` - Funciones inyectivas, suryectivas, biyectivas, composición, restricción
- `SetOps.Relations.lean` - Relaciones, equivalencia, orden, imagen de relaciones
- `Induction.Recursion.lean` - Teorema de recursión para números naturales, cómputos de longitud n
- `PeanoImport.lean` - Isomorfismo Von Neumann ↔ Peano completo: biyección, compatibilidad algebraica, transporte de recursión (simple y con paso), puentes de orden
- `Nat.Add.lean` - Suma en ω: definición vía Recursión, teorema puente `fromPeano_add`, propiedades de semianillo (conmutatividad, asociatividad, cancelación, monotonía)
- `Nat.Mul.lean` - Multiplicación en ω: definición vía Recursión, teorema puente `fromPeano_mul`, propiedades de anillo conmutativo (distributividad, asociatividad, identidades)
- `Nat.Sub.lean` - Sustracción saturada (monus) en ω: definición vía Recursión con predecessorFn, teorema puente `fromPeano_sub`, propiedades (cancelación, orden, positividad)
- `Nat.Div.lean` - División euclídea en ω: Patrón B (bridge-only) vía isomorfismo, teoremas puente `fromPeano_div`/`fromPeano_mod`, identidad euclídea, cota del resto, propiedades de cociente/resto
- `Nat.Pow.lean` - Potenciación en ω: Patrón RecursiveFn (mulFn como paso), teorema puente `fromPeano_pow`, propiedades algebraicas (leyes de exponentes, identidades)
- `Nat.Arith.lean` - Aritmética avanzada en ω: predicado `divides` (ZFC nativo), `div`/`mod` nativos vía RecursiveFn + `divMod_stepFn`, `gcdOf`/`lcmOf` Patrón B, teorema de Bézout (forma substractiva), 13 propiedades de divisibilidad
- `BoolAlg.Atomic.lean` - Álgebra de Boole atómica en conjuntos potencia: 4 definiciones (`isAtom`, `isAtomic`, `Atoms`, `atomBelow`), 14 teoremas (singletons ↔ átomos, atomicidad de 𝒫(A), descomposición en átomos)
- `Nat.Factorial.lean` - Factorial en ω: Patrón B (bridge-only) vía isomorfismo, 1 definición (`factorialOf`), teorema puente `fromPeano_factorial`, valores concretos (0!, 1!, 2!), ecuación de recursión, positividad y monotonía
- `Nat.Gcd.lean` - GCD y LCM en ω: GCD ZFC-nativo vía algoritmo euclídeo con RecursiveFn sobre ω ×ₛ ω, 2 definiciones (`gcd`, `lcm`), teoremas puente `gcd_eq_gcdOf`/`lcm_eq_lcmOf`, ecuaciones del algoritmo (caso base + paso), 4 propiedades de divisibilidad del GCD, 3 propiedades del LCM, 17 exports
- `Nat.Primes.lean` - Primalidad y TFA en ω: definición ZFC-nativa `isPrime`, teorema puente `fromPeano_prime` (Peano.Arith.Prime ↔ isPrime), propiedades básicas (∈ω, ≠∅, ≠σ∅, ≥2, divisores), existencia de divisor primo, TFA Existencia y Unicidad (Enfoque A: DList ℕ₀ en lado Peano), 11 exports
- `Nat.Binom.lean` - Coeficientes binomiales en ω: Patrón B (bridge-only) vía isomorfismo Peano, 1 definición (`binomOf`), teorema puente `fromPeano_binom`, valores concretos (C(0,0), C(σn,0), C(0,σk)), regla de Pascal, propiedades algebraicas (C(n,0)=1, C(n,1)=n, C(n,n)=1, C(σn,n)=σn), anulación/positividad, conexión con factorial (C(n,k)·k!·(n-k)!=n!), 15 exports
- `Nat.MaxMin.lean` - Máximo y mínimo en ω: Patrón B (bridge-only) vía isomorfismo Peano, 2 definiciones (`maxOf`, `minOf`), teoremas puente `fromPeano_max`/`fromPeano_min`, propiedades de retículo (idempotencia, conmutatividad, asociatividad, identidad/aniquilador con ∅), cotas superior/inferior, caracterización vía ≤, max/min es uno de los argumentos, max=min⇔iguales, 31 exports
- `Nat.NewtonBinom.lean` - Término binomial y teorema de Newton en ω: Patrón B (bridge-only) con 4 argumentos, 1 definición (`binomTermOf`), teorema puente `fromPeano_binomTerm`, valores concretos (k=0, k=n), expansión C(n,k)·a^k·b^(n−k), separación de potencias n^(m+k)=n^m·n^k, teorema binomial de Newton (nivel Peano→ZFC), Σ C(n,k)=2^n, comparación de crecimiento existencial, 12 exports
- `Nat.WellFounded.lean` - Buen fundamento y principio de buena ordenación en ω: accesibilidad vía `nat_mem_wf`, principio de buena ordenación con unicidad (transportado desde Peano), forma simplificada sin unicidad, 3 exports
- `Peano.FiniteSequences.lean` - Secuencias finitas en ZFC: functions f : n → A con n ∈ ω, 3 definiciones (`isFinSeq`, `FinSeqSet`, `appendElem`), 15 teoremas (predicado central, secuencia vacía, append, descomposición), sin exports a `ZFC`
- `SetOps.FiniteSets.lean` - Conjuntos finitos en ZFC: definición `isFiniteSet` (∃ n ∈ ω, A ≃ₛ n), infraestructura de biyecciones (identidad, inversa, composición), equipotencia como relación de equivalencia (refl/symm/trans), 1 definición + 21 teoremas + 22 exports
- `Peano.FiniteSequencesArith.lean` - Aritmética de secuencias finitas en ZFC: sumación/producto numérico (seqSum/seqProd), producto cartesiano de familias (familyProduct), teoremas de cardinalidad (card_product_two, card_familyProduct), 7 definiciones + 18 teoremas + 33 exports
- `Peano.FiniteSequencesBridge.lean` - Puente DList ↔ ZFC y TFA nativo: nth (acceso a elementos), seqProd generalizado (zero_gen, succ_gen, extensionalidad), dlistToSeq/dlistLen (conversión DList→ZFC), isPrimeSeq (secuencia de primos), TFA existencia/unicidad con secuencias ZFC-nativas, 4 definiciones + 15 teoremas + 23 exports
- `BoolAlg.FiniteCofinite.lean` - Álgebra booleana finita/cofinita: definiciones `isCofinite`, `isFinCof`, `FinCofAlg`, `EvenSet`; clausura de finitos (subconjunto, unión, ω no finito); paridad (even_or_odd, even_ne_odd, double_injective, EvenSet/OddSet infinitos); estructura de álgebra booleana (∅, A, complemento, unión, intersección ∈ FinCofAlg); contraejemplo FinCofAlg(ω) NO es retículo completo. 4 definiciones + 19 teoremas + 22 exports
- `BoolAlg.Complete.lean` - Álgebra booleana completa atómica en conjuntos potencia: definiciones `isSupremumIn`, `isInfimumIn`, `isCompleteLattice`, `isCompleteAtomicBA`; supremo/ínfimo en 𝒫(A) vía ⋃/⋂; unicidad; `powerset_is_complete_lattice`; `powerset_is_complete_atomic_BA`. 4 definiciones + 11 teoremas + 15 exports
- `BoolAlg.FiniteBA.lean` - Cardinalidad de BA finita: equipotencia de átomos con base, finiteness bidireccional átomos↔base, cardinalidad vía átomos (representación), |𝒫(A)|=2^n para A finito, BA finita es completa atómica. 0 definiciones + 8 teoremas + 8 exports
- `BoolAlg.BoolRingBA.lean` - Correspondencia Anillo Booleano ↔ Álgebra Booleana: X△Y△(X∩Y)=X∪Y, A△X=X^∁[A], (X∩Y^∁)∪(X^∁∩Y)=X△Y, round-trip BA→BR→BA (join/complement/meet), round-trip BR→BA→BR (add/mul), char 2, idempotencia, involución, X△X^∁=A. 0 definiciones + 13 teoremas + 13 exports
- `BoolAlg.Representation.lean` - Teorema de Representación de Stone (forma concreta): biyección A↔Atoms(A) vía singletons, biyección 𝒫(A)↔𝒫(Atoms A) vía atomsBelowMap, preservación de ∪/∩/complemento. 3 definiciones + 24 teoremas + 27 exports
- `Cardinal.FinitePowerSet.lean` - Cardinalidad del conjunto potencia finito: |𝒫(F)|=2^n, extensión de biyecciones, unión disjunta aditiva, descomposición en mitades, removeElemMap. 1 definición + 12 teoremas + 13 exports

### 7.3 Archivos Parcialmente Proyectados

Los siguientes archivos tienen **documentación parcial** (solo definiciones/teoremas principales):

- (Ninguno actualmente)

### 7.4 Archivos Casi Completos (con `sorry` documentados)

Los siguientes archivos están **casi completos** pero contienen algunos `sorry` documentados:

- (Ninguno actualmente - todos los módulos de Core Theory están 100% completos)

**Nota**: `SetOps.Functions.lean` está ahora ✅ **100% completo** (0 sorry).
**Nota**: `Induction.Recursion.lean` está ahora ✅ **100% completo** (0 sorry, 0 errores de compilación).
**Nota**: `Cardinal.Basic.lean` está ahora ✅ **100% completo** (0 sorry, CSB theorem completamente demostrado).

### 7.5 Archivos Completos Pendientes de Proyectar

(47/47 módulos completamente proyectados, 0 pendientes)

---

*Última actualización: 2026-04-09 — Proyección completa de BoolAlg.Representation.lean (§3.44, §4.40, §6.41: 3 def + 24 teoremas + 27 exports, teorema de representación de Stone forma concreta, biyección A↔Atoms(A) vía singletons, biyección 𝒫(A)↔𝒫(Atoms A) vía atomsBelowMap, preservación ∪/∩/complemento/∅/universo) y Cardinal.FinitePowerSet.lean (§3.45, §4.41, §6.42: 1 def + 12 teoremas + 13 exports, |𝒫(F)|=2^n, extensión de biyecciones por un elemento, unión disjunta aditiva, descomposición en mitades disjuntas, removeElemMap). Tabla §1.1 y §7.2 actualizadas. §7.5: 47/47 módulos proyectados. Estado: ✅ 100% completo, 0 sorry.*

*Última actualización: 2026-04-08 — Proyección completa de BoolAlg.FiniteBA.lean (§3.42, §4.38, §6.39: 0 def + 8 teoremas + 8 exports, cardinalidad de BA finita |𝒫(A)|=2^n, equipotencia átomos↔base, finiteness bidireccional, representación vía átomos, BA finita es completa atómica) y BoolAlg.BoolRingBA.lean (§3.43, §4.39, §6.40: 0 def + 13 teoremas + 13 exports, correspondencia BR↔BA, X△Y△(X∩Y)=X∪Y, A△X=X^∁[A], round-trips BA→BR→BA y BR→BA→BR, char 2, idempotencia, involución complemento). Tabla §1.1 y §7.2 actualizadas. §7.5: 45/45 módulos proyectados. Estado: ✅ 100% completo, 0 sorry.*

*Última actualización: 2026-04-07 — Proyección completa de BoolAlg.Complete.lean (§3.41, §4.37, §6.38: 4 def + 11 teoremas + 15 exports, supremo/ínfimo relativizados isSupremumIn/isInfimumIn, retículo completo isCompleteLattice, álgebra booleana completa atómica isCompleteAtomicBA, supremo en 𝒫(A) vía ⋃, ínfimo en 𝒫(A) vía ⋂, unicidad, ínfimo de familia vacía = A, powerset_is_complete_lattice, powerset_is_complete_atomic_BA). Tabla §1.1 y §7.2 actualizadas. §7.5 vacío: 43/43 módulos proyectados. Estado: ✅ 100% completo, 0 sorry.*

*Última actualización: 2026-04-01 — Proyección completa de BoolAlg.FiniteCofinite.lean (§3.40, §4.36, §6.37: 4 def + 19 teoremas + 22 exports, álgebra booleana finita/cofinita FinCofAlg(ω), clausura de finitos finite_subset/finite_union/Omega_not_finite, paridad even_or_odd/even_ne_odd/double_injective, EvenSet/OddSet infinitos, estructura BA ∅/A/complemento/unión/intersección, contraejemplo FinCofAlg_not_complete). Tabla §1.1 y §7.2 actualizadas. BoolAlg.Complete.lean añadido a §1.1 como ❌ Pendiente y §7.5. Estado: ✅ 100% completo, 0 sorry.*

*Última actualización: 2026-03-30 — Proyección completa de Peano.FiniteSequencesArith.lean (§3.38, §4.34, §6.35: 7 def + 18 teoremas + 33 exports, sumación/producto numérico seqSum/seqProd, producto cartesiano familyProduct, teoremas de cardinalidad card_product_two/card_familyProduct vía inducción ZFC). Tabla §1.1 y §7.2 actualizadas. Estado: ✅ 100% completo, 0 sorry.*

*Última actualización: 2026-03-29 — Proyección completa de SetOps.FiniteSets.lean (§3.37, §4.33, §6.34: 1 def + 21 teoremas + 22 exports, definición isFiniteSet, infraestructura de biyecciones id/inversa/composición, equipotencia refl/symm/trans, finitud de ∅/n/singleton/unión). Tabla §1.1 y §7.2 actualizadas. Estado: ✅ 100% completo, 0 sorry.*

*Última actualización: 2026-03-24 — Proyección completa de Nat.Gcd.lean (§3.30, §4.26, §6.27: 2 def + 13 teoremas + 17 exports, GCD ZFC-nativo vía algoritmo euclídeo + LCM vía bridge). Tabla §1.1 actualizada. Estado: ✅ 100% completo, 0 sorry.*

*Última actualización: 2026-03-26 — Proyección completa de Nat.MaxMin.lean (§3.33, §4.29, §6.30: 2 def + 29 teoremas + 31 exports, Patrón B bridge-only, máximo y mínimo vía isomorfismo Peano), Nat.NewtonBinom.lean (§3.34, §4.30, §6.31: 1 def + 10 teoremas + 12 exports, Patrón B 4-arg, teorema binomial Newton→ZFC), Nat.WellFounded.lean (§3.35, §4.31, §6.32: 0 def + 3 teoremas + 3 exports, buena ordenación de ω). Tabla §1.1 y §7.2 actualizadas. Estado: ✅ 100% completo, 0 sorry.*

*Última actualización: 2026-03-25 — Proyección completa de Nat.Binom.lean (§3.32, §4.28, §6.29: 1 def + 13 teoremas + 15 exports, Patrón B bridge-only, coeficientes binomiales vía isomorfismo Peano). Tabla §1.1 y §7.2 actualizadas. Estado: ✅ 100% completo, 0 sorry.*

*Última actualización: 2026-03-25 — Proyección completa de Nat.Primes.lean (§3.31, §4.27, §6.28: 1 def + 9 teoremas + 11 exports, primalidad ZFC-nativa + TFA Enfoque A). Tabla §1.1 y §7.2 actualizadas. Estado: ✅ 100% completo, 0 sorry.*

*Actualización anterior: 2026-03-24 — Proyección completa de Nat.Factorial.lean (§3.29, §4.25, §6.26: 1 def + 11 teoremas + 12 exports, Patrón B bridge-only vía isomorfismo Peano). Tabla §1.1 actualizada. Estado: ✅ 100% completo, 0 sorry.*

*Actualización anterior: 2026-03-22 — Proyección completa de Nat.Pow.lean (§3.27, §4.23, §6.23: 2 def + 13 teoremas + 18 exports, Patrón RecursiveFn con mulFn como paso) y Nat.Arith.lean (§3.28, §4.24, §6.24: 5 def públicas + 43 exports, div/mod nativos ZFC con divMod_stepFn + gcdOf/lcmOf Patrón B + Bézout substractivo). Tabla §1.1 actualizada. Estado: ✅ 100% completo, 0 sorry.*

*Actualización anterior: 2026-03-21 — Proyección completa de Nat.Div.lean: §3.26 con 2 definiciones (divOf, modOf), §4.22 con 9 teoremas (2 clausura, 2 puente, 5 propiedades algebraicas), §6.22 con 11 exports. Patrón B (bridge-only): toPeano_proof_irrel para proof-irrelevance de IsNat. Estado: ✅ 100% completo, 0 sorry. Módulo compilado al primer intento (tras fix de dirección en congr 1).*

*Actualización anterior: 2026-03-21 — Proyección completa de Nat.Sub.lean: §3.25 con 3 definiciones (predecessorFn, subFn, sub), §4.21 con 13 teoremas (3 sobre predecessorFn, 3 sobre sub, 2 ecuaciones de recursión, 1 puente fromPeano_sub, 7 propiedades algebraicas), §6.21 con 22 exports. Total: 3 definiciones + 13 teoremas completamente proyectados. Estado: ✅ 100% completo, 0 sorry. Módulo compilado sin errores.*

*Actualización anterior: 2026-03-16 19:30 — Proyección completa de Infinity.lean: añadidos 7 teoremas de orden en ω (natLt_trans, natLt_asymm, natLt_trichotomy, natLe_refl, natLe_trans, Omega_has_min, nat_mem_wf ya estaba), 2 notaciones (≺ y ≼) en §5.7, actualizados exports en §6.7 con 21 elementos organizados por categorías. Total: 1 axioma + 2 definiciones + 17 teoremas completamente proyectados. Estado confirmado: ✅ 100% completo, 0 sorry, cumple todos los requisitos de AIDER-AI-GUIDE.md (puntos 0-14). Documentación interna excepcional con explicaciones claras sobre el Axioma de Infinito y construcción de ω.*

*Actualización anterior: 2026-04-02 17:53 — Propagación de renombramientos de Fase 3 (convención Mathlib) a REFERENCE.md: 185 identificadores renombrados en todo el documento (definiciones, teoremas, notaciones, exports). Ejemplos: `BinUnion` → `union`, `BinInter` → `inter`, `subseteq` → `subset`, `subset` → `ssubset`, `SpecSet` → `sep`, `isNat` → `IsNat`, `_commutative` → `_comm`, `_associative` → `_assoc`, `_is_specified` → `mem_*_iff` (parcial). Actualizada §0.5 a estado completado. Los 43/43 módulos siguen completamente proyectados.*

*Actualización anterior: 2026-04-07 12:00 — Proyección completa de Pairing.lean: añadidas 5 definiciones faltantes (member_inter, interSet con notación ⋂, fst, snd) en §3.5, creada nueva subsección §3.5.1 con 25 predicados de relaciones y funciones (isRelation, isSymmetric, isTransitive, isFunction, etc.), añadidos 20 teoremas auxiliares en §4.2 (nonempty_iff_exists_mem, inter_of_ordered_pair, diff_pair_singleton, etc.), actualizados exports en §6.2 con 62 elementos organizados por categorías. Total: 8 definiciones + 25 predicados + 20 teoremas auxiliares + 7 teoremas principales completamente proyectados. Estado verificado: ✅ Completo.*

*Actualización anterior: 2026-03-16 17:00 — Proyección completa de Functions.lean: añadida definición restrict (§3.10) con notación f ↾ C, 4 teoremas sobre restrict en §4.6 (mem_restrict_iff, restrict_subset, restrict_is_function, restrict_apply), actualizadas ubicaciones de definiciones y teoremas, actualizada notación en §5.4, simplificados exports en §6.4. Total: 16 definiciones y teoremas de restricción completamente proyectados.*

*Actualización anterior: 2026-03-16 16:30 — Proyección completa de Relations.lean: añadidas 19 definiciones faltantes en §3.9 (isRelationFrom, Related, isIrreflexiveOn, isAsymmetricOn, isConnectedOn, isStronglyConnectedOn, isTrichotomousOn, isPreorderOn, isLinearOrderOn, isStrictOrderOn, isStrictPartialOrderOn, isStrictLinearOrderOn, isWellFoundedOn, isWellOrderOn, QuotientSet, domain, range, imag, InverseRel) y 13 teoremas faltantes en §4.5 (StrictOrder_is_Irreflexive, StrictPartialOrder_is_Irreflexive, Irreflexive_Transitive_implies_Asymmetric, Asymmetric_iff_Irreflexive_and_AntiSymmetric, PartialOrder_Connected_is_LinearOrder, LinearOrder_comparable, StrictOrder_Connected_is_Trichotomous, StrictLinearOrder_iff_StrictOrder_Connected, mem_IdRel, EqClass_mem_self, mem_EqClass_of_Related, Related_of_mem_EqClass, mem_EqClass_iff). Total: 28 definiciones y 24 teoremas en Relations.lean.*

*Actualización anterior: 2026-03-16 16:00 — Proyección completa de BoolAlg.PowerSetAlgebra.lean: añadidos 15 teoremas faltantes en §4.17 (complement_mem_powerset, empty_in_powerset, universe_in_PowerSet, powerset_absorb_inter_union, powerset_union_idempotent, powerset_inter_idempotent, powerset_union_comm, powerset_inter_comm, powerset_union_assoc, powerset_inter_assoc, powerset_inter_empty, powerset_empty_inter, powerset_complement_empty, powerset_complement_universe). Total: 22 teoremas en §4.17.*

*Actualización anterior: 2026-03-16 15:30 — Proyección completa de PowerSet.lean: axioma PowerSet (§2.6), 2 definiciones (§3.7), 12 teoremas principales (§4.3), notación 𝒫 (§5.6), 14 exports (§6.3). Renumeración de secciones 3.7→3.24, 4.3→4.20, 5.6→5.13, 6.3→6.20.*

*Actualización anterior: 2026-03-08 12:00 — Proyección de Nat.Add.lean (3 def + 16 teoremas), Nat.Mul.lean (2 def + 13 teoremas), y ampliación de PeanoImport.lean (9 nuevos teoremas: toPeano_zero, toPeano_succ, recursion_transport x4, succ_mem_succ_iff, fromPeano_lt_iff, fromPeano_le_iff). Secciones 3.22, 3.23, 4.18, 4.19 añadidas. Sección 6 actualizada con exports 6.15–6.17.*

*Actualización anterior: 2026-03-05 10:00 — Proyección completa de Recursion.lean: 5 lemas auxiliares globales, def RecursionComputations, RecursionTheorem 100% demostrado sin sorry.*

*Actualización anterior: 2026-03-04 12:00 — Proyección de PeanoImport.lean (2 def + 7 teoremas), nat_mem_wf en Infinity.lean, predecessor en Nat.Basic.lean.*

*Actualización anterior: 2026-02-12 18:45 — Completada proyección íntegra de Nat.Basic.lean (13 def + 36 teoremas + exports).*

*Este documento contiene únicamente construcciones y teoremas que están completamente implementados y demostrados en el código Lean 4. La proyección se actualiza conforme se agregan archivos al contexto de trabajo.*
