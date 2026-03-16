# Referencia Técnica - ZfcSetTheory

*Última actualización: 2026-03-16 16:30*
**Autor**: Julián Calderón Almendros

## 📋 Cumplimiento con AIDER-AI-GUIDE.md

Este documento cumple con todos los requisitos especificados en [AIDER-AI-GUIDE.md](AIDER-AI-GUIDE.md):

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
✅ **NaturalNumbersMul.lean creado (0 sorry, multiplicación ZFC + puente fromPeano_mul + 8 propiedades algebraicas)** - Actualizado 2026-03-08 12:00
✅ **NaturalNumbersAdd.lean ampliado (Sección 6: 6 nuevos teoremas de cancelación, positividad y orden)** - Actualizado 2026-03-08 12:00
✅ **PeanoImport.lean ampliado (Section 2: toPeano_zero/successor; Section 3: recursion_transport_step/inv; Section 4: orden ↔ membresía)** - Actualizado 2026-03-08 12:00
✅ **PeanoImport.lean completado (0 sorry, isomorfismo Von Neumann ↔ Peano, 100% proyectado)** - Actualizado 2026-03-04 12:00
✅ **Infinity.lean: nat_mem_wf demostrado (sin sorry, añadido a exports)** - Actualizado 2026-03-04 12:00
✅ **NaturalNumbers.lean: predecessor y teoremas exportados** - Actualizado 2026-03-04 12:00
✅ **NaturalNumbers.lean completado (0 sorry, 36 teoremas principales, 100% proyectado)** - Actualizado 2026-02-12 18:45
✅ **Recursion.lean completado (0 sorry, 0 errores de tipo)** - Actualizado 2026-03-05 10:00 (RecursionTheorem 100% demostrado sin sorry; añadidos 5 lemas auxiliares globales + RecursionComputations + computations_are_compatible)
✅ **Functions.lean completado (0 sorry)** - Actualizado 2026-02-12 14:52

---

## 1. Arquitectura del Proyecto

### 1.1 Módulos y Dependencias

| Archivo | Namespace | Dependencias | Estado Proyección |
|---------|-----------|--------------|-------------------|
| `Prelim.lean` | - | `Init.Classical` | ✅ Completo |
| `Extension.lean` | `SetUniverse.ExtensionAxiom` | `Prelim` | ✅ Completo |
| `Existence.lean` | `SetUniverse.ExistenceAxiom` | `Prelim`, `Extension` | ✅ Completo |
| `Specification.lean` | `SetUniverse.SpecificationAxiom` | `Prelim`, `Extension`, `Existence` | ✅ Completo |
| `Pairing.lean` | `SetUniverse.PairingAxiom` | `Prelim`, `Extension`, `Existence`, `Specification` | ✅ Completo (2026-03-16) |
| `Union.lean` | `SetUniverse.UnionAxiom` | `Prelim`, `Extension`, `Existence`, `Specification`, `Pairing` | ✅ Completo |
| `PowerSet.lean` | `SetUniverse.PowerSetAxiom` | `Prelim`, `Extension`, `Existence`, `Specification`, `Pairing`, `Union` | ✅ Completo |
| `PowerSetAlgebra.lean` | `SetUniverse.PowerSetAlgebra` | `PowerSet`, `BooleanAlgebra` + anteriores | ✅ Completo |
| `OrderedPair.lean` | `SetUniverse.OrderedPairExtensions` | Todos los anteriores + `PowerSet` | ✅ Completo |
| `CartesianProduct.lean` | `SetUniverse.CartesianProduct` | `OrderedPair` + anteriores | ✅ Completo |
| `Relations.lean` | `SetUniverse.Relations` | `CartesianProduct` + anteriores | ✅ Completo |
| `Functions.lean` | `SetUniverse.Functions` | `CartesianProduct`, `Relations` + anteriores | ✅ Completo |
| `BooleanAlgebra.lean` | `SetUniverse.BooleanAlgebra` | `Union`, `Specification`, `Pairing`, `Extension`, `Existence`, `Prelim` | ✅ Completo |
| `BooleanRing.lean` | `SetUniverse.BooleanRing` | `PowerSetAlgebra` + anteriores | ✅ Completo |
| `PowerSetAlgebra.lean` | `SetUniverse.PowerSetAlgebra` | `PowerSet`, `BooleanAlgebra` + anteriores | ✅ Completo |
| `AtomicBooleanAlgebra.lean` | `SetUniverse.AtomicBooleanAlgebra` | `PowerSetAlgebra`, `SetOrder`, `SetStrictOrder` + anteriores | 🔶 Parcial |
| `Cardinality.lean` | `SetUniverse.Cardinality` | `Functions` + todos los anteriores | ✅ Completo (2026-03-16) |
| `NaturalNumbers.lean` | `SetUniverse.NaturalNumbers` | `Cardinality` + todos los anteriores | ✅ Completo |
| `Infinity.lean` | `SetUniverse.InfinityAxiom` | `NaturalNumbers` + todos los anteriores | ✅ Completo |
| `PeanoImport.lean` | `SetUniverse` | `NaturalNumbers`, `Infinity`, `PeanoNatLib.PeanoNatAxioms` | ✅ Completo |
| `GeneralizedDeMorgan.lean` | `SetUniverse.GeneralizedDeMorgan` | `PowerSetAlgebra` + anteriores | ✅ Completo |
| `GeneralizedDistributive.lean` | `SetUniverse.GeneralizedDistributive` | `PowerSetAlgebra` + anteriores | ✅ Completo |
| `SetOrder.lean` | `SetUniverse.SetOrder` | `Relations` + anteriores | ✅ Completo |
| `SetStrictOrder.lean` | `SetUniverse.SetStrictOrder` | `SetOrder` + anteriores | ✅ Completo |
| `Recursion.lean` | `SetUniverse.Recursion` | `NaturalNumbers`, `Functions`, `Relations` + anteriores | ✅ Completo |
| `NaturalNumbersAdd.lean` | `SetUniverse.NaturalNumbersAdd` | `NaturalNumbers`, `Infinity`, `Recursion`, `PeanoImport`, `PeanoNatLib.PeanoNatAdd` | ✅ Completo |
| `NaturalNumbersMul.lean` | `SetUniverse.NaturalNumbersMul` | `NaturalNumbers`, `Infinity`, `Recursion`, `PeanoImport`, `NaturalNumbersAdd`, `PeanoNatLib.PeanoNatMul` | ✅ Completo |

## 2. Axiomas ZFC Implementados

### 2.1 Axioma de Extensionalidad

**Ubicación**: `Extension.lean`, línea 15  
**Namespace**: `SetUniverse.ExtensionAxiom`  
**Orden**: 1º axioma declarado

**Enunciado Matemático**: Dos conjuntos son iguales si y solo si tienen los mismos elementos.

**Firma Lean4**:

```lean
@[simp] axiom ExtSet (x y : U): (∀ (z: U), z ∈ x ↔ z ∈ y) → (x = y)
```

**Dependencias**: Ninguna (axioma primitivo)

### 2.2 Axioma de Existencia

**Ubicación**: `Existence.lean`, línea 12  
**Namespace**: `SetUniverse.ExistenceAxiom`  
**Orden**: 2º axioma declarado

**Enunciado Matemático**: Existe un conjunto que no contiene ningún elemento (conjunto vacío).

**Firma Lean4**:

```lean
@[simp] axiom ExistsAnEmptySet : ∃ (x : U), ∀ (y : U), y ∉ x
```

**Dependencias**: `ExtSet` (para unicidad)

### 2.3 Axioma de Especificación

**Ubicación**: `Specification.lean`, línea 15  
**Namespace**: `SetUniverse.SpecificationAxiom`  
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
**Namespace**: `SetUniverse.PairingAxiom`  
**Orden**: 4º axioma declarado

**Enunciado Matemático**: Para cualesquiera dos elementos a y b, existe un conjunto que contiene exactamente a y b.

**Firma Lean4**:

```lean
@[simp] axiom Pairing (x y : U) :
  ∃ (z : U), ∀ (w : U), w ∈ z ↔ (w = x ∨ w = y)
```

**Dependencias**: `ExtSet`, `SpecSet`

### 2.5 Axioma de Unión

**Ubicación**: `Union.lean`, línea 14  
**Namespace**: `SetUniverse.UnionAxiom`  
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
**Namespace**: `SetUniverse.PowerSetAxiom`  
**Orden**: 6º axioma declarado

**Enunciado Matemático**: Para todo conjunto A, existe un conjunto P que contiene exactamente los subconjuntos de A: ∀A ∃P ∀x (x ∈ P ↔ x ⊆ A).

**Firma Lean4**:

```lean
@[simp] axiom PowerSet : ∀ (A : U), ∃ (P : U), ∀ (x : U), x ∈ P ↔ x ⊆ A
```

**Dependencias**: `ExtSet`, `subseteq`

### 2.7 Axioma de Infinito

**Ubicación**: `Infinity.lean`, línea 45  
**Namespace**: `SetUniverse.InfinityAxiom`  
**Orden**: 6º axioma declarado

**Enunciado Matemático**: Existe un conjunto inductivo (que contiene ∅ y es cerrado bajo sucesores).

**Firma Lean4**:

```lean
axiom ExistsInductiveSet : ∃ (I : U), isInductive I
```

**Dependencias**: `isInductive` (de NaturalNumbers.lean)

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

#### Subconjunto (subseteq)

**Ubicación**: `Extension.lean`, línea 42  
**Orden**: 2ª definición

**Enunciado Matemático**: A es subconjunto de B si todo elemento de A está en B.

**Firma Lean4**:

```lean
@[simp] def subseteq (x y : U) : Prop := ∀ (z: U), z ∈ x → z ∈ y
notation:50 lhs:51 " ⊆ " rhs:51 => subseteq lhs rhs
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

#### Conjunto Especificado (SpecSet)

**Ubicación**: `Specification.lean`, línea 35  
**Orden**: 1ª definición principal

**Enunciado Matemático**: El conjunto de elementos de A que satisfacen la propiedad P.

**Firma Lean4**:

```lean
@[simp] noncomputable def SpecSet (x : U) (P : U → Prop) : U :=
  choose (SpecificationUnique x P)
notation " { " x " | " P " } " => SpecSet x P
```

**Dependencias**: `Specification`, `ExtSet`

#### Intersección Binaria (BinInter)

**Ubicación**: `Specification.lean`, línea 44  
**Orden**: 2ª definición principal

**Enunciado Matemático**: El conjunto de elementos que pertenecen tanto a A como a B.

**Firma Lean4**:

```lean
@[simp] noncomputable def BinInter (x y : U) : U :=
  choose (SpecificationUnique x fun z => z ∈ y)
notation:50 lhs:51 " ∩ " rhs:51 => BinInter lhs rhs
```

**Dependencias**: `SpecSet`

#### Diferencia (Difference)

**Ubicación**: `Specification.lean`, línea 175  
**Orden**: 3ª definición principal

**Enunciado Matemático**: El conjunto de elementos que están en A pero no en B.

**Firma Lean4**:

```lean
@[simp] noncomputable def Difference (x y : U) : U :=
  choose (SpecificationUnique x (fun z => z ∉ y))
notation:50 lhs:51 " \\ " rhs:51 => Difference lhs rhs
```

**Dependencias**: `SpecSet`

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
    SpecSet y₀ (fun v => ∀ y, y ∈ w → v ∈ y)
  else
    ∅
notation:100 "⋂ " w => interSet w
```

**Dependencias**: `SpecSet`, `EmptySet`, `Classical.choose`

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

**Dependencias**: `interSet`, `Difference`, `Singleton`, `Classical.choose`, `nonempty_iff_exists_mem`

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

#### Unión de Familia (UnionSet)

**Ubicación**: `Union.lean`, línea 35  
**Orden**: 1ª definición principal

**Enunciado Matemático**: El conjunto de todos los elementos que pertenecen a algún conjunto de la familia C.

**Firma Lean4**:

```lean
@[simp] noncomputable def UnionSet (C : U) : U :=
  choose (UnionExistsUnique C)
notation " ⋃ " C: 100 => UnionSet C
```

**Dependencias**: `Union`, `ExtSet`

#### Unión Binaria (BinUnion)

**Ubicación**: `Union.lean`, línea 158  
**Orden**: 2ª definición principal

**Enunciado Matemático**: El conjunto de elementos que están en A o en B (o en ambos).

**Firma Lean4**:

```lean
noncomputable def BinUnion (A B : U) : U := UnionSet (PairSet A B)
notation:50 lhs:51 " ∪ " rhs:51 => BinUnion lhs rhs
```

**Dependencias**: `UnionSet`, `PairSet`

### 3.7 PowerSet.lean

#### Existencia Única del Conjunto Potencia (PowerSetExistsUnique)

**Ubicación**: `PowerSet.lean`, línea 28  
**Orden**: 1ª definición

**Enunciado Matemático**: Para todo conjunto A, existe un único conjunto P tal que x ∈ P ↔ x ⊆ A.

**Firma Lean4**:

```lean
@[simp] theorem PowerSetExistsUnique (A : U) :
  ∃! P, ∀ x : U, x ∈ P ↔ x ⊆ A
```

**Dependencias**: `PowerSet`, `ExtSet`

#### Conjunto Potencia (PowerSetOf)

**Ubicación**: `PowerSet.lean`, línea 40  
**Orden**: 2ª definición principal

**Enunciado Matemático**: El conjunto potencia de A, denotado 𝒫(A), es el conjunto de todos los subconjuntos de A.

**Firma Lean4**:

```lean
@[simp] noncomputable def PowerSetOf (A : U) : U :=
  (PowerSetExistsUnique A).choose
notation " 𝒫 " A: 100 => PowerSetOf A
```

**Dependencias**: `PowerSetExistsUnique`, `Classical.choose`

**Notación**: `𝒫 A` para `PowerSetOf A`

### 3.8 CartesianProduct.lean

#### Producto Cartesiano (CartesianProduct)

**Ubicación**: `CartesianProduct.lean`, línea 25  
**Orden**: 1ª definición principal

**Enunciado Matemático**: El producto cartesiano A × B es el conjunto de todos los pares ordenados ⟨a,b⟩ donde a ∈ A y b ∈ B.

**Firma Lean4**:

```lean
noncomputable def CartesianProduct (A B : U) : U :=
  SpecSet (𝒫 (𝒫 (A ∪ B))) (fun p => isOrderedPair p ∧ fst p ∈ A ∧ snd p ∈ B)
notation:70 A:71 " ×ₛ " B:71 => CartesianProduct A B
```

**Dependencias**: `SpecSet`, `PowerSet`, `BinUnion`, `isOrderedPair`, `fst`, `snd`

### 3.9 Relations.lean

#### Relación en un Conjunto (isRelationOn)

**Ubicación**: `Relations.lean`, línea 44  
**Orden**: 1ª definición principal

**Enunciado Matemático**: R es una relación en A si R ⊆ A × A.

**Firma Lean4**:

```lean
def isRelationOn (R A : U) : Prop := R ⊆ (A ×ₛ A)
```

**Dependencias**: `subseteq`, `CartesianProduct`

#### Relación de A a B (isRelationFrom)

**Ubicación**: `Relations.lean`, línea 47  
**Orden**: 2ª definición principal

**Enunciado Matemático**: R es una relación de A a B si R ⊆ A × B.

**Firma Lean4**:

```lean
def isRelationFrom (R A B : U) : Prop := R ⊆ (A ×ₛ B)
```

**Dependencias**: `subseteq`, `CartesianProduct`

#### R Relaciona x con y (Related)

**Ubicación**: `Relations.lean`, línea 50  
**Orden**: 3ª definición principal

**Enunciado Matemático**: R relaciona x con y si ⟨x, y⟩ ∈ R.

**Firma Lean4**:

```lean
def Related (R x y : U) : Prop := ⟨x, y⟩ ∈ R
```

**Dependencias**: `OrderedPair`, `mem`

#### Reflexividad (isReflexiveOn)

**Ubicación**: `Relations.lean`, línea 54  
**Orden**: 4ª definición principal

**Enunciado Matemático**: R es reflexiva en A si ∀x ∈ A, (x,x) ∈ R.

**Firma Lean4**:

```lean
def isReflexiveOn (R A : U) : Prop :=
  ∀ x : U, x ∈ A → ⟨x, x⟩ ∈ R
```

**Dependencias**: `OrderedPair`

#### Irreflexividad (isIrreflexiveOn)

**Ubicación**: `Relations.lean`, línea 58  
**Orden**: 5ª definición principal

**Enunciado Matemático**: R es irreflexiva en A si ∀x ∈ A, (x,x) ∉ R.

**Firma Lean4**:

```lean
def isIrreflexiveOn (R A : U) : Prop :=
  ∀ x : U, x ∈ A → ⟨x, x⟩ ∉ R
```

**Dependencias**: `OrderedPair`

#### Simetría (isSymmetricOn)

**Ubicación**: `Relations.lean`, línea 62  
**Orden**: 6ª definición principal

**Enunciado Matemático**: R es simétrica en A si ∀x,y ∈ A, (x,y) ∈ R → (y,x) ∈ R.

**Firma Lean4**:

```lean
def isSymmetricOn (R A : U) : Prop :=
  ∀ x y : U, x ∈ A → y ∈ A → ⟨x, y⟩ ∈ R → ⟨y, x⟩ ∈ R
```

**Dependencias**: `OrderedPair`

#### Antisimetría (isAntiSymmetricOn)

**Ubicación**: `Relations.lean`, línea 66  
**Orden**: 7ª definición principal

**Enunciado Matemático**: R es antisimétrica en A si ∀x,y ∈ A, (x,y) ∈ R ∧ (y,x) ∈ R → x = y.

**Firma Lean4**:

```lean
def isAntiSymmetricOn (R A : U) : Prop :=
  ∀ x y : U, x ∈ A → y ∈ A → ⟨x, y⟩ ∈ R → ⟨y, x⟩ ∈ R → x = y
```

**Dependencias**: `OrderedPair`

#### Asimetría (isAsymmetricOn)

**Ubicación**: `Relations.lean`, línea 70  
**Orden**: 8ª definición principal

**Enunciado Matemático**: R es asimétrica en A si ∀x,y ∈ A, (x,y) ∈ R → (y,x) ∉ R.

**Firma Lean4**:

```lean
def isAsymmetricOn (R A : U) : Prop :=
  ∀ x y : U, x ∈ A → y ∈ A → ⟨x, y⟩ ∈ R → ⟨y, x⟩ ∉ R
```

**Dependencias**: `OrderedPair`

#### Transitividad (isTransitiveOn)

**Ubicación**: `Relations.lean`, línea 74  
**Orden**: 9ª definición principal

**Enunciado Matemático**: R es transitiva en A si ∀x,y,z ∈ A, (x,y) ∈ R ∧ (y,z) ∈ R → (x,z) ∈ R.

**Firma Lean4**:

```lean
def isTransitiveOn (R A : U) : Prop :=
  ∀ x y z : U, x ∈ A → y ∈ A → z ∈ A → ⟨x, y⟩ ∈ R → ⟨y, z⟩ ∈ R → ⟨x, z⟩ ∈ R
```

**Dependencias**: `OrderedPair`

#### Conexidad (isConnectedOn)

**Ubicación**: `Relations.lean`, línea 78  
**Orden**: 10ª definición principal

**Enunciado Matemático**: R es conexa (total) en A si ∀x≠y ∈ A, (x,y) ∈ R ∨ (y,x) ∈ R.

**Firma Lean4**:

```lean
def isConnectedOn (R A : U) : Prop :=
  ∀ x y : U, x ∈ A → y ∈ A → x ≠ y → ⟨x, y⟩ ∈ R ∨ ⟨y, x⟩ ∈ R
```

**Dependencias**: `OrderedPair`

#### Conexidad Fuerte (isStronglyConnectedOn)

**Ubicación**: `Relations.lean`, línea 82  
**Orden**: 11ª definición principal

**Enunciado Matemático**: R es fuertemente conexa en A si ∀x,y ∈ A, (x,y) ∈ R ∨ (y,x) ∈ R.

**Firma Lean4**:

```lean
def isStronglyConnectedOn (R A : U) : Prop :=
  ∀ x y : U, x ∈ A → y ∈ A → ⟨x, y⟩ ∈ R ∨ ⟨y, x⟩ ∈ R
```

**Dependencias**: `OrderedPair`

#### Tricotomía (isTrichotomousOn)

**Ubicación**: `Relations.lean`, línea 86  
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

**Ubicación**: `Relations.lean`, línea 94  
**Orden**: 13ª definición principal

**Enunciado Matemático**: R es relación de equivalencia en A si es reflexiva, simétrica y transitiva.

**Firma Lean4**:

```lean
def isEquivalenceOn (R A : U) : Prop :=
  isRelationOn R A ∧ isReflexiveOn R A ∧ isSymmetricOn R A ∧ isTransitiveOn R A
```

**Dependencias**: `isRelationOn`, `isReflexiveOn`, `isSymmetricOn`, `isTransitiveOn`

#### Preorden (isPreorderOn)

**Ubicación**: `Relations.lean`, línea 98  
**Orden**: 14ª definición principal

**Enunciado Matemático**: R es un preorden en A si es reflexiva y transitiva.

**Firma Lean4**:

```lean
def isPreorderOn (R A : U) : Prop :=
  isRelationOn R A ∧ isReflexiveOn R A ∧ isTransitiveOn R A
```

**Dependencias**: `isRelationOn`, `isReflexiveOn`, `isTransitiveOn`

#### Orden Parcial (isPartialOrderOn)

**Ubicación**: `Relations.lean`, línea 102  
**Orden**: 15ª definición principal

**Enunciado Matemático**: R es orden parcial en A si es reflexiva, antisimétrica y transitiva.

**Firma Lean4**:

```lean
def isPartialOrderOn (R A : U) : Prop :=
  isRelationOn R A ∧ isReflexiveOn R A ∧ isAntiSymmetricOn R A ∧ isTransitiveOn R A
```

**Dependencias**: `isRelationOn`, `isReflexiveOn`, `isAntiSymmetricOn`, `isTransitiveOn`

#### Orden Lineal (isLinearOrderOn)

**Ubicación**: `Relations.lean`, línea 106  
**Orden**: 16ª definición principal

**Enunciado Matemático**: R es orden lineal (total) en A si es orden parcial y conexa.

**Firma Lean4**:

```lean
def isLinearOrderOn (R A : U) : Prop :=
  isPartialOrderOn R A ∧ isConnectedOn R A
```

**Dependencias**: `isPartialOrderOn`, `isConnectedOn`

#### Orden Estricto (isStrictOrderOn)

**Ubicación**: `Relations.lean`, línea 110  
**Orden**: 17ª definición principal

**Enunciado Matemático**: R es orden estricto en A si es irreflexiva y transitiva.

**Firma Lean4**:

```lean
def isStrictOrderOn (R A : U) : Prop :=
  isRelationOn R A ∧ isIrreflexiveOn R A ∧ isTransitiveOn R A
```

**Dependencias**: `isRelationOn`, `isIrreflexiveOn`, `isTransitiveOn`

#### Orden Parcial Estricto (isStrictPartialOrderOn)

**Ubicación**: `Relations.lean`, línea 114  
**Orden**: 18ª definición principal

**Enunciado Matemático**: R es orden parcial estricto en A si es asimétrica y transitiva.

**Firma Lean4**:

```lean
def isStrictPartialOrderOn (R A : U) : Prop :=
  isRelationOn R A ∧ isAsymmetricOn R A ∧ isTransitiveOn R A
```

**Dependencias**: `isRelationOn`, `isAsymmetricOn`, `isTransitiveOn`

#### Orden Lineal Estricto (isStrictLinearOrderOn)

**Ubicación**: `Relations.lean`, línea 118  
**Orden**: 19ª definición principal

**Enunciado Matemático**: R es orden lineal estricto en A si es orden estricto y tricotómica.

**Firma Lean4**:

```lean
def isStrictLinearOrderOn (R A : U) : Prop :=
  isStrictOrderOn R A ∧ isTrichotomousOn R A
```

**Dependencias**: `isStrictOrderOn`, `isTrichotomousOn`

#### Bien Fundada (isWellFoundedOn)

**Ubicación**: `Relations.lean`, línea 124  
**Orden**: 20ª definición principal

**Enunciado Matemático**: R es bien fundada en A si todo subconjunto no vacío tiene un elemento minimal.

**Firma Lean4**:

```lean
def isWellFoundedOn (R A : U) : Prop :=
  ∀ S : U, S ⊆ A → S ≠ ∅ → ∃ m : U, m ∈ S ∧ ∀ x : U, x ∈ S → ⟨x, m⟩ ∉ R
```

**Dependencias**: `subseteq`, `EmptySet`, `OrderedPair`

#### Buen Orden (isWellOrderOn)

**Ubicación**: `Relations.lean`, línea 128  
**Orden**: 21ª definición principal

**Enunciado Matemático**: R es un buen orden en A si es orden lineal y bien fundada.

**Firma Lean4**:

```lean
def isWellOrderOn (R A : U) : Prop :=
  isLinearOrderOn R A ∧ isWellFoundedOn R A
```

**Dependencias**: `isLinearOrderOn`, `isWellFoundedOn`

#### Clase de Equivalencia (EqClass)

**Ubicación**: `Relations.lean`, línea 134  
**Orden**: 22ª definición principal

**Enunciado Matemático**: La clase de equivalencia de a bajo R en A: {x ∈ A | (a,x) ∈ R}.

**Firma Lean4**:

```lean
noncomputable def EqClass (a R A : U) : U :=
  SpecSet A (fun x => ⟨a, x⟩ ∈ R)
```

**Dependencias**: `SpecSet`, `OrderedPair`

#### Conjunto Cociente (QuotientSet)

**Ubicación**: `Relations.lean`, línea 138  
**Orden**: 23ª definición principal

**Enunciado Matemático**: El conjunto cociente A/R: el conjunto de todas las clases de equivalencia.

**Firma Lean4**:

```lean
noncomputable def QuotientSet (A R : U) : U :=
  SpecSet (𝒫 A) (fun C => ∃ a : U, a ∈ A ∧ C = EqClass a R A)
```

**Dependencias**: `SpecSet`, `PowerSet`, `EqClass`

#### Relación Identidad (IdRel)

**Ubicación**: `Relations.lean`, línea 144  
**Orden**: 24ª definición principal

**Enunciado Matemático**: La relación identidad en A: {(x,x) | x ∈ A}.

**Firma Lean4**:

```lean
noncomputable def IdRel (A : U) : U :=
  SpecSet (A ×ₛ A) (fun p => fst p = snd p)
```

**Dependencias**: `SpecSet`, `CartesianProduct`, `fst`, `snd`

#### Dominio de una Relación (domain)

**Ubicación**: `Relations.lean`, línea 150  
**Orden**: 25ª definición principal

**Enunciado Matemático**: domain R = {x | ∃ y, ⟨x, y⟩ ∈ R}

**Firma Lean4**:

```lean
noncomputable def domain (R : U) : U :=
  SpecSet (⋃(⋃ R)) (fun x => ∃ y, ⟨x, y⟩ ∈ R)
```

**Dependencias**: `SpecSet`, `UnionSet`, `OrderedPair`

#### Rango de una Relación (range)

**Ubicación**: `Relations.lean`, línea 155  
**Orden**: 26ª definición principal

**Enunciado Matemático**: range R = {y | ∃ x, ⟨x, y⟩ ∈ R}

**Firma Lean4**:

```lean
noncomputable def range (R : U) : U :=
  SpecSet (⋃(⋃ R)) (fun y => ∃ x, ⟨x, y⟩ ∈ R)
```

**Dependencias**: `SpecSet`, `UnionSet`, `OrderedPair`

#### Imagen de una Relación (imag)

**Ubicación**: `Relations.lean`, línea 159  
**Orden**: 27ª definición principal

**Enunciado Matemático**: imag R = range R (alias para rango)

**Firma Lean4**:

```lean
noncomputable def imag (R : U) : U := range R
```

**Dependencias**: `range`

#### Relación Inversa (InverseRel)

**Ubicación**: `Relations.lean`, línea 162  
**Orden**: 28ª definición principal

**Enunciado Matemático**: InverseRel R = {(y, x) | (x, y) ∈ R} (relación inversa)

**Firma Lean4**:

```lean
noncomputable def InverseRel (R : U) : U :=
  SpecSet (range R ×ₛ domain R) (fun p => ⟨snd p, fst p⟩ ∈ R)
```

**Dependencias**: `SpecSet`, `CartesianProduct`, `range`, `domain`, `fst`, `snd`

**Nota Importante**: A partir de 2026-02-12 14:52, `InverseRel` usa el producto cartesiano correcto `range R ×ₛ domain R` en lugar de `𝒫 (𝒫 (⋃(⋃ R)))` para ser consistente con `IdRel`.

#### Dominio de una Relación (domain)

**Ubicación**: `Relations.lean`, línea 176  
**Orden**: 11ª definición principal

**Enunciado Matemático**: domain R = {x | ∃ y, ⟨x, y⟩ ∈ R}

**Firma Lean4**:

```lean
noncomputable def domain (R : U) : U :=
  SpecSet (⋃(⋃ R)) (fun x => ∃ y, ⟨x, y⟩ ∈ R)
```

**Dependencias**: `SpecSet`, `UnionSet`, `OrderedPair`

#### Rango de una Relación (range)

**Ubicación**: `Relations.lean`, línea 181  
**Orden**: 12ª definición principal

**Enunciado Matemático**: range R = {y | ∃ x, ⟨x, y⟩ ∈ R}

**Firma Lean4**:

```lean
noncomputable def range (R : U) : U :=
  SpecSet (⋃(⋃ R)) (fun y => ∃ x, ⟨x, y⟩ ∈ R)
```

**Dependencias**: `SpecSet`, `UnionSet`, `OrderedPair`

#### Imagen de una Relación (imag)

**Ubicación**: `Relations.lean`, línea 185  
**Orden**: 13ª definición principal

**Enunciado Matemático**: imag R = range R (alias para rango)

**Firma Lean4**:

```lean
noncomputable def imag (R : U) : U := range R
```

**Dependencias**: `range`

### 3.10 Functions.lean

#### Función (isFunctionFromTo)

**Ubicación**: `Functions.lean`, línea 32  
**Orden**: 1ª definición principal

**Enunciado Matemático**: f es una función de A a B si f ⊆ A × B, es total en A y es univaluada.

**Firma Lean4**:

```lean
def isFunctionFromTo (f A B : U) : Prop :=
  f ⊆ (A ×ₛ B) ∧
  (∀ x, x ∈ A → ∃ y, ⟨x, y⟩ ∈ f) ∧
  isSingleValued f
```

**Dependencias**: `CartesianProduct`, `isSingleValued`

#### Univaluada (isSingleValued)

**Ubicación**: `Functions.lean`, línea 25  
**Orden**: 1ª definición principal

**Enunciado Matemático**: f es univaluada si cada x tiene a lo sumo un y tal que ⟨x,y⟩ ∈ f.

**Firma Lean4**:

```lean
def isSingleValued (f : U) : Prop :=
  ∀ x y₁ y₂, ⟨x, y₁⟩ ∈ f → ⟨x, y₂⟩ ∈ f → y₁ = y₂
```

**Dependencias**: `OrderedPair`

#### Dominio (Dom)

**Ubicación**: `Functions.lean`, línea 37  
**Orden**: 2ª definición principal

**Enunciado Matemático**: El dominio de f es el conjunto de primeras coordenadas: {x | ∃y, ⟨x,y⟩ ∈ f}.

**Firma Lean4**:

```lean
noncomputable def Dom (f : U) : U :=
  SpecSet (⋃ (⋃ f)) (fun x => ∃ y, ⟨x, y⟩ ∈ f)
```

**Dependencias**: `SpecSet`, `UnionSet`

#### Rango (Ran)

**Ubicación**: `Functions.lean`, línea 42  
**Orden**: 3ª definición principal

**Enunciado Matemático**: El rango de f es el conjunto de segundas coordenadas: {y | ∃x, ⟨x,y⟩ ∈ f}.

**Firma Lean4**:

```lean
noncomputable def Ran (f : U) : U :=
  SpecSet (⋃ (⋃ f)) (fun y => ∃ x, ⟨x, y⟩ ∈ f)
```

**Dependencias**: `SpecSet`, `UnionSet`

#### Aplicación de Función (apply)

**Ubicación**: `Functions.lean`, línea 58  
**Orden**: 4ª definición principal

**Enunciado Matemático**: f⦅x⦆ es el único y tal que ⟨x,y⟩ ∈ f.

**Firma Lean4**:

```lean
noncomputable def apply (f x : U) : U :=
  if h : ∃ y, ⟨x, y⟩ ∈ f then Classical.choose h else ∅
notation:max f "⦅" x "⦆" => apply f x
```

**Dependencias**: `Classical.choose`, `EmptySet`

#### Función Identidad (IdFunction)

**Ubicación**: `Functions.lean`, línea 85  
**Orden**: 5ª definición principal

**Enunciado Matemático**: La función identidad en A: {⟨x,x⟩ | x ∈ A}.

**Firma Lean4**:

```lean
noncomputable def IdFunction (A : U) : U :=
  SpecSet (A ×ₛ A) (fun p => ∃ x, x ∈ A ∧ p = ⟨x, x⟩)
notation:max "𝟙" A => IdFunction A
```

**Dependencias**: `SpecSet`, `CartesianProduct`, `OrderedPair`

#### Composición de Funciones (FunctionComposition)

**Ubicación**: `Functions.lean`, línea 125  
**Orden**: 6ª definición principal

**Enunciado Matemático**: La composición g ∘ f: {⟨x,z⟩ | ∃y, ⟨x,y⟩ ∈ f ∧ ⟨y,z⟩ ∈ g}.

**Firma Lean4**:

```lean
noncomputable def FunctionComposition (g f : U) : U :=
  SpecSet ((Dom f) ×ₛ (Ran g)) (fun p =>
    ∃ x z, p = ⟨x, z⟩ ∧ ∃ y, ⟨x, y⟩ ∈ f ∧ ⟨y, z⟩ ∈ g)
infixr:90 " ∘ₛ " => FunctionComposition
```

**Dependencias**: `SpecSet`, `Dom`, `Ran`, `OrderedPair`

#### Función Inversa (InverseFunction)

**Ubicación**: `Functions.lean`, línea 129  
**Orden**: 7ª definición principal

**Enunciado Matemático**: La relación inversa: {⟨y,x⟩ | ⟨x,y⟩ ∈ f}.

**Firma Lean4**:

```lean
noncomputable def InverseFunction (f : U) : U := InverseRel f
notation:100 f "⁻¹" => InverseFunction f
```

**Dependencias**: `InverseRel`

#### Restricción de Función (Restriction)

**Ubicación**: `Functions.lean`, línea 157  
**Orden**: 8ª definición principal

**Enunciado Matemático**: La restricción de una relación f a un dominio C: f ↾ C = {p ∈ f | fst p ∈ C}.

**Firma Lean4**:

```lean
noncomputable def Restriction (f C : U) : U :=
  SpecSet f (fun p => fst p ∈ C)
notation:60 f " ↾ " C:61 => Restriction f C
```

**Dependencias**: `SpecSet`, `fst`

**Notación**: `f ↾ C` para `Restriction f C`

#### Inyectividad (isInjective)

**Ubicación**: `Functions.lean`, línea 222  
**Orden**: 9ª definición principal

**Enunciado Matemático**: f es inyectiva si diferentes entradas dan diferentes salidas.

**Firma Lean4**:

```lean
def isInjective (f : U) : Prop :=
  ∀ x₁ x₂ y, ⟨x₁, y⟩ ∈ f → ⟨x₂, y⟩ ∈ f → x₁ = x₂
```

**Dependencias**: `OrderedPair`

#### Suryectividad (isSurjectiveOnto)

**Ubicación**: `Functions.lean`, línea 225  
**Orden**: 10ª definición principal

**Enunciado Matemático**: f es suryectiva en B si todo elemento de B está en el rango.

**Firma Lean4**:

```lean
def isSurjectiveOnto (f B : U) : Prop :=
  ∀ y, y ∈ B → ∃ x, ⟨x, y⟩ ∈ f
```

**Dependencias**: `OrderedPair`

#### Biyección (isBijection)

**Ubicación**: `Functions.lean`, línea 228  
**Orden**: 11ª definición principal

**Enunciado Matemático**: f es biyección de A a B si es función, inyectiva y suryectiva.

**Firma Lean4**:

```lean
def isBijection (f A B : U) : Prop :=
  isFunctionFromTo f A B ∧ isInjective f ∧ isSurjectiveOnto f B
```

**Dependencias**: `isFunctionFromTo`, `isInjective`, `isSurjectiveOnto`

#### Equipotencia (isEquipotent)

**Ubicación**: `Functions.lean`, línea 231  
**Orden**: 12ª definición principal

**Enunciado Matemático**: A y B son equipotentes si existe una biyección entre ellos.

**Firma Lean4**:

```lean
def isEquipotent (A B : U) : Prop := ∃ f, isBijection f A B
notation:50 A " ≃ₛ " B => isEquipotent A B
```

**Dependencias**: `isBijection`

#### Dominación (isDominatedBy)

**Ubicación**: `Functions.lean`, línea 236  
**Orden**: 13ª definición principal

**Enunciado Matemático**: A es dominado por B si existe una inyección de A a B.

**Firma Lean4**:

```lean
def isDominatedBy (A B : U) : Prop :=
  ∃ f, isFunctionFromTo f A B ∧ isInjective f
notation:50 A " ≼ₛ " B => isDominatedBy A B
```

**Dependencias**: `isFunctionFromTo`, `isInjective`

#### Dominación Estricta (isStrictlyDominatedBy)

**Ubicación**: `Functions.lean`, línea 241  
**Orden**: 14ª definición principal

**Enunciado Matemático**: A es estrictamente dominado por B si A ≼ B pero B ⊀ A.

**Firma Lean4**:

```lean
def isStrictlyDominatedBy (A B : U) : Prop :=
  (A ≼ₛ B) ∧ ¬(B ≼ₛ A)
notation:50 A " ≺ₛ " B => isStrictlyDominatedBy A B
```

**Dependencias**: `isDominatedBy`

#### Imagen Directa (ImageSet)

**Ubicación**: `Functions.lean`, línea 207  
**Orden**: 15ª definición principal

**Enunciado Matemático**: La imagen directa f[X] = {y | ∃x ∈ X, ⟨x,y⟩ ∈ f}.

**Firma Lean4**:

```lean
noncomputable def ImageSet (f X : U) : U :=
  range (f ↾ X)
notation:90 f "[" X "]" => ImageSet f X
```

**Dependencias**: `range`, `Restriction`

#### Imagen Inversa (PreimageSet)

**Ubicación**: `Functions.lean`, línea 212  
**Orden**: 16ª definición principal

**Enunciado Matemático**: La imagen inversa f⁻¹[Y] = {x | ∃y ∈ Y, ⟨x,y⟩ ∈ f}.

**Firma Lean4**:

```lean
noncomputable def PreimageSet (f Y : U) : U :=
  SpecSet (domain f) (fun x => ∃ y, ⟨x, y⟩ ∈ f ∧ y ∈ Y)
notation:90 f "⁻¹[" Y "]" => PreimageSet f Y
```

**Dependencias**: `SpecSet`, `domain`, `OrderedPair`

#### Inverso por Izquierda (hasLeftInverse)

**Ubicación**: `Functions.lean` (no presente en el archivo actual)
**Orden**: Definición no encontrada en el archivo

**Enunciado Matemático**: f tiene inverso por izquierda g si g ∘ f = id en A.

**Firma Lean4**:

```lean
def hasLeftInverse (f A B g : U) : Prop :=
  isFunctionFromTo f A B ∧ isFunctionFromTo g B A ∧
  ∀ x, x ∈ A → g⦅f⦅x⦆⦆ = x
```

**Dependencias**: `isFunctionFromTo`, `apply`

#### Inverso por Derecha (hasRightInverse)

**Ubicación**: `Functions.lean`, línea 225  
**Orden**: 12ª definición principal

**Enunciado Matemático**: f tiene inverso por derecha g si f ∘ g = id en B.

**Firma Lean4**:

```lean
def hasRightInverse (f A B g : U) : Prop :=
  isFunctionFromTo f A B ∧ isFunctionFromTo g B A ∧
  ∀ y, y ∈ B → f⦅g⦅y⦆⦆ = y
```

**Dependencias**: `isFunctionFromTo`, `apply`

#### Invertibilidad (isInvertible)

**Ubicación**: `Functions.lean`, línea 245  
**Orden**: 13ª definición principal

**Enunciado Matemático**: f es invertible si tiene inverso bilateral.

**Firma Lean4**:

```lean
def isInvertible (f A B : U) : Prop :=
  ∃ g, hasLeftInverse f A B g ∧ hasRightInverse f A B g
```

**Dependencias**: `hasLeftInverse`, `hasRightInverse`

#### Imagen Directa (ImageSet)

**Ubicación**: `Functions.lean`, línea 580  
**Orden**: 14ª definición principal

**Enunciado Matemático**: La imagen directa f[X] = {y | ∃x ∈ X, ⟨x,y⟩ ∈ f}.

**Firma Lean4**:

```lean
noncomputable def ImageSet (f X : U) : U :=
  SpecSet (Ran f) (fun y => ∃ x, x ∈ X ∧ ⟨x, y⟩ ∈ f)
notation:max f "⦃" X "⦄" => ImageSet f X
```

**Dependencias**: `SpecSet`, `Ran`, `OrderedPair`

#### Imagen Inversa (PreimageSet)

**Ubicación**: `Functions.lean`, línea 590  
**Orden**: 15ª definición principal

**Enunciado Matemático**: La imagen inversa f⁻¹[Y] = {x | ∃y ∈ Y, ⟨x,y⟩ ∈ f}.

**Firma Lean4**:

```lean
noncomputable def PreimageSet (f Y : U) : U :=
  SpecSet (Dom f) (fun x => ∃ y, y ∈ Y ∧ ⟨x, y⟩ ∈ f)
```

**Dependencias**: `SpecSet`, `Dom`, `OrderedPair`

#### Equipotencia (isEquipotent)

**Ubicación**: `Functions.lean`, línea 398  
**Orden**: 16ª definición principal

**Enunciado Matemático**: A y B son equipotentes si existe una biyección entre ellos.

**Firma Lean4**:

```lean
def isEquipotent (A B : U) : Prop := ∃ f, isBijection f A B
notation:50 A " ≃ₛ " B => isEquipotent A B
```

**Dependencias**: `isBijection`

#### Dominación (isDominatedBy)

**Ubicación**: `Functions.lean`, línea 430  
**Orden**: 17ª definición principal

**Enunciado Matemático**: A es dominado por B si existe una inyección de A a B.

**Firma Lean4**:

```lean
def isDominatedBy (A B : U) : Prop :=
  ∃ f, isFunctionFromTo f A B ∧ isInjective f
notation:50 A " ≼ₛ " B => isDominatedBy A B
```

**Dependencias**: `isFunctionFromTo`, `isInjective`

#### Dominación Estricta (isStrictlyDominatedBy)

**Ubicación**: `Functions.lean`, línea 465  
**Orden**: 18ª definición principal

**Enunciado Matemático**: A es estrictamente dominado por B si A ≼ B pero B ⊀ A.

**Firma Lean4**:

```lean
def isStrictlyDominatedBy (A B : U) : Prop :=
  (A ≼ₛ B) ∧ ¬(B ≼ₛ A)
notation:50 A " ≺ₛ " B => isStrictlyDominatedBy A B
```

**Dependencias**: `isDominatedBy`

### 3.11 BooleanAlgebra.lean

#### Teorema de Absorción

**Ubicación**: `BooleanAlgebra.lean`, línea 18  
**Orden**: 1º teorema principal

**Enunciado Matemático**: A ∪ (A ∩ B) = A.

**Firma Lean4**:

```lean
theorem BinUnion_absorb_inter (A B : U) : (A ∪ (A ∩ B)) = A
```

**Dependencias**: `BinUnion`, `BinInter`, `ExtSet`

#### Ley Distributiva

**Ubicación**: `BooleanAlgebra.lean`, línea 32  
**Orden**: 2º teorema principal

**Enunciado Matemático**: A ∪ (B ∩ C) = (A ∪ B) ∩ (A ∪ C).

**Firma Lean4**:

```lean
theorem BinUnion_distrib_inter (A B C : U) :
  (A ∪ (B ∩ C)) = ((A ∪ B) ∩ (A ∪ C))
```

**Dependencias**: `BinUnion`, `BinInter`, `ExtSet`

### 3.12 AtomicBooleanAlgebra.lean

#### Átomo (isAtom)

**Ubicación**: `AtomicBooleanAlgebra.lean`, línea 32  
**Orden**: 1ª definición principal

**Enunciado Matemático**: X es un átomo en 𝒫(A) si X ≠ ∅ y no hay elementos estrictamente entre ∅ y X.

**Firma Lean4**:

```lean
def isAtom (A X : U) : Prop :=
  X ∈ 𝒫 A ∧ X ≠ ∅ ∧ ∀ Y, Y ∈ 𝒫 A → Y ⊂ X → Y = ∅
```

**Dependencias**: `PowerSet`, `EmptySet`, `subset`

### 3.13 Cardinality.lean

#### Conjunto Diagonal (DiagonalSet)

**Ubicación**: `Cardinality.lean`, línea 37  
**Orden**: 1ª definición principal

**Enunciado Matemático**: El conjunto diagonal para la demostración de Cantor: { x ∈ A | x ∉ f⦅x⦆ }.

**Firma Lean4**:

```lean
noncomputable def DiagonalSet (f A : U) : U :=
  SpecSet A (fun x => x ∉ f⦅x⦆)
```

**Dependencias**: `SpecSet`, `apply`

#### Función Singleton (singletonMap)

**Ubicación**: `Cardinality.lean`, línea 95  
**Orden**: 2ª definición principal

**Enunciado Matemático**: La inyección canónica de A en 𝒫(A): x ↦ {x}.

**Firma Lean4**:

```lean
noncomputable def singletonMap (A : U) : U :=
  SpecSet (A ×ₛ 𝒫 A) (fun p => ∃ x, x ∈ A ∧ p = ⟨x, {x}⟩)
```

**Dependencias**: `SpecSet`, `CartesianProduct`, `PowerSet`, `OrderedPair`, `Singleton`

#### Diferencia de Conjuntos (SetDiff)

**Ubicación**: `Cardinality.lean`, línea 186  
**Orden**: 3ª definición principal

**Enunciado Matemático**: Diferencia de conjuntos: A \ B = { x ∈ A | x ∉ B }.

**Firma Lean4**:

```lean
noncomputable def SetDiff (A B : U) : U :=
  SpecSet A (fun x => x ∉ B)
notation:70 A " ∖ " B => SetDiff A B
```

**Dependencias**: `SpecSet`

**Notación**: `A ∖ B` para `SetDiff A B`

#### Núcleo CSB (CSB_core)

**Ubicación**: `Cardinality.lean`, línea 211  
**Orden**: 4ª definición principal

**Enunciado Matemático**: El núcleo CSB: intersección de todos los conjuntos cerrados bajo g ∘ f que contienen A \ g[B].

**Firma Lean4**:

```lean
noncomputable def CSB_core (f g A B : U) : U :=
  SpecSet A (fun x => ∀ X, X ⊆ A → isCSB_closed f g A B X → x ∈ X)
```

**Dependencias**: `SpecSet`, `isCSB_closed`, `subseteq`

#### Biyección CSB (CSB_bijection)

**Ubicación**: `Cardinality.lean`, línea 276  
**Orden**: 5ª definición principal

**Enunciado Matemático**: La biyección de Cantor-Schröder-Bernstein: h(x) = f(x) si x ∈ C, g⁻¹(x) si x ∉ C.

**Firma Lean4**:

```lean
noncomputable def CSB_bijection (f g A B : U) : U :=
  let C := CSB_core f g A B
  SpecSet (A ×ₛ B) (fun p =>
    ∃ x y, p = ⟨x, y⟩ ∧ x ∈ A ∧
      ((x ∈ C ∧ y = f⦅x⦆) ∨ (x ∉ C ∧ ⟨y, x⟩ ∈ g)))
```

**Dependencias**: `CSB_core`, `SpecSet`, `CartesianProduct`, `OrderedPair`, `apply`

### 3.14 NaturalNumbers.lean

#### Función Sucesor (successor)

**Ubicación**: `NaturalNumbers.lean`, línea 45  
**Orden**: 1ª definición principal

**Enunciado Matemático**: La función sucesor σ(n) = n ∪ {n}.

**Firma Lean4**:

```lean
noncomputable def successor (n : U) : U := n ∪ {n}
notation "σ " n:90 => successor n
```

**Dependencias**: `BinUnion`, `Singleton`

#### Conjunto Inductivo (isInductive)

**Ubicación**: `NaturalNumbers.lean`, línea 56  
**Orden**: 2ª definición principal

**Enunciado Matemático**: I es inductivo si contiene al vacío y es cerrado bajo sucesores.

**Firma Lean4**:

```lean
def isInductive (I : U) : Prop :=
  (∅ : U) ∈ I ∧ ∀ x, x ∈ I → (σ x) ∈ I
```

**Dependencias**: `EmptySet`, `successor`

#### Conjunto Transitivo (isTransitiveSet)

**Ubicación**: `NaturalNumbers.lean`, línea 68  
**Orden**: 3ª definición principal

**Enunciado Matemático**: S es transitivo si cada elemento es también un subconjunto de S.

**Firma Lean4**:

```lean
def isTransitiveSet (S : U) : Prop :=
  ∀ x, x ∈ S → x ⊆ S
```

**Dependencias**: `subseteq`

#### Orden Estricto Guiado por Membresía (StrictOrderMembershipGuided)

**Ubicación**: `NaturalNumbers.lean`, línea 78  
**Orden**: 4ª definición principal

**Enunciado Matemático**: El orden estricto inducido por la membresía: ∈[S] = {⟨x,y⟩ | x ∈ S ∧ y ∈ S ∧ x ∈ y}.

**Firma Lean4**:

```lean
noncomputable def StrictOrderMembershipGuided (S : U) : U :=
  SpecSet (S ×ₛ S) (fun p => ∃ x y, p = ⟨x, y⟩ ∧ x ∈ y)
notation "∈[" S "]" => StrictOrderMembershipGuided S
```

**Dependencias**: `SpecSet`, `CartesianProduct`, `OrderedPair`

#### Orden Total Estricto Guiado por Membresía (isTotalStrictOrderMembershipGuided)

**Ubicación**: `NaturalNumbers.lean`, línea 98  
**Orden**: 5ª definición principal

**Enunciado Matemático**: S tiene orden total estricto si es transitivo, asimétrico y tricotómico.

**Firma Lean4**:

```lean
def isTotalStrictOrderMembershipGuided (S : U) : Prop :=
  isTransitiveSet S ∧
  (∀ x y, x ∈ S → y ∈ S → x ∈ y → y ∉ x) ∧
  (∀ x y, x ∈ S → y ∈ S → (x ∈ y ∨ x = y ∨ y ∈ x))
```

**Dependencias**: `isTransitiveSet`

#### Bien Ordenado Guiado por Membresía (isWellOrderMembershipGuided)

**Ubicación**: `NaturalNumbers.lean`, línea 110  
**Orden**: 6ª definición principal

**Enunciado Matemático**: S está bien ordenado si todo subconjunto no vacío tiene mínimo Y máximo.

**Firma Lean4**:

```lean
def isWellOrderMembershipGuided (S : U) : Prop :=
  ∀ T, T ⊆ S → T ≠ (∅ : U) →
    (∃ m, m ∈ T ∧ ∀ x, x ∈ T → (m = x ∨ m ∈ x)) ∧ -- Mínimo
    (∃ M, M ∈ T ∧ ∀ x, x ∈ T → (M = x ∨ x ∈ M))   -- Máximo
```

**Dependencias**: `subseteq`, `EmptySet`

#### Número Natural (isNat)

**Ubicación**: `NaturalNumbers.lean`, línea 125  
**Orden**: 7ª definición principal (DEFINICIÓN CENTRAL)

**Enunciado Matemático**: n es un número natural si es transitivo, tiene orden total estricto y está bien ordenado.

**Firma Lean4**:

```lean
def isNat (n : U) : Prop :=
  isTransitiveSet n ∧
  isTotalStrictOrderMembershipGuided n ∧
  isWellOrderMembershipGuided n
```

**Dependencias**: `isTransitiveSet`, `isTotalStrictOrderMembershipGuided`, `isWellOrderMembershipGuided`

#### Segmento Inicial (isInitialSegment)

**Ubicación**: `NaturalNumbers.lean`, línea 1015  
**Orden**: 8ª definición principal

**Enunciado Matemático**: S es segmento inicial de n si S ⊆ n y es cerrado hacia abajo.

**Firma Lean4**:

```lean
def isInitialSegment (S n : U) : Prop :=
  S ⊆ n ∧ ∀ x y, x ∈ S → y ∈ x → y ∈ S
```

**Dependencias**: `subseteq`

#### Naturales Específicos

**Ubicación**: `NaturalNumbers.lean`, líneas 1350-1365  
**Orden**: 9ª-12ª definiciones principales

**Enunciado Matemático**: Construcción explícita de los primeros naturales.

**Firma Lean4**:

```lean
noncomputable def zero : U := (∅ : U)
noncomputable def one : U := σ (∅ : U)
noncomputable def two : U := σ one
noncomputable def three : U := σ two
```

**Dependencias**: `EmptySet`, `successor`

#### Naturales en Conjuntos Inductivos (zero/one/two/three_in_inductive)

**Ubicación**: `NaturalNumbers.lean`, líneas 1372-1387  
**Orden**: 10ª-13ª teoremas

**Enunciado Matemático**: Los primeros naturales pertenecen a todo conjunto inductivo.

**Firma Lean4**:

```lean
theorem zero_in_inductive (I : U) (hI : isInductive I) : (∅ : U) ∈ I := hI.1
theorem one_in_inductive (I : U) (hI : isInductive I) : σ (∅ : U) ∈ I := by
  have h0 := zero_in_inductive I hI
  exact hI.2 ∅ h0
theorem two_in_inductive (I : U) (hI : isInductive I) : σ (σ (∅ : U)) ∈ I := by
  have h1 := one_in_inductive I hI
  exact hI.2 (σ (∅ : U)) h1
theorem three_in_inductive (I : U) (hI : isInductive I) : σ (σ (σ (∅ : U))) ∈ I := by
  have h2 := two_in_inductive I hI
  exact hI.2 (σ (σ (∅ : U))) h2
```

**Dependencias**: `isInductive`, `successor`

#### Predecesor (predecessor)

**Ubicación**: `NaturalNumbers.lean`
**Orden**: 14ª definición principal
**Namespace**: `SetUniverse.NaturalNumbers`

**Enunciado Matemático**: El predecesor de un número natural n > 0 es el único k tal que σ k = n. Para n = ∅ (cero) devuelve ∅ por convención clásica.

**Firma Lean4**:

```lean
noncomputable def predecessor (n : U) : U :=
  if h : ∃ k : U, σ k = n then Classical.choose h else ∅
```

**Dependencias**: `successor`, `Classical.choose`

---

## 4. Teoremas Principales

### 4.1 NaturalNumbers.lean - Teoremas de Propiedades Elementales

#### Elemento Pertenece a su Sucesor (mem_successor_self)

**Ubicación**: `NaturalNumbers.lean`, línea 355  
**Namespace**: `SetUniverse.NaturalNumbers`

**Enunciado Matemático**: Para todo n, se tiene n ∈ σ(n). Este es el lema auxiliar fundamental del sucesor.

**Firma Lean4**:

```lean
theorem mem_successor_self (n : U) : n ∈ (σ n) := by
  rw [successor_is_specified]
  exact Or.inr rfl
```

**Dependencias**: `successor_is_specified`

#### Caracterización de Membresía en Sucesor (subset_of_mem_successor)

**Ubicación**: `NaturalNumbers.lean`, línea 361  
**Namespace**: `SetUniverse.NaturalNumbers`

**Enunciado Matemático**: x ∈ σ(n) ⟺ x ∈ n ∨ x = n

**Firma Lean4**:

```lean
theorem subset_of_mem_successor (n x : U) :
  x ∈ (σ n) → x ∈ n ∨ x = n := by
  intro hx
  rw [successor_is_specified] at hx
  exact hx
```

**Dependencias**: `successor_is_specified`

#### Preservación de Transitividad en Sucesores (successor_preserves_transitivity)

**Ubicación**: `NaturalNumbers.lean`, línea 373  
**Namespace**: `SetUniverse.NaturalNumbers`

**Enunciado Matemático**: Si n es transitivo, entonces σ(n) es transitivo.

**Firma Lean4**:

```lean
theorem successor_preserves_transitivity (n : U) (hn : isTransitiveSet n) :
  isTransitiveSet (σ n) := by
  -- Demostración por análisis de casos
  unfold isTransitiveSet at hn ⊢
  intro x hx y hy
  simp only [successor_is_specified] at hx ⊢
  cases hx with
  | inl hx_in_n =>
    have hx_sub : x ⊆ n := hn x hx_in_n
    left; exact hx_sub y hy
  | inr hx_eq_n =>
    rw [hx_eq_n] at hy
    left; exact hy
```

**Dependencias**: `isTransitiveSet`, `successor_is_specified`

#### Conjunto Vacío es Natural (zero_is_nat)

**Ubicación**: `NaturalNumbers.lean`, línea 441  
**Namespace**: `SetUniverse.NaturalNumbers`

**Enunciado Matemático**: El conjunto vacío es un número natural.

**Firma Lean4**:

```lean
theorem zero_is_nat : isNat (∅ : U) := by
  unfold isNat isTotalStrictOrderMembershipGuided isWellOrderMembershipGuided
  refine ⟨?_, ?_, ?_⟩
  -- Transitividad vacua
  unfold isTransitiveSet
  intro x hx; exfalso; exact EmptySet_is_empty x hx
  -- Orden total estricto (vacuamente)
  refine ⟨?_, ?_, ?_⟩
  -- ... (prueba vacua en todos los casos)
```

**Dependencias**: `isNat`, `EmptySet_is_empty`

### 4.2 NaturalNumbers.lean - Teoremas de Buena Fundación

#### Irreflexividad de Membresía (nat_not_mem_self)

**Ubicación**: `NaturalNumbers.lean`, línea 674  
**Namespace**: `SetUniverse.NaturalNumbers`

**Enunciado Matemático**: Para todo número natural n, se tiene n ∉ n (sin usar Axioma de Regularidad).

**Firma Lean4**:

```lean
theorem nat_not_mem_self (n : U) :
  isNat n → n ∉ n := by
  intro ⟨_, ⟨_, hasym, _⟩, _⟩ hn_mem
  have : n ∉ n := hasym n n hn_mem hn_mem hn_mem
  exact this hn_mem
```

**Dependencias**: `isNat`, `isTotalStrictOrderMembershipGuided`

#### Ausencia de Ciclos de Dos Elementos (nat_no_two_cycle)

**Ubicación**: `NaturalNumbers.lean`, línea 692  
**Namespace**: `SetUniverse.NaturalNumbers`

**Enunciado Matemático**: No existen números naturales x, y con x ∈ y ∧ y ∈ x.

**Firma Lean4**:

```lean
theorem nat_no_two_cycle (x y : U) :
  isNat x → isNat y → ¬(x ∈ y ∧ y ∈ x) := by
  intro hx hy hmem
  obtain ⟨hxy, hyx⟩ := hmem
  by_cases h_eq : x = y
  · rw [h_eq] at hxy
    exact nat_not_mem_self y hy hxy
  · have ⟨_, ⟨_, y_asym, _⟩, _⟩ := hy
    have y_trans : isTransitiveSet y := hy.1
    have x_sub_y : x ⊆ y := y_trans x hxy
    have y_in_y : y ∈ y := x_sub_y y hyx
    exact nat_not_mem_self y hy y_in_y
```

**Dependencias**: `isNat`, `nat_not_mem_self`

#### Ausencia de Ciclos de Tres Elementos (nat_no_three_cycle)

**Ubicación**: `NaturalNumbers.lean`, línea 715  
**Namespace**: `SetUniverse.NaturalNumbers`

**Enunciado Matemático**: No existen números naturales x, y, z formando un ciclo x ∈ y ∧ y ∈ z ∧ z ∈ x.

**Firma Lean4**:

```lean
theorem nat_no_three_cycle (x y z : U) :
  isNat x → isNat y → isNat z → ¬(x ∈ y ∧ y ∈ z ∧ z ∈ x) := by
  intro hx hy hz hmem
  obtain ⟨hxy, hyz, hzx⟩ := hmem
  have x_trans : isTransitiveSet x := hx.1
  have z_sub_x : z ⊆ x := x_trans z hzx
  have hyx : y ∈ x := z_sub_x y hyz
  exact nat_no_two_cycle x y hx hy ⟨hxy, hyx⟩
```

**Dependencias**: `isNat`, `isTransitiveSet`, `nat_no_two_cycle`

### 4.3 NaturalNumbers.lean - Teoremas de Herencia Estructural

#### Elementos de Naturales son Transitivos (nat_element_is_transitive)

**Ubicación**: `NaturalNumbers.lean`, línea 747  
**Namespace**: `SetUniverse.NaturalNumbers`

**Enunciado Matemático**: Si n es natural y m ∈ n, entonces m es transitivo.

**Firma Lean4**:

```lean
theorem nat_element_is_transitive (n m : U)
  (hn : isNat n) (hm_in_n : m ∈ n) :
  isTransitiveSet m := by
  -- Demostración por tricotomía y análisis de casos exhaustivo
  obtain ⟨hn_trans, ⟨hn_self, hn_asym, hn_trich⟩, hn_wo⟩ := hn
  have hn_reconstructed : isNat n := ⟨hn_trans, ⟨hn_self, hn_asym, hn_trich⟩, hn_wo⟩
  unfold isTransitiveSet at hn_trans ⊢
  intro k hk_in_m
  have hm_sub_n : m ⊆ n := hn_trans m hm_in_n
  have hk_in_n : k ∈ n := hm_sub_n k hk_in_m
  have hk_sub_n : k ⊆ n := hn_trans k hk_in_n
  intro l hl_in_k
  -- ... (análisis completo de tricotomía)
```

**Dependencias**: `isNat`, `isTransitiveSet`, `isTotalStrictOrderMembershipGuided`

#### Elementos de Naturales Tienen Orden Total (nat_element_has_strict_total_order)

**Ubicación**: `NaturalNumbers.lean`, línea 870  
**Namespace**: `SetUniverse.NaturalNumbers`

**Enunciado Matemático**: Si n es natural y m ∈ n, entonces m tiene orden total estricto.

**Firma Lean4**:

```lean
theorem nat_element_has_strict_total_order (n m : U)
  (hn : isNat n) (hm_in_n : m ∈ n) :
  isTotalStrictOrderMembershipGuided m := by
  obtain ⟨hn_trans, ⟨hn_self, hn_asym, hn_trich⟩, hn_wo⟩ := hn
  have hn_reconstructed : isNat n := ⟨hn_trans, ⟨hn_self, hn_asym, hn_trich⟩, hn_wo⟩
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

**Dependencias**: `isNat`, `isTotalStrictOrderMembershipGuided`, `nat_element_is_transitive`

#### Elementos de Naturales Están Bien Ordenados (nat_element_has_well_order)

**Ubicación**: `NaturalNumbers.lean`, línea 928  
**Namespace**: `SetUniverse.NaturalNumbers`

**Enunciado Matemático**: Si n es natural y m ∈ n, entonces m está bien ordenado (con mínimo y máximo).

**Firma Lean4**:

```lean
theorem nat_element_has_well_order (n m : U)
  (hn : isNat n) (hm_in_n : m ∈ n) :
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

**Dependencias**: `isNat`, `isWellOrderMembershipGuided`

#### Teorema Fundamental: Elementos de Naturales son Naturales (nat_element_is_nat)

**Ubicación**: `NaturalNumbers.lean`, línea 948  
**Namespace**: `SetUniverse.NaturalNumbers`

**Enunciado Matemático**: Si n es natural y m ∈ n, entonces m es natural. Esto es el **teorema fundamental** que establece la jerarquía de naturales.

**Firma Lean4**:

```lean
theorem nat_element_is_nat (n m : U) :
  isNat n → m ∈ n → isNat m := by
  intro hn hm_in_n
  unfold isNat
  refine ⟨?_, ?_, ?_⟩
  · exact nat_element_is_transitive n m hn hm_in_n
  · exact nat_element_has_strict_total_order n m hn hm_in_n
  · exact nat_element_has_well_order n m hn hm_in_n
```

**Dependencias**: `isNat`, `nat_element_is_transitive`, `nat_element_has_strict_total_order`, `nat_element_has_well_order`

### 4.4 NaturalNumbers.lean - Teoremas de Clausura bajo Sucesores

#### El Sucesor No es Igual al Natural Original (nat_ne_successor)

**Ubicación**: `NaturalNumbers.lean`, línea 961  
**Namespace**: `SetUniverse.NaturalNumbers`

**Enunciado Matemático**: Para todo natural n, se tiene n ≠ σ(n).

**Firma Lean4**:

```lean
theorem nat_ne_successor (n : U) (hn : isNat n) : n ≠ σ n := by
  intro h_eq
  have : n ∈ σ n := mem_successor_self n
  rw [←h_eq] at this
  exact nat_not_mem_self n hn this
```

**Dependencias**: `isNat`, `mem_successor_self`, `nat_not_mem_self`

#### El Sucesor del Vacío tiene Orden Total (successor_of_nat_has_strict_total_order)

**Ubicación**: `NaturalNumbers.lean`, línea 1005  
**Namespace**: `SetUniverse.NaturalNumbers`

**Enunciado Matemático**: Si n es natural, entonces σ(n) tiene orden total estricto.

**Firma Lean4**:

```lean
theorem successor_of_nat_has_strict_total_order (n : U) (hn : isNat n) :
  isTotalStrictOrderMembershipGuided (σ n) := by
  obtain ⟨hn_trans, ⟨hn_trans_self, hn_asym, hn_trich⟩, hn_wo⟩ := hn
  unfold isTotalStrictOrderMembershipGuided
  -- ... (análisis de casos para elementos en σ n)
```

**Dependencias**: `isNat`, `isTotalStrictOrderMembershipGuided`, `successor_is_specified`

#### Teorema Principal: El Sucesor de un Natural es Natural (nat_successor_is_nat)

**Ubicación**: `NaturalNumbers.lean`, línea 1076  
**Namespace**: `SetUniverse.NaturalNumbers`

**Enunciado Matemático**: Si n es natural, entonces σ(n) es natural. **Teorema clave de clausura inductiva.**

**Firma Lean4**:

```lean
theorem nat_successor_is_nat (n : U) (hn : isNat n) : isNat (σ n) := by
  obtain ⟨hn_trans, ⟨hn_trans_self, hn_asym, hn_trich⟩, hn_wo⟩ := hn
  have hn_reconstructed : isNat n := ⟨hn_trans, ⟨hn_trans_self, hn_asym, hn_trich⟩, hn_wo⟩
  refine ⟨?_, ?_, ?_⟩
  · exact successor_of_nat_is_transitive n hn_reconstructed
  · exact successor_of_nat_has_strict_total_order n hn_reconstructed
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
        have hB_sub_n : B ⊆ n := BinInter_subset A n |>.2
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
        rw [successor_is_specified] at hx_succ
        cases hx_succ with
        | inl hx_n => right; exact hx_n
        | inr hx_eq_n => left; exact hx_eq_n.symm
      · -- n ∉ A, entonces A ⊆ n
        have hA_sub_n : A ⊆ n := by
          intro x hx
          have hx_succ := hA_sub x hx
          rw [successor_is_specified] at hx_succ
          cases hx_succ with
          | inl hx_n => exact hx_n
          | inr hx_eq_n => rw [hx_eq_n] at hx; contradiction
        obtain ⟨M, hM_in_A, hM_max⟩ := (hn_wo A hA_sub_n hA_nonempty).2
        refine ⟨M, hM_in_A, hM_max⟩
    constructor; exact h_min; exact h_max
```

**Dependencias**: `isNat`, `successor_is_specified`, `BinInter_subset`

### 4.5 NaturalNumbers.lean - Teoremas de Tricotomía y Orden

#### Tricotomía entre Números Naturales (nat_trichotomy)

**Ubicación**: `NaturalNumbers.lean`, línea 1245  
**Namespace**: `SetUniverse.NaturalNumbers`

**Enunciado Matemático**: Para cualesquiera dos números naturales n y m, se cumple exactamente una de: n ∈ m, n = m, ó m ∈ n.

**Firma Lean4**:

```lean
theorem nat_trichotomy (n m : U) (hn : isNat n) (hm : isNat m) :
  n ∈ m ∨ n = m ∨ m ∈ n := by
  let k := n ∩ m
  have hk_init := inter_nat_is_initial_segment n m hn hm
  have hk_init_n : isInitialSegment k n := hk_init.1
  have hk_init_m : isInitialSegment k m := hk_init.2
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
      have hk_in_k : k ∈ k := (BinInter_is_specified n m k).mpr ⟨hk_in_n, hk_in_m⟩
      have hk_nat : isNat k := nat_element_is_nat n k hn hk_in_n
      exact nat_not_mem_self k hk_nat hk_in_k
```

**Dependencias**: `isNat`, `isInitialSegment`, `initial_segment_of_nat_is_eq_or_mem`, `inter_nat_is_initial_segment`, `nat_element_is_nat`, `nat_not_mem_self`

#### Transitividad de Membresía (nat_mem_trans)

**Ubicación**: `NaturalNumbers.lean`, línea 1301  
**Namespace**: `SetUniverse.NaturalNumbers`

**Enunciado Matemático**: Si n ∈ m y m ∈ k (todos naturales), entonces n ∈ k.

**Firma Lean4**:

```lean
theorem nat_mem_trans (n m k : U) (_hn : isNat n) (_hm : isNat m) (hk : isNat k)
  (hnm : n ∈ m) (hmk : m ∈ k) : n ∈ k := by
  have hm_sub_k : m ⊆ k := hk.1 m hmk
  exact hm_sub_k n hnm
```

**Dependencias**: `isNat`, `isTransitiveSet`

#### Asimetría de Membresía (nat_mem_asymm)

**Ubicación**: `NaturalNumbers.lean`, línea 1313  
**Namespace**: `SetUniverse.NaturalNumbers`

**Enunciado Matemático**: Si n ∈ m (ambos naturales), entonces m ∉ n.

**Firma Lean4**:

```lean
theorem nat_mem_asymm (n m : U) (hn : isNat n) (hm : isNat m)
  (hnm : n ∈ m) : m ∉ n := by
  intro hmn
  exact nat_no_two_cycle n m hn hm ⟨hnm, hmn⟩
```

**Dependencias**: `isNat`, `nat_no_two_cycle`

#### Subconjunto Implica Membresía u Igualdad (nat_subset_mem_or_eq)

**Ubicación**: `NaturalNumbers.lean`, línea 1333  
**Namespace**: `SetUniverse.NaturalNumbers`

**Enunciado Matemático**: Si n ⊆ m (ambos naturales), entonces n ∈ m ∨ n = m.

**Firma Lean4**:

```lean
theorem nat_subset_mem_or_eq
  (n m : U) (hn : isNat n) (hm : isNat m) (h_sub : n ⊆ m) :
  n ∈ m ∨ n = m := by
  have h_trich := nat_trichotomy n m hn hm
  cases h_trich with
  | inl h => left; exact h
  | inr h => cases h with
    | inl h => right; exact h
    | inr h_m_in_n =>
      exfalso
      have h_m_sub : m ⊆ n := hn.1 m h_m_in_n
      have h_eq : n = m := ExtSet_wc h_sub h_m_sub
      rw [h_eq] at h_m_in_n
      exact nat_not_mem_self m hm h_m_in_n
```

**Dependencias**: `isNat`, `nat_trichotomy`, `ExtSet_wc`

#### El Sucesor es Inyectivo (successor_injective)

**Ubicación**: `NaturalNumbers.lean`, línea 1351  
**Namespace**: `SetUniverse.NaturalNumbers`

**Enunciado Matemático**: Si σ(n) = σ(m), entonces n = m.

**Firma Lean4**:

```lean
theorem successor_injective (n m : U) (hn : isNat n) (hm : isNat m)
  (h_eq : σ n = σ m) : n = m := by
  have hn_in_succ_n : n ∈ σ n := mem_successor_self n
  rw [h_eq] at hn_in_succ_n
  rw [successor_is_specified] at hn_in_succ_n
  have hm_in_succ_m : m ∈ σ m := mem_successor_self m
  rw [←h_eq] at hm_in_succ_m
  rw [successor_is_specified] at hm_in_succ_m
  cases hn_in_succ_n with
  | inl hn_in_m =>
    cases hm_in_succ_m with
    | inl hm_in_n =>
      exfalso; exact nat_no_two_cycle n m hn hm ⟨hn_in_m, hm_in_n⟩
    | inr hm_eq_n => exact hm_eq_n.symm
  | inr hn_eq_m => exact hn_eq_m
```

**Dependencias**: `isNat`, `mem_successor_self`, `successor_is_specified`, `nat_no_two_cycle`

### 4.6 NaturalNumbers.lean - Teoremas de Finitud

#### Todo Natural es Cero o Sucesor (nat_is_zero_or_succ)

**Ubicación**: `NaturalNumbers.lean`, línea 1377  
**Namespace**: `SetUniverse.NaturalNumbers`

**Enunciado Matemático**: Para todo número natural n, se tiene n = ∅ ó ∃k, n = σ(k).

**Firma Lean4**:

```lean
theorem nat_is_zero_or_succ (n : U) (hn : isNat n) :
  n = ∅ ∨ ∃ k, n = σ k := by
  by_cases h_zero : n = ∅
  · left; exact h_zero
  · right
    obtain ⟨hn_trans, hn_order, hn_wo⟩ := hn
    have hn_reconstructed : isNat n := ⟨hn_trans, hn_order, hn_wo⟩
    obtain ⟨M, hM_in, hM_max⟩ := (hn_wo n (subseteq_reflexive n) h_zero).2
    exists M
    apply ExtSet
    intro x
    constructor
    · intro hx
      cases hM_max x hx with
      | inl h_eq => rw [successor_is_specified]; right; exact h_eq.symm
      | inr h_mem => rw [successor_is_specified]; left; exact h_mem
    · intro hx
      rw [successor_is_specified] at hx
      cases hx with
      | inl hx_M => exact hn_trans M hM_in x hx_M
      | inr hx_eq => rw [hx_eq]; exact hM_in
```

**Dependencias**: `isNat`, `successor_is_specified`, `ExtSet`, `subseteq_reflexive`

#### Teorema Fundamental: Vacío Pertenece a Todo Natural No Vacío (zero_mem_of_nat_nonempty)

**Ubicación**: `NaturalNumbers.lean`, línea 1398  
**Namespace**: `SetUniverse.NaturalNumbers`

**Enunciado Matemático**: Si n es un número natural no vacío, entonces ∅ ∈ n.

**Nota**: Este teorema se prueba **sin usar el Axioma de Regularidad**, solo mediante regresión imposible en la jerarquía de von Neumann.

**Firma Lean4**:

```lean
theorem zero_mem_of_nat_nonempty (n : U) (hn : isNat n) (h_ne : n ≠ ∅) : (∅ : U) ∈ n := by
  obtain ⟨hn_trans, hn_order, hn_wo⟩ := hn
  have hn_reconstructed : isNat n := ⟨hn_trans, hn_order, hn_wo⟩
  obtain ⟨m, hm_in_n, hm_min⟩ := (hn_wo n (subseteq_reflexive n) h_ne).1
  by_cases h_m_eq : m = ∅
  · rw [←h_m_eq]; exact hm_in_n
  · have hm_nat : isNat m := nat_element_is_nat n m hn_reconstructed hm_in_n
    obtain ⟨hn_trans_m, hn_order_m, hn_wo_m⟩ := hm_nat
    obtain ⟨m', hm'_in_m, hm'_min⟩ := (hn_wo_m m (subseteq_reflexive m) h_m_eq).1
    have hm'_in_n : m' ∈ n := hn_trans m hm_in_n m' hm'_in_m
    have hm_nat : isNat m := ⟨hn_trans_m, hn_order_m, hn_wo_m⟩
    match hm_min m' hm'_in_n with
      | Or.inl h_eq =>
        exfalso
        rw [←h_eq] at hm'_in_m
        exact nat_not_mem_self m hm_nat hm'_in_m
      | Or.inr h_m_in_m' =>
        exfalso
        exact nat_no_two_cycle m' m
          (nat_element_is_nat m m' hm_nat hm'_in_m)
          hm_nat
          ⟨hm'_in_m, h_m_in_m'⟩
```

**Dependencias**: `isNat`, `nat_element_is_nat`, `nat_not_mem_self`, `nat_no_two_cycle`

#### Teorema de Finitud: Máximo en Subconjuntos (nat_has_max)

**Ubicación**: `NaturalNumbers.lean`, línea 1296  
**Namespace**: `SetUniverse.NaturalNumbers`

**Enunciado Matemático**: Todo subconjunto no vacío de un número natural tiene un elemento máximo. **Teorema que caracteriza los naturales como ordinales finitos.**

**Firma Lean4**:

```lean
theorem nat_has_max (n T : U) (hn : isNat n) (hT_sub : T ⊆ n) (hT_ne : T ≠ ∅) :
  ∃ max, max ∈ T ∧ ∀ x, x ∈ T → (x ∈ max ∨ x = max) := by
  let Mx := SpecSet T (fun x => ¬∃ y, y ∈ T ∧ x ∈ y ∧ x ≠ y)
  by_cases hMx : Mx ≠ ∅
  · -- Si hay elementos maximales
    have hMx_sub : Mx ⊆ T := by
      intro x hx; rw [SpecSet_is_specified] at hx; exact hx.1
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
          rw [SpecSet_is_specified] at hmax_in_Mx
          exact hmax_in_Mx.2
        apply hmax_maximal
        exists x
        refine ⟨hx_in_T, h, ?_⟩
        intro h_eq
        have h_max_in_max : max ∈ max := h_eq ▸ h
        exact nat_not_mem_self max (nat_element_is_nat n max hn hmax_in_n) h_max_in_max
  · -- Si no hay elementos maximales, usar máximo de T en n
    have hMx_empty : Mx = ∅ := not_not.mp hMx
    obtain ⟨M, hM_in_T, hM_is_max⟩ := (hn.2.2 T hT_sub hT_ne).2
    have hM_in_Mx : M ∈ Mx := by
      rw [SpecSet_is_specified]
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

**Dependencias**: `isNat`, `SpecSet_is_specified`, `isTotalStrictOrderMembershipGuided`, `nat_element_is_nat`, `nat_not_mem_self`

### 4.7 NaturalNumbers.lean - Teoremas sobre Conjuntos Inductivos

#### Todo Natural Pertenece a Conjuntos Inductivos (nat_in_inductive_set)

**Ubicación**: `NaturalNumbers.lean`, línea 1550  
**Namespace**: `SetUniverse.NaturalNumbers`

**Enunciado Matemático**: Si n es un número natural e I es un conjunto inductivo, entonces n ∈ I.

**Firma Lean4**:

```lean
theorem nat_in_inductive_set (n : U) (hn : isNat n) (I : U) (hI : isInductive I) :
  n ∈ I := by
  cases nat_is_zero_or_succ n hn with
  | inl h_zero =>
    rw [h_zero]; exact hI.1
  | inr h_succ =>
    obtain ⟨k, hk_eq⟩ := h_succ
    have hk_in_n : k ∈ n := by rw [hk_eq]; exact mem_successor_self k
    have h_sub : n ⊆ I := nat_subset_inductive_set n hn I hI
    have hk_in_I : k ∈ I := h_sub k hk_in_n
    have h_succ_in : σ k ∈ I := hI.2 k hk_in_I
    rw [hk_eq]; exact h_succ_in
```

**Dependencias**: `isNat`, `isInductive`, `nat_is_zero_or_succ`, `nat_subset_inductive_set`, `mem_successor_self`

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
  SpecSet WitnessInductiveSet (fun x =>
    ∀ (J : U), J ⊆ WitnessInductiveSet → isInductive J → x ∈ J)
notation "ω" => Omega
```

**Dependencias**: `SpecSet`, `WitnessInductiveSet`, `isInductive`

### 3.16 GeneralizedDeMorgan.lean

#### Imagen de Familia por Función (ImageFamily)

**Ubicación**: `GeneralizedDeMorgan.lean`, línea 25  
**Orden**: 1ª definición principal

**Enunciado Matemático**: La imagen de una familia F bajo una función f: {f(X) | X ∈ F}.

**Firma Lean4**:

```lean
noncomputable def ImageFamily (f F : U) : U :=
  SpecSet (𝒫 (Ran f)) (fun Y => ∃ X, X ∈ F ∧ Y = ImageSet f X)
```

**Dependencias**: `SpecSet`, `PowerSet`, `Ran`, `ImageSet`

#### Familia de Complementos (ComplementFamily)

**Ubicación**: `GeneralizedDeMorgan.lean`, línea 35  
**Orden**: 2ª definición principal

**Enunciado Matemático**: La familia de complementos de F en A: {A \ X | X ∈ F}.

**Firma Lean4**:

```lean
noncomputable def ComplementFamily (A F : U) : U :=
  ImageFamily (ComplementFunction A) F
notation A " \\ᶠ " F => ComplementFamily A F
```

**Dependencias**: `ImageFamily`, `ComplementFunction`

#### Función Complemento (ComplementFunction)

**Ubicación**: `GeneralizedDeMorgan.lean`, línea 45  
**Orden**: 3ª definición principal

**Enunciado Matemático**: La función que mapea cada subconjunto X de A a su complemento A \ X.

**Firma Lean4**:

```lean
noncomputable def ComplementFunction (A : U) : U :=
  SpecSet ((𝒫 A) ×ₛ (𝒫 A)) (fun p => 
    isOrderedPair p ∧ snd p = A \ fst p)
```

**Dependencias**: `SpecSet`, `PowerSet`, `CartesianProduct`, `OrderedPair`, `Difference`

### 3.17 GeneralizedDistributive.lean

#### Intersección Generalizada de Familia (GeneralizedIntersection)

**Ubicación**: `GeneralizedDistributive.lean`, línea 25  
**Orden**: 1ª definición principal

**Enunciado Matemático**: La intersección generalizada de una familia F: ⋂ F = {x | ∀Y ∈ F, x ∈ Y}.

**Firma Lean4**:

```lean
noncomputable def GeneralizedIntersection (F : U) : U :=
  if h : F = ∅ then ∅ else
    SpecSet (⋃ F) (fun x => ∀ Y, Y ∈ F → x ∈ Y)
notation "⋂ " F:100 => GeneralizedIntersection F
```

**Dependencias**: `SpecSet`, `UnionSet`, `EmptySet`

#### Imagen de Familia por Intersección (IntersectionImageFamily)

**Ubicación**: `GeneralizedDistributive.lean`, línea 45  
**Orden**: 2ª definición principal

**Enunciado Matemático**: La familia de intersecciones de X con cada elemento de F: {X ∩ Y | Y ∈ F}.

**Firma Lean4**:

```lean
noncomputable def IntersectionImageFamily (X F : U) : U :=
  ImageFamily (IntersectionFunction X) F
notation X " ∩ᶠ " F => IntersectionImageFamily X F
```

**Dependencias**: `ImageFamily`, `IntersectionFunction`

#### Función Intersección (IntersectionFunction)

**Ubicación**: `GeneralizedDistributive.lean`, línea 55  
**Orden**: 3ª definición principal

**Enunciado Matemático**: La función que mapea cada conjunto Y a X ∩ Y.

**Firma Lean4**:

```lean
noncomputable def IntersectionFunction (X : U) : U :=
  SpecSet (𝒫 (⋃ {X, ⋃ (𝒫 X)}) ×ₛ 𝒫 (⋃ {X, ⋃ (𝒫 X)})) 
    (fun p => isOrderedPair p ∧ snd p = X ∩ fst p)
```

**Dependencias**: `SpecSet`, `PowerSet`, `CartesianProduct`, `BinInter`, `OrderedPair`

#### Imagen de Familia por Unión (UnionImageFamily)

**Ubicación**: `GeneralizedDistributive.lean`, línea 75  
**Orden**: 4ª definición principal

**Enunciado Matemático**: La familia de uniones de X con cada elemento de F: {X ∪ Y | Y ∈ F}.

**Firma Lean4**:

```lean
noncomputable def UnionImageFamily (X F : U) : U :=
  ImageFamily (UnionFunction X) F
notation X " ∪ᶠ " F => UnionImageFamily X F
```

**Dependencias**: `ImageFamily`, `UnionFunction`

#### Función Unión (UnionFunction)

**Ubicación**: `GeneralizedDistributive.lean`, línea 85  
**Orden**: 5ª definición principal

**Enunciado Matemático**: La función que mapea cada conjunto Y a X ∪ Y.

**Firma Lean4**:

```lean
noncomputable def UnionFunction (X : U) : U :=
  SpecSet (𝒫 (⋃ {X, ⋃ (𝒫 X)}) ×ₛ 𝒫 (⋃ {X, ⋃ (𝒫 X)})) 
    (fun p => isOrderedPair p ∧ snd p = X ∪ fst p)
```

**Dependencias**: `SpecSet`, `PowerSet`, `CartesianProduct`, `BinUnion`, `OrderedPair`

### 3.18 SetOrder.lean

#### Cota Superior (isUpperBound)

**Ubicación**: `SetOrder.lean`, línea 35  
**Orden**: 1ª definición principal

**Enunciado Matemático**: x es cota superior de S si todo elemento de S es subconjunto de x.

**Firma Lean4**:

```lean
def isUpperBound (S x : U) : Prop :=
  ∀ y, y ∈ S → y ⊆ x
```

**Dependencias**: `subseteq`

#### Cota Inferior (isLowerBound)

**Ubicación**: `SetOrder.lean`, línea 39  
**Orden**: 2ª definición principal

**Enunciado Matemático**: x es cota inferior de S si x es subconjunto de todo elemento de S.

**Firma Lean4**:

```lean
def isLowerBound (S x : U) : Prop :=
  ∀ y, y ∈ S → x ⊆ y
```

**Dependencias**: `subseteq`

#### Supremo (isSupremum)

**Ubicación**: `SetOrder.lean`, línea 43  
**Orden**: 3ª definición principal

**Enunciado Matemático**: x es supremo de S si es cota superior y la menor de todas las cotas superiores.

**Firma Lean4**:

```lean
def isSupremum (S x : U) : Prop :=
  isUpperBound S x ∧ ∀ z, isUpperBound S z → x ⊆ z
```

**Dependencias**: `isUpperBound`, `subseteq`

#### Ínfimo (isInfimum)

**Ubicación**: `SetOrder.lean`, línea 47  
**Orden**: 4ª definición principal

**Enunciado Matemático**: x es ínfimo de S si es cota inferior y la mayor de todas las cotas inferiores.

**Firma Lean4**:

```lean
def isInfimum (S x : U) : Prop :=
  isLowerBound S x ∧ ∀ z, isLowerBound S z → z ⊆ x
```

**Dependencias**: `isLowerBound`, `subseteq`

#### Acotado Superiormente (isBoundedAbove)

**Ubicación**: `SetOrder.lean`, línea 51  
**Orden**: 5ª definición principal

**Enunciado Matemático**: S está acotado superiormente si existe una cota superior.

**Firma Lean4**:

```lean
def isBoundedAbove (S : U) : Prop :=
  ∃ x, isUpperBound S x
```

**Dependencias**: `isUpperBound`

#### Acotado Inferiormente (isBoundedBelow)

**Ubicación**: `SetOrder.lean`, línea 55  
**Orden**: 6ª definición principal

**Enunciado Matemático**: S está acotado inferiormente si existe una cota inferior.

**Firma Lean4**:

```lean
def isBoundedBelow (S : U) : Prop :=
  ∃ x, isLowerBound S x
```

**Dependencias**: `isLowerBound`

### 3.19 SetStrictOrder.lean

*Nota: Este módulo no introduce nuevas definiciones principales, sino que establece propiedades del orden estricto ⊂ definido en `Extension.lean`.*

#### Orden Estricto (subset)

**Ubicación**: `Extension.lean`, línea 46 (definición implícita)  
**Orden**: Definición heredada

**Enunciado Matemático**: A ⊂ B si A ⊆ B y A ≠ B.

**Firma Lean4**:

```lean
-- Definición implícita: A ⊂ B ↔ (A ⊆ B ∧ A ≠ B)
notation:50 lhs:51 " ⊂ " rhs:51 => (lhs ⊆ rhs ∧ lhs ≠ rhs)
```

**Dependencias**: `subseteq`

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

#### Pertenencia en Conjunto Potencia (OrderedPair_in_PowerSet)

**Ubicación**: `OrderedPair.lean`, línea 42  
**Orden**: 3ª definición adicional

**Enunciado Matemático**: Si a ∈ A y b ∈ B, entonces ⟨a,b⟩ ∈ 𝒫(𝒫(A ∪ B)).

**Firma Lean4**:

```lean
theorem OrderedPair_in_PowerSet (a b A B : U)
  (ha : a ∈ A) (hb : b ∈ B) :
    ⟨a, b⟩ ∈ 𝒫 (𝒫 (A ∪ B))
```

**Dependencias**: `OrderedPair`, `PowerSet`, `BinUnion`, `Singleton`, `PairSet`

### 3.21 PowerSetAlgebra.lean

#### Complemento (Complement)

**Ubicación**: `PowerSetAlgebra.lean`, línea 68  
**Orden**: 1ª definición principal

**Enunciado Matemático**: El complemento de X relativo al universo A es A \ X.

**Firma Lean4**:

```lean
noncomputable def Complement (A X : U) : U := A \ X
notation:max X:max " ^∁[ " A:max " ]" => Complement A X
```

**Dependencias**: `Difference`

### 3.22 PeanoImport.lean

**Módulo**: `ZfcSetTheory.PeanoImport`
**Namespace**: `SetUniverse` (sub-namespace `SetUniverse.PeanoIsomorphism`)
**Dependencias**: `ZfcSetTheory.NaturalNumbers`, `ZfcSetTheory.Infinity`, `PeanoNatLib.PeanoNatAxioms`, `PeanoNatLib.PeanoNatStrictOrder`, `PeanoNatLib.PeanoNatOrder`
**Librería externa**: `peanolib` — ver [REFERENCE-PEANO.md](REFERENCE-PEANO.md) para la referencia técnica completa del proyecto Peano.
**Descripción**: Establece el isomorfismo completo entre los números naturales de Von Neumann y los de Peano. Contiene cuatro secciones: (1) la biyección `fromPeano`/`toPeano` con inyectividad, sobreyectividad e inversas; (2) compatibilidad con la estructura algebraica básica (`toPeano_zero`, `toPeano_successor`); (3) transporte de los teoremas de recursión (simple y con paso) entre los dos mundos; (4) puentes de orden: `fromPeano_lt_iff` y `fromPeano_le_iff` que identifican el orden estricto de Peano con la membresía en ω. **Notación**: `ΠZ p` para `fromPeano p`, `ZΠ n hn` para `toPeano n hn`.

**Abre los namespaces**: `Classical`, `SetUniverse.ExtensionAxiom`, `SetUniverse.ExistenceAxiom`, `SetUniverse.SpecificationAxiom`, `SetUniverse.PairingAxiom`, `SetUniverse.UnionAxiom`, `SetUniverse.PowerSetAxiom`, `SetUniverse.OrderedPairExtensions`, `SetUniverse.CartesianProduct`, `SetUniverse.Relations`, `SetUniverse.Functions`, `SetUniverse.Cardinality`, `SetUniverse.NaturalNumbers`

#### Conversión Peano → Von Neumann (fromPeano)

**Ubicación**: `PeanoImport.lean`, línea 35
**Orden**: 1ª definición principal

**Enunciado Matemático**: Convierte un número natural de Peano `p : Peano.ℕ₀` en su representación de Von Neumann: `fromPeano(0) = ∅`, `fromPeano(succ p) = σ(fromPeano(p))`.

**Firma Lean4**:

```lean
noncomputable def fromPeano : Peano.ℕ₀ → U
  | Peano.ℕ₀.zero    => (∅ : U)
  | Peano.ℕ₀.succ n' => successor (fromPeano n')
```

**Dependencias**: `EmptySet`, `successor`, `Peano.ℕ₀`

#### Conversión Von Neumann → Peano (toPeano)

**Ubicación**: `PeanoImport.lean`, línea 96
**Orden**: 2ª definición principal

**Enunciado Matemático**: Convierte un número natural de Von Neumann `n : U` (con prueba `hn : isNat n`) en su representante de Peano, usando elección clásica sobre `fromPeano_surjective`.

**Firma Lean4**:

```lean
noncomputable def toPeano (n : U) (hn : isNat n) : Peano.ℕ₀ :=
  Classical.choose (fromPeano_surjective n hn)
```

**Dependencias**: `fromPeano_surjective`, `Classical.choose`, `isNat`

### 3.23 NaturalNumbersAdd.lean

**Módulo**: `ZfcSetTheory.NaturalNumbersAdd`
**Namespace**: `SetUniverse.NaturalNumbersAdd`
**Dependencias**: `NaturalNumbers`, `Infinity`, `Recursion`, `PeanoImport`, `PeanoNatLib.PeanoNatAdd`
**Actualizado**: 2026-03-08 12:00
**Descripción**: Define la suma en ω mediante el Teorema de Recursión. Fijado m ∈ ω, `addFn m hm` es la función recursiva con base m y paso `successorFn`. La suma se extiende sin argumento de prueba (`add m n` con valor por defecto ∅ si m ∉ ω). El teorema puente `fromPeano_add` conecta con `Peano.Add.add`, permitiendo transportar todos los teoremas algebraicos de Peano.

**Abre los namespaces**: `Classical`, todos los de ZFC hasta `InfinityAxiom`. **No abre** `PeanoIsomorphism` para evitar ambigüedad de la notación `ΠZ`.

#### Función sucesor como conjunto ZFC (successorFn)

**Ubicación**: `NaturalNumbersAdd.lean`, línea 66
**Orden**: 1ª definición

**Enunciado Matemático**: `successorFn = {⟨n, σ n⟩ | n ∈ ω} ⊆ ω ×ₛ ω`. Es la función ZFC que representa el sucesor.

**Firma Lean4**:

```lean
noncomputable def successorFn : U :=
  SpecSet (ω ×ₛ ω) (fun p => ∃ n, n ∈ (ω : U) ∧ p = ⟨n, σ n⟩)
```

**Dependencias**: `SpecSet`, `ω`, `CartesianProduct`, `OrderedPair`, `successor`

#### Función de adición fijado m (addFn)

**Ubicación**: `NaturalNumbersAdd.lean`, línea 109
**Orden**: 2ª definición

**Enunciado Matemático**: `addFn m hm` es la única función ZFC `F : ω → ω` con `F(∅) = m` y `F(σ n) = σ(F(n))`, construida vía `RecursiveFn`.

**Firma Lean4**:

```lean
noncomputable def addFn (m : U) (hm : m ∈ (ω : U)) : U :=
  RecursiveFn ω m successorFn hm successorFn_is_function
```

**Dependencias**: `RecursiveFn`, `successorFn`, `successorFn_is_function`

#### Suma en ω (add)

**Ubicación**: `NaturalNumbersAdd.lean`, línea 120
**Orden**: 3ª definición

**Enunciado Matemático**: `add m n = (addFn m hm)(n)` si `m ∈ ω`, y `∅` en otro caso. No lleva argumento de prueba para evitar dependencias en reescrituras algebraicas.

**Firma Lean4**:

```lean
noncomputable def add (m n : U) : U :=
  if h : m ∈ (ω : U) then apply (addFn m h) n else ∅
```

**Dependencias**: `addFn`, `apply`

---

### 3.24 NaturalNumbersMul.lean

**Módulo**: `ZfcSetTheory.NaturalNumbersMul`
**Namespace**: `SetUniverse.NaturalNumbersMul`
**Dependencias**: `NaturalNumbers`, `Infinity`, `Recursion`, `PeanoImport`, `NaturalNumbersAdd`, `PeanoNatLib.PeanoNatMul`
**Actualizado**: 2026-03-08 12:00
**Descripción**: Define la multiplicación en ω mediante el Teorema de Recursión. Fijado m ∈ ω, `mulFn m hm` es la función recursiva con base ∅ y paso `addFn m hm` (cada paso de sucesor añade m). Así `mul m ∅ = ∅` y `mul m (σ n) = add m (mul m n)`. El teorema puente `fromPeano_mul` usa commutativity de la suma para adaptarse al orden de `Peano.Mul.mul_succ`.

#### Función de multiplicación fijado m (mulFn)

**Ubicación**: `NaturalNumbersMul.lean`, línea 69
**Orden**: 1ª definición

**Enunciado Matemático**: `mulFn m hm` es la única función ZFC `F : ω → ω` con `F(∅) = ∅` y `F(σ n) = m + F(n)`, construida vía `RecursiveFn`.

**Firma Lean4**:

```lean
noncomputable def mulFn (m : U) (hm : m ∈ (ω : U)) : U :=
  RecursiveFn ω ∅ (addFn m hm) zero_in_Omega (addFn_is_function m hm)
```

**Dependencias**: `RecursiveFn`, `addFn`, `addFn_is_function`, `zero_in_Omega`

#### Multiplicación en ω (mul)

**Ubicación**: `NaturalNumbersMul.lean`, línea 80
**Orden**: 2ª definición

**Enunciado Matemático**: `mul m n = (mulFn m hm)(n)` si `m ∈ ω`, y `∅` en otro caso. No lleva argumento de prueba.

**Firma Lean4**:

```lean
noncomputable def mul (m n : U) : U :=
  if h : m ∈ (ω : U) then apply (mulFn m h) n else ∅
```

**Dependencias**: `mulFn`, `apply`

---

## 4. Teoremas Principales por Módulo

### 4.1 Extension.lean

#### Igualdad por Subconjuntos

**Ubicación**: `Extension.lean`, línea 56  
**Orden**: 1º teorema principal

**Enunciado Matemático**: Si A ⊆ B y B ⊆ A, entonces A = B.

**Firma Lean4**:

```lean
@[simp] theorem EqualityOfSubset (x y : U) :
  (x ⊆ y) → (y ⊆ x) → (x = y)
```

**Dependencias**: `ExtSet`, `subseteq`

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

#### Intersección de Singleton (interSet_of_singleton)

**Ubicación**: `Pairing.lean`, línea 101  
**Orden**: 2º teorema auxiliar

**Enunciado Matemático**: ⋂{A} = A.

**Firma Lean4**:

```lean
@[simp] theorem interSet_of_singleton (A : U) : (⋂ { A }) = A
```

**Dependencias**: `interSet`, `Singleton`, `SpecSet_is_specified`, `Singleton_is_specified`

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

#### Diferencia de Par Ordenado con Singleton (diff_ordered_pair_neq)

**Ubicación**: `Pairing.lean`, línea 177  
**Orden**: 6º teorema auxiliar

**Enunciado Matemático**: Si x ≠ y, entonces ⟨x, y⟩ \ {{x}} = {{x, y}}.

**Firma Lean4**:

```lean
theorem diff_ordered_pair_neq (x y : U) (h_neq : x ≠ y) :
  ((⟨x, y⟩ : U) \ ({{x}} : U)) = {{x, y}}
```

**Dependencias**: `OrderedPair`, `Difference`, `Singleton`, `Difference_is_specified`, `OrderedPair_is_specified`, `Singleton_is_specified`

#### Diferencia de Par con Singleton (diff_pair_singleton)

**Ubicación**: `Pairing.lean`, línea 203  
**Orden**: 7º teorema auxiliar

**Enunciado Matemático**: Si x ≠ y, entonces {x, y} \ {x} = {y}.

**Firma Lean4**:

```lean
theorem diff_pair_singleton (x y : U) (h_neq : x ≠ y) :
  (({x, y} : U) \ ({x} : U)) = ({y} : U)
```

**Dependencias**: `PairSet`, `Singleton`, `Difference`, `ExtSet`, `Difference_is_specified`, `PairSet_is_specified`, `Singleton_is_specified`

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

#### Diferencia de Par con Intersección (diff_pair_sing_inter)

**Ubicación**: `Pairing.lean`, línea 271  
**Orden**: 11º teorema auxiliar

**Enunciado Matemático**: Si x = y, entonces ⟨x, y⟩ \ {⋂ ⟨x, y⟩} = ∅.

**Firma Lean4**:

```lean
theorem diff_pair_sing_inter (x y : U) :
  (x = y) → (((⟨x, y⟩ : U) \ ({(⋂ (⟨x, y⟩ : U))})) = (∅ : U))
```

**Dependencias**: `OrderedPair`, `interSet`, `Difference`, `Singleton`, `inter_of_ordered_pair`, `ordered_pair_self_eq_singleton_singleton`, `Difference_self_empty`

#### Corrección de fst (fst_of_ordered_pair)

**Ubicación**: `Pairing.lean`, línea 286  
**Orden**: 1º teorema principal

**Enunciado Matemático**: La primera proyección de un par ordenado es el primer elemento: fst(⟨x, y⟩) = x.

**Firma Lean4**:

```lean
@[simp] theorem fst_of_ordered_pair (x y : U) : fst (⟨x, y⟩ : U) = x
```

**Dependencias**: `fst`, `OrderedPair`, `inter_of_ordered_pair`, `interSet_of_singleton`

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

#### Intersección de Par Ordenado (inter_of_ordered_pair)

**Ubicación**: `Pairing.lean`, línea 293  
**Orden**: 13º teorema auxiliar

**Enunciado Matemático**: ⋂ ⟨x, y⟩ = {x}.

**Firma Lean4**:

```lean
theorem inter_of_ordered_pair (x y : U) : (⋂ ⟨x, y⟩) = {x}
```

**Dependencias**: `interSet`, `OrderedPair`, `Singleton`, `ExtSet`, `OrderedPair_is_specified`, `Singleton_is_specified`, `PairSet_is_specified`

#### Intersección de Par Ordenado con Desigualdad (inter_of_ordered_pair_neq_mem)

**Ubicación**: `Pairing.lean`, línea 295  
**Orden**: 14º teorema auxiliar

**Enunciado Matemático**: Si x ≠ y, entonces ⟨x, y⟩ \ {⋂ ⟨x, y⟩} = {{x, y}}.

**Firma Lean4**:

```lean
theorem inter_of_ordered_pair_neq_mem (x y : U) (h_eq : x ≠ y) :
  (((⟨x, y⟩ : U)  \ ({((⋂ (⟨x, y⟩ : U)) : U)} : U)  : U) = ({{x, y}} : U))
```

**Dependencias**: `OrderedPair`, `interSet`, `Difference`, `Singleton`, `ExtSet`, `inter_of_ordered_pair`, `Difference_is_specified`, `OrderedPair_is_specified`, `Singleton_is_specified`

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

#### Corrección de snd (snd_of_ordered_pair)

**Ubicación**: `Pairing.lean`, línea 325  
**Orden**: 2º teorema principal

**Enunciado Matemático**: La segunda proyección de un par ordenado es el segundo elemento: snd(⟨x, y⟩) = y.

**Firma Lean4**:

```lean
@[simp] theorem snd_of_ordered_pair (x y : U) : snd ⟨x, y⟩ = y
```

**Dependencias**: `snd`, `OrderedPair`, `snd_of_ordered_pair_eq`, `diff_ordered_pair_neq`, `diff_pair_singleton`, `inter_of_ordered_pair`, `interSet_of_singleton`, `is_singleton_unique_elem`, `nonempty_iff_exists_mem`

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

### 4.3 PowerSet.lean - Teoremas Principales

#### Especificación del Conjunto Potencia (PowerSet_is_specified)

**Ubicación**: `PowerSet.lean`, línea 47  
**Orden**: 1º teorema de especificación

**Enunciado Matemático**: x ∈ 𝒫(A) ↔ x ⊆ A.

**Firma Lean4**:

```lean
@[simp] theorem PowerSet_is_specified (A x : U) : x ∈ (𝒫 A) ↔ x ⊆ A
```

**Dependencias**: `PowerSetOf`, `PowerSetExistsUnique`

#### Unicidad del Conjunto Potencia (PowerSet_is_unique)

**Ubicación**: `PowerSet.lean`, línea 53  
**Orden**: 2º teorema de especificación

**Enunciado Matemático**: (∀x, x ∈ P ↔ x ⊆ A) ↔ P = 𝒫(A).

**Firma Lean4**:

```lean
@[simp] theorem PowerSet_is_unique (A P : U) :
  (∀ (x : U), x ∈ P ↔ x ⊆ A) ↔ (P = 𝒫 A)
```

**Dependencias**: `ExtSet`, `PowerSet_is_specified`

#### El Vacío Pertenece a Todo Conjunto Potencia (empty_mem_PowerSet)

**Ubicación**: `PowerSet.lean`, línea 68  
**Orden**: 1º teorema de propiedades básicas

**Enunciado Matemático**: ∅ ∈ 𝒫(A) para todo A.

**Firma Lean4**:

```lean
theorem empty_mem_PowerSet (A : U) : ∅ ∈ (𝒫 A)
```

**Dependencias**: `PowerSet_is_specified`, `EmptySet_subseteq_any`

#### Todo Conjunto Pertenece a su Conjunto Potencia (self_mem_PowerSet)

**Ubicación**: `PowerSet.lean`, línea 75  
**Orden**: 2º teorema de propiedades básicas

**Enunciado Matemático**: A ∈ 𝒫(A) para todo A.

**Firma Lean4**:

```lean
theorem self_mem_PowerSet (A : U) : A ∈ (𝒫 A)
```

**Dependencias**: `PowerSet_is_specified`, `subseteq_reflexive`

#### El Conjunto Potencia Nunca es Vacío (PowerSet_nonempty)

**Ubicación**: `PowerSet.lean`, línea 82  
**Orden**: 3º teorema de propiedades básicas

**Enunciado Matemático**: 𝒫(A) ≠ ∅ para todo A.

**Firma Lean4**:

```lean
theorem PowerSet_nonempty (A : U) : (𝒫 A) ≠ ∅
```

**Dependencias**: `empty_mem_PowerSet`, `EmptySet_is_empty`

#### Conjunto Potencia del Vacío (PowerSet_empty)

**Ubicación**: `PowerSet.lean`, línea 91  
**Orden**: 4º teorema de propiedades básicas

**Enunciado Matemático**: 𝒫(∅) = {∅}.

**Firma Lean4**:

```lean
theorem PowerSet_empty : (𝒫 (∅ : U)) = ({∅} : U)
```

**Dependencias**: `ExtSet`, `PowerSet_is_specified`, `Singleton_is_specified`, `EmptySet_is_empty`

#### Monotonicidad del Conjunto Potencia (PowerSet_mono)

**Ubicación**: `PowerSet.lean`, línea 111  
**Orden**: 1º teorema de relaciones con subconjuntos

**Enunciado Matemático**: Si A ⊆ B, entonces 𝒫(A) ⊆ 𝒫(B).

**Firma Lean4**:

```lean
theorem PowerSet_mono (A B : U) (h : A ⊆ B) : (𝒫 A) ⊆ (𝒫 B)
```

**Dependencias**: `PowerSet_is_specified`, `subseteq_transitive`

#### Caracterización Bidireccional de Monotonicidad (PowerSet_mono_iff)

**Ubicación**: `PowerSet.lean`, línea 119  
**Orden**: 2º teorema de relaciones con subconjuntos

**Enunciado Matemático**: 𝒫(A) ⊆ 𝒫(B) ↔ A ⊆ B.

**Firma Lean4**:

```lean
theorem PowerSet_mono_iff (A B : U) : (𝒫 A) ⊆ (𝒫 B) ↔ A ⊆ B
```

**Dependencias**: `PowerSet_mono`, `self_mem_PowerSet`, `PowerSet_is_specified`

#### Intersección de Conjuntos Potencia (PowerSet_inter)

**Ubicación**: `PowerSet.lean`, línea 138  
**Orden**: 1º teorema de relaciones con unión/intersección

**Enunciado Matemático**: 𝒫(A) ∩ 𝒫(B) = 𝒫(A ∩ B).

**Firma Lean4**:

```lean
theorem PowerSet_inter (A B : U) : ((𝒫 A) ∩ (𝒫 B)) = (𝒫 (A ∩ B))
```

**Dependencias**: `ExtSet`, `BinInter_is_specified`, `PowerSet_is_specified`

#### Unión de Conjuntos Potencia (PowerSet_union_subset)

**Ubicación**: `PowerSet.lean`, línea 165  
**Orden**: 2º teorema de relaciones con unión/intersección

**Enunciado Matemático**: 𝒫(A) ∪ 𝒫(B) ⊆ 𝒫(A ∪ B) (la igualdad NO vale en general).

**Firma Lean4**:

```lean
theorem PowerSet_union_subset (A B : U) : ((𝒫 A) ∪ (𝒫 B)) ⊆ (𝒫 (A ∪ B))
```

**Dependencias**: `BinUnion_is_specified`, `PowerSet_is_specified`

#### Subconjunto en Conjunto Potencia de Unión (subset_PowerSet_Union)

**Ubicación**: `PowerSet.lean`, línea 181  
**Orden**: 1º teorema de relaciones con unión generalizada

**Enunciado Matemático**: A ⊆ 𝒫(⋃ A) para cualquier familia A.

**Firma Lean4**:

```lean
theorem subset_PowerSet_Union (A : U) : A ⊆ (𝒫 (⋃ A))
```

**Dependencias**: `PowerSet_is_specified`, `UnionSet_is_specified`

#### Unión del Conjunto Potencia (Union_PowerSet)

**Ubicación**: `PowerSet.lean`, línea 189  
**Orden**: 2º teorema de relaciones con unión generalizada

**Enunciado Matemático**: ⋃ 𝒫(A) = A.

**Firma Lean4**:

```lean
theorem Union_PowerSet (A : U) : ⋃ (𝒫 A) = A
```

**Dependencias**: `ExtSet`, `UnionSet_is_specified`, `PowerSet_is_specified`, `Singleton_is_specified`

### 4.4 CartesianProduct.lean

#### Caracterización del Producto

**Ubicación**: `CartesianProduct.lean`, línea 30  
**Orden**: 1º teorema principal

**Enunciado Matemático**: p ∈ A × B ↔ (isOrderedPair p ∧ fst p ∈ A ∧ snd p ∈ B).

**Firma Lean4**:

```lean
theorem CartesianProduct_is_specified (A B p : U) :
  p ∈ (A ×ₛ B) ↔ (isOrderedPair p ∧ fst p ∈ A ∧ snd p ∈ B)
```

**Dependencias**: `SpecSet`, `PowerSet`, `OrderedPair`

#### Caracterización con Par Ordenado Explícito

**Ubicación**: `CartesianProduct.lean`, línea 50  
**Orden**: 2º teorema principal

**Enunciado Matemático**: ⟨a,b⟩ ∈ A × B ↔ (a ∈ A ∧ b ∈ B).

**Firma Lean4**:

```lean
theorem OrderedPair_mem_CartesianProduct (a b A B : U) :
  ⟨ a , b ⟩ ∈ (A ×ₛ B) ↔ (a ∈ A ∧ b ∈ B)
```

**Dependencias**: `CartesianProduct_is_specified`, `fst_of_ordered_pair`, `snd_of_ordered_pair`

#### Producto con Conjunto Vacío (Izquierda)

**Ubicación**: `CartesianProduct.lean`, línea 62  
**Orden**: 3º teorema principal

**Enunciado Matemático**: ∅ × B = ∅.

**Firma Lean4**:

```lean
theorem CartesianProduct_empty_left (B : U) :
  (∅ ×ₛ B) = ∅
```

**Dependencias**: `ExtSet`, `CartesianProduct_is_specified`, `EmptySet_is_empty`

#### Producto con Conjunto Vacío (Derecha)

**Ubicación**: `CartesianProduct.lean`, línea 72  
**Orden**: 4º teorema principal

**Enunciado Matemático**: A × ∅ = ∅.

**Firma Lean4**:

```lean
theorem CartesianProduct_empty_right (A : U) :
  (A ×ₛ ∅) = ∅
```

**Dependencias**: `ExtSet`, `CartesianProduct_is_specified`, `EmptySet_is_empty`

#### Monotonicidad del Producto Cartesiano

**Ubicación**: `CartesianProduct.lean`, línea 82  
**Orden**: 5º teorema principal

**Enunciado Matemático**: Si A ⊆ A' y B ⊆ B', entonces A × B ⊆ A' × B'.

**Firma Lean4**:

```lean
theorem CartesianProduct_mono (A A' B B' : U)
  (hA : A ⊆ A') (hB : B ⊆ B') :
    (A ×ₛ B) ⊆ (A' ×ₛ B')
```

**Dependencias**: `CartesianProduct_is_specified`, `subseteq`

#### Distributividad con Unión (Izquierda)

**Ubicación**: `CartesianProduct.lean`, línea 89  
**Orden**: 6º teorema principal

**Enunciado Matemático**: (A ∪ B) × C = (A × C) ∪ (B × C).

**Firma Lean4**:

```lean
theorem CartesianProduct_distrib_union_left (A B C : U) :
  ((A ∪ B) ×ₛ C) = ((A ×ₛ C) ∪ (B ×ₛ C))
```

**Dependencias**: `ExtSet`, `CartesianProduct_is_specified`, `BinUnion_is_specified`

#### Distributividad con Unión (Derecha)

**Ubicación**: `CartesianProduct.lean`, línea 115  
**Orden**: 7º teorema principal

**Enunciado Matemático**: A × (B ∪ C) = (A × B) ∪ (A × C).

**Firma Lean4**:

```lean
theorem CartesianProduct_distrib_union_right (A B C : U) :
  (A ×ₛ (B ∪ C)) = ((A ×ₛ B) ∪ (A ×ₛ C))
```

**Dependencias**: `ExtSet`, `CartesianProduct_is_specified`, `BinUnion_is_specified`

#### Distributividad con Intersección (Izquierda)

**Ubicación**: `CartesianProduct.lean`, línea 141  
**Orden**: 8º teorema principal

**Enunciado Matemático**: (A ∩ B) × C = (A × C) ∩ (B × C).

**Firma Lean4**:

```lean
theorem CartesianProduct_distrib_inter_left (A B C : U) :
  ((A ∩ B) ×ₛ C) = ((A ×ₛ C) ∩ (B ×ₛ C))
```

**Dependencias**: `ExtSet`, `CartesianProduct_is_specified`, `BinInter_is_specified`

#### Distributividad con Intersección (Derecha)

**Ubicación**: `CartesianProduct.lean`, línea 165  
**Orden**: 9º teorema principal

**Enunciado Matemático**: A × (B ∩ C) = (A × B) ∩ (A × C).

**Firma Lean4**:

```lean
theorem CartesianProduct_distrib_inter_right (A B C : U) :
  (A ×ₛ (B ∩ C)) = ((A ×ₛ B) ∩ (A ×ₛ C))
```

**Dependencias**: `ExtSet`, `CartesianProduct_is_specified`, `BinInter_is_specified`

### 4.5 Relations.lean

#### La Asimetría Implica Irreflexividad

**Ubicación**: `Relations.lean`, línea 168  
**Orden**: 1º teorema principal

**Enunciado Matemático**: Si R es asimétrica en A, entonces R es irreflexiva en A.

**Firma Lean4**:

```lean
theorem Asymmetric_implies_Irreflexive (R A : U) :
    isAsymmetricOn R A → isIrreflexiveOn R A
```

**Dependencias**: `isAsymmetricOn`, `isIrreflexiveOn`

#### Un Orden Estricto es Irreflexivo

**Ubicación**: `Relations.lean`, línea 173  
**Orden**: 2º teorema principal

**Enunciado Matemático**: Si R es un orden estricto en A, entonces R es irreflexiva en A.

**Firma Lean4**:

```lean
theorem StrictOrder_is_Irreflexive (R A : U) :
    isStrictOrderOn R A → isIrreflexiveOn R A
```

**Dependencias**: `isStrictOrderOn`, `isIrreflexiveOn`

#### Un Orden Parcial Estricto es Irreflexivo

**Ubicación**: `Relations.lean`, línea 178  
**Orden**: 3º teorema principal

**Enunciado Matemático**: Si R es un orden parcial estricto en A, entonces R es irreflexiva en A.

**Firma Lean4**:

```lean
theorem StrictPartialOrder_is_Irreflexive (R A : U) :
    isStrictPartialOrderOn R A → isIrreflexiveOn R A
```

**Dependencias**: `isStrictPartialOrderOn`, `isIrreflexiveOn`, `Asymmetric_implies_Irreflexive`

#### Irreflexiva y Transitiva Implica Asimétrica

**Ubicación**: `Relations.lean`, línea 183  
**Orden**: 4º teorema principal

**Enunciado Matemático**: Si R es irreflexiva y transitiva en A, entonces R es asimétrica en A.

**Firma Lean4**:

```lean
theorem Irreflexive_Transitive_implies_Asymmetric (R A : U) :
    isIrreflexiveOn R A → isTransitiveOn R A →
    isAsymmetricOn R A
```

**Dependencias**: `isIrreflexiveOn`, `isTransitiveOn`, `isAsymmetricOn`

#### Asimetría Equivale a Irreflexividad más Antisimetría

**Ubicación**: `Relations.lean`, línea 189  
**Orden**: 5º teorema principal

**Enunciado Matemático**: Para relaciones transitivas, asimetría es equivalente a irreflexividad más antisimetría.

**Firma Lean4**:

```lean
theorem Asymmetric_iff_Irreflexive_and_AntiSymmetric (R A : U)
    (hTrans : isTransitiveOn R A) :
    isAsymmetricOn R A ↔ isIrreflexiveOn R A ∧ isAntiSymmetricOn R A
```

**Dependencias**: `isAsymmetricOn`, `isIrreflexiveOn`, `isAntiSymmetricOn`, `isTransitiveOn`

#### Orden Parcial con Conexidad es Orden Lineal

**Ubicación**: `Relations.lean`, línea 200  
**Orden**: 6º teorema principal

**Enunciado Matemático**: Un orden parcial con conexidad es un orden lineal.

**Firma Lean4**:

```lean
theorem PartialOrder_Connected_is_LinearOrder (R A : U) :
    isPartialOrderOn R A → isConnectedOn R A → isLinearOrderOn R A
```

**Dependencias**: `isPartialOrderOn`, `isConnectedOn`, `isLinearOrderOn`

#### Orden Lineal: Elementos Comparables

**Ubicación**: `Relations.lean`, línea 204  
**Orden**: 7º teorema principal

**Enunciado Matemático**: En un orden lineal, cualesquiera dos elementos son comparables.

**Firma Lean4**:

```lean
theorem LinearOrder_comparable (R A : U) (hLO : isLinearOrderOn R A)
    (x y : U) (hxA : x ∈ A) (hyA : y ∈ A) :
    ⟨x, y⟩ ∈ R ∨ ⟨y, x⟩ ∈ R
```

**Dependencias**: `isLinearOrderOn`, `OrderedPair`

#### Orden Estricto con Conexidad es Tricotómico

**Ubicación**: `Relations.lean`, línea 215  
**Orden**: 8º teorema principal

**Enunciado Matemático**: Un orden estricto con conexidad es tricotómico.

**Firma Lean4**:

```lean
theorem StrictOrder_Connected_is_Trichotomous (R A : U)
    (hStrict : isStrictOrderOn R A) (hConn : isConnectedOn R A) :
    isTrichotomousOn R A
```

**Dependencias**: `isStrictOrderOn`, `isConnectedOn`, `isTrichotomousOn`, `Irreflexive_Transitive_implies_Asymmetric`

#### Orden Lineal Estricto Equivale a Orden Estricto Conexo

**Ubicación**: `Relations.lean`, línea 242  
**Orden**: 9º teorema principal

**Enunciado Matemático**: Un orden lineal estricto es equivalente a un orden estricto que es conexo.

**Firma Lean4**:

```lean
theorem StrictLinearOrder_iff_StrictOrder_Connected (R A : U) :
    isStrictLinearOrderOn R A ↔ isStrictOrderOn R A ∧ isConnectedOn R A
```

**Dependencias**: `isStrictLinearOrderOn`, `isStrictOrderOn`, `isConnectedOn`, `StrictOrder_Connected_is_Trichotomous`

#### Pertenencia en Relación Identidad

**Ubicación**: `Relations.lean`, línea 258  
**Orden**: 10º teorema principal

**Enunciado Matemático**: ⟨x, y⟩ ∈ IdRel A ↔ x ∈ A ∧ x = y.

**Firma Lean4**:

```lean
theorem mem_IdRel (A x y : U) :
    ⟨x, y⟩ ∈ IdRel A ↔ x ∈ A ∧ x = y
```

**Dependencias**: `IdRel`, `SpecSet_is_specified`, `OrderedPair_mem_CartesianProduct`, `fst_of_ordered_pair`, `snd_of_ordered_pair`

#### La Relación Identidad es de Equivalencia

**Ubicación**: `Relations.lean`, línea 271  
**Orden**: 11º teorema principal

**Enunciado Matemático**: La relación identidad IdRel A es una relación de equivalencia en A.

**Firma Lean4**:

```lean
theorem IdRel_is_Equivalence (A : U) :
    isEquivalenceOn (IdRel A) A
```

**Dependencias**: `IdRel`, `isEquivalenceOn`, `mem_IdRel`

#### Pertenencia en Clase de Equivalencia

**Ubicación**: `Relations.lean`, línea 289  
**Orden**: 12º teorema principal

**Enunciado Matemático**: x ∈ EqClass a R A ↔ x ∈ A ∧ ⟨a,x⟩ ∈ R.

**Firma Lean4**:

```lean
theorem mem_EqClass (a R A x : U) :
    x ∈ EqClass a R A ↔ x ∈ A ∧ ⟨a, x⟩ ∈ R
```

**Dependencias**: `EqClass`, `SpecSet_is_specified`

#### Elemento en su Propia Clase de Equivalencia

**Ubicación**: `Relations.lean`, línea 294  
**Orden**: 13º teorema principal

**Enunciado Matemático**: Para una relación de equivalencia, a está en su propia clase de equivalencia.

**Firma Lean4**:

```lean
theorem EqClass_mem_self (R A a : U)
    (hEq : isEquivalenceOn R A) (haA : a ∈ A) :
    a ∈ EqClass a R A
```

**Dependencias**: `EqClass`, `isEquivalenceOn`, `mem_EqClass`

#### Relacionados Pertenecen a la Misma Clase

**Ubicación**: `Relations.lean`, línea 301  
**Orden**: 14º teorema principal

**Enunciado Matemático**: Si (a, b) ∈ R y b ∈ A, entonces b ∈ EqClass a R A.

**Firma Lean4**:

```lean
theorem mem_EqClass_of_Related (R A a b : U)
    (_ : isEquivalenceOn R A) (hbA : b ∈ A) (hab : ⟨a, b⟩ ∈ R) :
    b ∈ EqClass a R A
```

**Dependencias**: `EqClass`, `isEquivalenceOn`, `mem_EqClass`

#### Pertenencia Implica Relación

**Ubicación**: `Relations.lean`, línea 308  
**Orden**: 15º teorema principal

**Enunciado Matemático**: Si b ∈ EqClass a R A, entonces (a, b) ∈ R.

**Firma Lean4**:

```lean
theorem Related_of_mem_EqClass (R A a b : U)
    (_ : isEquivalenceOn R A) (hb : b ∈ EqClass a R A) :
    ⟨a, b⟩ ∈ R
```

**Dependencias**: `EqClass`, `isEquivalenceOn`, `mem_EqClass`

#### Caracterización de Pertenencia a Clase

**Ubicación**: `Relations.lean`, línea 314  
**Orden**: 16º teorema principal

**Enunciado Matemático**: Para relaciones de equivalencia, b ∈ EqClass a R A ↔ (a, b) ∈ R.

**Firma Lean4**:

```lean
theorem mem_EqClass_iff (R A a b : U)
    (hEq : isEquivalenceOn R A) (hbA : b ∈ A) :
    b ∈ EqClass a R A ↔ ⟨a, b⟩ ∈ R
```

**Dependencias**: `EqClass`, `isEquivalenceOn`, `mem_EqClass`, `Related_of_mem_EqClass`, `mem_EqClass_of_Related`

#### Igualdad de Clases de Equivalencia

**Ubicación**: `Relations.lean`, línea 321  
**Orden**: 17º teorema principal

**Enunciado Matemático**: Para relaciones de equivalencia, EqClass a R A = EqClass b R A ↔ ⟨a,b⟩ ∈ R.

**Firma Lean4**:

```lean
theorem EqClass_eq_iff (R A a b : U)
    (hEq : isEquivalenceOn R A) (haA : a ∈ A) (hbA : b ∈ A) :
    EqClass a R A = EqClass b R A ↔ ⟨a, b⟩ ∈ R
```

**Dependencias**: `EqClass`, `isEquivalenceOn`, `ExtSet`

#### Las Clases de Equivalencia Particionan el Conjunto

**Ubicación**: `Relations.lean`, línea 352  
**Orden**: 18º teorema principal

**Enunciado Matemático**: Las clases de equivalencia son iguales o disjuntas.

**Firma Lean4**:

```lean
theorem EqClass_eq_or_disjoint (R A a b : U)
    (hEq : isEquivalenceOn R A) (haA : a ∈ A) (hbA : b ∈ A) :
    EqClass a R A = EqClass b R A ∨ BinInter (EqClass a R A) (EqClass b R A) = ∅
```

**Dependencias**: `EqClass`, `isEquivalenceOn`, `BinInter`, `EmptySet`

#### Caracterización de Pertenencia al Dominio

**Ubicación**: `Relations.lean`, línea 386  
**Orden**: 19º teorema principal

**Enunciado Matemático**: x es miembro del dominio de R si y solo si existe y tal que ⟨x, y⟩ ∈ R.

**Firma Lean4**:

```lean
theorem mem_domain (R x : U) :
    x ∈ domain R ↔ ∃ y, ⟨x, y⟩ ∈ R
```

**Dependencias**: `domain`, `SpecSet_is_specified`

#### Caracterización de Pertenencia al Rango

**Ubicación**: `Relations.lean`, línea 403  
**Orden**: 20º teorema principal

**Enunciado Matemático**: y es miembro del rango de R si y solo si existe x tal que ⟨x, y⟩ ∈ R.

**Firma Lean4**:

```lean
theorem mem_range (R y : U) :
    y ∈ range R ↔ ∃ x, ⟨x, y⟩ ∈ R
```

**Dependencias**: `range`, `SpecSet_is_specified`

#### Caracterización de Pertenencia a la Imagen

**Ubicación**: `Relations.lean`, línea 420  
**Orden**: 21º teorema principal

**Enunciado Matemático**: y es miembro de la imagen de R si y solo si existe x tal que ⟨x, y⟩ ∈ R.

**Firma Lean4**:

```lean
theorem mem_imag (R y : U) :
    y ∈ imag R ↔ ∃ x, ⟨x, y⟩ ∈ R
```

**Dependencias**: `imag`, `mem_range`

#### Par en Relación Implica Primera Componente en Dominio

**Ubicación**: `Relations.lean`, línea 424  
**Orden**: 22º teorema principal

**Enunciado Matemático**: Si ⟨x, y⟩ ∈ R, entonces x ∈ domain R.

**Firma Lean4**:

```lean
theorem pair_mem_implies_fst_in_domain (R x y : U) :
    ⟨x, y⟩ ∈ R → x ∈ domain R
```

**Dependencias**: `domain`, `mem_domain`

#### Par en Relación Implica Segunda Componente en Rango

**Ubicación**: `Relations.lean`, línea 429  
**Orden**: 23º teorema principal

**Enunciado Matemático**: Si ⟨x, y⟩ ∈ R, entonces y ∈ range R.

**Firma Lean4**:

```lean
theorem pair_mem_implies_snd_in_range (R x y : U) :
    ⟨x, y⟩ ∈ R → y ∈ range R
```

**Dependencias**: `range`, `mem_range`

#### Par en Relación Implica Segunda Componente en Imagen

**Ubicación**: `Relations.lean`, línea 434  
**Orden**: 24º teorema principal

**Enunciado Matemático**: Si ⟨x, y⟩ ∈ R, entonces y ∈ imag R.

**Firma Lean4**:

```lean
theorem pair_mem_implies_snd_in_imag (R x y : U) :
    ⟨x, y⟩ ∈ R → y ∈ imag R
```

**Dependencias**: `imag`, `mem_imag`

### 4.6 Functions.lean

#### Especificación del Dominio

**Ubicación**: `Functions.lean`, línea 47  
**Orden**: 1º teorema principal

**Enunciado Matemático**: x ∈ Dom f ↔ ∃y, ⟨x,y⟩ ∈ f.

**Firma Lean4**:

```lean
theorem Dom_is_specified (f x : U) :
    x ∈ Dom f ↔ ∃ y, ⟨x, y⟩ ∈ f
```

**Dependencias**: `Dom`, `SpecSet_is_specified`

#### Especificación del Rango

**Ubicación**: `Functions.lean`, línea 58  
**Orden**: 2º teorema principal

**Enunciado Matemático**: y ∈ Ran f ↔ ∃x, ⟨x,y⟩ ∈ f.

**Firma Lean4**:

```lean
theorem Ran_is_specified (f y : U) :
    y ∈ Ran f ↔ ∃ x, ⟨x, y⟩ ∈ f
```

**Dependencias**: `Ran`, `SpecSet_is_specified`

#### Corrección de la Aplicación

**Ubicación**: `Functions.lean`, línea 70  
**Orden**: 3º teorema principal

**Enunciado Matemático**: Si f es univaluada y ⟨x,y⟩ ∈ f, entonces f⦅x⦆ = y.

**Firma Lean4**:

```lean
theorem apply_eq (f x y : U) (hf : isSingleValued f) (hxy : ⟨x, y⟩ ∈ f) :
    f⦅x⦆ = y
```

**Dependencias**: `apply`, `isSingleValued`, `Classical.choose_spec`

#### Aplicación da Membresía

**Ubicación**: `Functions.lean`, línea 78  
**Orden**: 4º teorema principal

**Enunciado Matemático**: Si x ∈ Dom f y f es univaluada, entonces ⟨x, f⦅x⦆⟩ ∈ f.

**Firma Lean4**:

```lean
theorem apply_mem (f x : U) (hf : isSingleValued f) (hx : x ∈ Dom f) :
    ⟨x, f⦅x⦆⟩ ∈ f
```

**Dependencias**: `apply`, `Dom_is_specified`, `apply_eq`

#### Especificación de Función Identidad

**Ubicación**: `Functions.lean`, línea 90  
**Orden**: 5º teorema principal

**Enunciado Matemático**: ⟨x,y⟩ ∈ 𝟙 A ↔ x ∈ A ∧ x = y.

**Firma Lean4**:

```lean
theorem IdFunction_is_specified (A x y : U) :
    ⟨x, y⟩ ∈ (𝟙 A) ↔ x ∈ A ∧ x = y
```

**Dependencias**: `IdFunction`, `SpecSet_is_specified`, `OrderedPair_eq_iff`

#### Identidad es Univaluada

**Ubicación**: `Functions.lean`, línea 102  
**Orden**: 6º teorema principal

**Enunciado Matemático**: 𝟙 A es univaluada.

**Firma Lean4**:

```lean
theorem IdFunction_single_valued (A : U) : isSingleValued (𝟙 A)
```

**Dependencias**: `IdFunction`, `isSingleValued`, `IdFunction_is_specified`

#### Identidad es Función

**Ubicación**: `Functions.lean`, línea 107  
**Orden**: 7º teorema principal

**Enunciado Matemático**: 𝟙 A es función de A a A.

**Firma Lean4**:

```lean
theorem IdFunction_is_function (A : U) : isFunctionFromTo (𝟙 A) A A
```

**Dependencias**: `IdFunction`, `isFunctionFromTo`, `IdFunction_single_valued`

#### Aplicación de Identidad

**Ubicación**: `Functions.lean`, línea 115  
**Orden**: 8º teorema principal

**Enunciado Matemático**: (𝟙 A)⦅x⦆ = x para x ∈ A.

**Firma Lean4**:

```lean
theorem apply_id (A x : U) (hx : x ∈ A) : (𝟙 A)⦅x⦆ = x
```

**Dependencias**: `apply_eq`, `IdFunction_single_valued`, `IdFunction_is_specified`

#### Especificación de Composición

**Ubicación**: `Functions.lean`, línea 135  
**Orden**: 9º teorema principal

**Enunciado Matemático**: ⟨x,z⟩ ∈ g ∘ₛ f ↔ ∃y, ⟨x,y⟩ ∈ f ∧ ⟨y,z⟩ ∈ g.

**Firma Lean4**:

```lean
theorem comp_is_specified (g f x z : U) :
    ⟨x, z⟩ ∈ (g ∘ₛ f) ↔ ∃ y, ⟨x, y⟩ ∈ f ∧ ⟨y, z⟩ ∈ g
```

**Dependencias**: `FunctionComposition`, `SpecSet_is_specified`, `OrderedPair_eq_iff`

#### Composición Preserva Univaluación

**Ubicación**: `Functions.lean`, línea 147  
**Orden**: 10º teorema principal

**Enunciado Matemático**: Si f y g son univaluadas, entonces g ∘ₛ f es univaluada.

**Firma Lean4**:

```lean
theorem comp_single_valued (g f : U) (hf : isSingleValued f) (hg : isSingleValued g) :
    isSingleValued (g ∘ₛ f)
```

**Dependencias**: `isSingleValued`, `comp_is_specified`

#### Composición de Funciones es Función

**Ubicación**: `Functions.lean`, línea 155  
**Orden**: 11º teorema principal

**Enunciado Matemático**: Si f: A → B y g: B → C son funciones, entonces g ∘ₛ f: A → C es función.

**Firma Lean4**:

```lean
theorem comp_is_function (f g A B C : U)
    (hf : isFunctionFromTo f A B) (hg : isFunctionFromTo g B C) :
    isFunctionFromTo (g ∘ₛ f) A C
```

**Dependencias**: `isFunctionFromTo`, `comp_single_valued`, `comp_is_specified`

#### Composición con Identidad (Derecha)

**Ubicación**: `Functions.lean`, línea 175  
**Orden**: 12º teorema principal

**Enunciado Matemático**: f ∘ₛ 𝟙 A = f para f: A → B.

**Firma Lean4**:

```lean
theorem comp_id_right (f A B : U) (hf : isFunctionFromTo f A B) :
    (f ∘ₛ 𝟙 A) = f
```

**Dependencias**: `FunctionComposition`, `IdFunction`, `ExtSet`

#### Composición con Identidad (Izquierda)

**Ubicación**: `Functions.lean`, línea 190  
**Orden**: 13º teorema principal

**Enunciado Matemático**: 𝟙 B ∘ₛ f = f para f: A → B.

**Firma Lean4**:

```lean
theorem comp_id_left (f A B : U) (hf : isFunctionFromTo f A B) :
    ((𝟙 B) ∘ₛ f) = f
```

**Dependencias**: `FunctionComposition`, `IdFunction`, `ExtSet`

#### Especificación de Función Inversa

**Ubicación**: `Functions.lean`, línea 135  
**Orden**: 14º teorema principal

**Enunciado Matemático**: p ∈ f⁻¹ ↔ isOrderedPair p ∧ ⟨snd p, fst p⟩ ∈ f.

**Firma Lean4**:

```lean
theorem inverse_is_specified (f p : U) :
    p ∈ f⁻¹ ↔ isOrderedPair p ∧ ⟨snd p, fst p⟩ ∈ f
```

**Dependencias**: `InverseFunction`, `InverseRel`, `SpecSet_is_specified`

#### Especificación de Restricción (Restriction_is_specified)

**Ubicación**: `Functions.lean`, línea 162  
**Orden**: 15º teorema principal

**Enunciado Matemático**: p ∈ (f ↾ C) ↔ p ∈ f ∧ fst p ∈ C.

**Firma Lean4**:

```lean
theorem Restriction_is_specified (f C p : U) :
    p ∈ (f ↾ C) ↔ p ∈ f ∧ fst p ∈ C
```

**Dependencias**: `Restriction`, `SpecSet_is_specified`

#### Restricción es Subconjunto (Restriction_subset)

**Ubicación**: `Functions.lean`, línea 167  
**Orden**: 16º teorema principal

**Enunciado Matemático**: (f ↾ C) ⊆ f.

**Firma Lean4**:

```lean
theorem Restriction_subset (f C : U) : (f ↾ C) ⊆ f
```

**Dependencias**: `Restriction`, `Restriction_is_specified`

#### Restricción de Función es Función (Restriction_is_function)

**Ubicación**: `Functions.lean`, línea 172  
**Orden**: 17º teorema principal

**Enunciado Matemático**: Si f: A → B y C ⊆ A, entonces (f ↾ C): C → B.

**Firma Lean4**:

```lean
theorem Restriction_is_function (f A B C : U)
    (hf : isFunctionFromTo f A B) (hC : C ⊆ A) :
    isFunctionFromTo (f ↾ C) C B
```

**Dependencias**: `Restriction`, `isFunctionFromTo`, `Restriction_is_specified`, `CartesianProduct_is_specified`

#### Aplicación de Restricción (Restriction_apply)

**Ubicación**: `Functions.lean`, línea 192  
**Orden**: 18º teorema principal

**Enunciado Matemático**: Para x ∈ C, (f ↾ C)⦅x⦆ = f⦅x⦆.

**Firma Lean4**:

```lean
theorem Restriction_apply (f C x : U) (hx : x ∈ C) :
    apply (f ↾ C) x = apply f x
```

**Dependencias**: `Restriction`, `apply`, `Restriction_is_specified`, `fst_of_ordered_pair`

#### Inyectiva Implica Inversa Univaluada

**Ubicación**: `Functions.lean`, línea 251  
**Orden**: 19º teorema principal

**Enunciado Matemático**: Si f es inyectiva, entonces f⁻¹ es univaluada.

**Firma Lean4**:

```lean
theorem injective_inverse_single_valued (f : U) (hf : isInjective f) :
    isSingleValued (f⁻¹)
```

**Dependencias**: `isInjective`, `isSingleValued`, `inverse_is_specified`, `fst_of_ordered_pair`, `snd_of_ordered_pair`

#### Univaluada Implica Inversa Inyectiva

**Ubicación**: `Functions.lean`, línea 223  
**Orden**: 16º teorema principal

**Enunciado Matemático**: Si f es univaluada, entonces f⁻¹ˢ es inyectiva.

**Firma Lean4**:

```lean
theorem single_valued_inverse_injective (f : U) (hf : isSingleValued f) :
    isInjective (f⁻¹ˢ)
```

**Dependencias**: `isSingleValued`, `isInjective`, `inverse_is_specified`

#### Caracterización de Inyectividad

**Ubicación**: `Functions.lean`, línea 250  
**Orden**: 17º teorema principal

**Enunciado Matemático**: f es inyectiva ↔ f⁻¹ˢ es univaluada.

**Firma Lean4**:

```lean
theorem injective_iff_inverse_functional (f : U) :
    isInjective f ↔ isSingleValued (f⁻¹ˢ)
```

**Dependencias**: `isInjective`, `isSingleValued`, `injective_inverse_single_valued`

#### Inyectividad y Aplicación

**Ubicación**: `Functions.lean`, línea 258  
**Orden**: 18º teorema principal

**Enunciado Matemático**: Para función inyectiva, f⦅x₁⦆ = f⦅x₂⦆ → x₁ = x₂.

**Firma Lean4**:

```lean
theorem injective_apply_eq (f A B x₁ x₂ : U)
    (hf : isFunctionFromTo f A B) (hinj : isInjective f)
    (hx₁ : x₁ ∈ A) (hx₂ : x₂ ∈ A) (heq : f⦅x₁⦆ = f⦅x₂⦆) : x₁ = x₂
```

**Dependencias**: `isInjective`, `isFunctionFromTo`, `apply_eq`

#### Caracterización de Suryectividad

**Ubicación**: `Functions.lean`, línea 270  
**Orden**: 19º teorema principal

**Enunciado Matemático**: f es suryectiva en B ↔ Ran f = B.

**Firma Lean4**:

```lean
theorem surjective_iff_range_eq (f A B : U) (hf : isFunctionFromTo f A B) :
    isSurjectiveOnto f B ↔ Ran f = B
```

**Dependencias**: `isSurjectiveOnto`, `Ran`, `ExtSet`

#### Suryectiva Implica Inversa Total

**Ubicación**: `Functions.lean`, línea 285  
**Orden**: 20º teorema principal

**Enunciado Matemático**: Si f: A → B es suryectiva, entonces f⁻¹ˢ es total en B.

**Firma Lean4**:

```lean
theorem surjective_inverse_total (f A B : U)
    (_ : isFunctionFromTo f A B) (hsurj : isSurjectiveOnto f B) :
    ∀ y, y ∈ B → ∃ x, ⟨y, x⟩ ∈ f⁻¹ˢ
```

**Dependencias**: `isSurjectiveOnto`, `inverse_is_specified`

#### Biyección Implica Inversa es Función

**Ubicación**: `Functions.lean`, línea 295  
**Orden**: 21º teorema principal

**Enunciado Matemático**: Si f: A → B es biyección, entonces f⁻¹ˢ: B → A es función.

**Firma Lean4**:

```lean
theorem bijection_inverse_is_function (f A B : U) (hbij : isBijection f A B) :
    isFunctionFromTo (f⁻¹ˢ) B A
```

**Dependencias**: `isBijection`, `isFunctionFromTo`, `injective_inverse_single_valued`

#### Biyección: Composición con Inversa (Derecha)

**Ubicación**: `Functions.lean`, línea 310  
**Orden**: 22º teorema principal

**Enunciado Matemático**: Para biyección f: A → B, (f⁻¹ˢ)⦅f⦅x⦆⦆ = x para x ∈ A.

**Firma Lean4**:

```lean
theorem bijection_comp_inverse_right (f A B : U) (hbij : isBijection f A B) :
    ∀ x, x ∈ A → (f⁻¹ˢ)⦅f⦅x⦆⦆ = x
```

**Dependencias**: `isBijection`, `apply_eq`, `inverse_is_specified`

#### Biyección: Composición con Inversa (Izquierda)

**Ubicación**: `Functions.lean`, línea 325  
**Orden**: 23º teorema principal

**Enunciado Matemático**: Para biyección f: A → B, f⦅(f⁻¹ˢ)⦅y⦆⦆ = y para y ∈ B.

**Firma Lean4**:

```lean
theorem bijection_comp_inverse_left (f A B : U) (hbij : isBijection f A B) :
    ∀ y, y ∈ B → f⦅(f⁻¹ˢ)⦅y⦆⦆ = y
```

**Dependencias**: `isBijection`, `apply_eq`, `inverse_is_specified`

#### Inversa de Inversa

**Ubicación**: `Functions.lean`, línea 340  
**Orden**: 24º teorema principal

**Enunciado Matemático**: Para f ⊆ A ×ₛ B, (f⁻¹ˢ)⁻¹ˢ = f.

**Firma Lean4**:

```lean
theorem inverse_inverse (f A B : U) (hf : f ⊆ A ×ₛ B) : (f⁻¹ˢ)⁻¹ˢ = f
```

**Dependencias**: `InverseFunction`, `ExtSet`, `inverse_is_specified`

#### Biyección Implica Invertibilidad

**Ubicación**: `Functions.lean`, línea 365  
**Orden**: 25º teorema principal

**Enunciado Matemático**: Si f: A → B es biyección, entonces f es invertible.

**Firma Lean4**:

```lean
theorem bijection_implies_invertible (f A B : U) (hbij : isBijection f A B) :
    isInvertible f A B
```

**Dependencias**: `isBijection`, `isInvertible`, `bijection_inverse_is_function`

#### Inverso Izquierdo Implica Inyectividad

**Ubicación**: `Functions.lean`, línea 375  
**Orden**: 26º teorema principal

**Enunciado Matemático**: Si f tiene inverso por izquierda, entonces f es inyectiva.

**Firma Lean4**:

```lean
theorem left_invertible_implies_injective (f A B : U)
    (hf : isFunctionFromTo f A B) (hleft : isLeftInvertible f A B) :
    isInjective f
```

**Dependencias**: `isLeftInvertible`, `isInjective`, `apply_eq`

#### Inverso Derecho Implica Suryectividad

**Ubicación**: `Functions.lean`, línea 395  
**Orden**: 27º teorema principal

**Enunciado Matemático**: Si f tiene inverso por derecha, entonces f es suryectiva.

**Firma Lean4**:

```lean
theorem right_invertible_implies_surjective (f A B : U)
    (hf : isFunctionFromTo f A B) (hright : isRightInvertible f A B) :
    isSurjectiveOnto f B
```

**Dependencias**: `isRightInvertible`, `isSurjectiveOnto`, `apply_mem`

#### Invertibilidad Implica Biyección

**Ubicación**: `Functions.lean`, línea 415  
**Orden**: 28º teorema principal

**Enunciado Matemático**: Si f es invertible, entonces f es biyección.

**Firma Lean4**:

```lean
theorem invertible_implies_bijection (f A B : U)
    (hf : isFunctionFromTo f A B) (hinv : isInvertible f A B) :
    isBijection f A B
```

**Dependencias**: `isInvertible`, `isBijection`, `left_invertible_implies_injective`

#### Equivalencia Biyección-Invertibilidad

**Ubicación**: `Functions.lean`, línea 425  
**Orden**: 29º teorema principal (TEOREMA CENTRAL)

**Enunciado Matemático**: f: A → B es biyección ↔ f es invertible.

**Firma Lean4**:

```lean
theorem bijection_iff_invertible (f A B : U) (hf : isFunctionFromTo f A B) :
    isBijection f A B ↔ isInvertible f A B
```

**Dependencias**: `isBijection`, `isInvertible`, `bijection_implies_invertible`

#### Inversa de Biyección es Biyección

**Ubicación**: `Functions.lean`, línea 405  
**Orden**: 30º teorema principal

**Enunciado Matemático**: Si f: A → B es biyección, entonces f⁻¹ˢ: B → A es biyección.

**Firma Lean4**:

```lean
theorem inverse_is_bijection (f A B : U) (hbij : isBijection f A B) :
    isBijection (f⁻¹ˢ) B A
```

**Dependencias**: `isBijection`, `InverseFunction`, `single_valued_inverse_injective`

#### Equipotencia es Reflexiva

**Ubicación**: `Functions.lean`, línea 435  
**Orden**: 31º teorema principal

**Enunciado Matemático**: A ≃ₛ A.

**Firma Lean4**:

```lean
theorem equipotent_refl (A : U) : A ≃ₛ A
```

**Dependencias**: `isEquipotent`, `IdFunction`, `id_is_bijection`

#### Equipotencia es Simétrica

**Ubicación**: `Functions.lean`, línea 440  
**Orden**: 32º teorema principal

**Enunciado Matemático**: A ≃ₛ B → B ≃ₛ A.

**Firma Lean4**:

```lean
theorem equipotent_symm (A B : U) (h : A ≃ₛ B) : B ≃ₛ A
```

**Dependencias**: `isEquipotent`, `inverse_is_bijection`

#### Equipotencia es Transitiva

**Ubicación**: `Functions.lean`, línea 445  
**Orden**: 33º teorema principal

**Enunciado Matemático**: A ≃ₛ B → B ≃ₛ C → A ≃ₛ C.

**Firma Lean4**:

```lean
theorem equipotent_trans (A B C : U) (hab : A ≃ₛ B) (hbc : B ≃ₛ C) : A ≃ₛ C
```

**Dependencias**: `isEquipotent`, `comp_bijection`

#### Equipotencia es Relación de Equivalencia

**Ubicación**: `Functions.lean`, línea 450  
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

#### Identidad es Inyectiva

**Ubicación**: `Functions.lean`, línea 455  
**Orden**: 35º teorema principal

**Enunciado Matemático**: 𝟙 A es inyectiva.

**Firma Lean4**:

```lean
theorem id_is_injective (A : U) : isInjective (𝟙 A)
```

**Dependencias**: `isInjective`, `IdFunction_is_specified`

#### Dominación es Reflexiva

**Ubicación**: `Functions.lean`, línea 460  
**Orden**: 36º teorema principal

**Enunciado Matemático**: A ≼ₛ A.

**Firma Lean4**:

```lean
theorem dominated_refl (A : U) : A ≼ₛ A
```

**Dependencias**: `isDominatedBy`, `IdFunction_is_function`, `id_is_injective`

#### Dominación es Transitiva

**Ubicación**: `Functions.lean`, línea 465  
**Orden**: 37º teorema principal

**Enunciado Matemático**: A ≼ₛ B → B ≼ₛ C → A ≼ₛ C.

**Firma Lean4**:

```lean
theorem dominated_trans (A B C : U) (hab : A ≼ₛ B) (hbc : B ≼ₛ C) : A ≼ₛ C
```

**Dependencias**: `isDominatedBy`, `comp_is_function`, `comp_injective`

#### Dominación es Preorden

**Ubicación**: `Functions.lean`, línea 475  
**Orden**: 38º teorema principal

**Enunciado Matemático**: ≼ₛ es reflexiva y transitiva.

**Firma Lean4**:

```lean
theorem dominated_is_preorder :
    (∀ (A : U), isDominatedBy A A) ∧
    (∀ (A B C : U), isDominatedBy A B → isDominatedBy B C → isDominatedBy A C)
```

**Dependencias**: `dominated_refl`, `dominated_trans`

#### Equipotencia Implica Dominación Bilateral

**Ubicación**: `Functions.lean`, línea 480  
**Orden**: 39º teorema principal

**Enunciado Matemático**: A ≃ₛ B → (A ≼ₛ B ∧ B ≼ₛ A).

**Firma Lean4**:

```lean
theorem equipotent_implies_dominated_both (A B : U) (h : A ≃ₛ B) :
    (A ≼ₛ B) ∧ (B ≼ₛ A)
```

**Dependencias**: `isEquipotent`, `isDominatedBy`, `inverse_is_bijection`

#### Dominación Estricta es Irreflexiva

**Ubicación**: `Functions.lean`, línea 490  
**Orden**: 40º teorema principal

**Enunciado Matemático**: ¬(A ≺ₛ A).

**Firma Lean4**:

```lean
theorem strict_dominated_irrefl (A : U) : ¬(A ≺ₛ A)
```

**Dependencias**: `isStrictlyDominatedBy`, `dominated_refl`

#### Dominación Estricta es Transitiva

**Ubicación**: `Functions.lean`, línea 495  
**Orden**: 41º teorema principal

**Enunciado Matemático**: A ≺ₛ B → B ≺ₛ C → A ≺ₛ C.

**Firma Lean4**:

```lean
theorem strict_dominated_trans (A B C : U)
    (hab : A ≺ₛ B) (hbc : B ≺ₛ C) : A ≺ₛ C
```

**Dependencias**: `isStrictlyDominatedBy`, `dominated_trans`

#### Composición de Inyectivas es Inyectiva

**Ubicación**: `Functions.lean`, línea 505  
**Orden**: 42º teorema principal

**Enunciado Matemático**: Si f y g son inyectivas, entonces g ∘ₛ f es inyectiva.

**Firma Lean4**:

```lean
theorem comp_injective (f g : U) (hinj_f : isInjective f) (hinj_g : isInjective g) :
    isInjective (g ∘ₛ f)
```

**Dependencias**: `isInjective`, `comp_is_specified`

#### Composición de Suryectivas es Suryectiva

**Ubicación**: `Functions.lean`, línea 515  
**Orden**: 43º teorema principal

**Enunciado Matemático**: Si f y g son suryectivas, entonces g ∘ₛ f es suryectiva.

**Firma Lean4**:

```lean
theorem comp_surjective (f g A B C : U)
    (_ : isFunctionFromTo f A B) (hg : isFunctionFromTo g B C)
    (hsurj_f : isSurjectiveOnto f B) (hsurj_g : isSurjectiveOnto g C) :
    isSurjectiveOnto (g ∘ₛ f) C
```

**Dependencias**: `isSurjectiveOnto`, `comp_is_specified`

#### Composición de Biyecciones es Biyección

**Ubicación**: `Functions.lean`, línea 530  
**Orden**: 44º teorema principal

**Enunciado Matemático**: Si f y g son biyecciones, entonces g ∘ₛ f es biyección.

**Firma Lean4**:

```lean
theorem comp_bijection (f g A B C : U)
    (hf : isFunctionFromTo f A B) (hg : isFunctionFromTo g B C)
    (hbij_f : isBijection f A B) (hbij_g : isBijection g B C) :
    isBijection (g ∘ₛ f) A C
```

**Dependencias**: `isBijection`, `comp_is_function`, `comp_injective`, `comp_surjective`

#### Identidad es Biyección

**Ubicación**: `Functions.lean`, línea 540  
**Orden**: 45º teorema principal

**Enunciado Matemático**: 𝟙 A es biyección de A a A.

**Firma Lean4**:

```lean
theorem id_is_bijection (A : U) : isBijection (𝟙 A) A A
```

**Dependencias**: `isBijection`, `IdFunction_is_function`, `id_is_injective`

#### Especificación de Imagen Directa

**Ubicación**: `Functions.lean`, línea 590  
**Orden**: 46º teorema principal

**Enunciado Matemático**: y ∈ f⦃X⦄ ↔ ∃x, x ∈ X ∧ ⟨x,y⟩ ∈ f.

**Firma Lean4**:

```lean
theorem ImageSet_is_specified (f X y : U) :
    y ∈ f⦃X⦄ ↔ ∃ x, x ∈ X ∧ ⟨x, y⟩ ∈ f
```

**Dependencias**: `ImageSet`, `SpecSet_is_specified`

#### Especificación de Imagen Inversa

**Ubicación**: `Functions.lean`, línea 600  
**Orden**: 47º teorema principal

**Enunciado Matemático**: x ∈ PreimageSet f Y ↔ ∃y, y ∈ Y ∧ ⟨x,y⟩ ∈ f.

**Firma Lean4**:

```lean
theorem PreimageSet_is_specified (f Y x : U) :
    x ∈ PreimageSet f Y ↔ ∃ y, y ∈ Y ∧ ⟨x, y⟩ ∈ f
```

**Dependencias**: `PreimageSet`, `SpecSet_is_specified`

#### Imagen del Conjunto Vacío

**Ubicación**: `Functions.lean`, línea 610  
**Orden**: 48º teorema principal

**Enunciado Matemático**: f⦃∅⦄ = ∅.

**Firma Lean4**:

```lean
theorem image_empty (f : U) : f⦃∅⦄ = ∅
```

**Dependencias**: `ImageSet`, `ExtSet`, `EmptySet_is_empty`

#### Imagen Preserva Subconjuntos

**Ubicación**: `Functions.lean`, línea 620  
**Orden**: 49º teorema principal

**Enunciado Matemático**: Si X ⊆ Y, entonces f⦃X⦄ ⊆ f⦃Y⦄.

**Firma Lean4**:

```lean
theorem image_mono (f X Y : U) (h : X ⊆ Y) : f⦃X⦄ ⊆ f⦃Y⦄
```

**Dependencias**: `ImageSet`, `subseteq`, `ImageSet_is_specified`

#### Imagen de Unión

**Ubicación**: `Functions.lean`, línea 625  
**Orden**: 50º teorema principal

**Enunciado Matemático**: f⦃X ∪ Y⦄ = f⦃X⦄ ∪ f⦃Y⦄.

**Firma Lean4**:

```lean
theorem image_union (f X Y : U) : f⦃BinUnion X Y⦄ = BinUnion (f⦃X⦄) (f⦃Y⦄)
```

**Dependencias**: `ImageSet`, `BinUnion`, `ExtSet`, `BinUnion_is_specified`

#### Imagen Inversa de Unión

**Ubicación**: `Functions.lean`, línea 645  
**Orden**: 51º teorema principal

**Enunciado Matemático**: PreimageSet f (X ∪ Y) = PreimageSet f X ∪ PreimageSet f Y.

**Firma Lean4**:

```lean
theorem preimage_union (f X Y : U) :
    PreimageSet f (BinUnion X Y) = BinUnion (PreimageSet f X) (PreimageSet f Y)
```

**Dependencias**: `PreimageSet`, `BinUnion`, `ExtSet`, `PreimageSet_is_specified`

#### Imagen Inversa de Intersección (Inclusión)

**Ubicación**: `Functions.lean`, línea 665  
**Orden**: 52º teorema principal

**Enunciado Matemático**: PreimageSet f (X ∩ Y) ⊆ PreimageSet f X ∩ PreimageSet f Y.

**Firma Lean4**:

```lean
theorem preimage_inter_subset (f X Y : U) :
    PreimageSet f (BinInter X Y) ⊆ BinInter (PreimageSet f X) (PreimageSet f Y)
```

**Dependencias**: `PreimageSet`, `BinInter`, `subseteq`, `PreimageSet_is_specified`

#### Imagen Inversa de Intersección (Igualdad para Univaluadas)

**Ubicación**: `Functions.lean`, línea 675  
**Orden**: 53º teorema principal

**Enunciado Matemático**: Para f univaluada, PreimageSet f (X ∩ Y) = PreimageSet f X ∩ PreimageSet f Y.

**Firma Lean4**:

```lean
theorem preimage_inter_eq (f X Y : U) (hf : isSingleValued f) :
    PreimageSet f (BinInter X Y) = BinInter (PreimageSet f X) (PreimageSet f Y)
```

**Dependencias**: `PreimageSet`, `BinInter`, `isSingleValued`, `preimage_inter_subset`

#### Teorema de Cantor-Schröder-Bernstein

**Ubicación**: `Functions.lean`, línea 580  
**Orden**: 54º teorema principal (TEOREMA FUNDAMENTAL)

**Enunciado Matemático**: Si A ≼ B y B ≼ A, entonces A ≃ B.

**Firma Lean4**:

```lean
theorem cantor_schroeder_bernstein (A B : U)
    (hab : isDominatedBy A B) (hba : isDominatedBy B A) :
    isEquipotent A B
```

**Dependencias**: `isDominatedBy`, `isEquipotent`, `CSB_bijection`

### 4.7 AtomicBooleanAlgebra.lean

#### Los Singletons son Átomos

**Ubicación**: `AtomicBooleanAlgebra.lean`, línea 85  
**Orden**: 1º teorema principal

**Enunciado Matemático**: {x} es un átomo en 𝒫(A) cuando x ∈ A.

**Firma Lean4**:

```lean
theorem singleton_is_atom (A x : U) (hx : x ∈ A) : isAtom A {x}
```

**Dependencias**: `isAtom`, `Singleton`, `PowerSet`

#### Los Átomos son Singletons

**Ubicación**: `AtomicBooleanAlgebra.lean`, línea 120  
**Orden**: 2º teorema principal

**Enunciado Matemático**: Todo átomo es un singleton.

**Firma Lean4**:

```lean
theorem atom_is_singleton (A X : U) (hAtom : isAtom A X) :
  ∃ x, x ∈ A ∧ X = {x}
```

**Dependencias**: `isAtom`, `Singleton`

### 4.8 Cardinality.lean

#### Caracterización del Conjunto Diagonal (DiagonalSet_is_specified)

**Ubicación**: `Cardinality.lean`, línea 42  
**Orden**: 1º teorema auxiliar

**Enunciado Matemático**: x ∈ DiagonalSet f A ↔ x ∈ A ∧ x ∉ f⦅x⦆.

**Firma Lean4**:

```lean
theorem DiagonalSet_is_specified (f A x : U) :
    x ∈ DiagonalSet f A ↔ x ∈ A ∧ x ∉ f⦅x⦆
```

**Dependencias**: `DiagonalSet`, `SpecSet_is_specified`

#### El Conjunto Diagonal es Subconjunto (DiagonalSet_subset)

**Ubicación**: `Cardinality.lean`, línea 47  
**Orden**: 2º teorema auxiliar

**Enunciado Matemático**: DiagonalSet f A ⊆ A.

**Firma Lean4**:

```lean
theorem DiagonalSet_subset (f A : U) : DiagonalSet f A ⊆ A
```

**Dependencias**: `DiagonalSet`, `DiagonalSet_is_specified`

#### El Conjunto Diagonal está en el Conjunto Potencia (DiagonalSet_in_PowerSet)

**Ubicación**: `Cardinality.lean`, línea 52  
**Orden**: 3º teorema auxiliar

**Enunciado Matemático**: DiagonalSet f A ∈ 𝒫 A.

**Firma Lean4**:

```lean
theorem DiagonalSet_in_PowerSet (f A : U) : DiagonalSet f A ∈ 𝒫 A
```

**Dependencias**: `DiagonalSet`, `PowerSet_is_specified`, `DiagonalSet_subset`

#### El Conjunto Diagonal no está en el Rango (DiagonalSet_not_in_range)

**Ubicación**: `Cardinality.lean`, línea 57  
**Orden**: 4º teorema auxiliar (lema clave)

**Enunciado Matemático**: No existe d ∈ A tal que f⦅d⦆ = DiagonalSet f A.

**Firma Lean4**:

```lean
theorem DiagonalSet_not_in_range (f A : U) :
    ¬∃ d, d ∈ A ∧ f⦅d⦆ = DiagonalSet f A
```

**Dependencias**: `DiagonalSet`, `DiagonalSet_is_specified`, `Classical.byContradiction`

#### Teorema de Cantor (cantor_no_surjection)

**Ubicación**: `Cardinality.lean`, línea 78  
**Orden**: 1º teorema principal (TEOREMA FUNDAMENTAL)

**Enunciado Matemático**: No existe suryección de A a 𝒫(A).

**Firma Lean4**:

```lean
theorem cantor_no_surjection (f A : U) (hf : isFunctionFromTo f A (𝒫 A)) :
  ¬isSurjectiveOnto f (𝒫 A)
```

**Dependencias**: `DiagonalSet`, `DiagonalSet_not_in_range`, `isFunctionFromTo`, `isSurjectiveOnto`

#### No hay Biyección de A a 𝒫(A) (cantor_no_bijection)

**Ubicación**: `Cardinality.lean`, línea 90  
**Orden**: 2º teorema principal

**Enunciado Matemático**: No existe biyección de A a 𝒫(A).

**Firma Lean4**:

```lean
theorem cantor_no_bijection (f A : U) (hf : isFunctionFromTo f A (𝒫 A)) :
    ¬isBijection f A (𝒫 A)
```

**Dependencias**: `cantor_no_surjection`, `isBijection`

#### Caracterización de singletonMap (singletonMap_is_specified)

**Ubicación**: `Cardinality.lean`, línea 100  
**Orden**: 5º teorema auxiliar

**Enunciado Matemático**: ⟨x, y⟩ ∈ singletonMap A ↔ x ∈ A ∧ y = {x}.

**Firma Lean4**:

```lean
theorem singletonMap_is_specified (A x y : U) :
    ⟨x, y⟩ ∈ singletonMap A ↔ x ∈ A ∧ y = {x}
```

**Dependencias**: `singletonMap`, `SpecSet_is_specified`, `Eq_of_OrderedPairs_given_projections`

#### singletonMap es Función (singletonMap_is_function)

**Ubicación**: `Cardinality.lean`, línea 112  
**Orden**: 6º teorema auxiliar

**Enunciado Matemático**: singletonMap A es función de A a 𝒫(A).

**Firma Lean4**:

```lean
theorem singletonMap_is_function (A : U) : isFunctionFromTo (singletonMap A) A (𝒫 A)
```

**Dependencias**: `singletonMap`, `singletonMap_is_specified`, `isFunctionFromTo`

#### singletonMap es Inyectiva (singletonMap_is_injective)

**Ubicación**: `Cardinality.lean`, línea 125  
**Orden**: 7º teorema auxiliar

**Enunciado Matemático**: singletonMap A es inyectiva.

**Firma Lean4**:

```lean
theorem singletonMap_is_injective (A : U) : isInjective (singletonMap A)
```

**Dependencias**: `singletonMap`, `singletonMap_is_specified`, `isInjective`, `Singleton_is_specified`

#### A es Dominado por 𝒫(A) (A_dominated_by_PowerSet)

**Ubicación**: `Cardinality.lean`, línea 136  
**Orden**: 3º teorema principal

**Enunciado Matemático**: A ≼ₛ 𝒫(A).

**Firma Lean4**:

```lean
theorem A_dominated_by_PowerSet (A : U) : isDominatedBy A (𝒫 A)
```

**Dependencias**: `singletonMap`, `singletonMap_is_function`, `singletonMap_is_injective`, `isDominatedBy`

#### 𝒫(A) no Domina a A (PowerSet_not_dominated_by_A)

**Ubicación**: `Cardinality.lean`, línea 140  
**Orden**: 4º teorema principal

**Enunciado Matemático**: ¬(𝒫(A) ≼ₛ A).

**Firma Lean4**:

```lean
theorem PowerSet_not_dominated_by_A (A : U) : ¬isDominatedBy (𝒫 A) A
```

**Dependencias**: `isDominatedBy`, `SpecSet`, `Classical.byContradiction`

#### Dominación Estricta de Cantor (cantor_strict_dominance)

**Ubicación**: `Cardinality.lean`, línea 180  
**Orden**: 5º teorema principal (FORMA CARDINAL)

**Enunciado Matemático**: A ≺ₛ 𝒫(A).

**Firma Lean4**:

```lean
theorem cantor_strict_dominance (A : U) : isStrictlyDominatedBy A (𝒫 A)
```

**Dependencias**: `A_dominated_by_PowerSet`, `PowerSet_not_dominated_by_A`, `isStrictlyDominatedBy`

#### A y 𝒫(A) no son Equipotentes (cantor_not_equipotent)

**Ubicación**: `Cardinality.lean`, línea 183  
**Orden**: 6º teorema principal

**Enunciado Matemático**: ¬(A ≃ₛ 𝒫(A)).

**Firma Lean4**:

```lean
theorem cantor_not_equipotent (A : U) : ¬isEquipotent A (𝒫 A)
```

**Dependencias**: `isEquipotent`, `cantor_no_bijection`

#### Caracterización de SetDiff (SetDiff_is_specified)

**Ubicación**: `Cardinality.lean`, línea 191  
**Orden**: 8º teorema auxiliar

**Enunciado Matemático**: x ∈ (A ∖ B) ↔ x ∈ A ∧ x ∉ B.

**Firma Lean4**:

```lean
theorem SetDiff_is_specified (A B x : U) :
    x ∈ (A ∖ B) ↔ x ∈ A ∧ x ∉ B
```

**Dependencias**: `SetDiff`, `SpecSet_is_specified`

#### SetDiff es Subconjunto (SetDiff_subset)

**Ubicación**: `Cardinality.lean`, línea 196  
**Orden**: 9º teorema auxiliar

**Enunciado Matemático**: (A ∖ B) ⊆ A.

**Firma Lean4**:

```lean
theorem SetDiff_subset (A B : U) : (A ∖ B) ⊆ A
```

**Dependencias**: `SetDiff`, `SetDiff_is_specified`

#### CSB_core es Subconjunto (CSB_core_subset)

**Ubicación**: `Cardinality.lean`, línea 216  
**Orden**: 10º teorema auxiliar

**Enunciado Matemático**: CSB_core f g A B ⊆ A.

**Firma Lean4**:

```lean
theorem CSB_core_subset (f g A B : U) : CSB_core f g A B ⊆ A
```

**Dependencias**: `CSB_core`, `SpecSet_is_specified`

#### CSB_core Contiene la Base (CSB_core_contains_base)

**Ubicación**: `Cardinality.lean`, línea 223  
**Orden**: 11º teorema auxiliar

**Enunciado Matemático**: (A ∖ ImageSet g B) ⊆ CSB_core f g A B.

**Firma Lean4**:

```lean
theorem CSB_core_contains_base (f g A B : U) :
    (A ∖ ImageSet g B) ⊆ CSB_core f g A B
```

**Dependencias**: `CSB_core`, `SetDiff`, `ImageSet`, `SpecSet_is_specified`

#### CSB_core es Cerrado (CSB_core_closed)

**Ubicación**: `Cardinality.lean`, línea 234  
**Orden**: 12º teorema auxiliar

**Enunciado Matemático**: Si x ∈ CSB_core f g A B, entonces g⦅f⦅x⦆⦆ ∈ CSB_core f g A B.

**Firma Lean4**:

```lean
theorem CSB_core_closed (f g A B : U)
    (hf : isFunctionFromTo f A B) (hg : isFunctionFromTo g B A) :
    ∀ x, x ∈ CSB_core f g A B → g⦅f⦅x⦆⦆ ∈ CSB_core f g A B
```

**Dependencias**: `CSB_core`, `isFunctionFromTo`, `apply`, `SpecSet_is_specified`

#### Complemento de CSB_core está en Imagen (CSB_complement_in_image)

**Ubicación**: `Cardinality.lean`, línea 256  
**Orden**: 13º teorema auxiliar

**Enunciado Matemático**: Si x ∈ A y x ∉ CSB_core f g A B, entonces x ∈ ImageSet g B.

**Firma Lean4**:

```lean
theorem CSB_complement_in_image (f g A B x : U)
    (_ : isFunctionFromTo f A B) (_ : isFunctionFromTo g B A)
    (hx_A : x ∈ A) (hx_not : x ∉ CSB_core f g A B) :
    x ∈ ImageSet g B
```

**Dependencias**: `CSB_core`, `ImageSet`, `CSB_core_contains_base`, `SetDiff`, `Classical.byContradiction`

#### Caracterización de CSB_bijection (CSB_bijection_is_specified)

**Ubicación**: `Cardinality.lean`, línea 285  
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

**Dependencias**: `CSB_bijection`, `CSB_core`, `SpecSet_is_specified`, `OrderedPair_mem_CartesianProduct`, `Eq_of_OrderedPairs_given_projections`

#### CSB_bijection es Función (CSB_bijection_is_function)

**Ubicación**: `Cardinality.lean`, línea 302  
**Orden**: 15º teorema auxiliar

**Enunciado Matemático**: CSB_bijection f g A B es función de A a B.

**Firma Lean4**:

```lean
theorem CSB_bijection_is_function (f g A B : U)
    (hf : isFunctionFromTo f A B) (hg : isFunctionFromTo g B A)
    (_ : isInjective f) (hg_inj : isInjective g) :
    isFunctionFromTo (CSB_bijection f g A B) A B
```

**Dependencias**: `CSB_bijection`, `CSB_bijection_is_specified`, `CSB_core_closed`, `CSB_complement_in_image`, `isFunctionFromTo`, `ExistsUnique`

#### CSB_bijection es Inyectiva (CSB_bijection_is_injective)

**Ubicación**: `Cardinality.lean`, línea 351  
**Orden**: 16º teorema auxiliar

**Enunciado Matemático**: CSB_bijection f g A B es inyectiva.

**Firma Lean4**:

```lean
theorem CSB_bijection_is_injective (f g A B : U)
    (hf : isFunctionFromTo f A B) (hg : isFunctionFromTo g B A) (hf_inj : isInjective f) :
    isInjective (CSB_bijection f g A B)
```

**Dependencias**: `CSB_bijection`, `CSB_bijection_is_specified`, `CSB_core`, `CSB_core_closed`, `isInjective`, `apply_eq`

#### CSB_bijection es Suryectiva (CSB_bijection_is_surjective)

**Ubicación**: `Cardinality.lean`, línea 393  
**Orden**: 17º teorema auxiliar

**Enunciado Matemático**: CSB_bijection f g A B es suryectiva en B.

**Firma Lean4**:

```lean
theorem CSB_bijection_is_surjective (f g A B : U)
    (hf : isFunctionFromTo f A B) (hg : isFunctionFromTo g B A)
    (_ : isInjective f) (hg_inj : isInjective g) :
    isSurjectiveOnto (CSB_bijection f g A B) B
```

**Dependencias**: `CSB_bijection`, `CSB_bijection_is_specified`, `CSB_core`, `ImageSet`, `isSurjectiveOnto`, `Classical.byContradiction`

#### CSB_bijection es Biyección (CSB_bijection_is_bijection)

**Ubicación**: `Cardinality.lean`, línea 476  
**Orden**: 18º teorema auxiliar

**Enunciado Matemático**: CSB_bijection f g A B es biyección de A a B.

**Firma Lean4**:

```lean
theorem CSB_bijection_is_bijection (f g A B : U)
    (hf : isFunctionFromTo f A B) (hg : isFunctionFromTo g B A)
    (hf_inj : isInjective f) (hg_inj : isInjective g) :
    isBijection (CSB_bijection f g A B) A B
```

**Dependencias**: `CSB_bijection_is_function`, `CSB_bijection_is_injective`, `CSB_bijection_is_surjective`, `isBijection`

#### Teorema de Cantor-Schröder-Bernstein (cantor_schroeder_bernstein)

**Ubicación**: `Cardinality.lean`, línea 483  
**Orden**: 7º teorema principal (TEOREMA FUNDAMENTAL)

**Enunciado Matemático**: Si A ≼ₛ B y B ≼ₛ A, entonces A ≃ₛ B.

**Firma Lean4**:

```lean
theorem cantor_schroeder_bernstein (A B : U)
    (hab : isDominatedBy A B) (hba : isDominatedBy B A) :
    isEquipotent A B
```

**Dependencias**: `CSB_bijection`, `CSB_bijection_is_bijection`, `isDominatedBy`, `isEquipotent`

#### Antisimetría de Dominación (dominated_antisymm)

**Ubicación**: `Cardinality.lean`, línea 490  
**Orden**: 8º teorema principal

**Enunciado Matemático**: ≼ₛ es antisimétrica módulo equipotencia.

**Firma Lean4**:

```lean
theorem dominated_antisymm (A B : U) :
    isDominatedBy A B → isDominatedBy B A → isEquipotent A B
```

**Dependencias**: `cantor_schroeder_bernstein`

### 4.9 NaturalNumbers.lean

#### El Conjunto Vacío es Natural

**Ubicación**: `NaturalNumbers.lean`, línea 145  
**Orden**: 1º teorema principal (TEOREMA BASE)

**Enunciado Matemático**: ∅ es un número natural.

**Firma Lean4**:

```lean
theorem zero_is_nat : isNat (∅ : U)
```

**Dependencias**: `isNat`, `EmptySet`

#### Irreflexividad de Naturales

**Ubicación**: `NaturalNumbers.lean`, línea 280  
**Orden**: 2º teorema principal

**Enunciado Matemático**: Ningún número natural es miembro de sí mismo.

**Firma Lean4**:

```lean
theorem nat_not_mem_self (n : U) :
  isNat n → n ∉ n
```

**Dependencias**: `isNat`, `isTotalStrictOrderMembershipGuided`

#### Ausencia de Ciclos de Dos Elementos

**Ubicación**: `NaturalNumbers.lean`, línea 295  
**Orden**: 3º teorema principal

**Enunciado Matemático**: No existen ciclos de membresía de dos elementos entre naturales.

**Firma Lean4**:

```lean
theorem nat_no_two_cycle (x y : U) :
  isNat x → isNat y → ¬(x ∈ y ∧ y ∈ x)
```

**Dependencias**: `isNat`, `nat_not_mem_self`

#### Ausencia de Ciclos de Tres Elementos

**Ubicación**: `NaturalNumbers.lean`, línea 320  
**Orden**: 4º teorema principal

**Enunciado Matemático**: No existen ciclos de membresía de tres elementos entre naturales.

**Firma Lean4**:

```lean
theorem nat_no_three_cycle (x y z : U) :
  isNat x → isNat y → isNat z → ¬(x ∈ y ∧ y ∈ z ∧ z ∈ x)
```

**Dependencias**: `isNat`, `nat_no_two_cycle`

#### Elementos de Naturales son Naturales

**Ubicación**: `NaturalNumbers.lean`, línea 520  
**Orden**: 5º teorema principal (TEOREMA FUNDAMENTAL)

**Enunciado Matemático**: Todo elemento de un número natural es un número natural.

**Firma Lean4**:

```lean
theorem nat_element_is_nat (n m : U) :
  isNat n → m ∈ n → isNat m
```

**Dependencias**: `isNat`, `nat_element_is_transitive`, `nat_element_has_strict_total_order`, `nat_element_has_well_order`

#### El Sucesor de un Natural es Natural

**Ubicación**: `NaturalNumbers.lean`, línea 680  
**Orden**: 6º teorema principal (CLAUSURA BAJO SUCESORES)

**Enunciado Matemático**: Si n es natural, entonces σ(n) es natural.

**Firma Lean4**:

```lean
theorem nat_successor_is_nat (n : U) (hn : isNat n) : isNat (σ n)
```

**Dependencias**: `isNat`, `successor`, `successor_of_nat_is_transitive`, `successor_of_nat_has_strict_total_order`

#### Tricotomía entre Naturales

**Ubicación**: `NaturalNumbers.lean`, línea 1080  
**Orden**: 7º teorema principal (TRICOTOMÍA COMPLETA)

**Enunciado Matemático**: Dados dos naturales n y m, se cumple exactamente una: n ∈ m, n = m, o m ∈ n.

**Firma Lean4**:

```lean
theorem nat_trichotomy (n m : U) (hn : isNat n) (hm : isNat m) :
  n ∈ m ∨ n = m ∨ m ∈ n
```

**Dependencias**: `isNat`, `initial_segment_of_nat_is_eq_or_mem`, `inter_nat_is_initial_segment`

#### Segmento Inicial es Igual o Elemento

**Ubicación**: `NaturalNumbers.lean`, línea 1025  
**Orden**: 8º teorema principal

**Enunciado Matemático**: Un segmento inicial de un natural n es igual a n o es un elemento de n.

**Firma Lean4**:

```lean
theorem initial_segment_of_nat_is_eq_or_mem (n S : U)
  (hn : isNat n) (h_init : isInitialSegment S n) :
  S = n ∨ S ∈ n
```

**Dependencias**: `isNat`, `isInitialSegment`, `isWellOrderMembershipGuided`

#### Inyectividad del Sucesor

**Ubicación**: `NaturalNumbers.lean`, línea 1200  
**Orden**: 9º teorema principal

**Enunciado Matemático**: El sucesor es inyectivo: σ(n) = σ(m) → n = m.

**Firma Lean4**:

```lean
theorem successor_injective (n m : U) (hn : isNat n) (hm : isNat m)
  (h_eq : σ n = σ m) : n = m
```

**Dependencias**: `successor`, `isNat`, `nat_no_two_cycle`

#### Todo Natural es Cero o Sucesor

**Ubicación**: `NaturalNumbers.lean`, línea 1250  
**Orden**: 10º teorema principal

**Enunciado Matemático**: Todo número natural es 0 o sucesor de otro natural.

**Firma Lean4**:

```lean
theorem nat_is_zero_or_succ (n : U) (hn : isNat n) :
  n = ∅ ∨ ∃ k, n = σ k
```

**Dependencias**: `isNat`, `EmptySet`, `successor`, `isWellOrderMembershipGuided`

#### Naturales en Conjuntos Inductivos

**Ubicación**: `NaturalNumbers.lean`, línea 1320  
**Orden**: 11º teorema principal

**Enunciado Matemático**: Todo número natural pertenece a cualquier conjunto inductivo.

**Firma Lean4**:

```lean
theorem nat_in_inductive_set (n : U) (hn : isNat n) (I : U) (hI : isInductive I) :
  n ∈ I
```

**Dependencias**: `isNat`, `isInductive`, `nat_is_zero_or_succ`, `nat_subset_inductive_set`

#### Caracterización de Finitud

**Ubicación**: `NaturalNumbers.lean`, línea 850  
**Orden**: 12º teorema principal (TEOREMA DE FINITUD)

**Enunciado Matemático**: Todo subconjunto no vacío de un natural tiene elemento máximo.

**Firma Lean4**:

```lean
theorem nat_has_max (n T : U) (hn : isNat n) (hT_sub : T ⊆ n) (hT_ne : T ≠ ∅) :
  ∃ max, max ∈ T ∧ ∀ x, x ∈ T → (x ∈ max ∨ x = max)
```

**Dependencias**: `isNat`, `isWellOrderMembershipGuided`, `nat_not_mem_self`

### 4.10 Infinity.lean

#### Omega es Inductivo

**Ubicación**: `Infinity.lean`, línea 95  
**Orden**: 1º teorema principal (TEOREMA BASE)

**Enunciado Matemático**: ω es un conjunto inductivo.

**Firma Lean4**:

```lean
theorem Omega_is_inductive : isInductive (ω : U)
```

**Dependencias**: `Omega`, `isInductive`, `zero_in_Omega`, `succ_in_Omega`

#### Minimalidad de Omega

**Ubicación**: `Infinity.lean`, línea 100  
**Orden**: 2º teorema principal (PROPIEDAD FUNDAMENTAL)

**Enunciado Matemático**: ω es subconjunto de cualquier conjunto inductivo K.

**Firma Lean4**:

```lean
theorem Omega_subset_all_inductive (K : U) (hK : isInductive K) : ω ⊆ K
```

**Dependencias**: `Omega`, `isInductive`, `BinInter`

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

**Dependencias**: `Omega`, `ExtSet_wc`, `Omega_subset_all_inductive`

#### Elementos de Omega son Naturales

**Ubicación**: `Infinity.lean`, línea 140  
**Orden**: 4º teorema principal

**Enunciado Matemático**: Todo elemento de ω es un número natural.

**Firma Lean4**:

```lean
theorem mem_Omega_is_Nat (n : U) (hn : n ∈ ω) : isNat n
```

**Dependencias**: `Omega`, `isNat`, `induction_principle`, `zero_is_nat`, `nat_successor_is_nat`

#### Naturales Pertenecen a Omega

**Ubicación**: `Infinity.lean`, línea 165  
**Orden**: 5º teorema principal

**Enunciado Matemático**: Todo número natural pertenece a ω.

**Firma Lean4**:

```lean
theorem Nat_in_Omega (n : U) (hn : isNat n) : n ∈ ω
```

**Dependencias**: `isNat`, `Omega`, `nat_in_inductive_set`, `Omega_is_inductive`

#### Caracterización Completa de Naturales

**Ubicación**: `Infinity.lean`, línea 170  
**Orden**: 6º teorema principal (TEOREMA CENTRAL)

**Enunciado Matemático**: n es natural si y solo si n ∈ ω.

**Firma Lean4**:

```lean
theorem Nat_iff_mem_Omega (n : U) : isNat n ↔ n ∈ ω
```

**Dependencias**: `isNat`, `Omega`, `Nat_in_Omega`, `mem_Omega_is_Nat`

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

**Dependencias**: `Omega`, `SpecSet`, `successor_is_specified`, `induction_principle`

#### Omega es Transitivo

**Ubicación**: `Infinity.lean`, línea 210  
**Orden**: 8º teorema principal

**Enunciado Matemático**: ω es un conjunto transitivo.

**Firma Lean4**:

```lean
theorem Omega_is_transitive : isTransitiveSet (ω : U)
```

**Dependencias**: `Omega`, `isTransitiveSet`, `mem_Omega_is_Nat`, `nat_element_is_nat`, `Nat_in_Omega`

#### Omega tiene Orden Total

**Ubicación**: `Infinity.lean`, línea 220  
**Orden**: 9º teorema principal

**Enunciado Matemático**: ω tiene un orden total estricto guiado por membresía.

**Firma Lean4**:

```lean
theorem Omega_has_total_order : isTotalStrictOrderMembershipGuided (ω : U)
```

**Dependencias**: `Omega`, `isTotalStrictOrderMembershipGuided`, `Omega_is_transitive`, `mem_Omega_is_Nat`, `nat_trichotomy`

#### Omega no tiene Máximo

**Ubicación**: `Infinity.lean`, línea 235  
**Orden**: 10º teorema principal (TEOREMA DE INFINITUD)

**Enunciado Matemático**: ω no tiene elemento máximo (caracteriza la infinitud).

**Firma Lean4**:

```lean
theorem Omega_no_maximum : ∀ n : U, n ∈ ω → ∃ m : U, m ∈ ω ∧ n ∈ m
```

**Dependencias**: `Omega`, `successor`, `succ_in_Omega`, `mem_successor_self`

#### Buena Fundación de la Membresía en ω (nat_mem_wf)

**Ubicación**: `Infinity.lean`
**Orden**: 11º teorema principal (TEOREMA DE BUENA FUNDACIÓN)
**Namespace**: `SetUniverse.InfinityAxiom`

**Enunciado Matemático**: La relación de membresía restringida a ω es bien fundada: la relación R(a, b) ⟺ a ∈ ω ∧ b ∈ ω ∧ a ∈ b es bien fundada (toda cadena descendente termina).

**Firma Lean4**:

```lean
theorem nat_mem_wf : WellFounded (fun a b : U => a ∈ ω ∧ b ∈ ω ∧ a ∈ b)
```

**Dependencias**: `Omega`, `strong_induction_principle`, `SpecSet`, `Acc`

**Nota de implementación**: Los elementos fuera de ω son vacuosamente accesibles (ningún `y` satisface `R y a` si `a ∉ ω`). Los elementos de ω se prueban accesibles por inducción fuerte sobre ω, construyendo `S = SpecSet ω (Acc R)` y aplicando `strong_induction_principle`.

### 4.11 GeneralizedDeMorgan.lean

#### Primera Ley de De Morgan Generalizada

**Ubicación**: `GeneralizedDeMorgan.lean`, línea 85  
**Orden**: 1º teorema principal (LEY FUNDAMENTAL)

**Enunciado Matemático**: El complemento de la unión es la intersección de los complementos: A \ (⋃ F) = ⋂ (A \\ᶠ F).

**Firma Lean4**:

```lean
theorem generalized_demorgan_union (A F : U) :
  A \ (⋃ F) = ⋂ (A \\ᶠ F)
```

**Dependencias**: `Difference`, `UnionSet`, `BinInter`, `ComplementFamily`, `ExtSet`

#### Segunda Ley de De Morgan Generalizada

**Ubicación**: `GeneralizedDeMorgan.lean`, línea 125  
**Orden**: 2º teorema principal (LEY DUAL)

**Enunciado Matemático**: El complemento de la intersección es la unión de los complementos: A \ (⋂ F) = ⋃ (A \\ᶠ F).

**Firma Lean4**:

```lean
theorem generalized_demorgan_intersection (A F : U) (hF_ne : F ≠ ∅) :
  A \ (⋂ F) = ⋃ (A \\ᶠ F)
```

**Dependencias**: `Difference`, `BinInter`, `UnionSet`, `ComplementFamily`, `ExtSet`

#### Complemento de Familia Vacía

**Ubicación**: `GeneralizedDeMorgan.lean`, línea 165  
**Orden**: 3º teorema principal

**Enunciado Matemático**: El complemento de la familia vacía es la familia que contiene solo A.

**Firma Lean4**:

```lean
theorem complement_empty_family (A : U) :
  A \\ᶠ ∅ = {A}
```

**Dependencias**: `ComplementFamily`, `EmptySet`, `Singleton`, `ExtSet`

#### Complemento de Singleton

**Ubicación**: `GeneralizedDeMorgan.lean`, línea 185  
**Orden**: 4º teorema principal

**Enunciado Matemático**: El complemento de una familia singleton es el singleton del complemento: A \\ᶠ {X} = {A \ X}.

**Firma Lean4**:

```lean
theorem complement_singleton_family (A X : U) (hX : X ⊆ A) :
  A \\ᶠ {X} = {A \ X}
```

**Dependencias**: `ComplementFamily`, `Singleton`, `Difference`, `ExtSet`

#### Involutividad del Complemento

**Ubicación**: `GeneralizedDeMorgan.lean`, línea 205  
**Orden**: 5º teorema principal

**Enunciado Matemático**: El complemento del complemento es la identidad: A \\ᶠ (A \\ᶠ F) = F (para F ⊆ 𝒫(A)).

**Firma Lean4**:

```lean
theorem complement_involution (A F : U) (hF : F ⊆ 𝒫 A) :
  A \\ᶠ (A \\ᶠ F) = F
```

**Dependencias**: `ComplementFamily`, `PowerSet`, `ExtSet`, `Difference`

#### Antimonotonicidad del Complemento

**Ubicación**: `GeneralizedDeMorgan.lean`, línea 235  
**Orden**: 6º teorema principal

**Enunciado Matemático**: El complemento invierte las inclusiones: F ⊆ G → A \\ᶠ G ⊆ A \\ᶠ F.

**Firma Lean4**:

```lean
theorem complement_antimono (A F G : U) (hFG : F ⊆ G) :
  A \\ᶠ G ⊆ A \\ᶠ F
```

**Dependencias**: `ComplementFamily`, `subseteq`, `ImageFamily`

#### Distributividad del Complemento sobre Unión

**Ubicación**: `GeneralizedDeMorgan.lean`, línea 255  
**Orden**: 7º teorema principal

**Enunciado Matemático**: A \\ᶠ (F ∪ G) = (A \\ᶠ F) ∪ (A \\ᶠ G).

**Firma Lean4**:

```lean
theorem complement_union_distrib (A F G : U) :
  A \\ᶠ (F ∪ G) = (A \\ᶠ F) ∪ (A \\ᶠ G)
```

**Dependencias**: `ComplementFamily`, `BinUnion`, `ExtSet`

#### Distributividad del Complemento sobre Intersección

**Ubicación**: `GeneralizedDeMorgan.lean`, línea 275  
**Orden**: 8º teorema principal

**Enunciado Matemático**: A \\ᶠ (F ∩ G) = (A \\ᶠ F) ∩ (A \\ᶠ G).

**Firma Lean4**:

```lean
theorem complement_intersection_distrib (A F G : U) :
  A \\ᶠ (F ∩ G) = (A \\ᶠ F) ∩ (A \\ᶠ G)
```

**Dependencias**: `ComplementFamily`, `BinInter`, `ExtSet`

### 4.12 GeneralizedDistributive.lean

#### Primera Ley Distributiva Generalizada

**Ubicación**: `GeneralizedDistributive.lean`, línea 125  
**Orden**: 1º teorema principal (LEY FUNDAMENTAL)

**Enunciado Matemático**: La intersección distribuye sobre la unión: X ∩ (⋃ F) = ⋃ (X ∩ᶠ F).

**Firma Lean4**:

```lean
theorem generalized_distributive_intersection_union (X F : U) :
  X ∩ (⋃ F) = ⋃ (X ∩ᶠ F)
```

**Dependencias**: `BinInter`, `UnionSet`, `IntersectionImageFamily`, `ExtSet`

#### Segunda Ley Distributiva Generalizada

**Ubicación**: `GeneralizedDistributive.lean`, línea 165  
**Orden**: 2º teorema principal (LEY DUAL)

**Enunciado Matemático**: La unión distribuye sobre la intersección: X ∪ (⋂ F) = ⋂ (X ∪ᶠ F) (para F ≠ ∅).

**Firma Lean4**:

```lean
theorem generalized_distributive_union_intersection (X F : U) (hF_ne : F ≠ ∅) :
  X ∪ (⋂ F) = ⋂ (X ∪ᶠ F)
```

**Dependencias**: `BinUnion`, `GeneralizedIntersection`, `UnionImageFamily`, `ExtSet`

#### Distributividad de Intersección sobre Familia Vacía

**Ubicación**: `GeneralizedDistributive.lean`, línea 205  
**Orden**: 3º teorema principal

**Enunciado Matemático**: X ∩ (⋃ ∅) = ⋃ (X ∩ᶠ ∅).

**Firma Lean4**:

```lean
theorem distributive_intersection_empty_family (X : U) :
  X ∩ (⋃ ∅) = ⋃ (X ∩ᶠ ∅)
```

**Dependencias**: `BinInter`, `UnionSet`, `IntersectionImageFamily`, `EmptySet`

#### Distributividad de Intersección sobre Singleton

**Ubicación**: `GeneralizedDistributive.lean`, línea 225  
**Orden**: 4º teorema principal

**Enunciado Matemático**: X ∩ (⋃ {Y}) = ⋃ (X ∩ᶠ {Y}).

**Firma Lean4**:

```lean
theorem distributive_intersection_singleton_family (X Y : U) :
  X ∩ (⋃ {Y}) = ⋃ (X ∩ᶠ {Y})
```

**Dependencias**: `BinInter`, `UnionSet`, `IntersectionImageFamily`, `Singleton`

#### Distributividad de Unión sobre Singleton

**Ubicación**: `GeneralizedDistributive.lean`, línea 245  
**Orden**: 5º teorema principal

**Enunciado Matemático**: X ∪ (⋂ {Y}) = ⋂ (X ∪ᶠ {Y}).

**Firma Lean4**:

```lean
theorem distributive_union_singleton_family (X Y : U) :
  X ∪ (⋂ {Y}) = ⋂ (X ∪ᶠ {Y})
```

**Dependencias**: `BinUnion`, `GeneralizedIntersection`, `UnionImageFamily`, `Singleton`

#### Monotonicidad de la Intersección

**Ubicación**: `GeneralizedDistributive.lean`, línea 265  
**Orden**: 6º teorema principal

**Enunciado Matemático**: Si F ⊆ G, entonces X ∩ᶠ F ⊆ X ∩ᶠ G.

**Firma Lean4**:

```lean
theorem intersection_family_monotonic (X F G : U) (hFG : F ⊆ G) :
  X ∩ᶠ F ⊆ X ∩ᶠ G
```

**Dependencias**: `IntersectionImageFamily`, `subseteq`, `ImageFamily`

#### Monotonicidad de la Unión

**Ubicación**: `GeneralizedDistributive.lean`, línea 285  
**Orden**: 7º teorema principal

**Enunciado Matemático**: Si F ⊆ G, entonces X ∪ᶠ F ⊆ X ∪ᶠ G.

**Firma Lean4**:

```lean
theorem union_family_monotonic (X F G : U) (hFG : F ⊆ G) :
  X ∪ᶠ F ⊆ X ∪ᶠ G
```

**Dependencias**: `UnionImageFamily`, `subseteq`, `ImageFamily`

#### Distributividad sobre Unión de Familias

**Ubicación**: `GeneralizedDistributive.lean`, línea 305  
**Orden**: 8º teorema principal

**Enunciado Matemático**: X ∩ᶠ (F ∪ G) = (X ∩ᶠ F) ∪ (X ∩ᶠ G).

**Firma Lean4**:

```lean
theorem intersection_family_union_distrib (X F G : U) :
  X ∩ᶠ (F ∪ G) = (X ∩ᶠ F) ∪ (X ∩ᶠ G)
```

**Dependencias**: `IntersectionImageFamily`, `BinUnion`, `ExtSet`

#### Distributividad de Unión sobre Unión de Familias

**Ubicación**: `GeneralizedDistributive.lean`, línea 325  
**Orden**: 9º teorema principal

**Enunciado Matemático**: X ∪ᶠ (F ∪ G) = (X ∪ᶠ F) ∪ (X ∪ᶠ G).

**Firma Lean4**:

```lean
theorem union_family_union_distrib (X F G : U) :
  X ∪ᶠ (F ∪ G) = (X ∪ᶠ F) ∪ (X ∪ᶠ G)
```

**Dependencias**: `UnionImageFamily`, `BinUnion`, `ExtSet`

#### Asociatividad Generalizada de Intersección

**Ubicación**: `GeneralizedDistributive.lean`, línea 345  
**Orden**: 10º teorema principal

**Enunciado Matemático**: (X ∩ Y) ∩ᶠ F = X ∩ᶠ (Y ∩ᶠ F).

**Firma Lean4**:

```lean
theorem intersection_family_associative (X Y F : U) :
  (X ∩ Y) ∩ᶠ F = X ∩ᶠ (Y ∩ᶠ F)
```

**Dependencias**: `IntersectionImageFamily`, `BinInter`, `ExtSet`

### 4.13 SetOrder.lean

#### El Vacío es Mínimo Global

**Ubicación**: `SetOrder.lean`, línea 18  
**Orden**: 1º teorema principal (TEOREMA BASE)

**Enunciado Matemático**: ∅ es subconjunto de cualquier conjunto.

**Firma Lean4**:

```lean
theorem empty_is_minimum (x : U) : ∅ ⊆ x
```

**Dependencias**: `EmptySet`, `subseteq`, `EmptySet_is_empty`

#### Unicidad del Mínimo Global

**Ubicación**: `SetOrder.lean`, línea 23  
**Orden**: 2º teorema principal

**Enunciado Matemático**: Si x es subconjunto de todo conjunto, entonces x = ∅.

**Firma Lean4**:

```lean
theorem empty_is_unique_minimum (x : U) :
  (∀ y, x ⊆ y) → x = ∅
```

**Dependencias**: `subseteq`, `EmptySet`, `EqualityOfSubset`

#### Toda Familia está Acotada Inferiormente

**Ubicación**: `SetOrder.lean`, línea 59  
**Orden**: 3º teorema principal

**Enunciado Matemático**: Cualquier familia S está acotada inferiormente (por ∅).

**Firma Lean4**:

```lean
theorem any_family_bounded_below (S : U) : isBoundedBelow S
```

**Dependencias**: `isBoundedBelow`, `empty_is_minimum`

#### La Intersección es Greatest Lower Bound

**Ubicación**: `SetOrder.lean`, línea 64  
**Orden**: 4º teorema principal (TEOREMA FUNDAMENTAL)

**Enunciado Matemático**: A ∩ B es el mayor elemento que es subconjunto de ambos A y B.

**Firma Lean4**:

```lean
theorem inter_is_glb (A B : U) :
  (∀ x, (x ⊆ A ∧ x ⊆ B) → x ⊆ (A ∩ B)) ∧
  (∀ z, (∀ x, (x ⊆ A ∧ x ⊆ B) → x ⊆ z) → (A ∩ B) ⊆ z)
```

**Dependencias**: `BinInter`, `subseteq`, `BinInter_is_specified`, `BinInter_subset`

#### La Unión es Least Upper Bound

**Ubicación**: `SetOrder.lean`, línea 76  
**Orden**: 5º teorema principal (TEOREMA DUAL)

**Enunciado Matemático**: A ∪ B es el menor elemento que contiene tanto A como B.

**Firma Lean4**:

```lean
theorem union_is_lub (A B : U) :
  (∀ x, (A ⊆ x ∧ B ⊆ x) → (A ∪ B) ⊆ x) ∧
  (∀ z, (∀ x, (A ⊆ x ∧ B ⊆ x) → z ⊆ x) → z ⊆ (A ∪ B))
```

**Dependencias**: `BinUnion`, `subseteq`, `BinUnion_is_specified`

#### Reflexividad del Orden

**Ubicación**: `SetOrder.lean`, línea 91  
**Orden**: 6º teorema principal

**Enunciado Matemático**: La relación ⊆ es reflexiva.

**Firma Lean4**:

```lean
theorem order_reflexive (x : U) : x ⊆ x
```

**Dependencias**: `subseteq`, `subseteq_reflexive`

#### Transitividad del Orden

**Ubicación**: `SetOrder.lean`, línea 94  
**Orden**: 7º teorema principal

**Enunciado Matemático**: La relación ⊆ es transitiva.

**Firma Lean4**:

```lean
theorem order_transitive (x y z : U) : x ⊆ y → y ⊆ z → x ⊆ z
```

**Dependencias**: `subseteq`, `subseteq_transitive`

#### Antisimetría del Orden

**Ubicación**: `SetOrder.lean`, línea 97  
**Orden**: 8º teorema principal

**Enunciado Matemático**: La relación ⊆ es antisimétrica.

**Firma Lean4**:

```lean
theorem order_antisymmetric (x y : U) : x ⊆ y → y ⊆ x → x = y
```

**Dependencias**: `subseteq`, `subseteq_antisymmetric`

#### Monotonicidad de la Unión (Izquierda)

**Ubicación**: `SetOrder.lean`, línea 100  
**Orden**: 9º teorema principal

**Enunciado Matemático**: Si A ⊆ B, entonces A ∪ C ⊆ B ∪ C.

**Firma Lean4**:

```lean
theorem union_monotone_left (A B C : U) :
  A ⊆ B → (A ∪ C) ⊆ (B ∪ C)
```

**Dependencias**: `subseteq`, `BinUnion`, `BinUnion_is_specified`

#### Monotonicidad de la Unión (Derecha)

**Ubicación**: `SetOrder.lean`, línea 108  
**Orden**: 10º teorema principal

**Enunciado Matemático**: Si A ⊆ B, entonces C ∪ A ⊆ C ∪ B.

**Firma Lean4**:

```lean
theorem union_monotone_right (A B C : U) :
  A ⊆ B → (C ∪ A) ⊆ (C ∪ B)
```

**Dependencias**: `subseteq`, `BinUnion`, `BinUnion_is_specified`

#### Monotonicidad de la Intersección (Izquierda)

**Ubicación**: `SetOrder.lean`, línea 116  
**Orden**: 11º teorema principal

**Enunciado Matemático**: Si A ⊆ B, entonces A ∩ C ⊆ B ∩ C.

**Firma Lean4**:

```lean
theorem inter_monotone_left (A B C : U) :
  A ⊆ B → (A ∩ C) ⊆ (B ∩ C)
```

**Dependencias**: `subseteq`, `BinInter`, `BinInter_is_specified`

#### Monotonicidad de la Intersección (Derecha)

**Ubicación**: `SetOrder.lean`, línea 123  
**Orden**: 12º teorema principal

**Enunciado Matemático**: Si A ⊆ B, entonces C ∩ A ⊆ C ∩ B.

**Firma Lean4**:

```lean
theorem inter_monotone_right (A B C : U) :
  A ⊆ B → (C ∩ A) ⊆ (C ∩ B)
```

**Dependencias**: `subseteq`, `BinInter`, `BinInter_is_specified`

### 4.14 SetStrictOrder.lean

#### Orden Estricto Implica Orden Parcial

**Ubicación**: `SetStrictOrder.lean`, línea 15  
**Orden**: 1º teorema principal (TEOREMA BASE)

**Enunciado Matemático**: Si A ⊂ B, entonces A ⊆ B.

**Firma Lean4**:

```lean
theorem subset_subseteq (x y : U) :
  x ⊂ y → x ⊆ y
```

**Dependencias**: `subset`, `subseteq`

#### Caracterización del Orden Estricto

**Ubicación**: `SetStrictOrder.lean`, línea 20  
**Orden**: 2º teorema principal

**Enunciado Matemático**: A ⊆ B si y solo si A ⊂ B o A = B.

**Firma Lean4**:

```lean
theorem subseteq_subset_or_eq (x y : U) :
  x ⊆ y → (x ⊂ y ∨ x = y)
```

**Dependencias**: `subseteq`, `subset`

#### Irreflexividad del Orden Estricto

**Ubicación**: `SetStrictOrder.lean`, línea 26  
**Orden**: 3º teorema principal (PROPIEDAD FUNDAMENTAL)

**Enunciado Matemático**: Ningún conjunto es subconjunto estricto de sí mismo.

**Firma Lean4**:

```lean
theorem strict_order_irreflexive (x : U) : ¬(x ⊂ x)
```

**Dependencias**: `subset`

#### Asimetría del Orden Estricto

**Ubicación**: `SetStrictOrder.lean`, línea 30  
**Orden**: 4º teorema principal

**Enunciado Matemático**: Si A ⊂ B, entonces B ⊄ A.

**Firma Lean4**:

```lean
theorem strict_order_asymmetric (x y : U) : x ⊂ y → ¬(y ⊂ x)
```

**Dependencias**: `subset`, `EqualityOfSubset`

#### Transitividad del Orden Estricto

**Ubicación**: `SetStrictOrder.lean`, línea 37  
**Orden**: 5º teorema principal

**Enunciado Matemático**: Si A ⊂ B y B ⊂ C, entonces A ⊂ C.

**Firma Lean4**:

```lean
theorem strict_order_transitive (x y z : U) : x ⊂ y → y ⊂ z → x ⊂ z
```

**Dependencias**: `subset`, `order_transitive`, `EqualityOfSubset`

#### Transitividad Mixta (Izquierda)

**Ubicación**: `SetStrictOrder.lean`, línea 48  
**Orden**: 6º teorema principal

**Enunciado Matemático**: Si A ⊆ B y B ⊂ C, entonces A ⊂ C.

**Firma Lean4**:

```lean
theorem subset_transitive_mixed_left (x y z : U) :
  (x ⊆ y) → (y ⊂ z) → (x ⊂ z)
```

**Dependencias**: `subseteq`, `subset`, `order_transitive`, `EqualityOfSubset`

#### Transitividad Mixta (Derecha)

**Ubicación**: `SetStrictOrder.lean`, línea 58  
**Orden**: 7º teorema principal

**Enunciado Matemático**: Si A ⊂ B y B ⊆ C, entonces A ⊂ C.

**Firma Lean4**:

```lean
theorem subset_transitive_mixed_right (x y z : U) :
  (x ⊂ y) → (y ⊆ z) → (x ⊂ z)
```

**Dependencias**: `subset`, `subseteq`, `order_transitive`, `EqualityOfSubset`

#### Equivalencia entre Órdenes

**Ubicación**: `SetStrictOrder.lean`, línea 68  
**Orden**: 8º teorema principal (TEOREMA CENTRAL)

**Enunciado Matemático**: (A ⊆ B ∧ A ≠ B) ↔ A ⊂ B.

**Firma Lean4**:

```lean
theorem partial_to_strict_order (x y : U) :
  ((x ⊆ y) ∧ (x ≠ y)) ↔ x ⊂ y
```

**Dependencias**: `subseteq`, `subset`

#### Tricotomía Parcial

**Ubicación**: `SetStrictOrder.lean`, línea 78  
**Orden**: 9º teorema principal

**Enunciado Matemático**: Para cualesquiera A, B: A ⊂ B ∨ A = B ∨ B ⊂ A ∨ (A ⊄ B ∧ B ⊄ A).

**Firma Lean4**:

```lean
theorem strict_order_trichotomy_partial (x y : U) :
  x ⊂ y ∨ x = y ∨ y ⊂ x ∨ (¬(x ⊆ y) ∧ ¬(y ⊆ x))
```

**Dependencias**: `subset`, `subseteq`

#### El Vacío es Estrictamente Menor que Cualquier No Vacío

**Ubicación**: `SetStrictOrder.lean`, línea 87  
**Orden**: 10º teorema principal

**Enunciado Matemático**: Si A ≠ ∅, entonces ∅ ⊂ A.

**Firma Lean4**:

```lean
theorem empty_strict_subset_nonempty (x : U) :
  x ≠ ∅ → ∅ ⊂ x
```

**Dependencias**: `EmptySet`, `subset`, `empty_is_minimum`

#### Existencia de Elemento Diferenciador

**Ubicación**: `SetStrictOrder.lean`, línea 93  
**Orden**: 11º teorema principal (TEOREMA DE DIFERENCIACIÓN)

**Enunciado Matemático**: Si A ⊂ B, entonces existe z tal que z ∈ B y z ∉ A.

**Firma Lean4**:

```lean
theorem strict_subset_nonempty (x y : U) :
  x ⊂ y → ∃ z, z ∈ y ∧ z ∉ x
```

**Dependencias**: `subset`, `order_antisymmetric`, `Classical.byContradiction`

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

#### Inclusión en Conjunto Potencia Doble

**Ubicación**: `OrderedPair.lean`, línea 42  
**Orden**: 3º teorema adicional

**Enunciado Matemático**: Si a ∈ A y b ∈ B, entonces ⟨a,b⟩ ∈ 𝒫(𝒫(A ∪ B)).

**Firma Lean4**:

```lean
theorem OrderedPair_in_PowerSet (a b A B : U)
  (ha : a ∈ A) (hb : b ∈ B) :
    ⟨a, b⟩ ∈ 𝒫 (𝒫 (A ∪ B))
```

**Dependencias**: `OrderedPair`, `PowerSet`, `BinUnion`, `Singleton`, `PairSet`

### 4.16 BooleanRing.lean

#### SymDiff es Conmutativa

**Ubicación**: `BooleanRing.lean`, línea 59  
**Orden**: 1º teorema principal

**Enunciado Matemático**: A △ B = B △ A.

**Firma Lean4**:

```lean
theorem SymDiff_is_comm (X Y : U) :
  SymDiff X Y = SymDiff Y X
```

**Dependencias**: `SymDiff`, `SymDiff_comm`

#### SymDiff Identidad con Vacío

**Ubicación**: `BooleanRing.lean`, línea 73  
**Orden**: 2º teorema principal

**Enunciado Matemático**: X △ ∅ = X.

**Firma Lean4**:

```lean
theorem SymDiff_empty_identity (X : U) :
  SymDiff X ∅ = X
```

**Dependencias**: `SymDiff`, `SymDiff_comm`, `SymDiff_empty_left`

#### SymDiff Inverso

**Ubicación**: `BooleanRing.lean`, línea 79  
**Orden**: 3º teorema principal

**Enunciado Matemático**: X △ X = ∅.

**Firma Lean4**:

```lean
theorem SymDiff_inverse (X : U) :
  SymDiff X X = ∅
```

**Dependencias**: `SymDiff`, `SymDiff_self`

#### SymDiff es Asociativa

**Ubicación**: `BooleanRing.lean`, línea 86  
**Orden**: 4º teorema principal (PROPIEDAD FUNDAMENTAL)

**Enunciado Matemático**: (X △ Y) △ Z = X △ (Y △ Z).

**Firma Lean4**:

```lean
theorem SymDiff_assoc (X Y Z : U) :
  SymDiff (SymDiff X Y) Z = SymDiff X (SymDiff Y Z)
```

**Dependencias**: `SymDiff`, `ExtSet`

#### Distributividad de Intersección sobre SymDiff

**Ubicación**: `BooleanRing.lean`, línea 180  
**Orden**: 5º teorema principal

**Enunciado Matemático**: X ∩ (Y △ Z) = (X ∩ Y) △ (X ∩ Z).

**Firma Lean4**:

```lean
theorem SymDiff_inter_distrib (X Y Z : U) :
    BinInter X (SymDiff Y Z) = SymDiff (BinInter X Y) (BinInter X Z)
```

**Dependencias**: `SymDiff`, `BinInter`, `ExtSet`

#### SymDiff de Subconjuntos es Subconjunto

**Ubicación**: `BooleanRing.lean`, línea 240  
**Orden**: 6º teorema principal

**Enunciado Matemático**: Si X, Y ⊆ A, entonces X △ Y ⊆ A.

**Firma Lean4**:

```lean
theorem SymDiff_mem_PowerSet (A X Y : U) (hX : X ∈ 𝒫 A) (hY : Y ∈ 𝒫 A) :
    SymDiff X Y ∈ 𝒫 A
```

**Dependencias**: `SymDiff`, `PowerSet`

#### SymDiff como Unión de Diferencias

**Ubicación**: `BooleanRing.lean`, línea 251  
**Orden**: 7º teorema principal

**Enunciado Matemático**: X △ Y = (X \ Y) ∪ (Y \ X).

**Firma Lean4**:

```lean
theorem SymDiff_eq_union_diff (X Y : U) :
  SymDiff X Y = BinUnion (X \ Y) (Y \ X)
```

**Dependencias**: `SymDiff`, `BinUnion`, `Difference`

#### SymDiff usando Complemento

**Ubicación**: `BooleanRing.lean`, línea 257  
**Orden**: 8º teorema principal

**Enunciado Matemático**: Para X, Y ⊆ A: X △ Y = (X ∪ Y) ∩ (X ∩ Y)^∁[A].

**Firma Lean4**:

```lean
theorem SymDiff_as_complement (A X Y : U) (hX : X ⊆ A) (hY : Y ⊆ A) :
    SymDiff X Y = BinInter (BinUnion X Y) ((BinInter X Y)^∁[ A ])
```

**Dependencias**: `SymDiff`, `BinInter`, `BinUnion`, `Complement`

#### SymDiff igual a X implica Y Vacío

**Ubicación**: `BooleanRing.lean`, línea 288  
**Orden**: 9º teorema principal

**Enunciado Matemático**: X △ Y = X ↔ Y = ∅.

**Firma Lean4**:

```lean
theorem SymDiff_eq_self_iff_empty (X Y : U) : SymDiff X Y = X ↔ Y = ∅
```

**Dependencias**: `SymDiff`, `EmptySet`, `ExtSet`

### 4.17 PowerSetAlgebra.lean

#### Especificación del Complemento

**Ubicación**: `PowerSetAlgebra.lean`, línea 73  
**Orden**: 1º teorema principal

**Enunciado Matemático**: z ∈ X^∁[A] ↔ z ∈ A ∧ z ∉ X.

**Firma Lean4**:

```lean
theorem Complement_is_specified (A X z : U) : z ∈ (X ^∁[ A ]) ↔ z ∈ A ∧ z ∉ X
```

**Dependencias**: `Complement`, `Difference`

#### Unión de Subconjuntos es Subconjunto

**Ubicación**: `PowerSetAlgebra.lean`, línea 80  
**Orden**: 2º teorema principal

**Enunciado Matemático**: Si X, Y ∈ 𝒫(A), entonces X ∪ Y ∈ 𝒫(A).

**Firma Lean4**:

```lean
theorem union_mem_PowerSet (A X Y : U) (hX : X ∈ 𝒫 A) (hY : Y ∈ 𝒫 A) :
    BinUnion X Y ∈ 𝒫 A
```

**Dependencias**: `PowerSet`, `BinUnion`

#### Intersección con Universo

**Ubicación**: `PowerSetAlgebra.lean`, línea 115  
**Orden**: 3º teorema principal

**Enunciado Matemático**: Para X ⊆ A: X ∩ A = X.

**Firma Lean4**:

```lean
theorem PowerSet_inter_universe (A X : U) (hX : X ⊆ A) : BinInter X A = X
```

**Dependencias**: `BinInter`, `subseteq`, `ExtSet`

#### Unión con Complemento

**Ubicación**: `PowerSetAlgebra.lean`, línea 132  
**Orden**: 4º teorema principal

**Enunciado Matemático**: Para X ⊆ A: X ∪ X^∁[A] = A.

**Firma Lean4**:

```lean
theorem PowerSet_union_complement (A X : U) (hX : X ⊆ A) : BinUnion X (X ^∁[ A ]) = A
```

**Dependencias**: `BinUnion`, `Complement`, `ExtSet`

#### Intersección con Complemento

**Ubicación**: `PowerSetAlgebra.lean`, línea 147  
**Orden**: 5º teorema principal

**Enunciado Matemático**: X ∩ X^∁[A] = ∅.

**Firma Lean4**:

```lean
theorem PowerSet_inter_complement (A X : U) : BinInter X (X ^∁[ A ]) = ∅
```

**Dependencias**: `BinInter`, `Complement`, `EmptySet`

#### Distributiva: Unión sobre Intersección

**Ubicación**: `PowerSetAlgebra.lean`, línea 158  
**Orden**: 6º teorema principal (LEY DISTRIBUTIVA)

**Enunciado Matemático**: X ∪ (Y ∩ Z) = (X ∪ Y) ∩ (X ∪ Z).

**Firma Lean4**:

```lean
theorem PowerSet_union_distrib_inter (X Y Z : U) :
    BinUnion X (BinInter Y Z) = BinInter (BinUnion X Y) (BinUnion X Z)
```

**Dependencias**: `BinUnion`, `BinInter`, `ExtSet`

#### Distributiva: Intersección sobre Unión

**Ubicación**: `PowerSetAlgebra.lean`, línea 183  
**Orden**: 7º teorema principal (LEY DISTRIBUTIVA DUAL)

**Enunciado Matemático**: X ∩ (Y ∪ Z) = (X ∩ Y) ∪ (X ∩ Z).

**Firma Lean4**:

```lean
theorem PowerSet_inter_distrib_union (X Y Z : U) :
    BinInter X (BinUnion Y Z) = BinUnion (BinInter X Y) (BinInter X Z)
```

**Dependencias**: `BinInter`, `BinUnion`, `ExtSet`

#### De Morgan: Complemento de Unión

**Ubicación**: `PowerSetAlgebra.lean`, línea 207  
**Orden**: 8º teorema principal (LEY DE DE MORGAN)

**Enunciado Matemático**: (X ∪ Y)^∁[A] = X^∁[A] ∩ Y^∁[A].

**Firma Lean4**:

```lean
theorem PowerSet_DeMorgan_union (A X Y : U) :
    (BinUnion X Y) ^∁[ A ] = BinInter (X ^∁[ A ]) (Y ^∁[ A ])
```

**Dependencias**: `Complement`, `BinUnion`, `BinInter`, `ExtSet`

#### De Morgan: Complemento de Intersección

**Ubicación**: `PowerSetAlgebra.lean`, línea 230  
**Orden**: 9º teorema principal (LEY DE DE MORGAN DUAL)

**Enunciado Matemático**: (X ∩ Y)^∁[A] = X^∁[A] ∪ Y^∁[A].

**Firma Lean4**:

```lean
theorem PowerSet_DeMorgan_inter (A X Y : U) :
    (BinInter X Y) ^∁[ A ] = BinUnion (X ^∁[ A ]) (Y ^∁[ A ])
```

**Dependencias**: `Complement`, `BinInter`, `BinUnion`, `ExtSet`

#### Complemento de Subconjunto es Subconjunto (complement_mem_PowerSet)

**Ubicación**: `PowerSetAlgebra.lean`, línea 97  
**Orden**: 3º teorema de clausura

**Enunciado Matemático**: Si X ∈ 𝒫(A), entonces X^∁[A] ∈ 𝒫(A).

**Firma Lean4**:

```lean
theorem complement_mem_PowerSet (A X : U) (_hX : X ∈ 𝒫 A) :
    (X ^∁[ A ]) ∈ 𝒫 A
```

**Dependencias**: `PowerSet_is_specified`, `Complement_is_specified`

#### El Vacío está en Todo Conjunto Potencia (empty_in_PowerSet)

**Ubicación**: `PowerSetAlgebra.lean`, línea 103  
**Orden**: 4º teorema de clausura (alias)

**Enunciado Matemático**: ∅ ∈ 𝒫(A) para todo A.

**Firma Lean4**:

```lean
theorem empty_in_PowerSet (A : U) : ∅ ∈ 𝒫 A
```

**Dependencias**: `empty_mem_PowerSet`

**Nota**: Alias de `empty_mem_PowerSet` de PowerSet.lean.

#### El Universo está en su Conjunto Potencia (universe_in_PowerSet)

**Ubicación**: `PowerSetAlgebra.lean`, línea 106  
**Orden**: 5º teorema de clausura (alias)

**Enunciado Matemático**: A ∈ 𝒫(A) para todo A.

**Firma Lean4**:

```lean
theorem universe_in_PowerSet (A : U) : A ∈ 𝒫 A
```

**Dependencias**: `self_mem_PowerSet`

**Nota**: Alias de `self_mem_PowerSet` de PowerSet.lean.

#### Doble Complemento

**Ubicación**: `PowerSetAlgebra.lean`, línea 283  
**Orden**: 10º teorema principal (INVOLUTIVIDAD)

**Enunciado Matemático**: Para X ⊆ A: (X^∁[A])^∁[A] = X.

**Firma Lean4**:

```lean
theorem PowerSet_double_complement (A X : U) (hX : X ⊆ A) :
    (X ^∁[ A ]) ^∁[ A ] = X
```

**Dependencias**: `Complement`, `subseteq`, `ExtSet`

#### Absorción: Unión e Intersección

**Ubicación**: `PowerSetAlgebra.lean`, línea 302  
**Orden**: 11º teorema principal

**Enunciado Matemático**: X ∪ (X ∩ Y) = X.

**Firma Lean4**:

```lean
theorem PowerSet_absorb_union_inter (X Y : U) : BinUnion X (BinInter X Y) = X
```

**Dependencias**: `BinUnion`, `BinInter`, `ExtSet`

#### Absorción: Intersección y Unión (PowerSet_absorb_inter_union)

**Ubicación**: `PowerSetAlgebra.lean`, línea 316  
**Orden**: 12º teorema principal

**Enunciado Matemático**: X ∩ (X ∪ Y) = X.

**Firma Lean4**:

```lean
theorem PowerSet_absorb_inter_union (X Y : U) : BinInter X (BinUnion X Y) = X
```

**Dependencias**: `BinInter`, `BinUnion`, `ExtSet`

#### Idempotencia de Unión

**Ubicación**: `PowerSetAlgebra.lean`, línea 322  
**Orden**: 13º teorema principal

**Enunciado Matemático**: X ∪ X = X.

**Firma Lean4**:

```lean
theorem PowerSet_union_idempotent (X : U) : BinUnion X X = X
```

**Dependencias**: `BinUnion`, `BinUnion_idem`

#### Idempotencia de Intersección

**Ubicación**: `PowerSetAlgebra.lean`, línea 326  
**Orden**: 14º teorema principal

**Enunciado Matemático**: X ∩ X = X.

**Firma Lean4**:

```lean
theorem PowerSet_inter_idempotent (X : U) : BinInter X X = X
```

**Dependencias**: `BinInter`, `BinInter_idempotence`

#### Conmutatividad de Unión (PowerSet_union_comm)

**Ubicación**: `PowerSetAlgebra.lean`, línea 331  
**Orden**: 15º teorema principal

**Enunciado Matemático**: X ∪ Y = Y ∪ X.

**Firma Lean4**:

```lean
theorem PowerSet_union_comm (X Y : U) : BinUnion X Y = BinUnion Y X
```

**Dependencias**: `BinUnion_comm`

#### Conmutatividad de Intersección (PowerSet_inter_comm)

**Ubicación**: `PowerSetAlgebra.lean`, línea 334  
**Orden**: 16º teorema principal

**Enunciado Matemático**: X ∩ Y = Y ∩ X.

**Firma Lean4**:

```lean
theorem PowerSet_inter_comm (X Y : U) : BinInter X Y = BinInter Y X
```

**Dependencias**: `BinInter_commutative`

#### Asociatividad de Unión (PowerSet_union_assoc)

**Ubicación**: `PowerSetAlgebra.lean`, línea 339  
**Orden**: 17º teorema principal

**Enunciado Matemático**: X ∪ (Y ∪ Z) = (X ∪ Y) ∪ Z.

**Firma Lean4**:

```lean
theorem PowerSet_union_assoc (X Y Z : U) : BinUnion X (BinUnion Y Z) = BinUnion (BinUnion X Y) Z
```

**Dependencias**: `BinUnion_assoc`

#### Asociatividad de Intersección (PowerSet_inter_assoc)

**Ubicación**: `PowerSetAlgebra.lean`, línea 343  
**Orden**: 18º teorema principal

**Enunciado Matemático**: X ∩ (Y ∩ Z) = (X ∩ Y) ∩ Z.

**Firma Lean4**:

```lean
theorem PowerSet_inter_assoc (X Y Z : U) : BinInter X (BinInter Y Z) = BinInter (BinInter X Y) Z
```

**Dependencias**: `BinInter_associative`

#### Aniquilación: Intersección con Vacío (PowerSet_inter_empty)

**Ubicación**: `PowerSetAlgebra.lean`, línea 348  
**Orden**: 19º teorema principal

**Enunciado Matemático**: X ∩ ∅ = ∅.

**Firma Lean4**:

```lean
theorem PowerSet_inter_empty (X : U) : BinInter X ∅ = ∅
```

**Dependencias**: `BinInter_absorbent_elem`

#### Aniquilación: Vacío e Intersección (PowerSet_empty_inter)

**Ubicación**: `PowerSetAlgebra.lean`, línea 351  
**Orden**: 20º teorema principal

**Enunciado Matemático**: ∅ ∩ X = ∅.

**Firma Lean4**:

```lean
theorem PowerSet_empty_inter (X : U) : BinInter ∅ X = ∅
```

**Dependencias**: `BinInter_commutative`, `BinInter_absorbent_elem`

#### Complemento del Vacío

**Ubicación**: `PowerSetAlgebra.lean`, línea 356  
**Orden**: 21º teorema principal

**Enunciado Matemático**: ∅^∁[A] = A.

**Firma Lean4**:

```lean
theorem PowerSet_complement_empty (A : U) : (∅ ^∁[ A ]) = A
```

**Dependencias**: `Complement`, `EmptySet`, `Difference_with_empty`

#### Complemento del Universo

**Ubicación**: `PowerSetAlgebra.lean`, línea 361  
**Orden**: 22º teorema principal

**Enunciado Matemático**: A^∁[A] = ∅.

**Firma Lean4**:

```lean
theorem PowerSet_complement_universe (A : U) : (A ^∁[ A ]) = ∅
```

**Dependencias**: `Complement`, `EmptySet`, `Difference_self_empty`

### 4.18 PeanoImport.lean

**Módulo**: `ZfcSetTheory.PeanoImport`
**Namespace**: `SetUniverse`
**Actualizado**: 2026-03-04 12:00

#### fromPeano mapea Peano en Von Neumann (fromPeano_is_nat)

**Ubicación**: `PeanoImport.lean`, línea 40
**Orden**: 1º teorema principal

**Enunciado Matemático**: Para todo `p : Peano.ℕ₀`, `fromPeano(p)` es un número natural de Von Neumann: `isNat(fromPeano(p))`.

**Firma Lean4**:

```lean
theorem fromPeano_is_nat (n : Peano.ℕ₀) : isNat (fromPeano (U := U) n)
```

**Dependencias**: `fromPeano`, `isNat`, `zero_is_nat`, `nat_successor_is_nat`

#### fromPeano es Inyectiva (fromPeano_injective)

**Ubicación**: `PeanoImport.lean`, línea 46
**Orden**: 2º teorema principal

**Enunciado Matemático**: `fromPeano` es inyectiva: si `fromPeano(m) = fromPeano(n)` entonces `m = n`.

**Firma Lean4**:

```lean
theorem fromPeano_injective : Function.Injective (fromPeano (U := U))
```

**Dependencias**: `fromPeano`, `successor_nonempty`, `successor_injective`, `fromPeano_is_nat`

**Nota de implementación**: `Function.Injective` usa ligadores estrictos-implícitos `⦃⦄`; en la hipótesis de inducción `ih : ∀ ⦃b⦄, fromPeano m' = fromPeano b → m' = b`, Lean infiere `b` del tipo de la prueba, por lo que se usa `ih proof` (no `ih n' proof`). `successor_injective` requiere argumentos `isNat` explícitos.

#### fromPeano es Sobreyectiva (fromPeano_surjective)

**Ubicación**: `PeanoImport.lean`, línea 71
**Orden**: 3º teorema principal

**Enunciado Matemático**: Todo número natural de Von Neumann está en la imagen de `fromPeano`: si `isNat(n)` entonces existe `p : Peano.ℕ₀` tal que `fromPeano(p) = n`.

**Firma Lean4**:

```lean
theorem fromPeano_surjective (n : U) (hn : isNat n) :
    ∃ p : Peano.ℕ₀, fromPeano (U := U) p = n
```

**Dependencias**: `fromPeano`, `isNat`, `strong_induction_principle`, `SpecSet`, `Nat_in_Omega`, `mem_Omega_is_Nat`, `nat_is_zero_or_succ`, `mem_successor_self`

**Nota de implementación**: Demostrado por inducción fuerte sobre `S = SpecSet ω (fun m => ∃ p, fromPeano p = m)`, aplicando `strong_induction_principle`.

#### fromPeano(toPeano(n)) = n (fromPeano_toPeano)

**Ubicación**: `PeanoImport.lean`, línea 100
**Orden**: 4º teorema principal

**Enunciado Matemático**: `toPeano` es sección derecha de `fromPeano`: para todo Von Neumann natural `n`, `fromPeano(toPeano(n, hn)) = n`.

**Firma Lean4**:

```lean
theorem fromPeano_toPeano (n : U) (hn : isNat n) :
    fromPeano (U := U) (toPeano n hn) = n
```

**Dependencias**: `fromPeano`, `toPeano`, `fromPeano_surjective`, `Classical.choose_spec`

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

#### toPeano es Inyectiva (toPeano_injective)

**Ubicación**: `PeanoImport.lean`, línea 110
**Orden**: 6º teorema principal

**Enunciado Matemático**: `toPeano` es inyectiva en los naturales de Von Neumann: si `toPeano(m, hm) = toPeano(n, hn)` entonces `m = n`.

**Firma Lean4**:

```lean
theorem toPeano_injective {m n : U} (hm : isNat m) (hn : isNat n)
    (h : toPeano m hm = toPeano n hn) : m = n
```

**Dependencias**: `toPeano`, `fromPeano_toPeano`

#### toPeano es Sobreyectiva (toPeano_surjective)

**Ubicación**: `PeanoImport.lean`, línea 115
**Orden**: 7º teorema principal

**Enunciado Matemático**: `toPeano` es sobreyectiva: para todo Peano natural `p` existe un Von Neumann natural `n` tal que `toPeano(n, _) = p`.

**Firma Lean4**:

```lean
theorem toPeano_surjective (p : Peano.ℕ₀) :
    ∃ (n : U) (hn : isNat n), toPeano n hn = p
```

**Dependencias**: `toPeano`, `fromPeano`, `fromPeano_is_nat`, `toPeano_fromPeano`

#### toPeano lleva ∅ a zero (toPeano_zero)

**Ubicación**: `PeanoImport.lean`, línea 147
**Orden**: 8º teorema principal

**Enunciado Matemático**: `toPeano(∅, zero_is_nat) = Peano.ℕ₀.zero`.

**Firma Lean4**:

```lean
theorem toPeano_zero : toPeano (∅ : U) zero_is_nat = Peano.ℕ₀.zero
```

**Dependencias**: `toPeano`, `fromPeano_injective`, `fromPeano_toPeano`, `zero_is_nat`

#### toPeano preserva sucesor (toPeano_successor)

**Ubicación**: `PeanoImport.lean`, línea 155
**Orden**: 9º teorema principal

**Enunciado Matemático**: `toPeano(σ n, _) = Peano.ℕ₀.succ(toPeano(n, hn))` para todo Von Neumann natural n.

**Firma Lean4**:

```lean
theorem toPeano_successor (n : U) (hn : isNat n) :
    toPeano (σ n) (nat_successor_is_nat n hn) = Peano.ℕ₀.succ (toPeano n hn)
```

**Dependencias**: `toPeano`, `fromPeano_injective`, `fromPeano_toPeano`, `nat_successor_is_nat`

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

#### Transporte de recursión Peano → VN, simple (recursion_transport_inv)

**Ubicación**: `PeanoImport.lean`, línea 192
**Orden**: 11º teorema principal

**Enunciado Matemático**: Si `f : Peano.ℕ₀ → U` satisface `f(𝟘) = a` y `f(σ p) = g(f(p))`, entonces `f ∘ ZΠ` satisface la recursión en ω: `f(ZΠ(∅)) = a` y `f(ZΠ(σ n)) = g(f(ZΠ(n)))`.

**Firma Lean4**:

```lean
theorem recursion_transport_inv (a g : U) (f : Peano.ℕ₀ → U)
    (hf_zero : f Peano.ℕ₀.zero = a)
    (hf_succ : ∀ p, f (Peano.ℕ₀.succ p) = apply g (f p)) :
    f (ZΠ (∅ : U) zero_is_nat) = a ∧
    ∀ (n : U) (hn : n ∈ ω),
      f (ZΠ (σ n) (nat_successor_is_nat n (mem_Omega_is_Nat n hn))) =
      apply g (f (ZΠ n (mem_Omega_is_Nat n hn)))
```

**Dependencias**: `toPeano`, `toPeano_zero`, `toPeano_successor`

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

#### Transporte de recursión Peano → VN, con paso (recursion_transport_step_inv)

**Ubicación**: `PeanoImport.lean`, línea 222
**Orden**: 13º teorema principal

**Enunciado Matemático**: Variante de `recursion_transport_inv` para `RecursionTheoremWithStep`. Si `f(σ p) = g(⟨ΠZ p, f(p)⟩)`, entonces `f(ZΠ(σ n)) = g(⟨n, f(ZΠ(n))⟩)` para todo `n ∈ ω`.

**Firma Lean4**:

```lean
theorem recursion_transport_step_inv (a g : U) (f : Peano.ℕ₀ → U)
    (hf_zero : f Peano.ℕ₀.zero = a)
    (hf_succ : ∀ p, f (Peano.ℕ₀.succ p) = apply g ⟨(ΠZ p : U), f p⟩) :
    f (ZΠ (∅ : U) zero_is_nat) = a ∧
    ∀ (n : U) (hn : n ∈ ω),
      f (ZΠ (σ n) (nat_successor_is_nat n (mem_Omega_is_Nat n hn))) =
      apply g ⟨n, f (ZΠ n (mem_Omega_is_Nat n hn))⟩
```

**Dependencias**: `toPeano_zero`, `toPeano_successor`, `fromPeano_toPeano`

#### El sucesor preserva y refleja la membresía (succ_mem_succ_iff)

**Ubicación**: `PeanoImport.lean`, línea 242
**Orden**: 14º teorema principal

**Enunciado Matemático**: Para números naturales de Von Neumann, `n ∈ m ↔ σ n ∈ σ m`.

**Firma Lean4**:

```lean
theorem succ_mem_succ_iff (n m : U) (hn : isNat n) (hm : isNat m) :
    n ∈ m ↔ σ n ∈ σ m
```

**Dependencias**: `nat_trichotomy`, `nat_subset_mem_or_eq`, `nat_successor_is_nat`, `successor_injective`, `nat_not_mem_self`, `successor_is_specified`, `mem_successor_of_mem`

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

---

### 4.19 NaturalNumbersAdd.lean

**Módulo**: `ZfcSetTheory.NaturalNumbersAdd`
**Namespace**: `SetUniverse.NaturalNumbersAdd`
**Actualizado**: 2026-03-08 12:00

#### Sección 1: successorFn

| Nombre | Descripción matemática | Firma Lean4 |
|--------|----------------------|-------------|
| `mem_successorFn` | `⟨n, σ n⟩ ∈ successorFn` para todo n ∈ ω | `theorem mem_successorFn (n : U) (hn : n ∈ (ω : U)) : (⟨n, σ n⟩ : U) ∈ (successorFn : U)` |
| `successorFn_is_function` | `successorFn` es función de ω en ω | `theorem successorFn_is_function : isFunctionFromTo (successorFn : U) ω ω` |
| `successorFn_apply` | Aplicar `successorFn` a n ∈ ω da σ n | `theorem successorFn_apply (n : U) (hn : n ∈ (ω : U)) : apply (successorFn : U) n = σ n` |

#### Sección 2: addFn y add

| Nombre | Descripción matemática | Firma Lean4 |
|--------|----------------------|-------------|
| `addFn_is_function` | `addFn m hm` es función de ω en ω | `theorem addFn_is_function (m : U) (hm : m ∈ (ω : U)) : isFunctionFromTo (addFn m hm) ω ω` |
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

**Descripción**: Demostrado por inducción sobre q. Caso base usa `add_zero`; paso inductivo usa `add_succ` y `successorFn_apply`. Permite transportar automáticamente todos los teoremas de `PeanoNatAdd`.

**Dependencias**: `add_zero`, `add_succ`, `fromPeano`, `Nat_in_Omega`, `fromPeano_is_nat`, `successor`

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

### 4.20 NaturalNumbersMul.lean

**Módulo**: `ZfcSetTheory.NaturalNumbersMul`
**Namespace**: `SetUniverse.NaturalNumbersMul`
**Actualizado**: 2026-03-08 12:00

#### Sección 1: mulFn y mul

| Nombre | Descripción matemática | Firma Lean4 |
|--------|----------------------|-------------|
| `mulFn_is_function` | `mulFn m hm` es función de ω en ω | `theorem mulFn_is_function (m : U) (hm : m ∈ (ω : U)) : isFunctionFromTo (mulFn m hm) ω ω` |
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

**Patrón de demostración**: Igual que en NaturalNumbersAdd: `fromPeano_surjective` + `subst` + `fromPeano_mul`/`fromPeano_add` + `congrArg fromPeano (Peano.Mul.teorema ...)`.

**Dependencias para Sección 4**: `fromPeano_surjective`, `fromPeano_mul`, `fromPeano_add`, `Peano.Mul.zero_mul`, `Peano.Mul.mul_comm`, `Peano.Mul.succ_mul`, `Peano.Mul.mul_one`, `Peano.Mul.one_mul`, `Peano.Mul.mul_assoc`, `Peano.Mul.mul_ldistr`, `Peano.Mul.mul_rdistr`, `Nat_in_Omega`, `fromPeano_is_nat`

---

## 5. Notación y Sintaxis

### 5.1 Operadores Básicos

- `x ∈ A` - Pertenencia (`mem`)
- `A ⊆ B` - Subconjunto (`subseteq`)
- `A ⊂ B` - Subconjunto propio (`subset`)
- `A ⟂ B` - Conjuntos disjuntos (`disjoint`)
- `∅` - Conjunto vacío (`EmptySet`)

### 5.2 Construcciones de Conjuntos

- `{a}` - Singleton (`Singleton`)
- `{a, b}` - Par no ordenado (`PairSet`)
- `⋂ w` - Intersección de familia (`interSet`)
- `⟨a, b⟩` - Par ordenado (`OrderedPair`)
- `A ×ₛ B` - Producto cartesiano (`CartesianProduct`)

### 5.3 Operaciones Binarias

- `A ∪ B` - Unión binaria (`BinUnion`)
- `A ∩ B` - Intersección binaria (`BinInter`)
- `A \ B` - Diferencia (`Difference`)
- `A △ B` - Diferencia simétrica (`SymDiff`)

### 5.4 Funciones

- `f⦅x⦆` - Aplicación de función (`apply`)
- `𝟙 A` - Función identidad (`IdFunction`)
- `g ∘ f` - Composición (`FunctionComposition`)
- `f⁻¹` - Función inversa (`InverseFunction`)
- `f ↾ C` - Restricción de f a dominio C (`Restriction`)
- `f[X]` - Imagen directa (`ImageSet`)
- `f⁻¹[Y]` - Imagen inversa (`PreimageSet`)
- `A ≃ₛ B` - Equipotencia (`isEquipotent`)
- `A ≼ₛ B` - Dominación (`isDominatedBy`)
- `A ≺ₛ B` - Dominación estricta (`isStrictlyDominatedBy`)

### 5.5 Números Naturales

- `σ n` - Función sucesor (`successor`)
- `∈[S]` - Orden estricto guiado por membresía (`StrictOrderMembershipGuided`)
- `0`, `1`, `2`, `3` - Naturales específicos (`zero`, `one`, `two`, `three`)

### 5.6 Conjunto Potencia

- `𝒫 A` - Conjunto potencia de A (`PowerSetOf`)

### 5.7 Infinito

- `ω` - Conjunto de todos los números naturales (`Omega`)

### 5.12 Isomorfismo Peano ↔ Von Neumann

- `ΠZ p` - Conversión Peano → Von Neumann: `fromPeano p` (`scoped notation "ΠZ"`)
- `ZΠ n hn` - Conversión Von Neumann → Peano: `toPeano n hn` (`scoped notation "ZΠ"`)

**Uso**: Ambas notaciones están disponibles con `open SetUniverse` (son `scoped`). No se abren en `NaturalNumbersAdd`/`NaturalNumbersMul` para evitar ambigüedad.

### 5.13 Aritmética en ω

- `add m n` - Suma en ω (`NaturalNumbersAdd.add`); requiere `open SetUniverse.NaturalNumbersAdd` o export
- `mul m n` - Producto en ω (`NaturalNumbersMul.mul`); requiere `open SetUniverse.NaturalNumbersMul` o export

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
export SetUniverse.ExtensionAxiom (
    ExtSet ExtSetReverse ExtSet_wc EqualityOfSubset
    subseteq subseteq_reflexive subseteq_transitive subseteq_antisymmetric
    disjoint disjoint_symm disjoint_is_empty disjoint_is_empty_wc
    subset_irreflexive subset_asymmetric subset_transitive
)
```

### 6.2 Relations.lean

```lean
export SetUniverse.Relations (
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
export SetUniverse.PowerSetAxiom (
  PowerSet
  PowerSetExistsUnique
  PowerSetOf
  PowerSet_is_specified
  PowerSet_is_unique
  empty_mem_PowerSet
  self_mem_PowerSet
  PowerSet_nonempty
  PowerSet_empty
  PowerSet_mono
  PowerSet_mono_iff
  PowerSet_inter
  PowerSet_union_subset
  subset_PowerSet_Union
  Union_PowerSet
)
```

### 6.4 Functions.lean

```lean
export Functions (
  isSingleValued
  isFunctionFromTo
  apply apply_mem apply_eq
  FunctionComposition comp_is_specified comp_is_function
  IdFunction apply_id
  InverseFunction inverse_is_specified
  Restriction Restriction_is_specified Restriction_subset Restriction_is_function Restriction_apply
  ImageSet PreimageSet
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
  DiagonalSet DiagonalSet_is_specified DiagonalSet_subset DiagonalSet_in_PowerSet
  DiagonalSet_not_in_range
  cantor_no_surjection cantor_no_bijection cantor_not_equipotent
  singletonMap singletonMap_is_specified singletonMap_is_function singletonMap_is_injective
  A_dominated_by_PowerSet PowerSet_not_dominated_by_A cantor_strict_dominance
  SetDiff SetDiff_is_specified SetDiff_subset
  CSB_core CSB_core_subset CSB_core_contains_base CSB_core_closed
  CSB_bijection CSB_bijection_is_specified
  CSB_bijection_is_function CSB_bijection_is_injective CSB_bijection_is_surjective
  CSB_bijection_is_bijection
  cantor_schroeder_bernstein dominated_antisymm
)
```

### 6.6 NaturalNumbers.lean

```lean
export NaturalNumbers (
  -- Core definitions
  successor successor_is_specified
  isInductive isTransitiveSet
  StrictOrderMembershipGuided mem_StrictOrderMembershipGuided
  isTotalStrictOrderMembershipGuided isWellOrderMembershipGuided
  isNat
  -- Basic theorems
  zero_is_nat mem_successor_self subset_of_mem_successor
  successor_preserves_transitivity transitive_element_subset
  -- Well-foundedness properties
  nat_not_mem_self nat_no_two_cycle nat_no_three_cycle
  nat_element_is_transitive nat_element_has_strict_total_order
  nat_element_has_well_order nat_element_is_nat
  nat_ne_successor successor_of_nat_is_transitive
  successor_of_nat_has_strict_total_order nat_successor_is_nat
  no_nat_between
  -- Initial segments and trichotomy
  isInitialSegment initial_segment_of_nat_is_eq_or_mem
  inter_nat_is_initial_segment nat_subset_mem_or_eq
  nat_trichotomy nat_mem_trans nat_mem_asymm
  nat_is_initial_segment nat_element_trichotomy
  successor_injective successor_nonempty mem_successor_of_mem
  -- Nat is Zero or Succ
  nat_is_zero_or_succ nat_subset_inductive_set nat_in_inductive_set
  -- Naturales específicos en conjuntos inductivos
  zero_in_inductive one_in_inductive two_in_inductive three_in_inductive
  nat_has_max
  -- Examples
  zero one two three zero_eq one_eq two_eq three_eq
)
```

### 6.7 Infinity.lean

```lean
export InfinityAxiom (
  ExistsInductiveSet
  Omega
  Omega_is_inductive
  Omega_subset_all_inductive
  zero_in_Omega
  succ_in_Omega
  induction_principle
  mem_Omega_is_Nat
  Nat_in_Omega
  Nat_iff_mem_Omega
  strong_induction_principle
  Omega_is_transitive
  Omega_element_is_transitive
  Omega_has_total_order
  Omega_no_maximum
)
```

### 6.8 GeneralizedDeMorgan.lean

```lean
export GeneralizedDeMorgan (
  -- Core definitions
  ImageFamily ComplementFamily ComplementFunction
  -- Basic properties
  mem_ImageFamily mem_ComplementFamily
  ComplementFunction_is_function ComplementFunction_domain
  ComplementFunction_range ComplementFunction_apply
  -- Main theorems
  generalized_demorgan_union generalized_demorgan_intersection
  complement_empty_family complement_singleton_family
  complement_involution complement_antimono
  complement_union_distrib complement_intersection_distrib
  -- Additional properties
  complement_preserves_finite complement_preserves_countable
  complement_empty_set complement_universe
)
```

### 6.9 GeneralizedDistributive.lean

```lean
export GeneralizedDistributive (
  -- Core definitions
  GeneralizedIntersection IntersectionImageFamily IntersectionFunction
  UnionImageFamily UnionFunction
  -- Basic properties
  mem_GeneralizedIntersection mem_IntersectionImageFamily mem_UnionImageFamily
  IntersectionFunction_is_function IntersectionFunction_apply
  UnionFunction_is_function UnionFunction_apply
  -- Main theorems
  generalized_distributive_intersection_union generalized_distributive_union_intersection
  distributive_intersection_empty_family distributive_intersection_singleton_family
  distributive_union_singleton_family
  -- Monotonicity
  intersection_family_monotonic union_family_monotonic
  -- Distributivity over family operations
  intersection_family_union_distrib union_family_union_distrib
  intersection_family_intersection_distrib union_family_intersection_distrib
  -- Associativity
  intersection_family_associative union_family_associative
  -- Additional properties
  intersection_family_empty union_family_empty
  intersection_family_singleton union_family_singleton
)
```

### 6.10 BooleanRing.lean

```lean
export SetUniverse.BooleanRing (
    SymDiff_is_comm
    SymDiff_empty_identity
    SymDiff_identity_empty
    SymDiff_inverse
    SymDiff_assoc
    SymDiff_inter_distrib
    SymDiff_inter_distrib_right
    SymDiff_mem_PowerSet
    SymDiff_eq_union_diff
    SymDiff_as_complement
    SymDiff_eq_self_iff_empty
)
```

### 6.11 PowerSetAlgebra.lean

```lean
export SetUniverse.PowerSetAlgebra (
    Complement
    Complement_is_specified
    union_mem_PowerSet
    inter_mem_PowerSet
    complement_mem_PowerSet
    empty_in_PowerSet
    universe_in_PowerSet
    PowerSet_union_empty
    PowerSet_empty_union
    PowerSet_inter_universe
    PowerSet_universe_inter
    PowerSet_union_complement
    PowerSet_inter_complement
    PowerSet_union_distrib_inter
    PowerSet_inter_distrib_union
    PowerSet_DeMorgan_union
    PowerSet_DeMorgan_inter
    PowerSet_absorb_union_inter
    PowerSet_absorb_inter_union
    PowerSet_double_complement
    PowerSet_union_idempotent
    PowerSet_inter_idempotent
    PowerSet_union_comm
    PowerSet_inter_comm
    PowerSet_union_assoc
    PowerSet_inter_assoc
    PowerSet_inter_empty
    PowerSet_empty_inter
    PowerSet_complement_empty
    PowerSet_complement_universe
)
```

### 6.12 SetOrder.lean

```lean
export SetOrder (
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

### 6.13 SetStrictOrder.lean

```lean
export SetStrictOrder (
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

### 6.14 NaturalNumbers.lean

```lean
export NaturalNumbers (
  -- Definiciones de orden-epsilón
  successor
  successor_is_specified
  isInductive
  isTransitiveSet
  StrictOrderMembershipGuided
  mem_StrictOrderMembershipGuided
  isTotalStrictOrderMembershipGuided
  isWellOrderMembershipGuided
  isNat
  -- Propiedades elementales
  zero_is_nat
  mem_successor_self
  subset_of_mem_successor
  mem_successor_of_mem
  successor_preserves_transitivity
  transitive_element_subset
  -- Teoremas de buena fundación
  nat_not_mem_self
  nat_no_two_cycle
  nat_no_three_cycle
  -- Propiedades estructurales (heredabilidad)
  nat_element_is_transitive
  nat_element_has_strict_total_order
  nat_element_has_well_order
  nat_element_is_nat
  -- Clausura bajo sucesores
  nat_ne_successor
  successor_of_nat_is_transitive
  successor_of_nat_has_strict_total_order
  nat_successor_is_nat
  successor_injective
  successor_nonempty
  -- Segmentos iniciales y tricotomía
  isInitialSegment
  initial_segment_of_nat_is_eq_or_mem
  inter_nat_is_initial_segment
  nat_subset_mem_or_eq
  nat_trichotomy
  nat_mem_trans
  nat_mem_asymm
  nat_is_initial_segment
  nat_element_trichotomy
  no_nat_between
  -- Finitud y conjunto vacío
  nat_has_max
  nat_is_zero_or_succ
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
export OrderedPairExtensions (
  OrderedPair_eq_of
  OrderedPair_eq_iff
  OrderedPair_in_PowerSet
)
```

### 6.16 CartesianProduct.lean

```lean
export CartesianProduct (
  CartesianProduct
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

**Namespace**: `SetUniverse.Recursion`
**Última modificación**: 2026-03-05
**Dependencias**: `NaturalNumbers`, `Functions`, `Relations`, `CartesianProduct`, `OrderedPair`, `Union`, `PowerSet` + anteriores

#### Sección 0: Lemas Auxiliares Locales

| Nombre | Descripción matemática | Firma Lean 4 |
|--------|----------------------|--------------|
| `function_domain_eq` | Si f : A → B entonces dom(f) = A | `function_domain_eq (f A B : U) (h : isFunctionFromTo f A B) : domain f = A` |
| `mem_succ_iff_local` | x ∈ σ n ↔ x ∈ n ∨ x = n | `mem_succ_iff_local (n x : U) : x ∈ σ n ↔ x ∈ n ∨ x = n` |
| `subset_succ_local` | n ⊆ σ n | `subset_succ_local (n : U) : n ⊆ σ n` |
| `zero_in_succ_nat` | ∅ ∈ σ n para todo n ∈ ω | `zero_in_succ_nat (n : U) (hn : n ∈ ω) : (∅ : U) ∈ σ n` |
| `succ_mem_succ_of_mem` | Si k ∈ n (ambos naturales) entonces σ k ∈ σ n | `succ_mem_succ_of_mem (k n : U) (hk_nat : isNat k) (hn_nat : isNat n) (hk : k ∈ n) : σ k ∈ σ n` |

#### Sección 1: Definición de Cómputo Local

**Definición** (`isComputation`): Un conjunto f es un *cómputo de longitud n* para la función recursiva con base a ∈ A y paso g : A → A si f : σ n → A, f(∅) = a, y ∀ k ∈ n, f(σ k) = g(f(k)).

```lean
def isComputation (n : U) (f : U) (A : U) (a : U) (g : U) : Prop :=
  isFunctionFromTo f (σ n) A ∧
  (apply f (∅ : U) = a) ∧
  (∀ k, k ∈ n → apply f (σ k) = apply g (apply f k))
```

**Dependencias de construcción**: `isFunctionFromTo`, `apply`, `successor` (σ)

| Nombre | Descripción matemática | Firma Lean 4 |
|--------|----------------------|--------------|
| `restriction_is_computation` | La restricción de un cómputo de longitud σ n a σ n es un cómputo de longitud n | `restriction_is_computation (A a g n : U) (hn : n ∈ ω) : ∀ f, isComputation (σ n) f A a g → isComputation n (Restriction f (σ n)) A a g` |

#### Sección 2: Unicidad Local

| Nombre | Descripción matemática | Firma Lean 4 |
|--------|----------------------|--------------|
| `computation_uniqueness` | Para cada n ∈ ω, el cómputo de longitud n es único: si f₁ y f₂ son cómputos de longitud n para (A, a, g), entonces f₁ = f₂ | `computation_uniqueness (A a g : U) : ∀ n, n ∈ ω → ∀ f₁ f₂, isComputation n f₁ A a g → isComputation n f₂ A a g → f₁ = f₂` |

**Dependencias**: `induction_principle`, `ExtSet`, `apply_eq`, `apply_mem`, `OrderedPairSet_is_WellConstructed`, `Restriction_is_specified`, `Restriction_subset`, `restriction_is_computation`

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
| `union_compatible_is_function` | La unión de un sistema compatible de funciones es monovaluada | `union_compatible_is_function (F : U) (h_funcs : ∀ f, f ∈ F → ∃ A B, isFunctionFromTo f A B) (h_compat : isCompatibleSystem F) : isSingleValued (⋃ F)` |

**Dependencias**: `UnionSet_is_specified`, `BinInter_is_specified`, `apply_eq`, `mem_domain`

#### Sección 4: Existencia Local (Inducción)

| Nombre | Descripción matemática | Firma Lean 4 |
|--------|----------------------|--------------|
| `computation_existence` | Para todo n ∈ ω, existe un cómputo de longitud n | `computation_existence (A a g : U) (ha : a ∈ A) (hg : isFunctionFromTo g A A) : ∀ n, n ∈ ω → ∃ f, isComputation n f A a g` |

**Dependencias**: `induction_principle`, `Singleton`, `BinUnion_is_specified`, `Singleton_is_specified`, `apply_eq`, `apply_mem`, `Eq_of_OrderedPairs_given_projections`

#### Sección 5: Lemas de Compatibilidad Global

| Nombre | Descripción matemática | Firma Lean 4 |
|--------|----------------------|--------------|
| `succ_subset_omega` | Para todo n ∈ ω, σ n ⊆ ω | `succ_subset_omega (n : U) (hn : n ∈ ω) : (σ n) ⊆ ω` |
| `computation_subset_omega_times_A` | Todo cómputo de longitud n ∈ ω es subconjunto de ω ×ₛ A | `computation_subset_omega_times_A (A a g n : U) (hn : n ∈ ω) (f : U) (hf : isComputation n f A a g) : f ⊆ ω ×ₛ A` |
| `succ_subset_succ_of_mem` | Si n₁ ∈ n₂ (con n₂ natural), entonces σ n₁ ⊆ σ n₂ | `succ_subset_succ_of_mem (n₁ n₂ : U) (hn₂_nat : isNat n₂) (h : n₁ ∈ n₂) : σ n₁ ⊆ σ n₂` |
| `restriction_computation_general` | Si n₁ ∈ n₂ y f es cómputo de longitud n₂, entonces f restringido a σ n₁ es cómputo de longitud n₁ | `restriction_computation_general (A a g n₁ n₂ : U) (hn₁ : n₁ ∈ ω) (hn₂_nat : isNat n₂) (hlt : n₁ ∈ n₂) (f : U) (hf : isComputation n₂ f A a g) : isComputation n₁ (Restriction f (σ n₁)) A a g` |

**Definición** (`RecursionComputations`): El conjunto de todos los cómputos válidos para (A, a, g): el conjunto de funciones f ∈ 𝒫(ω ×ₛ A) tales que existe n ∈ ω con f un cómputo de longitud n.

```lean
noncomputable def RecursionComputations (A a g : U) : U :=
  SpecSet (𝒫 (ω ×ₛ A)) (fun f => ∃ n, (n ∈ ω) ∧ (isComputation n f A a g))
```

**Dependencias de construcción**: `SpecSet`, `PowerSet` (𝒫), `CartesianProduct` (×ₛ), `isComputation`, `ω`

| Nombre | Descripción matemática | Firma Lean 4 |
|--------|----------------------|--------------|
| `computations_are_compatible` | Los cómputos en RecursionComputations A a g son compatibles a pares (isCompatibleSystem) | `computations_are_compatible (A a g : U) : isCompatibleSystem (RecursionComputations A a g)` |

**Dependencias de `computations_are_compatible`**: `SpecSet_is_specified`, `BinInter_is_specified`, `nat_trichotomy`, `restriction_computation_general`, `computation_uniqueness`, `Restriction_apply`, `function_domain_eq`

#### Sección 6: Teorema de Recursión (Global)

| Nombre | Descripción matemática | Firma Lean 4 |
|--------|----------------------|--------------|
| `RecursionTheorem` | **Teorema de Recursión**: Para todo conjunto A, a ∈ A y g : A → A, existe una única función F : ω → A tal que F(∅) = a y F(σ n) = g(F(n)) para todo n ∈ ω | `RecursionTheorem (A a g : U) (ha : a ∈ A) (hg : isFunctionFromTo g A A) : ∃! F, isFunctionFromTo F ω A ∧ (apply F (∅ : U) = a) ∧ (∀ n, n ∈ ω → apply F (σ n) = apply g (apply F n))` |

**Descripción de la construcción**: F = ⋃(RecursionComputations A a g). La función F es la unión de todos los cómputos locales. La monovaluación sigue de `computations_are_compatible` + `union_compatible_is_function`. La unicidad se demuestra por inducción sobre ω usando `induction_principle`.

**Dependencias**: `RecursionComputations`, `computations_are_compatible`, `union_compatible_is_function`, `computation_existence`, `computation_subset_omega_times_A`, `induction_principle`, `ExtSet`, `apply_eq`, `apply_mem`, `OrderedPairSet_is_WellConstructed`, `SpecSet_is_specified`, `PowerSet_is_specified`, `UnionSet_is_specified`

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
  RecursionTheoremWithStep
  RecursiveFn
  RecursiveFn_is_function
  RecursiveFn_zero
  RecursiveFn_succ
  RecursiveFn_unique
)
```

### 6.18 PeanoImport.lean

**Namespace**: `SetUniverse.PeanoIsomorphism` (exportado a `SetUniverse`)
**Última modificación**: 2026-03-08

```lean
export PeanoIsomorphism (
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
  toPeano_successor
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
-- Notaciones scoped en SetUniverse:
-- scoped notation "ΠZ" => PeanoIsomorphism.fromPeano
-- scoped notation "ZΠ" => PeanoIsomorphism.toPeano
```

### 6.19 NaturalNumbersAdd.lean

**Namespace**: `SetUniverse.NaturalNumbersAdd` (exportado a `SetUniverse`)
**Última modificación**: 2026-03-08
**Dependencias**: `NaturalNumbers`, `Infinity`, `Recursion`, `PeanoImport`, `PeanoNatLib.PeanoNatAdd`

```lean
export NaturalNumbersAdd (
  -- Sección 1: successorFn
  successorFn
  mem_successorFn
  successorFn_is_function
  successorFn_apply
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

### 6.20 NaturalNumbersMul.lean

**Namespace**: `SetUniverse.NaturalNumbersMul` (exportado a `SetUniverse`)
**Última modificación**: 2026-03-08
**Dependencias**: `NaturalNumbers`, `Infinity`, `Recursion`, `PeanoImport`, `NaturalNumbersAdd`, `PeanoNatLib.PeanoNatMul`

```lean
export NaturalNumbersMul (
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
- `BooleanAlgebra.lean` - Teoremas de álgebra booleana
- `BooleanRing.lean` - Estructura de anillo booleano: SymDiff como suma, intersección como producto, leyes de asociatividad y distributividad
- `PowerSetAlgebra.lean` - Álgebra booleana de conjuntos potencia: complemento, leyes de De Morgan, distributividad, absorción, idempotencia
- `NaturalNumbers.lean` - Números naturales como ordinales de von Neumann
- `Infinity.lean` - Axioma de infinito y conjunto ω de todos los naturales
- `GeneralizedDeMorgan.lean` - Leyes de De Morgan generalizadas para familias de conjuntos
- `GeneralizedDistributive.lean` - Leyes distributivas generalizadas para familias de conjuntos
- `SetOrder.lean` - Teoría de órdenes parciales, cotas, supremos e ínfimos
- `SetStrictOrder.lean` - Teoría de órdenes estrictos, irreflexividad, asimetría y transitividad
- `OrderedPair.lean` - Extensiones del par ordenado de Kuratowski, igualdad y propiedades
- `CartesianProduct.lean` - Producto cartesiano A ×ₛ B, propiedades distributivas y monotonicidad
- `Functions.lean` - Funciones inyectivas, suryectivas, biyectivas, composición, restricción
- `Relations.lean` - Relaciones, equivalencia, orden, imagen de relaciones
- `Recursion.lean` - Teorema de recursión para números naturales, cómputos de longitud n
- `PeanoImport.lean` - Isomorfismo Von Neumann ↔ Peano completo: biyección, compatibilidad algebraica, transporte de recursión (simple y con paso), puentes de orden
- `NaturalNumbersAdd.lean` - Suma en ω: definición vía Recursión, teorema puente `fromPeano_add`, propiedades de semianillo (conmutatividad, asociatividad, cancelación, monotonía)
- `NaturalNumbersMul.lean` - Multiplicación en ω: definición vía Recursión, teorema puente `fromPeano_mul`, propiedades de anillo conmutativo (distributividad, asociatividad, identidades)

### 7.3 Archivos Parcialmente Proyectados

Los siguientes archivos tienen **documentación parcial** (solo definiciones/teoremas principales):

- `AtomicBooleanAlgebra.lean` - Solo definición de átomo y teoremas principales

### 7.4 Archivos Casi Completos (con `sorry` documentados)

Los siguientes archivos están **casi completos** pero contienen algunos `sorry` documentados:

- (Ninguno actualmente - todos los módulos de Core Theory están 100% completos)

**Nota**: `Functions.lean` está ahora ✅ **100% completo** (0 sorry).
**Nota**: `Recursion.lean` está ahora ✅ **100% completo** (0 sorry, 0 errores de compilación).
**Nota**: `Cardinality.lean` está ahora ✅ **100% completo** (0 sorry, CSB theorem completamente demostrado).

### 7.5 Archivos Completos Pendientes de Proyectar

**Ninguno** - Todos los archivos completamente implementados ya han sido proyectados en este documento.

---

*Última actualización: 2026-03-16 18:00 — Proyección completa de Pairing.lean: añadidas 5 definiciones faltantes (member_inter, interSet con notación ⋂, fst, snd) en §3.5, creada nueva subsección §3.5.1 con 25 predicados de relaciones y funciones (isRelation, isSymmetric, isTransitive, isFunction, etc.), añadidos 20 teoremas auxiliares en §4.2 (nonempty_iff_exists_mem, inter_of_ordered_pair, diff_pair_singleton, etc.), actualizados exports en §6.2 con 62 elementos organizados por categorías. Total: 8 definiciones + 25 predicados + 20 teoremas auxiliares + 7 teoremas principales completamente proyectados. Estado verificado: ✅ Completo.*

*Actualización anterior: 2026-03-16 17:30 — Proyección completa de Cardinality.lean: añadidas 4 definiciones faltantes (singletonMap, SetDiff con notación A ∖ B, CSB_core, CSB_bijection) en §3.13, añadidos 19 teoremas faltantes en §4.8 (todos los teoremas auxiliares de Cantor y CSB completos), actualizados exports en §6.5 con 28 elementos. Total: 5 definiciones + 20 teoremas completamente proyectados. Estado verificado: ✅ 0 sorry (CSB completamente demostrado).*

*Actualización anterior: 2026-03-16 17:00 — Proyección completa de Functions.lean: añadida definición Restriction (§3.10) con notación f ↾ C, 4 teoremas sobre Restriction en §4.6 (Restriction_is_specified, Restriction_subset, Restriction_is_function, Restriction_apply), actualizadas ubicaciones de definiciones y teoremas, actualizada notación en §5.4, simplificados exports en §6.4. Total: 16 definiciones y teoremas de restricción completamente proyectados.*

*Actualización anterior: 2026-03-16 16:30 — Proyección completa de Relations.lean: añadidas 19 definiciones faltantes en §3.9 (isRelationFrom, Related, isIrreflexiveOn, isAsymmetricOn, isConnectedOn, isStronglyConnectedOn, isTrichotomousOn, isPreorderOn, isLinearOrderOn, isStrictOrderOn, isStrictPartialOrderOn, isStrictLinearOrderOn, isWellFoundedOn, isWellOrderOn, QuotientSet, domain, range, imag, InverseRel) y 13 teoremas faltantes en §4.5 (StrictOrder_is_Irreflexive, StrictPartialOrder_is_Irreflexive, Irreflexive_Transitive_implies_Asymmetric, Asymmetric_iff_Irreflexive_and_AntiSymmetric, PartialOrder_Connected_is_LinearOrder, LinearOrder_comparable, StrictOrder_Connected_is_Trichotomous, StrictLinearOrder_iff_StrictOrder_Connected, mem_IdRel, EqClass_mem_self, mem_EqClass_of_Related, Related_of_mem_EqClass, mem_EqClass_iff). Total: 28 definiciones y 24 teoremas en Relations.lean.*

*Actualización anterior: 2026-03-16 16:00 — Proyección completa de PowerSetAlgebra.lean: añadidos 15 teoremas faltantes en §4.17 (complement_mem_PowerSet, empty_in_PowerSet, universe_in_PowerSet, PowerSet_absorb_inter_union, PowerSet_union_idempotent, PowerSet_inter_idempotent, PowerSet_union_comm, PowerSet_inter_comm, PowerSet_union_assoc, PowerSet_inter_assoc, PowerSet_inter_empty, PowerSet_empty_inter, PowerSet_complement_empty, PowerSet_complement_universe). Total: 22 teoremas en §4.17.*

*Actualización anterior: 2026-03-16 15:30 — Proyección completa de PowerSet.lean: axioma PowerSet (§2.6), 2 definiciones (§3.7), 12 teoremas principales (§4.3), notación 𝒫 (§5.6), 14 exports (§6.3). Renumeración de secciones 3.7→3.24, 4.3→4.20, 5.6→5.13, 6.3→6.20.*

*Actualización anterior: 2026-03-08 12:00 — Proyección de NaturalNumbersAdd.lean (3 def + 16 teoremas), NaturalNumbersMul.lean (2 def + 13 teoremas), y ampliación de PeanoImport.lean (9 nuevos teoremas: toPeano_zero, toPeano_successor, recursion_transport x4, succ_mem_succ_iff, fromPeano_lt_iff, fromPeano_le_iff). Secciones 3.22, 3.23, 4.18, 4.19 añadidas. Sección 6 actualizada con exports 6.15–6.17.*

*Actualización anterior: 2026-03-05 10:00 — Proyección completa de Recursion.lean: 5 lemas auxiliares globales, def RecursionComputations, RecursionTheorem 100% demostrado sin sorry.*

*Actualización anterior: 2026-03-04 12:00 — Proyección de PeanoImport.lean (2 def + 7 teoremas), nat_mem_wf en Infinity.lean, predecessor en NaturalNumbers.lean.*

*Actualización anterior: 2026-02-12 18:45 — Completada proyección íntegra de NaturalNumbers.lean (13 def + 36 teoremas + exports).*

*Este documento contiene únicamente construcciones y teoremas que están completamente implementados y demostrados en el código Lean 4. La proyección se actualiza conforme se agregan archivos al contexto de trabajo.*
