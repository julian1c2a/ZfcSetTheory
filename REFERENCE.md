# Referencia Técnica - ZfcSetTheory

*Última actualización: 11 de febrero de 2026*

## 1. Arquitectura del Proyecto

### 1.1 Módulos y Dependencias

| Archivo | Namespace | Dependencias | Estado Proyección |
|---------|-----------|--------------|-------------------|
| `Prelim.lean` | - | `Init.Classical` | ✅ Completo |
| `Extension.lean` | `SetUniverse.ExtensionAxiom` | `Prelim` | ✅ Completo |
| `Existence.lean` | `SetUniverse.ExistenceAxiom` | `Prelim`, `Extension` | ✅ Completo |
| `Specification.lean` | `SetUniverse.SpecificationAxiom` | `Prelim`, `Extension`, `Existence` | ✅ Completo |
| `Pairing.lean` | `SetUniverse.PairingAxiom` | `Prelim`, `Extension`, `Existence`, `Specification` | ✅ Completo |
| `Union.lean` | `SetUniverse.UnionAxiom` | `Prelim`, `Extension`, `Existence`, `Specification`, `Pairing` | ✅ Completo |
| `PowerSet.lean` | `SetUniverse.PowerSetAxiom` | `Prelim`, `Extension`, `Existence`, `Specification`, `Pairing`, `Union` | ✅ Completo |
| `PowerSetAlgebra.lean` | `SetUniverse.PowerSetAlgebra` | `PowerSet`, `BooleanAlgebra` + anteriores | ✅ Completo |
| `OrderedPair.lean` | `SetUniverse.OrderedPairExtensions` | Todos los anteriores + `PowerSet` | 🔶 Parcial |
| `CartesianProduct.lean` | `SetUniverse.CartesianProduct` | `OrderedPair` + anteriores | 🔶 Parcial |
| `Relations.lean` | `SetUniverse.Relations` | `CartesianProduct` + anteriores | ✅ Completo |
| `Functions.lean` | `SetUniverse.Functions` | `CartesianProduct`, `Relations` + anteriores | 🔶 Parcial |
| `BooleanAlgebra.lean` | `SetUniverse.BooleanAlgebra` | `Union`, `Specification`, `Pairing`, `Extension`, `Existence`, `Prelim` | ✅ Completo |
| `AtomicBooleanAlgebra.lean` | `SetUniverse.AtomicBooleanAlgebra` | `PowerSetAlgebra`, `SetOrder`, `SetStrictOrder` + anteriores | 🔶 Parcial |
| `Cardinality.lean` | `SetUniverse.Cardinality` | `Functions` + todos los anteriores | 🔶 Parcial |
| `NaturalNumbers.lean` | `SetUniverse.NaturalNumbers` | `Cardinality` + todos los anteriores | ❌ No proyectado |
| `Infinity.lean` | `SetUniverse.InfinityAxiom` | `NaturalNumbers` + todos los anteriores | ❌ No proyectado |
| `GeneralizedDeMorgan.lean` | `SetUniverse.GeneralizedDeMorgan` | `PowerSetAlgebra` + anteriores | ❌ No proyectado |
| `GeneralizedDistributive.lean` | `SetUniverse.GeneralizedDistributive` | `PowerSetAlgebra` + anteriores | ❌ No proyectado |
| `SetOrder.lean` | `SetUniverse.SetOrder` | `Relations` + anteriores | ❌ No proyectado |
| `SetStrictOrder.lean` | `SetUniverse.SetStrictOrder` | `SetOrder` + anteriores | ❌ No proyectado |
| `Recursion.lean` | `SetUniverse.Recursion` | `NaturalNumbers` + anteriores | ❌ No proyectado |

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

#### Par Ordenado (OrderedPair)

**Ubicación**: `Pairing.lean`, línea 95  
**Orden**: 3ª definición principal

**Enunciado Matemático**: El par ordenado de Kuratowski ⟨a,b⟩ = {{a}, {a,b}}.

**Firma Lean4**:

```lean
@[simp] noncomputable def OrderedPair (x y : U) : U
    := (({ (({ x }): U) , (({ x , y }): U) }): U)
notation " ⟨ " x " , " y " ⟩ " => OrderedPair x y
```

**Dependencias**: `PairSet`, `Singleton`

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

### 3.7 CartesianProduct.lean

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

### 3.8 Relations.lean

#### Relación en un Conjunto (isRelationOn)

**Ubicación**: `Relations.lean`, línea 44  
**Orden**: 1ª definición principal

**Enunciado Matemático**: R es una relación en A si R ⊆ A × A.

**Firma Lean4**:

```lean
def isRelationOn (R A : U) : Prop := R ⊆ (A ×ₛ A)
```

**Dependencias**: `subseteq`, `CartesianProduct`

#### Reflexividad (isReflexiveOn)

**Ubicación**: `Relations.lean`, línea 53  
**Orden**: 2ª definición principal

**Enunciado Matemático**: R es reflexiva en A si ∀x ∈ A, (x,x) ∈ R.

**Firma Lean4**:

```lean
def isReflexiveOn (R A : U) : Prop :=
  ∀ x : U, x ∈ A → ⟨x, x⟩ ∈ R
```

**Dependencias**: `OrderedPair`

#### Simetría (isSymmetricOn)

**Ubicación**: `Relations.lean`, línea 61  
**Orden**: 3ª definición principal

**Enunciado Matemático**: R es simétrica en A si ∀x,y ∈ A, (x,y) ∈ R → (y,x) ∈ R.

**Firma Lean4**:

```lean
def isSymmetricOn (R A : U) : Prop :=
  ∀ x y : U, x ∈ A → y ∈ A → ⟨x, y⟩ ∈ R → ⟨y, x⟩ ∈ R
```

**Dependencias**: `OrderedPair`

#### Antisimetría (isAntiSymmetricOn)

**Ubicación**: `Relations.lean`, línea 65  
**Orden**: 4ª definición principal

**Enunciado Matemático**: R es antisimétrica en A si ∀x,y ∈ A, (x,y) ∈ R ∧ (y,x) ∈ R → x = y.

**Firma Lean4**:

```lean
def isAntiSymmetricOn (R A : U) : Prop :=
  ∀ x y : U, x ∈ A → y ∈ A → ⟨x, y⟩ ∈ R → ⟨y, x⟩ ∈ R → x = y
```

**Dependencias**: `OrderedPair`

#### Transitividad (isTransitiveOn)

**Ubicación**: `Relations.lean`, línea 73  
**Orden**: 5ª definición principal

**Enunciado Matemático**: R es transitiva en A si ∀x,y,z ∈ A, (x,y) ∈ R ∧ (y,z) ∈ R → (x,z) ∈ R.

**Firma Lean4**:

```lean
def isTransitiveOn (R A : U) : Prop :=
  ∀ x y z : U, x ∈ A → y ∈ A → z ∈ A → ⟨x, y⟩ ∈ R → ⟨y, z⟩ ∈ R → ⟨x, z⟩ ∈ R
```

**Dependencias**: `OrderedPair`

#### Relación de Equivalencia (isEquivalenceOn)

**Ubicación**: `Relations.lean`, línea 89  
**Orden**: 6ª definición principal

**Enunciado Matemático**: R es relación de equivalencia en A si es reflexiva, simétrica y transitiva.

**Firma Lean4**:

```lean
def isEquivalenceOn (R A : U) : Prop :=
  isRelationOn R A ∧ isReflexiveOn R A ∧ isSymmetricOn R A ∧ isTransitiveOn R A
```

**Dependencias**: `isRelationOn`, `isReflexiveOn`, `isSymmetricOn`, `isTransitiveOn`

#### Orden Parcial (isPartialOrderOn)

**Ubicación**: `Relations.lean`, línea 97  
**Orden**: 7ª definición principal

**Enunciado Matemático**: R es orden parcial en A si es reflexiva, antisimétrica y transitiva.

**Firma Lean4**:

```lean
def isPartialOrderOn (R A : U) : Prop :=
  isRelationOn R A ∧ isReflexiveOn R A ∧ isAntiSymmetricOn R A ∧ isTransitiveOn R A
```

**Dependencias**: `isRelationOn`, `isReflexiveOn`, `isAntiSymmetricOn`, `isTransitiveOn`

#### Clase de Equivalencia (EqClass)

**Ubicación**: `Relations.lean`, línea 125  
**Orden**: 8ª definición principal

**Enunciado Matemático**: La clase de equivalencia de a bajo R en A: {x ∈ A | (a,x) ∈ R}.

**Firma Lean4**:

```lean
noncomputable def EqClass (a R A : U) : U :=
  SpecSet A (fun x => ⟨a, x⟩ ∈ R)
```

**Dependencias**: `SpecSet`, `OrderedPair`

#### Relación Identidad (IdRel)

**Ubicación**: `Relations.lean`, línea 133  
**Orden**: 9ª definición principal

**Enunciado Matemático**: La relación identidad en A: {(x,x) | x ∈ A}.

**Firma Lean4**:

```lean
noncomputable def IdRel (A : U) : U :=
  SpecSet (A ×ₛ A) (fun p => fst p = snd p)
```

**Dependencias**: `SpecSet`, `CartesianProduct`, `fst`, `snd`

### 3.9 Functions.lean

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

#### Aplicación de Función (apply)

**Ubicación**: `Functions.lean`, línea 58  
**Orden**: 2ª definición principal

**Enunciado Matemático**: f⦅x⦆ es el único y tal que ⟨x,y⟩ ∈ f.

**Firma Lean4**:

```lean
noncomputable def apply (f x : U) : U :=
  if h : ∃ y, ⟨x, y⟩ ∈ f then Classical.choose h else ∅
notation:max f "⦅" x "⦆" => apply f x
```

**Dependencias**: `Classical.choose`, `EmptySet`

#### Equipotencia (isEquipotent)

**Ubicación**: `Functions.lean`, línea 398  
**Orden**: 5ª definición principal

**Enunciado Matemático**: A y B son equipotentes si existe una biyección entre ellos.

**Firma Lean4**:

```lean
def isEquipotent (A B : U) : Prop := ∃ f, isBijection f A B
notation:50 A " ≃ₛ " B => isEquipotent A B
```

**Dependencias**: `isBijection`

### 3.9 BooleanAlgebra.lean

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

### 3.11 AtomicBooleanAlgebra.lean

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

### 3.12 Cardinality.lean

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

#### Corrección de fst

**Ubicación**: `Pairing.lean`, línea 286  
**Orden**: 1º teorema principal

**Enunciado Matemático**: La primera proyección de un par ordenado es el primer elemento.

**Firma Lean4**:

```lean
@[simp] theorem fst_of_ordered_pair (x y : U) : fst (⟨x, y⟩ : U) = x
```

**Dependencias**: `fst`, `OrderedPair`, `inter_of_ordered_pair`

#### Corrección de snd

**Ubicación**: `Pairing.lean`, línea 325  
**Orden**: 2º teorema principal

**Enunciado Matemático**: La segunda proyección de un par ordenado es el segundo elemento.

**Firma Lean4**:

```lean
@[simp] theorem snd_of_ordered_pair (x y : U) : snd ⟨x, y⟩ = y
```

**Dependencias**: `snd`, `OrderedPair`, múltiples lemas auxiliares

### 4.3 CartesianProduct.lean

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

### 4.4 Relations.lean

#### La Asimetría Implica Irreflexividad

**Ubicación**: `Relations.lean`, línea 142  
**Orden**: 1º teorema principal

**Enunciado Matemático**: Si R es asimétrica en A, entonces R es irreflexiva en A.

**Firma Lean4**:

```lean
theorem Asymmetric_implies_Irreflexive (R A : U) :
    isAsymmetricOn R A → isIrreflexiveOn R A
```

**Dependencias**: `isAsymmetricOn`, `isIrreflexiveOn`

#### La Relación Identidad es de Equivalencia

**Ubicación**: `Relations.lean`, línea 200  
**Orden**: 2º teorema principal

**Enunciado Matemático**: La relación identidad IdRel A es una relación de equivalencia en A.

**Firma Lean4**:

```lean
theorem IdRel_is_Equivalence (A : U) :
    isEquivalenceOn (IdRel A) A
```

**Dependencias**: `IdRel`, `isEquivalenceOn`, `mem_IdRel`

#### Pertenencia en Clase de Equivalencia

**Ubicación**: `Relations.lean`, línea 225  
**Orden**: 3º teorema principal

**Enunciado Matemático**: x ∈ EqClass a R A ↔ x ∈ A ∧ ⟨a,x⟩ ∈ R.

**Firma Lean4**:

```lean
theorem mem_EqClass (a R A x : U) :
    x ∈ EqClass a R A ↔ x ∈ A ∧ ⟨a, x⟩ ∈ R
```

**Dependencias**: `EqClass`, `SpecSet_is_specified`

#### Igualdad de Clases de Equivalencia

**Ubicación**: `Relations.lean`, línea 270  
**Orden**: 4º teorema principal

**Enunciado Matemático**: Para relaciones de equivalencia, EqClass a R A = EqClass b R A ↔ ⟨a,b⟩ ∈ R.

**Firma Lean4**:

```lean
theorem EqClass_eq_iff (R A a b : U)
    (hEq : isEquivalenceOn R A) (haA : a ∈ A) (hbA : b ∈ A) :
    EqClass a R A = EqClass b R A ↔ ⟨a, b⟩ ∈ R
```

**Dependencias**: `EqClass`, `isEquivalenceOn`, `ExtSet`

#### Las Clases de Equivalencia Particionan el Conjunto

**Ubicación**: `Relations.lean`, línea 300  
**Orden**: 5º teorema principal

**Enunciado Matemático**: Las clases de equivalencia son iguales o disjuntas.

**Firma Lean4**:

```lean
theorem EqClass_eq_or_disjoint (R A a b : U)
    (hEq : isEquivalenceOn R A) (haA : a ∈ A) (hbA : b ∈ A) :
    EqClass a R A = EqClass b R A ∨ BinInter (EqClass a R A) (EqClass b R A) = ∅
```

**Dependencias**: `EqClass`, `isEquivalenceOn`, `BinInter`, `EmptySet`

### 4.5 Functions.lean

#### Teorema de Cantor-Schröder-Bernstein

**Ubicación**: `Functions.lean`, línea 580  
**Orden**: Teorema principal

**Enunciado Matemático**: Si A ≼ B y B ≼ A, entonces A ≃ B.

**Firma Lean4**:

```lean
theorem cantor_schroeder_bernstein (A B : U)
    (hab : isDominatedBy A B) (hba : isDominatedBy B A) :
    isEquipotent A B
```

**Dependencias**: `isDominatedBy`, `isEquipotent`, `CSB_bijection`

### 4.6 AtomicBooleanAlgebra.lean

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

### 4.7 Cardinality.lean

#### Teorema de Cantor

**Ubicación**: `Cardinality.lean`, línea 65  
**Orden**: 1º teorema principal

**Enunciado Matemático**: No existe suryección de A a 𝒫(A).

**Firma Lean4**:

```lean
theorem cantor_no_surjection (f A : U) (hf : isFunctionFromTo f A (𝒫 A)) :
  ¬isSurjectiveOnto f (𝒫 A)
```

**Dependencias**: `DiagonalSet`, `isFunctionFromTo`, `isSurjectiveOnto`

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
- `g ∘ₛ f` - Composición (`FunctionComposition`)
- `A ≃ₛ B` - Equipotencia (`isEquipotent`)
- `A ≼ₛ B` - Dominación (`isDominatedBy`)

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
    mem_IdRel IdRel_is_Equivalence mem_EqClass
    EqClass_eq_iff EqClass_eq_or_disjoint
)
```

### 6.3 Functions.lean

```lean
export Functions (
  isSingleValued isFunctionFromTo Dom Ran apply
  IdFunction FunctionComposition InverseFunction
  isInjective isSurjectiveOnto isBijection
  isEquipotent isDominatedBy isStrictlyDominatedBy
  equipotent_refl equipotent_symm equipotent_trans
  dominated_refl dominated_trans
  bijection_iff_invertible cantor_schroeder_bernstein
)
```

### 6.4 Cardinality.lean

```lean
export Cardinality (
  DiagonalSet singletonMap
  cantor_no_surjection cantor_strict_dominance cantor_not_equipotent
  A_dominated_by_PowerSet PowerSet_not_dominated_by_A
  CSB_bijection cantor_schroeder_bernstein dominated_antisymm
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
- `PowerSetAlgebra.lean` - Complementos y De Morgan
- `Relations.lean` - Relaciones binarias y equivalencia
- `BooleanAlgebra.lean` - Teoremas de álgebra booleana

### 7.3 Archivos Parcialmente Proyectados

Los siguientes archivos tienen **documentación parcial** (solo definiciones/teoremas principales):

- `OrderedPair.lean` - Solo proyecciones fst/snd y igualdad de pares
- `CartesianProduct.lean` - Solo definición principal y caracterización
- `Functions.lean` - Solo definiciones básicas y Cantor-Schröder-Bernstein
- `AtomicBooleanAlgebra.lean` - Solo definición de átomo y teoremas principales
- `Cardinality.lean` - Solo conjunto diagonal y teorema de Cantor

### 7.4 Archivos No Proyectados

Los siguientes archivos **no están documentados** en este REFERENCE.md:

- `NaturalNumbers.lean` - Números naturales y inducción
- `Infinity.lean` - Axioma de infinito y conjunto ω
- `GeneralizedDeMorgan.lean` - De Morgan para familias
- `GeneralizedDistributive.lean` - Distributividad para familias
- `SetOrder.lean` - Órdenes parciales y retículos
- `SetStrictOrder.lean` - Órdenes estrictos
- `Recursion.lean` - Definiciones recursivas

---

*Este documento contiene únicamente construcciones y teoremas que están completamente implementados y demostrados en el código Lean 4. La proyección se actualiza conforme se agregan archivos al contexto de trabajo.*
