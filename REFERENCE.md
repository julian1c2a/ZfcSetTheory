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
| `OrderedPair.lean` | `SetUniverse.OrderedPairExtensions` | Todos los anteriores + `PowerSet` | ✅ Completo |
| `CartesianProduct.lean` | `SetUniverse.CartesianProduct` | `OrderedPair` + anteriores | ✅ Completo |
| `Relations.lean` | `SetUniverse.Relations` | `CartesianProduct` + anteriores | ✅ Completo |
| `Functions.lean` | `SetUniverse.Functions` | `CartesianProduct`, `Relations` + anteriores | 🔶 Parcial |
| `BooleanAlgebra.lean` | `SetUniverse.BooleanAlgebra` | `Union`, `Specification`, `Pairing`, `Extension`, `Existence`, `Prelim` | ✅ Completo |
| `AtomicBooleanAlgebra.lean` | `SetUniverse.AtomicBooleanAlgebra` | `PowerSetAlgebra`, `SetOrder`, `SetStrictOrder` + anteriores | 🔶 Parcial |
| `Cardinality.lean` | `SetUniverse.Cardinality` | `Functions` + todos los anteriores | 🔶 Parcial |
| `NaturalNumbers.lean` | `SetUniverse.NaturalNumbers` | `Cardinality` + todos los anteriores | ✅ Completo |
| `Infinity.lean` | `SetUniverse.InfinityAxiom` | `NaturalNumbers` + todos los anteriores | ✅ Completo |
| `GeneralizedDeMorgan.lean` | `SetUniverse.GeneralizedDeMorgan` | `PowerSetAlgebra` + anteriores | ✅ Completo |
| `GeneralizedDistributive.lean` | `SetUniverse.GeneralizedDistributive` | `PowerSetAlgebra` + anteriores | ✅ Completo |
| `SetOrder.lean` | `SetUniverse.SetOrder` | `Relations` + anteriores | ✅ Completo |
| `SetStrictOrder.lean` | `SetUniverse.SetStrictOrder` | `SetOrder` + anteriores | ✅ Completo |
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

### 2.6 Axioma de Infinito

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

### 3.13 NaturalNumbers.lean

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

### 3.14 Infinity.lean

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

### 3.15 GeneralizedDeMorgan.lean

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

### 3.16 GeneralizedDistributive.lean

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

### 3.17 SetOrder.lean

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

### 3.18 SetStrictOrder.lean

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

### 3.19 OrderedPair.lean (Extensiones)

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

### 4.8 NaturalNumbers.lean

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

### 4.9 Infinity.lean

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

### 4.10 GeneralizedDeMorgan.lean

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

### 4.11 GeneralizedDistributive.lean

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

### 4.12 SetOrder.lean

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

### 4.13 SetStrictOrder.lean

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

### 4.14 OrderedPair.lean (Extensiones)

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

### 5.5 Números Naturales

- `σ n` - Función sucesor (`successor`)
- `∈[S]` - Orden estricto guiado por membresía (`StrictOrderMembershipGuided`)
- `0`, `1`, `2`, `3` - Naturales específicos (`zero`, `one`, `two`, `three`)

### 5.6 Infinito

- `ω` - Conjunto de todos los números naturales (`Omega`)

### 5.7 De Morgan Generalizado

- `A \\ᶠ F` - Familia de complementos (`ComplementFamily`)

### 5.8 Distributividad Generalizada

- `⋂ F` - Intersección generalizada (`GeneralizedIntersection`)
- `X ∩ᶠ F` - Familia de intersecciones (`IntersectionImageFamily`)
- `X ∪ᶠ F` - Familia de uniones (`UnionImageFamily`)

### 5.9 Órdenes Parciales

- Conceptos de orden: cotas superiores/inferiores, supremo/ínfimo
- Propiedades de orden: reflexividad, transitividad, antisimetría
- Monotonicidad de operaciones de conjuntos

### 5.10 Órdenes Estrictos

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

### 6.5 NaturalNumbers.lean

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

### 6.6 Infinity.lean

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

### 6.7 GeneralizedDeMorgan.lean

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

### 6.8 GeneralizedDistributive.lean

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

### 6.9 SetOrder.lean

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

### 6.10 SetStrictOrder.lean

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

### 6.11 OrderedPair.lean (Extensiones)

```lean
export OrderedPairExtensions (
  OrderedPair_eq_of
  OrderedPair_eq_iff
  OrderedPair_in_PowerSet
)
```

### 6.12 CartesianProduct.lean

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
- `NaturalNumbers.lean` - Números naturales como ordinales de von Neumann
- `Infinity.lean` - Axioma de infinito y conjunto ω de todos los naturales
- `GeneralizedDeMorgan.lean` - Leyes de De Morgan generalizadas para familias de conjuntos
- `GeneralizedDistributive.lean` - Leyes distributivas generalizadas para familias de conjuntos
- `SetOrder.lean` - Teoría de órdenes parciales, cotas, supremos e ínfimos
- `SetStrictOrder.lean` - Teoría de órdenes estrictos, irreflexividad, asimetría y transitividad
- `OrderedPair.lean` - Extensiones del par ordenado de Kuratowski, igualdad y propiedades
- `CartesianProduct.lean` - Producto cartesiano A ×ₛ B, propiedades distributivas y monotonicidad

### 7.3 Archivos Parcialmente Proyectados

Los siguientes archivos tienen **documentación parcial** (solo definiciones/teoremas principales):

- `Functions.lean` - Solo definiciones básicas y Cantor-Schröder-Bernstein
- `AtomicBooleanAlgebra.lean` - Solo definición de átomo y teoremas principales
- `Cardinality.lean` - Solo conjunto diagonal y teorema de Cantor

### 7.4 Archivos No Proyectados

Los siguientes archivos **no están documentados** en este REFERENCE.md:

- `Recursion.lean` - Definiciones recursivas

---

*Última actualización: 11 de febrero de 2026 - Completado módulo CartesianProduct.lean*

*Este documento contiene únicamente construcciones y teoremas que están completamente implementados y demostrados en el código Lean 4. La proyección se actualiza conforme se agregan archivos al contexto de trabajo.*
