# Referencia Técnica - ZfcSetTheory

*Última actualización: 11 de febrero de 2026*

## 1. Arquitectura del Proyecto

### 1.1 Módulos y Dependencias

| Archivo | Namespace | Dependencias | Estado |
|---------|-----------|--------------|--------|
| `Prelim.lean` | - | `Init.Classical` | ✅ |
| `Extension.lean` | `SetUniverse.ExtensionAxiom` | `Prelim` | ✅ |
| `Existence.lean` | `SetUniverse.ExistenceAxiom` | `Prelim`, `Extension` | ✅ |
| `Specification.lean` | `SetUniverse.SpecificationAxiom` | `Prelim`, `Extension`, `Existence` | ✅ |
| `Pairing.lean` | `SetUniverse.PairingAxiom` | `Prelim`, `Extension`, `Existence`, `Specification` | ✅ |
| `Union.lean` | `SetUniverse.UnionAxiom` | `Prelim`, `Extension`, `Existence`, `Specification`, `Pairing` | ✅ |
| `OrderedPair.lean` | `SetUniverse.OrderedPairExtensions` | Todos los anteriores + `PowerSet` | ✅ |
| `CartesianProduct.lean` | `SetUniverse.CartesianProduct` | `OrderedPair` + anteriores | ✅ |
| `Relations.lean` | `SetUniverse.Relations` | `CartesianProduct` + anteriores | ✅ |
| `Functions.lean` | `SetUniverse.Functions` | `CartesianProduct`, `Relations` + anteriores | ✅ |
| `BooleanAlgebra.lean` | `SetUniverse.BooleanAlgebra` | `Union`, `Specification`, `Pairing`, `Extension`, `Existence`, `Prelim` | ✅ |
| `AtomicBooleanAlgebra.lean` | `SetUniverse.AtomicBooleanAlgebra` | `PowerSetAlgebra`, `SetOrder`, `SetStrictOrder` + anteriores | ✅ |
| `Cardinality.lean` | `SetUniverse.Cardinality` | `Functions` + todos los anteriores | ✅ |

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

### 3.8 Functions.lean

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

### 3.10 AtomicBooleanAlgebra.lean

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

### 3.11 Cardinality.lean

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

### 4.4 Functions.lean

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

### 4.5 AtomicBooleanAlgebra.lean

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

### 4.6 Cardinality.lean

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

### 6.2 Functions.lean
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

### 6.3 Cardinality.lean
```lean
export Cardinality (
  DiagonalSet singletonMap
  cantor_no_surjection cantor_strict_dominance cantor_not_equipotent
  A_dominated_by_PowerSet PowerSet_not_dominated_by_A
  CSB_bijection cantor_schroeder_bernstein dominated_antisymm
)
```

---

*Este documento contiene únicamente construcciones y teoremas que están completamente implementados y demostrados en el código Lean 4.*
