# Resumen de Axiomas, Definiciones y Teoremas - ZfcSetTheory

Este documento presenta un resumen completo de todos los axiomas, definiciones y teoremas del proyecto ZfcSetTheory, organizado por módulos.

## Tabla de Contenidos

1. [Prelim - Preliminares](#prelim)
2. [Extension - Axioma de Extensionalidad](#extension)
3. [Existence - Axioma de Existencia](#existence)
4. [Specification - Axioma de Especificación](#specification)
5. [Pairing - Axioma de Emparejamiento](#pairing)
6. [Union - Axioma de Unión](#union)
7. [PowerSet - Axioma del Conjunto Potencia](#powerset)
8. [OrderedPair - Par Ordenado](#orderedpair)
9. [CartesianProduct - Producto Cartesiano](#cartesianproduct)
10. [Relations - Relaciones](#relations)
11. [Functions - Funciones](#functions)
12. [SetOrder - Orden de Conjuntos](#setorder)
13. [SetStrictOrder - Orden Estricto](#setstrictorder)
14. [PowerSetAlgebra - Álgebra del Conjunto Potencia](#powersetalgebra)
15. [BooleanAlgebra - Álgebra Booleana](#booleanalgebra)
16. [BooleanRing - Anillo Booleano](#booleanring)
17. [AtomicBooleanAlgebra - Álgebra Booleana Atómica](#atomicbooleanalgebra)
18. [GeneralizedDistributive - Distributividad Generalizada](#generalizeddistributive)
19. [GeneralizedDeMorgan - Leyes de De Morgan Generalizadas](#generalizeddemorgan)
20. [NaturalNumbers - Números Naturales](#naturalnumbers)
21. [Cardinality - Cardinalidad](#cardinality)

---

## Prelim

**Namespace**: Raíz (sin namespace específico)

**Descripción**: Contiene definiciones y teoremas preliminares sobre existencia única.

### Definiciones

#### `ExistsUnique {α : Sort u} (p : α → Prop) : Prop`

```lean
∃! x, p x := ∃ x, p x ∧ ∀ y, p y → y = x
```

**Explicación**: Define en qué consiste la existencia única de un elemento que satisface un predicado p. Exige que exista al menos un elemento y que todos los elementos que satisfacen el predicado sean iguales al primero (y por lo tanto entre sí).

#### `ExistsUnique.choose {α : Sort u} {p : α → Prop} (h : ExistsUnique p) : α`

```lean
choose h := Classical.choose (ExistsUnique.exists h)
```

**Explicación**: Selector clásico que extrae el único testigo de una prueba de existencia única.

### Teoremas

#### `ExistsUnique.intro {α : Sort u} {p : α → Prop} (w : α) (hw : p w) (huniq : ∀ y, p y → y = w)`

```lean
ExistsUnique p
```

**Explicación**: Constructor de existencia única: dado un testigo w que satisface p y prueba de que es el único, construye una prueba de existencia única.

#### `ExistsUnique.exists {α : Sort u} {p : α → Prop} (h : ExistsUnique p)`

```lean
∃ x, p x
```

**Explicación**: De la existencia única se puede extraer existencia simple.

#### `ExistsUnique.choose_spec {α : Sort u} {p : α → Prop} (h : ExistsUnique p)`

```lean
p (ExistsUnique.choose h)
```

**Explicación**: El elemento elegido por choose satisface el predicado.

---

## Extension

**Namespace**: `SetUniverse.ExtensionAxiom`

**Descripción**: Define el Axioma de Extensionalidad (dos conjuntos son iguales si tienen los mismos elementos) y conceptos derivados como subconjunto, subconjunto propio, y disyunción.

### Axioma Primitivo

#### `mem (x y : U) : Prop`

```lean
axiom mem : U → U → Prop
```

**Explicación**: Relación primitiva de pertenencia entre conjuntos. Se denota x ∈ y.

### Axiomas

#### `ExtSet (x y : U)`

```lean
(∀ z : U, z ∈ x ↔ z ∈ y) → (x = y)
```

**Explicación**: Axioma de Extensionalidad: dos conjuntos son iguales si y solo si tienen exactamente los mismos elementos.

### Definiciones

#### `subseteq (x y : U) : Prop`

```lean
x ⊆ y := ∀ z, z ∈ x → z ∈ y
```

**Explicación**: Relación de subconjunto: x es subconjunto de y si todos los elementos de x están en y.

#### `subset (x y : U) : Prop`

```lean
x ⊂ y := x ⊆ y ∧ x ≠ y
```

**Explicación**: Relación de subconjunto propio: x es subconjunto propio de y si es subconjunto pero no igual.

#### `disjoint (x y : U) : Prop`

```lean
x ⟂ y := ∀ z, z ∈ x → z ∉ y
```

**Explicación**: Dos conjuntos son disjuntos si no comparten ningún elemento.

#### `isTransitiveSet (x : U) : Prop`

```lean
∀ y, y ∈ x → y ⊆ x
```

**Explicación**: Un conjunto es transitivo si cada uno de sus elementos es también un subconjunto de él.

#### `isEmpty (x : U) : Prop`

```lean
∀ y, y ∉ x
```

**Explicación**: Un conjunto es vacío si no contiene ningún elemento.

#### `isNonEmpty (x : U) : Prop`

```lean
∃ y, y ∈ x
```

**Explicación**: Un conjunto es no vacío si existe al menos un elemento en él.

#### `isSingleton (x : U) : Prop`

```lean
∃! y, y ∈ x
```

**Explicación**: Un conjunto es singleton si contiene exactamente un elemento.

#### `isPair (x : U) : Prop`

```lean
∃ y z, y ≠ z ∧ (∀ w, w ∈ x ↔ w = y ∨ w = z)
```

**Explicación**: Un conjunto es un par si contiene exactamente dos elementos distintos.

#### `isBinInter (x y s : U) : Prop`

```lean
∀ z, z ∈ s ↔ z ∈ x ∧ z ∈ y
```

**Explicación**: s es la intersección binaria de x e y.

#### `isBinUnion (x y s : U) : Prop`

```lean
∀ z, z ∈ s ↔ z ∈ x ∨ z ∈ y
```

**Explicación**: s es la unión binaria de x e y.

#### `isBinDiff (x y s : U) : Prop`

```lean
∀ z, z ∈ s ↔ z ∈ x ∧ z ∉ y
```

**Explicación**: s es la diferencia de x menos y.

#### `isBinSymDiff (x y s : U) : Prop`

```lean
∀ z, z ∈ s ↔ (z ∈ x ∧ z ∉ y) ∨ (z ∈ y ∧ z ∉ x)
```

**Explicación**: s es la diferencia simétrica de x e y.

#### `isUnion (x X : U) : Prop`

```lean
∀ z, z ∈ x ↔ ∃ y ∈ X, z ∈ y
```

**Explicación**: x es la unión de la familia de conjuntos X.

#### `isinter (x X : U) : Prop`

```lean
∀ z, z ∈ x ↔ ∀ y ∈ X, z ∈ y
```

**Explicación**: x es la intersección de la familia de conjuntos X.

### Teoremas

#### `ExtSetReverse (x y : U)`

```lean
x = y → (∀ z : U, z ∈ x ↔ z ∈ y)
```

**Explicación**: Recíproca del axioma de extensionalidad: si dos conjuntos son iguales, tienen los mismos elementos.

#### `ExtSet_wc {x y : U} (h : ∀ z : U, z ∈ x ↔ z ∈ y)`

```lean
x = y
```

**Explicación**: Versión con contexto del axioma de extensionalidad.

#### `EqualityOfSubset (x y : U)`

```lean
(x ⊆ y ∧ y ⊆ x) → x = y
```

**Explicación**: Dos conjuntos que se contienen mutuamente son iguales. Antisimetría de la inclusión.

#### `subseteq_reflexive`

```lean
∀ x : U, x ⊆ x
```

**Explicación**: La relación de subconjunto es reflexiva.

#### `subseteq_transitive`

```lean
∀ x y z : U, x ⊆ y → y ⊆ z → x ⊆ z
```

**Explicación**: La relación de subconjunto es transitiva.

#### `subseteq_antisymmetric`

```lean
∀ x y : U, x ⊆ y → y ⊆ x → x = y
```

**Explicación**: La relación de subconjunto es antisimétrica.

#### `subset_asymmetric`

```lean
∀ x y : U, x ⊂ y → ¬(y ⊂ x)
```

**Explicación**: La relación de subconjunto propio es asimétrica.

#### `subset_irreflexive`

```lean
∀ x : U, ¬(x ⊂ x)
```

**Explicación**: La relación de subconjunto propio es irreflexiva.

#### `subset_transitive`

```lean
∀ x y z : U, x ⊂ y → y ⊂ z → x ⊂ z
```

**Explicación**: La relación de subconjunto propio es transitiva.

#### `disjoint_symm (x y : U)`

```lean
x ⟂ y → y ⟂ x
```

**Explicación**: La disyunción es simétrica.

#### `disjoint_is_empty (x y : U)`

```lean
x ⟂ y → (∀ z, z ∈ x → z ∉ y)
```

**Explicación**: Si dos conjuntos son disjuntos, ningún elemento de uno está en el otro.

#### `disjoint_is_empty_wc {x y : U} (h_exists : ∃ z : U, z ∈ x ∧ z ∈ y)`

```lean
¬(x ⟂ y)
```

**Explicación**: Si existe un elemento común, los conjuntos no son disjuntos.

---

## Existence

**Namespace**: `SetUniverse.ExistenceAxiom`

**Descripción**: Axioma de Existencia (del conjunto vacío) y sus consecuencias.

### Axiomas

#### `ExistsAnEmptySet`

```lean
∃ (x : U), ∀ (y : U), y ∉ x
```

**Explicación**: Axioma de existencia: existe un conjunto que no contiene ningún elemento (el conjunto vacío).

### Definiciones

#### `EmptySet : U`

```lean
EmptySet := Classical.choose ExistsAnEmptySet
```

**Explicación**: El conjunto vacío, denotado ∅, definido como el único conjunto sin elementos.

### Teoremas

#### `ExistsUniqueEmptySet`

```lean
∃! (x : U), ∀ (y : U), y ∉ x
```

**Explicación**: El conjunto vacío es único (existencia única).

#### `EmptySet_is_empty`

```lean
∀ (y : U), y ∉ EmptySet
```

**Explicación**: Ningún elemento pertenece al conjunto vacío.

#### `EmptySet_unique`

```lean
∀ (x : U), (∀ (y : U), y ∉ x) → (x = EmptySet)
```

**Explicación**: Cualquier conjunto sin elementos es igual al conjunto vacío.

#### `EmptySet_subseteq_any (x : U)`

```lean
∅ ⊆ x
```

**Explicación**: El conjunto vacío es subconjunto de cualquier conjunto.

---

## Specification

**Namespace**: `SetUniverse.SpecificationAxiom`

**Descripción**: Axioma de Especificación (o Separación) que permite formar subconjuntos mediante predicados. Define operaciones como intersección binaria y diferencia de conjuntos.

### Axiomas

#### `Specification (x : U) (P : U → Prop)`

```lean
∃ y, ∀ z, z ∈ y ↔ z ∈ x ∧ P z
```

**Explicación**: Axioma de Especificación: dado un conjunto x y un predicado P, existe un conjunto y que contiene exactamente los elementos de x que satisfacen P.

### Definiciones

#### `SpecSet (x : U) (P : U → Prop) : U`

```lean
{z ∈ x | P z}
```

**Explicación**: Conjunto de separación: el subconjunto de x formado por los elementos que satisfacen P.

#### `BinInter (x y : U) : U`

```lean
x ∩ y := {z ∈ x | z ∈ y}
```

**Explicación**: Intersección binaria de dos conjuntos.

#### `Difference (x y : U) : U`

```lean
x \ y := {z ∈ x | z ∉ y}
```

**Explicación**: Diferencia de conjuntos: elementos de x que no están en y.

### Teoremas

#### `SpecificationUnique (x : U) (P : U → Prop)`

```lean
∃! y, ∀ z, z ∈ y ↔ z ∈ x ∧ P z
```

**Explicación**: El conjunto especificado por un predicado es único.

#### `SpecSet_is_specified (x z : U) (P : U → Prop)`

```lean
z ∈ SpecSet x P ↔ z ∈ x ∧ P z
```

**Explicación**: Caracterización de pertenencia al conjunto especificado.

#### `BinInter_is_specified (x y z : U)`

```lean
z ∈ (x ∩ y) ↔ z ∈ x ∧ z ∈ y
```

**Explicación**: Un elemento está en la intersección si y solo si está en ambos conjuntos.

#### `BinInterUniqueSet (x y : U)`

```lean
∃! s, ∀ z, z ∈ s ↔ z ∈ x ∧ z ∈ y
```

**Explicación**: La intersección binaria es única.

#### `BinInter_subset (x y : U)`

```lean
x ∩ y ⊆ x ∧ x ∩ y ⊆ y
```

**Explicación**: La intersección es subconjunto de ambos conjuntos.

#### `BinInter_empty (x y : U)`

```lean
(x ∩ y = ∅) ↔ x ⟂ y
```

**Explicación**: La intersección es vacía si y solo si los conjuntos son disjuntos.

#### `BinInter_commutative (x y : U)`

```lean
x ∩ y = y ∩ x
```

**Explicación**: La intersección es conmutativa.

#### `BinInter_associative (x y z : U)`

```lean
x ∩ (y ∩ z) = (x ∩ y) ∩ z
```

**Explicación**: La intersección es asociativa.

#### `BinInter_absorbent_elem (x : U)`

```lean
x ∩ ∅ = ∅
```

**Explicación**: El vacío es elemento absorbente para la intersección.

#### `BinInter_with_subseteq (x y : U)`

```lean
x ⊆ y → x ∩ y = x
```

**Explicación**: Si x está contenido en y, la intersección es x.

#### `BinInter_with_empty (x : U)`

```lean
x ∩ ∅ = ∅
```

**Explicación**: La intersección con el vacío es vacía.

#### `BinInter_idempotence (x : U)`

```lean
x ∩ x = x
```

**Explicación**: La intersección es idempotente.

#### `Difference_is_specified (x y z : U)`

```lean
z ∈ (x \ y) ↔ z ∈ x ∧ z ∉ y
```

**Explicación**: Un elemento está en la diferencia si está en x pero no en y.

#### `DifferenceUniqueSet (x y : U)`

```lean
∃! s, ∀ z, z ∈ s ↔ z ∈ x ∧ z ∉ y
```

**Explicación**: La diferencia de conjuntos es única.

#### `Difference_subset (x y : U)`

```lean
x \ y ⊆ x
```

**Explicación**: La diferencia es subconjunto del primer conjunto.

#### `Difference_empty_iff_subseteq (x y : U)`

```lean
(x \ y = ∅) ↔ x ⊆ y
```

**Explicación**: La diferencia es vacía si y solo si x está contenido en y.

#### `Difference_with_empty (x : U)`

```lean
x \ ∅ = x
```

**Explicación**: La diferencia con el vacío es el conjunto mismo.

#### `Difference_self_empty (x : U)`

```lean
x \ x = ∅
```

**Explicación**: La diferencia de un conjunto consigo mismo es vacía.

#### `Difference_disjoint (x y : U) (h_disjoint : x ⟂ y)`

```lean
x \ y = x
```

**Explicación**: Si los conjuntos son disjuntos, la diferencia es el primer conjunto.

---

## Pairing

**Namespace**: `SetUniverse.PairingAxiom`

**Descripción**: Axioma de Emparejamiento (o Pares) que garantiza la existencia del par no ordenado de dos conjuntos. Define pares ordenados, singletons e intersección generalizada.

### Axiomas

#### `Pairing (x y : U)`

```lean
∃ (z : U), x ∈ z ∧ y ∈ z
```

**Explicación**: Axioma de Emparejamiento: dado dos conjuntos x e y, existe un conjunto z que los contiene a ambos.

### Definiciones

#### `PairSet (x y : U) : U`

```lean
{x, y}
```

**Explicación**: Par no ordenado: conjunto que contiene exactamente x e y.

#### `Singleton (x : U) : U`

```lean
{x}
```

**Explicación**: Singleton: conjunto que contiene únicamente a x.

#### `interSet (w : U) : U`

```lean
⋂ w := {z | ∀ y ∈ w, z ∈ y}
```

**Explicación**: Intersección generalizada: conjunto de elementos que pertenecen a todos los elementos de w.

#### `OrderedPair (x y : U) : U`

```lean
⟨x, y⟩ := {{x}, {x, y}}
```

**Explicación**: Par ordenado de Kuratowski: construcción que distingue orden usando el par no ordenado.

#### `isOrderedPair (w : U) : Prop`

```lean
∃ x y, w = ⟨x, y⟩
```

**Explicación**: Predicado que indica si un conjunto es un par ordenado.

#### `fst (w : U) : U`

```lean
⋂ (⋂ w)
```

**Explicación**: Primera componente de un par ordenado.

#### `snd (w : U) : U`

```lean
⋂ {y | ∃ x ∈ (⋂ w), {x, y} ∈ w}
```

**Explicación**: Segunda componente de un par ordenado.

#### `isRelation (R : U) : Prop`

```lean
∀ w ∈ R, isOrderedPair w
```

**Explicación**: Un conjunto es una relación si todos sus elementos son pares ordenados.

#### `domain (R : U) : U`

```lean
{x | ∃ y, ⟨x, y⟩ ∈ R}
```

**Explicación**: Dominio de una relación: primeras componentes de los pares.

#### `range (R : U) : U`

```lean
{y | ∃ x, ⟨x, y⟩ ∈ R}
```

**Explicación**: Rango de una relación: segundas componentes de los pares.

### Teoremas

#### `PairingUniqueSet (x y : U)`

```lean
∃! z, (∀ w, w ∈ z ↔ w = x ∨ w = y)
```

**Explicación**: El par no ordenado es único.

#### `PairSet_is_specified (x y : U)`

```lean
∀ z, z ∈ {x, y} ↔ z = x ∨ z = y
```

**Explicación**: Un elemento está en el par si es igual a x o a y.

#### `Singleton_is_specified (x z : U)`

```lean
z ∈ {x} ↔ z = x
```

**Explicación**: Un elemento está en un singleton si y solo si es ese elemento.

#### `nonempty_iff_exists_mem (w : U)`

```lean
w ≠ ∅ ↔ ∃ y, y ∈ w
```

**Explicación**: Un conjunto es no vacío si y solo si tiene al menos un elemento.

#### `interSet_of_singleton (A : U)`

```lean
⋂ {A} = A
```

**Explicación**: La intersección de un singleton es el elemento mismo.

#### `OrderedPair_is_specified (x y : U)`

```lean
⟨x, y⟩ = {{x}, {x, y}}
```

**Explicación**: Definición explícita del par ordenado de Kuratowski.

#### `inter_of_ordered_pair (x y : U)`

```lean
⋂ ⟨x, y⟩ = {x}
```

**Explicación**: La intersección de un par ordenado es el singleton de la primera componente.

#### `fst_of_ordered_pair (x y : U)`

```lean
fst ⟨x, y⟩ = x
```

**Explicación**: La función fst extrae correctamente la primera componente.

#### `snd_of_ordered_pair (x y : U)`

```lean
snd ⟨x, y⟩ = y
```

**Explicación**: La función snd extrae correctamente la segunda componente.

#### `Eq_of_OrderedPairs_given_projections (a b c d : U)`

```lean
fst ⟨a, b⟩ = fst ⟨c, d⟩ ∧ snd ⟨a, b⟩ = snd ⟨c, d⟩ → ⟨a, b⟩ = ⟨c, d⟩
```

**Explicación**: Si las componentes son iguales, los pares ordenados son iguales.

#### `Eq_OrderedPairs (w v : U)`

```lean
isOrderedPair w ∧ isOrderedPair v → (w = v ↔ fst w = fst v ∧ snd w = snd v)
```

**Explicación**: Dos pares ordenados son iguales si y solo si sus componentes respectivas son iguales.

---

## Union

**Namespace**: `SetUniverse.UnionAxiom`

**Descripción**: Axioma de Unión que garantiza la existencia de la unión de una familia de conjuntos. Define unión binaria y diferencia simétrica.

### Axiomas

#### `Union`

```lean
∀ C : U, ∃ u : U, ∀ x : U, x ∈ u ↔ ∃ y : U, y ∈ C ∧ x ∈ y
```

**Explicación**: Axioma de Unión: dada una familia de conjuntos C, existe un conjunto u que contiene exactamente los elementos que pertenecen a algún miembro de C.

### Definiciones

#### `UnionSet (C : U) : U`

```lean
⋃ C
```

**Explicación**: Unión de una familia: conjunto de todos los elementos que pertenecen a algún miembro de C.

#### `BinUnion (A B : U) : U`

```lean
A ∪ B := ⋃ {A, B}
```

**Explicación**: Unión binaria de dos conjuntos.

#### `SymDiff (A B : U) : U`

```lean
A △ B := (A \ B) ∪ (B \ A)
```

**Explicación**: Diferencia simétrica: elementos que están en exactamente uno de los dos conjuntos.

### Teoremas

#### `UnionExistsUnique (C : U)`

```lean
∃! u, ∀ x, x ∈ u ↔ ∃ y ∈ C, x ∈ y
```

**Explicación**: La unión de una familia es única.

#### `UnionSet_is_specified (C x : U)`

```lean
x ∈ (⋃ C) ↔ ∃ y ∈ C, x ∈ y
```

**Explicación**: Un elemento está en la unión si pertenece a algún miembro de la familia.

#### `UnionSet_is_unique (C UC : U)`

```lean
(∀ x, x ∈ UC ↔ ∃ y ∈ C, x ∈ y) → UC = ⋃ C
```

**Explicación**: La unión es el único conjunto con esta propiedad.

#### `Set_is_empty_1 (C : U) (hC_empty : C = ∅)`

```lean
⋃ C = ∅
```

**Explicación**: La unión del vacío es vacía.

#### `UnionSet_is_empty (C : U)`

```lean
⋃ C = ∅ ↔ (C = ∅ ∨ C = {∅} ∨ (∀ y ∈ C, y = ∅))
```

**Explicación**: La unión es vacía si la familia es vacía, contiene solo el vacío, o todos sus miembros son vacíos.

#### `BinUnion_is_specified (A B x : U)`

```lean
x ∈ (A ∪ B) ↔ x ∈ A ∨ x ∈ B
```

**Explicación**: Un elemento está en la unión binaria si está en al menos uno de los conjuntos.

#### `BinUnion_comm (A B : U)`

```lean
A ∪ B = B ∪ A
```

**Explicación**: La unión binaria es conmutativa.

#### `BinUnion_empty_left (A : U)`

```lean
∅ ∪ A = A
```

**Explicación**: El vacío es elemento neutro por la izquierda.

#### `BinUnion_empty_right (A : U)`

```lean
A ∪ ∅ = A
```

**Explicación**: El vacío es elemento neutro por la derecha.

#### `BinUnion_idem (A : U)`

```lean
A ∪ A = A
```

**Explicación**: La unión es idempotente.

#### `BinUnion_assoc (A B C : U)`

```lean
A ∪ (B ∪ C) = (A ∪ B) ∪ C
```

**Explicación**: La unión es asociativa.

#### `SymDiff_is_specified (A B x : U)`

```lean
x ∈ (A △ B) ↔ (x ∈ A ∧ x ∉ B) ∨ (x ∈ B ∧ x ∉ A)
```

**Explicación**: Un elemento está en la diferencia simétrica si está en exactamente uno de los conjuntos.

#### `SymDiff_comm (A B : U)`

```lean
A △ B = B △ A
```

**Explicación**: La diferencia simétrica es conmutativa.

#### `SymDiff_empty_left (A : U)`

```lean
∅ △ A = A
```

**Explicación**: El vacío es elemento neutro para la diferencia simétrica.

#### `SymDiff_self (A : U)`

```lean
A △ A = ∅
```

**Explicación**: La diferencia simétrica de un conjunto consigo mismo es vacía.

---

## PowerSet

**Namespace**: `SetUniverse.PowerSetAxiom`

**Descripción**: Axioma del Conjunto Potencia que garantiza la existencia del conjunto de todos los subconjuntos de un conjunto dado.

### Axiomas

#### `PowerSet`

```lean
∀ A : U, ∃ P : U, ∀ x : U, x ∈ P ↔ x ⊆ A
```

**Explicación**: Axioma del Conjunto Potencia: para cualquier conjunto A, existe un conjunto P cuyos elementos son exactamente los subconjuntos de A.

### Definiciones

#### `PowerSetOf (A : U) : U`

```lean
𝒫 A
```

**Explicación**: Conjunto potencia: conjunto de todos los subconjuntos de A.

### Teoremas

#### `PowerSetExistsUnique (A : U)`

```lean
∃! P, ∀ x, x ∈ P ↔ x ⊆ A
```

**Explicación**: El conjunto potencia es único.

#### `PowerSet_is_specified (A x : U)`

```lean
x ∈ 𝒫 A ↔ x ⊆ A
```

**Explicación**: Un conjunto está en el conjunto potencia si y solo si es subconjunto.

#### `empty_mem_PowerSet (A : U)`

```lean
∅ ∈ 𝒫 A
```

**Explicación**: El vacío es siempre miembro del conjunto potencia.

#### `self_mem_PowerSet (A : U)`

```lean
A ∈ 𝒫 A
```

**Explicación**: Todo conjunto está en su propio conjunto potencia.

#### `PowerSet_nonempty (A : U)`

```lean
𝒫 A ≠ ∅
```

**Explicación**: El conjunto potencia nunca es vacío.

#### `PowerSet_empty`

```lean
𝒫 ∅ = {∅}
```

**Explicación**: El conjunto potencia del vacío contiene solo el vacío.

#### `PowerSet_mono (A B : U) (h : A ⊆ B)`

```lean
𝒫 A ⊆ 𝒫 B
```

**Explicación**: La operación de conjunto potencia es monótona.

#### `PowerSet_inter (A B : U)`

```lean
𝒫 (A ∩ B) = 𝒫 A ∩ 𝒫 B
```

**Explicación**: El conjunto potencia de una intersección es la intersección de los conjuntos potencia.

#### `PowerSet_union_subset (A B : U)`

```lean
𝒫 A ∪ 𝒫 B ⊆ 𝒫 (A ∪ B)
```

**Explicación**: La unión de conjuntos potencia está contenida en el conjunto potencia de la unión.

#### `Union_PowerSet (A : U)`

```lean
⋃ (𝒫 A) = A
```

**Explicación**: La unión del conjunto potencia es el conjunto original.

---

## OrderedPair

**Namespace**: `SetUniverse.OrderedPairExtensions`

**Descripción**: Extensiones y propiedades adicionales de pares ordenados.

### Teoremas

#### `OrderedPair_eq_of (a b c d : U)`

```lean
a = c → b = d → ⟨a, b⟩ = ⟨c, d⟩
```

**Explicación**: Si las componentes son iguales, los pares ordenados son iguales.

#### `OrderedPair_eq_iff (a b c d : U)`

```lean
⟨a, b⟩ = ⟨c, d⟩ ↔ a = c ∧ b = d
```

**Explicación**: Dos pares ordenados son iguales si y solo si sus componentes respectivas son iguales.

#### `OrderedPair_in_PowerSet (a b A B : U) (ha : a ∈ A) (hb : b ∈ B)`

```lean
⟨a, b⟩ ∈ 𝒫 (𝒫 (A ∪ B))
```

**Explicación**: Un par ordenado está en el doble conjunto potencia de la unión.

---

## CartesianProduct

**Namespace**: `SetUniverse.CartesianProduct`

**Descripción**: Define el producto cartesiano de dos conjuntos y sus propiedades.

### Definiciones

#### `CartesianProduct (A B : U) : U`

```lean
A ×ₛ B := {p | ∃ a ∈ A, ∃ b ∈ B, p = ⟨a, b⟩}
```

**Explicación**: Producto cartesiano: conjunto de todos los pares ordenados (a, b) con a ∈ A y b ∈ B.

### Teoremas

#### `CartesianProduct_is_specified (A B p : U)`

```lean
p ∈ (A ×ₛ B) ↔ ∃ a ∈ A, ∃ b ∈ B, p = ⟨a, b⟩
```

**Explicación**: Un elemento está en el producto cartesiano si es un par ordenado con componentes en A y B.

#### `OrderedPair_mem_CartesianProduct (a b A B : U)`

```lean
⟨a, b⟩ ∈ (A ×ₛ B) ↔ a ∈ A ∧ b ∈ B
```

**Explicación**: Un par ordenado está en el producto cartesiano si y solo si sus componentes están en los conjuntos respectivos.

#### `CartesianProduct_empty_left (B : U)`

```lean
∅ ×ₛ B = ∅
```

**Explicación**: El producto con el vacío por la izquierda es vacío.

#### `CartesianProduct_empty_right (A : U)`

```lean
A ×ₛ ∅ = ∅
```

**Explicación**: El producto con el vacío por la derecha es vacío.

#### `CartesianProduct_mono (A A' B B' : U) (hA : A ⊆ A') (hB : B ⊆ B')`

```lean
A ×ₛ B ⊆ A' ×ₛ B'
```

**Explicación**: El producto cartesiano es monótono en ambas componentes.

#### `CartesianProduct_distrib_union_left (A B C : U)`

```lean
(A ∪ B) ×ₛ C = (A ×ₛ C) ∪ (B ×ₛ C)
```

**Explicación**: El producto distribuye sobre la unión por la izquierda.

#### `CartesianProduct_distrib_union_right (A B C : U)`

```lean
A ×ₛ (B ∪ C) = (A ×ₛ B) ∪ (A ×ₛ C)
```

**Explicación**: El producto distribuye sobre la unión por la derecha.

#### `CartesianProduct_distrib_inter_left (A B C : U)`

```lean
(A ∩ B) ×ₛ C = (A ×ₛ C) ∩ (B ×ₛ C)
```

**Explicación**: El producto distribuye sobre la intersección por la izquierda.

#### `CartesianProduct_distrib_inter_right (A B C : U)`

```lean
A ×ₛ (B ∩ C) = (A ×ₛ B) ∩ (A ×ₛ C)
```

**Explicación**: El producto distribuye sobre la intersección por la derecha.

---

## Relations

**Namespace**: `SetUniverse.Relations`

**Descripción**: Define relaciones binarias y sus propiedades: reflexividad, simetría, transitividad, órdenes, equivalencias, etc.

### Definiciones

#### `isRelationOn (R A : U) : Prop`

```lean
R ⊆ (A ×ₛ A)
```

**Explicación**: R es una relación sobre A si es subconjunto del producto cartesiano A × A.

#### `isRelationFrom (R A B : U) : Prop`

```lean
R ⊆ (A ×ₛ B)
```

**Explicación**: R es una relación de A a B si es subconjunto de A × B.

#### `Related (R x y : U) : Prop`

```lean
⟨x, y⟩ ∈ R
```

**Explicación**: x está relacionado con y según R, denotado x ~ y.

#### `isReflexiveOn (R A : U) : Prop`

```lean
∀ x ∈ A, ⟨x, x⟩ ∈ R
```

**Explicación**: R es reflexiva sobre A si todo elemento está relacionado consigo mismo.

#### `isIrreflexiveOn (R A : U) : Prop`

```lean
∀ x ∈ A, ⟨x, x⟩ ∉ R
```

**Explicación**: R es irreflexiva sobre A si ningún elemento está relacionado consigo mismo.

#### `isSymmetricOn (R A : U) : Prop`

```lean
∀ x y ∈ A, ⟨x, y⟩ ∈ R → ⟨y, x⟩ ∈ R
```

**Explicación**: R es simétrica sobre A si la relación es bidireccional.

#### `isAntiSymmetricOn (R A : U) : Prop`

```lean
∀ x y ∈ A, ⟨x, y⟩ ∈ R → ⟨y, x⟩ ∈ R → x = y
```

**Explicación**: R es antisimétrica sobre A si elementos distintos no pueden estar relacionados en ambas direcciones.

#### `isAsymmetricOn (R A : U) : Prop`

```lean
∀ x y ∈ A, ⟨x, y⟩ ∈ R → ⟨y, x⟩ ∉ R
```

**Explicación**: R es asimétrica sobre A si la relación nunca es bidireccional.

#### `isTransitiveOn (R A : U) : Prop`

```lean
∀ x y z ∈ A, ⟨x, y⟩ ∈ R → ⟨y, z⟩ ∈ R → ⟨x, z⟩ ∈ R
```

**Explicación**: R es transitiva sobre A si la relación se compone.

#### `isConnectedOn (R A : U) : Prop`

```lean
∀ x y ∈ A, x ≠ y → (⟨x, y⟩ ∈ R ∨ ⟨y, x⟩ ∈ R)
```

**Explicación**: R es conexa sobre A si elementos distintos están relacionados en alguna dirección.

#### `isEquivalenceOn (R A : U) : Prop`

```lean
isReflexiveOn R A ∧ isSymmetricOn R A ∧ isTransitiveOn R A
```

**Explicación**: R es una relación de equivalencia si es reflexiva, simétrica y transitiva.

#### `isPreorderOn (R A : U) : Prop`

```lean
isReflexiveOn R A ∧ isTransitiveOn R A
```

**Explicación**: R es un preorden si es reflexiva y transitiva.

#### `isPartialOrderOn (R A : U) : Prop`

```lean
isReflexiveOn R A ∧ isAntiSymmetricOn R A ∧ isTransitiveOn R A
```

**Explicación**: R es un orden parcial si es reflexiva, antisimétrica y transitiva.

#### `isLinearOrderOn (R A : U) : Prop`

```lean
isPartialOrderOn R A ∧ isConnectedOn R A
```

**Explicación**: R es un orden lineal (o total) si es orden parcial y conexo.

#### `isStrictOrderOn (R A : U) : Prop`

```lean
isIrreflexiveOn R A ∧ isTransitiveOn R A
```

**Explicación**: R es un orden estricto si es irreflexiva y transitiva.

#### `isStrictPartialOrderOn (R A : U) : Prop`

```lean
isIrreflexiveOn R A ∧ isAsymmetricOn R A ∧ isTransitiveOn R A
```

**Explicación**: R es un orden parcial estricto si es irreflexiva, asimétrica y transitiva.

#### `isStrictLinearOrderOn (R A : U) : Prop`

```lean
isStrictPartialOrderOn R A ∧ isConnectedOn R A
```

**Explicación**: R es un orden lineal estricto si es orden parcial estricto y conexo.

#### `isWellFoundedOn (R A : U) : Prop`

```lean
∀ S ⊆ A, S ≠ ∅ → ∃ m ∈ S, ∀ x ∈ S, ⟨x, m⟩ ∉ R
```

**Explicación**: R es bien fundado si todo subconjunto no vacío tiene un elemento minimal.

#### `isWellOrderOn (R A : U) : Prop`

```lean
isLinearOrderOn R A ∧ isWellFoundedOn R A
```

**Explicación**: R es un buen orden si es orden lineal y bien fundado.

#### `EqClass (a R A : U) : U`

```lean
[a]ᴿ := {x ∈ A | ⟨a, x⟩ ∈ R}
```

**Explicación**: Clase de equivalencia de a según R: conjunto de elementos relacionados con a.

#### `QuotientSet (A R : U) : U`

```lean
A/R := {[a]ᴿ | a ∈ A}
```

**Explicación**: Conjunto cociente: conjunto de todas las clases de equivalencia.

#### `IdRel (A : U) : U`

```lean
{⟨x, x⟩ | x ∈ A}
```

**Explicación**: Relación de identidad: cada elemento relacionado solo consigo mismo.

#### `InverseRel (R : U) : U`

```lean
R⁻¹ := {⟨y, x⟩ | ⟨x, y⟩ ∈ R}
```

**Explicación**: Relación inversa: intercambia el orden de los pares.

### Teoremas

#### `Asymmetric_implies_Irreflexive (R A : U)`

```lean
isAsymmetricOn R A → isIrreflexiveOn R A
```

**Explicación**: Una relación asimétrica es necesariamente irreflexiva.

#### `Irreflexive_Transitive_implies_Asymmetric (R A : U)`

```lean
isIrreflexiveOn R A → isTransitiveOn R A → isAsymmetricOn R A
```

**Explicación**: Una relación irreflexiva y transitiva es asimétrica.

#### `Asymmetric_iff_Irreflexive_and_AntiSymmetric (R A : U)`

```lean
isAsymmetricOn R A ↔ isIrreflexiveOn R A ∧ isAntiSymmetricOn R A
```

**Explicación**: Asimetría equivale a irreflexividad más antisimetría.

#### `PartialOrder_Connected_is_LinearOrder (R A : U)`

```lean
isPartialOrderOn R A → isConnectedOn R A → isLinearOrderOn R A
```

**Explicación**: Un orden parcial conexo es un orden lineal.

#### `LinearOrder_comparable (R A : U) (hLO : isLinearOrderOn R A) (x y : U) (hx : x ∈ A) (hy : y ∈ A)`

```lean
⟨x, y⟩ ∈ R ∨ ⟨y, x⟩ ∈ R
```

**Explicación**: En un orden lineal, dos elementos cualesquiera son comparables.

#### `IdRel_is_Equivalence (A : U)`

```lean
isEquivalenceOn (IdRel A) A
```

**Explicación**: La relación de identidad es una relación de equivalencia.

#### `EqClass_mem_self (R A a : U) (ha : a ∈ A) (hR : isReflexiveOn R A)`

```lean
a ∈ [a]ᴿ
```

**Explicación**: En una relación reflexiva, cada elemento está en su propia clase de equivalencia.

#### `mem_EqClass_iff (R A a b : U) (hR : isEquivalenceOn R A) (ha : a ∈ A) (hb : b ∈ A)`

```lean
b ∈ [a]ᴿ ↔ ⟨a, b⟩ ∈ R
```

**Explicación**: Un elemento está en la clase de equivalencia si y solo si está relacionado.

#### `EqClass_eq_iff (R A a b : U) (hR : isEquivalenceOn R A) (ha : a ∈ A) (hb : b ∈ A)`

```lean
[a]ᴿ = [b]ᴿ ↔ ⟨a, b⟩ ∈ R
```

**Explicación**: Dos clases de equivalencia son iguales si y solo si sus representantes están relacionados.

#### `EqClass_eq_or_disjoint (R A a b : U) (hR : isEquivalenceOn R A) (ha : a ∈ A) (hb : b ∈ A)`

```lean
[a]ᴿ = [b]ᴿ ∨ [a]ᴿ ⟂ [b]ᴿ
```

**Explicación**: Dos clases de equivalencia son iguales o disjuntas.

---

## Functions

**Namespace**: `SetUniverse.Functions`

**Descripción**: Define funciones como relaciones especiales, operaciones de composición, inyectividad, sobreyectividad, biyecciones, y equipotencia.

### Definiciones

#### `isSingleValued (f : U) : Prop`

```lean
∀ x y₁ y₂, ⟨x, y₁⟩ ∈ f → ⟨x, y₂⟩ ∈ f → y₁ = y₂
```

**Explicación**: f es univalente si cada entrada tiene a lo sumo una salida.

#### `isFunctionFromTo (f A B : U) : Prop`

```lean
isSingleValued f ∧ Dom f = A ∧ Ran f ⊆ B
```

**Explicación**: f es una función de A a B si es univalente, con dominio A y rango contenido en B.

#### `Dom (f : U) : U`

```lean
{x | ∃ y, ⟨x, y⟩ ∈ f}
```

**Explicación**: Dominio de f: conjunto de primeras componentes.

#### `Ran (f : U) : U`

```lean
{y | ∃ x, ⟨x, y⟩ ∈ f}
```

**Explicación**: Rango de f: conjunto de segundas componentes.

#### `apply (f x : U) : U`

```lean
f⦅x⦆ := el único y tal que ⟨x, y⟩ ∈ f
```

**Explicación**: Aplicación de función: f⦅x⦆ es el valor de f en x.

#### `IdFunction (A : U) : U`

```lean
𝟙 A := {⟨x, x⟩ | x ∈ A}
```

**Explicación**: Función identidad sobre A: mapea cada elemento a sí mismo.

#### `FunctionComposition (g f : U) : U`

```lean
g ∘ f := {⟨x, z⟩ | ∃ y, ⟨x, y⟩ ∈ f ∧ ⟨y, z⟩ ∈ g}
```

**Explicación**: Composición de funciones: (g ∘ f)(x) = g(f(x)).

#### `InverseFunction (f : U) : U`

```lean
f⁻¹ˢ := {⟨y, x⟩ | ⟨x, y⟩ ∈ f}
```

**Explicación**: Función inversa: intercambia dominio y rango.

#### `isInjective (f : U) : Prop`

```lean
∀ x₁ x₂ y, ⟨x₁, y⟩ ∈ f → ⟨x₂, y⟩ ∈ f → x₁ = x₂
```

**Explicación**: f es inyectiva si elementos distintos tienen imágenes distintas.

#### `isSurjectiveOnto (f B : U) : Prop`

```lean
Ran f = B
```

**Explicación**: f es sobreyectiva sobre B si su rango es todo B.

#### `isBijection (f A B : U) : Prop`

```lean
isFunctionFromTo f A B ∧ isInjective f ∧ isSurjectiveOnto f B
```

**Explicación**: f es una biyección de A a B si es función inyectiva y sobreyectiva.

#### `hasLeftInverse (f A B g : U) : Prop`

```lean
g ∘ f = 𝟙 A
```

**Explicación**: g es inversa por la izquierda de f si g(f(x)) = x para todo x en A.

#### `hasRightInverse (f A B g : U) : Prop`

```lean
f ∘ g = 𝟙 B
```

**Explicación**: g es inversa por la derecha de f si f(g(y)) = y para todo y en B.

#### `isInvertible (f A B : U) : Prop`

```lean
∃ g, g ∘ f = 𝟙 A ∧ f ∘ g = 𝟙 B
```

**Explicación**: f es invertible si tiene inversa bilateral.

#### `ImageSet (f X : U) : U`

```lean
f⦃X⦄ := {y | ∃ x ∈ X, ⟨x, y⟩ ∈ f}
```

**Explicación**: Imagen de X bajo f: conjunto de valores de f en elementos de X.

#### `PreimageSet (f Y : U) : U`

```lean
f⁻¹⦃Y⦄ := {x | ∃ y ∈ Y, ⟨x, y⟩ ∈ f}
```

**Explicación**: Preimagen de Y bajo f: elementos cuya imagen está en Y.

#### `isEquipotent (A B : U) : Prop`

```lean
A ≃ₛ B := ∃ f, isBijection f A B
```

**Explicación**: A y B son equipotentes si existe una biyección entre ellos.

#### `isDominatedBy (A B : U) : Prop`

```lean
A ≼ₛ B := ∃ f, isFunctionFromTo f A B ∧ isInjective f
```

**Explicación**: A está dominado por B si existe una inyección de A a B.

#### `isStrictlyDominatedBy (A B : U) : Prop`

```lean
A ≺ₛ B := A ≼ₛ B ∧ ¬(A ≃ₛ B)
```

**Explicación**: A está estrictamente dominado por B si hay inyección pero no biyección.

### Teoremas Principales

#### `apply_eq (f x y : U) (hf : isSingleValued f) (hxy : ⟨x, y⟩ ∈ f)`

```lean
f⦅x⦆ = y
```

**Explicación**: Si (x,y) ∈ f, entonces f⦅x⦆ = y.

#### `IdFunction_is_function (A : U)`

```lean
isFunctionFromTo (𝟙 A) A A
```

**Explicación**: La identidad es una función de A a A.

#### `apply_id (A x : U) (hx : x ∈ A)`

```lean
(𝟙 A)⦅x⦆ = x
```

**Explicación**: La función identidad mapea cada elemento a sí mismo.

#### `comp_single_valued (g f : U) (hf : isSingleValued f) (hg : isSingleValued g)`

```lean
isSingleValued (g ∘ f)
```

**Explicación**: La composición de funciones univalentes es univalente.

#### `comp_is_function (f g A B C : U) (hf : isFunctionFromTo f A B) (hg : isFunctionFromTo g B C)`

```lean
isFunctionFromTo (g ∘ f) A C
```

**Explicación**: La composición de funciones es una función.

#### `comp_id_right (f A B : U) (hf : isFunctionFromTo f A B)`

```lean
f ∘ (𝟙 A) = f
```

**Explicación**: La identidad es elemento neutro por la derecha en la composición.

#### `comp_id_left (f A B : U) (hf : isFunctionFromTo f A B)`

```lean
(𝟙 B) ∘ f = f
```

**Explicación**: La identidad es elemento neutro por la izquierda en la composición.

#### `injective_iff_inverse_functional (f : U)`

```lean
isInjective f ↔ isSingleValued (f⁻¹ˢ)
```

**Explicación**: f es inyectiva si y solo si su inversa es univalente.

#### `surjective_iff_range_eq (f A B : U) (hf : isFunctionFromTo f A B)`

```lean
isSurjectiveOnto f B ↔ Ran f = B
```

**Explicación**: f es sobreyectiva sobre B si y solo si su rango es B.

#### `bijection_inverse_is_function (f A B : U) (hbij : isBijection f A B)`

```lean
isFunctionFromTo (f⁻¹ˢ) B A
```

**Explicación**: La inversa de una biyección es una función.

#### `bijection_comp_inverse_right (f A B : U) (hbij : isBijection f A B)`

```lean
f ∘ (f⁻¹ˢ) = 𝟙 B
```

**Explicación**: Una biyección compuesta con su inversa por la derecha da la identidad.

#### `bijection_comp_inverse_left (f A B : U) (hbij : isBijection f A B)`

```lean
(f⁻¹ˢ) ∘ f = 𝟙 A
```

**Explicación**: Una biyección compuesta con su inversa por la izquierda da la identidad.

#### `inverse_inverse (f A B : U) (hf : f ⊆ A ×ₛ B)`

```lean
(f⁻¹ˢ)⁻¹ˢ = f
```

**Explicación**: La inversa de la inversa es la función original.

#### `bijection_iff_invertible (f A B : U) (hf : isFunctionFromTo f A B)`

```lean
isBijection f A B ↔ isInvertible f A B
```

**Explicación**: Una función es biyección si y solo si es invertible.

#### `comp_injective (f g : U) (hinj_f : isInjective f) (hinj_g : isInjective g)`

```lean
isInjective (g ∘ f)
```

**Explicación**: La composición de funciones inyectivas es inyectiva.

#### `comp_surjective (f g A B C : U) (hf : isFunctionFromTo f A B) (hg : isFunctionFromTo g B C) (hsur_f : isSurjectiveOnto f B) (hsur_g : isSurjectiveOnto g C)`

```lean
isSurjectiveOnto (g ∘ f) C
```

**Explicación**: La composición de funciones sobreyectivas es sobreyectiva.

#### `comp_bijection (f g A B C : U) (hbij_f : isBijection f A B) (hbij_g : isBijection g B C)`

```lean
isBijection (g ∘ f) A C
```

**Explicación**: La composición de biyecciones es una biyección.

#### `id_is_bijection (A : U)`

```lean
isBijection (𝟙 A) A A
```

**Explicación**: La función identidad es una biyección.

#### `image_empty (f : U)`

```lean
f⦃∅⦄ = ∅
```

**Explicación**: La imagen del vacío es vacía.

#### `image_mono (f X Y : U) (h : X ⊆ Y)`

```lean
f⦃X⦄ ⊆ f⦃Y⦄
```

**Explicación**: La imagen es monótona: si X ⊆ Y, entonces f⦃X⦄ ⊆ f⦃Y⦄.

#### `image_union (f X Y : U)`

```lean
f⦃X ∪ Y⦄ = f⦃X⦄ ∪ f⦃Y⦄
```

**Explicación**: La imagen preserva uniones.

#### `preimage_union (f X Y : U)`

```lean
f⁻¹⦃X ∪ Y⦄ = f⁻¹⦃X⦄ ∪ f⁻¹⦃Y⦄
```

**Explicación**: La preimagen preserva uniones.

#### `preimage_inter_subset (f X Y : U)`

```lean
f⁻¹⦃X ∩ Y⦄ ⊆ f⁻¹⦃X⦄ ∩ f⁻¹⦃Y⦄
```

**Explicación**: La preimagen de la intersección está contenida en la intersección de las preimágenes.

#### `preimage_inter_eq (f X Y : U) (hf : isSingleValued f)`

```lean
f⁻¹⦃X ∩ Y⦄ = f⁻¹⦃X⦄ ∩ f⁻¹⦃Y⦄
```

**Explicación**: Para funciones, la preimagen preserva intersecciones.

#### `equipotent_refl (A : U)`

```lean
A ≃ₛ A
```

**Explicación**: La equipotencia es reflexiva.

#### `equipotent_symm (A B : U) (h : A ≃ₛ B)`

```lean
B ≃ₛ A
```

**Explicación**: La equipotencia es simétrica.

#### `equipotent_trans (A B C : U) (hab : A ≃ₛ B) (hbc : B ≃ₛ C)`

```lean
A ≃ₛ C
```

**Explicación**: La equipotencia es transitiva.

#### `equipotent_is_equivalence`

```lean
Equivalence (isEquipotent : U → U → Prop)
```

**Explicación**: La equipotencia es una relación de equivalencia.

#### `dominated_refl (A : U)`

```lean
A ≼ₛ A
```

**Explicación**: La dominación es reflexiva.

#### `dominated_trans (A B C : U) (hab : A ≼ₛ B) (hbc : B ≼ₛ C)`

```lean
A ≼ₛ C
```

**Explicación**: La dominación es transitiva.

#### `equipotent_implies_dominated_both (A B : U) (h : A ≃ₛ B)`

```lean
A ≼ₛ B ∧ B ≼ₛ A
```

**Explicación**: La equipotencia implica dominación mutua.

#### `strict_dominated_irrefl (A : U)`

```lean
¬(A ≺ₛ A)
```

**Explicación**: La dominación estricta es irreflexiva.

#### `strict_dominated_trans (A B C : U) (hab : A ≺ₛ B) (hbc : B ≺ₛ C)`

```lean
A ≺ₛ C
```

**Explicación**: La dominación estricta es transitiva.

---

## SetOrder

**Namespace**: `SetUniverse.SetOrder`

**Descripción**: Propiedades del orden parcial dado por la inclusión de conjuntos.

### Definiciones

#### `isUpperBound (S x : U) : Prop`

```lean
∀ y ∈ S, y ⊆ x
```

**Explicación**: x es cota superior de S si contiene a todos los elementos de S.

#### `isLowerBound (S x : U) : Prop`

```lean
∀ y ∈ S, x ⊆ y
```

**Explicación**: x es cota inferior de S si está contenido en todos los elementos de S.

#### `isSupremum (S x : U) : Prop`

```lean
isUpperBound S x ∧ ∀ z, isUpperBound S z → x ⊆ z
```

**Explicación**: x es el supremo de S si es la menor cota superior.

#### `isInfimum (S x : U) : Prop`

```lean
isLowerBound S x ∧ ∀ z, isLowerBound S z → z ⊆ x
```

**Explicación**: x es el ínfimo de S si es la mayor cota inferior.

#### `isBoundedAbove (S : U) : Prop`

```lean
∃ x, isUpperBound S x
```

**Explicación**: S está acotado superiormente si tiene alguna cota superior.

#### `isBoundedBelow (S : U) : Prop`

```lean
∃ x, isLowerBound S x
```

**Explicación**: S está acotado inferiormente si tiene alguna cota inferior.

### Teoremas

#### `empty_is_minimum (x : U)`

```lean
∅ ⊆ x
```

**Explicación**: El vacío es el elemento mínimo en el orden de inclusión.

#### `empty_is_unique_minimum (x : U)`

```lean
(∀ y, x ⊆ y) → x = ∅
```

**Explicación**: El vacío es el único conjunto contenido en todos los demás.

#### `any_family_bounded_below (S : U)`

```lean
isBoundedBelow S
```

**Explicación**: Toda familia de conjuntos está acotada inferiormente (por el vacío).

#### `inter_is_glb (A B : U)`

```lean
isInfimum {A, B} (A ∩ B)
```

**Explicación**: La intersección es el ínfimo de dos conjuntos.

#### `union_is_lub (A B : U)`

```lean
isSupremum {A, B} (A ∪ B)
```

**Explicación**: La unión es el supremo de dos conjuntos.

#### `order_reflexive (x : U)`

```lean
x ⊆ x
```

**Explicación**: La inclusión es reflexiva.

#### `order_transitive (x y z : U)`

```lean
x ⊆ y → y ⊆ z → x ⊆ z
```

**Explicación**: La inclusión es transitiva.

#### `order_antisymmetric (x y : U)`

```lean
x ⊆ y → y ⊆ x → x = y
```

**Explicación**: La inclusión es antisimétrica.

#### `union_monotone_left (A B C : U)`

```lean
A ⊆ B → A ∪ C ⊆ B ∪ C
```

**Explicación**: La unión es monótona en el primer argumento.

#### `union_monotone_right (A B C : U)`

```lean
A ⊆ B → C ∪ A ⊆ C ∪ B
```

**Explicación**: La unión es monótona en el segundo argumento.

#### `inter_monotone_left (A B C : U)`

```lean
A ⊆ B → A ∩ C ⊆ B ∩ C
```

**Explicación**: La intersección es monótona en el primer argumento.

#### `inter_monotone_right (A B C : U)`

```lean
A ⊆ B → C ∩ A ⊆ C ∩ B
```

**Explicación**: La intersección es monótona en el segundo argumento.

---

## SetStrictOrder

**Namespace**: `SetUniverse.SetStrictOrder`

**Descripción**: Propiedades del orden estricto dado por la inclusión propia de conjuntos.

### Teoremas

#### `subset_subseteq (x y : U)`

```lean
x ⊂ y → x ⊆ y
```

**Explicación**: La inclusión estricta implica inclusión.

#### `subseteq_subset_or_eq (x y : U)`

```lean
x ⊆ y → (x ⊂ y ∨ x = y)
```

**Explicación**: La inclusión es estricta o es igualdad.

#### `strict_order_irreflexive (x : U)`

```lean
¬(x ⊂ x)
```

**Explicación**: La inclusión estricta es irreflexiva.

#### `strict_order_asymmetric (x y : U)`

```lean
x ⊂ y → ¬(y ⊂ x)
```

**Explicación**: La inclusión estricta es asimétrica.

#### `strict_order_transitive (x y z : U)`

```lean
x ⊂ y → y ⊂ z → x ⊂ z
```

**Explicación**: La inclusión estricta es transitiva.

#### `subset_transitive_mixed_left (x y z : U)`

```lean
x ⊂ y → y ⊆ z → x ⊂ z
```

**Explicación**: Transitividad mixta: estricta con no estricta.

#### `subset_transitive_mixed_right (x y z : U)`

```lean
x ⊆ y → y ⊂ z → x ⊂ z
```

**Explicación**: Transitividad mixta: no estricta con estricta.

#### `partial_to_strict_order (x y : U)`

```lean
x ⊆ y ∧ x ≠ y → x ⊂ y
```

**Explicación**: Inclusión no estricta más diferencia implica inclusión estricta.

#### `strict_implies_partial (x y : U)`

```lean
x ⊂ y → x ⊆ y
```

**Explicación**: La inclusión estricta implica inclusión no estricta.

#### `strict_order_trichotomy_partial (x y : U)`

```lean
x ⊂ y ∨ x = y ∨ y ⊂ x ∨ (¬(x ⊆ y) ∧ ¬(y ⊆ x))
```

**Explicación**: Tricotomía parcial: o hay inclusión estricta en alguna dirección, o igualdad, o incomparabilidad.

#### `empty_strict_subset_nonempty (x : U)`

```lean
x ≠ ∅ → ∅ ⊂ x
```

**Explicación**: El vacío es subconjunto estricto de cualquier conjunto no vacío.

#### `strict_subset_nonempty (x y : U)`

```lean
x ⊂ y → y ≠ ∅
```

**Explicación**: Si x es subconjunto estricto de y, entonces y es no vacío.

---

## PowerSetAlgebra

**Namespace**: `SetUniverse.PowerSetAlgebra`

**Descripción**: Propiedades algebraicas del conjunto potencia con complemento: forma un álgebra booleana completa.

### Definiciones

#### `Complement (A X : U) : U`

```lean
X ^∁[A] := A \ X
```

**Explicación**: Complemento de X relativo a A: elementos de A que no están en X.

### Teoremas

#### `Complement_is_specified (A X z : U)`

```lean
z ∈ (X ^∁[A]) ↔ z ∈ A ∧ z ∉ X
```

**Explicación**: Un elemento está en el complemento si está en A pero no en X.

#### `union_mem_PowerSet (A X Y : U) (hX : X ∈ 𝒫 A) (hY : Y ∈ 𝒫 A)`

```lean
X ∪ Y ∈ 𝒫 A
```

**Explicación**: El conjunto potencia es cerrado bajo unión.

#### `inter_mem_PowerSet (A X Y : U) (hX : X ∈ 𝒫 A) (hY : Y ∈ 𝒫 A)`

```lean
X ∩ Y ∈ 𝒫 A
```

**Explicación**: El conjunto potencia es cerrado bajo intersección.

#### `complement_mem_PowerSet (A X : U) (hX : X ∈ 𝒫 A)`

```lean
X ^∁[A] ∈ 𝒫 A
```

**Explicación**: El conjunto potencia es cerrado bajo complemento.

#### `empty_in_PowerSet (A : U)`

```lean
∅ ∈ 𝒫 A
```

**Explicación**: El vacío es elemento mínimo (cero) del álgebra.

#### `universe_in_PowerSet (A : U)`

```lean
A ∈ 𝒫 A
```

**Explicación**: A es elemento máximo (uno) del álgebra.

#### `PowerSet_union_empty (X : U)`

```lean
X ∪ ∅ = X
```

**Explicación**: El vacío es elemento neutro para la unión.

#### `PowerSet_inter_universe (A X : U) (hX : X ⊆ A)`

```lean
X ∩ A = X
```

**Explicación**: A es elemento neutro para la intersección (dentro de 𝒫 A).

#### `PowerSet_union_complement (A X : U) (hX : X ⊆ A)`

```lean
X ∪ (X ^∁[A]) = A
```

**Explicación**: Ley del medio excluido: un conjunto unido con su complemento es el universo.

#### `PowerSet_inter_complement (A X : U)`

```lean
X ∩ (X ^∁[A]) = ∅
```

**Explicación**: Ley de no contradicción: un conjunto intersecado con su complemento es vacío.

#### `PowerSet_union_distrib_inter (X Y Z : U)`

```lean
X ∪ (Y ∩ Z) = (X ∪ Y) ∩ (X ∪ Z)
```

**Explicación**: La unión distribuye sobre la intersección.

#### `PowerSet_inter_distrib_union (X Y Z : U)`

```lean
X ∩ (Y ∪ Z) = (X ∩ Y) ∪ (X ∩ Z)
```

**Explicación**: La intersección distribuye sobre la unión.

#### `PowerSet_DeMorgan_union (A X Y : U)`

```lean
(X ∪ Y) ^∁[A] = (X ^∁[A]) ∩ (Y ^∁[A])
```

**Explicación**: Primera ley de De Morgan: complemento de unión es intersección de complementos.

#### `PowerSet_DeMorgan_inter (A X Y : U)`

```lean
(X ∩ Y) ^∁[A] = (X ^∁[A]) ∪ (Y ^∁[A])
```

**Explicación**: Segunda ley de De Morgan: complemento de intersección es unión de complementos.

#### `PowerSet_absorb_union_inter (X Y : U)`

```lean
X ∪ (X ∩ Y) = X
```

**Explicación**: Ley de absorción: unión con intersección.

#### `PowerSet_absorb_inter_union (X Y : U)`

```lean
X ∩ (X ∪ Y) = X
```

**Explicación**: Ley de absorción: intersección con unión.

#### `PowerSet_double_complement (A X : U) (hX : X ⊆ A)`

```lean
(X ^∁[A]) ^∁[A] = X
```

**Explicación**: Ley de doble negación: el complemento del complemento es el conjunto original.

#### `PowerSet_union_idempotent (X : U)`

```lean
X ∪ X = X
```

**Explicación**: La unión es idempotente.

#### `PowerSet_inter_idempotent (X : U)`

```lean
X ∩ X = X
```

**Explicación**: La intersección es idempotente.

#### `PowerSet_union_comm (X Y : U)`

```lean
X ∪ Y = Y ∪ X
```

**Explicación**: La unión es conmutativa.

#### `PowerSet_inter_comm (X Y : U)`

```lean
X ∩ Y = Y ∩ X
```

**Explicación**: La intersección es conmutativa.

#### `PowerSet_union_assoc (X Y Z : U)`

```lean
X ∪ (Y ∪ Z) = (X ∪ Y) ∪ Z
```

**Explicación**: La unión es asociativa.

#### `PowerSet_inter_assoc (X Y Z : U)`

```lean
X ∩ (Y ∩ Z) = (X ∩ Y) ∩ Z
```

**Explicación**: La intersección es asociativa.

#### `PowerSet_complement_empty (A : U)`

```lean
∅ ^∁[A] = A
```

**Explicación**: El complemento del vacío es el universo.

#### `PowerSet_complement_universe (A : U)`

```lean
A ^∁[A] = ∅
```

**Explicación**: El complemento del universo es el vacío.

---

## BooleanAlgebra

**Namespace**: `SetUniverse.BooleanAlgebra`

**Descripción**: Teoremas adicionales sobre la estructura de álgebra booleana de conjuntos.

### Teoremas

#### `BinUnion_absorb_inter (A B : U)`

```lean
A ∪ (A ∩ B) = A
```

**Explicación**: Ley de absorción para unión e intersección.

#### `BinInter_absorb_union (A B : U)`

```lean
A ∩ (A ∪ B) = A
```

**Explicación**: Ley de absorción para intersección y unión.

#### `BinUnion_distrib_inter (A B C : U)`

```lean
A ∪ (B ∩ C) = (A ∪ B) ∩ (A ∪ C)
```

**Explicación**: Distributividad de la unión sobre la intersección.

#### `BinInter_distrib_union (A B C : U)`

```lean
A ∩ (B ∪ C) = (A ∩ B) ∪ (A ∩ C)
```

**Explicación**: Distributividad de la intersección sobre la unión.

#### `DeMorgan_union (A B C : U)`

```lean
C \ (A ∪ B) = (C \ A) ∩ (C \ B)
```

**Explicación**: Ley de De Morgan para diferencia y unión.

#### `DeMorgan_inter (A B C : U)`

```lean
C \ (A ∩ B) = (C \ A) ∪ (C \ B)
```

**Explicación**: Ley de De Morgan para diferencia e intersección.

#### `Complement_union (A C : U) (h : A ⊆ C)`

```lean
C \ A = C \ (C ∩ A)
```

**Explicación**: Simplificación del complemento con intersección.

#### `Complement_inter (A C : U)`

```lean
C \ (C ∩ A) = C \ A
```

**Explicación**: Simplificación del complemento.

---

## BooleanRing

**Namespace**: `SetUniverse.BooleanRing`

**Descripción**: Propiedades del anillo booleano formado por (𝒫 A, △, ∩, ∅, A), donde △ es la diferencia simétrica.

### Teoremas

#### `SymDiff_is_comm (X Y : U)`

```lean
X △ Y = Y △ X
```

**Explicación**: La diferencia simétrica es conmutativa (anillo conmutativo).

#### `SymDiff_identity_empty (X : U)`

```lean
X △ ∅ = X
```

**Explicación**: El vacío es elemento neutro aditivo.

#### `SymDiff_inverse (X : U)`

```lean
X △ X = ∅
```

**Explicación**: Todo conjunto es su propio inverso aditivo.

#### `SymDiff_assoc (X Y Z : U)`

```lean
X △ (Y △ Z) = (X △ Y) △ Z
```

**Explicación**: La diferencia simétrica es asociativa.

#### `SymDiff_inter_distrib (X Y Z : U)`

```lean
X ∩ (Y △ Z) = (X ∩ Y) △ (X ∩ Z)
```

**Explicación**: La intersección distribuye sobre la diferencia simétrica (distributividad del producto sobre la suma).

#### `SymDiff_mem_PowerSet (A X Y : U) (hX : X ∈ 𝒫 A) (hY : Y ∈ 𝒫 A)`

```lean
X △ Y ∈ 𝒫 A
```

**Explicación**: El conjunto potencia es cerrado bajo diferencia simétrica.

#### `SymDiff_eq_union_diff (X Y : U)`

```lean
X △ Y = (X \ Y) ∪ (Y \ X)
```

**Explicación**: Expresión alternativa de la diferencia simétrica.

#### `SymDiff_as_complement (A X Y : U) (hX : X ⊆ A) (hY : Y ⊆ A)`

```lean
X △ Y = (X ∪ Y) ∩ ((X ∩ Y) ^∁[A])
```

**Explicación**: Diferencia simétrica en términos de unión, intersección y complemento.

#### `SymDiff_eq_self_iff_empty (X Y : U)`

```lean
X △ Y = X ↔ Y = ∅
```

**Explicación**: X △ Y = X si y solo si Y es vacío.

---

## AtomicBooleanAlgebra

**Namespace**: `SetUniverse.AtomicBooleanAlgebra`

**Descripción**: Propiedades de atomicidad del álgebra booleana 𝒫 A: todo elemento no vacío contiene un átomo (singleton).

### Definiciones

#### `isAtom (A X : U) : Prop`

```lean
X ∈ 𝒫 A ∧ X ≠ ∅ ∧ ∀ Y ∈ 𝒫 A, Y ⊆ X → (Y = ∅ ∨ Y = X)
```

**Explicación**: X es un átomo en 𝒫 A si es minimal no vacío: solo tiene como subconjuntos propios al vacío.

#### `Atoms (A : U) : U`

```lean
{X ∈ 𝒫 A | isAtom A X}
```

**Explicación**: Conjunto de todos los átomos de 𝒫 A.

#### `atomBelow (A X Y : U) : Prop`

```lean
isAtom A Y ∧ Y ⊆ X
```

**Explicación**: Y es un átomo contenido en X.

#### `isAtomic (A : U) : Prop`

```lean
∀ X ∈ 𝒫 A, X ≠ ∅ → ∃ atom, isAtom A atom ∧ atom ⊆ X
```

**Explicación**: Un álgebra es atómica si todo elemento no vacío contiene un átomo.

### Teoremas

#### `isAtom_alt (A X : U)`

```lean
isAtom A X ↔ X ∈ 𝒫 A ∧ X ≠ ∅ ∧ ∀ Y, Y ⊂ X → Y = ∅
```

**Explicación**: Caracterización alternativa: un átomo no tiene subconjuntos propios no vacíos.

#### `singleton_subset (A x : U) (hx : x ∈ A)`

```lean
{x} ⊆ A
```

**Explicación**: Un singleton de un elemento de A es subconjunto de A.

#### `singleton_mem_PowerSet (A x : U) (hx : x ∈ A)`

```lean
{x} ∈ 𝒫 A
```

**Explicación**: Los singletons de elementos de A están en 𝒫 A.

#### `singleton_nonempty (x : U)`

```lean
{x} ≠ ∅
```

**Explicación**: Un singleton nunca es vacío.

#### `subset_singleton (x Y : U) (hY : Y ⊆ {x})`

```lean
Y = ∅ ∨ Y = {x}
```

**Explicación**: Los únicos subconjuntos de un singleton son el vacío y él mismo.

#### `singleton_is_atom (A x : U) (hx : x ∈ A)`

```lean
isAtom A {x}
```

**Explicación**: Todo singleton de un elemento de A es un átomo en 𝒫 A.

#### `atom_has_unique_element (A X : U) (hAtom : isAtom A X)`

```lean
∃! x, x ∈ X
```

**Explicación**: Todo átomo contiene exactamente un elemento.

#### `atom_is_singleton (A X : U) (hAtom : isAtom A X)`

```lean
∃ x ∈ A, X = {x}
```

**Explicación**: Todo átomo es un singleton.

#### `atom_iff_singleton (A X : U)`

```lean
isAtom A X ↔ ∃ x ∈ A, X = {x}
```

**Explicación**: Caracterización: los átomos son exactamente los singletons.

#### `Atoms_eq_singletons (A X : U)`

```lean
X ∈ Atoms A ↔ ∃ x ∈ A, X = {x}
```

**Explicación**: El conjunto de átomos es el conjunto de singletons.

#### `PowerSet_is_atomic (A : U)`

```lean
isAtomic A
```

**Explicación**: El álgebra booleana 𝒫 A es atómica.

#### `element_is_union_of_atoms (A X : U) (hX : X ∈ 𝒫 A)`

```lean
∃ F ⊆ Atoms A, X = ⋃ F
```

**Explicación**: Todo elemento de 𝒫 A es unión de átomos.

#### `singleton_below_iff (A X x : U) (hx : x ∈ A)`

```lean
atomBelow A X {x} ↔ x ∈ X
```

**Explicación**: Un singleton está contenido en X si y solo si su único elemento está en X.

---

## GeneralizedDistributive

**Namespace**: `SetUniverse.GeneralizedDistributive`

**Descripción**: Leyes de distributividad generalizadas entre operaciones binarias y familias de conjuntos.

### Definiciones

#### `IntersectFamily (A F : U) : U`

```lean
⋂ᴬ F := {X ∩ Y | X ∈ F, Y ∈ F}
```

**Explicación**: Familia de intersecciones binarias de miembros de F dentro de A.

#### `UnionFamily (A F : U) : U`

```lean
⋃ᴬ F := {X ∪ Y | X ∈ F, Y ∈ F}
```

**Explicación**: Familia de uniones binarias de miembros de F dentro de A.

### Teoremas

#### `inter_distrib_union (A F : U)`

```lean
A ∩ (⋃ F) = ⋃ {A ∩ X | X ∈ F}
```

**Explicación**: La intersección distribuye sobre la unión generalizada.

#### `IntersectFamily_nonempty (A F : U) (hF : F ≠ ∅)`

```lean
IntersectFamily A F ≠ ∅
```

**Explicación**: Si F es no vacía, su familia de intersecciones es no vacía.

#### `UnionFamily_nonempty (A F : U) (hF : F ≠ ∅)`

```lean
UnionFamily A F ≠ ∅
```

**Explicación**: Si F es no vacía, su familia de uniones es no vacía.

#### `union_distrib_inter (A F : U) (hF : F ≠ ∅)`

```lean
A ∪ (⋂ F) = ⋂ {A ∪ X | X ∈ F}
```

**Explicación**: La unión distribuye sobre la intersección generalizada (cuando F ≠ ∅).

#### `union_inter_distrib (A F : U)`

```lean
A ∪ (⋂ F) ⊆ ⋂ {A ∪ X | X ∈ F}
```

**Explicación**: Versión débil de distributividad (siempre válida).

#### `inter_union_distrib (A F : U) (hF : F ≠ ∅)`

```lean
A ∩ (⋃ F) ⊆ ⋃ {A ∩ X | X ∈ F}
```

**Explicación**: Versión débil de distributividad invertida.

---

## GeneralizedDeMorgan

**Namespace**: `SetUniverse.GeneralizedDeMorgan`

**Descripción**: Leyes de De Morgan generalizadas para uniones e intersecciones arbitrarias con complementos.

### Definiciones

#### `ComplementFamily (A F : U) : U`

```lean
{X ^∁[A] | X ∈ F}
```

**Explicación**: Familia de complementos relativos a A de los miembros de F.

### Teoremas

#### `inter_complement_eq_complement_union (A F : U) (hF_subsets : ∀ X ∈ F, X ⊆ A)`

```lean
(⋃ F) ^∁[A] = ⋂ {X ^∁[A] | X ∈ F}
```

**Explicación**: Primera ley de De Morgan generalizada: el complemento de la unión es la intersección de complementos.

#### `union_complement_eq_complement_inter (A F : U) (hF_nonempty : F ≠ ∅) (hF_subsets : ∀ X ∈ F, X ⊆ A)`

```lean
(⋂ F) ^∁[A] = ⋃ {X ^∁[A] | X ∈ F}
```

**Explicación**: Segunda ley de De Morgan generalizada: el complemento de la intersección es la unión de complementos.

#### `double_complement (A B : U) (hB_sub : B ⊆ A)`

```lean
(B ^∁[A]) ^∁[A] = B
```

**Explicación**: Doble complementación: el complemento del complemento es el conjunto original.

#### `union_subsets (F A : U) (hF_subsets : ∀ X ∈ F, X ⊆ A)`

```lean
⋃ F ⊆ A
```

**Explicación**: Si todos los miembros de F son subconjuntos de A, su unión también lo es.

#### `complement_inter_complement_eq_union (A F : U) (hF_subsets : ∀ X ∈ F, X ⊆ A)`

```lean
⋂ {X ^∁[A] | X ∈ F} = (⋃ F) ^∁[A]
```

**Explicación**: Versión inversa de la primera ley de De Morgan.

#### `inter_subsets (F A : U) (hF_nonempty : F ≠ ∅) (hF_subsets : ∀ X ∈ F, X ⊆ A)`

```lean
⋂ F ⊆ A
```

**Explicación**: Si todos los miembros de F son subconjuntos de A, su intersección también lo es.

#### `complement_union_complement_eq_inter (A F : U) (hF_nonempty : F ≠ ∅) (hF_subsets : ∀ X ∈ F, X ⊆ A)`

```lean
⋃ {X ^∁[A] | X ∈ F} = (⋂ F) ^∁[A]
```

**Explicación**: Versión inversa de la segunda ley de De Morgan.

---

## NaturalNumbers

**Namespace**: `SetUniverse.NaturalNumbers`

**Descripción**: Los números naturales como ordinales de von Neumann. Define el Axioma de Infinito y el conjunto ω de números naturales.

### Axiomas

#### `Infinity`

```lean
∃ (I : U), isInductive I
```

**Explicación**: Axioma de Infinito: existe un conjunto inductivo (que contiene ∅ y es cerrado bajo la operación sucesor).

### Definiciones

#### `σ (x : U) : U`

```lean
σ(x) := x ∪ {x}
```

**Explicación**: Función sucesor: σ(n) es n junto con {n}, representando n+1.

#### `isTransitive (x : U) : Prop`

```lean
∀ y ∈ x, y ⊆ x
```

**Explicación**: x es transitivo si cada elemento es subconjunto de x.

#### `isInductive (I : U) : Prop`

```lean
∅ ∈ I ∧ ∀ x ∈ I, σ(x) ∈ I
```

**Explicación**: I es inductivo si contiene el vacío y es cerrado bajo sucesor.

#### `ω : U`

```lean
ω := ⋂ {I | isInductive I}
```

**Explicación**: El conjunto de números naturales: la intersección de todos los conjuntos inductivos (el menor conjunto inductivo).

#### `zero : U`

```lean
0 := ∅
```

**Explicación**: El número natural 0 es el conjunto vacío.

#### `one : U`

```lean
1 := σ(0) = {∅}
```

**Explicación**: El número natural 1 es {0}.

#### `two : U`

```lean
2 := σ(1) = {0, 1}
```

**Explicación**: El número natural 2 es {0, 1}.

#### `three : U`

```lean
3 := σ(2) = {0, 1, 2}
```

**Explicación**: El número natural 3 es {0, 1, 2}.

### Teoremas Principales

#### `σ_is_specified (x y : U)`

```lean
y ∈ σ(x) ↔ y ∈ x ∨ y = x
```

**Explicación**: Un elemento está en el sucesor si está en x o es igual a x.

#### `mem_σ_self (x : U)`

```lean
x ∈ σ(x)
```

**Explicación**: Todo conjunto está en su propio sucesor.

#### `σ_nonempty (x : U)`

```lean
σ(x) ≠ ∅
```

**Explicación**: El sucesor nunca es vacío.

#### `empty_is_transitive`

```lean
isTransitive ∅
```

**Explicación**: El vacío es transitivo (vacuamente).

#### `σ_preserves_transitive (a : U) (ha : isTransitive a)`

```lean
isTransitive (σ(a))
```

**Explicación**: El sucesor de un conjunto transitivo es transitivo.

#### `ω_is_specified (x : U)`

```lean
x ∈ ω ↔ ∀ J : U, isInductive J → x ∈ J
```

**Explicación**: x está en ω si y solo si está en todo conjunto inductivo.

#### `ω_is_inductive`

```lean
isInductive ω
```

**Explicación**: ω es inductivo.

#### `ω_minimal (I : U) (hI : isInductive I)`

```lean
ω ⊆ I
```

**Explicación**: ω es el menor conjunto inductivo.

#### `zero_in_ω`

```lean
∅ ∈ ω
```

**Explicación**: 0 es un número natural.

#### `σ_closed_in_ω (x : U) (hx : x ∈ ω)`

```lean
σ(x) ∈ ω
```

**Explicación**: ω es cerrado bajo sucesor.

#### `induction_principle (P : U → Prop) (hbase : P ∅) (hstep : ∀ n ∈ ω, P n → P (σ(n)))`

```lean
∀ n ∈ ω, P n
```

**Explicación**: Principio de inducción matemática: si P vale para 0 y se preserva por sucesor, vale para todos los naturales.

#### `ω_elements_transitive`

```lean
∀ n ∈ ω, isTransitive n
```

**Explicación**: Cada número natural es un conjunto transitivo.

#### `mem_σ_implies_subseteq (n m : U) (hn : isTransitive n) (hm : m ∈ σ(n))`

```lean
m ⊆ n
```

**Explicación**: Si n es transitivo y m ∈ σ(n), entonces m ⊆ n.

#### `ω_no_self_membership`

```lean
∀ n ∈ ω, n ∉ n
```

**Explicación**: Ningún número natural se pertenece a sí mismo.

#### `ω_no_membership_cycle (m n : U) (hn : n ∈ ω) (hm_in_n : m ∈ n)`

```lean
n ∉ m
```

**Explicación**: No hay ciclos de pertenencia en los naturales: si m ∈ n, entonces n ∉ m.

#### `σ_injective_on_ω (x y : U) (hx : x ∈ ω) (hy : y ∈ ω) (h : σ(x) = σ(y))`

```lean
x = y
```

**Explicación**: La función sucesor es inyectiva en ω.

#### `zero_not_σ (n : U)`

```lean
σ(n) ≠ ∅
```

**Explicación**: Cero no es sucesor de ningún número.

#### `one_eq_singleton_zero`

```lean
1 = {0}
```

**Explicación**: Uno es el singleton de cero.

#### `zero_ne_one`

```lean
0 ≠ 1
```

**Explicación**: Cero y uno son distintos.

#### `one_ne_two`

```lean
1 ≠ 2
```

**Explicación**: Uno y dos son distintos.

#### `ω_is_transitive_set`

```lean
isTransitive ω
```

**Explicación**: El conjunto ω es transitivo como conjunto.

#### `ω_transitive (n m : U) (hnm : n ∈ m) (hm : m ∈ ω)`

```lean
n ∈ ω
```

**Explicación**: Si m es natural y n ∈ m, entonces n también es natural.

#### `ω_zero_or_σ (n : U) (hn : n ∈ ω)`

```lean
n = 0 ∨ ∃ m ∈ ω, n = σ(m)
```

**Explicación**: Todo natural es 0 o sucesor de otro natural (requiere axioma de fundación para la demostración completa).

---

## Cardinality

**Namespace**: `SetUniverse.Cardinality`

**Descripción**: Teoría de cardinalidad: Teorema de Cantor y Teorema de Cantor-Schröder-Bernstein.

### Definiciones

#### `DiagonalSet (f A : U) : U`

```lean
{x ∈ A | x ∉ f⦅x⦆}
```

**Explicación**: Conjunto diagonal de Cantor: elementos de A que no pertenecen a su propia imagen.

#### `singletonMap (A : U) : U`

```lean
{⟨x, {x}⟩ | x ∈ A}
```

**Explicación**: Función que mapea cada elemento al singleton que lo contiene.

#### `SetDiff (A B : U) : U`

```lean
A \ B
```

**Explicación**: Diferencia de conjuntos (redefinición para el contexto de CSB).

#### `isCSB_closed (f g A B X : U) : Prop`

```lean
X ⊆ A ∧ (A \ Ran(g)) ⊆ X ∧ Im(f, X) ⊆ X
```

**Explicación**: X es cerrado bajo el operador de CSB si contiene A \ Ran(g) y su imagen por f.

#### `CSB_core (f g A B : U) : U`

```lean
⋂ {X | isCSB_closed f g A B X}
```

**Explicación**: Núcleo de CSB: el menor conjunto cerrado bajo el operador.

#### `CSB_bijection (f g A B : U) : U`

```lean
Función que usa f en CSB_core y g⁻¹ fuera de él
```

**Explicación**: La biyección construida en la prueba de Cantor-Schröder-Bernstein.

### Teoremas Principales

#### `DiagonalSet_not_in_range (f A : U) (hf : isFunctionFromTo f A (𝒫 A))`

```lean
DiagonalSet f A ∉ Ran f
```

**Explicación**: El conjunto diagonal nunca está en el rango de f.

#### `cantor_no_surjection (f A : U) (hf : isFunctionFromTo f A (𝒫 A))`

```lean
¬isSurjectiveOnto f (𝒫 A)
```

**Explicación**: Teorema de Cantor: no existe sobreyección de A sobre 𝒫 A.

#### `cantor_no_bijection (f A : U) (hf : isFunctionFromTo f A (𝒫 A))`

```lean
¬isBijection f A (𝒫 A)
```

**Explicación**: No existe biyección entre A y 𝒫 A.

#### `singletonMap_is_function (A : U)`

```lean
isFunctionFromTo (singletonMap A) A (𝒫 A)
```

**Explicación**: El mapeo a singletons es una función de A a 𝒫 A.

#### `singletonMap_is_injective (A : U)`

```lean
isInjective (singletonMap A)
```

**Explicación**: El mapeo a singletons es inyectivo.

#### `A_dominated_by_PowerSet (A : U)`

```lean
A ≼ₛ 𝒫 A
```

**Explicación**: Todo conjunto está dominado por su conjunto potencia.

#### `PowerSet_not_dominated_by_A (A : U)`

```lean
¬(𝒫 A ≼ₛ A)
```

**Explicación**: El conjunto potencia no está dominado por el conjunto original.

#### `cantor_strict_dominance (A : U)`

```lean
A ≺ₛ 𝒫 A
```

**Explicación**: Teorema de Cantor en términos cardinales: A es estrictamente dominado por 𝒫 A.

#### `cantor_not_equipotent (A : U)`

```lean
¬(A ≃ₛ 𝒫 A)
```

**Explicación**: A y 𝒫 A no son equipotentes.

#### `CSB_bijection_is_bijection (f g A B : U) (hf : isFunctionFromTo f A B ∧ isInjective f) (hg : isFunctionFromTo g B A ∧ isInjective g)`

```lean
isBijection (CSB_bijection f g A B) A B
```

**Explicación**: La construcción de CSB produce efectivamente una biyección.

#### `cantor_schroeder_bernstein (A B : U) (hab : A ≼ₛ B) (hba : B ≼ₛ A)`

```lean
A ≃ₛ B
```

**Explicación**: Teorema de Cantor-Schröder-Bernstein: si A ≼ₛ B y B ≼ₛ A, entonces A ≃ₛ B.

#### `dominated_antisymm (A B : U)`

```lean
A ≼ₛ B → B ≼ₛ A → A ≃ₛ B
```

**Explicación**: La dominación cardinal es antisimétrica módulo equipotencia.

---

## Resumen de Axiomas ZFC Implementados

El proyecto implementa los siguientes axiomas de ZFC:

1. **Extensionalidad** (`Extension.lean`): Dos conjuntos son iguales si tienen los mismos elementos.

2. **Existencia** (`Existence.lean`): Existe el conjunto vacío.

3. **Especificación/Separación** (`Specification.lean`): Dado un conjunto y un predicado, existe el subconjunto de elementos que satisfacen el predicado.

4. **Emparejamiento** (`Pairing.lean`): Para cualesquiera dos conjuntos, existe su par no ordenado.

5. **Unión** (`Union.lean`): Para cualquier familia de conjuntos, existe su unión.

6. **Conjunto Potencia** (`PowerSet.lean`): Para cualquier conjunto, existe el conjunto de todos sus subconjuntos.

7. **Infinito** (`NaturalNumbers.lean`): Existe un conjunto inductivo (que contiene ∅ y es cerrado bajo sucesor).

Los axiomas de **Reemplazo** y **Fundación** (Regularidad) no están explícitamente implementados en el proyecto actual, aunque algunos teoremas los requieren para demostración completa (marcados con `sorry`).

---

## Estado del Proyecto

El proyecto ZfcSetTheory es una formalización en Lean 4 de la teoría de conjuntos ZFC (sin Reemplazo ni Fundación completos), incluyendo:

- Axiomas fundamentales de ZFC
- Teoría de relaciones y funciones
- Números naturales como ordinales de von Neumann
- Teoría de cardinalidad (Cantor, Cantor-Schröder-Bernstein)
- Álgebra booleana completa formada por el conjunto potencia
- Estructuras de orden en conjuntos

La mayoría de los teoremas están completamente demostrados en Lean 4, con algunas excepciones que requieren axiomas adicionales para completarse.

---

**Fecha de generación**: 8 de febrero de 2026
**Versión del proyecto**: master branch
**Herramienta**: Lean 4
