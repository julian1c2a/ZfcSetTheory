# Referencia Rápida - ZfcSetTheory

## Notación y Sintaxis

### Operadores Básicos
- `x ∈ A` - Pertenencia
- `A ⊆ B` - Subconjunto (incluye igualdad)
- `A ⊂ B` - Subconjunto propio
- `A ⟂ B` - Conjuntos disjuntos
- `∅` - Conjunto vacío

### Construcciones de Conjuntos
- `{a}` - Singleton
- `{a, b}` - Par no ordenado
- `⟨a, b⟩` - Par ordenado (Kuratowski: `{{a}, {a, b}}`)
- `𝒫 A` - Conjunto potencia
- `A ×ₛ B` - Producto cartesiano

### Operaciones Binarias
- `A ∪ B` - Unión binaria (`BinUnion`)
- `A ∩ B` - Intersección binaria (`BinInter`)
- `A \ B` - Diferencia (`Difference`)
- `A △ B` - Diferencia simétrica (`SymmetricDifference`)

### Operaciones sobre Familias
- `⋃ F` - Unión de familia (`UnionSet`)
- `⋂ F` - Intersección de familia (`InterSet`)

### Funciones y Relaciones
- `f⦅x⦆` - Aplicación de función (`apply f x`)
- `𝟙 A` - Función identidad (`IdFunction A`)
- `g ∘ₛ f` - Composición de funciones (`FunctionComposition g f`)
- `f⁻¹ˢ` - Función inversa (`InverseFunction f`)
- `f⦃X⦄` - Imagen directa (`ImageSet f X`)
- `A ≃ₛ B` - Equipotencia (`isEquipotent A B`)
- `A ≼ₛ B` - Dominación (`isDominatedBy A B`)
- `A ≺ₛ B` - Dominación estricta (`isStrictlyDominatedBy A B`)

## Axiomas ZFC

1. **Extensionalidad**: `∀ A B, (∀ x, x ∈ A ↔ x ∈ B) → A = B`
2. **Existencia**: `∃ A, ∀ x, x ∉ A` (conjunto vacío)
3. **Especificación**: `∀ A P, ∃ B, ∀ x, x ∈ B ↔ (x ∈ A ∧ P x)`
4. **Par**: `∀ a b, ∃ A, ∀ x, x ∈ A ↔ (x = a ∨ x = b)`
5. **Unión**: `∀ F, ∃ A, ∀ x, x ∈ A ↔ (∃ B ∈ F, x ∈ B)`
6. **Conjunto Potencia**: `∀ A, ∃ B, ∀ x, x ∈ B ↔ x ⊆ A`

## Definiciones Principales

### Funciones
- `isSingleValued f` - f es univaluada (funcional)
- `isFunctionFromTo f A B` - f es función de A a B
- `Dom f` - Dominio de f
- `Ran f` - Rango (imagen) de f
- `isInjective f` - f es inyectiva
- `isSurjectiveOnto f B` - f es suryectiva sobre B
- `isBijection f A B` - f es biyección de A a B

### Cardinalidad
- `isEquipotent A B` - A y B son equipotentes (mismo cardinal)
- `isDominatedBy A B` - A es dominado por B (|A| ≤ |B|)
- `isStrictlyDominatedBy A B` - A es estrictamente dominado por B

### Álgebra de Boole
- `isAtom A X` - X es átomo en 𝒫(A)
- `isAtomic A` - 𝒫(A) es álgebra de Boole atómica

## Teoremas Principales

### Álgebra de Conjuntos

#### Leyes Básicas
- **Idempotencia**: `A ∪ A = A`, `A ∩ A = A`
- **Conmutatividad**: `A ∪ B = B ∪ A`, `A ∩ B = B ∩ A`
- **Asociatividad**: `(A ∪ B) ∪ C = A ∪ (B ∪ C)`
- **Absorción**: `A ∪ (A ∩ B) = A`, `A ∩ (A ∪ B) = A`

#### Distributividad
- **Básica**: `A ∪ (B ∩ C) = (A ∪ B) ∩ (A ∪ C)`
- **Dual**: `A ∩ (B ∪ C) = (A ∩ B) ∪ (A ∩ C)`

#### Leyes de De Morgan
- **Unión**: `C \ (A ∪ B) = (C \ A) ∩ (C \ B)`
- **Intersección**: `C \ (A ∩ B) = (C \ A) ∪ (C \ B)`

### Producto Cartesiano

#### Propiedades Básicas
- `⟨a, b⟩ ∈ A ×ₛ B ↔ a ∈ A ∧ b ∈ B`
- `∅ ×ₛ B = ∅`, `A ×ₛ ∅ = ∅`
- **Monotonía**: `A ⊆ A' → B ⊆ B' → A ×ₛ B ⊆ A' ×ₛ B'`

#### Distributividad
- `(A ∪ B) ×ₛ C = (A ×ₛ C) ∪ (B ×ₛ C)`
- `A ×ₛ (B ∪ C) = (A ×ₛ B) ∪ (A ×ₛ C)`
- `(A ∩ B) ×ₛ C = (A ×ₛ C) ∩ (B ×ₛ C)`
- `A ×ₛ (B ∩ C) = (A ×ₛ B) ∩ (A ×ₛ C)`

### Funciones

#### Composición
- **Asociatividad**: `(h ∘ₛ g) ∘ₛ f = h ∘ₛ (g ∘ₛ f)`
- **Identidad**: `f ∘ₛ 𝟙 A = f`, `𝟙 B ∘ₛ f = f`
- **Preserva propiedades**: composición de inyectivas es inyectiva

#### Aplicación
- `apply_eq`: Si f es univaluada y `⟨x, y⟩ ∈ f`, entonces `f⦅x⦆ = y`
- `apply_id`: `(𝟙 A)⦅x⦆ = x` para `x ∈ A`

#### Inversa
- `inverse_is_specified`: `⟨y, x⟩ ∈ f⁻¹ˢ ↔ ⟨x, y⟩ ∈ f`
- `inverse_inverse`: `(f⁻¹ˢ)⁻¹ˢ = f` para relaciones en `A ×ₛ B`

#### Imagen y Preimagen
- `ImageSet_is_specified`: `y ∈ f⦃X⦄ ↔ ∃ x, x ∈ X ∧ ⟨x, y⟩ ∈ f`
- `image_union`: `f⦃A ∪ B⦄ = f⦃A⦄ ∪ f⦃B⦄`
- `preimage_union`: `f⁻¹[A ∪ B] = f⁻¹[A] ∪ f⁻¹[B]`

### Equipotencia y Dominación

#### Propiedades de Equivalencia
- **Reflexiva**: `A ≃ₛ A`
- **Simétrica**: `A ≃ₛ B → B ≃ₛ A`
- **Transitiva**: `A ≃ₛ B → B ≃ₛ C → A ≃ₛ C`

#### Propiedades de Preorden
- **Reflexiva**: `A ≼ₛ A`
- **Transitiva**: `A ≼ₛ B → B ≼ₛ C → A ≼ₛ C`

#### Equivalencias Importantes
- `bijection_iff_invertible`: `isBijection f A B ↔ isInvertible f A B`
- `equipotent_implies_dominated_both`: `A ≃ₛ B → (A ≼ₛ B ∧ B ≼ₛ A)`

### Álgebra de Boole Atómica

#### Caracterización de Átomos
- `atom_iff_singleton`: `isAtom A X ↔ ∃ x, x ∈ A ∧ X = {x}`
- `singleton_is_atom`: `{x}` es átomo en `𝒫(A)` cuando `x ∈ A`
- `atom_is_singleton`: Todo átomo es un singleton

#### Atomicidad
- `PowerSet_is_atomic`: `𝒫(A)` es álgebra de Boole atómica
- `element_is_union_of_atoms`: Todo elemento es unión de átomos

### Cardinalidad

#### Teorema de Cantor
- `cantor_no_surjection`: No existe suryección `A → 𝒫(A)`
- `cantor_strict_dominance`: `A ≺ₛ 𝒫(A)`
- `cantor_not_equipotent`: `A` y `𝒫(A)` no son equipotentes

#### Cantor-Schröder-Bernstein
- `cantor_schroeder_bernstein`: `A ≼ₛ B ∧ B ≼ₛ A → A ≃ₛ B`
- `dominated_antisymm`: `≼ₛ` es antisimétrica módulo equipotencia

## Patrones de Demostración Comunes

### Igualdad de Conjuntos
```lean
apply ExtSet
intro x
constructor
· intro h
  -- demostrar x ∈ B
· intro h
  -- demostrar x ∈ A
```

### Funciones
```lean
-- Para demostrar que f es función:
refine ⟨?_, ?_, ?_⟩
· -- f ⊆ A ×ₛ B
· -- f es total en A
· -- f es univaluada
```

### Biyecciones
```lean
-- Para demostrar biyección:
refine ⟨función, inyectiva, suryectiva⟩
```

### Equipotencia
```lean
-- Para demostrar A ≃ₛ B:
use f  -- función biyectiva
exact ⟨función_de_A_a_B, es_biyección⟩
```

## Archivos por Tema

| Tema | Archivo | Contenido Principal |
|------|---------|-------------------|
| Fundamentos | `Prelim.lean`, `Extension.lean` | Extensionalidad, subconjuntos |
| Operaciones básicas | `Existence.lean`, `Specification.lean` | Conjunto vacío, especificación |
| Construcciones | `Pairing.lean`, `Union.lean`, `PowerSet.lean` | Pares, uniones, potencia |
| Productos | `OrderedPair.lean`, `CartesianProduct.lean` | Pares ordenados, productos |
| Relaciones | `Relations.lean` | Equivalencia, orden |
| Funciones | `Functions.lean` | Funciones, composición, equipotencia |
| Álgebra básica | `BooleanAlgebra.lean` | Absorción, distributividad, De Morgan |
| Álgebra avanzada | `PowerSetAlgebra.lean`, `AtomicBooleanAlgebra.lean` | Complementos, átomos |
| Cardinalidad | `Cardinality.lean` | Cantor, Cantor-Schröder-Bernstein |

## Teoremas por Importancia

### ⭐⭐⭐ Fundamentales
- Axioma de Extensionalidad
- Teorema de Cantor
- Cantor-Schröder-Bernstein
- Leyes de De Morgan

### ⭐⭐ Importantes
- Distributividad generalizada
- Atomicidad de 𝒫(A)
- Propiedades de composición
- Equivalencia biyección ↔ invertibilidad

### ⭐ Útiles
- Monotonía del producto cartesiano
- Propiedades de imagen/preimagen
- Caracterización de átomos
- Dominación estricta

## Referencias Cruzadas

- **Funciones** → **Cardinalidad**: Inyecciones, suryecciones, biyecciones
- **Producto Cartesiano** → **Funciones**: Dominio y codominio
- **Álgebra de Boole** → **Átomos**: Estructura atómica de 𝒫(A)
- **Equipotencia** → **Cantor**: Límites de equipotencia
- **Especificación** → **Imagen/Preimagen**: Construcción de conjuntos
