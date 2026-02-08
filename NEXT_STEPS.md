# Próximos Pasos - ZfcSetTheory

**Última actualización:** 7 de febrero de 2026

Este documento describe las tareas pendientes y la hoja de ruta del proyecto.

---

## 🎯 Prioridad Alta

### 1. ~~Producto Cartesiano (CartesianProduct.lean)~~ ✅ COMPLETADO

**Definición implementada**:

```lean
noncomputable def CartesianProduct (A B : U) : U :=
  SpecSet (𝒫 (𝒫 (A ∪ B))) (fun p => isOrderedPair p ∧ fst p ∈ A ∧ snd p ∈ B)

notation:70 A:71 " ×ₛ " B:71 => CartesianProduct A B
```

**Teoremas implementados**:

- [x] `CartesianProduct_is_specified`: p ∈ A ×ₛ B ↔ isOrderedPair p ∧ fst p ∈ A ∧ snd p ∈ B
- [x] `OrderedPair_mem_CartesianProduct`: ⟨a, b⟩ ∈ A ×ₛ B ↔ a ∈ A ∧ b ∈ B
- [x] `CartesianProduct_empty_left`: ∅ ×ₛ B = ∅
- [x] `CartesianProduct_empty_right`: A ×ₛ ∅ = ∅
- [x] `CartesianProduct_mono`: A ⊆ A' → B ⊆ B' → A ×ₛ B ⊆ A' ×ₛ B'
- [x] `CartesianProduct_distrib_union_left`: (A ∪ B) ×ₛ C = (A ×ₛ C) ∪ (B ×ₛ C)
- [x] `CartesianProduct_distrib_union_right`: A ×ₛ (B ∪ C) = (A ×ₛ B) ∪ (A ×ₛ C)
- [x] `CartesianProduct_distrib_inter_left`: (A ∩ B) ×ₛ C = (A ×ₛ C) ∩ (B ×ₛ C)
- [x] `CartesianProduct_distrib_inter_right`: A ×ₛ (B ∩ C) = (A ×ₛ B) ∩ (A ×ₛ C)

---

### 2. ~~Completar Álgebra de Boole~~ ✅ COMPLETADO

**Todos los teoremas implementados** en [BooleanAlgebra.lean](ZfcSetTheory/BooleanAlgebra.lean):

- [x] `BinInter_absorb_union`: A ∩ (A ∪ B) = A
- [x] `BinUnion_distrib_inter`: A ∪ (B ∩ C) = (A ∪ B) ∩ (A ∪ C)
- [x] `BinInter_distrib_union`: A ∩ (B ∪ C) = (A ∩ B) ∪ (A ∩ C)
- [x] `Complement_union`: A ∪ (C \ A) = C (si A ⊆ C)
- [x] `Complement_inter`: A ∩ (C \ A) = ∅
- [x] `DeMorgan_union`: C \ (A ∪ B) = (C \ A) ∩ (C \ B)
- [x] `DeMorgan_inter`: C \ (A ∩ B) = (C \ A) ∪ (C \ B)

---

### 3. ~~Leyes de De Morgan Generalizadas~~ ✅ COMPLETADO

**Implementado en GeneralizedDeMorgan.lean y PowerSetAlgebra.lean**:

- [x] `ComplementFamily A F` - Familia de complementos { A \ X | X ∈ F }
- [x] `complement_union_eq_inter_complement` - A \ ⋃ F = ⋂ (A \ F)
- [x] `complement_inter_eq_union_complement` - A \ ⋂ F = ⋃ (A \ F)
- [x] Versiones duales e inversas

---

### 4. ~~Leyes Distributivas Generalizadas~~ ✅ COMPLETADO

**Implementado en GeneralizedDistributive.lean**:

- [x] `DistribSet X F op` - Conjunto imagen { op(X, Y) | Y ∈ F }
- [x] `inter_union_distrib` - X ∩ (⋃ F) = ⋃ { X ∩ Y | Y ∈ F }
- [x] `union_inter_distrib` - X ∪ (⋂ F) = ⋂ { X ∪ Y | Y ∈ F }
- [x] Versiones conmutativas

---

### 5. ~~Álgebra de Boole Atómica~~ ✅ COMPLETADO

**Implementado en AtomicBooleanAlgebra.lean**:

- [x] `isAtom A X` - X es un átomo en 𝒫(A)
- [x] `Atoms A` - Conjunto de todos los átomos
- [x] `isAtomic A` - 𝒫(A) es atómica
- [x] `singleton_is_atom` - {x} es átomo cuando x ∈ A
- [x] `atom_is_singleton` - Todo átomo es un singleton  
- [x] `atom_iff_singleton` - Caracterización completa
- [x] `PowerSet_is_atomic` - 𝒫(A) es álgebra de Boole atómica
- [x] `element_is_union_of_atoms` - Todo elemento es unión de átomos

---

### 6. ~~Teoría de Cardinalidad~~ ✅ COMPLETADO

**Implementado en Cardinality.lean**:

**Teorema de Cantor:**

- [x] `DiagonalSet f A` - Conjunto diagonal { x ∈ A | x ∉ f⦅x⦆ }
- [x] `DiagonalSet_not_in_range` - D ∉ rango(f)
- [x] `cantor_no_surjection` - No existe suryección f: A → 𝒫(A)
- [x] `cantor_no_bijection` - No existe biyección A ↔ 𝒫(A)
- [x] `singletonMap` - Mapa canónico x ↦ {x}
- [x] `singletonMap_is_injective` - El mapa singleton es inyectivo
- [x] `cantor_strict_dominance` - A se inyecta en 𝒫(A) pero no viceversa
- [x] `cantor_not_equipotent` - A y 𝒫(A) no son equipotentes

**Teorema de Cantor-Schröder-Bernstein:**

- [x] `SetDiff A B` - Diferencia A ∖ B
- [x] `isCSB_closed f g A B C` - C es cerrado bajo g ∘ f
- [x] `CSB_core f g A B` - Núcleo cerrado mínimo
- [x] `CSB_bijection f g A B` - Biyección construida
- [x] `CSB_bijection_is_bijection` - La construcción produce biyección
- [x] `cantor_schroeder_bernstein` - Si ∃ inyecciones f: A → B y g: B → A, entonces ∃ biyección A ↔ B

---

## 🔧 Prioridad Media

### 7. Funciones como Relaciones Funcionales

**Mejoras sobre lo existente en Pairing.lean**:

- [ ] `function_graph`: Gráfico de una función
- [ ] `function_composition`: f ∘ g
- [ ] `identity_function`: id_A
- [ ] `inverse_function`: f⁻¹ para funciones biyectivas
- [ ] `image_of_set`: f[A] = {f(x) : x ∈ A}
- [ ] `preimage_of_set`: f⁻¹[B] = {x : f(x) ∈ B}

---

### 8. N-tuplas y Productos Finitos

```lean
-- Ternos
def Triple (a b c : U) : U := ⟨⟨a, b⟩, c⟩

-- Producto de n conjuntos
def FiniteProduct (sets : List U) : U := ...
```

---

## 📚 Prioridad Baja (Futuro)

### 9. Axioma del Infinito

```lean
axiom Infinity : ∃ (I : U), ∅ ∈ I ∧ ∀ x, x ∈ I → x ∪ {x} ∈ I
```

**Construcciones derivadas**:

- Números naturales como conjuntos de von Neumann
- Inducción sobre ω
- Aritmética básica

---

### 10. Axioma de Reemplazo

```lean
axiom Replacement : ∀ (A : U) (F : U → U), 
  (∀ x, x ∈ A → ∃! y, F x = y) → 
  ∃ B, ∀ y, y ∈ B ↔ ∃ x, x ∈ A ∧ F x = y
```

---

### 11. Axioma de Fundación (Regularidad)

```lean
axiom Foundation : ∀ (A : U), A ≠ ∅ → ∃ x, x ∈ A ∧ x ∩ A = ∅
```

---

### 12. Axioma de Elección

```lean
axiom Choice : ∀ (A : U), 
  (∀ x, x ∈ A → x ≠ ∅) → 
  ∃ f, isFunction A f ∧ ∀ x, x ∈ A → f(x) ∈ x
```

---

## 📊 Estado Actual del Proyecto

| Componente | Estado | Progreso |
|------------|--------|----------|
| Axiomas ZFC | 6/9 | ▓▓▓▓▓▓░░░ 67% |
| Álgebra Booleana | Completo | ▓▓▓▓▓▓▓▓▓ 100% |
| De Morgan Generalizadas | Completo | ▓▓▓▓▓▓▓▓▓ 100% |
| Distributivas Generalizadas | Completo | ▓▓▓▓▓▓▓▓▓ 100% |
| Álgebra Atómica | Completo | ▓▓▓▓▓▓▓▓▓ 100% |
| Par Ordenado | Completo | ▓▓▓▓▓▓▓▓▓ 100% |
| Producto Cartesiano | Completo | ▓▓▓▓▓▓▓▓▓ 100% |
| Relaciones | Completo | ▓▓▓▓▓▓▓▓▓ 100% |
| Cardinalidad (Cantor, CSB) | Completo | ▓▓▓▓▓▓▓▓▓ 100% |
| Funciones | Básico | ▓▓▓▓░░░░░ 40% |

---

## 🗓️ Hoja de Ruta Sugerida

### Fase 1 (Actual): Consolidación ✅ COMPLETADA

- [x] Axioma del Conjunto Potencia
- [x] Extensiones del Par Ordenado
- [x] Producto Cartesiano
- [x] Completar Álgebra de Boole
- [x] Relaciones formales (Relations.lean)
- [x] De Morgan generalizadas
- [x] Distributivas generalizadas
- [x] Álgebra de Boole atómica

### Fase 2: Estructuras (En progreso)

- [x] Relaciones sobre productos cartesianos
- [x] Leyes de De Morgan generalizadas
- [x] Leyes distributivas generalizadas  
- [x] Álgebra de Boole atómica
- [x] Teoría de Cardinalidad (Cantor, CSB)
- [ ] Funciones mejoradas (composición, inversa)
- [ ] N-tuplas

### Fase 3: Infinito

- [ ] Axioma del Infinito
- [ ] Números naturales
- [ ] Inducción

### Fase 4: Completar ZFC

- [ ] Axioma de Reemplazo
- [ ] Axioma de Fundación
- [ ] Axioma de Elección (opcional)

---

## 📝 Notas de Implementación

### Patrones Recomendados

```lean
-- Para demostrar igualdad de conjuntos
apply ExtSet
intro x
constructor
· intro hx
  -- demostrar x en el segundo conjunto
· intro hx
  -- demostrar x en el primer conjunto

-- Para destructurar hipótesis
obtain ⟨a, ha⟩ := h

-- Para casos
cases h with
| inl hl => ...
| inr hr => ...
```

### Evitar

- `simp` sin argumentos específicos
- `push_neg` (no disponible)
- Nombres duplicados en destructuración

---

*Este documento se actualiza conforme avanza el proyecto.*
