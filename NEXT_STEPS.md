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

## 🔧 Prioridad Media

### 3. Relaciones como Subconjuntos del Producto Cartesiano

**Objetivo**: Formalizar relaciones binarias R ⊆ A × B.

```lean
def isRelationOn (R A B : U) : Prop := R ⊆ A × B
```

**Teoremas a demostrar**:

- [ ] `domain_subset`: domain(R) ⊆ A
- [ ] `range_subset`: range(R) ⊆ B
- [ ] `relation_composition`: Composición de relaciones R ∘ S
- [ ] `inverse_relation`: R⁻¹ para relaciones

---

### 4. Funciones como Relaciones Funcionales

**Mejoras sobre lo existente en Pairing.lean**:

- [ ] `function_graph`: Gráfico de una función
- [ ] `function_composition`: f ∘ g
- [ ] `identity_function`: id_A
- [ ] `inverse_function`: f⁻¹ para funciones biyectivas
- [ ] `image_of_set`: f[A] = {f(x) : x ∈ A}
- [ ] `preimage_of_set`: f⁻¹[B] = {x : f(x) ∈ B}

---

### 5. N-tuplas y Productos Finitos

```lean
-- Ternos
def Triple (a b c : U) : U := ⟨⟨a, b⟩, c⟩

-- Producto de n conjuntos
def FiniteProduct (sets : List U) : U := ...
```

---

## 📚 Prioridad Baja (Futuro)

### 6. Axioma del Infinito

```lean
axiom Infinity : ∃ (I : U), ∅ ∈ I ∧ ∀ x, x ∈ I → x ∪ {x} ∈ I
```

**Construcciones derivadas**:

- Números naturales como conjuntos de von Neumann
- Inducción sobre ω
- Aritmética básica

---

### 7. Axioma de Reemplazo

```lean
axiom Replacement : ∀ (A : U) (F : U → U), 
  (∀ x, x ∈ A → ∃! y, F x = y) → 
  ∃ B, ∀ y, y ∈ B ↔ ∃ x, x ∈ A ∧ F x = y
```

---

### 8. Axioma de Fundación (Regularidad)

```lean
axiom Foundation : ∀ (A : U), A ≠ ∅ → ∃ x, x ∈ A ∧ x ∩ A = ∅
```

---

### 9. Axioma de Elección

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
| Par Ordenado | Completo | ▓▓▓▓▓▓▓▓▓ 100% |
| Producto Cartesiano | Completo | ▓▓▓▓▓▓▓▓▓ 100% |
| Relaciones | Básico | ▓▓▓▓░░░░░ 40% |
| Funciones | Básico | ▓▓▓▓░░░░░ 40% |

---

## 🗓️ Hoja de Ruta Sugerida

### Fase 1 (Actual): Consolidación

- [x] Axioma del Conjunto Potencia
- [x] Extensiones del Par Ordenado
- [x] Producto Cartesiano
- [x] Completar Álgebra de Boole

### Fase 2: Estructuras

- [ ] Relaciones sobre productos cartesianos
- [ ] Funciones mejoradas
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
