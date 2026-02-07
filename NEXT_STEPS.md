# Próximos Pasos - ZfcSetTheory

**Última actualización:** 7 de febrero de 2026

Este documento describe las tareas pendientes y la hoja de ruta del proyecto.

---

## 🎯 Prioridad Alta

### 1. Producto Cartesiano (CartesianProduct.lean)

**Objetivo**: Definir A × B como el conjunto de todos los pares ordenados ⟨a, b⟩ con a ∈ A y b ∈ B.

```lean
-- Definición usando Especificación y Potencia
def CartesianProduct (A B : U) : U := 
  SpecSet (𝒫 (𝒫 (A ∪ B))) (fun p => isOrderedPair p ∧ fst p ∈ A ∧ snd p ∈ B)

notation:70 A:71 " × " B:71 => CartesianProduct A B
```

**Teoremas a demostrar**:

- [ ] `CartesianProduct_is_specified`: ⟨a, b⟩ ∈ A × B ↔ a ∈ A ∧ b ∈ B
- [ ] `CartesianProduct_empty_left`: ∅ × B = ∅
- [ ] `CartesianProduct_empty_right`: A × ∅ = ∅
- [ ] `CartesianProduct_mono`: A ⊆ A' → B ⊆ B' → A × B ⊆ A' × B'
- [ ] `CartesianProduct_distrib_union_left`: (A ∪ B) × C = (A × C) ∪ (B × C)
- [ ] `CartesianProduct_distrib_union_right`: A × (B ∪ C) = (A × B) ∪ (A × C)

**Dependencias**: `OrderedPair_in_PowerSet` (✅ completado)

---

### 2. Completar Álgebra de Boole

**Teoremas pendientes** (ver [BOOLEAN_ALGEBRA_PLAN.md](BOOLEAN_ALGEBRA_PLAN.md)):

- [ ] `Inter_absorb_union`: A ∩ (A ∪ B) = A
- [ ] `Union_distrib_inter`: A ∪ (B ∩ C) = (A ∪ B) ∩ (A ∪ C)
- [ ] `Inter_distrib_union`: A ∩ (B ∪ C) = (A ∩ B) ∪ (A ∩ C)
- [ ] `Complement_union`: A ∪ (C \ A) = C (si A ⊆ C)
- [ ] `Complement_inter`: A ∩ (C \ A) = ∅
- [ ] `DeMorgan_union`: C \ (A ∪ B) = (C \ A) ∩ (C \ B)
- [ ] `DeMorgan_inter`: C \ (A ∩ B) = (C \ A) ∪ (C \ B)

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
| Álgebra Booleana | 23/30 | ▓▓▓▓▓▓▓░░ 77% |
| Par Ordenado | Completo | ▓▓▓▓▓▓▓▓▓ 100% |
| Producto Cartesiano | Pendiente | ░░░░░░░░░ 0% |
| Relaciones | Básico | ▓▓▓▓░░░░░ 40% |
| Funciones | Básico | ▓▓▓▓░░░░░ 40% |

---

## 🗓️ Hoja de Ruta Sugerida

### Fase 1 (Actual): Consolidación

- [x] Axioma del Conjunto Potencia
- [x] Extensiones del Par Ordenado
- [ ] Producto Cartesiano
- [ ] Completar Álgebra de Boole

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
