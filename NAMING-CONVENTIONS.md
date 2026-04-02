# Convenciones de Nombres — Estilo Mathlib

> Documento de referencia permanente para el proyecto **ZfcSetTheory**.
> Todas las reglas se basan en las
> [Mathlib Naming Conventions](https://leanprover-community.github.io/contribute/naming.html),
> adaptadas al contexto de ZFC sobre un universo `U`.

---

## 1. Reglas de Capitalización

| Tipo de declaración | Convención | Ejemplo |
|---------------------|------------|---------|
| Teoremas, lemas (terms de `Prop`) | `snake_case` | `union_comm`, `mem_powerset_iff` |
| Types, Props, Structures, Classes | `UpperCamelCase` | `IsFunction`, `IsNat`, `BooleanAlgebra` |
| Funciones que retornan `Type` | según tipo retorno | `powerset` (→ U → `snake`), `IsNat` (→ Prop → `Upper`) |
| Otros terms de `Type` | `lowerCamelCase` | `successor`, `fromPeano`, `binUnion` |
| Acrónimos | como grupo upper/lower | `ZFC` (namespace), `zfc` (en snake_case) |

---

## 2. Diccionario de Símbolos → Palabras en Nombres

| Símbolo | En nombres | Notas |
|---------|-----------|-------|
| ∈ | `mem` | `x ∈ A` → `mem` |
| ∉ | `not_mem` | |
| ∪ | `union` | binaria |
| ∩ | `inter` | binaria |
| ⋃ | `sUnion` | `s` = "set of sets" |
| ⋂ | `sInter` | ídem |
| ⊆ | `subset` | no estricto |
| ⊂ | `ssubset` | estricto (extra `s`) |
| 𝒫 | `powerset` | |
| σ | `succ` | |
| ∅ | `empty` | |
| △ | `symmDiff` | |
| ᶜ | `compl` | complemento |
| \ | `sdiff` | set difference |
| ×ₛ | `prod` | producto cartesiano |
| ⟂ | `disjoint` | |
| = | `eq` | a menudo omitido |
| ≠ | `ne` | |
| → | `of` / implícito | la conclusión va primero |
| ↔ | `iff` | sufijo |
| ¬ | `not` | |
| ∃ | `exists` | |
| ∀ | `forall` | |
| ∘ | `comp` | composición |
| ⁻¹ | `inv` | inversa |
| + | `add` | |
| \* / · | `mul` | |
| − | `sub` (binario) / `neg` (unario) | |
| ^ | `pow` | |
| / | `div` | |
| ∣ | `dvd` | divide |
| ≤ | `le` | |
| < | `lt` | |
| ≥ | `ge` | solo para swap de argumentos |
| > | `gt` | solo para swap de argumentos |
| 0 | `zero` | |
| 1 | `one` | |

---

## 3. Reglas de Formación de Nombres (12 reglas)

### REGLA 1 — Conclusión primero, hipótesis con `_of_`

El nombre describe **qué se demuestra**, no cómo. Las hipótesis se añaden con `_of_`:

```
-- Forma del teorema: A → B → C
-- Nombre:            c_of_a_of_b
-- Orden:             conclusión_of_hipótesis1_of_hipótesis2

-- ACTUAL:   nat_successor_is_nat : isNat n → isNat (σ n)
-- NUEVO:    isNat_succ_of_isNat
--           ^^^^^^^^^ ^^^^^^^^^^^^
--           conclusión  hipótesis
--           (lo que se  (lo que se
--            demuestra)  asume)

-- ACTUAL:   nat_element_is_nat : isNat n → m ∈ n → isNat m
-- NUEVO:    isNat_of_isNat_of_mem
--           ^^^^^ ^^^^^^^ ^^^^^^
--           concl  hip.1   hip.2
--           (m es  (n es   (m ∈ n)
--            nat)   nat)
```

### REGLA 2 — Bicondicionales llevan sufijo `_iff`

```
-- ACTUAL:   PowerSet_is_specified : x ∈ (𝒫 A) ↔ x ⊆ A
-- NUEVO:    mem_powerset_iff
--           ^^^ ^^^^^^^^ ^^^
--           ∈    𝒫        ↔
--
-- Desglose: "mem"       = ∈ (pertenencia)
--           "powerset"  = 𝒫 (conjunto potencia)
--           "_iff"      = ↔ (bicondicional)

-- ACTUAL:   BinInter_empty : (x ∩ y) = ∅ ↔ x ⟂ y
-- NUEVO:    inter_eq_empty_iff_disjoint
--           ^^^^^ ^^ ^^^^^ ^^^ ^^^^^^^^
--           ∩      =   ∅    ↔    ⟂
--
-- Desglose: "inter"     = ∩
--           "eq_empty"  = = ∅
--           "_iff_"     = ↔
--           "disjoint"  = ⟂
```

### REGLA 3 — Eliminar `_wc` — Usar `.mp` / `.mpr` o `_of_`

El sufijo `_wc` (actual) se reemplaza por la convención Mathlib:

```
-- ACTUAL:   BinInter_empty_left_wc : (x ∩ y) = ∅ → x ⟂ y
-- SOLUCIÓN: Usar   inter_eq_empty_iff_disjoint.mp
--                  ^^^^^^^^^^^^^^^^^^^^^^^^^^^^.^^
--                  nombre del iff              dirección →
--
-- Si se necesita teorema separado:
-- NUEVO:    disjoint_of_inter_eq_empty
--           ^^^^^^^^^ ^^^^^^^^^^^^^^^^
--           conclusión   hipótesis
--           (x ⟂ y)     ((x ∩ y) = ∅)

-- ACTUAL:   BinInter_empty_right_wc : x ⟂ y → (x ∩ y) = ∅
-- SOLUCIÓN: Usar   inter_eq_empty_iff_disjoint.mpr
--                                              .^^^
--                                              dirección ←
--
-- Si teorema separado:
-- NUEVO:    inter_eq_empty_of_disjoint
--           ^^^^^^^^^^^^^^ ^^^^^^^^^^^
--           conclusión     hipótesis

-- ACTUAL:   ExtSet_wc (h_x_subs_y)(h_y_subs_x) : x = y
-- NUEVO:    eq_of_subset_of_subset
--           ^^ ^^^^^^^^^^ ^^^^^^^^^
--           =   ⊆ (dir →)  ⊆ (dir ←)
--
-- Desglose: "eq"           = la conclusión (x = y)
--           "of_subset"    = primera hipótesis (∀ z, z ∈ x → z ∈ y, ≈ x ⊆ y)
--           "of_subset"    = segunda hipótesis (∀ z, z ∈ y → z ∈ x, ≈ y ⊆ x)
--
-- Alt. Mathlib: Subset.antisymm (usando dot notation)

-- ACTUAL:   Difference_empty_wc : (A \ B) = ∅ → ∀ x, x ∈ A → x ∈ B
-- NUEVO:    subset_of_sdiff_eq_empty
--           ^^^^^^ ^^^^^^^^^^^^^^^^^
--           concl   hipótesis
--           (A⊆B)  (A\B = ∅)

-- ACTUAL:   Difference_subseteq_wc : (∀ x, x ∈ A → x ∈ B) → (A \ B) = ∅
-- NUEVO:    sdiff_eq_empty_of_subset
--           ^^^^^^^^^^^^^ ^^^^^^^^^
--           conclusión    hipótesis
--           (A\B = ∅)    (A ⊆ B)
```

### REGLA 4 — Propiedades algebraicas → nombre axiomático corto

```
-- ACTUAL:   BinUnion_commutative
-- NUEVO:    union_comm
--           ^^^^^ ^^^^
--           ∪     propiedad axiomática
--
-- Desglose: "union" = ∪ (operación)
--           "_comm" = conmutatividad (propiedad axiomática estándar)

-- ACTUAL:   BinInter_associative
-- NUEVO:    inter_assoc
--           ^^^^^ ^^^^^
--           ∩     propiedad axiomática

-- ACTUAL:   BinUnion_absorb_inter
-- NUEVO:    union_inter_self
--           ^^^^^ ^^^^^ ^^^^
--           ∪     ∩     A ∪ (A ∩ B) = A ("self" indica que el resultado es el propio A)
--
-- Desglose: Describe el patrón de la expresión: union de algo con inter que involucra a sí mismo
--           "_self" es el patrón Mathlib para X op X = X o simplificación con uno mismo

-- ACTUAL:   BinUnion_distrib_inter
-- NUEVO:    union_inter_distrib_left
--           ^^^^^ ^^^^^ ^^^^^^^ ^^^^
--           ∪     ∩     distribut. izquierda (el ∪ está "fuera")
--
-- Desglose: A ∪ (B ∩ C) = (A ∪ B) ∩ (A ∪ C)
--           "union"   = la operación exterior
--           "inter"   = la operación interior
--           "distrib" = propiedad de distributividad
--           "_left"   = el elemento distributivo (A) está a la izquierda

-- ACTUAL:   BinInter_distrib_union
-- NUEVO:    inter_union_distrib_left
```

**Sufijos axiomáticos estándar (Mathlib):**

| Sufijo | Significado | Ejemplo |
|--------|------------|---------|
| `_comm` | conmutatividad | `union_comm` |
| `_assoc` | asociatividad | `inter_assoc` |
| `_refl` | reflexividad | `subset_refl` |
| `_irrefl` | irreflexividad | `ssubset_irrefl` |
| `_symm` | simetría | `disjoint_symm` |
| `_trans` | transitividad | `subset_trans` |
| `_antisymm` | antisimetría | `subset_antisymm` |
| `_asymm` | asimetría | `ssubset_asymm` |
| `_inj` | inyectividad (iff) | `succ_inj` (σ a = σ b ↔ a = b) |
| `_injective` | inyectividad (pred) | `succ_injective` |
| `_self` | operación consigo mismo | `union_self` (A ∪ A = A) |
| `_left` / `_right` | variante lateral | `union_subset_left` |
| `_cancel` | cancelación | `add_left_cancel` |
| `_mono` | monotonía | `powerset_mono` |

### REGLA 5 — Predicados como prefijo, operaciones en orden infijo

```
-- ACTUAL:   successor_injective
-- NUEVO:    succ_injective
--           ^^^^ ^^^^^^^^^
--           σ    predicado como sufijo (excepción estándar Mathlib)
--
-- Desglose: "succ"      = σ (la operación)
--           "_injective" = predicado Injective (sufijo por convención Mathlib)
--           Excepción: _injective, _surjective, _bijective siempre son sufijo

-- ACTUAL:   successor_nonempty
-- NUEVO:    succ_ne_empty    o    succ_nonempty
--           ^^^^ ^^^^^^^^
--           σ    ≠ ∅
--
-- Desglose: "succ"    = σ
--           "ne"      = ≠
--           "empty"   = ∅

-- ACTUAL:   zero_is_nat
-- NUEVO:    isNat_zero
--           ^^^^^ ^^^^
--           pred   argumento
--
-- Desglose: En Mathlib, predicados como prefijo: IsNat(zero) → isNat_zero
--           La excepción (sufijo) es para _injective, _monotone, etc.

-- ACTUAL:   nat_element_is_nat
-- NUEVO:    isNat_of_isNat_of_mem
--           ^^^^^ ^^^^^^^ ^^^^^^
--           concl  hip.1   hip.2
--
-- O más corto: isNat_of_mem (si el contexto de "n es nat" es implícito)
```

### REGLA 6 — Abreviaturas estándar para condiciones frecuentes

```
-- En lugar de:         Se usa:
-- "zero_lt_x"       →  "pos"       (x > 0)
-- "x_lt_zero"       →  "neg"       (x < 0)
-- "x_le_zero"       →  "nonpos"    (x ≤ 0)
-- "zero_le_x"       →  "nonneg"    (x ≥ 0)
-- "is_zero_or_succ" →  "eq_zero_or_succ"  (patrón Mathlib: eq para =)

-- ACTUAL:   nat_is_zero_or_succ : isNat n → n = ∅ ∨ ∃ m, isNat m ∧ n = σ m
-- NUEVO:    eq_empty_or_exists_succ_of_isNat
--           ^^^^^^^^ ^^ ^^^^^^^^^^^ ^^^^^^^^
--           = ∅       ∨   ∃ σ        hipótesis
--
-- O más corto: eq_zero_or_succ (usando "zero" para ∅ en contexto de naturales)
```

### REGLA 7 — Definiciones con `Is` para predicados Prop

```
-- ACTUAL:   def isNat (n : U) : Prop := ...
-- NUEVO:    def IsNat (n : U) : Prop := ...
--               ^^^^^
--               UpperCamelCase (es un Prop, regla 2)
--
-- NOTA: En los nombres de TEOREMAS, baja a lowerCamelCase:
--       isNat_zero, isNat_succ, isNat_of_mem
--       ^^^^^ (lowerCamelCase dentro de snake_case, regla 5 Mathlib)

-- ACTUAL:   def isSingleValued (f : U) : Prop := ...
-- NUEVO:    def IsSingleValued (f : U) : Prop := ...

-- ACTUAL:   def isFunctionFromTo (f A B : U) : Prop := ...
-- NUEVO:    def IsFunction (f A B : U) : Prop := ...
--               ^^^^^^^^^^
--               Nombre simplificado + UpperCamelCase

-- ACTUAL:   def isInductive (A : U) : Prop := ...
-- NUEVO:    def IsInductive (A : U) : Prop := ...

-- ACTUAL:   def isTransitiveSet (A : U) : Prop := ...
-- NUEVO:    def IsTransitive (A : U) : Prop := ...

-- ACTUAL:   def isInitialSegment ...
-- NUEVO:    def IsInitialSegment ...
```

### REGLA 8 — Funciones/constructores no-Prop: `lowerCamelCase`

```
-- ACTUAL:   noncomputable def PowerSetOf (A : U) : U := ...
-- NUEVO:    noncomputable def powerset (A : U) : U := ...
--                             ^^^^^^^^
--                             lowerCamelCase (retorna U, no Prop)
--                             Sin "Of" (redundante)

-- ACTUAL:   noncomputable def BinUnion (x y : U) : U := ...
-- NUEVO:    noncomputable def union (x y : U) : U := ...
--                             ^^^^^
--                             "Bin" se elimina (es binaria por aridad, no necesita prefijo)

-- ACTUAL:   noncomputable def BinInter (x y : U) : U := ...
-- NUEVO:    noncomputable def inter (x y : U) : U := ...

-- ACTUAL:   noncomputable def UnionSet (F : U) : U := ...
-- NUEVO:    noncomputable def sUnion (F : U) : U := ...
--                             ^^^^^^
--                             "s" = "set" (unión de un conjunto de conjuntos)

-- ACTUAL:   noncomputable def SpecSet (A : U) (P : U → Prop) : U := ...
-- NUEVO:    noncomputable def sep (A : U) (P : U → Prop) : U := ...
--                             ^^^
--                             "sep" = "separation" (nombre Mathlib para {x ∈ A | P x})

-- ACTUAL:   noncomputable def FunctionComposition (g f : U) : U := ...
-- NUEVO:    noncomputable def comp (g f : U) : U := ...

-- ACTUAL:   noncomputable def IdFunction (A : U) : U := ...
-- NUEVO:    noncomputable def id (A : U) : U := ...

-- ACTUAL:   noncomputable def InverseFunction (f : U) : U := ...
-- NUEVO:    noncomputable def inv (f : U) : U := ...

-- ACTUAL:   noncomputable def ImageSet (f X : U) : U := ...
-- NUEVO:    noncomputable def image (f X : U) : U := ...

-- ACTUAL:   noncomputable def PreimageSet (f Y : U) : U := ...
-- NUEVO:    noncomputable def preimage (f Y : U) : U := ...

-- ACTUAL:   noncomputable def Restriction (f C : U) : U := ...
-- NUEVO:    noncomputable def restrict (f C : U) : U := ...

-- ACTUAL:   noncomputable def DiagonalSet (f A : U) : U := ...
-- NUEVO:    noncomputable def diagSet (f A : U) : U := ...
```

### REGLA 9 — Axiomas y especificaciones: `_iff` y `mem_X_iff`

El patrón `X_is_specified` se reemplaza por `mem_X_iff` (describe el contenido):

```
-- ACTUAL:   successor_is_specified : x ∈ (σ n) ↔ x ∈ n ∨ x = n
-- NUEVO:    mem_succ_iff
--           ^^^ ^^^^ ^^^
--           ∈    σ    ↔
--
-- Desglose: "mem"   = ∈ (qué se está describiendo: pertenencia)
--           "succ"  = σ (en qué conjunto: el sucesor)
--           "_iff"  = ↔ (es un bicondicional)

-- ACTUAL:   BinInter_is_specified : x ∈ (A ∩ B) ↔ x ∈ A ∧ x ∈ B
-- NUEVO:    mem_inter_iff
--           ^^^ ^^^^^ ^^^
--           ∈    ∩     ↔

-- ACTUAL:   BinUnion_is_specified : x ∈ (A ∪ B) ↔ x ∈ A ∨ x ∈ B
-- NUEVO:    mem_union_iff

-- ACTUAL:   SpecSet_is_specified : x ∈ SpecSet A P ↔ x ∈ A ∧ P x
-- NUEVO:    mem_sep_iff

-- ACTUAL:   Difference_is_specified : x ∈ (A \ B) ↔ x ∈ A ∧ x ∉ B
-- NUEVO:    mem_sdiff_iff
```

### REGLA 10 — Unicidad y existencia

```
-- ACTUAL:   BinInterUniqueSet : ∃! z, ∀ x, x ∈ z ↔ ...
-- NUEVO:    inter_unique
--           ^^^^^ ^^^^^^
--           ∩     existencia única

-- ACTUAL:   PowerSetExistsUnique
-- NUEVO:    powerset_unique

-- ACTUAL:   UnionExistsUnique
-- NUEVO:    sUnion_unique
```

### REGLA 11 — Nombres con `_left` / `_right`

```
-- ACTUAL:   BinUnion_subset_left_wc : ... → A ⊆ (A ∪ B)
-- NUEVO:    subset_union_left
--           ^^^^^^ ^^^^^ ^^^^
--           ⊆      ∪     A está a la izquierda
--
-- Desglose: La conclusión es "subset" (⊆), de un "union" (∪)
--           "_left" indica que el subconjunto es el argumento izquierdo del ∪
--           Sin _wc: si era iff se usa .mp; si era implicación pura, _of_ hipótesis

-- ACTUAL:   BinUnion_subset_right_wc : ... → B ⊆ (A ∪ B)
-- NUEVO:    subset_union_right

-- ACTUAL:   add_le_add_left : ...
-- DESGLOSE: "add"  = +
--           "le"   = ≤
--           "add"  = + (repetido porque hay + en ambos lados)
--           "_left" = el argumento que cambia está a la izquierda
```

### REGLA 12 — Cantor y teoremas importantes — nombre descriptivo

```
-- ACTUAL:   cantor_no_surjection
-- NUEVO:    cantor_no_surjection   (nombre propio + descripción, OK en Mathlib)
--           ^^^^^^ ^^ ^^^^^^^^^^
--           nombre  no  surjección
--           propio     (descripción de la conclusión)

-- ACTUAL:   cantor_strict_dominance
-- NUEVO:    cantor_strict_dominance  (correcto)

-- ACTUAL:   cantor_schroeder_bernstein
-- NUEVO:    cantor_schroeder_bernstein  (correcto, nombre propio)
```

> **NOTA:** Los nombres propios matemáticos se mantienen tal cual en Mathlib.
> Solo se normalizan las palabras operacionales (`mem`, `union`, etc.).

---

## 4. Tabla de Referencia Rápida

### 4.1 Definiciones principales

| Actual | Nuevo | Desglose |
|--------|-------|----------|
| `subseteq` | `subset` | simplificación |
| `BinInter` | `inter` | quitar "Bin" |
| `BinUnion` | `union` | quitar "Bin" |
| `PowerSetOf` | `powerset` | lowerCamelCase, quitar "Of" |
| `UnionSet` | `sUnion` | "s" = set-of-sets |
| `SpecSet` | `sep` | Mathlib standard |
| `successor` | `succ` | abreviatura estándar |
| `FunctionComposition` | `comp` | abreviatura estándar |
| `IdFunction` | `id` | abreviatura estándar |
| `InverseFunction` | `inv` | abreviatura estándar |
| `ImageSet` | `image` | simplificación |
| `PreimageSet` | `preimage` | simplificación |
| `Restriction` | `restrict` | simplificación |
| `DiagonalSet` | `diagSet` | lowerCamelCase |
| `isNat` | `IsNat` | UpperCamelCase (Prop) |
| `isSingleValued` | `IsSingleValued` | UpperCamelCase (Prop) |
| `isFunctionFromTo` | `IsFunction` | simplificación + Upper |
| `isInductive` | `IsInductive` | UpperCamelCase |
| `isTransitiveSet` | `IsTransitive` | simplificación + Upper |
| `isInitialSegment` | `IsInitialSegment` | UpperCamelCase |

### 4.2 Teoremas — patrón `_is_specified` → `mem_X_iff`

| Actual | Nuevo | Desglose |
|--------|-------|----------|
| `PowerSet_is_specified` | `mem_powerset_iff` | mem + 𝒫 + ↔ |
| `PowerSet_is_unique` | `powerset_eq_iff` | 𝒫 + = + ↔ |
| `successor_is_specified` | `mem_succ_iff` | mem + σ + ↔ |
| `BinInter_is_specified` | `mem_inter_iff` | mem + ∩ + ↔ |
| `BinUnion_is_specified` | `mem_union_iff` | mem + ∪ + ↔ |
| `SpecSet_is_specified` | `mem_sep_iff` | mem + sep + ↔ |
| `Difference_is_specified` | `mem_sdiff_iff` | mem + \ + ↔ |
| `UnionSet_is_specified` | `mem_sUnion_iff` | mem + ⋃ + ↔ |

### 4.3 Teoremas — patrones `_wc` eliminados

| Actual | Nuevo | Desglose |
|--------|-------|----------|
| `ExtSet_wc` | `eq_of_subset_of_subset` | conclusión(=)\_of\_hip1(⊆)\_of\_hip2(⊆) |
| `disjoint_is_empty_wc` | `disjoint_of_inter_nonempty` | o directamente `.mp` del iff |
| `BinInter_empty_left_wc` | `inter_eq_empty_iff_disjoint.mp` | usar .mp del iff |
| `BinInter_empty_right_wc` | `inter_eq_empty_iff_disjoint.mpr` | usar .mpr del iff |
| `Difference_empty_wc` | `subset_of_sdiff_eq_empty` | concl(⊆)\_of\_hip(\\=∅) |
| `Difference_subseteq_wc` | `sdiff_eq_empty_of_subset` | concl(\\=∅)\_of\_hip(⊆) |

### 4.4 Teoremas — propiedades algebraicas

| Actual | Nuevo | Desglose |
|--------|-------|----------|
| `BinUnion_commutative` | `union_comm` | ∪ + conmutatividad |
| `BinInter_commutative` | `inter_comm` | ∩ + conmutatividad |
| `BinInter_associative` | `inter_assoc` | ∩ + asociatividad |
| `BinUnion_absorb_inter` | `union_inter_self` | ∪(∩) = self |
| `BinInter_absorb_union` | `inter_union_self` | ∩(∪) = self |
| `BinUnion_distrib_inter` | `union_inter_distrib_left` | ∪ distribuye sobre ∩, izq |
| `BinInter_distrib_union` | `inter_union_distrib_left` | ∩ distribuye sobre ∪, izq |
| `DeMorgan_union` | `compl_union` | complemento de ∪ |
| `DeMorgan_inter` | `compl_inter` | complemento de ∩ |
| `disjoint_symm` | `disjoint_comm` o `Disjoint.symm` | simetría |
| `subseteq_reflexive` | `subset_refl` | ⊆ + reflexividad |
| `subseteq_transitive` | `subset_trans` | ⊆ + transitividad |
| `subseteq_antisymmetric` | `subset_antisymm` | ⊆ + antisimetría |
| `subset_asymmetric` | `ssubset_asymm` | ⊂ + asimetría |
| `subset_irreflexive` | `ssubset_irrefl` | ⊂ + irreflexividad |
| `subset_transitive` | `ssubset_trans` | ⊂ + transitividad |
| `PowerSet_mono` | `powerset_mono` | ya correcto |
| `PowerSet_mono_iff` | `powerset_mono_iff` | ya correcto |

### 4.5 Teoremas — naturales

| Actual | Nuevo | Desglose |
|--------|-------|----------|
| `zero_is_nat` | `isNat_zero` | pred(IsNat) + arg(zero) |
| `nat_successor_is_nat` | `isNat_succ` | pred + arg |
| `successor_injective` | `succ_injective` | abreviar σ |
| `successor_nonempty` | `succ_nonempty` | abreviar σ |
| `nat_ne_successor` | `ne_succ_self` | ≠ + σ + self |
| `nat_not_mem_self` | `not_mem_self` | ¬ + ∈ + self |
| `nat_no_two_cycle` | `not_mem_of_mem` | ¬∈ dado ∈ (sin ciclo) |
| `nat_trichotomy` | `trichotomy` | nombre axiomático |
| `nat_mem_trans` | `mem_trans` | ∈ + transitividad |
| `nat_mem_asymm` | `mem_asymm` | ∈ + asimetría |
| `nat_is_zero_or_succ` | `eq_zero_or_exists_succ` | = 0 ∨ ∃ σ |
| `mem_successor_self` | `mem_succ_self` | ∈ + σ + self |
| `mem_successor_of_mem` | `mem_succ_of_mem` | ∈σ dado ∈ |

---

## 5. Nota sobre la Transición

Durante la migración (`ZFC` → `ZFC`), los nombres actuales se renombrarán progresivamente
siguiendo estas convenciones. El orden de prioridad es:

1. Módulos base (axiomas): `Extension`, `Specification`, `Union`, `PowerSet`
2. Números naturales: `NaturalNumbers` + 13 módulos de aritmética
3. Funciones y relaciones: `Functions`, `Relations`, `CartesianProduct`
4. Álgebra booleana: `BooleanAlgebra` + módulos derivados
5. Cardinalidad y resto

Cada renombrado se verifica con compilación completa antes de continuar.
