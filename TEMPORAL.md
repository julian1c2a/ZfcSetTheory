# Plan de Demostración: `card_familyProduct`

**Fecha**: 2026-03-30
**Archivo**: `ZfcSetTheory/FiniteSequencesArith.lean`
**Estado**: Último sorry del archivo (sorry #15 de 15)

---

## Enunciado del Teorema

```lean
theorem card_familyProduct {F c n : U}
    (hn : n ∈ (ω : U))
    (hF : isFinSeq F n (⋃ (ImageSet F n)))
    (hc : isFinSeq c n ω)
    (hcard : ∀ i, i ∈ n → F⦅i⦆ ≃ₛ c⦅i⦆) :
    familyProduct F n ≃ₛ seqProd c n
```

**Significado**: Para una familia finita F : n → Sets donde cada F(i) es equipotente a c(i) ∈ ω, el producto cartesiano Π_{i<n} F(i) es equipotente al producto numérico Π_{i<n} c(i).

---

## Análisis de Dificultades

### Problema Central: Inducción ZFC con Codominios

La prueba se hace por inducción sobre `n ∈ ω` usando `induction_principle` (SpecSet ω P).
El predicado P debe cuantificar universalmente sobre F y c para que el paso inductivo funcione con funciones restringidas.

**Dificultad principal**: En el paso σ n' → ..., las hipótesis dan F con dominio σ n', pero la hipótesis inductiva necesita aplicar el resultado a funciones con dominio n'. Esto obliga a usar restricciones F ↾ n' y c ↾ n', lo que introduce dos problemas de compatibilidad:

1. `familyProduct (F ↾ n') n' ≠ familyProduct F n'` a priori (codominios diferentes en FinSeqSet)
2. `seqProd (c ↾ n') n' ≠ seqProd c n'` a priori (funciones recursivas diferentes)

### Resolución

Ambas igualdades son demostrables:

1. **`familyProduct (F ↾ n') n' = familyProduct F n'`**: Se usa que `ImageSet (F ↾ n') n' = ImageSet F n'` (por idempotencia de restricción: `(F ↾ n') ↾ n' = F ↾ n'`) y que `(F ↾ n')⦅i⦆ = F⦅i⦆` para i ∈ n' (por `Restriction_apply`).

2. **`seqProd (c ↾ n') n' = seqProd c n'`**: Se demuestra por inducción ZFC interna sobre k ∈ ω, usando que `(c ↾ n')⦅k⦆ = c⦅k⦆` para k ∈ n' y la ecuación de recursión de seqProd.

---

## Lemas Auxiliares Necesarios (3 helpers privados)

### Helper 1: `restriction_idempotent`

```lean
private theorem restriction_idempotent {f C : U} :
    (f ↾ C) ↾ C = f ↾ C
```

**Prueba**: Por ExtSet y Restriction_is_specified. Un par p está en `(f ↾ C) ↾ C` iff `p ∈ (f ↾ C) ∧ fst p ∈ C` iff `(p ∈ f ∧ fst p ∈ C) ∧ fst p ∈ C` iff `p ∈ f ∧ fst p ∈ C` iff `p ∈ f ↾ C`.

**Consecuencia**: `ImageSet (F ↾ n') n' = range ((F ↾ n') ↾ n') = range (F ↾ n') = ImageSet F n'`, y por tanto `⋃ ImageSet (F ↾ n') n' = ⋃ ImageSet F n'`.

### Helper 2: `seqProd_restriction`

```lean
private theorem seqProd_restriction {c n' : U}
    (hc : isFinSeq c (σ n') ω) (hn' : n' ∈ (ω : U)) :
    seqProd (c ↾ n') n' = seqProd c n'
```

**Prueba**: Inducción ZFC sobre k ∈ ω con P(k) = `seqProd (c ↾ n') k = seqProd c k` (para k ⊆ n', ambos bien definidos).

- **Base** P(∅): `seqProd (c ↾ n') ∅ = σ ∅ = seqProd c ∅` por `seqProd_zero`.
- **Paso** P(k) → P(σ k):

  ```
  seqProd (c ↾ n') (σ k) = mul (seqProd (c ↾ n') k) ((c ↾ n')⦅k⦆)   [seqProd_succ]
                          = mul (seqProd c k) (c⦅k⦆)                  [IH + Restriction_apply]
                          = seqProd c (σ k)                            [seqProd_succ]
  ```

**Nota**: `seqProd_succ` para `c ↾ n'` necesita `isFinSeq (c ↾ n') (σ k) ω`, que se satisface cuando σ k ⊆ n' ya que `(c ↾ n')` tiene dominio n'. Sin embargo, `seqProd_succ` requiere `isFinSeq f (σ k) ω`, no solo que f tenga dominio ≥ σ k. Esto funciona porque realmente necesitamos evaluarlo solo en n', y podemos usar `seqProd_succ` con `isFinSeq (c ↾ n') n' ω` solo cuando `n' = σ k`.

**Alternativa más limpia**: Usar P(k) más fuerte:

```
P(k) = k ⊆ n' → seqProd (c ↾ n') k = seqProd c k
```

Realmente, necesitamos más cuidado. La inducción debe verificar que en cada paso `seqProd_succ` se puede aplicar. Veamos:

- `seqProd (c ↾ n') k` se calcula via `seqProdFn (c ↾ n') h` donde h : `isFinSeq (c ↾ n') n' ω`. La función recursiva `seqProdFn` está definida sobre TODO ω, así que `apply (seqProdFn ...) k` existe para todo k ∈ ω.
- `seqProd_succ` necesita `isFinSeq f (σ k) ω`. Esto falla si σ k ≠ n'. Pero realmente `seqProd_succ` solo se usa para reescribir, y internamente seqProd calcula correctamente via la función recursiva.

**Solución**: En vez de usar `seqProd_succ`, demostrar la igualdad directamente por la unicidad de la función recursiva. O mejor: usar `seqProd_succ` vía un truco de reescritura con `isFinSeq_domain`:

Realmente, `seqProd_succ` **solo requiere** `isFinSeq f (σ k) ω` para asegurar que `seqProdFn` existe y se puede evaluar en σ k. Pero `seqProd f (σ k) = apply (seqProdFn f h) (σ k)` donde h es `isFinSeq f (domain f) ω`. Si domain f = n' y σ k ≤ n', la función recursiva seqProdFn f h : ω → ω está definida sobre todo ω, así que `apply ... (σ k)` está bien definida. El problema es que `seqProd_succ` está enunciada con la hipótesis `isFinSeq f (σ k) ω`, que es **más fuerte** que lo necesario.

Conclusión: necesito un enfoque diferente. En vez de usar `seqProd_succ` repetidamente, puedo probar la igualdad `seqProd (c ↾ n') n' = seqProd c n'` de forma directa, sin inducción, usando que la función recursiva de seqProd satisface la misma ecuación funcional.

**Enfoque práctico para seqProd_restriction**: Inducción sobre n' con `nat_is_zero_or_succ`:

- Si n' = ∅: `seqProd (c ↾ ∅) ∅ = σ ∅ = seqProd c ∅`. Solo necesito `isFinSeq (c ↾ ∅) ∅ ω` para `seqProd_zero`.
- Si n' = σ m: `seqProd (c ↾ σ m) (σ m) = mul (seqProd (c ↾ σ m) m) ((c ↾ σ m)⦅m⦆)` por `seqProd_succ` con `isFinSeq (c ↾ σ m) (σ m) ω`. Necesito IH: `seqProd (c ↾ σ m) m = seqProd c m`.

¡Pero aquí el IH debería ser para `c ↾ m`, no `c ↾ σ m`! El IH da `seqProd (c ↾ m) m = seqProd c m`, pero necesito `seqProd (c ↾ σ m) m = seqProd c m`.

**Esto nos lleva a otra inducción interna** para probar `seqProd (c ↾ σ m) m = seqProd (c ↾ m) m`, que requiere probar que `c ↾ σ m` y `c ↾ m` producen el mismo seqProd en m...

**CAMBIO DE ESTRATEGIA**: En vez de probar `seqProd (c ↾ n') n' = seqProd c n'`, reformular P del teorema principal para **evitar la restricción de c**.

---

## Estrategia Definitiva

### Predicado de Inducción

```lean
P(n') := ∀ F c, 
  isFinSeq F n' (⋃ (ImageSet F n')) → 
  isFinSeq c n' ω → 
  (∀ i, i ∈ n' → F⦅i⦆ ≃ₛ c⦅i⦆) → 
  familyProduct F n' ≃ₛ seqProd c n'
```

### Caso Base: P(∅)

```
familyProduct F ∅ = {∅}           [familyProduct_zero]
seqProd c ∅ = σ ∅                 [seqProd_zero]
{∅} ≃ₛ σ ∅                       [singleton_is_finite ∅ extraído]
```

`singleton_is_finite ∅` da `isFiniteSet {∅}`, es decir `∃ n ∈ ω, {∅} ≃ₛ n`. El testigo es `n = σ ∅` con la biyección `{⟨∅, ∅⟩}`. Extraemos `{∅} ≃ₛ σ ∅`.

### Paso Inductivo: P(n') → P(σ n')

Dado:

- `hn'_w : n' ∈ ω`
- `ih : P(n')` (hipótesis inductiva)
- `F, c` con `hF : isFinSeq F (σ n') (⋃ ImageSet F (σ n'))`, `hc : isFinSeq c (σ n') ω`
- `hcard : ∀ i ∈ σ n', F⦅i⦆ ≃ₛ c⦅i⦆`

**Goal**: `familyProduct F (σ n') ≃ₛ seqProd c (σ n')`

**Sub-pasos**:

#### Paso I.1: Reescribir seqProd c (σ n')

```
seqProd c (σ n') = mul (seqProd c n') (c⦅n'⦆)     [seqProd_succ hc hn'_w]
```

#### Paso I.2: Preparar la IH

Necesito `isFinSeq (F ↾ n') n' (⋃ ImageSet (F ↾ n') n')` y `isFinSeq (c ↾ n') n' ω` para aplicar la IH.

- `isFinSeq (c ↾ n') n' ω` se obtiene de `isFinSeq_restriction hc`.
- `isFinSeq (F ↾ n') n' (⋃ ImageSet (F ↾ n') n')`:
  - `isFinSeq_restriction hF` da `isFinSeq (F ↾ n') n' (⋃ ImageSet F (σ n'))` (codominio incorrecto)
  - Necesito probar que `⋃ ImageSet (F ↾ n') n' = ⋃ ImageSet F n'` (vía `restriction_idempotent`)
  - Y demostrar `isFinSeq (F ↾ n') n' (⋃ ImageSet F n')` — necesito que `F ↾ n' ⊆ n' ×ₛ (⋃ ImageSet F n')`, lo cual se sigue de que cada valor (F ↾ n')⦅i⦆ = F⦅i⦆ y F⦅i⦆ ∈ ImageSet F n' ⊆ ⋃ ImageSet F (σ n') [NO, F⦅i⦆ es un miembro de ImageSet F n', no un elemento de ⋃]

**PROBLEMA**: La condición `isFinSeq F n (⋃ ImageSet F n)` dice `F⦅i⦆ ∈ ⋃ ImageSet F n` para todo i ∈ n. Es decir, F⦅i⦆ (un SET de la familia) es un ELEMENTO de algún F⦅j⦆. Esta es una condición circular que se satisface por hipótesis `hF`, y la restricción a n' la hereda automáticamente si todos los j testigos están en n'.

Pero esto no está garantizado: la hipótesis `hF` da `∃ j ∈ σ n', F⦅i⦆ ∈ F⦅j⦆`, y el testigo j podría ser n' (que no está en n').

**SOLUCIÓN PRAGMÁTICA**: La condición `isFinSeq F n (⋃ ImageSet F n)` es utilizada en `familyProduct` solo para definir el FinSeqSet contenedor. Lo que realmente importa para el teorema es:

1. F es una función con dominio n
2. Cada F⦅i⦆ es un set, y c⦅i⦆ su cardinalidad

Dado que no puedo garantizar `isFinSeq (F ↾ n') n' (⋃ ImageSet (F ↾ n') n')` directamente, uso una **variante del predicado P** que acepta un codominio arbitrario A:

```lean
P(n') := ∀ F c A, 
  isFinSeq F n' A → 
  isFinSeq c n' ω → 
  (∀ i, i ∈ n' → F⦅i⦆ ≃ₛ c⦅i⦆) → 
  familyProduct F n' ≃ₛ seqProd c n'
```

Así en el paso inductivo:

- `isFinSeq_restriction hF` da directamente `isFinSeq (F ↾ n') n' A₀` con A₀ = `⋃ ImageSet F (σ n')`.
- La IH se aplica con F' = F ↾ n', c' = c ↾ n', A' = A₀.

Con esto solo necesito:

- `familyProduct (F ↾ n') n' = familyProduct F n'` o ≃ₛ
- `seqProd (c ↾ n') n' = seqProd c n'`

#### Paso I.3: familyProduct (F ↾ n') n' vs familyProduct F n'

**Definiciones**:

```
familyProduct (F ↾ n') n' = SpecSet (FinSeqSet n' (⋃ ImageSet (F ↾ n') n')) 
                             (fun g => ∀ i ∈ n', g⦅i⦆ ∈ (F ↾ n')⦅i⦆)

familyProduct F n'       = SpecSet (FinSeqSet n' (⋃ ImageSet F n')) 
                             (fun g => ∀ i ∈ n', g⦅i⦆ ∈ F⦅i⦆)
```

**Igualdad se sigue de**:

1. `(F ↾ n') ↾ n' = F ↾ n'` ⟹ `ImageSet (F ↾ n') n' = ImageSet F n'` ⟹ `⋃ ImageSet (F ↾ n') n' = ⋃ ImageSet F n'`
2. Para todo g, i ∈ n': `(F ↾ n')⦅i⦆ = F⦅i⦆` (por `Restriction_apply`)
3. Por (1) y (2), ambos SpecSets tienen la misma base y la misma predicación ⟹ igualdad por ExtSet.

**Proof sketch**: `by apply ExtSet; intro g; simp [familyProduct, SpecSet_is_specified, mem_FinSeqSet_iff]; constructor <;> intro h <;> ...`, reescribiendo con la igualdad de ImageSets y `Restriction_apply`.

#### Paso I.4: seqProd (c ↾ n') n' vs seqProd c n'

**Probar `seqProd (c ↾ n') n' = seqProd c n'` usando una inducción ZFC interna**.

Definir P_inner(k) = `seqProd (c ↾ n') k = seqProd c k`, con S_inner = SpecSet ω P_inner.

**Base** P_inner(∅):

```
seqProd (c ↾ n') ∅ = σ ∅     [seqProd_zero, con isFinSeq (c ↾ n') ∅ ω]
seqProd c ∅ = σ ∅             [seqProd_zero, con isFinSeq c ∅ ω]
```

¡PROBLEMA! `seqProd_zero` necesita `isFinSeq f ∅ ω`. Pero `c` tiene dominio σ n', no ∅. Y `c ↾ n'` tiene dominio n', no ∅.

Realmente, `seqProd c ∅` se calcula como `apply (seqProdFn c h) ∅` donde h : `isFinSeq c (σ n') ω`. La función recursiva satisface `apply ... ∅ = σ ∅`. Esto se sigue de `seqProdFn_zero`, no de `seqProd_zero`. Pero `seqProd` está definida como:

```lean
noncomputable def seqProd (f n : U) : U :=
    if h : isFinSeq f (domain f) ω then apply (seqProdFn f h) n else ∅
```

Entonces `seqProd c ∅ = apply (seqProdFn c h) ∅ = σ ∅` (por seqProdFn_zero).
Y `seqProd (c ↾ n') ∅ = apply (seqProdFn (c ↾ n') h') ∅ = σ ∅`.

Ambos evalúan a σ ∅. ✓ Pero para **demostrarlo en Lean**, no puedo usar `seqProd_zero` directamente porque tiene la hipótesis `isFinSeq f ∅ ω`. Tendría que "desdoblar" seqProd y usar seqProdFn_zero.

**ALTERNATIVA MUCHO MÁS SIMPLE**: En vez de probar `seqProd (c ↾ n') n' = seqProd c n'` vía inducción interna, **reformular P para no necesitar la restricción de c**.

Si c tiene dominio σ n', `seqProd c n'` está perfectamente definido (la función recursiva seqProdFn evalúa en cualquier punto de ω). La IH necesita `isFinSeq c' n' ω` para algún c'. ¿Puedo pasar c directamente? No, porque c no tiene dominio n'.

**¿Y si la IH toma seqProd del c original?** Es decir, si reformulo P así:

```lean
P(n') := ∀ F c A, 
  isFinSeq F n' A → 
  (∀ x ∈ n', ∃! y, ⟨x, y⟩ ∈ c) →  -- c tiene valores únicos en n'
  (∀ i, i ∈ n' → c⦅i⦆ ∈ ω) →       -- c⦅i⦆ ∈ ω para i ∈ n'
  (∀ i, i ∈ n' → F⦅i⦆ ≃ₛ c⦅i⦆) → 
  familyProduct F n' ≃ₛ seqProd c n'
```

¡NO! Porque `seqProd c n'` depende de QUÉ c sea como función completa (su dominio determina si el dif es true/false, y seqProdFn se construye con toda la información de c).

---

**DECISIÓN FINAL: Reformulación del Predicado P**

Después del análisis, la estrategia más limpia es:

```lean
P(n') := ∀ F c, 
  (n' ∈ (ω : U)) →
  isFinSeq F n' (⋃ (ImageSet F n')) → 
  isFinSeq c n' ω → 
  (∀ i, i ∈ n' → F⦅i⦆ ≃ₛ c⦅i⦆) → 
  familyProduct F n' ≃ₛ seqProd c n'
```

Y aceptar que necesitamos dos helpers:

1. **`restriction_idempotent`**: `(f ↾ C) ↾ C = f ↾ C` (5-10 líneas)
2. **`familyProduct_restriction`**: `familyProduct (F ↾ n') n' = familyProduct F n'` — donde F tiene dominio σ n' (15-25 líneas). Usa helper 1 + Restriction_apply + ExtSet.
3. **`seqProd_restriction`**: `seqProd (c ↾ n') n' = seqProd c n'` — donde c tiene dominio σ n' (40-60 líneas). Requiere inducción ZFC interna.

Para el helper 3, el enfoque es usar `strong_induction_principle` o `induction_principle` con n' como destino, desdoblando seqProd con `simp only [seqProd, dif_pos]` y usando `seqProdFn_zero` / `seqProdFn_succ` directamente.

---

## Estructura de la Prueba Final

### Helpers (orden de implementación)

```
1. restriction_idempotent          ~8 líneas
2. familyProduct_restriction       ~25 líneas  
3. seqProd_restriction             ~50 líneas
```

### Prueba principal: card_familyProduct

```lean
theorem card_familyProduct ... := by
  -- Inducción ZFC
  let P : U → Prop := fun n' => ∀ F c, 
    isFinSeq F n' (⋃ (ImageSet F n')) → isFinSeq c n' ω → 
    (∀ i, i ∈ n' → F⦅i⦆ ≃ₛ c⦅i⦆) → familyProduct F n' ≃ₛ seqProd c n'
  suffices h : P n from h F c hF hc hcard
  let S := SpecSet (ω : U) P
  suffices hS : S = ω by
    exact ((SpecSet_is_specified (ω : U) n P).mp (hS ▸ hn)).2
  apply induction_principle S
  · -- S ⊆ ω
    exact fun x hx => ((SpecSet_is_specified (ω : U) x P).mp hx).1
  
  · -- CASO BASE: ∅ ∈ S
    rw [SpecSet_is_specified]
    refine ⟨zero_in_Omega, fun F c hF hc hcard => ?_⟩
    rw [familyProduct_zero, seqProd_zero hc]
    -- Goal: {∅} ≃ₛ σ ∅
    -- Extraer de singleton_is_finite ∅
    obtain ⟨_, _, h_equip⟩ := singleton_is_finite (∅ : U)
    exact h_equip  -- singleton_is_finite da {∅} ≃ₛ σ ∅
    
  · -- PASO INDUCTIVO: n' ∈ S → σ n' ∈ S
    intro n' hn'
    rw [SpecSet_is_specified] at hn' ⊢
    obtain ⟨hn'_w, ih⟩ := hn'
    refine ⟨succ_in_Omega n' hn'_w, fun F c hF hc hcard => ?_⟩
    
    -- Reescribir seqProd c (σ n')
    rw [seqProd_succ hc hn'_w]
    -- Goal: familyProduct F (σ n') ≃ₛ mul (seqProd c n') (c⦅n'⦆)
    
    -- Preparar restricciones
    have hFr := isFinSeq_restriction hF   -- isFinSeq (F ↾ n') n' (⋃ ImageSet F (σ n'))
    have hcr := isFinSeq_restriction hc   -- isFinSeq (c ↾ n') n' ω
    
    -- Mostrar isFinSeq (F ↾ n') n' (⋃ ImageSet (F ↾ n') n')
    -- Vía restriction_idempotent: ImageSet (F ↾ n') n' = ImageSet F n'
    -- Y probar isFinSeq (F ↾ n') n' (⋃ ImageSet F n') manualmente
    have hFr' : isFinSeq (F ↾ n') n' (⋃ (ImageSet (F ↾ n') n')) := ...
    
    -- Aplicar IH
    have ih_result := ih (F ↾ n') (c ↾ n') hFr' hcr (fun i hi => ...)
    -- ih_result : familyProduct (F ↾ n') n' ≃ₛ seqProd (c ↾ n') n'
    
    -- Reducir a familyProduct F n' ≃ₛ seqProd c n'
    rw [familyProduct_restriction ...] at ih_result  
    rw [seqProd_restriction ...] at ih_result
    -- ih_result : familyProduct F n' ≃ₛ seqProd c n'
    
    -- Biyección familyProduct F (σ n') ≃ₛ (familyProduct F n') ×ₛ F⦅n'⦆
    have h_decomp : familyProduct F (σ n') ≃ₛ (familyProduct F n') ×ₛ F⦅n'⦆ := ...
    -- [CONSTRUCCIÓN PRINCIPAL — ver abajo]
    
    -- Aplicar card_product_two
    have h_seqProd_omega := seqProd_in_Omega hcr
    rw [seqProd_restriction ...] at h_seqProd_omega
    have h_cn'_omega := isFinSeq_apply_mem hc (mem_successor_self n')
    exact equipotent_trans h_decomp 
      (card_product_two h_seqProd_omega h_cn'_omega ih_result (hcard n' (mem_successor_self n')))
```

### Construcción de la Biyección Principal

`familyProduct F (σ n') ≃ₛ (familyProduct F n') ×ₛ F⦅n'⦆`

**Función h**: `g ↦ ⟨g ↾ n', g⦅n'⦆⟩`

**Definida como set ZFC**:

```lean
let h := SpecSet ((familyProduct F (σ n')) ×ₛ ((familyProduct F n') ×ₛ F⦅n'⦆))
  (fun p => ∃ g, g ∈ familyProduct F (σ n') ∧ p = ⟨g, ⟨g ↾ n', g⦅n'⦆⟩⟩)
```

**Prueba de isBijection h (familyProduct F (σ n')) ((familyProduct F n') ×ₛ F⦅n'⦆)**:

#### Función (isFunctionFromTo)

- **Subset**: Para p ∈ h, p = ⟨g, ⟨g ↾ n', g⦅n'⦆⟩⟩ con g ∈ familyProduct F (σ n'). Necesito ⟨g ↾ n', g⦅n'⦆⟩ ∈ (familyProduct F n') ×ₛ F⦅n'⦆. Uso `familyProduct_succ_char` para obtener (g ↾ n') ∈ familyProduct F n' y g⦅n'⦆ ∈ F⦅n'⦆.
- **Univocidad**: Para x ∈ familyProduct F (σ n'), existe g = x en la definición, dando y = ⟨x ↾ n', x⦅n'⦆⟩ único (por unicidad de ↾ y ⦅⦆).

#### Inyectividad

Si ⟨g₁, y⟩ ∈ h y ⟨g₂, y⟩ ∈ h, entonces ⟨g₁ ↾ n', g₁⦅n'⦆⟩ = ⟨g₂ ↾ n', g₂⦅n'⦆⟩.
Por Eq_of_OrderedPairs: g₁ ↾ n' = g₂ ↾ n' y g₁⦅n'⦆ = g₂⦅n'⦆.
g₁ y g₂ son ambos isFinSeq de longitud σ n'.
Por `isFinSeq_ext` aplicado a g₁ y g₂ con dominio σ n':

- Para i ∈ n': g₁⦅i⦆ = (g₁ ↾ n')⦅i⦆ = (g₂ ↾ n')⦅i⦆ = g₂⦅i⦆ (vía Restriction_apply)
- Para i = n': g₁⦅n'⦆ = g₂⦅n'⦆ (hipótesis)
- ∀ i ∈ σ n': g₁⦅i⦆ = g₂⦅i⦆ (por successor_is_specified: i ∈ n' ∨ i = n')
⟹ g₁ = g₂

#### Sobreyectividad

Dado y = ⟨g', a⟩ ∈ (familyProduct F n') ×ₛ F⦅n'⦆:

- g' ∈ familyProduct F n' ⟹ isFinSeq g' n' (⋃ ImageSet F n')
- a ∈ F⦅n'⦆
- Sea g := appendElem g' n' a
- Probar g ∈ familyProduct F (σ n'):
  - isFinSeq g (σ n') (⋃ ImageSet F (σ n')): usar isFinSeq_appendElem. Necesito a ∈ ⋃ ImageSet F (σ n'). Sabemos a ∈ F⦅n'⦆ y F⦅n'⦆ ∈ ImageSet F (σ n'), así que a ∈ ⋃ ImageSet F (σ n'). También necesito g' tiene valores en ⋃ ImageSet F n' ⊆ ⋃ ImageSet F (σ n'). **PROBLEM**: isFinSeq_appendElem necesita `isFinSeq g' n' A` y `a ∈ A` con el MISMO A. Pero g' es isFinSeq con codominio `⋃ ImageSet F n'` y a ∈ F⦅n'⦆. Necesito a ∈ ⋃ ImageSet F n'? No necesariamente (a ∈ F⦅n'⦆ y F⦅n'⦆ puede no ser un subconjunto de ⋃ ImageSet F n'). PERO necesito a ∈ ⋃ ImageSet F (σ n'), que sí se cumple: F⦅n'⦆ ∈ ImageSet F (σ n') y a ∈ F⦅n'⦆ ⟹ a ∈ ⋃ ImageSet F (σ n'). Entonces uso isFinSeq_appendElem con A = ⋃ ImageSet F (σ n'). Pero g' es isFinSeq g' n' (⋃ ImageSet F n'), no (⋃ ImageSet F (σ n')). Necesito ampliar el codominio.

  **Para ampliar**: g' ⊆ n' ×ₛ (⋃ ImageSet F n') ⊆ n' ×ₛ (⋃ ImageSet F (σ n')) (por monotonía de ⋃ respecto a subconjuntos de ImageSet). Y la condición de función se preserva. Así que isFinSeq g' n' (⋃ ImageSet F (σ n')) se demuestra manualmente.

- ∀ i ∈ σ n', g⦅i⦆ ∈ F⦅i⦆:
  - i ∈ n': g⦅i⦆ = (appendElem g' n' a)⦅i⦆ = g'⦅i⦆ (appendElem_apply_prev) y g'⦅i⦆ ∈ F⦅i⦆ (por g' ∈ familyProduct F n')
  - i = n': g⦅n'⦆ = a (appendElem_apply_last) y a ∈ F⦅n'⦆ ✓
- g ∈ FinSeqSet (σ n') (⋃ ImageSet F (σ n')): por isFinSeq_appendElem ✓

- Probar h(g) = y = ⟨g', a⟩:
  - g ↾ n' = g'? Sí, por isFinSeq_ext: para i ∈ n', (g ↾ n')⦅i⦆ = g⦅i⦆ = (appendElem g' n' a)⦅i⦆ = g'⦅i⦆
  - g⦅n'⦆ = a? Sí, por appendElem_apply_last

---

## Estimación de Tamaño

| Componente | Líneas estimadas |
|---|---|
| restriction_idempotent | ~8 |
| familyProduct_restriction | ~25 |
| seqProd_restriction | ~50 |
| Biyección (inline en card_familyProduct) | ~80 |
| Setup inductivo + base + paso | ~40 |
| **TOTAL** | **~200** |

---

## Infraestructura Disponible (Resumen)

### Inducción y Naturales

- `induction_principle S (hS ⊆ ω) (∅ ∈ S) (∀ n ∈ S, σ n ∈ S) : S = ω`
- `nat_is_zero_or_succ n (isNat n) : n = ∅ ∨ ∃ k, n = σ k`
- `mem_successor_self n : n ∈ σ n`
- `mem_successor_of_mem i n (hi : i ∈ n) : i ∈ σ n`
- `successor_is_specified n x : x ∈ σ n ↔ x ∈ n ∨ x = n`
- `nat_not_mem_self n (isNat n) : n ∉ n`

### Equipotencia

- `equipotent_refl (A : U) : A ≃ₛ A`
- `equipotent_symm {A B} (h : A ≃ₛ B) : B ≃ₛ A`
- `equipotent_trans {A B C} (hab : A ≃ₛ B) (hbc : B ≃ₛ C) : A ≃ₛ C`
- `singleton_is_finite (a : U) : isFiniteSet ({a} : U)` — da `∃ n ∈ ω, {a} ≃ₛ n`, testigo σ ∅

### Secuencias Finitas

- `isFinSeq_restriction {f n A} (h : isFinSeq f (σ n) A) : isFinSeq (f ↾ n) n A`
- `isFinSeq_appendElem {f n A a} (hf : isFinSeq f n A) (ha : a ∈ A) : isFinSeq (appendElem f n a) (σ n) A`
- `appendElem_apply_last {f n A a} (hf : isFinSeq f n A) : (appendElem f n a)⦅n⦆ = a`
- `appendElem_apply_prev {f n A a i} (hf : isFinSeq f n A) (hi : i ∈ n) : (appendElem f n a)⦅i⦆ = f⦅i⦆`
- `isFinSeq_ext {f g n A} (hf hg : isFinSeq f/g n A) (hval : ∀ i ∈ n, f⦅i⦆ = g⦅i⦆) : f = g`
- `Restriction_apply (f C x : U) (hx : x ∈ C) : (f ↾ C)⦅x⦆ = f⦅x⦆`
- `Restriction_is_specified f C p : p ∈ (f ↾ C) ↔ p ∈ f ∧ fst p ∈ C`

### Familia y Producto

- `familyProduct_zero (F : U) : familyProduct F ∅ = {∅}`
- `familyProduct_succ_char {F n} (hn : n ∈ ω) (hF : isFinSeq F (σ n) (⋃ ImageSet F (σ n))) : ∀ g ∈ familyProduct F (σ n), (g ↾ n) ∈ familyProduct F n ∧ g⦅n⦆ ∈ F⦅n⦆`
- `seqProd_zero {f} (hf : isFinSeq f ∅ ω) : seqProd f ∅ = σ ∅`
- `seqProd_succ {f k} (hf : isFinSeq f (σ k) ω) (hk : k ∈ ω) : seqProd f (σ k) = mul (seqProd f k) (f⦅k⦆)`
- `seqProd_in_Omega {f n} (hf : isFinSeq f n ω) : seqProd f n ∈ ω`
- `card_product_two {A B n m} (hn : n ∈ ω) (hm : m ∈ ω) (hA : A ≃ₛ n) (hB : B ≃ₛ m) : (A ×ₛ B) ≃ₛ mul n m`

### Set Theory

- `Eq_of_OrderedPairs_given_projections a b c d (h : ⟨a, b⟩ = ⟨c, d⟩) : a = c ∧ b = d`
- `ExtSet (hiff : ∀ x, x ∈ A ↔ x ∈ B) : A = B`
- `SpecSet_is_specified A x P : x ∈ SpecSet A P ↔ x ∈ A ∧ P x`
- `mem_FinSeqSet_iff {f n A} : f ∈ FinSeqSet n A ↔ isFinSeq f n A`
- `UnionSet_is_specified A x : x ∈ ⋃ A ↔ ∃ S ∈ A, x ∈ S` (o similar)

---

## Riesgos y Mitigaciones

| Riesgo | Mitigación |
|---|---|
| `seqProd_restriction` requiere inducción interna compleja | Si falla, probar como lema separado con strong_induction |
| Codominios de `isFinSeq_appendElem` incompatibles | Ampliar manualmente `isFinSeq g' n' A` a `isFinSeq g' n' A'` con `A ⊆ A'` |
| La biyección inline es muy larga | Si > 100 líneas, extraer como helper `familyProduct_succ_equip` |
| `familyProduct_restriction` depende de igualdad de SpecSets | Probar por extensionalidad (ExtSet), no por congruencia |

---

## Orden de Implementación

1. ✍️ `restriction_idempotent` — helper mínimo
2. ✍️ `familyProduct_restriction` — usa helper 1
3. ✍️ `seqProd_restriction` — inducción interna
4. ✍️ `card_familyProduct` — usa helpers 2 y 3, construye biyección inline

---

# Estado de Compilación del Proyecto ZfcSetTheory (anterior)

**Fecha**: 2026-03-29 10:00
**Autor**: Julián Calderón Almendros

## ✅ Compilación Exitosa

**Build Status**: ✅ **Todos los módulos compilados correctamente** (0 sorry, 0 errores)

### 📊 Resumen del Estado

**Sorry activos**: 0

| Archivo | Estado |
| --- | --- |
| Todos los módulos (39) | ✅ 0 sorry |

### 🎉 Mejoras Recientes

#### ✅ FiniteSets.lean completado - 2026-03-29

- ✅ `isFiniteSet (A : U) : Prop` — definición: ∃ n ∈ ω, A ≃ₛ n
- ✅ Infraestructura de biyecciones: `id_is_bijection`, `bijection_inverse_is_bijection`, `comp_bijection`
- ✅ Relación de equivalencia de equipotencia: `equipotent_refl`, `equipotent_symm`, `equipotent_trans`
- ✅ Clausura bajo equipotencia: `finite_equipotent`
- ✅ Casos básicos: `empty_is_finite`, `nat_is_finite`, `singleton_is_finite`
- ✅ Unión con singleton: `finite_union_singleton`
- ✅ 1 definición + 21 teoremas en 8 secciones
- ✅ 22 exports al namespace `SetUniverse`
- ✅ Proyectado completamente en REFERENCE.md (§3.37, §4.33, §6.34)

#### ✅ FiniteSequences.lean completado - 2026-03-27

- ✅ `isFinSeq (f n A : U) : Prop` — predicado: n ∈ ω ∧ f : n → A
- ✅ `FinSeqSet (n A : U) : U` — conjunto de todas las n-secuencias en A
- ✅ `appendElem (f n a : U) : U` — extensión f ∪ {⟨n, a⟩}
- ✅ 15 teoremas en 5 secciones (predicado central, FinSeqSet, secuencia vacía, appendElem, descomposición)
- ✅ Namespace `SetUniverse.FiniteSequences` (sin export a `SetUniverse`)
- ✅ Proyectado completamente en REFERENCE.md (§3.36, §4.32, §6.33)

#### ✅ NaturalNumbersBinom.lean completado - 2026-03-25

- ✅ Definición `binomOf` vía Patrón B (bridge-only): `fromPeano (Peano.Binom.binom (toPeano n _) (toPeano k _))`
- ✅ Teorema puente `fromPeano_binom`: Peano.Binom.binom p q ↔ binomOf (ΠZ p) (ΠZ q)
- ✅ Valores concretos: `binomOf_zero_zero`, `binomOf_succ_zero`, `binomOf_zero_succ`
- ✅ Regla de Pascal: `binomOf_pascal` — C(σ n, σ k) = C(n, k) + C(n, σ k)
- ✅ Propiedades algebraicas: `binomOf_n_zero`, `binomOf_n_one`, `binomOf_self`, `binomOf_succ_n_by_n`
- ✅ Anulación/positividad: `binomOf_eq_zero_of_gt`, `binomOf_pos`
- ✅ Conexión factorial: `binomOf_mul_factorials` — C(n,k)·k!·(n−k)! = n!
- ✅ 15 exports al namespace `SetUniverse`
- ✅ Proyectado completamente en REFERENCE.md (§3.32, §4.28, §6.29)

#### ✅ NaturalNumbersMaxMin.lean completado - 2026-03-26

- ✅ `maxOf (n m : U) : U` — máximo vía Patrón B (bridge-only)
- ✅ `minOf (n m : U) : U` — mínimo vía Patrón B (bridge-only)
- ✅ Teoremas puente: `fromPeano_max`, `fromPeano_min`
- ✅ 27 teoremas: idempotencia, conmutatividad, asociatividad, identidad/aniquilador, cotas, caracterización, max=min⇔iguales
- ✅ 31 exports al namespace `SetUniverse`
- ✅ Proyectado completamente en REFERENCE.md (§3.33, §4.29, §6.30)

#### ✅ NaturalNumbersNewtonBinom.lean completado - 2026-03-26

- ✅ `binomTermOf (a b n k : U) : U` — término binomial Patrón B (4 argumentos)
- ✅ Teorema puente `fromPeano_binomTerm` con `congr 1` ×4
- ✅ Newton's binomial theorem y Σ C(n,k)=2^n (Peano→ZFC)
- ✅ Separación de potencias, comparación de crecimiento existencial
- ✅ 12 exports al namespace `SetUniverse`
- ✅ Proyectado completamente en REFERENCE.md (§3.34, §4.30, §6.31)

#### ✅ NaturalNumbersWellFounded.lean completado - 2026-03-26

- ✅ `acc_lt_Omega` — accesibilidad bajo ∈ restringido a ω
- ✅ `well_ordering_Omega` — principio de buena ordenación con unicidad
- ✅ `well_ordering_Omega_exists` — forma simplificada
- ✅ 3 exports al namespace `SetUniverse`
- ✅ Proyectado completamente en REFERENCE.md (§3.35, §4.31, §6.32)

#### ✅ NaturalNumbersPrimes.lean completado - 2026-03-25

- ✅ Definición ZFC-nativa `isPrime` (p ∈ ω ∧ p ≠ ∅ ∧ p ≠ σ∅ ∧ propiedad de Euclides)
- ✅ Teorema puente `fromPeano_prime`: Peano.Arith.Prime p ↔ isPrime (fromPeano p)
- ✅ Propiedades básicas: `isPrime_in_Omega`, `isPrime_ne_zero`, `isPrime_ne_one`, `isPrime_ge_two`, `isPrime_prime_divisors`
- ✅ `exists_prime_divisor_ZFC`: todo n ≥ 2 en ω tiene un divisor primo ZFC
- ✅ TFA Existencia (Enfoque A): `exists_prime_factorization_ZFC`
- ✅ TFA Unicidad (Enfoque A): `unique_prime_factorization_ZFC`
- ✅ 11 exports al namespace `SetUniverse`
- ✅ Proyectado completamente en REFERENCE.md (§3.31, §4.27, §6.28)

#### ✅ NaturalNumbersGcd.lean completado - 2026-03-24

- ✅ `gcd` ZFC-nativo vía algoritmo euclídeo con `RecursiveFn` sobre ω ×ₛ ω
- ✅ `lcm` vía `divOf (mul a b) (gcd a b)`
- ✅ Teoremas puente: `gcd_eq_gcdOf`, `lcm_eq_lcmOf`
- ✅ Propiedades: divisibilidad del GCD, conmutatividad, GCD más grande, LCM
- ✅ 17 exports al namespace `SetUniverse`

#### ✅ NaturalNumbersFactorial.lean completado - 2026-03-22

- ✅ `factorialOf` via Patrón B (bridge-only) vía isomorfismo
- ✅ Teorema puente `fromPeano_factorial`
- ✅ Ecuación de recursión, valores concretos (0!, 1!, 2!), positividad, monotonía
- ✅ 11 exports al namespace `SetUniverse`

#### ✅ NaturalNumbersArith.lean completado - 2026-03-21

- ✅ `divides` ZFC-nativo: `∃ k ∈ ω, mul m k = n`
- ✅ `div`/`mod` nativos vía RecursiveFn (verificados iguales a `divOf`/`modOf`)
- ✅ `gcdOf`/`lcmOf` Patrón B
- ✅ Identidad de Bézout (forma substractiva)
- ✅ 13 propiedades de divisibilidad

#### ✅ PeanoImport.lean completo - 2026-03-08

- ✅ Isomorfismo Von Neumann ↔ Peano completo (sin sorry)
- ✅ Bridges de orden: `fromPeano_lt_iff`, `fromPeano_le_iff`
- ✅ `toPeano_proof_irrel` demostrado

#### ✅ Recursion.lean completado - 2026-03-05

- ✅ Teorema de recursión sobre ℕ (0 sorry, 0 errores de tipo)
- ✅ `RecursiveFn_zero`, `RecursiveFn_succ`, `RecursiveFn_unique`

### 📈 Métricas del Proyecto

- **Módulos totales**: 38
- **Compilación**: ✅ Exitosa (0 errores, 0 sorry)
- **Pruebas completas**: 100%
- **Líneas de código Lean**: ~5,300+
- **Líneas de documentación**: 10,500+ (REFERENCE.md ~10,500 líneas)

### 📝 Archivos de Documentación

| Archivo | Estado |
| --- | --- |
| REFERENCE.md | ✅ ~10,500 lineas — 37 modulos proyectados |
| NEXT-STEPS.md | ✅ Actualizado 2026-03-26 |
| TODO.md | ✅ Actualizado 2026-03-26 |
| README.md | ✅ Actualizado 2026-03-25 |

### 🎯 Estado por Categoría

**Axiomas ZFC** (7/9):

- ✅ Extensionalidad, Existencia, Especificación, Par, Unión, Potencia, Infinito
- ⏳ Reemplazo, Fundación (pendientes)

**Estructuras Algebraicas**:

- ✅ BooleanAlgebra completa
- ✅ BooleanRing completo
- ✅ PowerSetAlgebra completo
- ✅ AtomicBooleanAlgebra completo (átomos, atomicidad de 𝒫(A))

**Relaciones y Funciones**:

- ✅ Producto Cartesiano completo
- ✅ Relations.lean 100% completo (0 sorry)
- ✅ Functions.lean 100% completo (0 sorry)
- ✅ `domain`/`range`/`imag` completamente probados

**Cardinalidad**:

- ✅ Cardinality.lean 100% completo (Cantor + CSB demostrados, 0 sorry)

**Teoría de Números (ω)**:

- ✅ NaturalNumbers.lean completo (predecessor exportado)
- ✅ Infinity.lean completo (nat_mem_wf probado, exportado)
- ✅ Recursion.lean completo (teorema de recursión, 0 sorry)
- ✅ PeanoImport.lean completo (isomorfismo Von Neumann ↔ Peano, bridges de orden)
- ✅ NaturalNumbersAdd.lean completo (suma ZFC, puente fromPeano_add)
- ✅ NaturalNumbersMul.lean completo (multiplicación ZFC, puente fromPeano_mul)
- ✅ NaturalNumbersSub.lean completo (monus ZFC, puente fromPeano_sub)
- ✅ NaturalNumbersDiv.lean completo (divOf/modOf Patrón B, puente fromPeano_div/mod)
- ✅ NaturalNumbersPow.lean completo (potenciación ZFC, puente fromPeano_pow)
- ✅ NaturalNumbersArith.lean completo (divides nativo, gcdOf/lcmOf Patrón B, Bézout)
- ✅ NaturalNumbersFactorial.lean completo (factorial Patrón B, 10 propiedades)
- ✅ NaturalNumbersGcd.lean completo (gcd ZFC-nativo euclídeo, lcm, 17 exports)
- ✅ NaturalNumbersPrimes.lean completo (isPrime ZFC-nativo, TFA Enfoque A, 11 exports)
- ✅ NaturalNumbersBinom.lean completo (binomOf Patrón B, regla de Pascal, 15 exports)
- ✅ NaturalNumbersMaxMin.lean completo (maxOf/minOf Patrón B, 29 teoremas, 31 exports)
- ✅ NaturalNumbersNewtonBinom.lean completo (binomTermOf Patrón B 4-arg, Newton binom, 12 exports)
- ✅ NaturalNumbersWellFounded.lean completo (acc_lt_Omega, well_ordering_Omega, 3 exports)

---

## 🎯 Próximos Pasos

1. **Álgebra de Boole Completa** — completar teoremas de representación en `AtomicBooleanAlgebra`
2. **Secuencias Finitas en ZFC** (`FiniteSequences.lean`) — funciones `f : n → ω`
3. **Enteros ℤ en ZFC** — clases de equivalencia de pares (a, b) ∈ ω × ω

**Nota:** Todos los módulos bridge de peanolib han sido completados (MaxMin, NewtonBinom, WellFounded fueron los últimos tres).

---

## 🎉 Conclusión

El proyecto está en **excelente estado**:

- ✅ Compilación exitosa sin errores (37 módulos, 0 sorry)
- ✅ 37/37 módulos 100% completos
- ✅ Todos los módulos bridge de peanolib completados
- ✅ Teorema Fundamental de la Aritmética (TFA) completamente demostrado en ZFC
- ✅ Documentación completa en REFERENCE.md (~10,000 líneas)

---

**Autor**: Julián Calderón Almendros
**License**: MIT License
