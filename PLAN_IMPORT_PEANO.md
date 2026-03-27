# Plan de Importación de Peano → ZfcSetTheory

> **⚠️ ARCHIVADO — 2026-03-27**
> Este plan está **completamente ejecutado**. Todos los módulos bridge de peanolib
> han sido implementados (37/37 módulos, 0 sorry). Ver CURRENT-STATUS-PROJECT.md
> para el estado actual del proyecto.

**Creado:** 2026-03-21
**Archivado:** 2026-03-27
**Autor:** Julián Calderón Almendros

> Este documento describe el plan completo para importar las operaciones y resultados del
> proyecto Peano al universo ZFC de `SetUniverse`, aprovechando el isomorfismo
> `fromPeano` / `toPeano` definido en `PeanoImport.lean`.

---

## 0. Estado Actual

### 0.1. Ya completado

| Módulo ZfcSetTheory | Módulo Peano fuente | Estado |
|---|---|---|
| `NaturalNumbersAdd.lean` | `Peano.Add` | ✅ Completo |
| `NaturalNumbersMul.lean` | `Peano.Mul` | ✅ Completo |

### 0.2. Módulos Peano disponibles en `.lake` actual

El `.lake/packages/peanolib/` está desactualizado (snapshot de 2026-03-04). Contiene:
`PeanoNatLib`, `PeanoNatAxioms`, `PeanoNatStrictOrder`, `PeanoNatOrder`,
`PeanoNatMaxMin`, `PeanoNatWellFounded`, `PeanoNatAdd`, `PeanoNatSub`,
`PeanoNatMul`, `PeanoNatDiv`, `PeanoNatArith`.

### 0.3. Módulos Peano disponibles en GitHub master (2026-03-16)

Todos los anteriores **más**: `PeanoNatPow`, `PeanoNatFactorial`, `PeanoNatBinom`,
`PeanoNatNewtonBinom`, `PeanoNatPrimes`.

---

## 1. Paso Previo: Actualizar el Paquete Peano

**Antes de implementar Pow, Factorial, Binom, NewtonBinom, Primes**, ejecutar:

```bash
lake update
```

Esto actualizará `.lake/packages/peanolib/` al master actual de
`https://github.com/julian1c2a/Peano` (que ya tiene los módulos nuevos).

> **Verificación:** tras `lake update`, deben aparecer en
> `.lake/packages/peanolib/PeanoNatLib/`:
> `PeanoNatPow.lean`, `PeanoNatFactorial.lean`, `PeanoNatBinom.lean`,
> `PeanoNatNewtonBinom.lean`, `PeanoNatPrimes.lean`.

---

## 2. Patrón General de Implementación

Todos los módulos siguen uno de dos patrones:

### Patrón A — RecursiveFn (para operaciones de recursión estructural simple)

Aplica a: **Sub**, **Pow** (y se aplicó a Add, Mul).

```
1. Definir la función ZFC "paso" como conjunto:
      stepFn : U  (e.g. predFn, mulFn m hm)

2. Demostrar que stepFn es función de ω en ω:
      stepFn_is_function : isFunctionFromTo stepFn ω ω

3. Definir la operación via RecursiveFn:
      opFn m hm := RecursiveFn ω (base m) (stepFn m hm) (base_in_omega m hm) (stepFn_is_function m hm)

4. Definir op sin argumento de prueba:
      op m n := if h : m ∈ ω then apply (opFn m h) n else ∅

5. Probar ecuaciones recursivas: op_zero, op_succ

6. Probar bridge theorem:
      fromPeano (Peano.Op.op p q) = op (fromPeano p) (fromPeano q)

7. Levantar propiedades algebraicas desde Peano via bridge + fromPeano_injective
```

### Patrón B — Bridge directo (para recursión bien fundada o funciones de ℕ₀)

Aplica a: **Div/Mod**, **Arith** (divisibilidad, gcd, lcm), **Factorial**, **Binom**.

```
1. Definir op directamente via fromPeano/toPeano:
      op m n (hm : m ∈ ω) (hn : n ∈ ω) : U :=
        fromPeano (Peano.Op.op (toPeano m (mem_Omega_is_Nat m hm))
                               (toPeano n (mem_Omega_is_Nat n hn)))

   O con firma sin prueba (para compatibilidad algebraica):
      op m n := if h : m ∈ ω ∧ n ∈ ω then ... else ∅

2. Probar bridge theorem (trivial por definición o por recursión):
      fromPeano (Peano.Op.op p q) = op (fromPeano p) (fromPeano q)

3. Levantar propiedades algebraicas desde Peano via bridge + fromPeano_injective
```

---

## 3. Módulos a Implementar (por orden de dependencia)

### Módulo 3.1 — `NaturalNumbersSub.lean`

**Fuente Peano:** `PeanoNatLib.PeanoNatSub` (`Peano.Sub`)
**Patrón:** A (RecursiveFn con `predFn`)
**Prerrequisitos:** `NaturalNumbersAdd.lean` ✅

#### 3.1.1. Función auxiliar `predFn`

En ZFC (números de Von Neumann): `∪ (σ n) = n` y `∪ ∅ = ∅`.
Así, `predFn := {⟨n, ∪ n⟩ | n ∈ ω}` es la función predecesor truncado.

```lean
noncomputable def predFn : U :=
  -- SpecSet sobre ω ×ₛ ω: {⟨n, ∪ n⟩ | n ∈ ω}
  -- apply predFn n = ∪ n  para n ∈ ω
theorem predFn_is_function : isFunctionFromTo predFn ω ω
theorem predFn_apply (n : U) (hn : n ∈ ω) : apply predFn n = ∪ n
-- Nota: para n = σ k con k ∈ ω: ∪ (σ k) = k (propiedad de Von Neumann)
theorem predFn_succ (n : U) (hn : n ∈ ω) : apply predFn (σ n) = n
theorem predFn_zero : apply predFn ∅ = ∅
```

#### 3.1.2. Definición de `subFn` y `sub`

```lean
noncomputable def subFn (m : U) (hm : m ∈ ω) : U :=
  RecursiveFn ω m predFn hm predFn_is_function

noncomputable def sub (m n : U) : U :=
  if h : m ∈ ω then apply (subFn m h) n else ∅
```

#### 3.1.3. Ecuaciones recursivas

```lean
theorem sub_eq (m n : U) (hm : m ∈ ω) : sub m n = apply (subFn m hm) n
theorem sub_in_Omega (m n : U) (hm : m ∈ ω) (hn : n ∈ ω) : sub m n ∈ ω
theorem sub_zero (m : U) (hm : m ∈ ω) : sub m ∅ = m
theorem sub_succ (m n : U) (hm : m ∈ ω) (hn : n ∈ ω) : sub m (σ n) = ∪ (sub m n)
-- Refinamiento:
theorem sub_succ' (m n : U) (hm : m ∈ ω) (hn : n ∈ ω) :
    sub m (σ n) = if sub m n = ∅ then ∅ else ...
-- O simplemente el bridge:
```

#### 3.1.4. Bridge theorem

```lean
theorem fromPeano_sub (p q : Peano.ℕ₀) :
    (fromPeano (Peano.Sub.sub p q) : U) = sub (fromPeano p) (fromPeano q)
```

#### 3.1.5. Propiedades algebraicas (levantadas desde `Peano.Sub`)

```lean
theorem sub_zero_Omega (m : U) (hm : m ∈ ω) : sub m ∅ = m        -- [T8.1]
theorem zero_sub_Omega (n : U) (hn : n ∈ ω) : sub ∅ n = ∅         -- [T8.2]
theorem sub_k_add_k_Omega (n k : U) (hn : n ∈ ω) (hk : k ∈ ω)    -- [T8.3]
    (h : k ≤ₙ n) : add (sub n k) k = n
theorem add_k_sub_k_Omega (n k : U) (hn : n ∈ ω) (hk : k ∈ ω)    -- [T8.4]
    : sub (add n k) k = n
theorem sub_pos_iff_lt_Omega (n m : U) (hn : n ∈ ω) (hm : m ∈ ω) -- [T8.6]
    : σ ∅ ≤ₙ sub n m ↔ m ∈ n   -- (m < n en Von Neumann)
theorem sub_lt_self_Omega (a b : U) (ha : a ∈ ω) (hb : b ∈ ω)     -- [T8.7]
    (h_le : b ≤ₙ a) (h_ne : b ≠ ∅) : sub a b ∈ a
```

> **Nota sobre `≤ₙ`**: el orden en ω es la relación de pertenencia. `n ≤ₙ m` se puede
> expresar como `n ∈ m ∨ n = m` (equivalente a `n ⊆ m` para Von Neumann).
> Ver `natLe` en `Infinity.lean`.

---

### Módulo 3.2 — `NaturalNumbersDiv.lean`

**Fuente Peano:** `PeanoNatLib.PeanoNatDiv` (`Peano.Div`)
**Patrón:** B (bridge directo — la división euclídea usa recursión bien fundada)
**Prerrequisitos:** `NaturalNumbersSub.lean`

#### 3.2.1. Definiciones

```lean
noncomputable def div (m n : U) : U :=
  if h : m ∈ ω ∧ n ∈ ω then
    fromPeano (Peano.Div.div
      (toPeano m (mem_Omega_is_Nat m h.1))
      (toPeano n (mem_Omega_is_Nat n h.2)))
  else ∅

noncomputable def mod (m n : U) : U :=
  if h : m ∈ ω ∧ n ∈ ω then
    fromPeano (Peano.Div.mod
      (toPeano m (mem_Omega_is_Nat m h.1))
      (toPeano n (mem_Omega_is_Nat n h.2)))
  else ∅
```

#### 3.2.2. Bridge theorems

```lean
theorem fromPeano_div (p q : Peano.ℕ₀) :
    (fromPeano (Peano.Div.div p q) : U) = div (fromPeano p) (fromPeano q)
theorem fromPeano_mod (p q : Peano.ℕ₀) :
    (fromPeano (Peano.Div.mod p q) : U) = mod (fromPeano p) (fromPeano q)
```

#### 3.2.3. Propiedades levantadas desde `Peano.Div`

```lean
theorem divMod_eq_Omega (a b : U) (ha : a ∈ ω) (hb : b ∈ ω) (hb_ne : b ≠ ∅) :
    a = add (mul (div a b) b) (mod a b)                              -- [T10.1]
theorem mod_lt_divisor_Omega (a b : U) (ha : a ∈ ω) (hb : b ∈ ω) (hb_ne : b ≠ ∅) :
    mod a b ∈ b                                                      -- [T10.2]
```

---

### Módulo 3.3 — `NaturalNumbersPow.lean`

**Fuente Peano:** `PeanoNatLib.PeanoNatPow` (`Peano.Pow`)
**Patrón:** A (RecursiveFn con `mulFn m hm` como paso)
**Prerrequisitos:** `NaturalNumbersMul.lean` ✅; `lake update` para `PeanoNatPow`

#### 3.3.1. Definición

Peano define: `pow n ∅ = 𝟙`, `pow n (σ m) = mul (pow n m) n`.
El paso es "multiplicar por n a la derecha". Usando `mul_comm_Omega`:

```lean
-- powFn m hm computa "· ↦ m^·"
-- base = σ ∅ (el 1 en ZFC), paso = mulFn m hm (izquierda mult por m)
-- Resultado: powFn(k) = m^k  ya que m^0=1 y m^(σk) = m * m^k = m^k * m por comm.

noncomputable def powFn (m : U) (hm : m ∈ ω) : U :=
  RecursiveFn ω (σ ∅) (mulFn m hm) (succ_in_Omega ∅ zero_in_Omega)
                (mulFn_is_function m hm)

noncomputable def pow (m n : U) : U :=
  if h : m ∈ ω then apply (powFn m h) n else ∅
```

#### 3.3.2. Ecuaciones recursivas

```lean
theorem pow_zero (m : U) (hm : m ∈ ω) : pow m ∅ = σ ∅              -- m⁰ = 1
theorem pow_succ (m n : U) (hm : m ∈ ω) (hn : n ∈ ω) :
    pow m (σ n) = mul m (pow m n)                                    -- m^(σn) = m * m^n
```

#### 3.3.3. Bridge theorem

```lean
theorem fromPeano_pow (p q : Peano.ℕ₀) :
    (fromPeano (Peano.Pow.pow p q) : U) = pow (fromPeano p) (fromPeano q)
-- Prueba: inducción sobre q; paso usa mul_comm_Omega (igual que fromPeano_mul usó add_comm_Omega)
```

#### 3.3.4. Propiedades levantadas (selección de [T13.1]–[T13.23])

```lean
theorem pow_zero_Omega (m : U) (hm : m ∈ ω) : pow m ∅ = σ ∅        -- [T13.1]
theorem zero_pow_Omega (m : U) (hm : m ∈ ω) (hm_ne : m ≠ ∅) :
    pow ∅ m = ∅                                                      -- [T13.2]
theorem one_pow_Omega (m : U) (hm : m ∈ ω) : pow (σ ∅) m = σ ∅     -- [T13.3]
theorem pow_one_Omega (m : U) (hm : m ∈ ω) : pow m (σ ∅) = m       -- [T13.5]
theorem pow_add_eq_mul_pow_Omega (n m k : U) (hn : n ∈ ω)
    (hm : m ∈ ω) (hk : k ∈ ω) :
    pow n (add m k) = mul (pow n m) (pow n k)                       -- [T13.11]
theorem pow_pow_eq_pow_mul_Omega (n m k : U) (hn : n ∈ ω)
    (hm : m ∈ ω) (hk : k ∈ ω) :
    pow (pow n m) k = pow n (mul m k)                               -- [T13.13]
theorem mul_pow_Omega (n k m : U) (hn : n ∈ ω) (hk : k ∈ ω) (hm : m ∈ ω) :
    mul (pow n m) (pow k m) = pow (mul n k) m                       -- [T13.12]
```

---

### Módulo 3.4 — `NaturalNumbersArith.lean`

**Fuente Peano:** `PeanoNatLib.PeanoNatArith` (`Peano.Arith`)
**Patrón:** B (bridge directo para gcd/lcm; definiciones proposicionales directas para divisibilidad)
**Prerrequisitos:** `NaturalNumbersDiv.lean`

#### 3.4.1. Definiciones proposicionales (directas en ZFC)

```lean
-- Divisibilidad en ω
def divides (a b : U) : Prop := ∃ k : U, k ∈ ω ∧ b = mul a k
notation a " ∣ω " b => divides a b

def coprime (a b : U) (ha : a ∈ ω) (hb : b ∈ ω) : Prop :=
  ∀ d : U, d ∈ ω → divides d a → divides d b → d = σ ∅  -- gcd = 1

def isPrime (p : U) : Prop :=
  p ∈ ω ∧ p ≠ ∅ ∧ p ≠ σ ∅ ∧
  ∀ a b : U, a ∈ ω → b ∈ ω → divides p (mul a b) → divides p a ∨ divides p b
```

#### 3.4.2. gcd y lcm via bridge

```lean
noncomputable def gcd (a b : U) : U :=
  if h : a ∈ ω ∧ b ∈ ω then
    fromPeano (Peano.Arith.gcd (toPeano a ...) (toPeano b ...))
  else ∅

noncomputable def lcm (a b : U) : U :=
  div (mul a b) (gcd a b)
```

#### 3.4.3. Bridge theorems y propiedades clave

```lean
theorem fromPeano_gcd (p q : Peano.ℕ₀) :
    (fromPeano (Peano.Arith.gcd p q) : U) = gcd (fromPeano p) (fromPeano q)
-- Propiedades via bridge:
theorem gcd_comm_Omega, gcd_assoc_Omega, gcd_zero_r_Omega, gcd_zero_l_Omega
theorem divides_gcd_Omega, gcd_divides_l_Omega, gcd_divides_r_Omega
theorem bezout_Omega  -- identidad de Bézout (sin enteros negativos)
theorem gauss_Omega   -- Lema de Gauss: gcd(a,b)=1 ∧ a∣bc ⇒ a∣c
```

> **Nota:** La aritmética de `Peano.Arith` es extensa (~200 teoremas).
> Priorizar: divisibilidad básica, gcd, lcm, y Lema de Gauss.
> Dejar `PeanoNatPrimes` para un módulo opcional posterior.

---

### Módulo 3.5 — `NaturalNumbersFactorial.lean`

**Fuente Peano:** `PeanoNatLib.PeanoNatFactorial` (`Peano.Factorial`)
**Patrón:** A (RecursiveFn con `mulFn (σ ·) ·` — pero es función de un argumento; alternativamente Pattern B)
**Prerrequisitos:** `NaturalNumbersMul.lean` ✅; `lake update`

> **Observación:** `factorial n` es una función de **un argumento** en ℕ₀,
> no de dos. No encaja directamente en `RecursiveFn` (que toma base + step).
> La definición más natural en ZFC es:
> - `fact_step(n) = mul n (σ n)` — no es constante respecto al paso.
>
> **Estrategia recomendada:** Patrón B (bridge directo). Definir como imagen bajo fromPeano.

```lean
noncomputable def factorial (n : U) : U :=
  if h : n ∈ ω then
    fromPeano (Peano.Factorial.factorial (toPeano n (mem_Omega_is_Nat n h)))
  else ∅

theorem fromPeano_factorial (p : Peano.ℕ₀) :
    (fromPeano (Peano.Factorial.factorial p) : U) = factorial (fromPeano p)

-- Propiedades levantadas:
theorem factorial_zero_Omega : factorial ∅ = σ ∅                    -- [T14.1]
theorem factorial_succ_Omega (n : U) (hn : n ∈ ω) :
    factorial (σ n) = mul (factorial n) (σ n)                       -- [T14.2]
theorem factorial_pos_Omega (n : U) (hn : n ∈ ω) : ∅ ∈ factorial n  -- [T14.5]
theorem factorial_in_Omega (n : U) (hn : n ∈ ω) : factorial n ∈ ω
theorem factorial_le_mono_Omega (m n : U) (hm : m ∈ ω) (hn : n ∈ ω)
    (h : m ≤ₙ n) : factorial m ≤ₙ factorial n                       -- [T14.9]
```

---

### Módulo 3.6 — `NaturalNumbersBinom.lean`

**Fuente Peano:** `PeanoNatLib.PeanoNatBinom` (`Peano.Binom`)
**Patrón:** B (bridge directo)
**Prerrequisitos:** `NaturalNumbersFactorial.lean`, `NaturalNumbersSub.lean`; `lake update`

```lean
noncomputable def binom (n k : U) : U :=
  if h : n ∈ ω ∧ k ∈ ω then
    fromPeano (Peano.Binom.binom (toPeano n ...) (toPeano k ...))
  else ∅

-- Ecuaciones de Pascal:
theorem binom_zero_zero_Omega : binom ∅ ∅ = σ ∅                     -- [T15.1]
theorem binom_zero_succ_Omega (k : U) (hk : k ∈ ω) :
    binom ∅ (σ k) = ∅                                               -- [T15.2]
theorem binom_succ_zero_Omega (n : U) (hn : n ∈ ω) :
    binom (σ n) ∅ = σ ∅                                             -- [T15.3]
theorem binom_pascal_Omega (n k : U) (hn : n ∈ ω) (hk : k ∈ ω) :
    binom (σ n) (σ k) = add (binom n k) (binom n (σ k))             -- [T15.4]
theorem binom_eq_zero_of_lt_Omega (n k : U) (hn : n ∈ ω) (hk : k ∈ ω)
    (h : n ∈ k) : binom n k = ∅                                     -- [T15.7]
```

---

### Módulo 3.7 — `NaturalNumbersNewtonBinom.lean`

**Fuente Peano:** `PeanoNatLib.PeanoNatNewtonBinom` (`Peano.NewtonBinom`)
**Patrón:** B (sumatorio finito sobre funciones Lean; no hay función ZFC directa)
**Prerrequisitos:** `NaturalNumbersBinom.lean`, `NaturalNumbersPow.lean`, `NaturalNumbersSub.lean`; `lake update`

> **Observación:** `finSum` opera sobre funciones `ℕ₀ → ℕ₀`, no sobre conjuntos ZFC.
> En ZfcSetTheory, el sumatorio finito debe operar sobre funciones `U → U` (Lean),
> no sobre conjuntos ZFC. El `finSum` de Peano es directamente transportable
> como función Lean si se reformula sobre `U`.

```lean
-- finSum en ZFC: sobre funciones U → U
noncomputable def finSum (f : U → U) : U → U
  | n => ... -- definición recursiva sobre n ∈ ω via toPeano/fromPeano

-- Bridge principal:
theorem newton_binom_Omega (a b n : U) (ha : a ∈ ω) (hb : b ∈ ω) (hn : n ∈ ω) :
    pow (add a b) n =
    finSum (fun k => mul (mul (binom n k) (pow a k)) (pow b (sub n k))) n

theorem sum_binom_eq_pow_two_Omega (n : U) (hn : n ∈ ω) :
    finSum (fun k => binom n k) n = pow (σ (σ ∅)) n  -- Σ C(n,k) = 2^n
```

---

### Módulo 3.8 — `NaturalNumbersPrimes.lean` (OPCIONAL)

**Fuente Peano:** `PeanoNatLib.PeanoNatPrimes` (`Peano.Primes`)
**Patrón:** B (bridge directo + definiciones proposicionales)
**Prerrequisitos:** `NaturalNumbersArith.lean`; `lake update`

> **Alcance:** Existencia y unicidad de factorización (TFA). Muy extenso.
> Considerar como objetivo a largo plazo.

Teoremas clave a transportar:
- `prime_iff_Omega`: equivalencias de primalidad (euclídea, irreducible, divisores exactos)
- `exists_prime_factor_Omega`: todo n ≥ 2 tiene un factor primo
- `fundamental_theorem_arithmetic_Omega`: TFA completo

---

## 4. Orden de Implementación Recomendado

```
lake update
      ↓
NaturalNumbersSub.lean    (Patrón A; predFn via ∪)
      ↓
NaturalNumbersDiv.lean    (Patrón B; bridge directo)
      ↓
NaturalNumbersPow.lean    (Patrón A; mulFn como paso)
      ↓
NaturalNumbersArith.lean  (Patrón B; gcd/lcm + divisibilidad)
      ↓
NaturalNumbersFactorial.lean  (Patrón B)
      ↓
NaturalNumbersBinom.lean      (Patrón B)
      ↓
NaturalNumbersNewtonBinom.lean (Patrón B; finSum sobre U→U)
      ↓
NaturalNumbersPrimes.lean     (OPCIONAL; muy extenso)
```

---

## 5. Actualizaciones a `ZfcSetTheory.lean`

Añadir al final del fichero raíz, en orden:

```lean
import ZfcSetTheory.NaturalNumbersSub
import ZfcSetTheory.NaturalNumbersDiv
import ZfcSetTheory.NaturalNumbersPow
import ZfcSetTheory.NaturalNumbersArith
import ZfcSetTheory.NaturalNumbersFactorial
import ZfcSetTheory.NaturalNumbersBinom
import ZfcSetTheory.NaturalNumbersNewtonBinom
-- import ZfcSetTheory.NaturalNumbersPrimes   -- opcional
```

---

## 6. Actualizaciones a `REFERENCE.md`

Tras completar cada módulo, añadir una sección a `REFERENCE.md` bajo
`SetUniverse.NaturalNumbersXxx` con:
- Definiciones exportadas (`def`, `noncomputable def`)
- Teoremas exportados
- Notaciones (si aplica)

---

## 7. Consideraciones Técnicas

### 7.1. Notaciones para el orden en ω

En Infinity.lean ya existe `natLe` (`≼`) y `natLt` (pertenencia `∈` como `<`).
En los módulos nuevos, usar consistently estas notaciones y conectarlas con
`fromPeano_lt_iff` / `fromPeano_le_iff` de `PeanoImport.lean`.

### 7.2. El "1" en ZFC

En ZFC, 1 = σ ∅ = {∅}. Usarlo explícitamente como `σ (∅ : U)` o definir:

```lean
-- En Prelim.lean o NaturalNumbers.lean ya debería existir:
abbrev one : U := σ ∅  -- = {∅}
```

### 7.3. Truco con `mul_comm_Omega` en el bridge de Pow

El bridge `fromPeano_pow` necesita `mul_comm_Omega` porque:
- Peano define `pow n (σ m) = mul (pow n m) n` (mult derecha)
- ZFC con RecursiveFn+mulFn da `pow m (σ n) = mul m (pow m n)` (mult izquierda)
- El paso de prueba: `rw [mul_comm_Omega]` al igual que `fromPeano_mul` usó `add_comm_Omega`

### 7.4. `subₕₖ` vs `sub` de Peano

Peano tiene DOS versiones de resta:
- `subₕₖ n m h` (resta exacta, con prueba `h : Le m n`)
- `sub n m` (monus truncado: = subₕₖ si m≤n, else 0)

En ZFC, `sub m n = ∪ ∪ ... ∪ m` (n aplicaciones de pred) es **truncado** naturalmente.
No necesitamos `subₕₖ` como definición separada; `sub` ZFC corresponde a `Peano.Sub.sub`.

### 7.5. `predFn` y el axioma Union

`predFn` se define como `{p ∈ ω ×ₛ ω | ∃ n ∈ ω, p = ⟨σ n, n⟩ ∨ p = ⟨∅, ∅⟩}`.
Más directamente: `predFn = {⟨n, ∪ n⟩ | n ∈ ω}` usando el axioma Union ya importado.
Necesita `union` (`∪`) del `UnionAxiom` disponible en el proyecto.

### 7.6. Cuidado con módulos NewtonBinom y finSum

`finSum` en Peano es `ℕ₀ → ℕ₀`, no una función ZFC (conjunto de pares).
En ZfcSetTheory, `finSum` debe ser `(U → U) → U → U`, una función Lean.
No hay obstáculo para definirla vía `toPeano`/`fromPeano` usando la inyectividad.

---

## 8. Checklist de Implementación

- [x] `lake update` — actualizar paquete Peano
- [x] `NaturalNumbersSub.lean` — Sub (Patrón A) ✅ 2026-03-21
- [x] `NaturalNumbersDiv.lean` — Div/Mod (Patrón B) ✅ 2026-03-21
- [x] `NaturalNumbersPow.lean` — Pow (Patrón A) ✅ 2026-03-22
- [x] `NaturalNumbersArith.lean` — divisibilidad, gcd, lcm (Patrón B) ✅ 2026-03-22
- [x] `NaturalNumbersFactorial.lean` — factorial (Patrón B) ✅ 2026-03-22
- [x] `NaturalNumbersGcd.lean` — GCD ZFC-nativo (Euclides) ✅ 2026-03-24
- [x] `NaturalNumbersPrimes.lean` — TFA Enfoque A ✅ 2026-03-25
- [x] `NaturalNumbersBinom.lean` — coeficientes binomiales (Patrón B) ✅ 2026-03-25
- [x] `NaturalNumbersMaxMin.lean` — máximo/mínimo (Patrón B) ✅ 2026-03-26
- [x] `NaturalNumbersNewtonBinom.lean` — Binomio de Newton (Patrón B 4-arg) ✅ 2026-03-26
- [x] `NaturalNumbersWellFounded.lean` — buena ordenación de ω (Patrón B) ✅ 2026-03-26
- [x] Actualizar `ZfcSetTheory.lean` con los nuevos imports
- [x] Actualizar `REFERENCE.md` con las nuevas secciones (37 módulos proyectados)

---

*Fin del plan — 2026-03-21*
