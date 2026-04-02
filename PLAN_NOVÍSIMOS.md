# Plan de Implementación de los Novísimos

**Creado:** 2026-04-02
**Autor:** Julián Calderón Almendros
**Estado:** Borrador inicial — En planificación

> Este documento reelabora las ideas expuestas en la sección **NOVÍSIMOS** y
> **UNA IDEA DE IMPLEMENTACIÓN DE LOS NOVÍSIMOS** de `THOUGHTS.md`,
> transformándolas en un plan concreto y accionable para un macro-proyecto
> que unificaría `ZfcSetTheory`, `Peano`, `AczelSetTheory` y `MKplusCAC`
> bajo un marco común de interfaces (typeclasses) y puentes (equivalencias).

---

## Índice

- [0. Visión general y motivación](#0-visión-general-y-motivación)
- [1. Tensión fundamental: tipos externos vs. elementos internos](#1-tensión-fundamental)
- [2. Fase 0: Limpieza de warnings](#2-fase-0-limpieza-de-warnings)
- [3. Fase 1: Interfaces como tipoclases (`FMath.Interface`)](#3-fase-1-interfaces)
- [4. Fase 2: Instancias — proyectos existentes como modelos](#4-fase-2-instancias)
- [5. Fase 3: Teoremas abstractos contra interfaces](#5-fase-3-teoremas-abstractos)
- [6. Fase 4: Sistema de puentes entre sistemas axiomáticos](#6-fase-4-puentes)
- [7. Fase 5: Modelo de Aczel — Computabilidad plena](#7-fase-5-aczel)
- [8. Fase 6: Proyecto unificado (`FundamentosMath`)](#8-fase-6-proyecto-unificado)
- [9. Orden de ejecución y dependencias](#9-orden-de-ejecución)
- [10. Advertencias y decisiones abiertas](#10-advertencias)
- [Apéndice A: Mapa de puentes](#apéndice-a-mapa-de-puentes)
- [Apéndice B: Bocetos de código](#apéndice-b-bocetos-de-código)

---

## 0. Visión general y motivación

### ¿Qué tenemos hoy?

| Proyecto | Descripción | Estado |
|----------|-------------|--------|
| **ZfcSetTheory** | ZFC axiomático en Lean 4. Tipo opaco `U : Type u`, axiomas como `axiom`. 43 módulos, 0 sorry. | Producción |
| **Peano** (`peanolib`) | Naturales inductivos `ℕ₀` con aritmética completa. | Producción |
| **AczelSetTheory** | Conjuntos hereditariamente finitos, computables. Basado en listas. | Incipiente |
| **MKplusCAC** | Morse-Kelley con Axioma de Elección para Clases. | Futuro |

### ¿Qué queremos?

Un **meta-proyecto** llamado `FundamentosMath` (o `FMathLean`) que:

1. Defina **interfaces abstractas** (tipoclases Lean 4) para universos conjuntistas
   y estructuras matemáticas, independientes de cualquier sistema axiomático concreto.
2. Demuestre cada proyecto existente como **instancia** (modelo) de esas interfaces.
3. Demuestre **teoremas una sola vez** contra las interfaces, aplicables automáticamente a
   toda instancia (ZFC, Peano, Aczel, MK).
4. Establezca **puentes formales** entre sistemas: equivalencias, inclusiones,
   y los metateoremas de separación (Gödel).
5. Mantenga la **introducción gradual de axiomas** (punto 0.9 de THOUGHTS.md):
   cada axioma solo se introduce cuando es necesario, preservando la jerarquía
   constructiva por capas.

---

## 1. Tensión fundamental: tipos externos vs. elementos internos {#1-tensión-fundamental}

Antes de diseñar las interfaces, hay que resolver una tensión clave en la arquitectura:

| Sistema | Los naturales son... | Tipo Lean |
|---------|---------------------|-----------|
| **Peano** | Un tipo inductivo propio (datos) | `Peano.ℕ₀ : Type` |
| **ZFC** | Elementos internos del universo (proposiciones) | `x : U` con `IsNat x` |
| **Aczel** | Elementos internos de un tipo inductivo computable | `x : HFSet` con `HFSet.isNat x` |
| **MK** | Conjuntos (elementos de la clase universal) | `x : V` con `V.IsNat x` |

Una `class NaturalNumbers (N : Type)` funciona directamente para Peano, pero para
ZFC requiere un **subtipo envoltorio** como `{ x : U // IsNat x }`.

### Decisión de diseño

Las interfaces operarán en **dos niveles**:

1. **Nivel universo** — `class SetUniverse (V : Type u)`:
   describe el universo conjuntista con sus axiomas.
2. **Nivel estructura** — `class NaturalNumbers (N : Type)`:
   describe sistemas de números.

Para conectar ambos niveles, cada sistema conjuntista proveerá una instancia
`NaturalNumbers` sobre su subtipo de naturales:

```lean
-- ZFC: subtipo envoltorio
def OmegaElem := { x : U // IsNat x }

instance : NaturalNumbers OmegaElem where
  zero := ⟨∅, zero_in_Omega⟩
  succ := fun ⟨n, hn⟩ => ⟨σ n, succ_in_Omega hn⟩
  ...
```

---

## 2. Fase 0: Limpieza de warnings {#2-fase-0-limpieza-de-warnings}

> Ref: Novísimos [1] y [2]

**Objetivo:** Salida de build completamente limpia (solo errores o nada).

**Alcance:**

- [ ] `ZfcSetTheory`: 43 módulos
- [ ] `Peano` (`peanolib`): todos los módulos

**Estrategia:**

1. Ejecutar `lake build 2>&1 | Select-String "warning"` para inventariar warnings.
2. Para cada warning:
   - **`unused variable`**: prefijar con `_` o eliminar.
   - **`shadowed variable`**: renombrar la variable interna.
   - **`deprecated`**: actualizar al API nuevo.
   - **Irreducibles (linter bugs o diseño)**: suprimir con `set_option linter.<nombre> false`
     en el scope mínimo necesario (nunca global).
3. Verificar build limpio: `lake build` sin ninguna línea de warning.

**Criterio de finalización:** `lake build 2>&1 | Select-String "warning" | Measure-Object`
devuelve `Count : 0`.

**Prioridad:** ALTA — prerrequisito para toda reestructuración.

---

## 3. Fase 1: Interfaces como tipoclases (`FMath.Interface`) {#3-fase-1-interfaces}

> Ref: Novísimos [3], THOUGHTS.md §1 "Las interfaces son Clases de Tipos"

**Objetivo:** Biblioteca Lake independiente (`FMath.Interface`) sin dependencias externas,
que contenga las tipoclases abstractas.

### 3.1 Tipoclases de universo conjuntista — escalonamiento axiomático

El escalonamiento replica la introducción gradual de axiomas del proyecto ZFC (punto 0.9):

```
SetMembership          ← solo ∈
  └─ SetExt            ← + Extensionalidad
      └─ SetEmpty      ← + Existencia de ∅
          └─ SetPair   ← + Pares
              └─ SetSpec ← + Especificación (Comprehensión acotada)
                  └─ SetUnion  ← + Unión
                      └─ SetPower ← + Potencia
                          └─ SetInfinity ← + Infinitud    ← este es ZF⁻ (sin reemplazo ni regularidad)
                              └─ SetReplacement ← + Reemplazo
                                  └─ SetFoundation ← + Regularidad   ← esto es ZF
                                      └─ SetChoice ← + Elección      ← esto es ZFC
                                          └─ SetClassCompr ← + Comprensión de clases ← esto es MK
```

Cada paso añade exactamente un axioma como campo de la tipoclase:

```lean
-- FMath/Interface/SetUniverse.lean

class SetMembership (V : Type u) where
  mem : V → V → Prop

class SetExt (V : Type u) extends SetMembership V where
  ext : ∀ (a b : V), (∀ z, mem z a ↔ mem z b) → a = b

class SetEmpty (V : Type u) extends SetExt V where
  empty : V
  empty_spec : ∀ y, ¬ mem y empty

class SetPair (V : Type u) extends SetEmpty V where
  pair : V → V → V
  pair_spec : ∀ x a b, mem x (pair a b) ↔ (x = a ∨ x = b)

class SetSpec (V : Type u) extends SetPair V where
  sep : V → (V → Prop) → V
  sep_spec : ∀ x A P, mem x (sep A P) ↔ (mem x A ∧ P x)

class SetUnion (V : Type u) extends SetSpec V where
  sUnion : V → V
  sUnion_spec : ∀ x C, mem x (sUnion C) ↔ ∃ y, mem y C ∧ mem x y

class SetPower (V : Type u) extends SetUnion V where
  powerset : V → V
  powerset_spec : ∀ x A, mem x (powerset A) ↔ (∀ z, mem z x → mem z A)

class SetInfinity (V : Type u) extends SetPower V where
  -- Definiciones previas necesarias (sucesor, inductivo)
  omega : V
  omega_inductive : mem (SetEmpty.empty) omega ∧
    ∀ n, mem n omega → mem (SetPair.pair n (SetPair.pair n n) |> ...) omega
  omega_minimal : ∀ I, IsInductive I → ∀ n, mem n omega → mem n I

-- ... continúa para Reemplazo, Regularidad, Elección, MK
```

> **Nota:** La definición de `succ` dentro de la interfaz requiere cuidado porque
> depende de `union` y `singleton`, que a su vez se construyen sobre `pair` y `sUnion`.
> Las interfaces de `SetInfinity` en adelante necesitarán definiciones auxiliares
> (como `singleton`, `succ`, `IsInductive`) expresadas en términos de las operaciones
> anteriores. Estas se pueden definir como `def` en el namespace de la interfaz.

### 3.2. Tipoclases de estructura matemática

```lean
-- FMath/Interface/NaturalNumbers.lean

class NaturalNumbers (N : Type) where
  zero : N
  succ : N → N
  succ_inj : ∀ {a b : N}, succ a = succ b → a = b
  zero_ne_succ : ∀ n : N, zero ≠ succ n
  induction : ∀ (P : N → Prop), P zero → (∀ n, P n → P (succ n)) → ∀ n, P n

class NatAdd (N : Type) extends NaturalNumbers N where
  add : N → N → N
  add_zero : ∀ n, add n zero = n
  add_succ : ∀ n m, add n (succ m) = succ (add n m)

class NatMul (N : Type) extends NatAdd N where
  mul : N → N → N
  mul_zero : ∀ n, mul n zero = zero
  mul_succ : ∀ n m, mul n (succ m) = add (mul n m) n

class NatOrder (N : Type) extends NatMul N where
  le : N → N → Prop
  lt : N → N → Prop
  le_iff : ∀ a b, le a b ↔ ∃ k, add a k = b
  lt_iff : ∀ a b, lt a b ↔ le (succ a) b

class NatArithmetic (N : Type) extends NatOrder N where
  sub : N → N → N          -- resta truncada
  div : N → N → N          -- división entera
  modulo : N → N → N       -- resto
  pow : N → N → N          -- exponenciación
  -- Axiomas de cada operación...
```

### 3.3 Estructura de archivos propuesta

```
FMath/
  Interface/
    SetMembership.lean
    SetExt.lean
    SetEmpty.lean
    SetPair.lean
    SetSpec.lean
    SetUnion.lean
    SetPower.lean
    SetInfinity.lean
    SetReplacement.lean
    SetFoundation.lean
    SetChoice.lean
    SetClassCompr.lean
    NaturalNumbers.lean
    NatArithmetic.lean
    BooleanAlgebra.lean      -- interfaz abstracta de álgebra booleana
    Equiv.lean               -- equivalencia/isomorfismo abstracto
  Interface.lean             -- importa todo
```

### 3.4 Principios de diseño

1. **Sin dependencias externas.** Solo `import Init`.
2. **Cada tipoclase añade exactamente un axioma** (o un grupo mínimo inseparable).
3. **Nombres Mathlib**: seguir las convenciones ya adoptadas en ZfcSetTheory.
4. **Universe-polymorphic**: `(V : Type u)` en todos los casos.
5. **`Prop` vs `Bool`**: las interfaces son proposicionales. Las instancias computables
   (Aczel) pueden proveer adicionalmente instancias `Decidable`.

---

## 4. Fase 2: Instancias — proyectos existentes como modelos {#4-fase-2-instancias}

> Ref: Novísimos [4]

### 4.1 ZfcSetTheory como instancia

**Nuevo módulo:** `ZfcSetTheory/Instance.lean`

Demuestra que `U` (con los axiomas actuales) satisface cada tipoclase:

```lean
import FMath.Interface
import ZfcSetTheory

-- U satisface SetEmpty (y todos sus ancestros)
noncomputable instance : SetEmpty U where
  mem := ZFC.Axiom.Extension.mem
  ext := ZFC.Axiom.Extension.ExtSet
  empty := ZFC.Axiom.Existence.EmptySet
  empty_spec := ZFC.Axiom.Existence.EmptySet_property

-- ... escalonando hasta SetChoice (ZFC completo)
```

Para los naturales:

```lean
-- Subtipo envoltorio
def OmegaElem := { x : U // ZFC.Nat.Basic.IsNat x }

noncomputable instance : NaturalNumbers OmegaElem where
  zero := ⟨(∅ : U), zero_in_Omega⟩
  succ := fun ⟨n, hn⟩ => ⟨σ n, succ_in_Omega hn⟩
  succ_inj := fun {⟨a, ha⟩ ⟨b, hb⟩} h => by
    -- demostración usando succ_injective del proyecto actual
    ...
  zero_ne_succ := fun ⟨n, hn⟩ => by
    -- demostración usando empty_ne_succ
    ...
  induction := fun P hzero hsucc ⟨n, hn⟩ => by
    -- demostración usando nat_induction
    ...
```

**Principio clave: no se reescriben los 43 módulos existentes.** La instancia es
una capa *encima*, no un reemplazo. Todos los teoremas existentes siguen
funcionando sin cambios.

### 4.2 Peano como instancia

**Nuevo módulo:** `PeanoNatLib/Instance.lean` (en el proyecto Peano)

```lean
import FMath.Interface
import PeanoNatLib

instance : NaturalNumbers Peano.ℕ₀ where
  zero := Peano.ℕ₀.zero
  succ := Peano.ℕ₀.succ
  succ_inj := Peano.succ_inj
  zero_ne_succ := Peano.zero_ne_succ
  induction := Peano.nat_induction
```

Esta instancia es directa porque `ℕ₀` ya es un tipo tipo inductivo con exactamente
la misma estructura que `NaturalNumbers` requiere.

### 4.3 Aczel como instancia (parcial)

**En el proyecto `AczelSetTheory`:**

```lean
import FMath.Interface

-- Aczel satisface SetPower (ZF sin infinitud, sin regularidad, sin elección)
instance : SetPower HFSet where
  mem := HFSet.mem
  ext := HFSet.ext_theorem
  empty := HFSet.mk []
  ...
  powerset := HFSet.powerset
  powerset_spec := HFSet.powerset_theorem
```

**Aczel NO satisface `SetInfinity`** — este es el punto 0.7 de los Novísimos.
El escalonamiento de las tipoclases permite que Aczel sea instancia de `SetPower`
sin necesitar instanciar `SetInfinity`.

### 4.4 MKplusCAC como instancia

**Futuro.** MK satisfaría `SetClassCompr` (el nivel más alto). Dado que
`SetClassCompr extends SetChoice`, esto implica automáticamente que MK es modelo
de ZFC (punto 0.6 de los Novísimos).

### 4.5 Transporte de teoremas — el subtipo `OmegaElem` como cuello de botella

El punto más delicado es que los teoremas existentes de ZfcSetTheory están formulados
sobre `x : U` con hipótesis `IsNat x`, no sobre `OmegaElem`. Necesitamos un mecanismo
para transportar:

- **Opción A (manual):** Escribir lemas puente `OmegaElem.lift` que envuelven/desenvuelven.
  Tedioso pero predecible.
- **Opción B (macro/tactic):** Crear una táctica `omega_lift` que automatice el transporte.
  Más elegante, más esfuerzo inicial.
- **Opción C (coerción):** Definir `Coe OmegaElem U` con coerción automática, y
  demostrar que las operaciones son compatibles. Compromiso razonable.

**Recomendación:** Empezar con **Opción C** (coerción) y complementar con lemas puente
manuales donde la coerción no baste.

---

## 5. Fase 3: Teoremas abstractos contra interfaces {#5-fase-3-teoremas-abstractos}

> Ref: THOUGHTS.md §1 "el teorema fundamental, su firma será algo como:
> `theorem fundamental_arithmetic {N : Type} [Naturals N]`"

**Objetivo:** Demostrar teoremas *una sola vez* para cualquier instancia de las interfaces.

### 5.1 ¿Qué vale la pena generalizar?

| Prioridad | Teoremas | Interfaz requerida |
|-----------|----------|--------------------|
| 1 | Conmutatividad, asociatividad de +, × | `NatAdd`, `NatMul` |
| 2 | Distributividad, cancelación | `NatMul` |
| 3 | Propiedades de orden, tricotomía | `NatOrder` |
| 4 | Divisibilidad, MCD, primos | `NatArithmetic` |
| 5 | TFA (Teorema Fundamental de la Aritmética) | `NatArithmetic` + `DecidableEq` |
| 6 | Buena fundamentación de < | `NatOrder` |

### 5.2 ¿Qué NO se generaliza?

Los resultados **específicos de la teoría de conjuntos** no se abstraen:

- Operaciones con conjuntos (∩, ∪, ∖, 𝒫)
- Relaciones, funciones, productos cartesianos
- Álgebras de Boole sobre 𝒫(A)
- Ordinales, cardinales
- Codificación de Gödel

Estos son propios de cada sistema axiomático concreto y de las interfaces `SetUniverse`.

### 5.3 Estructura de archivos

```
FMath/
  Abstract/
    NatAdd.lean          -- add_comm, add_assoc, add_zero, etc.
    NatMul.lean          -- mul_comm, mul_assoc, mul_dist, etc.
    NatOrder.lean        -- tricotomy, well_ordering, etc.
    NatDiv.lean          -- division algorithm, gcd, etc.
    NatPrimes.lean       -- isPrime, TFA abstracto
  Abstract.lean          -- importa todo
```

### 5.4 Relación con Mathlib

Mathlib ya tiene tipoclases para monoides, anillos, etc. Nuestras interfaces son
**intencionalmente más restrictivas**: solo cubren los axiomas de Peano, no la
aritmética general. Esto evita la dependencia de Mathlib y mantiene la autonomía
filosófica del proyecto (todo desde ZFC/Peano/Aczel, sin matemáticas tipificadas previas).

Si en el futuro se quisiera conectar con Mathlib, nuestras instancias de `NatArithmetic`
podrían derivar instancias de `CommMonoid`, `OrderedSemiring`, etc.

---

## 6. Fase 4: Sistema de puentes entre sistemas axiomáticos {#6-fase-4-puentes}

> Ref: THOUGHTS.md §0, §2 "Isomorfismos y el paso de teoremas"

### 6.1 Puentes de inclusión (un sistema demuestra los axiomas de otro)

Cada puente es una **instancia condicional**: si tenemos `[SetX V]` (sistema fuerte),
demostramos que `V` también satisface las interfaces del sistema más débil.

| Puente | Referencia | Enunciado formal | Dificultad |
|--------|-----------|-------------------|------------|
| **0.1** Aczel → ZF⁻ | Novísimo 0.1 | `instance [AczelSet V] : SetPower V` | Media |
| **0.3** ZF → Aczel | Novísimo 0.3 | Modelo interno: `HFSet` construible dentro de ZF | Alta |
| **0.4** ZF → Peano | Novísimo 0.4 | `instance [SetInfinity V] : NaturalNumbers (OmegaElem V)` | Media (ya hecho parcialmente) |
| **0.5** Aczel → Peano | Novísimo 0.5 | `instance [AczelSet V] : NaturalNumbers (HFNat V)` | Media |
| **0.6** MK → ZFC | Novísimo 0.6 | `instance [SetClassCompr V] : SetChoice V` | Baja (herencia de `extends`) |

### 6.2 Puentes de equivalencia (isomorfismos entre tipos)

Para transportar teoremas entre implementaciones concretas:

```lean
-- FMath/Transfer/PeanoZFC.lean

-- Equivalencia entre naturales de Peano y naturales de Von Neumann
noncomputable def peanoVonNeumannEquiv :
    Peano.ℕ₀ ≃ OmegaElem U where
  toFun := fun n => ⟨fromPeano n, fromPeano_in_Omega n⟩
  invFun := fun ⟨x, hx⟩ => toPeano x hx
  left_inv := toPeano_fromPeano
  right_inv := fromPeano_toPeano
```

Este `Equiv` ya está **esencialmente demostrado** en `Peano.Import`:
`fromPeano` y `toPeano` con sus inversas forman la biyección.
Solo falta empaquetarlo como `Equiv` y demostrar la compatibilidad con las operaciones.

### 6.3 Transferencia automática de teoremas

**Objetivo final:** dada una prueba de `theorem T : P (n : Peano.ℕ₀)`, generar
automáticamente `theorem T' : P' (x : OmegaElem U)` a través del `Equiv`.

**Implementación propuesta:**

1. **Corto plazo:** Lemas `Equiv.map_*` manuales para cada operación
   (`map_zero`, `map_succ`, `map_add`, `map_mul`).
2. **Medio plazo:** Macrotáctica `transfer` (similar a la de Mathlib) que automatice
   la reescritura a lo largo del `Equiv`.
3. **Largo plazo:** Metaprogramación Lean 4 para generar las pruebas transportadas
   como `Elab.Command`.

### 6.4 Puentes de separación (metateoremas)

| Puente | Referencia | Enunciado | Dificultad |
|--------|-----------|-----------|------------|
| **0.7** ZFC ⊄ Aczel | Novísimo 0.7 | ∃ φ demostrable en ZFC y no demostrable en Aczel | Muy Alta |
| **0.8** MK ⊄ ZFC | Novísimo 0.8 | ∃ φ demostrable en MK y no demostrable en ZFC | Muy Alta |

Estos son **metateoremas**: no se prueban dentro de un sistema, sino *sobre* los sistemas.
Requieren:

- Codificación de la sintaxis formal (fórmulas como datos).
- Numeración de Gödel (inyección de fórmulas en ω).
- Representabilidad de funciones recursivas.
- Teoremas de incompletitud de Gödel (forma de Rosser).

Esto coincide con el punto [8] de `NEXT-STEPS.md` (Gödel). Se deja para las
últimas fases del proyecto.

**Ejemplo concreto para 0.7:** El axioma de infinitud no es demostrable en Aczel
(todo objeto de `HFSet` es hereditariamente finito). Formalizando Aczel como modelo
de ZF⁻, basta mostrar que ω no existe en `HFSet` — lo cual es un argumento
semántico directo, no requiere Gödel.

**Ejemplo concreto para 0.8:** `Con(ZFC)` es demostrable en MK pero no en ZFC
(por el segundo teorema de incompletitud). Esto SÍ requiere Gödel.

---

## 7. Fase 5: Modelo de Aczel — Computabilidad plena {#7-fase-5-aczel}

> Ref: THOUGHTS.md §4 "El Modelo de Aczel"

### 7.1 Tipo básico

```lean
-- AczelSetTheory/Core/HFSet.lean

/-- Conjuntos hereditariamente finitos.
    Todo objeto es un conjunto finito de objetos del mismo tipo.
    DecidableEq y Repr se derivan automáticamente. -/
inductive HFSet where
  | mk : List HFSet → HFSet
  deriving Repr

/-- Normalización: ordena y elimina duplicados para unicidad canónica. -/
def HFSet.normalize : HFSet → HFSet := ...

/-- Igualdad extensional decidible. -/
instance : DecidableEq HFSet := ...
```

### 7.2 Operaciones computables

Todas las operaciones son `def` (no `noncomputable`), evaluables con `#eval`:

```lean
-- AczelSetTheory/Core/Operations.lean

def HFSet.empty : HFSet := .mk []

def HFSet.mem (x : HFSet) (s : HFSet) : Bool :=
  match s with | .mk elems => elems.any (· == x)

def HFSet.insert (x : HFSet) (s : HFSet) : HFSet :=
  match s with | .mk elems => .mk (x :: elems) |>.normalize

def HFSet.union (a b : HFSet) : HFSet := ...
def HFSet.inter (a b : HFSet) : HFSet := ...
def HFSet.powerset (a : HFSet) : HFSet := ...
```

### 7.3 Axiomas como teoremas

La clave del modelo de Aczel: los axiomas de la teoría de conjuntos (sin infinitud)
se **demuestran como teoremas** sobre las operaciones computables:

```lean
-- AczelSetTheory/Axioms/Extension.lean

theorem HFSet.ext_theorem (a b : HFSet) :
    (∀ x, HFSet.mem x a = HFSet.mem x b) → a = b := by
  ...  -- demostración por inducción estructural

-- AczelSetTheory/Axioms/Pairing.lean

theorem HFSet.pairing (x y : HFSet) :
    ∃ z, ∀ w, HFSet.mem w z ↔ (w = x ∨ w = y) := by
  exact ⟨HFSet.mk [x, y], fun w => ...⟩
```

### 7.4 Naturales computables en Aczel

```lean
-- AczelSetTheory/Nat/Natural.lean

def HFSet.zero : HFSet := .mk []                    -- ∅
def HFSet.one  : HFSet := .mk [.mk []]              -- {∅}
def HFSet.two  : HFSet := .mk [.mk [], .mk [.mk []]] -- {∅, {∅}}

def HFSet.vonNeumann : Nat → HFSet
  | 0     => .mk []
  | n + 1 => let prev := vonNeumann n; .mk (prev :: match prev with | .mk es => es)

#eval HFSet.vonNeumann 3
-- HFSet.mk [HFSet.mk [HFSet.mk [HFSet.mk []], ...], ...]
```

### 7.5 Estructura de archivos

```
AczelSetTheory/
  lakefile.lean
  AczelSetTheory.lean          -- raíz de imports
  AczelSetTheory/
    Core/
      HFSet.lean               -- tipo inductivo + DecidableEq + Repr
      Membership.lean          -- ∈ computable (Bool) + ∈ propositional (Prop)
      Operations.lean          -- ∪, ∩, \, 𝒫 como `def`
      Normalize.lean           -- forma canónica para unicidad
    Axioms/
      Extension.lean           -- demostrado como teorema
      Empty.lean               -- demostrado como teorema
      Pairing.lean             -- demostrado como teorema
      Specification.lean       -- demostrado como teorema
      Union.lean               -- demostrado como teorema
      PowerSet.lean            -- demostrado como teorema
    Nat/
      Natural.lean             -- natural de Von Neumann computable
      Add.lean                 -- suma computable + teoremas
      Mul.lean                 -- producto computable + teoremas
      Order.lean               -- orden computable + teoremas
    Instance.lean              -- satisface FMath.Interface.SetPower
    Bridge/
      ToPeano.lean             -- HFSet.Nat ≃ Peano.ℕ₀
```

### 7.6 Test de computabilidad

Un criterio de éxito del modelo de Aczel es que todo sea `#eval`-able:

```lean
-- Verificación por ejecución
#eval HFSet.vonNeumann 5                    -- {0,1,2,3,4} = 5
#eval HFSet.union (HFSet.vonNeumann 2) (HFSet.vonNeumann 3)  -- {0,1,2} = 3
#eval HFSet.powerset (HFSet.vonNeumann 2)   -- 𝒫({0,1}) = {{},{0},{1},{0,1}}
#eval HFSet.mem (HFSet.vonNeumann 1) (HFSet.vonNeumann 3)  -- true (1 ∈ 3)
```

---

## 8. Fase 6: Proyecto unificado (`FundamentosMath`) {#8-fase-6-proyecto-unificado}

> Ref: Novísimos [5] y [6]

### 8.1 Estructura como Lake workspace

Lean 4 soporta **multi-paquetes** en un workspace. La estructura final:

```
FundamentosMath/
  lakefile.lean                -- workspace raíz
  FMath/
    Interface/                 -- Fase 1: tipoclases abstractas
    Abstract/                  -- Fase 3: teoremas contra interfaces
    Transfer/                  -- Fase 4: tácticas de transporte, Equiv
  FMath.lean                   -- importa todo FMath
  ZfcSetTheory/                -- git submodule → github.com/julian1c2a/ZfcSetTheory
  PeanoNatLib/                 -- git submodule → github.com/julian1c2a/Peano
  AczelSetTheory/              -- Fase 5: nuevo proyecto
  MKplusCAC/                   -- futuro
```

### 8.2 Lakefile raíz

```lean
-- FundamentosMath/lakefile.lean
import Lake
open Lake DSL

package FundamentosMath where
  moreServerArgs := #["-DautoImplicit=false"]

-- Sub-proyectos como dependencias locales
require FMathInterface from ./"FMath"/"Interface"

require ZfcSetTheory from ./"ZfcSetTheory"
require peanolib from ./"PeanoNatLib"
require AczelSetTheory from ./"AczelSetTheory"

-- Biblioteca raíz que importa todo
@[default_target]
lean_lib FundamentosMath where
```

### 8.3 Gestión de dependencias

```
FMath.Interface  ← sin dependencias
     ↑
     ├── ZfcSetTheory/Instance.lean (depende de Interface + ZfcSetTheory)
     ├── PeanoNatLib/Instance.lean  (depende de Interface + peanolib)
     ├── AczelSetTheory/Instance.lean (depende de Interface + AczelSetTheory)
     ↑
FMath.Abstract   ← depende solo de Interface
     ↑
FMath.Transfer   ← depende de Interface + las instancias concretas
     ↑
FundamentosMath  ← importa todo
```

**Propiedad crítica:** `FMath.Abstract` NO depende de ningún proyecto concreto.
Los teoremas abstractos se demuestran solo con las tipoclases de `FMath.Interface`.

### 8.4 Repositorios Git

| Repositorio | Contenido | Estado |
|-------------|-----------|--------|
| `julian1c2a/FundamentosMath` | Workspace raíz + FMath + submodules | Nuevo |
| `julian1c2a/ZfcSetTheory` | Proyecto ZFC (actual) | Existente, se añade `Instance.lean` |
| `julian1c2a/Peano` | Proyecto Peano (actual) | Existente, se añade `Instance.lean` |
| `julian1c2a/AczelSetTheory` | Modelo de Aczel | Nuevo |
| `julian1c2a/MKplusCAC` | Morse-Kelley + CAC | Futuro |

---

## 9. Orden de ejecución y dependencias {#9-orden-de-ejecución}

```
                    ┌─────────────────────────────────┐
                    │ Fase 0: Limpieza de warnings     │
                    │ (ZfcSetTheory + Peano)           │
                    └─────────┬───────────────────────┘
                              │
              ┌───────────────┼───────────────┐
              ▼               ▼               ▼
    ┌─────────────┐  ┌──────────────┐  ┌─────────────────┐
    │ Fase 1      │  │ Fase 5       │  │ Trabajo pendiente│
    │ Interfaces  │  │ HFSet básico │  │ dentro de ZFC    │
    │ (FMath.Intf)│  │ (Aczel core) │  │ (BoolAlg, ℤ...) │
    └──────┬──────┘  └──────┬───────┘  └─────────────────┘
           │                │
           ▼                ▼
    ┌──────────────────────────────┐
    │ Fase 2: Instancias           │
    │ ZFC + Peano + Aczel          │
    └──────────────┬───────────────┘
                   │
           ┌───────┴───────┐
           ▼               ▼
    ┌─────────────┐  ┌──────────────┐
    │ Fase 3      │  │ Fase 4       │
    │ Teoremas    │  │ Puentes      │
    │ abstractos  │  │ 0.1–0.6     │
    └──────┬──────┘  └──────┬───────┘
           │                │
           ▼                ▼
    ┌──────────────────────────────┐
    │ Fase 6: Workspace unificado  │
    │ FundamentosMath              │
    └──────────────┬───────────────┘
                   │
                   ▼
    ┌──────────────────────────────┐
    │ Fase 4 (cont.): Puentes     │
    │ 0.7–0.8 (Gödel)             │
    └──────────────────────────────┘
```

### Tabla resumen

| Orden | Fase | Esfuerzo | Bloquea a | Bloqueada por |
|-------|------|----------|-----------|---------------|
| 1 | **Fase 0**: Limpiar warnings | Bajo | Fases 1–6 | Ninguna |
| 2a | **Fase 1**: Interfaces | Medio | Fases 2, 3 | Fase 0 |
| 2b | **Fase 5**: HFSet básico | Medio | Fase 2 (Aczel) | Fase 0 |
| 3 | **Fase 2**: Instancias | Medio-Alto | Fases 3, 4 | Fases 1, 5 |
| 4a | **Fase 3**: Teoremas abstractos | Medio | Fase 6 | Fase 2 |
| 4b | **Fase 4a**: Puentes 0.1–0.6 | Alto | Fase 6 | Fase 2 |
| 5 | **Fase 6**: Workspace unificado | Bajo | Puentes 0.7–0.8 | Fases 3, 4a |
| 6 | **Fase 4b**: Puentes 0.7–0.8 | Muy alto | Ninguna | Fase 6 + Gödel |

> **Nota:** Las Fases 1 y 5 son **independientes** y pueden avanzarse en paralelo.
> Las Fases 3 y 4a también son independientes entre sí.

### Compatibilidad con trabajo pendiente existente

El trabajo pendiente dentro de ZfcSetTheory (álgebras de Boole, enteros, Gödel...)
**NO se bloquea** por los Novísimos y puede avanzar en paralelo. Solo el módulo
`Instance.lean` necesita actualizarse si se añaden nuevos axiomas o estructuras.

---

## 10. Advertencias y decisiones abiertas {#10-advertencias}

### 10.1 Riesgos

1. **Subtipo `OmegaElem`**: Es el cuello de botella de la Fase 2 para ZFC.
   Cada teorema sobre `IsNat x` debe poder transportarse. La coerción `Coe OmegaElem U`
   aliviará mucho, pero habrá casos que requieran lemas puente explícitos.

2. **Definición de `succ` en interfaces**: Dentro de `SetInfinity`, `succ` depende de
   `union` y `singleton`, que a su vez dependen de `pair`. Las tipoclases precederían
   necesitan proveer estas definiciones auxiliares. Hay que decidir si son campos de la
   tipoclase o `def` derivadas.

3. **Universos polimórficos**: `U : Type u` en ZFC es polimórfico, pero en la práctica
   siempre se usa en un universo concreto. Las interfaces deben ser igualmente polimórficas.

4. **Evitar Mathlib**: El proyecto es filosóficamente autónomo. Pero si Mathlib ya tiene
   `Equiv`, `transfer`, etc., vale la pena considerar si replicar o depender.
   **Recomendación:** Replicar lo mínimo necesario (definición de `Equiv` y lemas básicos).

### 10.2 Decisiones pendientes

- [ ] **Nombre del meta-proyecto**: `FundamentosMath`, `FMathLean`, `FoundationsOfMath`?
- [ ] **Git submodules vs require from git**: ¿Mantener repos separados con `require from git`
      (como peanolib ahora) o usar submodules en un monorepo?
- [ ] **¿Depender de Mathlib para `Equiv`?** O replicar la definición.
- [ ] **Forma canónica de HFSet**: ¿Normalización por ordenamiento, o cociente por extensionalidad?
- [ ] **¿Las tipoclases SetX deben usar `Prop` membership o `Bool`?** Recomendación: `Prop`,
      con instancias `Decidable` opcionales para modelos computables.

---

## Apéndice A: Mapa de puentes {#apéndice-a-mapa-de-puentes}

```
                    MKplusCAC
                   /    |
              [0.6]     |
                /       | [0.8] (metateorema: ∃φ en MK \ ZFC)
               ▼        |
              ZFC ◄─────┘
             / | \
        [0.4] | [0.3]
           /  |    \
          ▼   |     ▼
       Peano  |   Aczel (HFSet)
          ▲   |   / ▲
      [0.2]\  | /[0.5]
            \ |/
             \▼
        [0.7] (metateorema: ∃φ en ZFC \ Aczel)

        ──► = "demuestra los axiomas del otro como teoremas"
        ◄── = dirección inversa
```

| Puente | De → A | Axiomas demostrados | Axiomas faltantes |
|--------|--------|--------------------|--------------------|
| 0.1 | Aczel → ZF⁻ | Ext, Empty, Pair, Spec, Union, Power | Infinity, Foundation, Replacement |
| 0.2 | Peano ↪ Aczel | (embedding: naturales computables) | — |
| 0.3 | ZF → Aczel | (modelo interno: HF ⊂ V_ω) | — |
| 0.4 | ZF → Peano | (ya implementado: `fromPeano`/`toPeano`) | — |
| 0.5 | Aczel → Peano | (isomorfismo: HFNat ≃ ℕ₀) | — |
| 0.6 | MK → ZFC | (herencia: `extends SetChoice`) | — |
| 0.7 | ZFC ⊄ Aczel | Axioma de infinitud (argumento semántico) | — |
| 0.8 | MK ⊄ ZFC | Con(ZFC) (2º teorema de Gödel) | Codificación sintáctica |

---

## Apéndice B: Bocetos de código {#apéndice-b-bocetos-de-código}

### B.1 Definición completa de `SetEmpty`

```lean
-- FMath/Interface/SetEmpty.lean

universe u

class SetMembership (V : Type u) where
  mem : V → V → Prop

namespace SetMembership
  scoped notation:50 lhs:51 " ∈ " rhs:51 => SetMembership.mem lhs rhs
  scoped notation:50 lhs:51 " ∉ " rhs:51 => ¬(SetMembership.mem lhs rhs)
end SetMembership

class SetExt (V : Type u) extends SetMembership V where
  ext : ∀ (a b : V), (∀ z, mem z a ↔ mem z b) → a = b

namespace SetExt
  open SetMembership in
  def subset [inst : SetExt V] (x y : V) : Prop := ∀ z, z ∈ x → z ∈ y
  scoped notation:50 lhs:51 " ⊆ " rhs:51 => SetExt.subset lhs rhs
end SetExt

class SetEmpty (V : Type u) extends SetExt V where
  empty : V
  empty_spec : ∀ (y : V), ¬ mem y empty
```

### B.2 OmegaElem y la instancia NaturalNumbers para ZFC

```lean
-- ZfcSetTheory/Instance.lean (boceto)

import FMath.Interface
import ZfcSetTheory

open ZFC

namespace ZFC.Instance

universe u
variable {U : Type u}

/-- Subtipo de elementos de ω. -/
def OmegaElem := { x : U // Axiom.Infinity.IsNat x }

instance : Coe OmegaElem U where
  coe := Subtype.val

noncomputable instance : NaturalNumbers OmegaElem where
  zero := ⟨(∅ : U), Axiom.Infinity.zero_in_Omega⟩
  succ := fun ⟨n, hn⟩ => ⟨Nat.Basic.succ n, Axiom.Infinity.succ_in_Omega hn⟩
  succ_inj := fun {⟨a, _⟩ ⟨b, _⟩} h => by
    have := Nat.Basic.succ_injective (Subtype.mk.inj h)
    exact Subtype.ext this
  zero_ne_succ := fun ⟨n, _⟩ h => by
    exact absurd (Subtype.mk.inj h) (Nat.Basic.empty_ne_succ n)
  induction := fun P hzero hsucc ⟨n, hn⟩ => by
    apply Axiom.Infinity.nat_induction (fun x hx => P ⟨x, hx⟩)
    · exact hzero
    · intro m hm ih
      exact hsucc ⟨m, hm⟩ ih

end ZFC.Instance
```

### B.3 Teorema abstracto: conmutatividad de la suma

```lean
-- FMath/Abstract/NatAdd.lean

import FMath.Interface.NaturalNumbers

open NaturalNumbers NatAdd

theorem add_comm {N : Type} [NatAdd N] (a b : N) : add a b = add b a := by
  induction a with
  | zero => rw [add_zero, zero_add]
  | succ n ih => rw [add_succ, succ_add, ih]
```

---

*Documento vivo — se actualizará a medida que avancen las fases.*
*Referencia cruzada: THOUGHTS.md (sección NOVÍSIMOS), NEXT-STEPS.md.*
