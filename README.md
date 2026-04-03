# ZfcSetTheory

[![Lean 4](https://img.shields.io/badge/Lean-v4.28.0-blue)](https://leanprover.github.io/)
[![Build Status](https://img.shields.io/badge/build-passing-brightgreen)](REFERENCE.md)
[![License](https://img.shields.io/badge/license-MIT-green)](LICENSE)
[![Coverage](https://img.shields.io/badge/proofs-100%25%20complete-brightgreen)](REFERENCE.md)

> 📊 **Project Status**: See [REFERENCE.md](REFERENCE.md) for complete technical reference
>
> ✅ **47/47 modules** compiling successfully
> ✅ **100% of theorems** completely proven
> ✅ **0 `sorry`** in all 47 modules

Una implementación formal de la **Teoría de Conjuntos de Zermelo-Fraenkel (ZFC)** en Lean 4, sin dependencias de Mathlib.

## 📖 Descripción

Este proyecto desarrolla los axiomas fundamentales de ZFC de manera progresiva, construyendo desde los fundamentos hasta estructuras algebraicas más complejas como álgebras de Boole y retículos. Incluye infraestructura personalizada para existencia única (`ExistsUnique`) y definiciones correctas de dominio y rango para relaciones.

## 🧱 Axiomas ZFC Implementados

| # | Axioma | Archivo | Estado |
|---|--------|---------|--------|
| 1 | **Extensionalidad** | `Extension.lean` | ✅ Completo |
| 2 | **Existencia** (Conjunto Vacío) | `Existence.lean` | ✅ Completo |
| 3 | **Especificación** (Separación) | `Specification.lean` | ✅ Completo |
| 4 | **Par** | `Pairing.lean` | ✅ Completo |
| 5 | **Unión** | `Union.lean` | ✅ Completo |
| 6 | **Conjunto Potencia** | `PowerSet.lean` | ✅ Completo |
| 7 | **Infinito** | `Infinity.lean` | ✅ Completo |
| 8 | Reemplazo | - | 🔄 Futuro |
| 9 | Fundación | - | 🔄 Futuro |
| 10 | Elección | - | 🔄 Futuro |

## 🚀 Construcciones Avanzadas (más allá de los axiomas básicos)

| Categoría | Módulos | Descripción | Estado |
|-----------|---------|-------------|--------|
| **Pares Ordenados** | `OrderedPair.lean` | Par de Kuratowski, teoremas fundamentales | ✅ Completo |
| **Producto Cartesiano** | `SetOps.CartesianProduct.lean` | A ×ₛ B, pertenencia, proyecciones | ✅ Completo |
| **Relaciones** | `SetOps.Relations.lean` | Equivalencia, orden parcial/lineal, clases | ✅ Completo |
| **Funciones** | `SetOps.Functions.lean` | Inyectivas, suryectivas, biyectivas, composición | ✅ Completo |
| **Números Naturales** | `Nat.Basic.lean` | ℕ como ordinales de von Neumann | ✅ Completo |
| **Recursión en ℕ** | `Induction.Recursion.lean` | Teorema de recursión sobre naturales | ✅ Completo |
| **Isomorfismo Von Neumann ↔ Peano** | `PeanoImport.lean` | Biyección ℕ_VN ↔ Peano.ℕ₀ (peanolib) | ✅ Completo |
| **Suma en ℕ (ZFC)** | `Nat.Add.lean` | Suma via Recursión, puente `fromPeano_add`, semianillo | ✅ Completo |
| **Multiplicación en ℕ (ZFC)** | `Nat.Mul.lean` | Mul via Recursión, puente `fromPeano_mul`, anillo conmutativo | ✅ Completo |
| **Sustracción saturada en ℕ** | `Nat.Sub.lean` | Monus via Recursión (sustracción truncada), puente `fromPeano_sub` | ✅ Completo |
| **División euclídea en ℕ** | `Nat.Div.lean` | `divOf`/`modOf` via Patrón B (isomorfismo), algoritmo de Euclides | ✅ Completo |
| **Potenciación en ℕ** | `Nat.Pow.lean` | `pow` via RecursiveFn + mulFn, puente `fromPeano_pow` | ✅ Completo |
| **Aritmética en ℕ (GCD, LCM, Bézout)** | `Nat.Arith.lean` | `div`/`mod` nativo ZFC, `gcdOf`/`lcmOf` Patrón B, Bézout substractivo | ✅ Completo |
| **Factorial en ℕ** | `Nat.Factorial.lean` | `factorial` via Patrón B (peanolib), 10 propiedades | ✅ Completo |
| **GCD/LCM nativo ZFC** | `Nat.Gcd.lean` | GCD vía algoritmo euclídeo, LCM, propiedades divisibilidad | ✅ Completo |
| **Primalidad y TFA** | `Nat.Primes.lean` | `isPrime` ZFC-nativo, TFA Existencia + Unicidad | ✅ Completo |
| **Coeficientes binomiales** | `Nat.Binom.lean` | `binomOf` Patrón B, regla de Pascal, C(n,k)·k!·(n−k)!=n! | ✅ Completo |
| **Máximo y mínimo** | `Nat.MaxMin.lean` | `maxOf`/`minOf` Patrón B, 29 teoremas de retículo | ✅ Completo |
| **Teorema de Newton** | `Nat.NewtonBinom.lean` | `binomTermOf` Patrón B 4-arg, teorema binomial | ✅ Completo |
| **Buen fundamento** | `Nat.WellFounded.lean` | Accesibilidad, buena ordenación de ω | ✅ Completo |
| **Secuencias finitas** | `Peano.FiniteSequences.lean` | `isFinSeq`, `FinSeqSet`, `appendElem`, 15 teoremas | ✅ Completo |
| **Conjuntos finitos** | `SetOps.FiniteSets.lean` | `isFiniteSet`, biyecciones, equipotencia refl/symm/trans | ✅ Completo |
| **Aritmética de secuencias** | `Peano.FiniteSequencesArith.lean` | `seqSum`, `seqProd`, `familyProduct`, `card_familyProduct` | ✅ Completo |
| **Puente DList ↔ ZFC** | `Peano.FiniteSequencesBridge.lean` | `nth`, `dlistToSeq`, `isPrimeSeq`, TFA nativo | ✅ Completo |
| **Álgebra Booleana** | `BoolAlg.Basic.lean` | Leyes fundamentales, idempotencia, absorción | ✅ Completo |
| **Anillo Booleano** | `BoolAlg.Ring.lean` | Diferencia simétrica, propiedades de anillo | ✅ Completo |
| **Álgebra de 𝒫(A)** | `BoolAlg.PowerSetAlgebra.lean` | Complemento, De Morgan, distributividad | ✅ Completo |
| **De Morgan Generalizado** | `BoolAlg.GenDeMorgan.lean` | Leyes para familias arbitrarias | ✅ Completo |
| **Distributividad Generalizada** | `BoolAlg.GenDistributive.lean` | Leyes para familias arbitrarias | ✅ Completo |
| **Álgebra Booleana Atómica** | `BoolAlg.Atomic.lean` | 𝒫(A) es atómica, representación por átomos | ✅ Completo |
| **Orden Parcial** | `SetOps.SetOrder.lean` | Retículos, orden en conjuntos | ✅ Completo |
| **Orden Estricto** | `SetOps.SetStrictOrder.lean` | Propiedades de orden estricto | ✅ Completo |
| **Álgebra Booleana Completa** | `BoolAlg.Complete.lean` | 𝒫(A) es retículo completo y AB completa atómica | ✅ Completo |
| **Álgebra Finita/Cofinita** | `BoolAlg.FiniteCofinite.lean` | FinCofAlg(ω), clausura, contraejemplo completitud | ✅ Completo |
| **Representación de Stone** | `BoolAlg.Representation.lean` | Toda BA completa atómica ≅ algún 𝒫(A) | ✅ Completo |
| **Cardinalidad de 𝒫 finito** | `Cardinal.FinitePowerSet.lean` | |𝒫(F)| = 2^n para F finito | ✅ Completo |
| **BA Finita** | `BoolAlg.FiniteBA.lean` | Toda BA finita tiene cardinalidad 2^n | ✅ Completo |
| **Anillo ↔ Álgebra Booleana** | `BoolAlg.BoolRingBA.lean` | Correspondencia formal BR ↔ BA, round-trips | ✅ Completo |
| **Cardinalidad** | `Cardinal.Basic.lean` | Teorema de Cantor, CSB | ✅ Completo |

### Total: 47 módulos — 47/47 con 0 sorry

## ✨ Características Destacadas

### Infraestructura de Existencia Única Personalizada

- **`ExistsUnique`**: Implementación propia de `∃!` compatible con paréntesis y tipos explícitos
- **API completa**: `.intro`, `.exists`, `.choose`, `.choose_spec`, `.unique`
- **Sintaxis natural**: `∃! x, P` funciona en todos los contextos

### Dominio y Rango para Relaciones

Definiciones **matemáticamente correctas** usando `⋃(⋃ R)`:

- **`domain R`**: Dominio de relación (completamente probado ✅)
- **`range R`**: Rango de relación (completamente probado ✅)
- **`imag R`**: Imagen de relación (alias de `range`)

Teoremas clave:

- `mem_domain`: `x ∈ domain R ↔ ∃ y, ⟨x, y⟩ ∈ R`
- `mem_range`: `y ∈ range R ↔ ∃ x, ⟨x, y⟩ ∈ R`

*Nota*: Las definiciones legacy `domain`/`range` en `Pairing.lean` tienen limitaciones estructurales. Usar las definiciones de `SetOps.Relations.lean` para desarrollos nuevos.

### Álgebras de Boole Atómicas

- Demostración completa de que `𝒫(A)` es un álgebra de Boole atómica
- Todo elemento es unión de átomos
- Leyes de De Morgan generalizadas para familias de conjuntos

## 📁 Estructura del Proyecto

```text
ZfcSetTheory/
├── Prelim.lean                  # Definiciones preliminares (ExistsUnique)
├── Extension.lean               # Axioma de Extensionalidad + ⊆, ⊂, ⟂
├── Existence.lean               # Axioma de Existencia (∅)
├── Specification.lean           # Axioma de Especificación + ∩, \
├── Pairing.lean                 # Axioma de Par + {a,b}, {a}, ⟨a,b⟩, relaciones, funciones
├── Union.lean                   # Axioma de Unión + ⋃, ∪, △
├── PowerSet.lean                # Axioma de Potencia (𝒫)
├── OrderedPair.lean             # Extensiones del par ordenado
├── SetOps.CartesianProduct.lean        # Producto Cartesiano A ×ₛ B
├── Relations.lean               # Relaciones: equivalencia, orden parcial, orden lineal
├── BoolAlg.Basic.lean          # Teoremas de álgebra booleana
├── BoolAlg.PowerSetAlgebra.lean         # Álgebra del conjunto potencia (complemento, De Morgan)
├── BoolAlg.GenDeMorgan.lean     # Leyes de De Morgan generalizadas para familias
├── BoolAlg.GenDistributive.lean # Leyes distributivas generalizadas
├── BoolAlg.Atomic.lean    # Álgebra de Boole atómica (𝒫(A) es atómica)
├── SetOps.SetOrder.lean                # Orden parcial y retículos
├── SetOps.SetStrictOrder.lean          # Orden estricto
├── Cardinality.lean             # Teoremas de Cantor y Cantor-Schröder-Bernstein
├── Nat.Basic.lean          # ℕ como ordinales de von Neumann (predecessor exportado)
├── Infinity.lean                # Axioma del Infinito y ω (nat_mem_wf probado)
├── Recursion.lean               # Teorema de recursión sobre ℕ (completo)
├── PeanoImport.lean             # Isomorfismo Von Neumann ↔ Peano (peanolib)
├── Nat.Add.lean       # Suma en ω vía Recursión + puente fromPeano_add
├── Nat.Mul.lean       # Multiplicación en ω vía Recursión + puente fromPeano_mul
├── Nat.Sub.lean       # Sustracción saturada (monus) + puente fromPeano_sub
├── Nat.Div.lean       # División euclídea (divOf/modOf) via Patrón B
├── Nat.Pow.lean       # Potenciación en ω vía RecursiveFn + mulFn
├── Nat.Arith.lean     # Divisibilidad, GCD, LCM, Bézout (nativo ZFC + Patrón B)
├── Nat.Factorial.lean # Factorial en ω via Patrón B (peanolib)
├── Nat.Gcd.lean       # GCD/LCM ZFC-nativo (algoritmo euclídeo)
├── Nat.Primes.lean    # Primalidad ZFC-nativa + TFA
├── Nat.Binom.lean     # Coeficientes binomiales Patrón B
├── Nat.MaxMin.lean    # Máximo y mínimo en ω Patrón B
├── Nat.NewtonBinom.lean # Teorema binomial de Newton
├── Nat.WellFounded.lean # Buen fundamento de ω
├── Peano.FiniteSequences.lean         # Secuencias finitas en ZFC
├── Peano.FiniteSequencesArith.lean    # Aritmética de secuencias finitas
├── Peano.FiniteSequencesBridge.lean   # Puente DList ↔ ZFC, nth, TFA nativo
├── BoolAlg.Complete.lean   # 𝒫(A) es retículo completo + AB completa atómica
├── BoolAlg.Representation.lean # Teorema de representación: BA completa atómica ≅ 𝒫(A)
├── BoolAlg.FiniteCofinite.lean           # FinCofAlg(ω), paridad, contraejemplo completitud
├── BoolAlg.FiniteBA.lean       # Toda BA finita tiene cardinalidad 2^n
├── BoolAlg.BoolRingBA.lean     # Correspondencia Anillo Booleano ↔ Álgebra Booleana
├── SetOps.FiniteSets.lean              # Conjuntos finitos en ZFC
├── Cardinal.FinitePowerSet.lean # |𝒫(F)| = 2^n para F finito
└── ZfcSetTheory.lean            # Módulo raíz
```

## 🛠️ Construcciones Disponibles

### Operaciones de Conjuntos

- **Pertenencia**: `x ∈ A`
- **Subconjunto**: `A ⊆ B`, `A ⊂ B`
- **Conjunto vacío**: `∅`
- **Singleton**: `{a}`
- **Par no ordenado**: `{a, b}`
- **Par ordenado (Kuratowski)**: `⟨a, b⟩ = {{a}, {a, b}}`
- **Unión binaria**: `A ∪ B`
- **Intersección binaria**: `A ∩ B`
- **Diferencia**: `A \ B`
- **Diferencia simétrica**: `A △ B`
- **Unión familiar**: `⋃ C`
- **Intersección familiar**: `⋂ C`
- **Conjunto potencia**: `𝒫 A`
- **Producto cartesiano**: `A ×ₛ B`

### Relaciones y Funciones

- Relaciones binarias R ⊆ A ×ₛ A
- Propiedades: reflexiva, simétrica, transitiva, antisimétrica, asimétrica
- Relaciones de equivalencia
- Clases de equivalencia y conjuntos cociente
- Órdenes parciales, lineales y estrictos
- Órdenes bien fundados
- Funciones (parciales, totales)
- Funciones inyectivas, suryectivas, biyectivas
- Dominio y rango

### Álgebra de Boole

- **Leyes de De Morgan generalizadas**: `(A \ ⋃ F) = ⋂ (A \ F)` y duales
- **Leyes distributivas generalizadas**: `X ∩ (⋃ F) = ⋃ { X ∩ Y | Y ∈ F }`
- **Átomos en 𝒫(A)**: Los singletons son exactamente los átomos
- **𝒫(A) es atómica**: Todo elemento no vacío contiene un átomo

### Teoría de Cardinalidad

- **Teorema de Cantor**: No existe biyección A → 𝒫(A)
- **Inyección canónica**: El mapa x ↦ {x} es inyección A → 𝒫(A)
- **Dominación estricta**: A se inyecta en 𝒫(A) pero no viceversa
- **Teorema de Cantor-Schröder-Bernstein**: Si existen inyecciones f: A → B y g: B → A, entonces existe biyección A ↔ B

## � Naming Conventions

El proyecto adopta convenciones de nombres estilo [Mathlib](https://leanprover-community.github.io/contribute/naming.html):

- **Conclusión primero**: `isNat_succ_of_isNat` — la conclusión va antes, las hipótesis con `_of_`
- **Bicondicionales**: sufijo `_iff` — `mem_powerset_iff`
- **Propiedades algebraicas**: sufijos cortos — `_comm`, `_assoc`, `_refl`, `_trans`
- **Especificaciones**: `mem_X_iff` en lugar de `X_is_specified`

Para el detalle completo, consultar [NAMING-CONVENTIONS.md](NAMING-CONVENTIONS.md).

## �📦 Instalación

```bash
# Clonar el repositorio
git clone https://github.com/julian1c2a/ZfcSetTheory.git
cd ZfcSetTheory

# Compilar con Lake
lake build
```

## 🔧 Requisitos

- **Lean 4**: v4.28.0 o superior
- **Lake**: Incluido con Lean 4

## 📚 Additional Documentation

### Status and Development

- **[REFERENCE.md](REFERENCE.md)** - 📖 **Complete technical reference** (13000+ lines)
  - 47/47 modules fully documented
  - All definitions, theorems, and exports with Lean4 signatures
  - Dependency tracking and namespace organization
  - §1.2: ZFC axiom dependency mapping for all 47 modules
  - §4: Importance annotations (high/medium/low) for all theorems
- [CHANGELOG.md](CHANGELOG.md) - Detailed change history
- [DEPENDENCIES.md](DEPENDENCIES.md) - Dependency diagrams and module relationships
- [NEXT-STEPS.md](NEXT-STEPS.md) - Project roadmap and future plans

## 📄 Licencia

Este proyecto está bajo la licencia MIT. Ver [LICENSE](LICENSE) para más detalles.

## 👤 Autor

Julián Calderón Almendros

## 🙏 Créditos y Reconocimientos

Este proyecto se desarrolló basándose en las siguientes fuentes:

### Recursos Educativos

- **"Razonando con Lean"** - José A. Alonso  
  Canal de YouTube con tutoriales de Lean 4 (y otros asistentes de demostración automática, además de cursos de lenguajes de programación funcional como Haskell)

- **Adrián GQ** ([@conjuntos_y_logica](https://www.youtube.com/@conjuntos_y_logica))  
  Canal de YouTube sobre teoría de conjuntos y lógica (3 cursos completos de teoría de conjuntos, comenzando en ZFC, temario Conjuntos I, II y III, además de cursos de lógica)

### Referencias Bibliográficas

- **"Axiomatic Set Theory"** - Patrick Suppes (1960/1972)  
  Fundamentos de teoría axiomática de conjuntos

- **"Axiomatic Set Theory"** - Paul Bernays (1958)  
  Desarrollo formal de los axiomas ZFC

### Herramientas de IA

- **Claude Code AI** (Anthropic)  
  Asistencia en desarrollo y documentación

- **Gemini AI** (Google)  
  Apoyo en resolución de problemas

---

**Autor**: Julián Calderón Almendros
*Last updated: 2026-04-10*
