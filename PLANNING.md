# PLANNING — ZfcSetTheory

Documento de planificación estratégica. Recoge decisiones de arquitectura,
estrategia de documentación, plan de ramificación y hoja de ruta a largo plazo.
Se mantiene actualizado sesión a sesión como registro permanente de decisiones tomadas.

*Última actualización: 2026-05-26 (sesión 15).*

---

## 1. Visión Global

ZfcSetTheory construye matemática formal desde axiomas ZFC en Lean 4, sin depender de Mathlib.
La jerarquía de objetivos es:

1. **Fundacional**: toda definición se reduce a los seis axiomas ZFC explícitos del proyecto
   (Extensionalidad, Especificación, Par, Unión, Potencia, Infinito).
2. **Constructiva donde sea posible**: preferir definiciones computacionales
   antes que existenciales puras.
3. **Documentada para IA y humanos**: REFERENCE.md y sus hijos futuros deben permitir
   cargar un contexto matemático completo sin necesidad de leer el código Lean.
4. **Integrada con Peano**: el proyecto PeanoNatLib (`makingdecidable`) es el eje
   computable; su embedding en ZFC da una medida precisa de lo computable dentro
   de la teoría de conjuntos.

El proyecto no es solo un ejercicio técnico: la jerarquía de cuerpos
ℚ ⊂ Computables ⊂ Constructibles ⊂ Radicales ⊂ Algebraicos ⊂ ℝ
ilustra la tensión entre computabilidad y completitud, central en los
fundamentos del siglo XX (Turing, Gödel, Bishop).

---

## 2. Estado Actual (2026-05-26)

| Área | Módulos | Sorry | Errores |
|------|---------|-------|---------|
| Axiomas y SetOps (Core, Axiom/, SetOps/, incl. Tuple/TupleOps) | ~24 | 0 | 0 |
| ω, BoolAlg, Cardinal, Peano bridge | ~28 | 0 | 0 |
| Enteros ℤ | 15 | 0 | 0 |
| Racionales ℚ + sucesiones + Cauchy + Pow + TupleSeq | 18 | 0 | 0 |
| Incompletitud de ℚ (√2 irracional) | 1 | 0 | 0 |
| Puente Peano (rama master de PeanoNatLib) | 4 | 0 | 0 |
| **Total** | **93** | **0** | **0** |

*(+ barrel `ZFC/Algebra.lean` placeholder; `lake build`: 114 jobs.)*

---

## 3. Plan del Embedding Peano → ZFC

### 3.1 Embedding actual (rama master de PeanoNatLib)

Ya existe en `ZFC/Peano/`:

- `Import.lean`: `ΠZ : Peano.ℕ₀ → ω`, inyectivo, preserva sucesor y orden
- `FiniteSequences.lean` / `FiniteSequencesBridge.lean`: puente DList ↔ secuencias ZFC
- `FiniteSequencesArith.lean`: operaciones aritméticas sobre secuencias finitas

La imagen de `ΠZ` es exactamente el fragmento **hereditariamente finito** de ω en ZFC.
Esto conecta con AczelSetTheory: los conjuntos hereditariamente finitos (HF) son
exactamente los que se pueden describir sin el Axioma de Infinito, y forman una
teoría de conjuntos completa en sí mismos.

### 3.2 Embedding fuerte (rama makingdecidable — futuro)

**Cuándo**: después de que `makingdecidable` quede congelada, al terminar el
Teorema de Wilson más la infraestructura de cuerpos intermedios en Peano.

**Inventario estimado de `makingdecidable`**:

| Área | Cobertura | Observaciones |
|------|-----------|---------------|
| Aritmética básica ℕ | Completa | TFA, GCD, potencias, factorial, binomio |
| Aritmética modular | Completa | División modular, inversos, CRT |
| Teorema de Wilson | Casi completo (2026-05-01) | Toda la infraestructura necesaria probada |
| Teoría de grupos finitos | Completa | Solo sobre ℕ y listas — sin conjuntos |
| Sylow I, II, III | Completos | Probados sobre grupos finitos Peano |
| Tres teoremas de isomorfismos | Completos | Solo para grupos finitos |
| Cuerpos de números (computable, constructible…) | Planificado | A añadir antes de congelar |

**Secuencia de migración**:

1. Terminar Teorema de Wilson en Peano → congelar `makingdecidable` (tag en PeanoNatLib)
2. Implementar Abstract Algebra en ZFC (Phase 11) — magmas, grupos, anillos, cuerpos
3. Implementar Group Theory en ZFC (Phase 12) — subgrupos, cocientes, acciones, Sylow
4. Actualizar `ZFC/Peano/Import.lean` para apuntar a la rama congelada
5. Traer Wilson como teorema en ZFC vía `ΠZ` — no hay ampliación posible, viene tal cual
6. Traer aritmética modular — también computable, viene tal cual
7. Traer Sylow + tres isomorfismos — sobre la base de Phase 12 ya construida en ZFC

**Nota sobre HF y Aczel**: la imagen de `ΠZ` en ZFC es el subuniverso HF de
conjuntos hereditariamente finitos. AczelSetTheory ya tiene esta teoría construida.
Un puente AczelSetTheory → ZFC (distinto de ΠZ) podría unificar ambos proyectos
en el futuro. Queda como trabajo a largo plazo.

### 3.3 Observación sobre Computabilidad vs. Decidibilidad

Todo lo que viene de Peano (Lean 4) es **computable**: los términos del CIC son
inherentemente computacionales. Por tanto, la imagen de `ΠZ` es la parte
efectivamente computable de ω.

Sin embargo, **computabilidad ≠ decidibilidad** para los números de Phase 9a:
dada una representación `(f, N₀)` de un número computable, la **igualdad** entre
dos representaciones no es decidible en general. La comparación `≤` tampoco lo es.
Este es un resultado clásico de la teoría de la computabilidad:

- Igualdad de números computables: **Π₂-completa** (no decidible, no semidecidible)
- Comparación ≤: **también indecidible** en el caso general

Esto distingue la semántica *computable* de la *decidible*, y es lo que hace
que los números computables de Phase 9a sean matemáticamente ricos: el cuerpo
ordenado existe y es efectivo, pero su estructura de orden no tiene algoritmo.

---

## 4. Nuevas Áreas Matemáticas

### 4.0 Monomios y Polinomios (Phase 8)

**Motivación**: los polinomios sobre ℚ son la herramienta central de las Phases 9a–9d.
Un número algebraico es raíz de un polinomio con coeficientes racionales;
los constructibles son raíces de polinomios de grado ≤ 2; los radicales, raíces de
`x^n − a`; los computables admiten una representación en términos de sucesiones
racionales que aproximan raíces de polinomios.
Además, el anillo ℚ[x] es el caso prototípico del álgebra abstracta (Phase 11):
dominio de integridad euclídeo que ilustra todos los conceptos relevantes.

**Representación — Decisión D11**: un polinomio de grado n se representa como una
tupla `p : σn → RatSet` (función con dominio `σn = {0, …, n}` y codominio ⊆ RatSet).
Se escribe `p⦅k⦆` para el coeficiente de `x^k`. Esta elección reutiliza la
infraestructura de Phase 7 (`IsTuple`, `tupleGraph`, `tupleUpdate`, …) sin introducir
ningún nuevo mecanismo de representación. Un polinomio "no nulo" exige adicionalmente
`p⦅n⦆ ≠ zeroQ` (coeficiente líder distinto de cero).

**Prerequisito de Phase 8** — `Rat/Pow.lean` — ✅ **COMPLETO (2026-05-08)**:
la evaluación `polyEval p n x = ∑_{k=0}^{n} p⦅k⦆ · x^k` requiere potenciación racional
`powRatQ x n` (x^n para x ∈ RatSet, n ∈ ω). Implementado como módulo auxiliar
independiente antes de `Algebra/Polynomial.lean`, por recursión sobre ω con
`RecursionTheoremWithStep` (base `oneQ`, paso $v \mapsto v \cdot x$). 16 exports, 0 sorry.

**Módulos propuestos — `ZFC/Algebra/`**:

| Módulo | Contenido principal | Exports estimados |
|--------|---------------------|-------------------|
| `Rat/Pow.lean` *(prereq)* ✅ | `powRatQ x n`; `powRatQ_zero`, `powRatQ_succ`, `powRatQ_mem_RatSet`, `powRatQ_one`, `powRatQ_zero_base`, `powRatQ_one_base`, `powRatQ_add_exp`, `powRatQ_mul_base` | **16 (hecho)** |
| `Algebra/Polynomial.lean` | `IsPoly p n` (tupla con coefs en RatSet); `PolySet n`; `polyCoeff`; `polyEval`; `IsRoot`; `zeroPoly n`; `constPoly c`; `linearPoly a b`; `leadCoeff`; `IsNonzeroPoly`; `IsMonic`; `IsIrreduciblePoly` (solo definición) | ~20 |
| `Algebra/Monomial.lean` | `IsMonom p c k n`: `p` es tupla de grado `n` con `p⦅k⦆ = c` y cero en el resto; `monomEval`; `polyEval_monomial`; `poly_as_sum_of_monomials` | ~10 |
| `Algebra/PolyArith.lean` | `polyAdd p n q m`; `polyNeg p n`; `polySub`; `polyScalarMul c p n`; `polyMul p n q m` (grado n+m, convolución); propiedades: conmutatividad, asociatividad, distributividad; `polyMul_leadCoeff`; `polyEval_add`, `polyEval_mul`, `polyEval_neg` | ~25 |
| `Algebra/PolyDiv.lean` | `polyDivMod p n q m`: par (cociente, resto) por división euclídea; `RemainderThm`: `IsRoot p n a ↔ ∃ q, p = polyMul (linearPoly oneQ (negQ a)) q`; `roots_le_degree`: número de raíces distintas ≤ n; `RationalRootThm`: si `evalQ (a/b) = 0` (fracción irred.) entonces `a ∣ p⦅0⦆` y `b ∣ p⦅n⦆` | ~20 |
| `Algebra/PolyGcd.lean` | `polyContent p n` (MCD de coeficientes); `IsPrimitivePoly`; `GaussLemma`; `polyGcd p n q m`; algoritmo de Euclides para polinomios; `IsMinPoly p n α`: mónico, irreducible, menor grado con α raíz; `minPoly_unique`; `minPoly_divides` | ~15 |

**Orden de implementación**:

1. ✅ `Rat/Pow.lean` — potenciación racional, independiente del resto (**hecho 2026-05-08**)
2. `Algebra/Polynomial.lean` — definiciones base, depende de Pow + SetOps/Tuple ← **siguiente**
3. `Algebra/Monomial.lean` — caso especial de polinomio, depende de Polynomial
4. `Algebra/PolyArith.lean` — aritmética completa, depende de Polynomial
5. `Algebra/PolyDiv.lean` — división euclídea, depende de PolyArith
6. `Algebra/PolyGcd.lean` — GCD y polinomio mínimo, depende de PolyDiv

**Retos técnicos anticipados**:

- **`polyEval` con `seqSumQ`**: la suma `∑_{k=0}^{n} p⦅k⦆ · x^k` se expresa como
  `seqSumQ (fun k => mulQ (polyCoeff p k) (powRatQ x k)) n`, reutilizando
  `Rat/TupleSeq.lean`. Requiere verificar que la función interior toma valores en RatSet.

- **`polyMul` (convolución)**: el coeficiente `(p·q)⦅j⦆ = ∑_{i=0}^{j} p⦅i⦆ · q⦅j−i⦆`
  para j ∈ σ(n+m). Se construye con `seqSumQ` indexado sobre j, con índice desplazado.
  Es el paso más complejo de la fase.

- **`polyDivMod`**: división de p (grado n) por q (grado m ≤ n) con coeficiente
  líder invertible (siempre en ℚ). Se formaliza por inducción decreciente sobre n − m:
  en cada paso se resta el monomio `(leadCoeff p / leadCoeff q) · x^(n−m) · q`.

- **`polyContent` y Lema de Gauss**: el contenido es el MCD de los coeficientes vistos
  como enteros (numeradores y denominadores). Se apoya en `gcdOf` de `ZFC/Nat/Gcd.lean`
  via el puente de enteros y la inclusión ℤ → ℚ de `Rat/Embedding.lean`.

**Exports clave para Phase 9**:

- `IsPoly p n`, `polyEval p n x`, `IsRoot p n x`
- `IsNonzeroPoly p n`, `IsMonic p n`, `IsIrreduciblePoly p n`
- `IsMinPoly p n α`, `minPoly_unique`, `minPoly_divides`
- `polyMul`, `polyGcd`, `RemainderThm`, `roots_le_degree`

**Barril**: nuevo archivo `ZFC/Algebra.lean` con imports de todos los módulos de esta fase;
`Rat/Pow.lean` se añade al barril existente `ZFC/Rat.lean`.

---

### 4.1 Álgebra Abstracta (Phase 11)

**Motivación**: la infraestructura algebraica genérica en ZFC es necesaria para:

- Recibir los teoremas de grupos de Peano (Phase 12 + embedding)
- Fundamentar polinomios sobre el concepto de dominio de integridad (Phase 8)
- Formalizar la jerarquía de cuerpos de números intermedios (Phase 9)
- Sentar la base para espacios vectoriales y módulos (futuros)

**Principio de diseño**: todo se define como **predicados sobre conjuntos ZFC**,
no como typeclasses de Lean 4. Esto es consistente con el resto del proyecto
(`IsFunction`, `IsSeqQ`, `IsCauchyQ`, etc.) y permite razonar sobre ellos
usando la maquinaria de conjuntos ya construida.

**Módulos propuestos — `ZFC/Algebra/`**:

| Módulo | Contenido principal | Dependencias |
|--------|---------------------|--------------|
| `Algebra/Magma.lean` | `IsMagma A op` (clausura), `IsSemigroup A op` (+ asociatividad) | SetOps/Functions |
| `Algebra/Group.lean` | `IsGroup A op e inv`, `IsAbelianGroup` | Magma |
| `Algebra/Ring.lean` | `IsRing A add mul`, distributividad, `IsCommRing`, `IsDomain` | Group |
| `Algebra/Field.lean` | `IsField A add mul`, inverso multiplicativo, conexión con ℚ y futura ℝ | Ring |
| `Algebra/Morphisms.lean` | `IsGroupHom f A B`, `IsRingHom f`, núcleo, imagen, exactitud | Group, Ring |
| `Algebra/Subgroup.lean` | `IsSubgroup H G`, `IsNormalSub H G`, `IsCharacteristic H G` | Group, Morphisms |
| `Algebra/Quotient.lean` | `QuotientGroup G H`, operaciones, `quotientHom` (primer isomorfismo) | Subgroup |
| `Algebra/VectorSpace.lean` | `IsVectorSpace V F`, combinaciones lineales, dimensión finita | Field |
| `Algebra/Module.lean` | `IsModule M R`, generalización de espacio vectorial | Ring |

Los módulos de espacio vectorial y módulo pueden posponerse hasta que sean necesarios.
La prioridad es Magma → Group → Ring → Field → Morphisms → Subgroup → Quotient.

### 4.2 Teoría de Grupos (Phase 12)

**Motivación**: acoger los teoremas de Sylow y los tres teoremas de isomorfismos
provenientes de Peano, que requieren grupos sobre conjuntos ZFC generales
(no solo sobre ω).

**Módulos propuestos — `ZFC/GroupTheory/`**:

| Módulo | Contenido principal | Dependencias |
|--------|---------------------|--------------|
| `GroupTheory/Cosets.lean` | Clases laterales izq/der, índice [G:H], Teorema de Lagrange | Algebra/Subgroup |
| `GroupTheory/Action.lean` | `GroupAction G X`, órbitas, estabilizador, ecuación de clases | Algebra/Subgroup |
| `GroupTheory/Sylow.lean` | Teoremas de Sylow I, II, III; p-subgrupos | Action, Cosets |
| `GroupTheory/Iso1.lean` | Primer teorema: G/ker(f) ≅ Im(f) | Algebra/Quotient, Morphisms |
| `GroupTheory/Iso2.lean` | Segundo teorema: HN/N ≅ H/(H∩N) | Iso1 |
| `GroupTheory/Iso3.lean` | Tercer teorema: (G/N)/(H/N) ≅ G/H | Iso2 |

**Observación**: los teoremas de Sylow para grupos finitos no requieren el Axioma de
Elección. Toda la prueba es efectiva para grupos finitos, y los grupos que vendrán de
Peano son todos finitos (definidos sobre ω con cardinalidad finita).

### 4.3 Topología (Phase 13)

**Motivación**: la completitud de ℝ (Phase 10) y los teoremas de continuidad
(Bolzano, Weierstrass, Heine-Borel) son más naturales en un marco topológico.
Además, las métricas generalizan la estructura de `absQ` y `absZ` ya construidas.

**Módulos propuestos — `ZFC/Topology/`**:

| Módulo | Contenido principal | Dependencias |
|--------|---------------------|--------------|
| `Topology/Basic.lean` | `IsTopology τ X`: ∅,X ∈ τ; clausura bajo uniones y fintersecciones finitas; `IsOpen`, `IsClosed`, `Closure` | SetOps |
| `Topology/Neighborhoods.lean` | Bases de entornos, equivalencia con axiomas de abiertos; `IsNeighborhoodBase` | Basic |
| `Topology/Continuous.lean` | `IsContinuous f τ₁ τ₂`: preimagen de abierto es abierto; composición | Basic |
| `Topology/Homeomorphism.lean` | `IsHomeomorphism f`, invariantes topológicos básicos | Continuous |
| `Topology/Metric.lean` | `IsMetric d X`: no negatividad, simetría, triangular, identidad; bola abierta como base; toda métrica genera topología | Basic |
| `Topology/Compact.lean` | `IsCompact K τ`, cubrimiento finito, Heine-Borel para ℝ | Basic, Metric |
| `Topology/Connected.lean` | `IsConnected X τ`; Teorema del Valor Intermedio como consecuencia | Basic |

**Sobre métricas**: la abstracción `IsMetric d X` es natural aquí porque ya tenemos
`absQ` (métrica sobre ℚ) y tendremos `absR` (métrica sobre ℝ). Recomendación:
definir `IsMetric` en `Topology/Metric.lean` y demostrar que `d(x,y) := absQ(subQ x y)`
hace de ℚ un espacio métrico. Esto unifica el tratamiento de convergencia en ℚ
(ya hecha en `Rat/Convergence.lean`) con la topología general.

---

## 5. Estrategia de Documentación

### 5.1 Principios

- La documentación se organiza **por dominio matemático**, no por tipo de contenido
  (no separar definiciones/teoremas/exports en archivos distintos).
- Cada archivo markdown hijo contiene definiciones, teoremas y exports del dominio.
- La navegación es **bidireccional**: enlace ← y → en cabecera y pie de cada archivo hijo.
- Cada archivo hijo tiene un **"adelanto"** al inicio: párrafos resumiendo qué contiene
  y cuándo conviene cargar ese archivo específico.
- El objetivo es que una IA (o un humano) pueda cargar un único archivo hijo y tener el
  contexto matemático completo de un dominio sin leer ningún `.lean`.

### 5.2 Árbol de archivos propuesto (post-Phase 9d)

```
REFERENCE.md                          ← raíz/índice (~400 líneas)
docs/
├── REFERENCE-FOUNDATIONS.md          ← Axiomas, Core, SetOps (§3.1–§3.22)
├── REFERENCE-NAT.md                  ← ω, Peano bridge, BoolAlg, Cardinal (§3.23–§3.50)
├── REFERENCE-INT.md                  ← ℤ, 15 módulos (§3.51–§3.65)
├── REFERENCE-RAT.md                  ← ℚ + sucesiones + Cauchy, 15 módulos (§3.66–§3.83)
├── REFERENCE-ALGEBRA.md              ← Polinomios, Álgebra abstracta (Phase 7-8-11-12)
├── REFERENCE-NUMBERS.md              ← Computables, Constructibles, Radicales, Algebraicos (Phase 9)
├── REFERENCE-TOPOLOGY.md             ← Topología y métricas (Phase 13)
└── REFERENCE-PEANO.md                ← Embedding completo Peano → ZFC (Phase E)
```

Los archivos de ℝ y análisis (Phase 10) se añadirán después como hijos adicionales.

**Estimación de tamaño**: ~4.000–6.000 líneas por hijo; raíz ~400 líneas.

### 5.3 Estructura de cada archivo hijo

```markdown
# REFERENCE — [Nombre del dominio]

← [Anterior](prev.md) | [Índice](../REFERENCE.md) | [Siguiente →](next.md)

## Sobre este documento

[2-3 párrafos: qué contiene este archivo, qué teoremas clave tiene,
cuándo es útil cargar específicamente este archivo en lugar de otro]

## Módulos cubiertos

| Módulo | Estado | Exports clave |
|--------|--------|---------------|
| ...    | ✅     | ...           |

---

[contenido migrado de REFERENCE.md — secciones §3.x y §4.x del dominio]

---

← [Anterior](prev.md) | [Índice](../REFERENCE.md) | [Siguiente →](next.md)
```

### 5.4 Estructura de REFERENCE.md raíz (post-split)

```markdown
# REFERENCE — ZfcSetTheory

## Sobre este proyecto
[3-4 párrafos: qué es, qué axiomas usa, cómo navegar la documentación,
cómo cargar contexto para una sesión de trabajo en un dominio específico]

## Navegación por dominio

| Sección | Dominio | Módulos | Archivo |
|---------|---------|---------|---------|
| Fundamentos | Axiomas ZFC, SetOps, pares ordenados | ~22 | [REFERENCE-FOUNDATIONS.md](docs/REFERENCE-FOUNDATIONS.md) |
| ω y Álgebra | ℕ, BoolAlg, Cardinal, Peano | ~28 | [REFERENCE-NAT.md](docs/REFERENCE-NAT.md) |
| Enteros ℤ | Aritmética entera completa | 15 | [REFERENCE-INT.md](docs/REFERENCE-INT.md) |
| Racionales ℚ | ℚ + sucesiones + Cauchy + SqrtApprox | 15 | [REFERENCE-RAT.md](docs/REFERENCE-RAT.md) |
| Álgebra | Tuplas, polinomios, álgebra abstracta, grupos | TBD | [REFERENCE-ALGEBRA.md](docs/REFERENCE-ALGEBRA.md) |
| Números intermedios | Computables, Constructibles, Radicales, Algebraicos | TBD | [REFERENCE-NUMBERS.md](docs/REFERENCE-NUMBERS.md) |
| Topología | Topologías, métricas, compacidad | TBD | [REFERENCE-TOPOLOGY.md](docs/REFERENCE-TOPOLOGY.md) |
| Embedding Peano | ΠZ completo, Wilson, Sylow, isomorfismos | TBD | [REFERENCE-PEANO.md](docs/REFERENCE-PEANO.md) |

## Top 20 teoremas del proyecto

[lista con hiperenlaces al archivo hijo correspondiente — los teoremas más importantes
para entender el proyecto de un vistazo]
```

### 5.5 Timing del split

| Evento | Condición | Acción |
|--------|-----------|--------|
| Fin Phase 9d (algebraicos) | Phase 9a-d completas, 0 sorry | Crear rama `docs/reference-split`, migrar a `docs/` |
| Congelado Peano makingdecidable | TW probado + embedding fuerte | Crear `docs/REFERENCE-PEANO.md` |
| Fin Phase 10 (ℝ) | Phase 10 completa | Añadir `docs/REFERENCE-REAL.md` |

**Regla invariante**: el split se hace siempre en una **rama separada** `docs/*`
antes de hacer merge a master. Las ramas `docs/*` nunca tocan código `.lean`.

---

## 6. Estrategia de Branching Git

### 6.1 Rama principal

`master` = código estable, **0 sorry**, 0 errores. Nunca se mergea código con sorry.

### 6.2 Tags de hitos

| Tag | Condición de activación | Estado |
|-----|-------------------------|--------|
| `v0.9-phase6-complete` | Phase 6 + 6.5 + 6.6 completas, 0 sorry | ✅ Alcanzado (2026-05-01) |
| `v1.0-phase9-complete` | Phase 9d (algebraicos) completa, 0 sorry | 📋 Futuro |
| `v1.1-peano-frozen` | Embedding fuerte completo post-makingdecidable | 📋 Futuro |
| `v2.0-reals-complete` | Phase 10 (ℝ) completa | 📋 Futuro |

### 6.3 Ramas de trabajo planificadas

| Rama | Propósito | Puede abrirse |
|------|-----------|---------------|
| `phase-7-tuples` | `SetOps/Tuple.lean`, `SetOps/TupleOps.lean` | Ahora |
| `phase-8-polynomials` | `Algebra/Monomial.lean`, `Polynomial.lean`, ... | Tras phase-7 |
| `phase-9-intermediate` | Computables, Constructibles, Radicales, Algebraicos | Tras phase-8 |
| `phase-11-algebra` | Álgebra abstracta (Magma → Field + Morphisms) | En paralelo |
| `phase-12-groups` | GroupTheory (Cosets, Action, Sylow, Iso1-3) | Tras phase-11 |
| `phase-13-topology` | Topology (Basic, Metric, Compact, Connected) | En paralelo |
| `embedding-peano-full` | Import completo de makingdecidable congelado | Tras Peano frozen + phase-12 |
| `docs/reference-split` | Split de REFERENCE.md en `docs/` | Entre phase 9d y phase 10 |

**Reglas**:

- Las ramas `docs/*` nunca tocan código `.lean`.
- Las ramas de código nunca tocan `REFERENCE.md` de manera masiva
  (solo añadir secciones de los módulos nuevos que implementan).
- Ninguna rama se mergea a `master` si tiene `sorry` o errores.

---

## 7. Roadmap Completo

### Bloque 0: Activo ahora

- **Phase 7** (rama `phase-7-tuples`): `SetOps/Tuple.lean`, `SetOps/TupleOps.lean`
  *Pre-requisito de todo lo que sigue.*

### Bloque A: Números y Álgebra Elemental

*(Secuencial, cada fase depende de la anterior)*

- **Phase 8**: Monomios y Polinomios — `Algebra/Monomial.lean`, `Polynomial.lean`, `PolyArith.lean`, `PolyDiv.lean`
- **Phase 9a**: Números Computables — `Computable/Basic.lean`, `Arith.lean`, `Embedding.lean`, `NotComplete.lean`
- **Phase 9b**: Números Constructibles — `Constructible/Basic.lean`, `NotComplete.lean`
- **Phase 9c**: Números Radicales — `Radical/Basic.lean`, `NotComplete.lean`
- **Phase 9d**: Números Algebraicos — `Algebraic/Basic.lean`, `NotComplete.lean`
  ← **hito: tag `v1.0-phase9-complete`**

### Bloque B: Infraestructura Algebraica y de Grupos

*(Puede desarrollarse en paralelo con Bloque A después de Phase 8)*

- **Phase 11**: Álgebra Abstracta — `Algebra/Magma.lean` → `Group.lean` → `Ring.lean` → `Field.lean` → `Morphisms.lean` → `Subgroup.lean` → `Quotient.lean`
- **Phase 12**: Teoría de Grupos — `GroupTheory/Cosets.lean` → `Action.lean` → `Sylow.lean` → `Iso1-3.lean`

### Bloque C: Topología

*(Puede desarrollarse en paralelo; necesaria antes de Phase 10)*

- **Phase 13**: Topología — `Topology/Basic.lean` → `Neighborhoods.lean` → `Continuous.lean` → `Homeomorphism.lean` → `Metric.lean` → `Compact.lean` → `Connected.lean`

### Bloque D: Embedding Peano Completo

*(Depende de Bloque B completo y de que makingdecidable esté congelado)*

- **Phase E**: Embedding fuerte — actualizar `ZFC/Peano/Import.lean` + traer Wilson + aritmética modular + Sylow vía `ΠZ` sobre Phase 12
  ← **hito: tag `v1.1-peano-frozen`**

### Bloque Doc: Migración de Documentación

*(Entre Phase 9d y Phase 10, en rama separada)*

- **docs/reference-split**: migrar REFERENCE.md a árbol `docs/` con hiperenlaces bidireccionales

### Bloque F: Reales y Análisis

*(Depende de Bloque A + Bloque C)*

- **Phase 10**: Reales ℝ — construcción de Cauchy completa, completitud, Arquimediano, análisis real, FTC, series, funciones especiales
  ← **hito: tag `v2.0-reals-complete`**

---

## 8. Decisiones Arquitectónicas Tomadas

*(Registro permanente de decisiones que no deben reconsiderarse sin razón explícita)*

| # | Decisión | Descripción | Fecha |
|---|----------|-------------|-------|
| D1 | Organización por dominio | REFERENCE.md (y sus hijos) se organiza por dominio matemático, no por tipo de contenido | 2026-05-01 |
| D2 | Eliminar stubs vacíos | REFERENCE-AXIOMS.md y similares eliminados; reemplazados por `docs/` en el futuro | 2026-05-01 |
| D3 | Tag v1.0-phase9-complete | El primer tag mayor se asigna al terminar Phase 9d (algebraicos, 0 sorry) | 2026-05-01 |
| D4 | Split entre fases | Split de documentación entre Phase 9d y Phase 10, nunca en medio de una fase | 2026-05-01 |
| D5 | Ramas separadas para docs | Toda migración de documentación en rama `docs/*`; nunca afectan `.lean` | 2026-05-01 |
| D6 | Peano embedding fuerte | Esperar a makingdecidable congelado; requiere Phase 11-12 construidas en ZFC | 2026-05-01 |
| D7 | Álgebra = predicados ZFC | `IsGroup`, `IsRing`, etc. como predicados sobre conjuntos ZFC, no typeclasses | 2026-05-01 |
| D8 | Topología incluye métricas | `IsMetric` en `Topology/Metric.lean` como caso especial que genera topología | 2026-05-01 |
| D9 | Convención tuplas | Tupla de grado n = función con dominio σn = {0,...,n} (n+1 elementos) | 2026-04-30 |
| D10 | master = 0 sorry siempre | Ninguna rama se mergea si tiene sorry o errores de compilación | antes |

---

## 9. Cuestiones Abiertas

| # | Pregunta | Estado |
|---|----------|--------|
| Q1 | ¿Igualdad decidible en Computables (Phase 9a)? | Respondida: **No**. Π₂-completa. ≤ tampoco decidible. |
| Q2 | ¿Incluir métricas en Topología? | Sí (D8). `IsMetric` en `Topology/Metric.lean`. |
| Q3 | ¿Espacios vectoriales sobre ℚ o ℝ? | Primero sobre ℚ (Phase 11). Sobre ℝ después de Phase 10. |
| Q4 | ¿Hasta dónde llega el Álgebra Abstracta? | Hasta `IsField` + `Morphisms` + `Subgroup` + `Quotient`. Módulos y V.E. opcionales. |
| Q5 | ¿Cómo traer grupos finitos de Peano? | Sobre Phase 12 (grupos ZFC) + `ΠZ`: grupos finitos Peano son grupos sobre ω. |
| Q6 | ¿Axioma de Elección para Sylow? | No necesario: Sylow en grupos finitos es efectivo. |
| Q7 | ¿Dónde termina Peano makingdecidable? | Al terminar Wilson + cuerpos intermedios. Fecha: TBD. |
| Q8 | ¿Conectar con AczelSetTheory HF? | Trabajo a largo plazo. Puente HF_Aczel → ZFC (distinto de ΠZ). |
| Q9 | ¿Módulos o V.E. antes de Phase 10? | Abierto. Depende de si los algebraicos los necesitan. |
| Q10 | ¿Gödel en scope? | Futuro lejano. Requiere aritmética de Gödel y recursión primitiva en ZFC. |

---

## 10. Conexión con Otros Proyectos

| Proyecto | Relación | Estado del puente |
|----------|----------|-------------------|
| PeanoNatLib (master) | Embedding básico `ΠZ` — ℕ₀ → ω | ✅ Hecho (`ZFC/Peano/Import.lean`) |
| PeanoNatLib (makingdecidable) | Embedding fuerte — Wilson, Sylow, módulos | 📋 Futuro (Phase E) |
| AczelSetTheory | HF sets ≅ imagen de ΠZ; teoría de conjuntos finitos | 📋 Futuro (largo plazo) |
| Mathlib | Sin dependencia; este proyecto es alternativa fundacional | N/A |

---

*Próxima revisión prevista: al terminar Phase 7 (tuplas) o al cambiar la situación de makingdecidable.*
