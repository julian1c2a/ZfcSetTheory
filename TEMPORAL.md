# TEMPORAL — Notas de trabajo temporales

**Fecha**: 2026-04-02
**Autor**: Julián Calderón Almendros

## Estado actual

Reorganización profunda del proyecto en curso (ver `/memories/session/plan.md`).

### Completados recientemente

- ~~Plan de demostración `card_familyProduct`~~ — ✅ Completado 2026-03-30
- ~~Estado de compilación (39 módulos)~~ — ✅ Superado: 43/43 módulos, 0 sorry
- ~~BoolAlg.Complete.lean + BoolAlg.FiniteCofinite.lean~~ — ✅ Completados 2026-04-01
- ~~Proyección CBA en REFERENCE.md~~ — ✅ Completado 2026-04-07 (§3.41, §4.37, §6.38)
- ~~Fase 3: Convención de nombres Mathlib~~ — ✅ Completado 2026-04-02 (185 identificadores renombrados en 40 archivos)
- ~~Propagación renombramientos a REFERENCE.md~~ — ✅ Completado 2026-04-02 (185 identificadores actualizados, §0.5 actualizado)

### Fase 0 — Documentación preparatoria (2026-04-07)

- ✅ Proyectar BoolAlg.Complete en REFERENCE.md (43/43 módulos proyectados)
- ✅ §23 Convenciones de nombres añadido a AIDER-AI-GUIDE.md
- ✅ §0 Guía de convenciones añadida a REFERENCE.md
- ✅ Sección de naming añadida a README.md
- ✅ Creado NAMING-CONVENTIONS.md (documento de referencia completo)
- ✅ Actualizado TEMPORAL.md

### Reorganización del proyecto — Estado

Fases del plan de reorganización (aprobado 2026-04-07):

1. ✅ **Fase 1**: Estructura de directorios — 43 archivos movidos a 8 subdirectorios temáticos
2. ✅ **Fase 2**: Namespace `SetUniverse` → `ZFC` + sub-namespaces alineados con directorios
3. ✅ **Fase 3**: Renombrado de identificadores según convenciones Mathlib (commit `81f9075`)
4. **Fase 4**: Sistema de anotaciones (@importance, @axiom_system)

## Siguiente objetivo: Teorema de Representación de Álgebras Booleanas

### Estado de los items de álgebras booleanas

| # | Item | Estado |
|---|------|--------|
| 1 | 𝒫(A) es álgebra booleana completa atómica | ✅ `BoolAlg.Complete.lean` |
| 2 | **Teorema de representación**: toda BA completa atómica ≅ algún 𝒫(A) | ❌ Pendiente |
| 3 | Functor Anillo Booleano ↔ Álgebra de Boole | ❌ Pendiente |
| 4 | Contraejemplo: FinCofAlg(ω) no es completa | ✅ `BoolAlg.FiniteCofinite.lean` |
| 5 | \|𝒫(F)\| = 2^n para F finito | ❌ Pendiente |
| 6 | Toda álgebra booleana finita tiene cardinalidad 2^n | ❌ Pendiente |

### Plan de demostración del Teorema de Representación (item 2)

Dado un álgebra booleana completa atómica (B, ∧, ∨, ¬, 0, 1):

1. Tomar A = Atoms(B)
2. Construir φ : B → 𝒫(A) definida por φ(x) = {a ∈ A | a ≤ x}
3. Demostrar que φ preserva ∧, ∨, ¬ (es homomorfismo de álgebras booleanas)
4. Demostrar inyectividad: la atomicidad garantiza que si φ(x) = φ(y) entonces x = y
5. Demostrar sobreyectividad: la completitud garantiza que todo elemento es el supremo de los átomos debajo de él, dando que φ es sobre

**Archivo propuesto**: `BoolAlg/Representation.lean`
**Dependencias**: `BoolAlg.Complete`, `BoolAlg.Atomic`, `Cardinality`

### Después: Fase 4

Tras completar los items 2, 3, 5, 6 de álgebras booleanas → Fase 4 (sistema de anotaciones @importance, @axiom_system).

## Próximos pasos sugeridos (posteriores)

1. **Enteros ℤ en ZFC** — clases de equivalencia de pares (a, b) ∈ ω × ω
2. **Axioma de Reemplazo** — requerido para funciones con codominios grandes
3. **Axioma de Fundación** — para función rango y estratificación del universo
