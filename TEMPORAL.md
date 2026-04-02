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

## Próximos pasos sugeridos

1. **Fase 4 del plan** — Sistema de anotaciones (@importance, @axiom_system)
2. **Enteros ℤ en ZFC** — clases de equivalencia de pares (a, b) ∈ ω × ω
3. **Axioma de Reemplazo** — requerido para funciones con codominios grandes
4. **Axioma de Fundación** — para función rango y estratificación del universo
5. **Teorema de representación** — Toda álgebra booleana completa atómica es isomorfa a algún 𝒫(A)
