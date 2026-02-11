# ZfcSetTheory

[![Lean 4](https://img.shields.io/badge/Lean-v4.23.0--rc2-blue)](https://leanprover.github.io/)
[![Build Status](https://img.shields.io/badge/build-passing-brightgreen)]()
[![License](https://img.shields.io/badge/license-MIT-green)](LICENSE)
[![Coverage](https://img.shields.io/badge/proofs-95%25%20complete-brightgreen)]()

> 📊 **Estado del Proyecto**: Ver [ESTADO_ACTUAL.md](ESTADO_ACTUAL.md) para detalles completos
>
> ✅ **24/24 módulos** compilando correctamente  
> ✅ **~95% de teoremas** completamente probados  
> ⚠️ **4 `sorry`** pendientes (bien documentados)

Una implementación formal de la **Teoría de Conjuntos de Zermelo-Fraenkel (ZFC)** en Lean 4, sin dependencias de Mathlib.

## 📖 Descripción

Este proyecto desarrolla los axiomas fundamentales de ZFC de manera progresiva, construyendo desde los fundamentos hasta estructuras algebraicas más complejas como álgebras de Boole y retículos. Incluye infraestructura personalizada para existencia única (`ExistsUnique`) y definiciones correctas de dominio y rango para relaciones.

## 🧱 Axiomas Implementados

| # | Axioma | Archivo | Estado |
|---|--------|---------|--------|
| 1 | **Extensionalidad** | `Extension.lean` | ✅ Completo |
| 2 | **Existencia** (Conjunto Vacío) | `Existence.lean` | ✅ Completo |
| 3 | **Especificación** (Separación) | `Specification.lean` | ✅ Completo |
| 4 | **Par** | `Pairing.lean` | ✅ Completo |
| 5 | **Unión** | `Union.lean` | ✅ Completo |
| 6 | **Conjunto Potencia** | `Potencia.lean` | ✅ Completo |
| 7 | Infinito | - | ⏳ Pendiente |
| 8 | Reemplazo | - | ⏳ Pendiente |
| 9 | Fundación | - | ⏳ Pendiente |

## ✨ Características Destacadas

### Infraestructura de Existencia Única Personalizada

- **`ExistsUnique`**: Implementación propia de `∃!` compatible con paréntesis y tipos explícitos
- **API completa**: `.intro`, `.exists`, `.choose`, `.choose_spec`, `.unique`
- **Sintaxis natural**: `∃! x, P` funciona en todos los contextos

### Dominio y Rango para Relaciones

Definiciones **matemáticamente correctas** usando `⋃(⋃ R)`:

- **`domain_rel R`**: Dominio de relación (completamente probado ✅)
- **`range_rel R`**: Rango de relación (completamente probado ✅)
- **`imag_rel R`**: Imagen de relación (alias de `range_rel`)

Teoremas clave:

- `mem_domain_rel`: `x ∈ domain_rel R ↔ ∃ y, ⟨x, y⟩ ∈ R`
- `mem_range_rel`: `y ∈ range_rel R ↔ ∃ x, ⟨x, y⟩ ∈ R`

*Nota*: Las definiciones legacy `domain`/`range` en `Pairing.lean` tienen limitaciones estructurales. Usar `domain_rel`/`range_rel` para desarrollos nuevos.

### Álgebras de Boole Atómicas

- Demostración completa de que `𝒫(A)` es un álgebra de Boole atómica
- Todo elemento es unión de átomos
- Leyes de De Morgan generalizadas para familias de conjuntos

## 📁 Estructura del Proyecto

```
ZfcSetTheory/
├── Prelim.lean                  # Definiciones preliminares (ExistsUnique)
├── Extension.lean               # Axioma de Extensionalidad + ⊆, ⊂, ⟂
├── Existence.lean               # Axioma de Existencia (∅)
├── Specification.lean           # Axioma de Especificación + ∩, \
├── Pairing.lean                 # Axioma de Par + {a,b}, {a}, ⟨a,b⟩, relaciones, funciones
├── Union.lean                   # Axioma de Unión + ⋃, ∪, △
├── PowerSet.lean                # Axioma de Potencia (𝒫)
├── OrderedPair.lean             # Extensiones del par ordenado
├── CartesianProduct.lean        # Producto Cartesiano A ×ₛ B
├── Relations.lean               # Relaciones: equivalencia, orden parcial, orden lineal
├── BooleanAlgebra.lean          # Teoremas de álgebra booleana
├── PowerSetAlgebra.lean         # Álgebra del conjunto potencia (complemento, De Morgan)
├── GeneralizedDeMorgan.lean     # Leyes de De Morgan generalizadas para familias
├── GeneralizedDistributive.lean # Leyes distributivas generalizadas
├── AtomicBooleanAlgebra.lean    # Álgebra de Boole atómica (𝒫(A) es atómica)
├── SetOrder.lean                # Orden parcial y retículos
├── SetStrictOrder.lean          # Orden estricto
├── Cardinality.lean             # Teoremas de Cantor y Cantor-Schröder-Bernstein
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

## 📦 Instalación

```bash
# Clonar el repositorio
git clone https://github.com/julian1c2a/ZfcSetTheory.git
cd ZfcSetTheory

# Compilar con Lake
lake build
```

## 🔧 Requisitos

- **Lean 4**: v4.23.0-rc2 o superior
- **Lake**: Incluido con Lean 4

## 📚 Documentación Adicional

### Estado y Desarrollo

- **[ESTADO_ACTUAL.md](ESTADO_ACTUAL.md)** - ⭐ **Estado completo del proyecto** (actualizado 2026-02-11)
  - Logros recientes (ExistsUnique, domain_rel/range_rel)
  - Análisis de los 4 `sorry` pendientes con niveles de dificultad
  - Arquitectura y jerarquías de dependencias
  - Próximos pasos con estimaciones de tiempo
- [CHANGELOG.md](CHANGELOG.md) - Historial de cambios detallado
- [NEXT_STEPS.md](NEXT_STEPS.md) - Próximos pasos y tareas pendientes

### Informes Técnicos

- [COMPLETION_REPORT.md](COMPLETION_REPORT.md) - Reporte detallado del estado del proyecto
- [DEPENDENCIES.md](DEPENDENCIES.md) - Diagrama de dependencias entre módulos
- [BOOLEAN_ALGEBRA_PLAN.md](BOOLEAN_ALGEBRA_PLAN.md) - Plan para teoremas de álgebra booleana

## 📄 Licencia

Este proyecto está bajo la licencia MIT. Ver [LICENSE](LICENSE) para más detalles.

## 👤 Autor

**Julián Caicedo**

---

*Última actualización: 7 de febrero de 2026*
