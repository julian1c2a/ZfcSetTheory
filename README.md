# ZfcSetTheory

[![Lean 4](https://img.shields.io/badge/Lean-v4.23.0--rc2-blue)](https://leanprover.github.io/)
[![Build Status](https://img.shields.io/badge/build-passing-brightgreen)]()
[![License](https://img.shields.io/badge/license-MIT-green)](LICENSE)

Una implementación formal de la **Teoría de Conjuntos de Zermelo-Fraenkel (ZFC)** en Lean 4, sin dependencias de Mathlib.

## 📖 Descripción

Este proyecto desarrolla los axiomas fundamentales de ZFC de manera progresiva, construyendo desde los fundamentos hasta estructuras algebraicas más complejas como álgebras de Boole y retículos.

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

## 📁 Estructura del Proyecto

```
ZfcSetTheory/
├── Prelim.lean              # Definiciones preliminares (ExistsUnique)
├── Extension.lean           # Axioma de Extensionalidad + ⊆, ⊂, ⟂
├── Existence.lean           # Axioma de Existencia (∅)
├── Specification.lean       # Axioma de Especificación + ∩, \
├── Pairing.lean             # Axioma de Par + {a,b}, {a}, ⟨a,b⟩, relaciones, funciones
├── Union.lean               # Axioma de Unión + ⋃, ∪, △
├── Potencia.lean            # Axioma de Potencia (𝒫)
├── OrderedPair.lean         # Extensiones del par ordenado
├── CartesianProduct.lean    # Producto Cartesiano A ×ₛ B
├── Relations.lean           # Relaciones: equivalencia, orden parcial, orden lineal
├── BooleanAlgebra.lean      # Teoremas de álgebra booleana
├── SetOrder.lean            # Orden parcial y retículos
├── SetStrictOrder.lean      # Orden estricto
└── ZfcSetTheory.lean        # Módulo raíz
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

- [DEPENDENCIES.md](DEPENDENCIES.md) - Diagrama de dependencias entre módulos
- [COMPLETION_REPORT.md](COMPLETION_REPORT.md) - Reporte detallado del estado del proyecto
- [BOOLEAN_ALGEBRA_PLAN.md](BOOLEAN_ALGEBRA_PLAN.md) - Plan para teoremas de álgebra booleana
- [CHANGELOG.md](CHANGELOG.md) - Historial de cambios
- [NEXT_STEPS.md](NEXT_STEPS.md) - Próximos pasos y tareas pendientes

## 📄 Licencia

Este proyecto está bajo la licencia MIT. Ver [LICENSE](LICENSE) para más detalles.

## 👤 Autor

**Julián Caicedo**

---

*Última actualización: 7 de febrero de 2026*
