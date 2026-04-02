# Known Issues — ZfcSetTheory Project

**Last updated**: 2026-07-22

---

## Lean 4.28.0 Notation Gotchas

Problemas descubiertos durante el desarrollo de `BoolAlg.Representation.lean`. Se documentan aquí para evitar repetir los mismos errores en módulos futuros.

### 1. Clash de notación `∪` / `∩` con typeclasses `Union` / `Inter`

**Problema**: Nuestras notaciones infix `∪` (precedencia 50) e `∩` (precedencia 50) colisionan con las typeclasses `Union` e `Inter` incorporadas en Lean 4. Cuando se usan en firmas de teoremas, el elaborador intenta resolver la typeclass en lugar de usar nuestra notación, produciendo errores de tipo crípticos.

**Solución**: En firmas de teoremas y definiciones, usar las funciones directamente (`union X Y`, `inter X Y`) en lugar de la notación infix. La notación puede usarse sin problemas dentro de cuerpos de demostración cuando el contexto de tipos ya está fijado.

**Archivos afectados**: Cualquier módulo de `BoolAlg/` que defina teoremas con `∪` o `∩` en la firma.

### 2. Ambigüedad del nombre `Complement`

**Problema**: El identificador `Complement` es ambiguo entre `_root_.Complement` (función del prelude de Lean) y `@PowerSetAlgebra.Complement` (nuestra definición en `BoolAlg.PowerSetAlgebra`). Intentar `unfold Complement` produce un error de ambigüedad.

**Solución**: Usar `Complement_is_specified` (que reescribe la pertenencia al complemento como `mem_sdiff_iff`) en lugar de `unfold Complement; rw [mem_sdiff_iff]`.

**Archivos afectados**: `BoolAlg/Representation.lean`, y potencialmente cualquier módulo futuro que use `Complement`.

### 3. Notación `^∁[ expr ]` con precedencia máxima

**Problema**: La notación postfija `^∁[ Atoms A ]` para el complemento relativo tiene precedencia máxima y puede parsear incorrectamente expresiones compuestas, especialmente cuando el argumento contiene aplicaciones de función.

**Solución**: Usar paréntesis explícitos o la función `Complement` directamente cuando la expresión del argumento es compleja.

### 4. Destructuración de `intro` tras `unfold` + `rw`

**Problema**: Tras una secuencia `unfold ...; rw [mem_sep_iff]`, el objetivo queda en un término no completamente beta-reducido. Usar `intro ⟨ha, hY⟩` (destructuración directa) falla porque Lean espera un par, pero el término aún no está normalizado.

**Solución**: Usar `intro h` seguido de proyecciones `h.1` / `h.2`, o bien usar `simp only [mem_sep_iff]` (que normaliza mejor) en lugar de `rw`.

---

## Otros problemas conocidos

_(Ninguno por ahora.)_
