# Guía de Requisitos para REFERENCE.md y Documentación del Proyecto

**Última actualización:** 2026-04-21 20:00
**Autor**: Julián Calderón Almendros

Este documento establece los requisitos y estándares para la documentación técnica del proyecto ZfcSetTheory (módulo principal `ZFC`).

---

## Requisitos para REFERENCE.md

### (0.) **Esta documentación es de tipo técnico, no de usuario final**, incluso como referencia de la IA, para no tener que cargar el proyecto completo. Debe ser clara, precisa y completa, pero no necesariamente amigable para usuarios sin conocimientos técnicos

### (1.) **Los diferentes módulos .lean**: tanto en el módulo raíz como en los módulos secundarios, con su ubicación, namespace, dependencias y estado de documentación (si está documentado o no, o si está pendiente de documentación)

### (2.) **Las dependencias entre los módulos**: cada módulo tiene que tener claramente documentado a qué otros módulos depende, y qué módulos dependen de él, para entender la estructura del proyecto y las relaciones entre los diferentes componentes. Esto es especialmente importante para la IA, para que pueda entender cómo se relacionan los diferentes módulos y cómo navegar por el proyecto sin necesidad de cargarlo completamente

### (3.) **Espacios de nombres y relaciones entre ellos**: al no ser necesariamente iguales los espacios de nombre que los módulos, es importante documentar claramente qué espacios de nombre existen, a qué módulos pertenecen, y cómo se relacionan entre sí. Esto ayudará a la IA a entender la organización del proyecto y a navegar por él de manera más eficiente

### (4.) **Definiciones introducidas**: por cada módulo y espacio de nombres debe quedar claras las definiciones que se introducen, con su ubicación, dependencias, y formato tanto en nomenclatura matemática como en firma lean4, para que se puedan usar como referencia en la documentación y en los comentarios de los archivos .lean, y para que la IA pueda entender claramente qué definiciones existen, cómo se relacionan entre sí, y cómo se pueden usar en demostraciones o construcciones más elaboradas

#### (4.1.) **Cómo reflejar en la documentación las definiciones**: Debe quedar, además de la firma lean4, la nomenclatura matemática (sin explicaciones, los destinatarios de esta documentación son matemáticos y técnicos en lean4) de cada definición siguiendo lo más fielmente posible la estructura del código. Debe aparecer el módulo y el espacio de nombres al que pertenece, y las dependencias necesarias para construir la definición

#### (4.2.) **Característica de computabilidad**: Debe indicarse si la definición es computable o no, si tiene par booleano

#### (4.3.) **Característica de buena fundación**: Debe indicarse si en la definición se contiene una demostración de terminación de la computación (*terminated by*)

#### (4.4.) **Notación**: Debe quedar registrada la notación introducida por cada definición, si es infija o prefija, o más compleja, qué símbolos se usan y qué prioridades hay entre las notaciones, para que se puedan usar correctamente en la documentación y en los comentarios de los archivos .lean, y para que la IA pueda entender claramente cómo se pueden usar en demostraciones o construcciones más elaboradas

### (5.) **Axiomas introducidos y sus referencias**: cada axioma debe tener claramente documentado dónde se encuentra, en qué módulo, en qué namespace, y el orden en el que se declaran/definen, su relación con las definiciones

### (6.) En cuanto a los axiomas y las definiciones, las queremos

#### (6.1.) En **nomenclatura matemática (no lean code)**, para una fácil comprensión humana, y para que se puedan usar como referencia en la documentación y en los comentarios de los archivos .lean. No necesitamos explicaciones, el lenguaje matemático se bastará por sí mismo

#### (6.2.) **Firma lean4** para que cuando se llamen en demostraciones o construcciones más elaboradas, se haga correctamente

#### (6.3.) Deben quedar registradas las **dependencias** para construir el axioma

### (7.) Teoremas principales **sin demostración de ningún tipo**, con su referencia a dónde se encuentran, módulo, namespace, orden en el que se declaran/demuestran

#### (7.1.) En **nomenclatura matemática (no lean code)**, para una fácil comprensión humana, y para que se puedan usar como referencia en la documentación y en los comentarios de los archivos .lean. No se necesitan explicaciones, el lenguaje matemático se bastará por sí mismo

#### (7.2.) **Firma lean4** para que cuando se llamen en demostraciones o construcciones más elaboradas, se haga correctamente

#### (7.3.) Deben quedar registradas las **dependencias** para construir la demostración del teorema

### (8.) Nada que no esté demostrado o construido debe estar en este archivo, ni siquiera como comentario o como "teorema pendiente". Solo lo que ya esté demostrado o construido en los archivos .lean

### (9.) Cada vez que cargas un archivo .lean, actualizas (si es necesario) el REFERENCE.md con lo que se ha demostrado o construido en ese archivo, siguiendo los puntos anteriores. Si hace falta anotar una fecha y la fecha de la última modificación del archivo .lean, estará bien, para trazar bien lo que de hecho tenemos

### (10.) Sistema de Documentación Modular

**PROBLEMA RESUELTO**: REFERENCE.md alcanzó 234k tokens, excediendo la ventana de contexto.

**SOLUCIÓN**: Sistema modular con archivos especializados:

| Archivo | Contenido | Tokens aprox. | Propósito |
|---------|-----------|---------------|-----------|
| **REFERENCE.md** | Índice maestro + tabla de módulos | ~10k | Punto de entrada, siempre cargar primero |
| **REFERENCE-AXIOMS.md** | Todos los axiomas (§2) | ~15k | Axiomas ZFC completos |
| **REFERENCE-DEFINITIONS.md** | Definiciones principales (§3) | ~50k | Definiciones exportables |
| **REFERENCE-THEOREMS.md** | Teoremas principales (§4) | ~80k | Teoremas sin demostraciones |
| **REFERENCE-NOTATION.md** | Toda la notación (§5) | ~10k | Símbolos y prioridades |
| **REFERENCE-EXPORTS.md** | Todos los exports (§6) | ~30k | API pública por módulo |

**Total**: ~195k tokens distribuidos en 6 archivos manejables

**Protocolo de carga**:
1. Cargar siempre **REFERENCE.md** primero (índice maestro)
2. Cargar **solo los submódulos necesarios** para la tarea actual:
   - Para consultar axiomas → cargar REFERENCE-AXIOMS.md
   - Para consultar definiciones → cargar REFERENCE-DEFINITIONS.md
   - Para consultar teoremas → cargar REFERENCE-THEOREMS.md
   - Para consultar notación → cargar REFERENCE-NOTATION.md
   - Para consultar exports → cargar REFERENCE-EXPORTS.md
3. Para proyectar un módulo .lean:
   - Cargar REFERENCE.md
   - Cargar REFERENCE-AXIOMS.md si el módulo define axiomas
   - Cargar REFERENCE-DEFINITIONS.md si el módulo define definiciones
   - Cargar REFERENCE-THEOREMS.md si el módulo prueba teoremas
   - Cargar REFERENCE-NOTATION.md si el módulo introduce notación
   - Cargar REFERENCE-EXPORTS.md siempre (para actualizar exports)
   - Actualizar los archivos correspondientes
   - Actualizar la tabla §1.1 en REFERENCE.md

**Límite de tokens**: Cada archivo REFERENCE-*.md debe mantenerse **bajo 50k tokens**. Si un archivo crece demasiado, subdividirlo (ej: REFERENCE-THEOREMS-NAT.md, REFERENCE-THEOREMS-INT.md, etc.)

### (11.) Cuando leas este archivo introduce en cada archivo .lean una cabecera de instrucciones de su relación con REFERENCE.md, para que al entrar y leer, si es que es necesario, un archivo .lean, se recuerde la necesidad de **proyectar** ese archivo de código en REFERENCE.md

### (12.) Defino **proyectar** un archivo .lean en REFERENCE.md como el proceso de actualizar REFERENCE.md con toda la información relevante demostrada o construida en ese archivo .lean, siguiendo los puntos anteriores

### (13.) Por información relevante me refiero a todas las definiciones, notaciones, axiomas, teoremas no privados, y cualquier otro contenido que se haya demostrado o construido en ese archivo .lean, y que sea necesario para entender el proyecto, para usarlo como referencia, o para construir demostraciones o construcciones más elaboradas

### (14.) Todo lo exportable en un módulo .lean debe estar proyectado en REFERENCE.md, y debe aparecer en el export de ese módulo .lean

---

## Requisitos de Timestamps

### (15.) Formato de Fecha y Hora

Todos los archivos de documentación técnica deben incluir timestamps completos con el siguiente formato:

**Formato requerido**: `YYYY-MM-DD HH:MM` (ISO 8601 abreviado)

**Ejemplos válidos**:

- `2026-02-12 14:30`
- `2026-02-12 09:15`
- `2026-01-05 23:45`

**Dónde aplicar**:

- **REFERENCE.md**: Timestamp principal en el encabezado del documento
- **CHANGELOG.md**: Fechas de cada entrada
- **DEPENDENCIES.md**: Fecha de última actualización
- **Cualquier archivo de resumen técnico**: Incluir timestamp de última modificación

**Propósito**: Permite rastrear cuánto está desactualizado un archivo respecto a REFERENCE.md y viceversa, incluso dentro de la misma sesión de trabajo.

**Ejemplo de uso**:

```markdown
**Last updated**: 2026-02-12 14:30
```

---

## Requisitos de Autoría y Licencia

### (16.) Información de Autoría

En todos los archivos de documentación principal (README.md, REFERENCE.md), debe quedar claro:

**Autor**: Julián Calderón Almendros

### (17.) Créditos y Reconocimientos

Los siguientes créditos deben estar claramente visibles en README.md:

**Recursos Educativos**:

- "Razonando con Lean" - José A. Alonso (YouTube)
- Adrián GQ (@conjuntos_y_logica) - YouTube

**Referencias Bibliográficas**:

- "Axiomatic Set Theory" - Patrick Suppes (1960/1972)
- "Axiomatic Set Theory" - Paul Bernays (1958)

**Herramientas de IA**:

- Claude Code AI (Anthropic)
- Gemini AI (Google)

### (18.) Licencia

**Licencia del proyecto**: MIT License

Debe estar claramente indicada en:

- Archivo LICENSE (texto completo con copyright de Julián Calderón Almendros)
- README.md (sección de licencia con enlace)
- Badge en README.md: `[![License](https://img.shields.io/badge/license-MIT-green)](LICENSE)`

### (19.) Cabeceras de Archivos .lean

**Todos los archivos .lean DEBEN incluir una cabecera con información de copyright y licencia.**

**Formato requerido**:

```lean
/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/
```

**Dónde aplicar**: En TODOS los archivos `.lean` del proyecto, antes de cualquier `import`.

**Colocación exacta**:

1. Abrir el archivo .lean
2. Primera línea: `/-`
3. Segunda línea: `Copyright (c) 2026. All rights reserved.`
4. Tercera línea: `Author: Julián Calderón Almendros`
5. Cuarta línea: `License: MIT`
6. Quinta línea: `-/`
7. Sexta línea: Línea en blanco
8. Séptima línea en adelante: `import ...` y código

**Excepciones**: Ninguna - todos los archivos `.lean`, incluyendo el módulo principal `ZFC.lean`.

**Propósito**:

- Clarificar propiedad del código
- Comunicar licencia MIT explícitamente en el código fuente
- Cumplir con estándares de código abierto
- Facilitar rastreo legal y atribución

**Verificación**:

```bash
Get-ChildItem -Recurse -Filter "*.lean" | Select-String "Copyright (c) 2026" | Measure-Object
# Debe devolver N (N es el número total de archivos .lean)
```

---

## Sistema de Bloqueo de Archivos .lean

### (20.) Política de archivos desbloqueados

**Regla principal**: En todo momento, como máximo **un único archivo `.lean`** puede estar desbloqueado para edición.

**Herramienta**: `git-lock.bash` en la raíz del proyecto. Implementa dos niveles de protección:

| Nivel | Comando | Reversible | Propósito |
|-------|---------|------------|-----------|
| **Lock** | `lock` / `unlock` | Sí | Un archivo a la vez durante desarrollo |
| **Freeze** | `freeze` / `thaw --confirm` | Solo emergencia | Módulo completado — inmutable para siempre |

Archivos de seguimiento:

- `locked_files.txt` — todos los archivos bloqueados (lock + freeze)
- `frozen_files.txt` — solo módulos congelados permanentemente

```bash
bash git-lock.bash lock   ZFC/Archivo.lean   # bloqueo temporal
bash git-lock.bash unlock ZFC/Archivo.lean   # desbloqueo temporal
bash git-lock.bash freeze ZFC/Archivo.lean   # congelado permanente
bash git-lock.bash thaw   ZFC/Archivo.lean --confirm  # descongelar (emergencia)
bash git-lock.bash list                      # muestra estado de todos
bash git-lock.bash init                      # instala/reinstala hook pre-commit
```

**Protocolo de trabajo (lock)**:

1. **Al inicio de sesión**: Verificar con `bash git-lock.bash list` qué archivos están desbloqueados. Si hay más de uno, bloquear todos excepto el que se va a editar.
2. **Al cambiar de archivo**: Bloquear el archivo actual **antes** de desbloquear el siguiente.
3. **Al final de la sesión**: Bloquear **todos** los archivos `.lean` modificados en esa sesión. No dejar ningún `.lean` desbloqueado entre sesiones.
4. **Verificación al hacer commit**: El hook `pre-commit` rechaza commits que toquen archivos en `locked_files.txt`. Esto es una red de seguridad, no un sustituto del protocolo.

**Consecuencia de violar la regla**: Si se detecta más de un archivo desbloqueado, bloquear todos y empezar de nuevo con el archivo correcto.

### (20b.) Protocolo de congelado de módulos — módulos completados inmutables

Cuando un módulo alcanza el estado ✅ Completo en REFERENCE.md, debe **congelarse**.
Un módulo congelado es permanentemente inmutable: no puede desbloquearse, solo extenderse.

```bash
bash git-lock.bash freeze ZFC/Nat/Basic.lean   # marcar como congelado permanentemente
bash git-lock.bash list                         # muestra [frozen] vs [locked]
```

**Intentar desbloquear un módulo congelado está bloqueado** con un mensaje que apunta al protocolo de extensión.

**Solo para emergencias** — descongelar un módulo:

```bash
bash git-lock.bash thaw ZFC/Nat/Basic.lean --confirm
```

El flag `--confirm` es obligatorio. Tras descongelar, actualizar el estado en REFERENCE.md y documentar la razón.

#### Protocolo de extensión de módulos congelados

Cuando un módulo congelado `Foo.lean` necesita contenido nuevo:

1. Crear `FooExt.lean` en el mismo directorio.
2. Importar el módulo congelado y reabrir su namespace:

   ```lean
   /-
   Copyright (c) 2026. All rights reserved.
   Author: Julián Calderón Almendros
   License: MIT
   -/
   import ZFC.Foo

   namespace ZFC   -- mismo namespace que Foo.lean
   -- nuevas definiciones y teoremas aquí
   end ZFC
   ```

3. Añadir `FooExt.lean` al barrel/root y a REFERENCE.md.
4. `Foo.lean` permanece congelado e intacto.

**Regla de nombres**: extensiones siguen `UpperCamelCase`:

| Módulo base | Extensión |
|-------------|----------|
| `Nat/Basic.lean` | `Nat/BasicExt.lean` |
| `Nat/Primes.lean` | `Nat/PrimesExt.lean` |

Se prefieren nombres descriptivos del contenido (`Nat/ArithDivisibility.lean`) sobre numerados (`Nat/ArithExt1.lean`).

#### Tabla de códigos de estado para REFERENCE.md

| Código | Significado |
|--------|-------------|
| ✅ Completo | Proyectado completamente. Puede estar bloqueado (temporal). |
| 🧊 Congelado | Congelado permanentemente. Solo extensiones via `*Ext.lean`. |
| 🔶 Parcial | Documentado parcialmente. |
| 🔄 En progreso | En desarrollo activo. |
| ❌ Pendiente | Aún no iniciado. |

Transición de estados: 🔄 → 🔶 → ✅ → 🧊. El estado 🧊 es final.

---

## Scripts Disponibles

| Script | Propósito |
|--------|-----------|
| `bash git-lock.bash lock/unlock <file>` | Bloqueo temporal de archivo |
| `bash git-lock.bash freeze <file>` | Congelado permanente de módulo |
| `bash git-lock.bash thaw <file> --confirm` | Descongelado de emergencia |
| `bash git-lock.bash list` | Mostrar archivos bloqueados y congelados |
| `bash git-lock.bash init` | Instalar/reinstalar hook pre-commit |
| `bash new-module.bash ModuleName` | Crear nuevo módulo desde plantilla |
| `bash gen-root.bash` | Regenerar archivo de imports raíz |
| `bash check-sorry.bash` | Encontrar todos los `sorry` en el proyecto |
| `bash update-toolchain.bash v4.x.x` | Actualizar toolchain Lean con verificación de build |
| `make help` | Mostrar todos los targets del Makefile |

---

## Versiones del Proyecto (resumen de CHANGELOG.md)

### Versión actual: [Unreleased] — 2026-03-08

- **Nat.Add.lean** (nuevo módulo): suma en ω via Recursión, teorema puente `fromPeano_add`, 3 definiciones (`successorFn`, `addFn`, `add`), 16 teoremas (semianillo conmutativo: conmutatividad, asociatividad, cancelación izquierda/derecha, monotonía, tricotomía con adición)
- **Nat.Mul.lean** (nuevo módulo): multiplicación en ω via Recursión, teorema puente `fromPeano_mul`, 2 definiciones (`mulFn`, `mul`), 13 teoremas (anillo conmutativo: distributividad izquierda/derecha, asociatividad, identidades, conmutatividad)
- **PeanoImport.lean** (ampliado): +4 teoremas de transporte de recursión con paso (`recursion_transport_step`, `recursion_transport_step_inv`), +2 teoremas de puente de orden (`fromPeano_lt_iff`, `fromPeano_le_iff`)
- **REFERENCE.md**: proyectados todos los nuevos módulos y teoremas (§3.22, §3.23, §4.18, §4.19, §5.11, §5.12, §6.15-6.17)
- **Cardinality.lean**: ✅ confirmado 0 sorry (CSB completamente demostrado)

### [0.9.0] — 2026-03-04

- **PeanoImport.lean** (nuevo módulo): isomorfismo Von Neumann ↔ Peano, `fromPeano`/`toPeano`, biyección completa, 7 teoremas iniciales
- **Infinity.lean**: `nat_mem_wf` demostrado sin sorry
- **Nat.Basic.lean**: exports de predecessor ampliados

### [0.8.0] — 2026-02-07

- BoolAlg.PowerSetAlgebra, BoolAlg.GenDeMorgan, BoolAlg.GenDistributive, BoolAlg.Atomic: álgebra de Boole atómica completa

### [0.7.0] — 2026-02-07

- Relations.lean: relaciones de equivalencia, orden parcial/lineal, bien fundadas, clases de equivalencia

### [0.6.0] — 2026-02-07

- OrderedPair.lean: par ordenado de Kuratowski, extensiones
- SetOps.CartesianProduct.lean: producto cartesiano A ×ₛ B

### [0.5.0] — 2026-02-06

- PowerSet.lean: axioma del conjunto potencia

### [0.4.0] — 2026-02-05

- SetOps.SetStrictOrder.lean, SetOps.SetOrder.lean: órdenes y retículos

### [0.3.0] — 2026-02-04

- BoolAlg.Basic.lean, Union.lean (operaciones binarias): álgebra booleana básica

### [0.2.0] — 2026-02-03

- Pairing.lean: pares, singletons, pares ordenados (Kuratowski), funciones básicas

### [0.1.0] — 2026-02-02

- Prelim.lean, Extension.lean, Existence.lean, Specification.lean: fundamentos ZFC

---

## Comandos de Revisión de Módulos

### (21.) Sistema de Comandos para Revisión Sistemática

Para facilitar la revisión sistemática de módulos .lean y su proyección en REFERENCE.md, se definen los siguientes comandos:

#### Comando: `revisar <módulo>`

**Sintaxis**: `revisar <nombre_módulo.lean>`

**Acción**:

1. Cargar el archivo `ZFC/<nombre_módulo.lean>` si no está ya en el chat
2. Analizar el contenido del módulo:
   - Cabecera de copyright y licencia
   - Definiciones (con notación, computabilidad, terminación)
   - Axiomas (ubicación, namespace, orden)
   - Teoremas principales (sin demostración)
   - Exports
3. Comparar con REFERENCE.md:
   - Verificar si el módulo está proyectado
   - Identificar definiciones/teoremas/exports faltantes
   - Detectar inconsistencias en el estado de proyección
4. Actualizar REFERENCE.md §1.1 con:
   - Estado de revisión (✅ Completo / ⚠️ Parcial / ❌ No proyectado)
   - Lista detallada de acciones necesarias
   - Fecha de revisión (formato YYYY-MM-DD)
5. Descargar el módulo del chat al finalizar

**Ejemplo de uso**:

```
revisar PowerSet.lean
```

#### Comando: `proyecta <módulo>`

**Sintaxis**: `proyecta <nombre_módulo.lean>`

**Acción**:

1. Cargar el archivo `ZFC/<nombre_módulo.lean>` si no está ya en el chat

2. Cargar **REFERENCE.md** (índice maestro) si no está ya en el chat

3. Identificar qué archivos REFERENCE-*.md necesitas y cargarlos:
   - Si el módulo tiene axiomas → cargar **REFERENCE-AXIOMS.md**
   - Si el módulo tiene definiciones → cargar **REFERENCE-DEFINITIONS.md**
   - Si el módulo tiene teoremas → cargar **REFERENCE-THEOREMS.md**
   - Si el módulo tiene notación → cargar **REFERENCE-NOTATION.md**
   - Siempre cargar **REFERENCE-EXPORTS.md**

4. Extraer toda la información relevante del módulo según AI-GUIDE.md:
   - Axiomas con ubicación, namespace, orden, enunciado matemático, firma Lean4, dependencias
   - Definiciones con ubicación, namespace, orden, enunciado matemático, firma Lean4, notación, computabilidad, terminación, dependencias
   - Teoremas principales con ubicación, namespace, orden, enunciado matemático, firma Lean4, dependencias (sin demostración)
   - Exports completos

5. Actualizar **solo los archivos REFERENCE-*.md correspondientes**:
   - **REFERENCE-AXIOMS.md**: crear/actualizar sección §2.X si hay axiomas
   - **REFERENCE-DEFINITIONS.md**: crear/actualizar sección §3.X si hay definiciones
   - **REFERENCE-THEOREMS.md**: crear/actualizar sección §4.X si hay teoremas
   - **REFERENCE-NOTATION.md**: crear/actualizar sección §5.X si hay notación
   - **REFERENCE-EXPORTS.md**: crear/actualizar sección §6.X con exports
   - **REFERENCE.md**: actualizar tabla §1.1 con estado "✅ Completo" y contadores
   - Renumerar secciones si es necesario

6. Actualizar timestamps en **todos los archivos modificados** (formato YYYY-MM-DD HH:MM)

7. Descargar el módulo del chat al finalizar

**Ejemplo de uso**:

```
proyecta PowerSet.lean
```

**Nota importante**: Este comando ahora trabaja con el sistema modular, cargando solo los archivos necesarios para evitar exceder la ventana de contexto (234k tokens).

#### Comando: `siguiente módulo`

**Sintaxis**: `siguiente módulo`

**Acción**:

1. Consultar REFERENCE.md §1.1 para identificar módulos pendientes de revisión
2. Analizar dependencias en REFERENCE.md (tabla §1.1)
3. Seleccionar el módulo con menos dependencias no revisadas
4. Informar al usuario qué módulo se va a revisar y por qué
5. Solicitar confirmación antes de proceder

**Ejemplo de uso**:

```
siguiente módulo
```

#### Comando: `estado revisión`

**Sintaxis**: `estado revisión`

**Acción**:

1. Leer REFERENCE.md §1.1
2. Generar resumen con:
   - Total de módulos revisados (✅)
   - Total de módulos con acciones pendientes (⚠️)
   - Total de módulos no proyectados (❌)
   - Total de módulos pendientes de revisión ([ ])
   - Lista de módulos por categoría
3. Mostrar próximo módulo sugerido según dependencias

**Ejemplo de uso**:

```
estado revisión
```

#### Comando: `verificar proyección <módulo>`

**Sintaxis**: `verificar proyección <nombre_módulo.lean>`

**Acción**:

1. Cargar el archivo `ZFC/<nombre_módulo.lean>`
2. Cargar REFERENCE.md
3. Verificar exhaustivamente:
   - Todos los axiomas están proyectados
   - Todas las definiciones están proyectadas
   - Todos los teoremas principales están proyectados
   - Todos los exports están documentados
   - La notación está registrada
   - Las dependencias están correctas
   - El estado en tabla §1.1 es correcto
4. Generar informe de verificación
5. Actualizar REFERENCE.md §1.1 si se detectan problemas
6. Descargar el módulo del chat al finalizar

**Ejemplo de uso**:

```
verificar proyección Nat.Basic.lean
```

#### Comando: `ciclo revisión completo`

**Sintaxis**: `ciclo revisión completo`

**Acción**:

1. Ejecutar `siguiente módulo`
2. Ejecutar `revisar <módulo_seleccionado>`
3. Si el módulo requiere proyección, preguntar al usuario si proceder
4. Si el usuario confirma, ejecutar `proyectar <módulo_seleccionado>`
5. Repetir hasta que no queden módulos pendientes
6. Generar informe final de revisión

**Ejemplo de uso**:

```
ciclo revisión completo
```

### (22.) Protocolo de Trabajo con Comandos

**Flujo recomendado**:

1. **Inicio de sesión de revisión**:

   ```
   estado revisión
   ```

2. **Revisión individual**:

   ```
   siguiente módulo
   revisar <módulo>
   proyecta <módulo>  # proyectar según AI-GUIDE.md (sistema modular)
   ```

3. **Revisión automática**:

   ```
   ciclo revisión completo
   ```

4. **Verificación post-proyección**:

   ```
   verificar proyección <módulo>
   ```

5. **Guardar y subir cambios**:

   ```
   guarda_y_sube "Mensaje descriptivo del commit"
   ```

**Reglas de los comandos**:

- Los comandos son **case-insensitive** (mayúsculas/minúsculas no importan)
- Los nombres de módulos deben incluir la extensión `.lean`
- Los comandos siempre descargan los módulos .lean del chat al finalizar
- Los comandos siempre actualizan timestamps en formato YYYY-MM-DD HH:MM
- Los comandos siempre actualizan REFERENCE.md §1.1 con el estado actual
- Los comandos respetan el sistema de bloqueo de archivos (§20)
- `proyecta` ahora trabaja con el **sistema modular** (REFERENCE-*.md)
- `guarda_y_sube` maneja automáticamente el ciclo completo de unlock → commit → push → lock

---

## Convenciones de Nombres (estilo Mathlib)

### (23.) Sistema de Nombres para Definiciones y Teoremas

El proyecto adopta las [convenciones de nombres de Mathlib](https://leanprover-community.github.io/contribute/naming.html) como estándar. A continuación se resumen las reglas principales. Para el detalle completo con ejemplos y desgloses comentados, consultar `NAMING-CONVENTIONS.md`.

#### Reglas de Capitalización

| Tipo de declaración | Convención | Ejemplo |
|---------------------|------------|---------|
| Teoremas, lemas (terms de `Prop`) | `snake_case` | `union_comm`, `mem_powerset_iff` |
| Types, Props, Structures, Classes | `UpperCamelCase` | `IsFunction`, `IsNat`, `BoolAlg.Basic` |
| Funciones (retornan `U`) | `lowerCamelCase` | `powerset`, `union`, `sUnion` |
| Acrónimos como grupo | `ZFC` (namespace) / `zfc` (en snake_case) | |

#### Diccionario de Símbolos → Palabras

| Símbolo | En nombres | | Símbolo | En nombres |
|---------|-----------|---|---------|-----------|
| ∈ | `mem` | | ∪ | `union` |
| ∉ | `not_mem` | | ∩ | `inter` |
| ⊆ | `subset` | | ⋃ | `sUnion` |
| ⊂ | `ssubset` | | ⋂ | `sInter` |
| 𝒫 | `powerset` | | \ | `sdiff` |
| σ | `succ` | | △ | `symmDiff` |
| ∅ | `empty` | | ᶜ | `compl` |
| = | `eq` | | ↔ | `iff` |
| ≠ | `ne` | | → | `of` (implícito) |
| ¬ | `not` | | ⟂ | `disjoint` |
| + | `add` | | * | `mul` |
| - | `sub`/`neg` | | ^ | `pow` |
| / | `div` | | ∣ | `dvd` |
| ≤ | `le` | | < | `lt` |
| 0 | `zero` | | 1 | `one` |

#### Reglas de Formación de Nombres (resumen)

1. **Conclusión primero, hipótesis con `_of_`**: `isNat_succ_of_isNat` (concl = isNat succ, hip = isNat)
2. **Bicondicionales con `_iff`**: `mem_powerset_iff` (∈ 𝒫 ↔ ⊆)
3. **Eliminar `_wc`**: usar `.mp`/`.mpr` del iff, o `_of_` para implicaciones separadas
4. **Propiedades axiomáticas**: `_comm`, `_assoc`, `_refl`, `_trans`, `_antisymm`, `_self`, `_left`/`_right`, `_cancel`, `_mono`, `_inj`, `_injective`
5. **Predicados como prefijo** en teoremas: `isNat_zero`, `isNat_succ` (excepto `_injective`, `_surjective`)
6. **Abreviaturas estándar**: `pos` (> 0), `neg` (< 0), `nonpos` (≤ 0), `nonneg` (≥ 0)
7. **Definiciones Prop**: `UpperCamelCase` (`IsNat`, `IsFunction`); en nombres de teoremas: `lowerCamelCase` (`isNat_zero`)
8. **Funciones no-Prop**: `lowerCamelCase` sin prefijos redundantes (`union` no `BinUnion`, `powerset` no `PowerSetOf`)
9. **Especificaciones**: `mem_X_iff` en lugar de `X_is_specified`
10. **Unicidad/existencia**: `X_unique` en lugar de `XExistsUnique`
11. **Variantes laterales**: `subset_union_left`, `subset_union_right`
12. **Nombres propios**: se conservan (`cantor_no_surjection`, `cantor_schroeder_bernstein`)

#### Referencia completa

Consultar `NAMING-CONVENTIONS.md` para:

- Desgloses comentados de cada regla con ejemplos del proyecto
- Tabla de renombramientos actual → nuevo
- Guía de transición

### Sufijos Axiomáticos Estándar

| Sufijo | Significado | | Sufijo | Significado |
|--------|------------|---|--------|------------|
| `_comm` | conmutatividad | | `_self` | operación consigo mismo |
| `_assoc` | asociatividad | | `_left`/`_right` | variante lateral |
| `_refl` | reflexividad | | `_cancel` | cancelación |
| `_trans` | transitividad | | `_mono` | monotonicidad |
| `_antisymm` | antisimetría | | `_inj` | inyectividad (iff) |
| `_symm` | simetría | | `_injective` | inyectividad (predicado) |
| `_irrefl` | irreflexividad | | `_surjective` | sobreyectividad |

---

### (NC-1) Módulos (archivos `.lean`)

`UpperCamelCase`. Nombrados según el contenido matemático, no el rol técnico.

| Patrón | Ejemplo |
|--------|---------|
| `UpperCamelCase.lean` | `SetOps.lean`, `CartesianProduct.lean`, `Primes.lean` |

- Módulo raíz: `ZFC.lean` — solo imports y exports, sin nuevas definiciones.
- Plantilla: `_template.lean` — el prefijo guión bajo indica archivo utilitario no importado.
- Extensión de módulo congelado: `FooExt.lean` — importa `Foo.lean`, reabre su namespace.
- Se prefieren extensiones con nombre de contenido: `NatArithDivisibility.lean` sobre `NatArithExt1.lean`.

---

### (NC-2) Namespaces

`UpperCamelCase`. Reflejan el tema matemático del módulo.

| Nivel | Patrón | Ejemplo |
|-------|--------|---------|
| Raíz | `ZFC` | `namespace ZFC` |
| Sub | `ZFC.Tema` | `namespace ZFC.Nat`, `namespace ZFC.SetOps` |
| Hoja | `ZFC.Tema.Subtema` | `namespace ZFC.Nat.Arith`, `namespace ZFC.BoolAlg.Basic` |

- Una namespace por módulo como regla general.
- No crear sub-namespaces solo para agrupar dentro de un archivo — usar `section` en su lugar.
- Las declaraciones `private` no necesitan namespace propio.

---

### (NC-3) Tipos y predicados Prop (`def` que retorna `Type` o `Prop`)

`UpperCamelCase`. Sigue la convención de Mathlib para `IsEmpty`, `IsClosed`, `Finset`, etc.

| Tipo | Ejemplo |
|------|---------|
| Sort/Type | `U` (universo ZFC), `ω` (omega) |
| Predicado Prop | `IsFunction`, `IsOrdinal`, `IsNat`, `IsGCD` |

---

### (NC-4) Funciones y definiciones a nivel de términos (`def` que retorna un valor)

`lowerCamelCase`.

| Tipo | Ejemplo |
|------|---------|
| Constructor | `succ`, `pair`, `union` |
| Accessor | `fst`, `snd` |
| Operación | `powerset`, `sUnion`, `sep` |
| Isomorfismo/puente | `toPeano`, `fromPeano` |

---

### (NC-5) Axiomas

Los axiomas ZFC se fijan como `axiom` (primitivas del sistema).
En los nombres de teoremas derivados, se les referencia con sufijos descriptivos:
`extension_axiom`, `pairing_axiom`, `infinity_axiom`, etc.

---

### (NC-6) Teoremas y lemas exportables

Siguen el patrón **sujeto\_predicado** de Mathlib4, todo `snake_case` con guiones bajos.

```text
[sujeto]_[predicado]
[sujeto]_[predicado]_[objeto]
[sujeto]_[predicado]_of_[hipótesis]
```

Sufijos estándar:

| Sufijo | Significado | Ejemplo |
|--------|-------------|---------|
| `_iff` | bicondicional | `mem_powerset_iff`, `mem_inter_iff` |
| `_eq` | igualdad | `union_self_eq`, `inter_empty_eq` |
| `_of_` | se sigue de | `subset_of_mem_powerset`, `eq_of_subset_of_subset` |
| `_comm` | conmutatividad | `union_comm`, `inter_comm` |
| `_assoc` | asociatividad | `union_assoc`, `inter_assoc` |
| `_cancel` | cancelación | `add_left_cancel` |
| `_inj` | inyectividad | `succ_inj`, `pair_inj` |

---

### (NC-7) Declaraciones privadas y auxiliares

Usar la palabra clave `private`. Opcionalmente añadir `_aux` para pasos intermedios.

```lean
private lemma mem_union_aux : … := …
private def witnessFor_aux : … := …
```

- El sufijo `_aux` es opcional pero recomendado cuando el lema es un paso intermedio dentro de una prueba.
- Nunca exportar nombres `_aux`.

---

### (NC-8) Notaciones

Documentar cada notación introducida en REFERENCE.md §5 con: símbolo, prioridad, ámbito, expansión.

Reglas:

- Preferir `local notation` dentro de namespaces para evitar contaminación global.
- Seguir las convenciones Unicode de Mathlib cuando existe un símbolo estándar (∈, ⊆, ∅, 𝒫, ⟨⟩).
- Los símbolos personalizados deben declararse `local` salvo que sean la notación primaria del proyecto y nunca colisionen con imports de Mathlib.
- Prioridad: seguir los valores por defecto de Lean 4 (50 para relaciones, 65 para operadores aritméticos).

---

### (NC-9) Nombres de secciones

`UpperCamelCase`, descriptivos.

```lean
section Induction
section UnionProperties
section Divisibility
```

---

### (NC-10) Tabla resumen

| Entidad | Convención | Ejemplo |
|---------|------------|---------|
| Módulo (archivo `.lean`) | `UpperCamelCase` | `CartesianProduct.lean` |
| Namespace | `UpperCamelCase` | `ZFC`, `ZFC.Nat`, `ZFC.BoolAlg.Basic` |
| Tipo / predicado Prop | `UpperCamelCase` | `IsFunction`, `IsOrdinal` |
| Función / def de valor | `lowerCamelCase` | `powerset`, `toPeano` |
| Teorema exportable | `sujeto_predicado` | `union_comm`, `mem_powerset_iff` |
| Privado / auxiliar | `private` + `_aux` opcional | `private lemma foo_aux` |
| Sección | `UpperCamelCase` | `section Divisibility` |
| Notación | `local notation` preferido | `local notation:50 …` |

---

## Cumplimiento de Convenciones (Compliance)

Verificar que los archivos `.lean` y la documentación cumplen con todos los puntos
(0–22) del sistema de lock/freeze, las reglas export/glob (§26-29), y las convenciones
de nombres (NC-1–NC-10) antes de considerar un módulo completamente documentado.

---

## Estructura de Directorios y Barrel Modules

### (24.) Organización de módulos por subdirectorio

A medida que el proyecto crece, los módulos se organizan en **subdirectorios temáticos** dentro de `ZFC/`.
Cada subdirectorio agrupa módulos relacionados y corresponde a un sub-namespace.

Estructura actual:

```
ZFC/
├── ZFC.lean              # Nivel 0: barrel raíz (solo imports)
├── Axiom/                # Axiomas ZFC
├── Core/                 # Prelim, fundamentos
├── SetOps/               # Operaciones de conjuntos
├── Nat/                  # Naturales Von Neumann
├── Int/                  # Enteros ZFC
├── Peano/                # Puente Peano ↔ Von Neumann
├── BoolAlg/              # Álgebra de Boole
├── Cardinal/             # Teoría de cardinales
└── Induction/            # Principios de recursión/inducción
```

Reglas:

- Nombres de subdirectorios: `UpperCamelCase`, reflejando el sub-namespace.
- Cada subdirectorio puede tener un `Basic.lean` para las definiciones fundamentales del área.
- `new-module.bash` admite rutas: `bash new-module.bash Nat/GcdExt` crea `ZFC/Nat/GcdExt.lean`.
- `gen-root.bash` escanea subdirectorios automáticamente.
- El namespace refleja la ruta: `ZFC/Nat/Basic.lean` → `namespace ZFC.Nat.Basic`.

### (25.) Barrel modules (obligatorios para subdirectorios)

Todo subdirectorio con 2 o más módulos `.lean` **DEBE** tener un barrel file.
El barrel file:

- Está al mismo nivel que el directorio, llamado `DirName.lean` (ej. `Nat.lean` para `Nat/`).
- Importa TODOS los submódulos de producción del directorio (excluye `test_*.lean`).
- **No contiene** definiciones, teoremas ni pruebas — solo `import` y un comentario de cabecera.
- Sirve como **punto de import único** para el subdirectorio.

```lean
-- ZFC/Nat.lean (barrel file)
import ZFC.Nat.Basic
import ZFC.Nat.Add
import ZFC.Nat.Mul
-- ... todos los módulos de producción en Nat/
```

El barrel raíz (`ZFC.lean`) **prefiere imports de barrel** sobre módulos individuales cuando existe barrel:

```lean
-- ZFC.lean (barrel raíz)
import ZFC.Axiom      -- barrel de Axiom/
import ZFC.Nat        -- barrel de Nat/
-- ...
```

---

## Arquitectura Export/Glob

### (26.) Bloques export en módulos hoja

Todo módulo de producción (no barrels, no test files) **DEBE** terminar con un bloque `export`
que liste todas las definiciones, teoremas, lemas e instancias públicas (no-privados) del namespace del módulo.
Esto hace las declaraciones disponibles a importadores sin necesitar `open Namespace`.

**Patrón:**

```lean
namespace ZFC.Nat.Basic

def myDef : Type := ...

theorem myTheorem : ... := ...

end ZFC.Nat.Basic

-- Export: todas las declaraciones públicas de este módulo
export ZFC.Nat.Basic (myDef myTheorem)
```

**Reglas:**

1. El `export` va DESPUÉS de `end namespace`, en el nivel raíz del archivo.
2. Listar TODAS las `def`, `theorem`, `lemma`, `instance` no-privadas.
3. NO exportar declaraciones `private`, helpers `_aux`, ni lemas intermedios con prefijo `private`.
4. Mantener la lista de exports **ordenada alfabéticamente** dentro de cada namespace.
5. Si un módulo contribuye a múltiples namespaces, usar un `export` por namespace.
6. `notation`, `macro`, `syntax` NO se listan en `export` — se propagan automáticamente con `import`.

### (27.) Mantenimiento del bloque export

- **Añadir** una declaración pública requiere añadirla al bloque `export`.
- **Renombrar** una declaración requiere actualizar el bloque `export`.
- **Eliminar** una declaración pública requiere quitarla del bloque `export`.
- Al **proyectar** un módulo a REFERENCE.md (§14), verificar que la lista export coincide.
- La lista export es la **lista canónica de la API pública** del módulo.

### (28.) Barrel files y exports

Los barrel files (`DirName.lean`) **no añaden** sus propios bloques `export` — los módulos hoja manejan sus propios exports. La única función del barrel file es la agregación via `import`.

Un barrel file **puede** incluir un comentario-catálogo de la API pública:

```lean
-- ZFC/Nat.lean
-- API pública: add_comm, mul_assoc, sub_le, ...
import ZFC.Nat.Basic
import ZFC.Nat.Add
-- ...
```

### (29.) Cumplimiento con plantilla

El archivo `_template.lean` debe reflejar el patrón export. La sección de Exports en la plantilla muestra el bloque `export` tras `end namespace`. Los módulos nuevos creados por `new-module.bash` heredan esta estructura.

---

## Sistema de Anotaciones para REFERENCE.md

### (30.) Anotaciones a nivel de módulo

Cada entrada de módulo en REFERENCE.md §3 puede incluir los siguientes metadatos:

```markdown
**@axiom_system**: `ZFC` | `Peano` | `none`
**@importance**: `foundational` | `high` | `medium` | `low`
```

- `@axiom_system`: A qué sistema formal pertenece principalmente el módulo.
- `@importance`: Cuán crítico es el módulo para la cadena de dependencias del proyecto.

### (31.) Anotaciones a nivel de teorema

Los teoremas o definiciones individuales en REFERENCE.md pueden anotarse:

```markdown
**@importance**: `high` | `medium` | `low`
```

- `high`: Usado por 3+ módulos, o es un axioma/definición clave.
- `medium`: Usado por 1-2 módulos.
- `low`: Utilidad interna, solo usado dentro de su propio módulo.

Propósito: Ayuda a los asistentes de IA a priorizar qué teoremas cargar para contexto.

---

## Archivos de Referencia Cruzada

### (32.) NAMING-CONVENTIONS.md

Archivo independiente con el diccionario completo de nombres, las 12 reglas de formación,
tablas de migración, y ejemplos detallados. Referencia canónica para renombramientos.
Se actualiza cada vez que las convenciones de nombres evolucionan.

### (33.) NEXT-STEPS.md

Documento vivo que rastrea las fases de desarrollo planificadas. Cada fase incluye:

- Nombre y objetivo
- Lista de módulos a crear/modificar
- Dependencias de fases anteriores
- Complejidad estimada (simple/media/compleja)

### (34.) THOUGHTS.md

Diario de diseño informal para registrar ideas, alternativas consideradas,
preguntas abiertas y direcciones futuras. No normativo — puramente exploratorio.
Útil para contexto de IA sobre el "por qué" de las decisiones tomadas.

---

## Cumplimiento de Requisitos

Verificar que REFERENCE.md, archivos .lean y otros archivos de documentación cumplan con todos los puntos (0-34), convenciones de nombres (§23), reglas export/glob (§26-29), y protocolos de lock/freeze (§20, §20b) antes de considerar la documentación completa y actualizada.
