# THOUGHTS — ZfcSetTheory

Notas de diseño, reflexiones y hoja de ruta del proyecto.

---

## 📌 Estado de las reflexiones (actualizado 2026-05-26)

- **[1.] / [2.] — RESUELTO**: toda la aritmética de límites en ℚ está implementada y proyectada
  (`convergesToQ_neg/sub/const_mul/mul/inv/div/abs/of_eventually_eq`, `squeeze_theorem`,
  `convergesToQ_of_dominated`, `IsSubseqOf`, `strictly_increasing_ge`, `subseq_convergent`,
  `CauchyEquivQ` refl/symm/trans). Lo hecho/no-hecho está marcado en `NEXT-STEPS.md` (Phase 6.5 ✅).
  Quedan pendientes (no bloqueantes, para Phase 10): `cauchyQ_of_convergent_subseq` y `convergesToQ_tail`.
- **[3.]–[8.] — VIGENTE**: el diseño de Computables/Constructibles (Phase 9) sigue abierto y es
  la referencia para esa fase. Antes está la **Phase 8 (polinomios)**, cuyo prerequisito
  `Rat/Pow.lean` (`powRatQ x n`) ya está completo (0 sorry, 16 exports).

---

## 🧠 REFLEXIONES 22:17/27-04-2026

[1.] ACLÁRAME: Ejemplo de teoremas que no sé si están implementados: 'convergesToQ_neg f L', 'convergesToQ_sub f g L₁ L₂', 'convergesToQ_const_mul c f L', 'convergesToQ_mul f g L₁ L₂', 'convergesToQ_inv f L', 'convergesToQ_div f g L₁ L₂', 'convergesToQ_abs f L', 'convergesToQ_abs f L', 'convergesToQ_of_eventually_eq f g L', 'squeeze_theorem a f b L', convergesToQ_of_dominated f g L, IsSubseqOf g f, strictly_increasing_ge φ n, subseq_convergent f g L, cualquier subsucesión de cauchy es de cauchy, y establecemos que dos sucesiones de Cauchy, f, g, son equivalentes f ~ g \<=> f-g converge a 0

[2.] MARCA CLARAMENTE EN NEXT-STEPS.md lo hecho y lo no hecho

[3.] SOBRE LA DEFINICIÓN DE NÚMEROS COMPUTABLES: Sea $f : \Nat_0 → \Rat$ una sucesión de racionales, y $∃ N_0 ∈ \Nat_0$ tal que $∀ N > N_0$, $∀ n, m > N, |f(n)-f(m)| < \frac 1 {2^N}$. Entonces $\< f, hexN_0: ∃ N_0 ∈ \Nat_0, ∀ N > N_0, ∀ n, m > N, |f(n)-f(m)| < \frac 1 {2^N} \>$ es un número computable. Es decir, un número computable es una sucesión de racionales de Cauchy con una tasa de convergencia dada por $N$. Este par de función de \Nat₀ a \Rat y la prueba de que existe un $N_0$ natural que cumple la condición de Cauchy con esa tasa de convergencia, no define un número computable, sino solo una representación.

[4.] CUANDO DOS REPRESENTACIONES DE NÚMEROS COMPUTABLES SON IGUALES: Dadas dos sucesiones de Cauchy $\left< f, ∃ N_0 \right>$ y $\left< g, ∃ M_0 \right>$, serán iguales, cuando la sucesión (número computable) $\left< |f-g| , max(N*M, N+M) \right>$, no solo es de Cauchy, sino que converge a 0. Es decir, si la diferencia entre las dos sucesiones converge a 0 con una tasa de convergencia dada por $max(N*M, N+M)$. De esta forma, establecemos una relación de equivalencia entre las sucesiones de Cauchy computables. Esto será una relación de equivalencia, ya que es reflexiva (la diferencia entre una sucesión y sí misma es 0), simétrica (si la diferencia entre f y g converge a 0, entonces la diferencia entre g y f también converge a 0) y transitiva (si la diferencia entre f y g converge a 0, y la diferencia entre g y h converge a 0, entonces la diferencia entre f y h también converge a 0). De esta forma, si llamamos a esa relación de equivalencia ~, entonces el número computable será $[\left< f, ∃ N_0 \right>] = [\left< g, ∃ M_0 \right>] ∈ {\RatSet / ~}$.

[5.] CUANDO UN NÚMERO COMPUTABLE ES MENOR QUE OTRO: Dadas dos sucesiones de Cauchy $[\left< f, ∃ N_0 \right>]$ y $[\left< g, ∃ M_0 \right>]$, diremos que $[\left< f, ∃ N_0 \right>] < [\left< g, ∃ M_0 \right>]$ si la sucesión (número computable) $[\left< g-f , max(N*M, N+M) \right>]$ es de Cauchy y siempre positivo, y no converge a 0. Es decir, si la diferencia entre las dos sucesiones converge a un número positivo con una tasa de convergencia dada por $max(N*M, N+M)$. De esta forma, establecemos una relación de orden entre las clases de equivalencia de sucesiones de Cauchy computables. Hay que demostrar que esta relación no solo es de orden sino que está bien definida.

[6.] DADOS DOS NÚMEROS COMPUTABLES, CUALES SON EL PRODUCTO Y LA SUMA DE AMBOS: Dadas dos sucesiones de Cauchy $[\left< f, ∃ N_0 \right>]$ y $[\left< g, ∃ M_0 \right>]$, el producto de ambos será la sucesión de Cauchy $[\left< f*g, max(N*M, N+M) \right>]$, y la suma de ambos será la sucesión de Cauchy $[\left< f+g, max(N*M, N+M) \right>]$. De esta forma, establecemos las operaciones de suma y producto entre las clases de equivalencia de sucesiones de Cauchy computables. Hay que demostrar que estas operaciones están bien definidas.

[7.] NÚMEROS CONSTRUCTIBLES: Son aquellos números que se pueden construir a partir de los racionales usando un número finito de operaciones de suma, resta, multiplicación, división y extracción de raíces cuadradas. Estos números forman un subcuerpo de los números reales, y son exactamente los números que se pueden construir con regla y compás en geometría clásica. Sin embargo, este cuerpo no es completo, ya que hay sucesiones de Cauchy de números constructibles que no convergen a ningún número constructible (por ejemplo, la sucesión definida por el método de Newton para aproximar $\sqrt{2}$).

[8.] DEFINICIÓN DE NÚMEROS CONSTRUCTIBLES EN LEAN 4 EN NUESTRO PROYECTO: Para COPILOT: ayúdame a ver como podríamos definirlo en Lean 4. ¿Cual sería la definición de tipo inductivo? Supongamos que decimos que los números constructibles son o bien un número racional, o bien la raíz cuadrada de un número constructible, o bien la suma, resta, multiplicación o división de dos números constructibles. Entonces podríamos definir el tipo inductivo Constructible como sigue:

```lean
inductive Constructible
| rat (q : Rat)                             : Constructible
| sqrt (c : Constructible) (h : c ≥ 0)      : Constructible
| add (c1 c2 : Constructible)               : Constructible
| sub (c1 c2 : Constructible)               : Constructible
| mul (c1 c2 : Constructible)               : Constructible
| div (c1 c2 : Constructible) (h : c2 ≠ 0)  : Constructible
```

Para esta definición debemos tener la definición de `sqrt` o bien como una definición no expresamente computable, por sus propiedades: `sqrt c` es un número constructible positivo tal que `sqrt c * sqrt c = c`. Para esto, podríamos definir `sqrt c` como el límite de la sucesión de Cauchy dada por el método de Newton para aproximar la raíz cuadrada de `c`, es decir, la sucesión `f(n)` definida por:

$$
f(0) = {\frac 2 3}​ \newline
f(n+1)= {\frac 1 2} ⋅ ​(f(n) + {\frac c {f(n)}}) \text{ para } n≥0
$$

que en código lean sería algo como:

```lean

-- Deberíamos buscar un forma de dado un c, tener una aproximación inicial r, tal que r^2 > c, 
-- para así garantizar que la sucesión de Newton es monótonamente decreciente y acotada inferiormente 
-- por sqrt c, lo que nos permitiría demostrar que converge a sqrt c.

-- Como primera aproximación podríamos coger un racional tal que r_1 < r_0/2 < r_1 + 1, por ejemplo, 
-- r_1 := {{r_0}-2}/2, tomando r_0 como la r anterior.
def initial_aproximation (c : Constructible) (h : c ≥ 0) : Rat := 
    let r2 : Rat := |intToRat E[c]| + rat 1 -- r2 es un entero aquí, por lo que es un racional, 
                         -- y es mayor que sqrt c, porque sqrt c ≤ |c| + 1
    let r : Rat := (r2 / (rat 2)) + (rat 1)
    let r_1 : Rat := div (sub r (rat 2)) (rat 2)
    if mul r_1 r_1 > c then 
        r_1 
    else 
        r_1 + (rat 1) -- FALTARÍA UNA RECURSIÓN HAS TA QUE FUESE MAYOR QUE c

def NewtonRaphsonSqrt 
    (n : ℕ₀) (c : Constructible) (hneq0 : c ≠ 0) : 
        ℕ₀ → Constructible 
            := 
    if n = 0 then 
        initial_aproximation c hneq0 
    else 
        (add 
            (mul (rat (1/2)) (NewtonRaphsonSqrt (n-1) c hneq0)) 
            (mul (rat (1/2)) (div c (NewtonRaphsonSqrt (n-1) c hneq0)))
        )

def sqrt (c : Constructible) (h : c ≥ 0) : Constructible
    -- Aquí deberíamos demostrar que f es una sucesión de Cauchy y 
    -- que su límite es la raíz cuadrada de c
    -- Luego podríamos definir sqrt c como el límite de f (con un `existe ese límite`, 
    -- con la precisión necesaria que se pida) )
    -- Debería devolver esta función sqrt como una aproximación de Newton-Raphson, 
    -- y la prueba de que es de Cauchy y con una
    -- tasa de convergencia que para n, m > N, |f(n)-f(m)| < 1/2^N, el límite es esa pareja 
```

[9.] SOBRE LOS NÚMEROS RADICALES: La diferencia fundamental con los números constructibles es que los números radicales perminten no solo raíces cuadradas, sino también raíces n-ésimas:

```lean
inductive Radical
| rat (q : Rat)                                    : Radical
| root (n : ℕ₀) (c : Radical) (h : c ≥ 0)          : Radical
| add (c1 c2 : Radical)                            : Radical
| sub (c1 c2 : Radical)                            : Radical
| mul (c1 c2 : Radical)                            : Radical
| div (c1 c2 : Radical) (h : c2 ≠ 0)               : Radical
```

Dado que la raíz n-ésima cumple que ${\sqrt[n]{c}}^n = c$, que si c debe ser positivo, entonces podemos encontrar un la ecuación dada por el método de Newton-Raphson para aproximar la raíz n-ésima de c, que es la sucesión dada por:
$$
f(0) = {\frac 2 3}​ \newline
f(n+1)= {\frac 1 n} ⋅ ​((n-1)f(n) + {\frac c {f(n)^{n-1}}}) \text{ para } n≥0
$$

$$
x^n = c \iff x = c / x^(n-1) \iff f(n+1) = (1/n) * ((n-1)f(n) + \frac c {f(n)^{(n-1)}})
$$

Así obtenemos la situación de la sucesión aproximación:

$$
x_0 = \text{InitialApproximation } (c, h) \newline
x_{n+1} = (\frac 1 n) * ((n-1) * x_n + \frac c {x_{n}^{(n-1)}})
$$

Todo lo demás se parece mucho a la situación de los números constructibles.

[10.] SOBRE LOS NÚMEROS CONSTRUCTIBLES Y RADICALES: Ambos cuerpos no son completos, ya que hay sucesiones de Cauchy de números constructibles o radicales que no convergen a ningún número constructible o radical. Por ejemplo, la sucesión dada por el método de Newton para aproximar $\sqrt{2}$ es una sucesión de Cauchy de números racionales (que son constructibles), pero su límite $\sqrt{2}$ no es un número racional, por lo que no es un número constructible. Sin embargo, $\sqrt{2}$ sí es un número radical, ya que se puede expresar como la raíz cuadrada de 2, que es un número constructible. Habrá que demostrar que ambos cuerpos no son completos. Esto también habrá de hacerse con los números computables.

[11.] SOBRE LOS NÚMEROS ALGEBRÁICOS: Este cuerpo requerirá la introducción de polinomios, toda una infraestructura de álgebra abstracta, y la demostración de que los números algebraicos forman un cuerpo. Además, habrá que demostrar que este cuerpo no es completo, ya que hay sucesiones de Cauchy de números algebraicos que no convergen a ningún número algebraico (por ejemplo, la sucesión dada por el método de Newton para aproximar $1 + \frac 1 {2!} + \frac 1 {3!} + \frac 1 {4!} + ... + \frac 1 {n!} + ...$ es una sucesión de Cauchy de números racionales, pero su límite $exp(1)$ no es un número algebraico (y habría que demostrarlo), por lo que no es un número algebraico). Para dar una definición computable de números algebraicos, el algoritmo es fuertemente más complejo, ya que no solo hay que dar una sucesión de racionales de Cauchy, sino también un algoritmo para encontrar el polinomio mínimo de ese número algebraico, y un algoritmo para encontrar las raíces de ese polinomio mínimo. De hecho no sé si valdrá con soluciones de polinomios en una indeterminada, o si tendremos que dar  soluciones de sistemas de polinomios en varias indeterminadas: es una duda que tengo.

[12.] DESARROLLO DE N-TUPLAS EN ZFC: Para desarrollar la teoría de números algebráicos me hacen falta los polinomios, y para ello me hará falta desarrollar la teoría de n-tuplas en ZFC. Como tengo definidos los naturales, los enteros y los racionales, y también tenemos definidos los pares ordenados de Kuratowski y los naturales de Von Neumann, podemos definir las n-tuplas como funciones finitas indexadas por los naturales.

**Idea básica.** En ZFC una "n-tupla" sobre un conjunto $\Omega$ con coordenadas $a_0, a_1, \dots, a_{n-1}$ se identifica con su gráfica como función $\{0,1,\dots,n-1\} \to \Omega$. Como $\sigma n = \{0, 1, \dots, n-1, n\} \setminus \{n\}$ no nos sirve directamente, conviene fijar el dominio $n$ (el natural de Von Neumann, que coincide con $\{0,1,\dots,n-1\}$) o bien $\sigma n$ si queremos $n+1$ coordenadas indexadas $0, \dots, n$. Eligiremos esta segunda variante por simetría con la notación $\langle a_0, \dots, a_n\rangle$ ("tupla de grado $n$" para polinomios de grado $n$).

**Infraestructura ya disponible en el proyecto.**

- Axioma de separación: `sep S P` (`ZFC/Axiom/Specification.lean`).
- Pares ordenados Kuratowski: `⟨a, b⟩`, `fst`, `snd`, `OrderedPair_eq_iff` (`ZFC/SetOps/OrderedPair.lean`).
- Producto cartesiano: `A ×ₛ B`, `OrderedPair_mem_CartesianProduct` (`ZFC/SetOps/CartesianProduct.lean`).
- Funciones como conjuntos: `IsFunction f A B := f ⊆ A ×ₛ B ∧ ∀ x ∈ A, ∃! y, ⟨x,y⟩ ∈ f`.
- Aplicación: `f⦅x⦆`, `apply_mem`, `apply_eq` (`ZFC/SetOps/Functions.lean`).
- Naturales de Von Neumann: `ω`, `σ n`, `mem_succ_iff` (`ZFC/Nat/Basic.lean`, `ZFC/Axiom/Infinity.lean`).
- Recursión sobre $\omega$: `RecursiveFn` (`ZFC/Induction/Recursion.lean`) — ya usada para sucesiones.
- Sucesiones $\omega \to \mathbb{Q}$: `IsSeqQ` (`ZFC/Rat/Sequences.lean`) — patrón a seguir.

**Definición propuesta — Tupla de longitud $n+1$ sobre $\Omega$.**

Dados $n \in \omega$, un conjunto $\Omega \in U$ y una función "fuente" $f$ con $\mathrm{dom}(f) \supseteq \sigma n$ y valores en $\Omega$ (formalmente, $f$ tal que $\sigma n \times_s \Omega$ contiene la gráfica restringida), definimos
$$
\mathrm{tuple}(n, f, \Omega) \;:=\; \mathrm{sep}\,(\sigma n \times_s \Omega)\,\bigl(\lambda p.\; \mathrm{snd}(p) = f\!\left(\mathrm{fst}(p)\right)\bigr).
$$
Es decir, es el subconjunto de $\sigma n \times_s \Omega$ formado por los pares $\langle k, f(k)\rangle$ con $k \in \sigma n$. Esta es exactamente la gráfica de $f \restriction \sigma n$ vista como conjunto, y patrón ya validado en el proyecto (cf. `addSeqQ`, `tailSeqQ` en `ZFC/Rat/Convergence.lean`, `ZFC/Rat/Sequences.lean`).

**Definición alternativa más algebraica — Tupla por enumeración explícita.** Cuando los coeficientes son fijos $a_0, \dots, a_n \in \Omega$ podemos construir la tupla sin necesidad de una función previa: por recursión sobre $n$,
$$
T_0(a_0) := \{\langle 0, a_0\rangle\}, \qquad
T_{n+1}(a_0,\dots,a_{n+1}) := T_n(a_0,\dots,a_n) \cup \{\langle \sigma n, a_{n+1}\rangle\}.
$$
Esta definición conviene para escribir polinomios literales y se conecta con la primera vía recursión.

**Predicado "ser una n-tupla".** En lugar de una definición posicional, podemos preferir el predicado
$$
\mathrm{IsTuple}(t, n, \Omega) \;:\Leftrightarrow\; \mathrm{IsFunction}(t,\,\sigma n,\,\Omega).
$$
Una n-tupla **es** una función con dominio $\sigma n$ y codominio $\Omega$. Esto reusa toda la maquinaria de funciones sin definiciones nuevas: el "elemento $i$-ésimo" es $t\!⦅i⦆$, la igualdad de tuplas se hereda de igualdad de funciones (extensionalidad), etc. **Recomiendo esta vía como definición primaria** y reservar `tuple n f Ω` como _constructor_ a partir de una función dada.

**Lemas mínimos a probar (esqueleto).**

1. `tuple_isFunction : IsFunction (tuple n f Ω) (σ n) Ω` — usando `mem_succ_iff` y `apply_eq` por el patrón de `addSeqQ_isSeqQ`.
2. `tuple_apply : ∀ k ∈ σ n, (tuple n f Ω)⦅k⦆ = f⦅k⦆` — patrón de `addSeqQ_apply`.
3. `tuple_ext : IsTuple t₁ n Ω → IsTuple t₂ n Ω → (∀ k ∈ σ n, t₁⦅k⦆ = t₂⦅k⦆) → t₁ = t₂` — extensionalidad de funciones.
4. `tuple_zero_eq_singleton_pair : tuple ∅ f Ω = {⟨∅, f⦅∅⦆⟩}` — caso base.
5. `tuple_succ_eq_union : tuple (σ n) f Ω = tuple n f Ω ∪ {⟨σ n, f⦅σ n⦆⟩}` — paso recursivo (puente entre las dos definiciones).

**Concatenación y operaciones derivadas (para polinomios).**

- `concat (s n) (t m) := s ∪ shift_by (σ n) t` donde `shift_by k t := { ⟨add k i, v⟩ : ⟨i, v⟩ ∈ t }` — concatena una tupla de longitud $n+1$ con una de longitud $m+1$ para dar una de longitud $n+m+2$. Necesita `add` en $\omega$ (ya lo tenemos: `ZFC/Nat/Add.lean`).
- `head : tuple → Ω`, `tail : tuple → tuple` — útiles para polinomios mediante el isomorfismo recursivo $\Omega^{n+1} \cong \Omega \times \Omega^n$.
- `update t i v := (t \setminus \{⟨i, t⦅i⦆⟩\}) ∪ \{⟨i, v⟩\}` — modificar una coordenada.

**Ubicación sugerida en el árbol de módulos.**

- `ZFC/SetOps/Tuple.lean` (nuevo): definiciones `tuple`, `IsTuple`, lemas básicos 1–5.
- `ZFC/SetOps/TupleOps.lean` (nuevo): `concat`, `head`, `tail`, `update`, `shift_by`, isomorfismos.
- Importar desde `ZFC/SetOps.lean` y desde donde se necesite (futuro `ZFC/Algebra/Polynomial.lean`).

**Notación informal sugerida (sintaxis Lean).**

- `⟨a₀, a₁, …, aₙ⟩ₜ` (subíndice `ₜ` para distinguir del par ordenado de Kuratowski). Implementable como macro de Lean que despliega a `tuple n (constructed from list)` o directamente como union iterada de singletons.
- `t⦅i⦆` ya disponible para acceso por índice (porque las tuplas serán funciones).

**Cuidado con el dominio.** Dos convenios posibles, **fija uno y mantenlo en todo el proyecto**:

- (A) "Tupla de grado $n$" = tupla de longitud $n+1$, dominio $\sigma n = \{0,\dots,n\}$. Encaja con polinomios de grado $n$.
- (B) "Tupla de longitud $n$", dominio $n = \{0,\dots,n-1\}$. Encaja con la convención clásica $\Omega^n$.

Recomiendo **(A)** para polinomios (`tuple n f` ≡ polinomio de grado $\le n$ con coeficientes $f(0),\dots,f(n)$), y un alias `tupleOfLength k f := tuple (predecessor k) f` para casos en que se piense en longitud.

**Compatibilidad con `RecursiveFn`.** Como `RecursiveFn` ya construye funciones $\omega \to A$ a partir de un valor inicial y un paso, una n-tupla puede obtenerse "truncando" una sucesión: `tuple n (RecursiveFn …) Ω`. Esto unifica el tratamiento con sucesiones y simplifica las pruebas.

[13.] DESARROLLO DE POLINOMIOS: Para desarrollar la teoría de los números algebraicos, necesitaremos una teoría de polinomios. Esto incluirá la definición de polinomios, operaciones con polinomios (suma, producto, división), el concepto de raíz de un polinomio, el teorema del residuo, el teorema de factorización, y la definición de polinomio mínimo. Además, habrá que demostrar que el conjunto de números algebraicos es cerrado bajo las operaciones de suma, resta, multiplicación y división (excepto por cero), lo que implica que forman un cuerpo.

Podemos definir un polinomio en una indeterminada $X$ de grado $n$ como una tupla de $n+1$ números racionales $\left< a₀, a₁, ..., aₙ \right>$ que representa el polinomio $a₀ + a₁X + a₂X² + ... + aₙXⁿ$, o incluso más fácil como una tupla de enteros multiplicada por un un racional positivo tipo $1 / n$ dónde $n ∈ \mathbb{N}_1$. Las operaciones de suma y producto de polinomios se pueden definir de manera estándar utilizando las operaciones de los coeficientes racionales. La división de polinomios se puede definir utilizando el algoritmo de división de polinomios, que también se basa en las operaciones con los coeficientes racionales.

```lean
-- La idea de la definción es que se le pasa un natural n como grado del monomio, 
-- y se le pasa un entero (numerador) y un natural no nulo (denominador) como coeficiente 
-- del monomio. En caso de pasarle el coeficiente como un racional, se le pasaría el 
-- numerador como entero y el denominador como natural no nulo.
inductive Monomial  : Type where
  | mk_nat (n : ℕ₀) : Monomial -- grado 0, coeficiente n
  | mk_int (z : IntSet) : Monomial -- grado 0
  | mk_rat (q : Rat) : Monomial  -- grado 0
  | mk (n : ℕ₀) (z : IntSet) (d : ℕ₀) (hneq0 : d ≠ 0) : Monomial -- grado n, coeficiente z/d
  | mk_from_rat (n : ℕ₀) (s : Rat) : Monomial -- grado n, coeficiente s

-- Primero vamos a hacer las funciones extractoras de grado y coeficiente de un monomio.
-- Tendríamos que conseguir que el grado del monomio zero fuese -1
def grado : Monomial → ℕ₀
    | Monomial.mk_nat _ => 0
    | Monomial.mk_int _ => 0
    | Monomial.mk_rat _ => 0
    | Monomial.mk n _ _ _ => n
    | Monomial.mk_from_rat n _ => n

def coeficiente : Monomial → Rat
    | Monomial.mk_nat n => rat (int n)
    | Monomial.mk_int z => rat z
    | Monomial.mk_rat q => q
    | Monomial.mk _ z d _ => rat z (natToInteger d)
    | Monomial.mk_from_rat _ s => s

-- Habría que definir los monomios constantes cero, uno y menos uno.
def zeroMonomial : Monomial := Monomial.mk_nat 0
def oneMonomial : Monomial := Monomial.mk_nat 1
def negOneMonomial : Monomial := Monomial.mk_int (-1)

-- Ahora se definirían las sumas (de monomios del mismo grado) y 
-- el producto de monomios cualquiera, 
-- la potencia de un monomio a un número natural, 
-- la resta y 
-- la división de monomios (esta última solo si el divisor es el monomio no nulo).

def addMonomial (m1 : Monomial) (m2 : Monomial) (heq : grado m1 = grado m2) : Monomial := 
    let n := grado m1
    let c1 := coeficiente m1
    let c2 := coeficiente m2
    Monomial.mk_from_rat n (c1 + c2)

def subMonomial (m1 : Monomial) (m2 : Monomial) (heq : grado m1 = grado m2) : Monomial := 
    let n := grado m1
    let c1 := coeficiente m1
    let c2 := coeficiente m2
    Monomial.mk_from_rat n (c1 - c2)

def negMonomial (m : Monomial) : Monomial := 
    let n := grado m
    let c := coeficiente m
    Monomial.mk_from_rat n (-c)

def mulMonomial (m1 : Monomial) (m2 : Monomial) : Monomial := 
    let n1 := grado m1
    let n2 := grado m2
    let c1 := coeficiente m1
    let c2 := coeficiente m2
    Monomial.mk_from_rat (n1 + n2) (c1 * c2)

def powMonomial (m : Monomial) (k : ℕ₀) : Monomial := 
    let n := grado m
    let c := coeficiente m
    Monomial.mk_from_rat (n * k) (c ^ k)

def divMonomial (m1 : Monomial) (m2 : Monomial) (hneq0 : coeficiente m2 ≠ 0) : Monomial := 
    let n1 := grado m1
    let n2 := grado m2
    let c1 := coeficiente m1
    let c2 := coeficiente m2
    Monomial.mk_from_rat (n1 - n2) (c1 / c2)

--
inductive Polynomial : Type where
  | mk_nat (n : ℕ₀) : Polynomial -- polinomio de grado 0 y coeficiente n
  | mk_int (z : IntSet) : Polynomial -- polinomio de grado 0 y coeficiente z
  | mk_rat (q : Rat) : Polynomial  -- polinomio de grado 0 y coeficiente q 
  | mk_from_monomial (mon : Monomial) : Polynomial -- un monomio es un polinomio
  | mk (tupla : Tuple (n+1) IntSet) (k : ℕ₁) : Polynomial
  | mk_from_rats (tupla : Tuple (n+1) Rat) : Polynomial
  | mk_from_list_of_monomials (list : List Monomial) : Polynomial 

def mainCoefficient (P : Polynomial) : Rat := 
    match P with
    | Polynomial.mk_nat n => rat (int n)
    | Polynomial.mk_int z => rat z
    | Polynomial.mk_rat q => q
    | Polynomial.mk_from_monomial mon => coeficiente mon
    | Polynomial.mk Tuple tupla k => 
        -- aquí habría que definir cómo extraer el coeficiente principal de un 
        -- polinomio dado por una tupla de enteros
        -- Dada una tupla de n+2 enteros, el coeficiente principal sería el n-ésimo 
        -- elemento de la tupla dividido por natToIntSet k 
        -- que es el denominador común de los coeficientes del polinomio.
        -- En el caso que el n-ésimo elemento de la tupla fuese cero, el coeficiente principal
        -- pasaría a considerarse el n-1-ésimo elemento de la tupla dividido por el valor
        -- k, y así sucesivamente hasta encontrar el
        -- primer elemento de la tupla que no sea cero, o llegar al elemento 0 de la tupla, 
        -- en cuyo caso el coeficiente principal sería cero. 
        
    | Polynomial.mk_from_rats Tuple _ => -- aquí habría que definir cómo extraer el coeficiente principal de un polinomio dado por una tupla de racionales
        sorry
    | Polynomial.mk_from_list_of_monomials list => -- aquí habría que definir cómo extraer el coeficiente principal de un polinomio dado por una lista de monomios, que sería el coeficiente del monomio de mayor grado
        sorry
```

[14.] No tenemos una prueba que los primos son infinitos(dando un primo posterior a cualquiera primo dado). Si p es primo, entonces p! + 1 es primo. Si q := p! + 1 no es primo, cualquier número r entre 1 (no igual a 1) y q (sin incluir q), r no divide a q. Si (div q r)*r + (mod q r) = q = p! + 1, entonces si r | q, entonces (div q r)*r = q, lo que implica que (mod q r) = 0, lo que es una contradicción (sabemos que todos los factores de p! son menores o iguales a p, y esos factores no dividen a p! + 1). Por tanto, ningún número entre 1 y q divide a q, lo que implica que q es primo. Por tanto, dado un primo p, podemos encontrar un primo posterior a p, que es p! + 1. Hay afinar la prueba.

[15.] Tenemos que completar el Teorema de Wilson (vendrá de Peano)

[16.] ✅ HECHO — `cauchyQ_of_convergent_subseq f g L` demostrado: si $f$ es de Cauchy, $g$ es subsucesión de $f$ y $g \to L$, entonces $f \to L$ (argumento $\varepsilon/2$).

[17.] **Irracionalidad generalizada.** Hemos demostrado que $\sqrt{2} \notin \mathbb{Q}$ en `SqrtApprox.lean` (`sqrt2_irrational`). Naturalmente queremos generalizar:

- **Primo $p$**: $\sqrt{p} \notin \mathbb{Q}$ para todo primo $p$. El argumento es idéntico: si $a^2 = p \cdot b^2$ con $\gcd(a,b)=1$, entonces $p \mid a$, luego $a = p \cdot c$ y $p^2 c^2 = p b^2$, así $p \mid b^2$ y $p \mid b$, contradicción con $\gcd(a,b)=1$. Necesita `IsPrime` de `Nat/Primes.lean` y divisibilidad de `Int/Div.lean`.

- **Entero $n$ que no es cuadrado perfecto**: $\sqrt{n} \notin \mathbb{Q}$ cuando $n$ no es cuadrado perfecto. Estrategia: factorizar $n$ en primos; algún primo $p$ aparece con exponente impar; una extensión del argumento de Cauchy implica que $\sqrt{n} \notin \mathbb{Q}$. Necesita factorización prima completa (`Nat/Primes.lean`, TFA).

- **Meta**: `prime_sqrt_irrational (p : U) (hp : IsPrime p) : ¬∃ a b : IntSet, b ≠ zeroZ ∧ mulZ a a = mulZ (natToInt p) (mulZ b b)` y `nonsquare_sqrt_irrational (n : U) (hn : ¬IsSquare n) : ...`.

---

## ✅ COMPLETADO

### Phase 1–3: Estructura y nomenclatura (2025–2026)

- Reorganización en subdirectorios: `Core/`, `Axiom/`, `SetOps/`, `Nat/`, `Peano/`, `Induction/`, `BoolAlg/`, `Cardinal/`
- Namespaces `ZFC.*` alineados con la estructura de directorios
- 185 identificadores renombrados según convención Mathlib
- Sistema de anotaciones `@importance` y `@axiom_system` en REFERENCE.md

### Phase 4: Sistema de anotaciones (abril 2026)

- `@importance` (high/medium/low) en 280+ teoremas
- `@axiom_system` en 47+ módulos (clasifica dependencias de axiomas ZFC transitivamente)
- Distinción entre resultados de lógica pura y los que usan Infinito/Potencia/Elección

### Phase 5: Enteros ℤ (abril 2026)

**75 jobs de build, 0 sorry, 0 errores. 15 módulos, 190 exports.**

| Módulo | Estado |
|--------|--------|
| `Int/Equiv.lean` | ✅ Relación de equivalencia en ω × ω, IntEquivRel |
| `Int/Basic.lean` | ✅ IntSet, intClass, zeroZ, oneZ, tricotomía |
| `Int/Add.lean` | ✅ addZ, identidades, conmutatividad, asociatividad |
| `Int/Neg.lean` | ✅ negZ, subZ, inversos aditivos, involución |
| `Int/Mul.lean` | ✅ mulZ, conmutatividad, asociatividad, identidades |
| `Int/Ring.lean` | ✅ Distributividad, dominio de integridad, cancelación, difference_of_squares |
| `Int/Sub.lean` | ✅ subZ como operación derivada, propiedades |
| `Int/Order.lean` | ✅ leZ, ltZ, orden total, compatibilidad +/×, square_nonneg |
| `Int/DivMod.lean` | ✅ dividesZ, divisibilidad, propiedades |
| `Int/Embedding.lean` | ✅ natToInt, inyección ω → ℤ, preserva +/×/≤ |
| `Int/Abs.lean` | ✅ absZ, signZ, desigualdad triangular, absZ_mulZ_nonneg |
| `Int/Div.lean` | ✅ gcdZ, modZ, quotZ, lcmZ, bezoutZ, tfa_Z (TFA en ℤ) |
| `Int/Pow.lean` | ✅ powZ, potenciación, powZ_powZ, powZ_negZ_odd |
| `Int/Induction.lean` | ✅ int_induction_abs, int_strong_induction_abs, int_descent |
| `Int/Units.lean` | ✅ isUnitZ, unitZ_iff (unidades = {±1}) |

### BoolAlg completo (fases anteriores)

- `BoolAlg.Basic`, `Ring`, `PowerSetAlgebra`, `GenDeMorgan`, `GenDistributive`
- `BoolAlg.Atomic`, `Complete`, `FiniteCofinite`, `Representation`, `FiniteBA`, `BoolRingBA`
- Resultados clave: 𝒫(A) es AB completa atómica; toda BA completa atómica ≅ 𝒫(A); FinCofAlg(ω) no es completa; toda BA finita tiene cardinalidad 2^n; correspondencia BR ↔ BA

#### NUEVOS PENSAMIENTOS SOBRE BOOLALG: 21:37/23-04-2026

Deberíamos añadir la compleción del teorema de representación de Stone. Hay que hacer una plan para la representación inversa de Stone, que es el isomorfismo inverso entre una BA completa atómica A y 𝒫(Atoms(A)). Para esto, hay que definir la función atomsBelowMap: A → 𝒫(Atoms(A)) que a cada elemento a ∈ A le asigna el conjunto de átomos que están por debajo de a. Luego hay que demostrar que esta función es un isomorfismo de BA, es decir, que preserva las operaciones de unión, intersección, complemento, así como los elementos neutros ∅ y universo. Esto completaría la caracterización de las BA completas atómicas como álgebras de conjuntos.

Además tengo un álgebra de Boole de cardinalidad infinita contable, que no es atómica:

Álgebras de Boole Numerables y sin Átomos

Un álgebra de Boole se dice que es sin átomos (o no atómica) si para cualquier elemento no nulo $x$, existe otro elemento no nulo $y$ estrictamente menor que $x$ (es decir, $y \le x$ y $y \neq x$). En términos de conjuntos, esto significa que ningún conjunto no vacío es "indivisible": siempre puedes encontrar un subconjunto propio no vacío.A continuación, se presentan dos construcciones puramente conjuntistas (álgebras de conjuntos, donde las operaciones son la unión $\cup$, intersección $\cap$ y complemento $\setminus$ clásicos) que dan lugar a un álgebra de Boole numerable y sin átomos.

Construcción 1: El álgebra de intervalos de los racionales

Esta es la forma más clásica e intuitiva de construirla.

El conjunto base: Tomamos como conjunto base a los números racionales en el intervalo semiabierto: $X = \mathbb{Q} \cap [0, 1)$.

Los elementos del álgebra: Consideramos la familia de conjuntos $\mathcal{B}$ formada por todas las uniones finitas de intervalos semiabiertos de la forma $[a, b)$, donde $a, b \in \mathbb{Q}$ y $0 \le a < b \le 1$. También incluimos el conjunto vacío $\emptyset$.

Es un álgebra de Boole: $\mathcal{B}$ es cerrada bajo intersecciones finitas y bajo uniones finitas. Además, es cerrada bajo el complemento relativo a $X$.

Por ejemplo, el complemento de $[a, b)$ es $[0, a) \cup [b, 1)$, que sigue siendo una unión finita de intervalos semiabiertos.

Cardinalidad contable (Numerable): Dado que los extremos $a$ y $b$ de los intervalos se eligen de $\mathbb{Q}$ (que es numerable), existen numerables intervalos de esta forma. Como los elementos del álgebra son solo las uniones finitas de estos intervalos, el cardinal del álgebra $\mathcal{B}$ sigue siendo $\aleph_0$ (numerable).

Sin átomos: Sea $A \in \mathcal{B}$ un conjunto no vacío. Por definición, $A$ debe contener al menos un intervalo de la forma $[a, b)$ con $a < b$. Como los números racionales son densos, siempre existe un número racional $c$ tal que $a < c < b$. El intervalo $[a, c)$ es no vacío, pertenece al álgebra $\mathcal{B}$, y es un subconjunto propio estricto de $A$. Por tanto, no existen elementos indivisibles (átomos).

Construcción 2: El álgebra de conjuntos cilindro (Espacio de Cantor)

Esta construcción es fundamental en teoría de la medida y topología, y muestra una distinción interesante: el álgebra es numerable, aunque el conjunto base sobre el que opera es no numerable.

El conjunto base: Sea $X = \{0, 1\}^{\mathbb{N}}$, el conjunto de todas las sucesiones infinitas de ceros y unos. (Notar que el cardinal de $X$ es el del continuo, $2^{\aleph_0}$).

Los conjuntos cilindro (o abiertos básicos): Definimos un "cilindro" fijando un prefijo finito. Por ejemplo, el cilindro $C_{011}$ es el conjunto de todas las sucesiones infinitas que comienzan exactamente con la secuencia finita (0, 1, 1, ...).

Los elementos del álgebra: Definimos nuestra familia $\mathcal{C}$ como la colección de todas las uniones finitas de conjuntos cilindro, además del vacío $\emptyset$.

Es un álgebra de Boole: La intersección o unión de dos cilindros es otro cilindro (o una unión finita de ellos). El complemento de un cilindro también es una unión finita de cilindros. (Por ejemplo, el complemento de "sucesiones que empiezan por 0" son "las sucesiones que empiezan por 1"). Por lo tanto, $\mathcal{C}$ es un álgebra de conjuntos.

Cardinalidad contable: El número de posibles secuencias prefijo finitas de ceros y unos es numerable (es la suma de $2^n$ para $n \in \mathbb{N}$). Puesto que tomamos solo uniones finitas de estos cilindros, la cantidad total de conjuntos en nuestra álgebra $\mathcal{C}$ es $\aleph_0$ (numerable).

Sin átomos: Toma cualquier conjunto no vacío en $\mathcal{C}$. Este debe contener al menos algún cilindro definido por un prefijo de longitud $n$ (digamos, el prefijo $s$). Podemos "dividir" este cilindro en dos subcilindros disjuntos, especificando el siguiente dígito: el subcilindro de sucesiones que empiezan por $s \frown 0$ (el prefijo $s$ seguido de un 0) y el de sucesiones que empiezan por $s \frown 1$. Ambos pertenecen al álgebra y son estrictamente más pequeños. Ningún conjunto del álgebra es atómico.

Conclusión

Ambas construcciones proporcionan modelos puramente conjuntistas de un álgebra de Boole contable y sin átomos. De hecho, por el teorema de representación (y resultados clásicos de teoría de modelos sobre categorías $\aleph_0$-categóricas), el álgebra $\mathcal{B}$ (de los intervalos racionales) y el álgebra $\mathcal{C}$ (de los cilindros booleanos) son exactamente la misma estructura algebraica disfrazada de dos formas distintas: existe un isomorfismo de álgebras de Boole entre ellas.

### Cardinal (fases anteriores)

- `Cardinal.Basic`: Teorema de Cantor, Cantor-Schröder-Bernstein
- `Cardinal.FinitePowerSet`: |𝒫(F)| = 2^n para F finito

---

## ✅ COMPLETADO — Phase 6: Racionales ℚ (terminada 2026-05-01)

Módulos en `ZFC/Rat/`:

| # | Módulo | Contenido |
|---|--------|-----------|
| 1 | `Rat/Equiv.lean` | ✅ RatEquivRel en ℤ × ℤ*, reflexividad, simetría, transitividad |
| 2 | `Rat/Basic.lean` | ✅ RatSet := (ℤ × ℤ*) / ~, ratClass, zeroQ, oneQ, representante canónico |
| 3 | `Rat/Add.lean` | ✅ addQ con buena definición, clausura, conmutatividad, asociatividad |
| 4 | `Rat/Neg.lean` | ✅ negQ, subQ, inversos aditivos |
| 5 | `Rat/Mul.lean` | ✅ mulQ, conmutatividad, asociatividad, identidades, inverso multiplicativo |
| 6 | `Rat/Order.lean` | ✅ leQ, ltQ, orden total, compatibilidad con +/× |
| 7 | `Rat/Embedding.lean` | ✅ inyección ℤ → ℚ, preserva +/×/≤ |
| 8 | `Rat/Field.lean` | ✅ ℚ es cuerpo ordenado, propiedad Arquimediana, densidad |
| 9 | `Rat/Abs.lean` | ✅ absQ, signQ, desigualdad triangular |
| 10 | `Rat/MaxMin.lean` | ✅ maxQ, minQ, propiedades |
| 11 | `Rat/Sequences.lean` | ✅ IsSeqQ, constSeqQ, addSeqQ, mulSeqQ, negSeqQ, absSeqQ |
| 12 | `Rat/Convergence.lean` | ✅ convergesToQ, subsucesiones, aritmética de límites, invSeqQ, tailSeqQ, shiftSeqQ, strictly_increasing_ge |
| 13 | `Rat/CauchyQ.lean` | ✅ IsCauchyQ, CauchyEquivQ, cauchyQ_of_convergent_subseq |
| 14 | `Rat/Monotone.lean` | ✅ sucesiones monótonas acotadas |
| 15 | `Rat/SqrtApprox.lean` | ✅ sqrt2_irrational (0 sorry, 0 errores) |

Relación de equivalencia: $(a, b) \sim (c, d) \iff a \cdot d = b \cdot c$ en $\mathbb{Z} \times \mathbb{Z}^*$.

## ADDENDUM: 20:35/23-04-2026 Nuevas ideas sobre los racionales

Antes de pasar a los reales, vamos a construir sobre los racionales las sucesiones. Vamos a ver sucesiones en general como funciones f: ℕ₀ → ℚ. Construiremos las definiciones de convergencia, límites y sucesiones de Cauchy. Construiremos una sucesión que será de Cauchy pero no convergente, para así dar la explicación sobre la necesidad de los reales.

Las sucesiones serán convergentes si existe un límite L ∈ ℚ tal que para todo ε > 0 (racional), existe N ∈ ℕ₀ tal que para todo ∀ n ∈ ℕ₀, n ≥ N $\->$ |f(n) - L| < ε. Las sucesiones de Cauchy serán aquellas para las cuales para todo ε > 0, existe N tal que para todo m, n ≥ N, |f(m) - f(n)| < ε.

Distinguiremos entre convergencia absoluta y convergencia relativa o normal. La convergencia absoluta será aquella para la cual existe L ∈ ℚ tal que para todo ε > 0, existe N tal que para todo n ≥ N, |f(n)| < ε. La convergencia relativa o normal será aquella para la cual existe L ∈ ℚ tal que para todo ε > 0, existe N tal que para todo n ≥ N, |f(n) - L| < ε. También podemos distinguir entre convergencia de Cauchy absoluta y relativa.

Construiremos una sucesión de racionales, de Cauchy, f: ℕ₀ → ℚ, tal que la sucesión g:: ℕ₀ → ℚ : n → f(n)⋅f(n) es convergente al límite 2.

$$
f(0) = {\frac 2 3}​ \newline
f(n+1)= {\frac 1 2} ⋅ ​(f(n) + {\frac 2 {f(n)}}) \text{ para } n≥0
$$

Demostramos que efectivamente es lo que queríamos:

1. Es una sucesión de racionales ($f(n) \in \mathbb{Q}$)

El primer término $f(0) = 3/2$ es un número racional. Como el cuerpo de los números racionales es cerrado bajo la suma, la multiplicación y la división (siempre que el divisor no sea cero, y aquí $f(n)$ es siempre estrictamente positivo), por inducción, todos los términos $f(n)$ pertenecen a $\mathbb{Q}$.

1. $(f(n))^2$ se acerca a 2 de forma monótona

Para demostrar que el acercamiento de los cuadrados es estrictamente monótono (en este caso, decreciente hacia 2), primero calculemos la diferencia entre el cuadrado del término siguiente y 2:

$$f(n+1)^2 - 2 = \left( \frac{f(n)^2 + 2}{2f(n)} \right)^2 - 2 = \frac{f(n)^4 + 4f(n)^2 + 4 - 8f(n)^2}{4f(n)^2} = \frac{(f(n)^2 - 2)^2}{4f(n)^2}$$

Dado que el numerador es un cuadrado perfecto y el denominador es positivo, la fracción entera es estrictamente mayor que cero. Esto significa que para cualquier $n \ge 0$, siempre se cumple que $f(n+1)^2 > 2$. (El término inicial $f(0)^2 = 9/4 > 2$ también lo cumple).

Ahora evaluamos la diferencia entre dos términos consecutivos de la sucesión:

$$f(n+1) - f(n) = \frac{1}{2} \left( f(n) + \frac{2}{f(n)} \right) - f(n) = \frac{2 - f(n)^2}{2f(n)}$$

Como acabamos de demostrar que $f(n)^2 > 2$ para todo $n$, el numerador $2 - f(n)^2$ es negativo. Al ser el denominador positivo, la fracción completa es negativa. Por tanto:

$$f(n+1) < f(n)$$

Como todos los términos son positivos y la sucesión $f(n)$ es estrictamente decreciente, sus cuadrados también lo son. Por lo tanto, la sucesión $(f(n))^2$ se acerca a 2 de forma monótona decreciente.

1. Es una sucesión de Cauchy

Por definición, una sucesión de Cauchy es aquella en la que la distancia entre sus elementos se vuelve arbitrariamente pequeña a medida que avanza la sucesión.

En el ámbito de los números reales $\mathbb{R}$, toda sucesión convergente es de Cauchy. Dado que hemos demostrado que $f(n)$ es decreciente y está acotada inferiormente por $\sqrt{2}$, por el teorema de la convergencia monótona, la sucesión converge a $\sqrt{2}$. Al converger a un límite real finito, la sucesión de racionales $f(n)$ cumple intrínsecamente la condición de Cauchy:

Para todo $\epsilon > 0$, existe un número natural $N$ tal que para todo $n, m > N$, se cumple que $|f(n) - f(m)| < \epsilon$.

De hecho, debido a que se origina en el método de Newton, esta sucesión tiene convergencia cuadrática, lo que significa que el número de decimales correctos se duplica (aproximadamente) en cada paso, haciendo que los términos se "apelotonen" extremadamente rápido.

Vamos a hacer nuevas construcciones que cumplen que son cuerpos ordenados que contienen a los racionales, pero que no son completos:

- El cuerpo de los números computables. Estableceremos el conjunto de las funciones computables de números racionales como sucesiones f: ℕ₀ → ℚ de Cauchy, junto con un $N \in ℕ$, tal que $∀ (n, m) ∈ ℕ × ℕ , n > N ∧ m > N ⟹ |f(n)-f(m)| < {\frac 1 {2^{N}}}$. Definiremos las operaciones de suma, producto, orden, etc. de forma punto a punto. Este cuerpo es un cuerpo ordenado que contiene a los racionales (identificados con las sucesiones constantes), pero no es completo (como ya hemos visto anteriormente), ya que la sucesión f(n) definida anteriormente es computable pero no tiene porqué tener un límite computable.

- El cuerpo de los números cerrados bajo la operación raíz cuadrada (números constructibles, que son los que nos permiten hacer geometría). Veremos que no es completo.

- El cuerpo de los números cerrados bajo la operación raíces de cualquier exponente entero. Veremos que no es completo.

- El cuerpo de los números algebraicos (cerrados bajo raíces de polinomios con coeficientes enteros). Veremos que no es completo.

---

## 📋 PRÓXIMO — Phase 7: Tuplas e Infraestructura

Antes de polinomios necesitamos un tipo de tupla finita bien fundada en ZFC:

- `SetOps/Tuple.lean`: `IsTuple t n Ω` (t es función de {0,...,n} a Ω), `tuple : (Fin n → U) → U`, `tuple_isFunction`, `tuple_apply`, `tuple_ext` (igualdad punto a punto)
  - Convención A: una tupla de grado $n$ tiene dominio $\sigma n = \{0, \ldots, n\}$ (nota: $n+1$ elementos)
- `SetOps/TupleOps.lean`: `concat` (concatenación de tuplas), `head`, `tail`, `update` (modificar índice), `shift_by` (desplazar dominio)

## 📋 Phase 8 (futura): Monomios y Polinomios

- `Algebra/Monomial.lean`: monomial = par ordenado ⟨grado n∈ω, coeficiente q∈RatSet⟩
- `Algebra/Polynomial.lean`: `IsPolyQ p n ↔ IsTuple p n RatSet`; `polyEval p x` (evaluación); grado, coeficiente líder, algoritmo de división de polinomios
- Teorema: ℚ[X] es dominio de integridad; algoritmo de Euclides para polinomios

## 📋 Phase 9 (futura): Campos Intermedios / Irracionalidad Generalizada

- Generalizar `sqrt2_irrational` a `prime_sqrt_irrational` y `nonsquare_sqrt_irrational` (ver punto [17.] arriba)
- Construir extensiones algebraicas mínimas: ℚ(√p) para p primo

## 📋 Phase 10 (futura): Reales ℝ

Construcción vía sucesiones de Cauchy de racionales:

- `Real/Equiv.lean`: sucesiones de Cauchy en ℚ, relación de equivalencia
- `Real/Basic.lean`: ℝ := Cauchy(ℚ) / ~, completitud
- `Real/Add.lean`, `Neg.lean`, `Mul.lean`, `Order.lean`, `Embedding.lean`
- `Real/Field.lean`: ℝ es cuerpo ordenado completo, propiedad Arquimediana
- `Real/Sequences.lean`: convergencia, sucesiones monótonas acotadas, criterio de Bolzano-Weierstrass
- `Real/Topology.lean`: abiertos, cerrados, compactos (Heine-Borel)
- `Real/Continuity.lean`: Bolzano, Weierstrass
- `Real/Differentiability.lean`: derivada, regla de la cadena, Rolle, valor medio
- `Real/Integration.lean`: integral de Riemann vía particiones
- `Real/FTC.lean`: Teorema Fundamental del Cálculo
- `Real/Series.lean`: series, criterios de convergencia
- `Real/SpecialFunctions.lean`: exp, log, sin, cos (via series), x^r para r ∈ ℝ

**Pendiente menor de BoolAlg**: representación de Stone inversa (isomorfismo inverso BA ≅ 𝒫(A) completa).

---

## 🔮 FUTURO LEJANO

### Álgebra Abstracta

- Grupos, anillos, módulos como estructuras genéricas
- Espacios vectoriales sobre ℚ y ℝ
- Interfaces via Typeclasses de Lean 4 (Naturals, Integers, Rationals, ...)

### Teoría de Ordinales y Cardinales

- Axioma de Reemplazo, Axioma de Fundación, Axioma de Elección
- Ordinales transfinitos, recursión transfinita, aritmética ordinal
- Cardinales ℵ, jerarquía de Zermelo, jerarquía de Gödel (construibles)

### Teoría de Modelos y Fundamentos

- Incompletitud de Gödel (forma de Rosser: consistencia, no solo ω-consistencia)
- Prueba dentro de ZFC

### Sistema de Interfaces entre Axiomáticas

- ZFC, Peano, Aczel (hereditariamente finito), MKplusCAC
- Bridges/functores entre sistemas
- Teoremas genéricos via Typeclasses: `[Naturals N]`, `[Integers Z]`, etc.
- Nuevo proyecto unificador: "Fundamentos de la Matemática en Lean"

---

_Última actualización: 2026-04-23. Phase 5 (ℤ) 100% completa. Comenzando Phase 6 (ℚ)._
