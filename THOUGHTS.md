**[1.]** Me acabo de dar cuenta que los teoremas de incompletitud de Gödel también pueden ser demostrados dentro de ZFC, y esto es algo que definitivamente quiero incluir en el proyecto. La demostración de los teoremas de incompletitud de Gödel dentro de ZFC no solo fortalecerá la comprensión de las limitaciones de los sistemas formales, sino que también proporcionará una perspectiva más profunda sobre la naturaleza de la lógica y la matemática. Esto será un paso crucial para mostrar cómo ZFC puede manejar incluso los resultados más profundos y fundamentales en la teoría de la computación y la lógica matemática.

**[2.]** ~~Al revisar el proyecto creo que me he quedado cojo con la parte de Álgebras de Boole, Anillos Booleanos y Retículos por Inclusión en álgebras de la partes de un conjunto. Lo que me interesa es terminar de demostrar que el conjunto de las partes de un conjunto es un Álgebra de Boole Atómica Completa~~, y luego mostrar que cualquier Álgebra de Boole Atómica Completa es isomorfa a un Álgebra de Boole de partes de un conjunto.
> ✅ Primera parte completada en `BoolAlg.Complete.lean`: `PowerSet_is_complete_atomic_BA`. Pendiente: teorema de representación (isomorfismo inverso).

**[3.]** Como continuación de lo anterior, también quiero incluir que todo Anillo Booleano nos lleva via biyección (functor) a un Álgebra de Boole y viceversa.

**[4.]** ~~Construiremos un Álgebra de Boole que no sea atómica con las partes finitas y cofinitas de un conjunto infinito, y mostraremos que no es isomorfa al Álgebra de Boole de las partes de un conjunto.~~ En el caso concreto de un conjunto numerable infinito, quedará claro que hay más Álgebras de Boole que las de las partes de un conjunto. Queda la duda de si en un conjunto inifinito no numerable ($\aleph_1$) también podemos construir un álgebra de Boole de las partes numerables y conumerables de las partes de un conjunto.
> ✅ Completado en `BoolAlg.FiniteCofinite.lean`: `FinCofAlg_not_complete`, `EvenSet_not_in_FinCofAlg`. Nota: FinCofAlg(ω) SÍ es atómica (los átomos son singletons), pero NO es completa — por tanto no es isomorfa a ningún 𝒫(A).

**[5.]** Los resultados **[2.]**, **[3.]** y **[4.]** quedarán unidos en un único módulo final sobre este tema.

**[6.]** Queda algo interesante que es demostrar que para los conjuntos finitos, digamos que $F$ es de cardinalidad $n \in \omega$, $\mathcal{P}(F) = 2^n$. Esto se puede demostrar con el sistema de isomorfismos, mostrando que $\mathcal{P}(F)$ es isomorfo a $2^n$ (con la estructura de los naturales de Von Neumann). Esto también quedará dentro del módulo final sobre Álgebras de Boole.

**[7.]** Además habría que demostrar que si definimos sobre un conjunto finito $F$ un álgebra de Boole, entonces $∃ n ∈ ω, #F = 2^n$.

**[8.]** En ZFC se puede (creo que con lo que tenemos es suficiente) demostrar los teoremas de Incompletitud de Gödel, y esto debe quedar dentro del proyecto. Quisiera que la forma final fuera la forma que demustra consistencia y no solo omega-consitencia (forma de Rosser).

**[9.]** En un futuro, me gustaría incluir una introducción de la Topología, con las definiciones estándar de espacios topológicos, bases, subbases, etc. Igualmente me gustaría introducir la nociones básicas de Teoría de Grupos y de Anillos.

**[10.]** ~~Todo lo anterior nos lleva a que la organización del proyecto es demasiado básica, necesitamos un sistema de módulo y de espacios de nombres más compartimentados y con una organización más clara. Esto es algo que se puede hacer sin problemas, pero que requiere un poco de trabajo para reorganizar todo el proyecto. Creo que sería bueno tener módulos separados para cada uno de los temas principales, como por ejemplo un módulo para los naturales de Von Neumann, otro para las Álgebras de Boole, otro para los teoremas de incompletitud de Gödel, etc. Esto hará que el proyecto sea más fácil de navegar y entender. Además, dentro de cada módulo, podríamos tener submódulos para organizar mejor las definiciones, teoremas y demostraciones relacionadas con ese tema específico. Por ejemplo, dentro del módulo de los naturales de Von Neumann, podríamos tener submódulos para las definiciones básicas, las operaciones aritméticas, las propiedades fundamentales, etc. Esto no solo mejorará la claridad del proyecto, sino que también facilitará la colaboración y el mantenimiento a largo plazo.~~
> ✅ Completado (Fases 1–3, abril 2026): 43 archivos en 8 subdirectorios (Core, Axiom, SetOps, Nat, Peano, Induction, BoolAlg, Cardinal), namespaces `ZFC.*` alineados con directorios, 185 identificadores renombrados según convención Mathlib.

**[11.]** Lo siguiente a todo lo anterior (que podría seguir incrementándose hasta el infinito) es crear módulos para los números enteros en ZFC, para los racionales, y finalmente para los reales.

**[12.]** Una vez terminada toda esa parte más práctica, habría que empeza a introducir ordinales, recursión transfinita, y demás temas como aritmética ordinal, el teorema de (cada conjunto al que se le asigne un orden es isomorfo a un único ordinal) etc. Para esto habrá que incorporar los axiomas de ZFC como el de reemplazo y el de elección.

**[13.]**  Acontinuación habría que introducir la teoría de cardinales (aleph) y comenzar a exponer la jerarquía de conjuntos de Zermelo, y después la jerarquía de Gödel (construibles).

**[14.]** Habrá que exponer la teoría de modelos, construcción de modelos, expresiones lógicas relativas y absolutas. Introducción de modelos que satisfacen distintos axiomas, etc.

**NUEVOS PENSAMIENTOS:**

**[1.]** ~~Es prioritario ordenar fuertemente el proyecto.~~
> ✅ Completado (Fases 1–3).

*[1.1.]* ~~Crear módulos separados en función de los temas principales, a ser posible en subdirectorios separados.~~
> ✅ Completado (Fase 1): Core, Axiom, SetOps, Nat, Peano, Induction, BoolAlg, Cardinal.

*[1.2.]* ~~Utilizar de forma más sistemática y ordenadora los espacios de nombres.~~
> ✅ Completado (Fase 2): namespace `ZFC.*` alineado con directorios.
*[1.3.]* Temas: [Preliminares], [Axiomas de ZFC], [Operaciones con conjuntos en ZFC], [Construcción de los Teoremas sobre Recursión e Inducción], [Números Naturales de Von Neumann], [Integración de los Postulados de Peano en ZFC], [Integración del proyecto Peano en ZFC], [Álgebras y Anillos Booleanos], [Sistemas de Números Enteros, Racionales, Reales y Complejos], [Álgebra Lineal], [Topología], [Ordinales y su Teoría], [Recursion Transfinita], [Teoría de Cardinales], [Jerarquía de Conjuntos de Zermelo], [Jerarquía de Gödel (construibles)], [Teoría de Modelos], etc.
*[1.4.]* Hacer algún tipo de comentario sistematizado para distinguir en cada módulo cuáles son los teoremas principales, cuáles son los secundarios, etc. Esto se puede hacer con algún tipo de etiqueta o comentario especial que permita identificar rápidamente la importancia de cada resultado dentro del módulo.
> ⏳ Pendiente: Fase 4 del plan de reorganización (sistema de anotaciones @importance, @axiom_system).

*[1.5.]* Algún sistema de marcas para identificar las dependencias.
> ⏳ Pendiente: Fase 4.

*[1.6.]* Algún sistema de marcas para identificar los resultados que se han demostrado dentro de ZFC y los que no.
> ⏳ Pendiente: Fase 4.

*[1.7.]* Algún sistema de marcas para identificar los resultados que se han demostrado en Peano o en el sistema de Aczel (nuevo proyecto) y los que no.
> ⏳ Pendiente: Fase 4.

*[1.8.]* ~~Quiero que adoptemos el sistema de nombres de teoremas, definiciones, etc de mathlib, si es que este es fácil de entender y de seguir. Tenemos una deuda de sistematicidad en los nombres que hace que sean muy difíciles de seguir los teoremas etc por sus nombres actuales. Esto es algo que se puede solucionar con un poco de trabajo y que hará que el proyecto sea mucho más fácil de seguir y de entender.~~
> ✅ Completado (Fase 3): 185 identificadores renombrados según convención Mathlib. Ver REFERENCE.md §0 para la tabla completa.

*[1.9.]* ~~Necesitamos un sistema de nombres para módulos y submódulos.~~
> ✅ Completado (Fases 1–2): directorios temáticos + namespaces `ZFC.*`.

*[1.10.]* ~~Necesitamos un sistema de nombres para los espacios de nombres.~~
> ✅ Completado (Fase 2): `ZFC.Axiom.*`, `ZFC.SetOps.*`, `ZFC.Nat.*`, `ZFC.BoolAlg.*`, etc.

**NUEVOS PENSAMIENTOS EXTENSIÓN**

*[1.]* Necesitamos una definición de las álgebras de Boole sobre un conjunto dado (en ZFC) en general. También de álgebras completas y de álgebras atómicas.

*[2.]* El Álgebra de Boole pdodría definirse dentro de la definición de la estructura de un retículo, añadiendo los axiomas correspondientes. Esto es algo que se puede hacer sin problemas y que hará que la definición de Álgebra de Boole sea más clara y más fácil de entender.

*[3.]* También necesitamos definir la estructura genérica de un grupo, de un anillo, y de un módulo izquierdo y derecho, para luego poder definir los grupos, anillos y módulos concretos dentro de ZFC. Esto es algo que se puede hacer sin problemas y que hará que la definición de estos objetos algebraicos sea más clara y más fácil de entender.

*[4.]* Dentro del punto *[3.]* anterior, definiremos la estructura de anillo booleano, y mostraremos que todo anillo booleano nos lleva a un álgebra de boole y viceversa. Esto es algo que se puede hacer sin problemas y que hará que la relación entre estas dos estructuras algebraicas sea más clara y más fácil de entender.

*[5.]* Todo lo anterior podría quedar en dos grupos temáticos, Álgebras de Boole y Retículos (estructuras de orden sobre conjuntos) por un lado, y Grupos, Anillos y Módulos (operaciones que cumplen determinadas propiedades sobre uno o varios conjuntos) como Álgebra Abstracta por otro lado.

*[6.]* Para usar ya en los conjuntos numéricos que vayamos creando, podemos definir el espacio vectorial como un afinamiento de un módulo, y luego definir los espacios vectoriales concretos sobre los números racionales, reales, etc. Esto es algo que se puede hacer sin problemas y que hará que la definición de espacio vectorial sea más clara y más fácil de entender.

*[7.]* Para el functor entre álgebras de Boole y anillos booleanos, tendremos que definir la estructura de Álgebra de Boole:

**Estructura de Álgebra de Boole:**

La estructura $\langle B, +_B, \cdot_B, \mathbf{0}_B, \mathbf{1}_B \rangle$ es un álgebra de Boole si cumple:

1. $\langle B, +_B, \mathbf{0}_B \rangle$ es una operación interna conmutativa con identidad $\mathbf{0}_B$.

2. $\langle B, \cdot_B, \mathbf{1}_B \rangle$ es una operación interna conmutativa con identidad $\mathbf{1}_B$.

3. La operación $+_B$ distribuye sobre $\cdot_B$.

4. Para cada elemento $a \in B$ existe un elemento $\neg_B a$ tal que $a +_B \neg_B a = \mathbf{1}_B$ y $a \cdot_B \neg_B a = \mathbf{0}_B$.

*[7.1.]* Habrá que añadirle la propiedad de ser completa.

*[7.2.]* Habrá que añadirle la propiedad de ser atómica.

**De Álgebra de Boole a Anillo Booleano:**

Si el álgebra de Boole es $\langle B, +_B, \cdot_B, \mathbf{0}_B, \mathbf{1}_B \rangle$, entonces definimos la función suma exclusiva $\oplus_B : B \times B \to B$ como $a \oplus_B b := (a \cdot_B \neg_B b) +_B (\neg_B a \cdot_B b)$, y definiremos la multiplicación $\odot_B : B \times B \to B$ como $a \odot_B b := a \cdot_B b$.
Entonces, con estas operaciones, $\langle B, \oplus_B, \odot_B, \mathbf{0}_B, \mathbf{1}_B \rangle$ es un anillo booleano.
Además el functor asignará a $\mathbf{0}_B$ el elemento $\mathbf{0}_R$, y a $\mathbf{1}_B$ el elemento $\mathbf{1}_R$.

*[8.]* Para el functor entre álgebras de Boole y anillos booleanos, tendremos que definir la estructura de grupo y de anillo:

**Estructura de Grupo:**

$\langle G, +_G, \mathbf{0}_G \rangle$ es un grupo si cumple:

1. $+_G$ es una operación interna asociativa con identidad $\mathbf{0}_G$.

2. Para cada elemento $x \in G$ existe un elemento $y \in G$ tal que $x +_G y = \mathbf{0}_G$ y $y +_G x = \mathbf{0}_G$.

La estructura de anillo es un refinamiento de la estructura de grupo, añadiendo una operación de multiplicación que cumple las siguientes propiedades:

**Estructura de Anillo Booleano:**

La estructura $\langle R, +_R, \cdot_R, \mathbf{0}_R, \mathbf{1}_R \rangle$ es un anillo booleano si cumple:

1. $\langle R, +_R, \mathbf{0}_R \rangle$ es un grupo abeliano.

2. $\langle R, \cdot_R, \mathbf{1}_R \rangle$ es una operación asociativa con identidad $\mathbf{1}_R$.

3. La operación $\cdot_R$ distribuye sobre $+_R$.

Para que sea un anillo booleano, además de lo anterior, debe cumplir la propiedad de ser idempotente:

1. Para cada elemento $a \in R$ se cumple que $a \cdot_R a = a$.

**De Anillo Booleano a Álgebra de Boole:**

Si el anillo booleano es $\langle R, +_R, \cdot_R, \mathbf{0}_R, \mathbf{1}_R \rangle$, entonces definimos la función $+_B : R \times R \to R$ como $a +_B b := a +_R b +_R (a \cdot_R b)$, y definimos $\cdot_B : R \times R \to R$ como $a \cdot_B b := a \cdot_R b$.
Entonces, con estas operaciones, $\langle R, +_B, \cdot_B, \mathbf{0}_R, \mathbf{1}_R \rangle$ es un álgebra de Boole.
Además el functor asignará a $\mathbf{0}_R$ el elemento $\mathbf{0}_B$, y a $\mathbf{1}_R$ el elemento $\mathbf{1}_B$.

**NOVÍSIMOS:**

*[1.]* Hay que quitar los warnings de lean, de forma que aparezcan solo los errores, y finalmente la salida sea completamente limpia. Esto es algo que se puede hacer con un poco de trabajo y que hará que el proyecto sea mucho más fácil de seguir y de entender, ya que no habrá ruido visual de warnings que no aportan nada.

*[2.]* Haría falta hacer todo lo anteripr también en el proyecto Peano.

*[3.]* Necesitamos hacer un sistema de "interfaz" de los axiomas, teoremas, operaciones, etc. independientes del sistema axiomático demostrado.

*[4.]* *ZFC* sería un *modelo* que satisface las interfaces anteriormente escritas, como también *Peano*, como el sistema de *Aczel* (comenzado en paralelo), como el sistema del proyecto *MKplusCAC*.

*[5.]* Para *[5.]* nos hace falta una estructuración más robusta del proyecto, que llegue a unificar todos los proyectos anteriores.

*[6.]* Todo lo dicho quedaría en un nuevo proyecto, que podría llamarse algo así como "Fundamentos de la Matemática en Lean", o algo por el estilo, que unificaría todos los proyectos anteriores y que tendría una organización mucho más clara y sistematizada. Este nuevo proyecto sería el que se mantendría a largo plazo, y en el que se irían añadiendo nuevos temas y resultados a medida que se vayan desarrollando. El proyecto actual de ZFC quedaría como un subproyecto dentro de este nuevo proyecto más amplio, y se iría integrando poco a poco con los demás subproyectos (Peano, Aczel, MKplusCAC, etc) para crear una visión unificada de los fundamentos de la matemática en Lean.

**INMEDIATO: ENTEROS**

[1.] En $ω×ω$ establecemos la relación de equivalencia $(a,b)∼ω×ω(c,d)⟺a+d=b+c$. Entonces, los enteros se definen como las clases de equivalencia de esta relación. Hay que demostrar que $∼ω×ω$ es una relación de equivalencia, que es transitiva, simétrica y reflexiva.

[2.] Definimos los enteros $\bZ := (ω×ω)/∼ω×ω$ como el conjunto de las clases de equivalencia de la relación $∼ω×ω$. ¿Usamos el setoid? Cada entero se representa como una clase de equivalencia de pares ordenados de naturales, donde el primer componente representa la parte positiva y el segundo componente representa la parte negativa. Por ejemplo, el entero $0_z$ se representa como la clase de equivalencia que contiene al par $(0,0)$, el entero $1_z$ se representa como la clase de equivalencia que contiene al par $(1,0)$, el entero $-1_z$ se representa como la clase de equivalencia que contiene al par $(0,1)$, etc. De esta forma, cada entero se puede representar de forma única como un par ordenado de naturales, con uno de los componentes igual a cero. Esto nos permite trabajar con los enteros dentro del marco de ZFC utilizando solo los números naturales y las operaciones definidas sobre ellos. El elemento neutro aditivo es $0_z := [(0,0)]$, el elemento neutro multiplicativo es $1_z = [(1,0)]$, y el inverso aditivo de $[(a,b)]$ es $-[(a,b)]=[(b,a)]$.

[3.] Cogeremos siempre el representante canónico de cada clase de equivalencia, que será concretamente el representante de la clase de equivalencia que tiene la forma $[(a,0)]$ para $a≥0$, y $[(0,b)]$ para $b>0$. De esta forma, cada entero se representa de forma única como un par ordenado de naturales, con uno de los componentes igual a cero.

[4.] Establecemos la relación de orden total en los enteros, definiendo $[(a,b)] ≤ [(c,d)]$ si y solo si $a + d ≤ b + c$. Hay que demostrar que esta relación es un orden total, es decir, que es reflexiva, antisimétrica, transitiva y total.

[5.] Establecemos una biyección entre los enteros y los naturales de Von Neumann, definiendo la función $f : \bZ \to ω$ como $f([(a,b)]) = a - b$ si $a ≥ b$, y $f([(a,b)]) = -(b - a)$ si $b > a$. Hay que demostrar que esta función es una biyección, es decir, que es inyectiva y sobreyectiva.

[6.] Establecemos una biyección entre los enteros y los números de Peano, definiendo la función $g : \bZ \to \mathbb{N}_{Peano}$ como $g([(a,b)]) = S^a(0)$ si $a ≥ b$, y $g([(a,b)]) = -S^b(0)$ si $b > a$. Hay que demostrar que esta función es una biyección, es decir, que es inyectiva y sobreyectiva.

[7.] La suma y el producto se definen de la forma habitual: $[(a,b)]+[(c,d)]=[(a+c,b+d)]$ y $[(a,b)]⋅[(c,d)]=[(ac+bd,ad+bc)]$. Hay que demostrar que estas operaciones están bien definidas.

[8.] Hay que demostrar que con estas operaciones, los enteros forman un anillo conmutativo con identidad, y que además cumplen las propiedades habituales de los enteros, como por ejemplo que la suma es conmutativa y asociativa, que el producto es conmutativo y asociativo, que el producto distribuye sobre la suma, etc.

[9.] Establecemos una inyección canónica de los naturales de Von Neumann en los enteros, definiendo la función $h : ω \to \bZ$ como $h(n) = [(n,0)]$. Hay que demostrar que esta función es una inyección, es decir, que es inyectiva y que su imagen es un subconjunto de los enteros. Demostramos que esta función preserva la suma y el producto. También demostramos que preserva el orden, es decir, que si $m ≤ n$ en $ω$, entonces $h(m) ≤ h(n)$ en $\bZ$.

[10.] También tendremos la exponenciación con exponente natural, la definimos como en los naturales. 

[11.] Hay que traer todo lo demostrado en el módulo de los naturales: igualdad de Bezout, y TFA, etc. para demostrar que los enteros también cumplen estas propiedades.

[12.] Nos traeremos todo el sistema de inducción, para trabajar ágilmente con los enteros, y para demostrar propiedades de los enteros por inducción.

[13.] Volvemos a traer la operaciones de números binomiales, los factoriales, el binomio de Newton, etc. para trabajar con los enteros de forma más ágil y para demostrar propiedades de los enteros relacionadas con estas operaciones.

[14.] Finalmente, también podríamos definir la función valor absoluto, y demostrar sus propiedades habituales, como por ejemplo que el valor absoluto de un entero es siempre un número natural, que el valor absoluto de un producto es el producto de los valores absolutos, etc. También definiremos la función signo, y demostraremos sus propiedades habituales, como por ejemplo que el signo de un producto es el producto de los signos, etc.

[15.] Propiedades de crecimiento de las funciones de argumentos enteros y retorno entero. Por ejemplo, que la multiplicación crece más que la suma, que la exponenciación crece más que la multiplicación,que el valor absoluto de un producto es el producto de los valores absolutos, etc. *[Esto debería estar ya en los naturales y traerlo aquí]*

**INMEDIATO 2: RACIONALES**

[1.] Establecemos el conjunto $\mathbb{Z}^{*} := \mathbb{Z} ⧵ \{0_z\}$, y el conjunto base $\mathbb{Z}\times\mathbb{Z}^{*}$.

[2.] Establecemos en $\mathbb{Z}\times\mathbb{Z}^{*}$ la relación de equivalencia $(a,b)∼\mathbb{Z}\times\mathbb{Z}^{*}(c,d)⟺a⋅d=b⋅c$. Entonces, los racionales se definen como las clases de equivalencia de esta relación. [¿usamos setoid?] Hay que demostrar que $∼\mathbb{Z}\times\mathbb{Z}^{*}$ es una relación de equivalencia, que es transitiva, simétrica y reflexiva.

[3.] Definimos los racionales $\bQ := (\mathbb{Z}\times\mathbb{Z}^{*})/∼\mathbb{Z}\times\mathbb{Z}^{*}$ como el conjunto de las clases de equivalencia de la relación $∼\mathbb{Z}\times\mathbb{Z}^{*}$. Cada racional se representa como una clase de equivalencia de pares ordenados de enteros, donde el primer componente representa el numerador y el segundo componente representa el denominador. Por ejemplo, el racional $0_q$ se representa como la clase de equivalencia que contiene al par $(0_z,1_z)$, el racional $1_q$ se representa como la clase de equivalencia que contiene al par $(1_z,1_z)$, el racional $-1_q$ se representa como la clase de equivalencia que contiene al par $(-1_z,1_z)$, etc. De esta forma, cada racional se puede representar de forma única como un par ordenado de enteros, con el segundo componente distinto de cero. Esto nos permite trabajar con los racionales dentro del marco de ZFC utilizando solo los números enteros y las operaciones definidas sobre ellos. El elemento neutro aditivo es $0_q := [(0_z,1_z)]$, el elemento neutro multiplicativo es $1_q = [(1_z,1_z)]$, y el inverso aditivo de $[(a,b)]$ es $-[(a,b)]=[(-a,b)]$, y el inverso multiplicativo de $[(a,b)]$ es $[(b,a)]$ si $a≠0_z$.

[4.] Cogeremos siempre el representante canónico de cada clase de equivalencia, que será concretamente el representante de la clase de equivalencia que tiene la forma $[(a,b)]$ con $a$ y $b$ coprimos, y $b>0$. De esta forma, cada racional se representa de forma única como un par ordenado de enteros, con el segundo componente distinto de cero.

[5.] Establecemos la relación de orden total en los racionales, definiendo $[(a,b)] ≤ [(c,d)]$ si y solo si $a⋅d ≤ b⋅c$. Hay que demostrar que esta relación es un orden total, es decir, que es reflexiva, antisimétrica, transitiva y total. También que no depende del representante de la clase de equivalencia que elijamos.

[6.] Establecemos una biyección entre los racionales y los naturales de Peano, definiendo la función $f : \bQ \to \mathbb{N}_{Peano}$ como $f([(a,b)]) = S^n(0)$ si $a/b ≥ 0$, y $f([(a,b)]) = -S^n(0)$ si $a/b < 0$, donde $n$ es el valor absoluto del cociente $a/b$. Hay que demostrar que esta función es una biyección, es decir, que es inyectiva y sobreyectiva. La cardinalidad de los racionales es la misma que la de los naturales.

[7.] La suma y el producto se definen de la forma habitual: $[(a,b)]+[(c,d)]=[(ad+bc,bd)]$ y $[(a,b)]⋅[(c,d)]=[(ac,bd)]$. Hay que demostrar que estas operaciones están bien definidas.

[8.] Establecemos la inyección de los números enteros en los racionales, definiendo la función $g : \bZ \to \bQ$ como $g([(a,b)]) = [(a,1_z)]$. Hay que demostrar que esta función es una inyección, es decir, que es inyectiva. Demostramos que se conservan todas las operaciones de los enteros dentro de los racionales. También demostramos que se conserva el orden de los enteros dentro de los racionales.

[9.] Hay que demostrar que con estas operaciones, los racionales forman un cuerpo conmutativo con identidad, y que además cumplen las propiedades habituales de los racionales, como por ejemplo que la suma es conmutativa y asociativa, que el producto es conmutativo y asociativo, que el producto distribuye sobre la suma, etc.

[10.] También tendremos la exponenciación con exponente entero. Demostramos que está bien definida, y que cumple las propiedades habituales de la exponenciación, como por ejemplo que $x^0=1_q$ para todo $x≠0_q$, que $x^{m+n}=x^m⋅x^n$ para todo $m,n∈\bZ$, que $(x⋅y)^n=x^n⋅y^n$ para todo $n∈\bZ$, etc. 

[11.] Defininimos las sucesiones de los racionales, y definimos las sucesiones de Cauchy y las sucesiones con límite.

[12.] Entre cualquier dos racionales distintos, hay un racional distinto de los anteriores. Entre cualquiera dos racionales distintos, existe una cantidad infinita de racionales distintos de los anteriores. Esto muestra que los racionales son densos.

[13.] Sucesiones monótonas crecientes/decrecientes acotadas no tienen necesariamente límite en los racionales. Dar ejemplos de sucesiones monótonas crecientes/decrecientes acotadas que no tienen límite en los racionales, como por ejemplo alguna subsucesión concreta de $\{a_n ∈ \bQ ∣ a_n^2 < 2\}$ estrictamente creciente , que es monótonamente creciente y acotada por $2$, pero que no tiene límite dentro de los racionales.

[14.] ¿Merece la pena definir las series de racionales? ¿O es mejor esperar a tener los reales para definir las series de números reales? Creo que es mejor esperar a tener los reales, ya que las series de racionales no tienen tantas propiedades interesantes como las series de números reales, y además pueden ser un poco más complicadas de manejar debido a la densidad de los racionales. Por ejemplo, una serie de racionales puede converger a un número irracional, lo que puede complicar un poco las cosas. Por tanto, creo que es mejor esperar a tener los reales para definir las series de números reales, y así poder aprovechar todas las propiedades interesantes que tienen las series de números reales.

**INMEDIATO 3: REALES**

[1.] Establecemos el conjunto base de las sucesiones de racionales, es decir, el conjunto $\bQ^{\bN}$ de todas las funciones $f : \bN \to \bQ$.

[2.] Definimos la relación de equivalencia en $\bQ^{\bN}$ que identifica dos sucesiones de racionales $f$ y $g$ si y solo si la sucesión de diferencias $f(n) - g(n)$ converge a $0_q$. Es decir, $f ∼ g$ si y solo si para todo $\epsilon > 0_q$, existe un número natural $N$ tal que para todo $n ≥ N$, se cumple que $|f(n) - g(n)| < \epsilon$. Hay que demostrar que esta relación es una relación de equivalencia, es decir, que es reflexiva, simétrica y transitiva.

[3.] Definimos los números reales $\bR := \bQ^{\bN}/∼$ como el conjunto de las clases de equivalencia de la relación $∼$. Cada número real se representa como una clase de equivalencia de sucesiones de racionales. Por ejemplo, el número real $0_r$ se representa como la clase de equivalencia que contiene a la sucesión constante $f(n) = 0_q$ para todo $n$, el número real $1_r$ se representa como la clase de equivalencia que contiene a la sucesión constante $f(n) = 1_q$ para todo $n$, etc. De esta forma, cada número real se puede representar de forma única como una clase de equivalencia de sucesiones de racionales. Esto nos permite trabajar con los números reales dentro del marco de ZFC utilizando solo los números racionales y las operaciones definidas sobre ellos. El elemento neutro aditivo es $0_r := [f]$ donde $f(n) = 0_q$ para todo $n$, el elemento neutro multiplicativo es $1_r = [g]$ donde $g(n) = 1_q$ para todo $n$, el inverso aditivo de $[f]$ es $-[f] = [-f]$ donde $-f(n) = -f(n)$ para todo $n$, y el inverso multiplicativo de $[f]$ es $[h]$ donde $h(n) = 1/f(n)$ si $f(n) ≠ 0_q$ para todo $n$, y $h(n) = 0_q$ si $f(n) = 0_q$ para algún $n$.

[4.] Cogeremos el representante canónico de cada clase de equivalencia que represente un número racional por la función constante ese número racional.

[5.] Establecemos la relación de orden total en los números reales, definiendo $[f] ≤ [g]$ si y solo si la sucesión de diferencias $f(n) - g(n)$ converge a un número real menor o igual a $0_r$. Es decir, $[f] ≤ [g]$ si y solo si para todo $\epsilon > 0_r$, existe un número natural $N$ tal que para todo $n ≥ N$, se cumple que $f(n) - g(n) < \epsilon$. Hay que demostrar que esta relación es un orden total, es decir, que es reflexiva, antisimétrica, transitiva y total. También que no depende del representante de la clase de equivalencia que elijamos.

[6.] La suma y el producto se definen de la forma habitual: $[f]+[g]=[f+g]$ donde $(f+g)(n) = f(n) + g(n)$ para todo $n$, y $[f]⋅[g]=[f⋅g]$ donde $(f⋅g)(n) = f(n) ⋅ g(n)$ para todo $n$. Hay que demostrar que estas operaciones están bien definidas.

[7.] Hay que demostrar que con estas operaciones, los números reales forman un cuerpo conmutativo con identidad, y que además cumplen las propiedades habituales de los números reales, como por ejemplo que la suma es conmutativa y asociativa, que el producto es conmutativo y asociativo, que el producto distribuye sobre la suma, etc.

[8.] Establecemos la inyección de los números racionales en los números reales, de forma que se conserven todas las operaciones de números racionales y su orden dentro de los números reales. Esto se puede hacer definiendo la función $f : \bQ \to \bR$ como $f(q) = [g]$ donde $g(n) = q$ para todo $n$. Hay que demostrar que esta función es una inyección, es decir, que es inyectiva y que conserva todas las operaciones de números racionales y su orden dentro de los números reales.

[9.] También tendremos la exponenciación con exponente real. Demostramos que está bien definida, y que cumple las propiedades habituales de la exponenciación, como por ejemplo que $x^0=1_r$ para todo $x≠0_r$, que $x^{m+n}=x^m⋅x^n$ para todo $m,n∈\bR$, que $(x⋅y)^n=x^n⋅y^n$ para todo $n∈\bR$, etc. 

[10.] Definimos las sucesiones de los números reales, y definimos las sucesiones de Cauchy y las sucesiones con límite.

[11.] Entre cualquier dos números reales distintos, hay un número racional distinto de los anteriores. Entre cualquiera dos números reales distintos, existe una cantidad infinita de números racionales distintos de los anteriores. Esto muestra que los números racionales son densos en los números reales.

[12.] Sucesiones monótonas crecientes/decrecientes acotadas tienen límite en los números reales. Dar ejemplos demostrar que las sucesiones monótonas crecientes/decrecientes acotadas tienen límite en los números reales, como por ejemplo alguna subsucesión concreta de $\{a_n ∈ \bQ ∣ a_n^2 < 2\}$ estrictamente creciente , que es monótonamente creciente y acotada por $2$, y que tiene límite dentro de los números reales, concretamente el número real $√2$.

[13.] Completitud de los números reales: todo subconjunto no vacío de los números reales que está acotado superiormente tiene un supremo.

[14.] Definimos las funciones continuas y todas las propiedades habituales de las funciones continuas, como por ejemplo que la suma y el producto de funciones continuas es continua, que la composición de funciones continuas es continua, etc. También definimos las funciones derivables y todas las propiedades habituales de las funciones derivables, como por ejemplo que la suma y el producto de funciones derivables es derivable, que la composición de funciones derivables es derivable, etc.

[15.] Definimos las series de números reales con base en las sucesiones de números reales, y definimos la convergencia de las series de números reales. También definimos las propiedades habituales de las series de números reales, como por ejemplo que la suma de una serie de números reales es conmutativa y asociativa, que el producto de una serie de números reales es conmutativo y asociativo, que el producto distribuye sobre la suma, etc.

[16.] Convergencia absoluta y relativa de las series de números reales, y todas las propiedades habituales de la convergencia absoluta y relativa, como por ejemplo que una serie de números reales que converge absolutamente también converge relativamente, pero que una serie de números reales que converge relativamente no necesariamente converge absolutamente, etc.

[17.] Definimos la integración de funciones continuas al estilo Riemann, y todas las propiedades habituales de la integración de funciones continuas, como por ejemplo que la suma y el producto de funciones integrables es integrable, que la composición de funciones integrables es integrable, etc.

[18.] Definimos la derivación de funciones continuas, y todas las propiedades habituales de la derivación de funciones continuas, como por ejemplo que la suma y el producto de funciones derivables es derivable, que la composición de funciones derivables es derivable, etc.

[19.] Definimos las funciones exponenciales, logarítmicas, trigonométricas, etc. y todas las propiedades habituales de estas funciones, como por ejemplo que la función exponencial es continua y derivable, que la función logarítmica es continua y derivable, que las funciones trigonométricas son continuas y derivables, etc.

[20.] Definimos las funciones hiperbólicas, y todas las propiedades habituales de las funciones hiperbólicas, como por ejemplo que las funciones hiperbólicas son continuas y derivables, etc.

[21.] Teorema fundamental del cálculo: la derivación y la integración son operaciones inversas entre sí, es decir, que si $f$ es una función continua en un intervalo cerrado $[a,b]$, entonces la función $F$ definida por $F(x) = \int_a^x f(t) dt$ para todo $x ∈ [a,b]$ es una función derivable en el intervalo abierto $(a,b)$, y su derivada es igual a $f$, es decir, que $F'(x) = f(x)$ para todo $x ∈ (a,b)$.

**UNA IDEA DE IMPLEMENTACIÓN DE LOS NOVÍSIMOS**

0. El sistema de puentes entre sistemas axiomáticos

   0.1. El sistema de Aczel debe probar como teoremas los axiomas de ZF (sin infinitud y sin regularidad, por supuesto que sin elección).

   0.2. El sistema de Peano debe probar que puede reproducido dentro del sistema de Aczel.

   0.3. El sistema ZF (debidamente recortado) debe probar que los axiomas de Aczael se pueden demostrar como teoremas dentro de ZF.

   0.4. El sistema de ZF debe probar que puede reproducir el sistema de Peano.

   0.5. El sistema de Aczel debe probar que puede reproducir el sistema de Peano.

   0.6. El sistema de MKplusCAC debe probar que puede reproducir el sistema ZFC completo.

   0.7. Debemos probar quje existen teoremas en ZFC que no pueden ser demostrados en el sistema computacional de Aczel.

   0.8. Debemos probar que existen teoremas en MKplusCAC que no pueden ser demostrados en ZFC.

   0.9. Debemos mantener el esquema de pruebas que tenemos en ZFC, que introduce los distintos axiomas solo cuando son necesarios para demostrar algún nuevo teorema en algún nuevo tema concreto. De esta forma, mantenemos una jerarquía clara de los axiomas dentro de los porpios sistemas axiomáticos, manteniendo así una isomorfía constructiva de los diferentes sistemas por capas.

1. Las "Interfaces" son Clases de Tipos (class)

En Lean 4, la forma estándar de hacer que un teorema sirva tanto para Peano como para Von Neumann es usar Typeclasses. En lugar de demostrar el Teorema Fundamental de la Aritmética para un tipo específico, lo demuestras para cualquier tipo que cumpla tu interfaz.
Lean

-- 1. Defines la interfaz abstracta (Typeclass)
class Naturals (N : Type) where
  zero : N
  succ : N → N
  add  : N → N → N
  -- Aquí añadirías los axiomas, por ejemplo:
  succ_inj : ∀ {a b : N}, succ a = succ b → a = b
  -- (y el principio de inducción)

-- 2. Tus implementaciones serán instancias (Instances)
inductive PeanoNat where
  | zero : PeanoNat
  | succ : PeanoNat → PeanoNat

instance : Naturals PeanoNat where
  zero := PeanoNat.zero
  succ := PeanoNat.succ
  add  := ... -- tu función de suma
  succ_inj := ... -- tu demostración

De este modo, cuando escribas el teorema fundamental, su firma será algo como: theorem fundamental_arithmetic {N : Type} [Naturals N] : .... Lean se encargará de inyectar los axiomas correctos ya sea que uses Peano o Von Neumann.

1. Isomorfismos y el paso de teoremas (Equiv)

Para tus "puentes" entre Peano y Von Neumann, no reinventes la rueda: usa (o replica si estás evitando Mathlib) las equivalencias. Una equivalencia en Lean (≃) es una biyección con su inversa demostrada.

Si demuestras que PeanoNat ≃ VonNeumannNat, puedes usar técnicas de transferencia. Lean tiene mecanismos (o puedes escribir una pequeña macro/táctica gracias al sistema de metaprogramación de Lean 4) para que si tienes un teorema demostrado en PeanoNat, la táctica lo transporte a través del isomorfismo (Equiv) para generar automáticamente la demostración en VonNeumannNat. Esto mantendrá tu código base extremadamente limpio.

1. Manejando Morse-Kelley vs ZFC: Universos de Tipos

Lean 4 está basado en la Teoría de Tipos (Cálculo de Construcciones Inductivas), no en Teoría de Conjuntos. Hacer Teoría de Conjuntos axiomática dentro de Lean requiere crear un modelo. Aquí es donde Morse-Kelley (MK) brilla en Lean si usas los Universos de Tipos (Type u).

    Conjuntos (ZFC): Puedes definir tu modelo de conjuntos como un tipo inductivo o una estructura que habita en un universo particular (ej. Type 0).

    Clases (MK): En Morse-Kelley, las clases propias son colecciones de conjuntos que son "demasiado grandes" para ser conjuntos. En Lean 4, esto se modela maravillosamente subiendo un nivel en la jerarquía de universos. Una clase sobre tu modelo de conjuntos V puede ser simplemente un predicado V → Prop. Así, el esquema de reemplazo de ZFC y el esquema de comprensión de clases de MK se expresan de forma muy natural usando las funciones del propio lenguaje Lean.

4. El Modelo de Aczel (Computabilidad plena)

Mencionaste que estás construyendo Aczel basado en listas para que sea computable. El punto fuerte de Lean 4 es que compila a C.
Para tu modelo de Aczel, usa el comando inductive estándar de Lean apoyado en estructuras de datos eficientes (como List o Array).
Lean

-- Un modelo muy simplificado de Aczel (conjuntos hereditariamente finitos)
inductive AczelSet where
  | mk (elements : List AczelSet) : AczelSet
  deriving Repr

Como Lean 4 diferencia entre Prop (proposiciones, que se borran en tiempo de compilación y no tienen coste de ejecución) y Type (datos), puedes escribir tu sistema de Aczel para que operaciones como la intersección o unión sean funciones computables reales (def), que puedes testear usando #eval. Luego, usas Prop y theorem para demostrar que esas funciones en Lean satisfacen los axiomas de la Teoría de Conjuntos de tu capa base.
Siguientes pasos en tu proyecto Lean 4:

    Crea un lakefile.lean robusto: Organiza tu código en módulos lógicos (ej. MathFundamentals.Axioms.ZFC, MathFundamentals.Arithmetic.Abstract, etc.).

    Abraza las class: Reescribe tus teoremas de Peano para que acepten variables de tipo [Naturals N] en lugar de depender directamente del tipo Peano.

    Aisla las dependencias: Crea un archivo raíz que simplemente importe todo tu trabajo para asegurarte de que Lean compila todo el ecosistema sin dependencias circulares (Lean es muy estricto con esto).
