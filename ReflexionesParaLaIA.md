**[1.]** Me acabo de dar cuenta que los teoremas de incompletitud de Gödel también pueden ser demostrados dentro de ZFC, y esto es algo que definitivamente quiero incluir en el proyecto. La demostración de los teoremas de incompletitud de Gödel dentro de ZFC no solo fortalecerá la comprensión de las limitaciones de los sistemas formales, sino que también proporcionará una perspectiva más profunda sobre la naturaleza de la lógica y la matemática. Esto será un paso crucial para mostrar cómo ZFC puede manejar incluso los resultados más profundos y fundamentales en la teoría de la computación y la lógica matemática.

**[2.]** Al revisar el proyecto creo que me he quedado cojo con la parte de Álgebras de Boole, Anillos Booleanos y Retículos por Inclusión en álgebras de la partes de un conjunto. Lo que me interesa es terminar de demostrar que el conjunto de las partes de un conjunto es un Álgebra de Boole Atómica Completa, y luego mostrar que cualquier Álgebra de Boole Atómica Completa es isomorfa a un Álgebra de Boole de partes de un conjunto.

**[3.]** Como continuación de lo anterior, también quiero incluir que todo Anillo Booleano nos lleva via biyección (functor) a un Álgebra de Boole y viceversa.

**[4.]** Construiremos un Álgebra de Boole que no sea atómica con las partes finitas y cofinitas de un conjunto infinito, y mostraremos que no es isomorfa al Álgebra de Boole de las partes de un conjunto. En el caso concreto de un conjunto numerable infinito, quedará claro que hay más Álgebras de Boole que las de las partes de un conjunto. Queda la duda de si en un conjunto inifinito no numerable (aleph_1) también podemos construir un álgebra de Boole de las partes numerables y conumerables de las partes de un conjunto.

**[5.]** Los resultados **[2.]**, **[3.]** y **[4.]** quedarán unidos en un único módulo final sobre este tema.

**[6.]** Queda algo interesante que es demostrar que para los conjuntos finitos, digamos que $F$ es de cardinalidad $n \in \omega$, $#\mathcal{P}(F) = 2^n$. Esto se puede demostrar con el sistema de isomorfismos, mostrando que $\mathcal{P}(F)$ es isomorfo a $2^n$ (con la estructura de los naturales de Von Neumann). Esto también quedará dentro del módulo final sobre Álgebras de Boole.

**[7.]** Además habría que demostrar que si definimos sobre un conjunto finito $F$ un álgebra de Boole, entonces $∃ n ∈ ω, #F = 2^n$.

**[8.]** En ZFC se puede (creo que con lo que tenemos es suficiente) demostrar los teoremas de Incompletitud de Gödel, y esto debe quedar dentro del proyecto. Quisiera que la forma final fuera la forma que demustra consistencia y no solo omega-consitencia (forma de Rosser).

**[9.]** En un futuro, me gustaría incluir una introducción de la Topología, con las definiciones estándar de espacios topológicos, bases, subbases, etc. Igualmente me gustaría introducir la nociones básicas de Teoría de Grupos y de Anillos.

**[10.]** Todo lo anterior nos lleva a que la organización del proyecto es demasiado básica, necesitamos un sistema de módulo y de espacios de nombres más compartimentados y con una organización más clara. Esto es algo que se puede hacer sin problemas, pero que requiere un poco de trabajo para reorganizar todo el proyecto. Creo que sería bueno tener módulos separados para cada uno de los temas principales, como por ejemplo un módulo para los naturales de Von Neumann, otro para las Álgebras de Boole, otro para los teoremas de incompletitud de Gödel, etc. Esto hará que el proyecto sea más fácil de navegar y entender. Además, dentro de cada módulo, podríamos tener submódulos para organizar mejor las definiciones, teoremas y demostraciones relacionadas con ese tema específico. Por ejemplo, dentro del módulo de los naturales de Von Neumann, podríamos tener submódulos para las definiciones básicas, las operaciones aritméticas, las propiedades fundamentales, etc. Esto no solo mejorará la claridad del proyecto, sino que también facilitará la colaboración y el mantenimiento a largo plazo.

**[11.]** Lo siguiente a todo lo anterior (que podría seguir incrementándose hasta el infinito) es crear módulos para los números enteros en ZFC, para los racionales, y finalmente para los reales.

**[12.]** Una vez terminada toda esa parte más práctica, habría que empeza a introducir ordinales, recursión transfinita, y demás temas como aritmética ordinal, el teorema de (cada conjunto al que se le asigne un orden es isomorfo a un único ordinal) etc. Para esto habrá que incorporar los axiomas de ZFC como el de reemplazo y el de elección.

**[13.]**  Acontinuación habría que introducir la teoría de cardinales (aleph) y comenzar a exponer la jerarquía de conjuntos de Zermelo, y después la jerarquía de Gödel (construibles).

**[14.]** Habrá que exponer la teoría de modelos, construcción de modelos, expresiones lógicas relativas y absolutas. Introducción de modelos que satisfacen distintos axiomas, etc.
