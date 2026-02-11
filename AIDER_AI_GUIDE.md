# Necesitamos que el archivo **REFERENCE.md** contenga

## (1.) Los diferentes módulos .lean

## (2.) Las dependencias entre los módulos

## (3.) Espacios de nombres y relaciones entre ellos

## (4.) Axiomas introducidos y sus referencias a dónde se encuentran, módulo, namespace, orden en el que se declaran/definen

## (5.) En cuanto a los axiomas y las definciones, las queremos

### (5.1.) En nomenclatura matemática (no lean code), para una fácil comprensión humana, y para que se puedan usar como referencia en la documentación y en los comentarios de los archivos .lean

### (5.2.) Firma lean4 para que cuando se llamen en demostraciones o construcciones más elaboradas, se haga correctamente

### (5.3.) Debe quedar en algún sitio las dependencias para construir la definición o el axioma

## (6.) Teoremas principales **sin demostración de ningún tipo**, con su referencia a dónde se encuentran, módulo, namespace, orden en el que se declaran/demuestran

### (6.1.) En nomenclatura matemática (no lean code), para una fácil comprensión humana, y para que se puedan usar como referencia en la documentación y en los comentarios de los archivos .lean

### (6.2.) Firma lean4 para que cuando se llamen en demostraciones o construcciones más elaboradas, se haga correctamente

### (6.3.) Debe quedar en algún sitio las dependencias para construir la demostración del teorema

## (7.) Nada que no esté demostrado o construido debe estar en este archivo, ni siquiera como comentario o como "teorema pendiente". Solo lo que ya esté demostrado o construido en los archivos .lean

## (8.) Cada vez que cargas un archivo .lean, actualizas (si es necesario) el REFERENCE.md con lo que se ha demostrado o construido en ese archivo, siguiendo los puntos anteriores. Si hace falta anotar una fecha y la fecha de la última modificación del archivo .lean, estará bien, para trazar bien lo que de hecho tenemos

## (9.) El archivo REFERENCE.md debe ser lo único que necesites para escribir la documentación, o para hacer un nuevo archivo/módulo .lean de forma que no haya que cargar los 200000 tokens que tiene actualmente el proyecto
