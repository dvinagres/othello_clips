; =========================================
; 1. TEMPLATES (Estructuras de datos)
; =========================================

; Representa una única casilla del tablero
; El atributo "nivel" es importante: el 0 es la partida real, y los niveles > 0 son las situaciones que crea el agente para pensar
; De esta manera, podemos reutilizar las mismas reglas para: partida real o simulaciones Minimax
(deftemplate tablero
    (slot fila (type INTEGER))
    (slot columna (type INTEGER))
    (slot estado (type SYMBOL) (allowed-values vacia negra blanca))
    (slot nivel (type INTEGER) (default 0))
)

; Almacena los ajustes globales de la partida
(deftemplate configuracion
    (slot tamano (type INTEGER) (default 8))
)

; Controla de quién es el turno actual
(deftemplate turno
    (slot jugador (type SYMBOL) (allowed-values negra blanca))
    (slot nivel (type INTEGER) (default 0))
)

; Cada participante. 
; Define si es humano o máquina y lleva la cuenta de las fichas que le quedan por poner
(deftemplate jugador
    (slot color (type SYMBOL) (allowed-values negra blanca))
    (slot tipo (type SYMBOL) (allowed-values humano maquina))
    (slot cantidad_fichas (type INTEGER))
)

; Es la "orden" que da un jugador (o el agente) cuando elige dónde mover 
; La fase de validación comprueba si este movimiento es legal y ejecutable
(deftemplate intento-movimiento
    (slot color (type SYMBOL))
    (slot fila (type INTEGER))
    (slot columna (type INTEGER))
    (slot nivel (type INTEGER) (default 0))
)

; Controla el flujo de la partida 
; Define en qué estado (fase) nos encontramos y en qué profundidad (nivel) se está ejecutando
; Controlamos la máquina de estados del sistema
(deftemplate juego
    (slot fase (allowed-values inicializacion analisis peticion validacion ejecucion cambio-turno fin-juego simulacion))
    (slot nivel (type INTEGER) (default 0))
)

; Define los 8 vectores de movimiento (horizontal, vertical y diagonales)
; Se usa para que los "rastreadores" sepan hacia dónde tienen que ir
; Así evitamos programar lógica separada para cada dirección
(deftemplate direccion
    (slot df (type INTEGER)) ; Desplazamiento de fila (-1, 0, 1)
    (slot dc (type INTEGER)) ; Desplazamiento de columna (-1, 0, 1)
)

; Generado por la validación
; Guarda la coordenada de inicio, la coordenada final del "sándwich" y la dirección, datos imprescindibles para la regla de voltear fichas
; Permite luego voltear fichas
(deftemplate captura-confirmada
    (slot fila-orig)
    (slot col-orig)
    (slot fila-fin)
    (slot col-fin)
    (slot df)
    (slot dc)
    (slot color)
    (slot nivel (type INTEGER) (default 0))
)

; Es el "explorador" temporal que camina por el tablero buscando fichas 
; Se usa tanto para buscar huecos libres (análisis) como para confirmar "sándwiches" (validación)
; Rastreo es una estructura de exploración temporal que analiza direcciones posibles, 
; mientras que captura-confirmada representa una línea legal ya validada que será usada para ejecutar el volteo de fichas
(deftemplate rastreo
   (slot f (type INTEGER))
   (slot c (type INTEGER))
   (slot df (type INTEGER))
   (slot dc (type INTEGER))
   (slot orig-f (type INTEGER)) ; Casilla vacía donde empezó el rastreo
   (slot orig-c (type INTEGER))
   (slot nivel (type INTEGER) (default 0))
)

; Es el resultado de la fase de análisis 
; Marca una casilla como candidata legal para poner una ficha, informando al jugador de sus opciones o al agente de sus posibles ramas
(deftemplate posible-jugada
   (slot fila)
   (slot columna)
   (slot puntuacion (default 0))
   (slot nivel (type INTEGER) (default 0))
)

; Estructura para Alpha-Beta
; Representa un estado en el árbol de búsqueda del agente, guardando sus límites de poda (alpha/beta) y la evaluación de esa rama
(deftemplate nodo
   (slot nivel (type INTEGER))           ; Profundidad actual
   (slot padre-nivel (type INTEGER))     ; Referencia al nivel anterior
   (slot alpha (type NUMBER) (default -10000)) ; El mejor valor para MAX
   (slot beta (type NUMBER) (default 10000))   ; El mejor valor para MIN
   (slot estado (allowed-values expandiendo evaluado finalizado))
   (slot valor-elegido (type NUMBER))    ; El valor que subirá al padre
)

; Marca temporal para el algoritmo del agente
; Evita que la máquina intente clonar y evaluar la misma "posible-jugada" más de una vez en el mismo nivel de simulación
(deftemplate simulacion-iniciada
    (slot fila (type INTEGER))
    (slot columna (type INTEGER))
    (slot nivel (type INTEGER) (default 0))
)

; =========================================
; 2. FACTS (Hechos iniciales)
; =========================================

; Esta es la "foto" del juego antes de poner la primera ficha
; Aquí definimos las reglas del mundo: el tablero será de 8x8, el humano (negras) empieza primero,
; y ambos jugadores tienen 30 fichas en mano. 
; También inicializamos variables de control: 'pases-consecutivos' para saber cuándo 
; se bloquea la partida (Primer jugador sin movimientos → pasa turno, Segundo consecutivo → fin de partida)
; y 'profundidad-maxima' que marca hasta qué nivel "pensará" el agente (Minimax). Limitamos porque explorar todo el árbol sería computacionalmente inviable.
(deffacts estado-inicial
    (configuracion (tamano 8))
    (turno (jugador negra))
    (jugador (color negra) (tipo humano) (cantidad_fichas 30))
    (jugador (color blanca) (tipo maquina) (cantidad_fichas 30))
    (juego (fase inicializacion)) ; Arrancamos en inicialización
    (pases-consecutivos 0)
    (profundidad-maxima 3)
)

; Define los 8 vectores posibles (vertical, horizontal y las 4 diagonales)
; Al dejarlos como hechos, evitamos usar bucles for/while en las reglas; 
; el motor de CLIPS simplemente lanzará exploradores en estas 8 direcciones simultáneamente
(deffacts vectores-direccion
    (direccion (df -1) (dc -1)) (direccion (df -1) (dc  0)) (direccion (df -1) (dc  1))
    (direccion (df  0) (dc -1))                            (direccion (df  0) (dc  1))
    (direccion (df  1) (dc -1)) (direccion (df  1) (dc  0)) (direccion (df  1) (dc  1))
)

; =========================================
; 3. FUNCIONES
; =========================================

; Dibuja el tablero en la consola de texto para que el jugador humano pueda jugar
; Es una función puramente visual que genera una cuadrícula dinámica según el tamaño
; DETALLE: la condición '(= ?casilla:nivel 0)' garantiza que la pantalla SOLO muestre la partida real y 
; nunca imprima los tableros que el agente está "imaginando" durante sus simulaciones.
(deffunction mostrar-tablero (?tamano)
    (printout t crlf "    | ")
    (loop-for-count (?c 1 ?tamano) (printout t ?c " | "))
    (printout t crlf)
    
    ; Línea divisoria dinámica
    (loop-for-count (?i 1 (+ 2 (* ?tamano 4))) (printout t "-")) 
    (printout t crlf)

    (loop-for-count (?f 1 ?tamano)
        (printout t " " ?f " | ") 
        (loop-for-count (?c 1 ?tamano)
            (do-for-fact ((?casilla tablero)) 
                (and (= ?casilla:fila ?f) (= ?casilla:columna ?c) (= ?casilla:nivel 0))
                (if (eq ?casilla:estado vacia) then (printout t "  | "))
                (if (eq ?casilla:estado negra) then (printout t "N | "))
                (if (eq ?casilla:estado blanca) then (printout t "B | "))
            )
        )
        (printout t crlf)
        (loop-for-count (?i 1 (+ 2 (* ?tamano 4))) (printout t "-"))
        (printout t crlf)
    )
)

; =========================================
; 4. RULES (Reglas del sistema)
; =========================================

; -----------------------------------------
; 4.1. INICIALIZACIÓN Y FLUJO BÁSICO
; -----------------------------------------

; Se ejecuta una única vez
; Calcula  el centro del tablero (dividiendo el tamaño entre 2) 
; para colocar las 4 fichas iniciales cruzadas (2 blancas y 2 negras). 
; DETALLE: crea absolutamente todas las casillas (ocupadas y vacías) 
; anclándolas al "nivel 0" (el juego real). Tras montar el escenario, 
; avanza el estado del juego directamente a la fase de "análisis" para buscar el primer movimiento
(defrule inicializar-tablero
   ?fase <- (juego (fase inicializacion))
   (configuracion (tamano ?n))
   =>
   (bind ?c1 (/ ?n 2)) (bind ?c2 (+ (/ ?n 2) 1)) 
   (loop-for-count (?f 1 ?n)
      (loop-for-count (?c 1 ?n)
         (bind ?estado (if (or (and (= ?f ?c1) (= ?c ?c1)) (and (= ?f ?c2) (= ?c ?c2))) then blanca
                        else (if (or (and (= ?f ?c1) (= ?c ?c2)) (and (= ?f ?c2) (= ?c ?c1))) then negra
                        else vacia)))
         (assert (tablero (fila ?f) (columna ?c) (estado ?estado) (nivel 0)))
      )
   )
   (retract ?fase)
   (assert (juego (fase analisis) (nivel 0)))
   (printout t "TABLERO INICIALIZADO" crlf)
   (mostrar-tablero ?n)
)

; Solo se dispara si estamos en el nivel 0 (juego real) y si el jugador con el turno actual es de tipo 'humano'
; Su trabajo es simple: detiene la ejecución, lee las coordenadas que se escriben por teclado 
; y las transforma en el hecho 'intento-movimiento'. 
; Automáticamente después, pasa a la fase de 'validacion' para que el sistema 
; compruebe si lo que se acaba de escribir es legal
(defrule pedir-movimiento-humano
    ?fase <- (juego (fase peticion) (nivel 0))
    (configuracion (tamano ?n))
    (turno (jugador ?color-actual) (nivel 0))
    (jugador (color ?color-actual) (tipo humano))
    (not (intento-movimiento (nivel 0)))
    =>
    (printout t "Turno de " ?color-actual ". Fila (1-" ?n "): ")
    (bind ?f (integer (read))) 
    (printout t "Columna (1-" ?n "): ")
    (bind ?c (integer (read)))
    (assert (intento-movimiento (color ?color-actual) (fila ?f) (columna ?c) (nivel 0)))
    (retract ?fase)
    (assert (juego (fase validacion) (nivel 0))) 
)

; Esta regla gestiona la transición entre jugadores una vez terminada la ejecución.
; Se encarga de invertir el color del jugador activo y, si es la partida real (nivel 0),
; dibuja el tablero actualizado en pantalla para dar retroalimentación visual.
; DETALLE: 'do-for-all-facts' filtrado por '(= ?j:nivel ?n)'. Al cambiar de turno, 
; borra las marcas de 'posible-jugada' del jugador anterior, pero SOLO en el nivel actual. 
; Esto asegura que, cuando el agente simule el futuro, no borre accidentalmente las jugadas 
; de los niveles superiores del árbol Minimax que todavía está evaluando.
; Por último, reinicia el ciclo enviando el motor a la fase de 'analisis'.
(defrule realizar-cambio-turno
    ?fase <- (juego (fase cambio-turno) (nivel ?n))
    ?t <- (turno (jugador ?color) (nivel ?n))
    (configuracion (tamano ?tam))
    =>
    (retract ?t ?fase)
    (bind ?nuevo-color (if (eq ?color negra) then blanca else negra))
    (assert (turno (jugador ?nuevo-color) (nivel ?n)))
    
    (if (= ?n 0) then
        (printout t crlf "--- TURNO DE " ?nuevo-color " ---" crlf)
        (mostrar-tablero ?tam) ; 
    )
    ; SOLO borramos las posibles jugadas del nivel actual
    (do-for-all-facts ((?j posible-jugada)) (= ?j:nivel ?n) (retract ?j))
    (assert (juego (fase analisis) (nivel ?n)))
)

; Esta regla soluciona un caso muy común en Othello:
; ¿Qué ocurre si a un jugador le tocan movimientos legales en el tablero, pero ya ha gastado todas sus fichas de la mano?
; En lugar de dar error o bloquear la partida, se simula la regla de donde el rival le "presta" una ficha.
; DETALLE: tiene una prioridad alta '(declare (salience 50))'. Esto garantiza
; que el traspaso de la ficha ocurra justo ANTES de que el sistema le pida al jugador (o al agente) que mueva.
(defrule ceder-ficha
    (declare (salience 50)) ; Prioridad alta para que ocurra antes de leer el teclado
    (juego (fase peticion) (nivel 0))
    (turno (jugador ?color) (nivel 0))
    ?j-actual <- (jugador (color ?color) (cantidad_fichas 0))
    ?j-rival <- (jugador (color ~?color) (cantidad_fichas ?c-rival&:(> ?c-rival 0)))
    =>
    (modify ?j-actual (cantidad_fichas 1))
    (modify ?j-rival (cantidad_fichas (- ?c-rival 1)))
    (printout t "AVISO: " ?color " no tiene fichas en mano. El rival le cede una." crlf)
)

; -----------------------------------------
; 4.2. ANÁLISIS DE TABLERO
; -----------------------------------------

; 1.
; Escanea todo el tablero buscando una combinación exacta:
; 1. Una casilla que esté vacía.
; 2. Que tenga, justo a su lado (en cualquiera de las 8 direcciones), una ficha del rival.
; Si encuentra esto, dispara un "explorador" (el hecho 'rastreo'). 
; DETALLE: en la parte de la derecha (assert), no se manda al "explorador" a la casilla del rival, sino que lo manda directamente a la SIGUIENTE 
; casilla usando '(* 2 ?df)'. Como ya se sabe que el vecino es enemigo, se envia al explorador a comprobar qué hay detrás de ese enemigo.
(defrule iniciar-analisis
   (juego (fase analisis) (nivel ?n))
   (turno (jugador ?p) (nivel ?n))
   (tablero (fila ?f) (columna ?c) (estado vacia) (nivel ?n))
   (direccion (df ?df) (dc ?dc))
   (tablero (fila =(+ ?f ?df)) (columna =(+ ?c ?dc)) (estado ?r&~vacia&~?p) (nivel ?n))
   =>
   ; Guardamos el origen (orig-f, orig-c) para saber qué casilla estamos evaluando
   (assert (rastreo (f (+ ?f (* 2 ?df))) (c (+ ?c (* 2 ?dc))) (df ?df) (dc ?dc) (orig-f ?f) (orig-c ?c) (nivel ?n)))
)

; 2. 
; Una vez que el "explorador" nace (en la regla anterior), esta regla lo hace caminar.
; Se mueve solo si la casilla que está pisando actualmente contiene una ficha del rival ('~vacia&~?p').
; Si es así, significa que el "sándwich" todavía es posible, por lo que el "explorador" debe dar un paso más.
; DETALLE: se usa la función 'modify' en lugar de borrar y crear un hecho nuevo con 'assert/retract'. 
; 'modify' simplemente actualiza los valores 'f' y 'c' sumándoles la dirección ('df' y 'dc'). 
(defrule propagar-analisis
   (juego (fase analisis) (nivel ?n))
   ?rastreo <- (rastreo (f ?f) (c ?c) (df ?df) (dc ?dc) (nivel ?n)) 
   (turno (jugador ?p) (nivel ?n))
   (tablero (fila ?f) (columna ?c) (estado ~vacia&~?p) (nivel ?n))
   =>
   (modify ?rastreo (f (+ ?f ?df)) (c (+ ?c ?dc)))
)

; 3. 
; Se dispara cuando el "explorador" finalmente choca con una ficha de su propio color ('estado ?p').
; DETALLE: en el la parte de ejecución, el explorador se destruye con '(retract ?rastreo)' 
; porque ya ha hecho su trabajo. Pero lo más importante es que el '(assert (posible-jugada...))' 
; NO usa las coordenadas actuales ('?rf', '?rc'), sino las coordenadas de ORIGEN ('?f', '?c') 
; del "explorador". Ahí es donde el jugador debe poner la ficha.
(defrule exito-analisis
   (juego (fase analisis) (nivel ?n))
   ?rastreo <- (rastreo (orig-f ?f) (orig-c ?c) (f ?rf) (c ?rc) (nivel ?n))
   (turno (jugador ?p) (nivel ?n))
   (tablero (fila ?rf) (columna ?rc) (estado ?p) (nivel ?n))
   =>
   (retract ?rastreo)
   (assert (posible-jugada (fila ?f) (columna ?c) (nivel ?n)))
)

; 4. 
; No todos los caminos llevan a un "sándwich" válido. 
; Se encarga de eliminar al "explorador" (hacer un retract) si ocurren dos cosas:
; 1. Se sale del tablero (la coordenada ya no existe en los hechos).
; 2. Aterriza en una casilla vacía (lo que rompe la línea continua de fichas enemigas).
; DETALLE: '(declare (salience -5))'. Al darle prioridad negativa, 
; se obliga a CLIPS a que PRIMERO intente hacer avanzar al "explorador" o confirmar su éxito. 
; Si ninguna de esas opciones se puede ejecutar, entonces, y solo como último recurso, 
; se dispara esta regla para limpiar la basura y no saturar la memoria.
(defrule limpiar-analisis
   (declare (salience -5))
   (juego (fase analisis) (nivel ?n))
   ?rastreo <- (rastreo (f ?f) (c ?c) (nivel ?n)) 
   (or (not (tablero (fila ?f) (columna ?c) (nivel ?n)))
       (tablero (fila ?f) (columna ?c) (estado vacia) (nivel ?n)))
   =>
   (retract ?rastreo)
)

; --- RESOLUCIÓN PARA EL JUEGO REAL (Nivel 0) ---

; Esta regla confirma si se puede continuar la partida.
; Se dispara solo cuando termina de escanear (salience -10) y confirma que al menos 
; hay una casilla legal donde jugar en el tablero real (nivel 0).
; DETALLE: '(exists (posible-jugada...))'. Si no usáramos 'exists' y el jugador tuviera 5 jugadas posibles, esta regla intentaría 
; dispararse 5 veces y colapsaría el flujo.
; Además, como el jugador SÍ puede mover, reiniciamos el contador 
; de 'pases-consecutivos' a 0 y pasamos a la fase de pedirle las coordenadas ('peticion').
; Aunque los rastreos deberían haberse eliminado ya durante el análisis anterior (exito-analisis o limpiar-analisis),
; se realiza una limpieza exhaustiva para prevenir residuos en la base de hechos y asegurar estabilidad entre fases.
(defrule analisis-con-movimientos-real
   (declare (salience -10))
   ?fase <- (juego (fase analisis) (nivel 0))
   (exists (posible-jugada (nivel 0))) ; Usamos exists para evitar disparos duplicados
   ?p-cons <- (pases-consecutivos ?c)
   =>
   (retract ?fase ?p-cons)
   (do-for-all-facts ((?r rastreo)) (= ?r:nivel 0) (retract ?r))
   (assert (pases-consecutivos 0))
   (assert (juego (fase peticion) (nivel 0)))
)

; Esta regla es el reverso de la anterior. Mira si un jugador se queda sin opciones.
; Al tener (salience -10), espera a que terminen todos los "exploradores". 
; Si al terminar, NO existe ninguna '(posible-jugada)', significa que el jugador actual está bloqueado.

; DETALLE: 
; En Othello, si no puedes mover, pasas turno. Pero si NINGUNO de los dos puede mover, la partida termina.
; Por eso se usa la variable '?pcount' (pases consecutivos):
; - Si valía 0: es el primer bloqueo. Suma 1 al contador, y salta directamente 
;   a la fase de 'cambio-turno' (robando el turno sin pasar por 'peticion').
; - Si valía 1: significa que el rival anterior tampoco pudo mover. El tablero está 
;   completamente congelado. Se envía el juego a la fase 'fin-juego'.
(defrule analisis-sin-movimientos-real
   (declare (salience -10))
   ?fase <- (juego (fase analisis) (nivel 0))
   (not (posible-jugada (nivel 0)))
   ?p <- (pases-consecutivos ?pcount)
   (turno (jugador ?color) (nivel 0))
   =>
   (retract ?fase ?p)
   (if (= ?pcount 1) then
       (printout t "FIN DEL JUEGO: Ningun jugador tiene movimientos validos." crlf)
       (assert (juego (fase fin-juego) (nivel 0)))
   else
       (printout t "AVISO: " ?color " no tiene movimientos. Pasa turno." crlf)
       (assert (pases-consecutivos 1))
       (assert (juego (fase cambio-turno) (nivel 0)))
   )
)

; --- RESOLUCIÓN PARA LA SIMULACIÓN DE LA IA (Nivel > 0) ---

; Esta regla hace exactamente la misma función que la anterior, 
; pero está diseñada en exclusiva para los tableros paralelos del agente (nivel > 0).
; La diferencia principal está en la consecuencia: como aquí no hay un humano al que preguntarle,
; no se pasa a la fase de 'peticion'. En su lugar, se limpia la basura del rastreo y 
; pasamos directamente a la fase de 'simulacion'. 
; Allí, Minimax tomará las 'posibles-jugadas' encontradas y decidirá cuál probar primero.
(defrule analisis-con-movimientos-sim
   (declare (salience -10))
   ?fase <- (juego (fase analisis) (nivel ?n&:(> ?n 0)))
   (exists (posible-jugada (nivel ?n)))
   =>
   (retract ?fase)
   (do-for-all-facts ((?r rastreo)) (= ?r:nivel ?n) (retract ?r))
   (assert (juego (fase simulacion) (nivel ?n)))
)

; Se ejecuta con máxima prioridad (salience 100) si, al explorar un futuro posible (nivel > 0), 
; el algoritmo llega a un tablero donde el jugador activo no tiene jugadas legales.
; Al no poder expandir más ramas desde aquí, este escenario se trata como un nodo hoja.
; DETALLE: como el juego se detiene en esta rama, hay que darle una puntuación. 
; La regla cuenta todas las fichas del agente (blancas) y le resta las fichas del humano (negras). 
; Este cálculo ('- ?f-ia ?f-hu') funciona como la función de evaluación heurística. 
; El resultado se almacena en el slot 'valor-elegido' y el nodo pasa a estado 'evaluado', 
; para que el algoritmo propague ese número hacia arriba en el árbol.
(defrule evaluar-tablero-sin-movimientos-sim
   (declare (salience 100))
   ?fase <- (juego (fase analisis) (nivel ?n&:(> ?n 0)))
   (not (posible-jugada (nivel ?n)))
   ?nod <- (nodo (nivel ?n) (estado expandiendo))
   =>
   (retract ?fase)
   (bind ?f-ia (length$ (find-all-facts ((?t tablero)) (and (= ?t:nivel ?n) (eq ?t:estado blanca)))))
   (bind ?f-hu (length$ (find-all-facts ((?t tablero)) (and (= ?t:nivel ?n) (eq ?t:estado negra)))))
   (modify ?nod (estado evaluado) (valor-elegido (- ?f-ia ?f-hu)))
)

; -----------------------------------------
; 4.3. VALIDACIÓN Y ERRORES
; -----------------------------------------

; 1. 
; Esta regla es estructuralmente casi idéntica a 'iniciar-analisis', 
; pero su propósito en la arquitectura del juego es totalmente distinto.
; Mientras que el análisis buscaba TODAS las opciones posibles a lo ancho del tablero, 
; esta regla evalúa exclusivamente las coordenadas que el jugador (o el agente) acaba de proponer 
; mediante el hecho 'intento-movimiento'. 
; Si detecta una ficha enemiga justo al lado, dispara un rastreador ('rastreo') en esa dirección 
; para comprobar si la línea termina en una ficha propia y el movimiento es legal.
(defrule iniciar-rastreo
   (juego (fase validacion) (nivel ?n)) 
   (intento-movimiento (color ?propio) (fila ?f) (columna ?c) (nivel ?n))
   (direccion (df ?df) (dc ?dc))
   (tablero (fila =(+ ?f ?df)) (columna =(+ ?c ?dc)) (estado ?rival&~vacia&~?propio) (nivel ?n))
   =>
   (assert (rastreo (f (+ ?f (* 2 ?df))) (c (+ ?c (* 2 ?dc))) (df ?df) (dc ?dc) (orig-f ?f) (orig-c ?c) (nivel ?n)))
)

; 2. 
; Esta regla es la equivalente a 'propagar-analisis', pero opera estrictamente 
; durante la fase de validación de un movimiento específico.
; Su función es mantener al "explorador" caminando en la dirección asignada 
; mientras la casilla que pise contenga una ficha del oponente ('~vacia&~?propio').
; DETALLE: reutiliza el uso de 'modify' para sumar los desplazamientos 
; ('df' y 'dc') a las coordenadas actuales. El "explorador" continuará su camino 
; en esa línea recta hasta que se tope con una casilla vacía, se salga del tablero, 
; o encuentre una ficha del jugador actual (lo que confirmaría la jugada).
(defrule propagar-rastreo
   (juego (fase validacion) (nivel ?n))
   ?r <- (rastreo (f ?f) (c ?c) (df ?df) (dc ?dc) (nivel ?n))
   (intento-movimiento (color ?propio) (nivel ?n))
   (tablero (fila ?f) (columna ?c) (estado ?rival&~vacia&~?propio) (nivel ?n))
   =>
   (modify ?r (f (+ ?f ?df)) (c (+ ?c ?dc)))
)

; 3. 
; Esta regla certifica que el movimiento elegido es legal en una dirección concreta.
; Se dispara cuando el rastreador que venía avanzando por fichas enemigas 
; choca finalmente con una ficha del jugador actual ('estado ?propio').
; DETALLE: se destruye el rastreador '(retract ?r)' y nace un nuevo hecho llamado 'captura-confirmada'. 
; Este nuevo hecho contiene la info de la acción (dónde empieza, dónde acaba y en qué dirección va) 
; que el sistema utilizará en la siguiente fase para saber qué fichas debe voltear.
(defrule confirmar-captura
   (juego (fase validacion) (nivel ?n))
   ?r <- (rastreo (f ?f_fin) (c ?c_fin) (df ?df) (dc ?dc) (nivel ?n))
   (intento-movimiento (color ?propio) (fila ?f_orig) (columna ?c_orig) (nivel ?n))
   (tablero (fila ?f_fin) (columna ?c_fin) (estado ?propio) (nivel ?n))
   =>
   (retract ?r)
   (assert (captura-confirmada (fila-orig ?f_orig) (col-orig ?c_orig) 
                               (fila-fin ?f_fin) (col-fin ?c_fin)
                               (df ?df) (dc ?dc) (color ?propio) (nivel ?n)))
)

; 4. 
; Al igual que sucedía en la fase de análisis, no todas las direcciones exploradas 
; a partir del intento de movimiento terminan en un "sándwich" válido.
; Esta regla elimina al rastreador si se da una de estas dos condiciones:
; 1. Se cae por el borde del tablero (la coordenada ya no existe).
; 2. Tropieza con una casilla vacía (rompiendo la línea ininterrumpida que exige Othello).
; DETALLE: gracias a su prioridad baja '(declare (salience -5))', el motor 
; solo recurre a esta regla si las reglas de avanzar o confirmar (que tienen 
; prioridad normal de 0) no pueden ejecutarse.
(defrule limpiar-rastreo-fallido
   (declare (salience -5))
   (juego (fase validacion) (nivel ?n))
   ?r <- (rastreo (f ?f) (c ?c) (nivel ?n))
   (or (not (tablero (fila ?f) (columna ?c) (nivel ?n)))
       (tablero (fila ?f) (columna ?c) (estado vacia) (nivel ?n)))
   =>
   (retract ?r)
)

; 5.
; Se ejecuta con alta prioridad (salience 20) si el jugador intenta colocar una ficha 
; en una coordenada del tablero que ya contiene una pieza ('estado ?estado&~vacia').
; DETALLE: al detectar la infracción, la regla termina la validación 
; eliminando el hecho 'intento-movimiento'. A continuación, imprime un mensaje de error 
; por consola y hace retroceder el estado del juego a la fase de 'peticion', 
; obligando al jugador a introducir unas coordenadas nuevas y válidas. 
; Está restringida al 'nivel 0' porque el motor de análisis garantiza que el agente 
; nunca genere intentos de movimiento sobre casillas ocupadas durante sus simulaciones.
(defrule error-casilla-ocupada
    (declare (salience 20))
    ?fase <- (juego (fase validacion) (nivel 0))
    ?i <- (intento-movimiento (fila ?f) (columna ?c) (nivel 0))
    (tablero (fila ?f) (columna ?c) (estado ?estado&~vacia) (nivel 0))
    =>
    (retract ?i ?fase)
    (printout t "ERROR: Casilla ocupada por " ?estado ". Intenta de nuevo." crlf)
    (assert (juego (fase peticion) (nivel 0)))
) 

; 6.
; Esta regla evita que el programa falle si el jugador introduce números fuera del tamaño del tablero (por ejemplo, fila 9 o columna 0).
; Se ejecuta con alta prioridad (salience 20) durante la fase de validación en la partida real (nivel 0).
; Si no existe el hecho que representa a la casilla en memoria, el movimiento está fuera de los límites físicos del tablero, se borra el intento 
; y devuelve el estado a la fase de 'peticion' para volver a preguntar.
(defrule error-coordenadas-invalidas
    (declare (salience 20))
    ?fase <- (juego (fase validacion) (nivel 0))
    ?i <- (intento-movimiento (fila ?f) (columna ?c) (nivel 0))
    (not (tablero (fila ?f) (columna ?c) (nivel 0)))
    =>
    (retract ?i ?fase)
    (printout t "ERROR: Las coordenadas " ?f "," ?c " no existen en el tablero." crlf)
    (assert (juego (fase peticion) (nivel 0)))
)

; 7.
; Esta regla comprueba la legalidad estructural de la jugada.
; Su característica principal es la prioridad muy baja '(declare (salience -20))'. 
; Esto obliga al motor a esperar a que todos los rastreadores
; terminen de buscar en las 8 direcciones posibles. 
; Si, una vez concluida toda la exploración, el sistema verifica que NO se ha generado 
; ni un solo hecho de 'captura-confirmada', significa que la coordenada elegida 
; no consigue hacer el "sándwich" a ninguna ficha rival, lo cual es ilegal en Othello.
; DETALLE: borra el intento de movimiento y devuelve el juego a la fase de 'peticion'. 
; Además, la condición '(if (= ?n 0) ...)': solo se imprime por consola si es una partida real
(defrule error-movimiento-ilegal
    (declare (salience -20)) ; Se ejecuta al final de la validacion
    ?fase <- (juego (fase validacion) (nivel ?n))
    ?i <- (intento-movimiento (fila ?f) (columna ?c) (nivel ?n))
    (not (captura-confirmada (nivel ?n)))
    =>
    (retract ?fase ?i)
    (if (= ?n 0) then (printout t "ERROR: Movimiento ilegal. Debe capturar al menos una ficha rival." crlf))
    (assert (juego (fase peticion) (nivel ?n)))
)

; 8.
; Esta regla actúa como el puente entre la validación y la acción.
; Su prioridad media-baja '(declare (salience -10))' asegura que se ejecute 
; después de que los rastreadores hayan evaluado y limpiado las rutas (-5), pero 
; estrictamente antes de que salte el error por movimiento ilegal (-20).
; DETALLE: exige la presencia de al menos un hecho 'captura-confirmada'. 
; En Othello, una sola ficha puede provocar volteos en múltiples direcciones a la vez. 
; Aunque existan varios hechos de captura para un mismo movimiento, al hacer un 
; '(retract ?fase)' en el consecuente, se elimina la condición principal de disparo. 
; Esto garantiza que esta regla de transición se ejecute una única vez por turno. 
; Tras esto, el motor avanza a la fase de 'ejecucion' para colocar y voltear las fichas.
; Es decir, solo nos interesa saber si hay alguna captura confirmada y si se puede pasar a la siguiente fase
(defrule validar-exito-y-ejecutar
   (declare (salience -10))
   ?fase <- (juego (fase validacion) (nivel ?n))
   (captura-confirmada (nivel ?n)) ; Existe al menos una dirección válida
   =>
   (retract ?fase)
   (assert (juego (fase ejecucion) (nivel ?n)))
)

; -----------------------------------------
; 4.4. EJECUCIÓN DE MOVIMIENTOS
; -----------------------------------------

; 1. COLOCAR: pone la ficha y marca el inicio del volteo
; Una vez que la fase de validación ha garantizado que el movimiento es legal 
; (generando los hechos 'captura-confirmada'), esta regla ejecuta la primera 
; acción: colocar la nueva ficha en la casilla vacía.
; DETALLE: se le asigna una prioridad alta '(declare (salience 10))'. 
; Esto asegura que la ficha original se asiente en el tablero antes de que 
; el sistema empiece a procesar los volteos de las fichas capturadas.
; Adicionalmente, el bloque '(if (= ?n 0)...)' discrimina entre el juego real y la simulación. 
; La resta de la ficha del inventario del jugador y el aviso por consola solo se ejecutan 
; en el nivel 0, evitando cálculos de inventario innecesarios para el agente.
(defrule colocar-ficha-actual
   (declare (salience 10))
   ?fase <- (juego (fase ejecucion) (nivel ?n))
   ?i <- (intento-movimiento (color ?color) (fila ?f) (columna ?c) (nivel ?n))
   ?casilla <- (tablero (fila ?f) (columna ?c) (estado vacia) (nivel ?n))
   ?jug <- (jugador (color ?color) (cantidad_fichas ?can))
   =>
   (retract ?i)
   (modify ?casilla (estado ?color))
   (if (= ?n 0) then
       (modify ?jug (cantidad_fichas (- ?can 1)))
       (printout t "Ficha " ?color " colocada en " ?f "," ?c crlf)
   )
)

; 2. VOLTEAR: Reacción en cadena (Efecto Dominó)
; Esta regla es el corazón de la mecánica de captura.
; Al emparejar una 'captura-confirmada' con cualquier ficha rival en el tablero,
; la regla evalúa simultáneamente si dicha ficha debe ser volteada.
;
; DETALLE: el uso de '(test)' actúa como un filtro:
; 1. Producto cruzado = 0: garantiza que la ficha enemiga pertenece a la recta matemática que une el origen y el destino.
; 2. Sentido del vector: asegura que la ficha enemiga está "hacia adelante" en la dirección del movimiento, evitando falsos positivos detrás de la jugada.
; 3. Límites espaciales: usa valores absolutos para certificar que la ficha está estrictamente atrapada entre la pieza colocada y la que cierra el "sándwich".
; Además, la ejecución ('if (= ?n 0)') mantiene la máxima velocidad durante los volteos imaginarios que procesa el árbol del agente
(defrule aplicar-volteo
   (juego (fase ejecucion) (nivel ?n)) 
   (captura-confirmada (fila-orig ?fo) (col-orig ?co) 
                       (fila-fin ?ff) (col-fin ?cf) 
                       (df ?df) (dc ?dc) (color ?p) (nivel ?n)) 
   
   ; Buscamos fichas del rival en el tablero
   ?t <- (tablero (fila ?fr) (columna ?cr) (estado ~vacia&~?p) (nivel ?n)) 
   
   ; TEST GEOMÉTRICO: ¿Está la ficha rival en la línea y entre los dos extremos?
   (test (and
      ; 1. ¿Está alineada con el movimiento? (Producto cruzado = 0)
      (= (* (- ?fr ?fo) ?dc) (* (- ?cr ?co) ?df))
      ; 2. ¿Está en la dirección correcta?
      (>= (* (- ?fr ?fo) ?df) 0)
      (>= (* (- ?fr ?fo) ?dc) 0)
      ; 3. ¿Está antes de llegar a la ficha que cierra el sándwich?
      (or (< (abs (- ?fr ?fo)) (abs (- ?ff ?fo)))
          (< (abs (- ?cr ?co)) (abs (- ?cf ?co))))
   ))
   =>
   (modify ?t (estado ?p))
   (if (= ?n 0) then (printout t "Ficha capturada en [" ?fr "," ?cr "]" crlf)) 
)

; 3. FINALIZAR: Limpia las direcciones y cambia el turno
; Esta regla marca el final de la jugada.
; Al tener una prioridad baja '(declare (salience -10))', el motor garantiza 
; que espera a que todas las cascadas de volteos provocadas por 
; la regla 'aplicar-volteo' (que opera con prioridad normal) hayan concluido por completo.
; 
; DETALLE: verifica que ya no exista el 'intento-movimiento' 
; (el cual fue consumido al colocar la ficha inicial). Tras esto, ejecuta una 
; limpieza masiva mediante 'do-for-all-facts' para eliminar todos los vectores de 
; 'captura-confirmada' exclusivos de este nivel de profundidad (?n). Finalmente, cierra la fase de
; 'ejecucion' y envía el estado del juego a 'cambio-turno', cerrando el ciclo 
; tanto para la partida en curso como para las ramas simuladas.
(defrule finalizar-fase-ejecucion
   (declare (salience -10))
   ?fase <- (juego (fase ejecucion) (nivel ?n))
   (not (intento-movimiento (nivel ?n)))
   =>
   (retract ?fase)
   (do-for-all-facts ((?c captura-confirmada)) (= ?c:nivel ?n) (retract ?c))
   (assert (juego (fase cambio-turno) (nivel ?n)))
)

; -----------------------------------------
; 4.5. MINIMAX (ALPHA-BETA)
; -----------------------------------------

; Durante el juego real (nivel 0), cuando el sistema entra en la fase de 'peticion', 
; habitualmente se esperaría una entrada por teclado. Sin embargo, esta regla verifica 
; directamente si el jugador activo está clasificado como 'maquina'.
; 
; DETALLE: si es el turno del agente, la regla retira la fase de 'peticion' 
; para anular cualquier solicitud al usuario. En su lugar, transfiere el estado a 'simulacion' 
; e inicializa la estructura de datos para el algoritmo Minimax creando el nodo raíz. 
; Este primer 'nodo' se establece en el 'nivel 0', con un 'padre-nivel' de -1 
; (para indicar que es la base del árbol) y se inicializa en estado 'expandiendo', 
; lo que habilitará a las siguientes reglas para empezar a calcular los movimientos futuros.
(defrule iniciar-simulacion-ia
   ?fase <- (juego (fase peticion) (nivel 0))
   (turno (jugador ?p) (nivel 0))
   (jugador (color ?p) (tipo maquina))
   =>
   (retract ?fase)
   (assert (juego (fase simulacion) (nivel 0)))
   (assert (nodo (nivel 0) (padre-nivel -1) (estado expandiendo)))
   (printout t "IA pensando..." crlf)
)

; Esta regla es el mecanismo principal de ramificación del algoritmo Minimax.
; Se ejecuta cuando el sistema está en un nodo en expansión, tiene jugadas disponibles
; que aún no ha explorado y no ha superado la profundidad máxima de búsqueda ('?max').
;
; DETALLE: para calcular las consecuencias de una 'posible-jugada', 
; el agente requiere un entorno de prueba aislado. La regla genera un nuevo índice 
; de profundidad ('?nuevo-nivel') y utiliza la función 'do-for-all-facts' para duplicar 
; casilla por casilla el estado del tablero actual hacia el nuevo nivel.
; Una vez estructurado este tablero paralelo, introduce la jugada seleccionada como un 
; 'intento-movimiento' y establece la fase del nuevo nivel en 'validacion'. 
; Esta arquitectura permite que el sistema reutilice las mismas reglas 
; (rastreo, captura y volteo) que controlan las jugadas de la partida real. 
; El hecho 'simulacion-iniciada' asegura que cada ramificación se procese una sola vez.
(defrule clonar-nivel-para-simulacion
   (juego (fase simulacion) (nivel ?n))
   (nodo (nivel ?n) (estado expandiendo))
   (profundidad-maxima ?max)
   (test (< ?n ?max))
   ; Buscamos una jugada que queramos probar
   ?j <- (posible-jugada (fila ?f) (columna ?c) (nivel ?n))
   (not (simulacion-iniciada (fila ?f) (columna ?c) (nivel ?n)))
   (turno (jugador ?color-actual) (nivel ?n))
   =>
   (bind ?nuevo-nivel (+ ?n 1))
   ; Clonamos el tablero al completo para el nuevo nivel
   (do-for-all-facts ((?t tablero)) (= ?t:nivel ?n)
      (assert (tablero (fila ?t:fila) (columna ?t:columna) (estado ?t:estado) (nivel ?nuevo-nivel)))
   )
   
   ; Mantenemos el turno original, insertamos el movimiento y lanzamos la validación del motor
   (assert (turno (jugador ?color-actual) (nivel ?nuevo-nivel)))
   (assert (intento-movimiento (color ?color-actual) (fila ?f) (columna ?c) (nivel ?nuevo-nivel)))
   (assert (juego (fase validacion) (nivel ?nuevo-nivel)))
   
   ; Marcamos que ya estamos probando esta jugada
   (assert (simulacion-iniciada (fila ?f) (columna ?c) (nivel ?n)))
   (assert (nodo (nivel ?nuevo-nivel) (padre-nivel ?n) (estado expandiendo)))
)

; Esta regla es la función heurística del agente. Es la forma en la que
; el programa "ve" el tablero y decide si una posición le resulta favorable o no.
; Se dispara con máxima prioridad (salience 100) pero tiene una condición restrictiva clave:
; '(profundidad-maxima ?n)'. Esto significa que solo se ejecuta cuando la simulación 
; ha alcanzado el límite inferior del árbol de búsqueda (el nodo hoja).
;
; DETALLE: en lugar de simplemente contar fichas, esta evaluación
; incorpora conocimiento experto sobre Othello.
; Utiliza 'find-all-facts' y 'length$' para hacer un conteo rápido de las piezas en el tablero.
; Sin embargo, la clave está en el bonus: a las posiciones de las cuatro esquinas (1,1; 1,8; 8,1; 8,8)
; se les otorga un peso alto (+50 puntos). En Othello, una ficha en una esquina es invulnerable 
; y garantiza el control de toda esa zona. 
; El resultado final de esta fórmula (puntos IA - puntos Humano) se guarda en el 'valor-elegido' 
; y el estado del nodo pasa a 'evaluado', marcando el inicio de la fase de retroceso
; donde este valor subirá por las ramas del algoritmo Minimax.
(defrule evaluar-tablero-hoja
   (declare (salience 100))
   (juego (fase simulacion) (nivel ?n))
   (profundidad-maxima ?n) ; Solo evaluamos si estamos en el fondo
   ?nod <- (nodo (nivel ?n) (estado expandiendo))
   =>
   ; Identificamos quién es el agente y quién el humano
   (bind ?color-ia blanca)
   (bind ?color-humano negra)

   ; Calculamos puntuación agente
   (bind ?fichas-ia (length$ (find-all-facts ((?t tablero)) (and (= ?t:nivel ?n) (eq ?t:estado ?color-ia)))))
   ; Bonus esquinas agente (50 puntos extra por cada una)
   (bind ?esquinas-ia (length$ (find-all-facts ((?t tablero)) 
      (and (= ?t:nivel ?n) (eq ?t:estado ?color-ia)
           (or (and (= ?t:fila 1) (= ?t:columna 1)) (and (= ?t:fila 1) (= ?t:columna 8))
               (and (= ?t:fila 8) (= ?t:columna 1)) (and (= ?t:fila 8) (= ?t:columna 8)))))))
   
   ; Calculamos puntuación Humano
   (bind ?fichas-hu (length$ (find-all-facts ((?t tablero)) (and (= ?t:nivel ?n) (eq ?t:estado ?color-humano)))))
   (bind ?esquinas-hu (length$ (find-all-facts ((?t tablero)) 
      (and (= ?t:nivel ?n) (eq ?t:estado ?color-humano)
           (or (and (= ?t:fila 1) (= ?t:columna 1)) (and (= ?t:fila 1) (= ?t:columna 8))
               (and (= ?t:fila 8) (= ?t:columna 1)) (and (= ?t:fila 8) (= ?t:columna 8)))))))

   ; Valor total: (Fichas + Bonus IA) - (Fichas + Bonus Humano)
   (bind ?puntos (+ ?fichas-ia (* ?esquinas-ia 50)))
   (bind ?puntos-rival (+ ?fichas-hu (* ?esquinas-hu 50)))
   (bind ?valor-final (- ?puntos ?puntos-rival))

   ; Actualizamos el nodo: ya está evaluado y tiene un valor
   (modify ?nod (estado evaluado) (valor-elegido ?valor-final))
)

; Esta regla es el núcleo del retroceso en el algoritmo Minimax.
; Se ejecuta con máxima prioridad (salience 100) en el momento en que un nodo "hijo"
; ha terminado de calcular su valor (estado evaluado o finalizado) y necesita
; comunicar ese resultado a su nodo "padre".
;
; DETALLE: 
; 1. Limpieza: antes de actualizar los valores, la regla destruye el nodo hijo y utiliza 
;    'do-for-all-facts' para borrar absolutamente todos los rastros (tableros, turnos, 
;    fases, jugadas) del nivel inferior ('?nh'). Esto es vital para evitar que la memoria 
;    se sature al crear el inmenso árbol de variaciones posibles.
; 2. Lógica Minimax:
;    - Si es el turno del agente (Jugador MAX / blanca): busca maximizar el beneficio, 
;      por lo que compara su valor 'alpha' actual con el valor reportado por el hijo y 
;      se queda con el mayor ('max ?a ?val').
;    - Si es el turno del humano (Jugador MIN / negra): el agente asume que el humano jugará 
;      de forma óptima para perjudicarle, por lo que busca minimizar el valor, actualizando 
;      su límite 'beta' ('min ?b ?val').
(defrule actualizar-padre-desde-hijo
   (declare (salience 100))
   ; Un nodo hijo ha terminado de evaluarse
   ?hijo <- (nodo (nivel ?nh) (padre-nivel ?np) (estado evaluado|finalizado) (valor-elegido ?val))
   ; Tenemos al padre esperando
   ?padre <- (nodo (nivel ?np) (estado expandiendo) (alpha ?a) (beta ?b))
   (turno (jugador ?jug-padre) (nivel ?np))
   =>
   (retract ?hijo)
   
   ; LIMPIEZA: borramos el nivel inferior que ya no necesitamos
   (do-for-all-facts ((?t tablero)) (= ?t:nivel ?nh) (retract ?t))
   (do-for-all-facts ((?p posible-jugada)) (= ?p:nivel ?nh) (retract ?p))
   (do-for-all-facts ((?s simulacion-iniciada)) (= ?s:nivel ?nh) (retract ?s))
   (do-for-all-facts ((?j juego)) (= ?j:nivel ?nh) (retract ?j))
   (do-for-all-facts ((?t turno)) (= ?t:nivel ?nh) (retract ?t))
   
   (if (eq ?jug-padre blanca) ; Si el padre es el agente (MAX)
    then
       (bind ?nuevo-alpha (max ?a ?val))
       (modify ?padre (alpha ?nuevo-alpha) (valor-elegido ?nuevo-alpha))
    else ; Si el padre es el humano (MIN)
       (bind ?nuevo-beta (min ?b ?val))
       (modify ?padre (beta ?nuevo-beta) (valor-elegido ?nuevo-beta))
   )
)

; Se ejecuta con la prioridad absoluta más alta del sistema (salience 110).
; Su función es monitorizar constantemente los límites 'alpha' (el valor mínimo asegurado para el agente) 
; y 'beta' (el valor máximo permitido por el humano) en el nodo que se está evaluando.
;
; DETALLE: la condición de disparo '(test (>= ?a ?b))' indica que se ha encontrado una refutación.
; Esto significa matemáticamente que el jugador del nivel superior ya tiene garantizada 
; una opción mejor por otra rama del árbol, por lo que el oponente (asumiendo que juega perfecto) 
; nunca le permitiría alcanzar este estado actual. 
; 
; Al cumplirse esta condición, calcular las 'posibles-jugadas' que quedan en este nodo es 
; un desperdicio de recursos. La regla interrumpe la exploración, elimina de la memoria los tableros y las jugadas sobrantes de este nivel 
; para liberar memoria, y fuerza el retroceso modificando la fase del juego para volver 
; al nivel del padre ('- ?n 1').
(defrule poda-alpha-beta
   (declare (salience 110)) ; Prioridad máxima para ahorrar tiempo
   ?fase <- (juego (fase simulacion) (nivel ?n))
   (nodo (nivel ?n) (alpha ?a) (beta ?b))
   (test (>= ?a ?b)) ; Condición de poda: Alpha >= Beta
   =>
   ; Borramos todo lo relacionado con este nivel y volvemos al nivel anterior
   (do-for-all-facts ((?t tablero)) (= ?t:nivel ?n) (retract ?t))
   (do-for-all-facts ((?p posible-jugada)) (= ?p:nivel ?n) (retract ?p))
   (modify ?fase (nivel (- ?n 1)))
)

; Esta regla actúa como el mecanismo de cierre para un nodo en el árbol Minimax.
; Gracias a su baja prioridad '(declare (salience -10))', el motor espera
; a que la regla 'clonar-nivel-para-simulacion' haya procesado todas las opciones disponibles.
;
; DETALLE: doble negación lógica: '(not (and (posible-jugada ...) (not (simulacion-iniciada ...))))'.
; Es decir, ¿es cierto que NO queda ninguna jugada que NO haya sido probada?. Verifica que todas y cada una 
; de las 'posibles-jugadas' de este nivel ya tienen su correspondiente marca de 'simulacion-iniciada'.
; Cuando esto ocurre, la regla modifica el estado del nodo a 'finalizado'. 
; Este cambio de estado es la señal que estaba esperando la regla 'actualizar-padre-desde-hijo' 
; para tomar el valor definitivo (el alpha o beta final de este subárbol) y propagarlo al nivel superior.
(defrule finalizar-exploracion-nodo
   (declare (salience -10)) ; Solo cuando no queden más jugadas por clonar
   ?nod <- (nodo (nivel ?n) (estado expandiendo))
   ; Si NO existe una jugada que NO haya sido probada... entonces hemos terminado
   (not (and (posible-jugada (fila ?f) (columna ?c) (nivel ?n))
             (not (simulacion-iniciada (fila ?f) (columna ?c) (nivel ?n)))))
   =>
   (modify ?nod (estado finalizado))
)

; Su objetivo es recordar qué coordenadas exactas producen el mejor resultado,
; ya que el nodo raíz (nivel 0) por sí solo solo guarda la puntuación (alpha), no el movimiento.
;
; DETALLE: tiene una prioridad altísima '(declare (salience 150))'. Debe ejecutarse ANTES que la regla 'actualizar-padre-desde-hijo' (que tiene salience 100). 
; Si se ejecutara después, la limpieza destruiría el nodo hijo y el hecho 
; 'simulacion-iniciada' antes de que la IA pudiera extraer la fila ('?f') y columna ('?c') 
; que originaron ese tablero. Al detectar que el hijo aporta un valor mayor que el 'alpha' 
; actual del padre ('test (> ?val ?a)'), el sistema genera un hecho 'mejor-movida-encontrada' 
; que servirá para ejecutar la jugada real cuando el árbol termine de procesarse.
(defrule registrar-mejor-movimiento-ia
   (declare (salience 150))
   ?padre <- (nodo (nivel 0) (estado expandiendo) (alpha ?a))
   ?hijo <- (nodo (nivel 1) (padre-nivel 0) (estado evaluado|finalizado) (valor-elegido ?val))
   (simulacion-iniciada (fila ?f) (columna ?c) (nivel 0)) ; Buscamos qué coordenadas eran
   (test (> ?val ?a)) ; Si este hijo es mejor que lo que teníamos
   =>
   (assert (mejor-movida-encontrada ?f ?c ?val))
)

; Esta regla marca el momento exacto en el que el agente deja de pensar y actúa en el tablero real.
; Se activa cuando el nodo raíz (nivel 0) cambia su estado a 'finalizado', lo que significa 
; que todo el árbol Minimax ha sido explorado, podado y resuelto por completo.
;
; DETALLE: el patrón '(not (mejor-movida-encontrada ? ? ?v2&:(> ?v2 ?v)))' encuentra el máximo absoluto dentro de una base de hechos. Busca un hecho 
; 'mejor-movida-encontrada', y simultáneamente verifica que NO exista ningún otro con un valor superior.
; Una vez identificadas las coordenadas definitivas, la regla realiza una limpieza general final, 
; borrando cualquier rastro residual del universo simulado (niveles > 0). Finalmente, introduce la 
; decisión en el motor de juego real afirmando un 'intento-movimiento' en el nivel 0 y cambiando 
; la fase a 'validacion'. A partir de este instante, las mismas reglas que aplican 
; al humano validarán y ejecutarán el movimiento de la máquina.
(defrule finalizar-ia-y-ejecutar-real
   ?f <- (juego (fase simulacion) (nivel 0))
   (nodo (nivel 0) (estado finalizado))
   ?mejor <- (mejor-movida-encontrada ?f-real ?c-real ?v)
   (not (mejor-movida-encontrada ? ? ?v2&:(> ?v2 ?v))) ; Es la mejor de las mejores
   (turno (jugador ?p) (nivel 0))
   =>
   (printout t "IA decide mover a " ?f-real "," ?c-real " con valor esperado " ?v crlf)
   
   (do-for-all-facts ((?t tablero)) (> ?t:nivel 0) (retract ?t))
   (do-for-all-facts ((?n nodo)) (> ?n:nivel 0) (retract ?n))
   
   ; VOLVEMOS AL JUEGO REAL
   (retract ?f ?mejor)
   (assert (intento-movimiento (color ?p) (fila ?f-real) (columna ?c-real) (nivel 0)))
   (assert (juego (fase validacion) (nivel 0)))
)

; -----------------------------------------
; 4.6. FIN DE PARTIDA
; -----------------------------------------

; Esta regla representa el desenlace de la partida.
; Se activa exclusivamente cuando el estado del juego pasa a la fase 'fin-juego' 
; en el nivel real (nivel 0), lo que ocurre cuando ninguno de los dos jugadores 
; tiene movimientos legales disponibles en el tablero.
;
; DETALLE: para realizar el conteo de forma directa y limpia, la regla prescinde de iteradores o bucles. 
; En su lugar, se utiliza 'find-all-facts' 
; para extraer listas con todas las casillas del nivel 0 ocupadas por cada color, y 'length$' 
; para contar los elementos de dichas listas de manera instantánea. 
; Tras imprimir el balance final por consola y evaluar al ganador (o empate), 
; se ejecuta el comando '(halt)'. Esta instrucción detiene el motor de inferencia, 
; vaciando la agenda de reglas y dando por concluida la ejecución del programa.
(defrule determinar-ganador
   (juego (fase fin-juego) (nivel 0))
   =>
   ; Guardar todos los hechos que coinciden en una lista y medir su longitud
   (bind ?n (length$ (find-all-facts ((?t tablero)) (and (= ?t:nivel 0) (eq ?t:estado negra)))))
   (bind ?b (length$ (find-all-facts ((?t tablero)) (and (= ?t:nivel 0) (eq ?t:estado blanca)))))
   
   (printout t crlf "--- RECUENTO FINAL ---" crlf)
   (printout t "Fichas NEGRAS: " ?n crlf)
   (printout t "Fichas BLANCAS: " ?b crlf)
   
   (if (> ?n ?b) then
       (printout t "¡GANAN LAS NEGRAS!" crlf)
   else (if (> ?b ?n) then
       (printout t "¡GANAN LAS BLANCAS!" crlf)
   else
       (printout t "¡EMPATE!" crlf)))
   
   (printout t "----------------------" crlf)
   (halt)
)