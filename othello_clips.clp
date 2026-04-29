; =========================================
; 1. TEMPLATES (Estructuras de datos)
; =========================================

(deftemplate tablero
    (slot fila (type INTEGER))
    (slot columna (type INTEGER))
    (slot estado (type SYMBOL) (allowed-values vacia negra blanca))
    (slot nivel (type INTEGER) (default 0))
)

(deftemplate configuracion
    (slot tamano (type INTEGER) (default 8))
)

(deftemplate turno
    (slot jugador (type SYMBOL) (allowed-values negra blanca))
    (slot nivel (type INTEGER) (default 0))
)

(deftemplate jugador
    (slot color (type SYMBOL) (allowed-values negra blanca))
    (slot tipo (type SYMBOL) (allowed-values humano maquina))
    (slot cantidad_fichas (type INTEGER))
)

(deftemplate intento-movimiento
    (slot color (type SYMBOL))
    (slot fila (type INTEGER))
    (slot columna (type INTEGER))
    (slot nivel (type INTEGER) (default 0))
)

(deftemplate juego
    (slot fase (allowed-values inicializacion analisis peticion validacion ejecucion cambio-turno fin-juego simulacion))
    (slot nivel (type INTEGER) (default 0))
)

(deftemplate direccion
    (slot df (type INTEGER)) ; Desplazamiento de fila (-1, 0, 1)
    (slot dc (type INTEGER)) ; Desplazamiento de columna (-1, 0, 1)
)

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

(deftemplate rastreo
   (slot f (type INTEGER))
   (slot c (type INTEGER))
   (slot df (type INTEGER))
   (slot dc (type INTEGER))
   (slot orig-f (type INTEGER)) ; Casilla vacía donde empezó el rastreo
   (slot orig-c (type INTEGER))
   (slot nivel (type INTEGER) (default 0))
)

(deftemplate posible-jugada
   (slot fila)
   (slot columna)
   (slot puntuacion (default 0))
   (slot nivel (type INTEGER) (default 0))
)

(deftemplate nodo
   (slot nivel (type INTEGER))           ; Profundidad actual
   (slot padre-nivel (type INTEGER))     ; Referencia al nivel anterior
   (slot alpha (type NUMBER) (default -10000)) ; El mejor valor para MAX
   (slot beta (type NUMBER) (default 10000))   ; El mejor valor para MIN
   (slot estado (allowed-values expandiendo evaluado finalizado))
   (slot valor-elegido (type NUMBER))    ; El valor que subirá al padre
)

(deftemplate simulacion-iniciada
    (slot fila (type INTEGER))
    (slot columna (type INTEGER))
    (slot nivel (type INTEGER) (default 0))
)

; =========================================
; 2. FACTS (Hechos iniciales)
; =========================================

(deffacts estado-inicial
    (configuracion (tamano 8))
    (turno (jugador negra))
    (jugador (color negra) (tipo humano) (cantidad_fichas 30))
    (jugador (color blanca) (tipo maquina) (cantidad_fichas 30))
    (juego (fase inicializacion)) ; Arrancamos en inicialización
    (pases-consecutivos 0)
    (profundidad-maxima 3)
)

(deffacts vectores-direccion
    (direccion (df -1) (dc -1)) (direccion (df -1) (dc  0)) (direccion (df -1) (dc  1))
    (direccion (df  0) (dc -1))                            (direccion (df  0) (dc  1))
    (direccion (df  1) (dc -1)) (direccion (df  1) (dc  0)) (direccion (df  1) (dc  1))
)

; =========================================
; 3. FUNCIONES
; =========================================

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

; Genera el tablero y pasa a pedir el movimiento
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
         (assert (tablero (fila ?f) (columna ?c) (estado ?estado) (nivel 0))) ; <--- NIVEL 0
      )
   )
   (retract ?fase)
   (assert (juego (fase analisis) (nivel 0)))
   (printout t "TABLERO INICIALIZADO" crlf)
   (mostrar-tablero ?n)
)

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

; 1. COLOCAR: Pone la ficha y marca el inicio del volteo
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
; Esta regla se dispara para cada dirección confirmada y va saltando ficha a ficha
(defrule aplicar-volteo
   (juego (fase ejecucion) (nivel ?n)) ; <--- Añadido ?n
   (captura-confirmada (fila-orig ?fo) (col-orig ?co) 
                       (fila-fin ?ff) (col-fin ?cf) 
                       (df ?df) (dc ?dc) (color ?p) (nivel ?n)) ; <--- Añadido ?n
   
   ; Buscamos fichas del rival en el tablero
   ?t <- (tablero (fila ?fr) (columna ?cr) (estado ~vacia&~?p) (nivel ?n)) ; <--- Añadido ?n
   
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
   (if (= ?n 0) then (printout t "Ficha capturada en [" ?fr "," ?cr "]" crlf)) ; Silencio en simulación
)

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
        (mostrar-tablero ?tam) ; <--- Mostramos aquí para que el jugador vea el estado actual
    )
    ; SOLO borramos las posibles jugadas del nivel actual
    (do-for-all-facts ((?j posible-jugada)) (= ?j:nivel ?n) (retract ?j))
    (assert (juego (fase analisis) (nivel ?n)))
)

; 1. Si el vecino en una dirección es del rival, lanzamos un rastreador
(defrule iniciar-rastreo
   (juego (fase validacion) (nivel ?n)) 
   (intento-movimiento (color ?propio) (fila ?f) (columna ?c) (nivel ?n))
   (direccion (df ?df) (dc ?dc))
   (tablero (fila =(+ ?f ?df)) (columna =(+ ?c ?dc)) (estado ?rival&~vacia&~?propio) (nivel ?n))
   =>
   (assert (rastreo (f (+ ?f (* 2 ?df))) (c (+ ?c (* 2 ?dc))) (df ?df) (dc ?dc) (orig-f ?f) (orig-c ?c) (nivel ?n)))
)

; 2. El rastreador avanza mientras encuentre fichas del rival
(defrule propagar-rastreo
   (juego (fase validacion) (nivel ?n))
   ?r <- (rastreo (f ?f) (c ?c) (df ?df) (dc ?dc) (nivel ?n))
   (intento-movimiento (color ?propio) (nivel ?n))
   (tablero (fila ?f) (columna ?c) (estado ?rival&~vacia&~?propio) (nivel ?n))
   =>
   (modify ?r (f (+ ?f ?df)) (c (+ ?c ?dc)))
)

; 3. Si el rastreador encuentra una ficha propia, ¡sándwich confirmado! 
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

; 4. Si el rastreador se sale del tablero o encuentra un hueco, se borra
(defrule limpiar-rastreo-fallido
   (declare (salience -5))
   (juego (fase validacion) (nivel ?n))
   ?r <- (rastreo (f ?f) (c ?c) (nivel ?n))
   (or (not (tablero (fila ?f) (columna ?c) (nivel ?n)))
       (tablero (fila ?f) (columna ?c) (estado vacia) (nivel ?n)))
   =>
   (retract ?r)
)

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

(defrule validar-exito-y-ejecutar
   (declare (salience -10))
   ?fase <- (juego (fase validacion) (nivel ?n))
   (captura-confirmada (nivel ?n)) ; Existe al menos una dirección válida
   =>
   (retract ?fase)
   (assert (juego (fase ejecucion) (nivel ?n)))
)

; 3. FINALIZAR: Limpia las direcciones y cambia el turno
(defrule finalizar-fase-ejecucion
   (declare (salience -10))
   ?fase <- (juego (fase ejecucion) (nivel ?n))
   (not (intento-movimiento (nivel ?n)))
   =>
   (retract ?fase)
   (do-for-all-facts ((?c captura-confirmada)) (= ?c:nivel ?n) (retract ?c))
   (assert (juego (fase cambio-turno) (nivel ?n)))
)

; 1. Lanza rastreadores desde todas las casillas vacías hacia los rivales
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

; 2. El rastreador avanza por la línea de rivales
(defrule propagar-analisis
   (juego (fase analisis) (nivel ?n))
   ?rastreo <- (rastreo (f ?f) (c ?c) (df ?df) (dc ?dc) (nivel ?n)) ; AJUSTE: Slots
   (turno (jugador ?p) (nivel ?n))
   (tablero (fila ?f) (columna ?c) (estado ~vacia&~?p) (nivel ?n))
   =>
   ; AJUSTE: Usamos modify para avanzar slots
   (modify ?rastreo (f (+ ?f ?df)) (c (+ ?c ?dc)))
)

; 3. Si llega a una ficha propia, hay movimiento posible
(defrule exito-analisis
   (juego (fase analisis) (nivel ?n))
   ?rastreo <- (rastreo (orig-f ?f) (orig-c ?c) (f ?rf) (c ?rc) (nivel ?n))
   (turno (jugador ?p) (nivel ?n))
   (tablero (fila ?rf) (columna ?rc) (estado ?p) (nivel ?n))
   =>
   (retract ?rastreo)
   ; Si no existía ya esta jugada posible, la creamos
   (assert (posible-jugada (fila ?f) (columna ?c) (nivel ?n)))
)

; 4. Limpiar los rastreadores que se salen del tablero o caen en vacío
(defrule limpiar-analisis
   (declare (salience -5))
   (juego (fase analisis) (nivel ?n))
   ?rastreo <- (rastreo (f ?f) (c ?c) (nivel ?n)) ; AJUSTE: Slots
   (or (not (tablero (fila ?f) (columna ?c) (nivel ?n)))
       (tablero (fila ?f) (columna ?c) (estado vacia) (nivel ?n)))
   =>
   (retract ?rastreo)
)

; --- RESOLUCIÓN PARA EL JUEGO REAL (Nivel 0) ---

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

(defrule analisis-con-movimientos-sim
   (declare (salience -10))
   ?fase <- (juego (fase analisis) (nivel ?n&:(> ?n 0)))
   (exists (posible-jugada (nivel ?n)))
   =>
   (retract ?fase)
   (do-for-all-facts ((?r rastreo)) (= ?r:nivel ?n) (retract ?r))
   (assert (juego (fase simulacion) (nivel ?n)))
)

(defrule evaluar-tablero-sin-movimientos-sim
   (declare (salience 100))
   ?fase <- (juego (fase analisis) (nivel ?n&:(> ?n 0)))
   (not (posible-jugada (nivel ?n)))
   ?nod <- (nodo (nivel ?n) (estado expandiendo))
   =>
   (retract ?fase)
   ; Si no hay movimientos posibles en este futuro imaginario, se puntúa inmediatamente y se retrocede
   (bind ?f-ia (length$ (find-all-facts ((?t tablero)) (and (= ?t:nivel ?n) (eq ?t:estado blanca)))))
   (bind ?f-hu (length$ (find-all-facts ((?t tablero)) (and (= ?t:nivel ?n) (eq ?t:estado negra)))))
   (modify ?nod (estado evaluado) (valor-elegido (- ?f-ia ?f-hu)))
)

; QUEDARSE SIN FICHAS
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

; DETERMINAR GANADOR
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

; INICIO ALPHA-BETA
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
   
   ; Mantenemos el turno original, inyectamos el movimiento y lanzamos la validación del motor
   (assert (turno (jugador ?color-actual) (nivel ?nuevo-nivel)))
   (assert (intento-movimiento (color ?color-actual) (fila ?f) (columna ?c) (nivel ?nuevo-nivel)))
   (assert (juego (fase validacion) (nivel ?nuevo-nivel)))
   
   ; Marcamos que ya estamos probando esta jugada
   (assert (simulacion-iniciada (fila ?f) (columna ?c) (nivel ?n)))
   (assert (nodo (nivel ?nuevo-nivel) (padre-nivel ?n) (estado expandiendo)))
)

(defrule evaluar-tablero-hoja
   (declare (salience 100))
   (juego (fase simulacion) (nivel ?n))
   (profundidad-maxima ?n) ; Solo evaluamos si estamos en el fondo
   ?nod <- (nodo (nivel ?n) (estado expandiendo))
   =>
   ; Identificamos quién es la IA y quién el humano (suponiendo IA es blanca)
   (bind ?color-ia blanca)
   (bind ?color-humano negra)

   ; Calculamos puntuación IA
   (bind ?fichas-ia (length$ (find-all-facts ((?t tablero)) (and (= ?t:nivel ?n) (eq ?t:estado ?color-ia)))))
   ; Bonus esquinas IA (50 puntos extra por cada una)
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

(defrule actualizar-padre-desde-hijo
   (declare (salience 100))
   ; Un nodo hijo ha terminado de evaluarse
   ?hijo <- (nodo (nivel ?nh) (padre-nivel ?np) (estado evaluado|finalizado) (valor-elegido ?val))
   ; Tenemos al padre esperando
   ?padre <- (nodo (nivel ?np) (estado expandiendo) (alpha ?a) (beta ?b))
   (turno (jugador ?jug-padre) (nivel ?np))
   =>
   (retract ?hijo)
   
   ; LIMPIEZA PROFUNDA: Borramos el nivel inferior que ya no necesitamos
   (do-for-all-facts ((?t tablero)) (= ?t:nivel ?nh) (retract ?t))
   (do-for-all-facts ((?p posible-jugada)) (= ?p:nivel ?nh) (retract ?p))
   (do-for-all-facts ((?s simulacion-iniciada)) (= ?s:nivel ?nh) (retract ?s))
   (do-for-all-facts ((?j juego)) (= ?j:nivel ?nh) (retract ?j))
   (do-for-all-facts ((?t turno)) (= ?t:nivel ?nh) (retract ?t))
   
   (if (eq ?jug-padre blanca) ; Si el padre es la IA (MAX)
    then
       (bind ?nuevo-alpha (max ?a ?val))
       (modify ?padre (alpha ?nuevo-alpha) (valor-elegido ?nuevo-alpha))
    else ; Si el padre es el HUMANO (MIN)
       (bind ?nuevo-beta (min ?b ?val))
       (modify ?padre (beta ?nuevo-beta) (valor-elegido ?nuevo-beta))
   )
)

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

(defrule finalizar-exploracion-nodo
   (declare (salience -10)) ; Solo cuando no queden más jugadas por clonar
   ?nod <- (nodo (nivel ?n) (estado expandiendo))
   ; Si NO existe una jugada que NO haya sido probada... entonces hemos terminado
   (not (and (posible-jugada (fila ?f) (columna ?c) (nivel ?n))
             (not (simulacion-iniciada (fila ?f) (columna ?c) (nivel ?n)))))
   =>
   (modify ?nod (estado finalizado))
)

(defrule registrar-mejor-movimiento-ia
   (declare (salience 150))
   ?padre <- (nodo (nivel 0) (estado expandiendo) (alpha ?a))
   ?hijo <- (nodo (nivel 1) (padre-nivel 0) (estado evaluado|finalizado) (valor-elegido ?val))
   (simulacion-iniciada (fila ?f) (columna ?c) (nivel 0)) ; Buscamos qué coordenadas eran
   (test (> ?val ?a)) ; Si este hijo es mejor que lo que teníamos
   =>
   (assert (mejor-movida-encontrada ?f ?c ?val))
)

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