; =========================================
; 1. TEMPLATES (Estructuras de datos)
; =========================================

(deftemplate tablero
    (slot fila (type INTEGER))
    (slot columna (type INTEGER))
    (slot estado (type SYMBOL) (allowed-values vacia negra blanca))
)

(deftemplate configuracion
    (slot tamano (type INTEGER) (default 8))
)

(deftemplate turno
    (slot jugador (type SYMBOL) (allowed-values negra blanca))
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
)

(deftemplate juego
    (slot fase (allowed-values inicializacion analisis peticion validacion ejecucion cambio-turno fin-juego))
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
)

(deftemplate rastreo
   (slot f (type INTEGER))
   (slot c (type INTEGER))
   (slot df (type INTEGER))
   (slot dc (type INTEGER))
)

; =========================================
; 2. FACTS (Hechos iniciales)
; =========================================

(deffacts estado-inicial
    (configuracion (tamano 8))
    (turno (jugador negra))
    (jugador (color negra) (tipo humano) (cantidad_fichas 30))
    (jugador (color blanca) (tipo humano) (cantidad_fichas 30))
    (juego (fase inicializacion)) ; Arrancamos en inicialización
    (pases-consecutivos 0)
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
                (and (= ?casilla:fila ?f) (= ?casilla:columna ?c))
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
   (bind ?c1 (/ ?n 2))
   (bind ?c2 (+ (/ ?n 2) 1)) 

   (loop-for-count (?f 1 ?n)
      (loop-for-count (?c 1 ?n)
         (if (or (and (= ?f ?c1) (= ?c ?c1)) (and (= ?f ?c2) (= ?c ?c2))) then
            (assert (tablero (fila ?f) (columna ?c) (estado blanca)))
         else (if (or (and (= ?f ?c1) (= ?c ?c2)) (and (= ?f ?c2) (= ?c ?c1))) then
            (assert (tablero (fila ?f) (columna ?c) (estado negra)))
         else
            (assert (tablero (fila ?f) (columna ?c) (estado vacia))))
         )
      )
   )
   (printout t "TABLERO " ?n "x" ?n " INICIALIZADO" crlf)
   (mostrar-tablero ?n)
   (retract ?fase)
   (assert (juego (fase analisis)))
)

(defrule pedir-movimiento-humano
    ?fase <- (juego (fase peticion))
    (configuracion (tamano ?n)) ; <--- Añadimos esto para saber el límite
    (turno (jugador ?color-actual))
    (jugador (color ?color-actual) (tipo humano))
    (not (intento-movimiento))
    =>
    (printout t "Turno de " ?color-actual ". Fila (1-" ?n "): ") ; <--- Usamos ?n
    (bind ?f (integer (read))) 
    (printout t "Columna (1-" ?n "): ") ; <--- Usamos ?n
    (bind ?c (integer (read)))
    
    (assert (intento-movimiento (color ?color-actual) (fila ?f) (columna ?c)))
    
    (retract ?fase)
    (assert (juego (fase validacion))) 
)

; 1. COLOCAR: Pone la ficha y marca el inicio del volteo
(defrule colocar-ficha-actual
   (declare (salience 10)) ; Mayor prioridad para asegurar que la ficha existe
   ?fase <- (juego (fase ejecucion))
   ?i <- (intento-movimiento (color ?color) (fila ?f) (columna ?c))
   ?casilla <- (tablero (fila ?f) (columna ?c) (estado vacia))
   ?jug <- (jugador (color ?color) (cantidad_fichas ?can))
   =>
   (retract ?i)
   (modify ?casilla (estado ?color))
   (modify ?jug (cantidad_fichas (- ?can 1)))
   (printout t "Ficha " ?color " colocada en " ?f "," ?c crlf)
)

; 2. VOLTEAR: Reacción en cadena (Efecto Dominó)
; Esta regla se dispara para cada dirección confirmada y va saltando ficha a ficha
(defrule aplicar-volteo
   (juego (fase ejecucion))
   (captura-confirmada (fila-orig ?fo) (col-orig ?co) 
                       (fila-fin ?ff) (col-fin ?cf) 
                       (df ?df) (dc ?dc) (color ?p))
   
   ; Buscamos fichas del rival en el tablero
   ?t <- (tablero (fila ?fr) (columna ?cr) (estado ~vacia&~?p))
   
   ; TEST GEOMÉTRICO: ¿Está la ficha rival en la línea y entre los dos extremos?
   (test (and
      ; 1. ¿Está alineada con el movimiento? (Producto cruzado = 0)
      (= (* (- ?fr ?fo) ?dc) (* (- ?cr ?co) ?df))
      ; 2. ¿Está en la dirección correcta?
      (>= (* (- ?fr ?fo) ?df) 0)
      (>= (* (- ?cr ?co) ?dc) 0)
      ; 3. ¿Está antes de llegar a la ficha que cierra el sándwich?
      (or (< (abs (- ?fr ?fo)) (abs (- ?ff ?fo)))
          (< (abs (- ?cr ?co)) (abs (- ?cf ?co))))
   ))
   =>
   (modify ?t (estado ?p))
   (printout t "Ficha capturada en [" ?fr "," ?cr "]" crlf)
)

(defrule error-casilla-ocupada
    (declare (salience 20))
    ?fase <- (juego (fase validacion))
    ?i <- (intento-movimiento (fila ?f) (columna ?c))
    (tablero (fila ?f) (columna ?c) (estado ?estado&~vacia))
    =>
    (retract ?i ?fase)
    (printout t "ERROR: Casilla ocupada por " ?estado ". Intenta de nuevo." crlf)
    (assert (juego (fase peticion)))
) 

(defrule error-coordenadas-invalidas
    (declare (salience 20))
    ?fase <- (juego (fase validacion))
    ?i <- (intento-movimiento (fila ?f) (columna ?c))
    (not (tablero (fila ?f) (columna ?c)))
    =>
    (retract ?i ?fase)
    (printout t "ERROR: Las coordenadas " ?f "," ?c " no existen en el tablero." crlf)
    (assert (juego (fase peticion)))
)

(defrule realizar-cambio-turno
    ?fase <- (juego (fase cambio-turno))
    ?t <- (turno (jugador ?color))
    (configuracion (tamano ?n))
    =>
    (retract ?t ?fase)
    (if (eq ?color negra) 
        then (assert (turno (jugador blanca)))
        else (assert (turno (jugador negra)))
    )
    (mostrar-tablero ?n)
    (assert (juego (fase analisis))) 
)

; 1. Si el vecino en una dirección es del rival, lanzamos un rastreador
(defrule iniciar-rastreo
   (juego (fase validacion))
   (intento-movimiento (color ?propio) (fila ?f) (columna ?c))
   (direccion (df ?df) (dc ?dc))
   ; El vecino inmediato debe ser del rival
   (tablero (fila =(+ ?f ?df)) (columna =(+ ?c ?dc)) (estado ?rival&~vacia&~?propio))
   =>
   (assert (rastreo (f (+ ?f (* 2 ?df))) (c (+ ?c (* 2 ?dc))) (df ?df) (dc ?dc)))
)

; 2. El rastreador avanza mientras encuentre fichas del rival
(defrule propagar-rastreo
   (juego (fase validacion))
   ?r <- (rastreo (f ?f) (c ?c) (df ?df) (dc ?dc))
   (intento-movimiento (color ?propio))
   (tablero (fila ?f) (columna ?c) (estado ?rival&~vacia&~?propio))
   =>
   (modify ?r (f (+ ?f ?df)) (c (+ ?c ?dc)))
)

; 3. Si el rastreador encuentra una ficha propia, ¡sándwich confirmado! 
(defrule confirmar-captura
   (juego (fase validacion))
   ?r <- (rastreo (f ?f_fin) (c ?c_fin) (df ?df) (dc ?dc))
   (intento-movimiento (color ?propio) (fila ?f_orig) (columna ?c_orig))
   (tablero (fila ?f_fin) (columna ?c_fin) (estado ?propio))
   =>
   (retract ?r)
   (assert (captura-confirmada (fila-orig ?f_orig) (col-orig ?c_orig) 
                               (fila-fin ?f_fin) (col-fin ?c_fin)
                               (df ?df) (dc ?dc) (color ?propio)))
)

; 4. Si el rastreador se sale del tablero o encuentra un hueco, se borra
(defrule limpiar-rastreo-fallido
   (declare (salience -5))
   (juego (fase validacion))
   ?r <- (rastreo (f ?f) (c ?c))
   (or (not (tablero (fila ?f) (columna ?c)))
       (tablero (fila ?f) (columna ?c) (estado vacia)))
   =>
   (retract ?r)
)

(defrule error-movimiento-ilegal
    (declare (salience -20)) ; Se ejecuta al final de la validacion
    ?fase <- (juego (fase validacion))
    ?i <- (intento-movimiento (fila ?f) (columna ?c))
    (not (captura-confirmada))
    =>
    (retract ?fase ?i)
    (printout t "ERROR: Movimiento ilegal. Debe capturar al menos una ficha rival." crlf)
    (assert (juego (fase peticion)))
)

(defrule validar-exito-y-ejecutar
   (declare (salience -10))
   ?fase <- (juego (fase validacion))
   (captura-confirmada) ; Existe al menos una dirección válida
   =>
   (retract ?fase)
   (assert (juego (fase ejecucion)))
)

; 3. FINALIZAR: Limpia las direcciones y cambia el turno
(defrule finalizar-fase-ejecucion
   (declare (salience -10))
   ?fase <- (juego (fase ejecucion))
   (not (intento-movimiento))
   =>
   (retract ?fase)
   (do-for-all-facts ((?c captura-confirmada)) TRUE (retract ?c))
   (assert (juego (fase cambio-turno)))
)

; PASAR TURNO Y FIN DE JUEGO
; 1. Lanza rastreadores desde todas las casillas vacías hacia los rivales
(defrule iniciar-analisis
   (juego (fase analisis))
   (turno (jugador ?p))
   (tablero (fila ?f) (columna ?c) (estado vacia))
   (direccion (df ?df) (dc ?dc))
   (tablero (fila =(+ ?f ?df)) (columna =(+ ?c ?dc)) (estado ?r&~vacia&~?p))
   =>
   (assert (rastreo-analisis (+ ?f (* 2 ?df)) (+ ?c (* 2 ?dc)) ?df ?dc))
)

; 2. El rastreador avanza por la línea de rivales
(defrule propagar-analisis
   (juego (fase analisis))
   ?rastreo <- (rastreo-analisis ?f ?c ?df ?dc)
   (turno (jugador ?p))
   (tablero (fila ?f) (columna ?c) (estado ?r&~vacia&~?p))
   =>
   (retract ?rastreo)
   (assert (rastreo-analisis (+ ?f ?df) (+ ?c ?dc) ?df ?dc))
)

; 3. Si llega a una ficha propia, hay movimiento posible
(defrule exito-analisis
   (juego (fase analisis))
   ?rastreo <- (rastreo-analisis ?f ?c ?df ?dc)
   (turno (jugador ?p))
   (tablero (fila ?f) (columna ?c) (estado ?p))
   =>
   (retract ?rastreo)
   (assert (puede-mover))
)

; 4. Limpiar los rastreadores que se salen del tablero o caen en vacío
(defrule limpiar-analisis
   (declare (salience -5))
   (juego (fase analisis))
   ?rastreo <- (rastreo-analisis ?f ?c ?df ?dc)
   (or (not (tablero (fila ?f) (columna ?c)))
       (tablero (fila ?f) (columna ?c) (estado vacia)))
   =>
   (retract ?rastreo)
)

; 5A. RESOLUCIÓN: Si hay movimiento, pedir coordenadas y resetear pases
(defrule analisis-con-movimientos
   (declare (salience -10))
   ?fase <- (juego (fase analisis))
   ?m <- (puede-mover)
   ?p <- (pases-consecutivos ?n)
   =>
   (retract ?fase ?m ?p)
   (assert (pases-consecutivos 0))
   (assert (juego (fase peticion)))
)

; 5B. RESOLUCIÓN: Si no hay movimiento, pasar turno o acabar
(defrule analisis-sin-movimientos
   (declare (salience -10))
   ?fase <- (juego (fase analisis))
   (not (puede-mover))
   ?p <- (pases-consecutivos ?n)
   (turno (jugador ?color))
   =>
   (retract ?fase ?p)
   (if (= ?n 1) then
       (printout t "FIN DEL JUEGO: Ningun jugador tiene movimientos validos." crlf)
       (assert (juego (fase fin-juego)))
   else
       (printout t "AVISO: " ?color " no tiene movimientos. Pasa turno." crlf)
       (assert (pases-consecutivos 1))
       (assert (juego (fase cambio-turno)))
   )
)

; QUEDARSE SIN FICHAS
(defrule ceder-ficha
    (declare (salience 50)) ; Prioridad alta para que ocurra antes de leer el teclado
    (juego (fase peticion))
    (turno (jugador ?color))
    ?j-actual <- (jugador (color ?color) (cantidad_fichas 0))
    ?j-rival <- (jugador (color ~?color) (cantidad_fichas ?c-rival&:(> ?c-rival 0)))
    =>
    (modify ?j-actual (cantidad_fichas 1))
    (modify ?j-rival (cantidad_fichas (- ?c-rival 1)))
    (printout t "AVISO: " ?color " no tiene fichas en mano. El rival le cede una." crlf)
)

; DETERMINAR GANADOR
(defrule determinar-ganador
   (juego (fase fin-juego))
   =>
   ; Guardar todos los hechos que coinciden en una lista y medir su longitud
   (bind ?n (length$ (find-all-facts ((?t tablero)) (eq ?t:estado negra))))
   (bind ?b (length$ (find-all-facts ((?t tablero)) (eq ?t:estado blanca))))
   
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
