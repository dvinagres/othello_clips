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
    (slot fase (allowed-values inicializacion peticion validacion ejecucion cambio-turno))
)

; =========================================
; 2. FACTS (Hechos iniciales)
; =========================================

(deffacts estado-inicial
    (configuracion (tamano 8))
    (turno (jugador negra))
    (jugador (color negra) (tipo humano) (cantidad_fichas 2))
    (jugador (color blanca) (tipo humano) (cantidad_fichas 2))
    (juego (fase inicializacion)) ; Arrancamos en inicialización
)

; =========================================
; 3. FUNCIONES
; =========================================

(deffunction mostrar-tablero (?tamano)
    (printout t crlf "   | ")
    (loop-for-count (?c 1 ?tamano)
        (printout t ?c " | ")
    )
    (printout t crlf "---------------------------------------" crlf)
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
        (printout t crlf "---------------------------------------" crlf)
    )
    (printout t crlf)
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
   (assert (juego (fase peticion)))
)

(defrule pedir-movimiento-humano
    ?fase <- (juego (fase peticion))
    (turno (jugador ?color-actual))
    (jugador (color ?color-actual) (tipo humano))
    (not (intento-movimiento))
    =>
    (printout t "Turno de " ?color-actual ". Fila (1-8): ")
    (bind ?f (integer (read))) 
    (printout t "Columna (1-8): ")
    (bind ?c (integer (read)))
    
    (assert (intento-movimiento (color ?color-actual) (fila ?f) (columna ?c)))
    
    (retract ?fase)
    (assert (juego (fase ejecucion))) 
)

(defrule ejecutar-movimiento-simple
    ?fase <- (juego (fase ejecucion))
    ?i <- (intento-movimiento (color ?color) (fila ?f) (columna ?c))
    ?casilla <- (tablero (fila ?f) (columna ?c) (estado vacia))
    =>
    (retract ?i ?fase)
    (modify ?casilla (estado ?color))
    (printout t "Movimiento realizado en " ?f "," ?c crlf)
    (assert (juego (fase cambio-turno))) 
)

(defrule error-casilla-ocupada
    ?fase <- (juego (fase ejecucion))
    ?i <- (intento-movimiento (fila ?f) (columna ?c))
    (tablero (fila ?f) (columna ?c) (estado ?estado&~vacia))
    =>
    (retract ?i ?fase)
    (printout t "ERROR: Casilla ocupada por " ?estado ". Intenta de nuevo." crlf)
    (assert (juego (fase peticion)))
) 

(defrule error-coordenadas-invalidas
    ?fase <- (juego (fase ejecucion))
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
    (assert (juego (fase peticion))) 
)