; T
; info tablero
(deftemplate tablero
    (slot fila (type INTEGER))
    (slot columna (type INTEGER))
    (slot estado (type SYMBOL) (allowed-values vacia negra blanca))
)

; info del turno
(deftemplate turno
    (slot jugador (type SYMBOL) (allowed-values negra blanca))
)

; info del jugador
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

; FACTS
; estado inicial
(deffacts estado-inicial
    (turno (jugador negra)) ; Empiezan negras
    (jugador (color negra) (tipo humano) (cantidad_fichas 2))
    (jugador (color blanca) (tipo humano) (cantidad_fichas 2))
)

; inicializar el tablero: las fichas deben existir en memoria
(defrule inicializar-tablero
   (initial-fact)
   =>
   (loop-for-count (?f 1 8)
      (loop-for-count (?c 1 8)
         (if (and (= ?f 4) (= ?c 4)) then (assert (tablero (fila 4) (columna 4) (estado blanca)))
          else (if (and (= ?f 4) (= ?c 5)) then (assert (tablero (fila 4) (columna 5) (estado negra)))
          else (if (and (= ?f 5) (= ?c 4)) then (assert (tablero (fila 5) (columna 4) (estado negra)))
          else (if (and (= ?f 5) (= ?c 5)) then (assert (tablero (fila 5) (columna 5) (estado blanca)))
          else (assert (tablero (fila ?f) (columna ?c) (estado vacia)))))))
      )
   )
)

; RULES
(defrule imprimir-tablero-inicial
    (declare (salience -10)) ; prioridad baja para que se ejecute después de crear las fichas
    (initial-fact)
    =>
    (printout t "ESTADO ACTUAL DEL TABLERO:" crlf)
    (mostrar-tablero 8)
)

(defrule pedir-movimiento-humano
    (turno (jugador ?color-actual))
    (jugador (color ?color-actual) (tipo humano))
    (not (intento-movimiento)) ; Solo pide si no hay un intento procesándose
    =>
    (printout t "Turno de " ?color-actual ". Introduce la fila (1-8): ")
    (bind ?f (read))
    (printout t "Introduce la columna (1-8): ")
    (bind ?c (read))
    
    (assert (intento-movimiento (color ?color-actual) (fila ?f) (columna ?c)))
)

(defrule ejecutar-movimiento-simple
    ?i <- (intento-movimiento (color ?color) (fila ?f) (columna ?c))
    ?casilla <- (tablero (fila ?f) (columna ?c) (estado vacia))
    =>
    (retract ?i)
    (modify ?casilla (estado ?color))
    (printout t "Movimiento realizado en " ?f "," ?c crlf)
)

(defrule pasar-turno-a-blanca
    (not (intento-movimiento)) 
    ?t <- (turno (jugador negra))
    =>
    (retract ?t)
    (assert (turno (jugador blanca)))
    (mostrar-tablero 8))

(defrule pasar-turno-a-negra
    (not (intento-movimiento))
    ?t <- (turno (jugador blanca))
    =>
    (retract ?t)
    (assert (turno (jugador negra)))
    (mostrar-tablero 8))

; FUNCIONES 
(deffunction mostrar-tablero (?tamano)
    (printout t crlf "   | ")
    
    ; imprimir la cabecera de las columnas (1 2 3 4...)
    (loop-for-count (?c 1 ?tamano)
        (printout t ?c " | ")
    )
    (printout t crlf "---------------------------------------" crlf)
    
    ; imprimir las filas
    (loop-for-count (?f 1 ?tamano)
        (printout t " " ?f " | ") ; imprime el número de fila al inicio
        
        (loop-for-count (?c 1 ?tamano)
            ; do-for-fact busca el hecho "tablero" que coincida con la fila y columna del bucle
            (do-for-fact ((?casilla tablero)) 
                (and (= ?casilla:fila ?f) (= ?casilla:columna ?c))
                
                ; imprime el símbolo correspondiente según el estado
                (if (eq ?casilla:estado vacia) then (printout t "  | "))
                (if (eq ?casilla:estado negra) then (printout t "N | "))
                (if (eq ?casilla:estado blanca) then (printout t "B | "))
            )
        )
        (printout t crlf "---------------------------------------" crlf)
    )
    (printout t crlf)
)

; ---- PRUEBA
; -- (mostrar-tablero 8) EN TERMINAL

;(deffacts partida-prueba
;    (tablero (fila 4) (columna 4) (estado blanca))
;    (tablero (fila 4) (columna 5) (estado negra))
;    (tablero (fila 5) (columna 4) (estado negra))
;    (tablero (fila 5) (columna 5) (estado blanca))
;)

; -- TEST HUMANO CONTRA HUMANO


