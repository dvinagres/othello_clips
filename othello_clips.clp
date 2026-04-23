; 1. 
; info tablero
(deftemplate tablero
    (slot fila (type INTEGER))
    (slot columna (type INTEGER))
    (slot estado (type SYMBOL) (allowed-values vacia negra blanca))
)

; info del turno
(deftemplate turno
    (slot jugador (type SYMBOL) (allowed-values negro blanco))
)

; info del jugador
(deftemplate jugador
    (slot color (type SYMBOL) (allowed-values negro blanco))
    (slot tipo (type SYMBOL) (allowed-values humano maquina))
    (slot cantidad_fichas (type INTEGER))
)

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

(defrule imprimir-tablero-inicial
    (declare (salience -10)) ; prioridad baja para que se ejecute después de crear las fichas
    (initial-fact)
    =>
    (printout t "ESTADO ACTUAL DEL TABLERO:" crlf)
    (mostrar-tablero 8)
)