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
    ()
)