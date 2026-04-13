; info tablero
(deftemplate tablero
    (slot fila (type INTEGER))
    (slot columna (type INTEGER))
    (slot estado (type SYMBOL) (allowed-values vacia negra blanca))
)