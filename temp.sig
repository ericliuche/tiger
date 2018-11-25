signature TEMP = 
sig
  eqtype temp
  val newtemp : unit -> temp
  structure Table : TABLE sharing type Table.key = temp
  structure Set : ORD_SET sharing type Set.Key.ord_key = temp
  val makestring: temp -> string
  type label = Symbol.symbol
  val newlabel : unit -> label
  val namedlabel : string -> label
end

