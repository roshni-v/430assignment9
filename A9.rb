=begin
PROG : DEFN+

DEFN : {def {id id ...} = EXPR}

Exp : Num
    | id
    | String
    | {Expr if Expr else Expr}
    | {Expr where {[id := Expr] ...}}
    | {{id ...} => Expr}
    | {Expr Expr ...}
=end

puts "Hello world!"
