import Examples.Rewrite
import Examples.Hello

namespace Examples

def mulDiv (a b c : Nat) : Nat :=
  (a * b) / c

def addOne (x: Nat) := x * x + 2 * x + 1
#eval (addOne 3) * 10

end Examples
