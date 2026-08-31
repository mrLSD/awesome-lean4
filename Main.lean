import Examples.Hello

open Examples.Hello (hello)

def main : IO Unit :=
  IO.println s!"Hello, {hello}!"
