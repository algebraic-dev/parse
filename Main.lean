import Parse

def main : IO UInt32 := do
  let mut str := "PUT  4ABCDPUT"

  let data := Parse.Http.create ()
    (on_body := λx y s => dbg_trace s!"body {x} {y} '{str.extract (String.Pos.mk x) (String.Pos.mk y)}'"; s)
    (on_url := λx y s => dbg_trace s!"url {x} {y} '{str.extract (String.Pos.mk x) (String.Pos.mk y)}'"; s)

  let res := Parse.Http.parse data str (str.length.toUInt32)
  IO.println s!"go! {res}"

  let data := data.reset

  let data := data.res

  IO.println s!"{data}"

  return 0
