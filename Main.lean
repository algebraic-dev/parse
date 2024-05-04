import Parse

def main : IO UInt32 := do
  let data := Parse.Http.create ()
  let str := "P"
  let res := Parse.Http.parse data str (str.length.toUInt32)
  IO.println s!"hello {res}"
  return 0
