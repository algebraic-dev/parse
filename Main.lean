import Parse

def main : IO Unit := do
  let data := Parse.createData ()
  let res := Parse.ata data 0 "PUT    ATA/B"
  let res := Parse.ata data res "E HTTP/9.8"
  IO.println res
