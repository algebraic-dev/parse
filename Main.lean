import Parse

def main : IO Unit := do
  let data := Parse.createData 0
  IO.println "hello"
  IO.println (← Parse.ata data 0 "PUT   ABCS/D")
