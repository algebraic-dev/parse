import Parse.Syntax
import Parse.Specialize
import Parse.Compile
import Parse.ToC

import Lean.Elab.Command

open Parse.Syntax

namespace Parse

def http : Grammar :=
  let storage :=
    #[ ("method", Typ.u8)
    , ("minor", Typ.char)
    , ("major", Typ.char)
    , ("url", Typ.span)
    , ("prop", Typ.span)
    , ("value", Typ.span) ]

  let methodProp := 0
  let minorProp := 1
  let majorProp := 2
  let urlProp := 3
  let propProp := 4
  let valueProp := 5

  let method := 0
  let beforeUrl := 1
  let url := 2
  let http := 3
  let headerMajor := 4
  let headerVersionDot := 5
  let headerVersionMinor := 6
  let headerEnd := 7
  let fieldsStart := 8
  let fieldLineStart := 9
  let fieldLineSpace := 10
  let fieldLineOWS := 11
  let fieldLineValue := 12
  let fieldLineEnd := 13
  let conclude := 14

  let digit := #["0", "1", "2", "3", "4", "5", "a", "!", "8", "9"]

  let nodes :=
    #[ Node.mk "method"
        #[ Case.mk (Matcher.select
            #[ ("HEAD", 0),
               ("GET", 1),
               ("POST", 2),
               ("PUT", 3),
               ("DELETE", 4),
               ("OPTIONS", 5),
               ("CONNECT", 6),
               ("TRACE", 7),
               ("PATCH", 8) ])
            (Action.store methodProp beforeUrl)
         ]
      , Node.mk "beforeUrl"
          #[ Case.mk (Matcher.is #[" "]) (Action.goto beforeUrl)
           , Case.mk (Matcher.goto false) (Action.capture urlProp url)
           ]
      , Node.mk "url"
          #[ Case.mk (Matcher.peek #[' ']) (Action.close urlProp http)
           , Case.mk (Matcher.goto true) (Action.goto url)
           ]
      , Node.mk "http"
          #[ Case.mk (Matcher.is #[" HTTP/"]) (Action.goto headerMajor)
           ]
      , Node.mk "headerMajor"
          #[ Case.mk (Matcher.is digit) (Action.store majorProp headerVersionDot)
           ]
      , Node.mk "headerVersionDot"
          #[ Case.mk (Matcher.is #["."]) (Action.goto headerVersionMinor)
           ]
      , Node.mk "headerVersionMinor"
          #[ Case.mk (Matcher.is digit) (Action.store minorProp headerEnd)
           ]
      , Node.mk "headerEnd"
          #[ Case.mk (Matcher.is #["\r\n"]) (Action.goto fieldsStart)
           ]
      , Node.mk "fieldsStart"
          #[ Case.mk (Matcher.is #["\r\n"]) (Action.goto conclude)
           , Case.mk (Matcher.goto false) (Action.capture propProp fieldLineStart)
           ]
      , Node.mk "fieldLineStart"
          #[ Case.mk (Matcher.peek #[':']) (Action.close propProp fieldLineSpace)
           , Case.mk (Matcher.goto true) (Action.goto fieldLineStart)
           ]
      , Node.mk "fieldLineSpace"
          #[ Case.mk (Matcher.is #[":"]) (Action.goto fieldLineOWS)
           ]
      , Node.mk "fieldLineOWS"
          #[ Case.mk (Matcher.is #[" "]) (Action.goto fieldLineOWS)
           , Case.mk (Matcher.goto false) (Action.capture valueProp fieldLineValue)
           ]
      , Node.mk "fieldLineValue"
          #[ Case.mk (Matcher.peek #['\r']) (Action.close valueProp fieldLineEnd)
           , Case.mk (Matcher.goto true) (Action.goto fieldLineValue)
           ]
      , Node.mk "fieldLineEnd"
          #[ Case.mk (Matcher.is #["\r\n"]) (Action.stop 0 fieldsStart)
           ]
      , Node.mk "conclude"
          #[ Case.mk (Matcher.goto false) (Action.stop 1 method)
           ]
    ]

  Grammar.mk
    (Storage.mk storage)
    nodes

elab "aaasp" s:ident : command => do
  let res ← Parse.ToC.compile s http
  Lean.Elab.Command.elabCommand res

aaasp Http
