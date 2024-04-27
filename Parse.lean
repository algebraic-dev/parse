import Parse.DSL
import Parse.Data

/-!
  Parse library for network protocols.
-/

parser parseHttp where
    def method : Nat
    def url : Nat × Nat

    node method where
        switch (store method onMeth)
            | "HEAD" => 0
            | "HE" => 1
        otherwise (error 1)



def res := parseHttp (Inhabited.default) (GState.state_0) "HEAD".toSubstring

#eval res.snd
