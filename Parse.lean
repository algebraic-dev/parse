import Parse.DSL
import Parse.State

/-!
  Parse library for network protocols.
-/

parser parseHttp : HttpData, HttpState Nat exception String where
    def method : Nat
    def url : Nat × Nat

    node method where
        switch (store method beforeUrl)
          | "HEAD" => 0
          | "GET" => 1
          | "POST" => 2
          | "PUT" => 3
          | "DELETE" => 4
          | "OPTIONS" => 5
          | "CONNECT" => 6
          | "TRACE" => 7
          | "PATCH" => 8
        otherwise (error "cannot match metho")

    node beforeUrl where
        is ['a' 'b' 'c'] beforeUrl
        goto (start url url)

    node url where
        peek ' ' (end url http)
        otherwise url

    node http where
        is " HTTP/1.1\r\n\r\n" http
        otherwise (error "cannot match http header")
