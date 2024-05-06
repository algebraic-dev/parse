# Parse.lean

It"s a protocol parser generator for Lean4, currently, it only generates Lean4. It uses lean macros to generate lean code that is optimized. It's based on https://github.com/nodejs/llparse.

```lean
parser Http where
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
        otherwise (error 0)

    node beforeUrl where
        is " " beforeUrl
        goto (start url url)

    node url where
        peek ' ' (end url http)
        otherwise url

    node http where
        is " HTTP/1.1\r\n\r\n" http
        otherwise (error 1)
```

