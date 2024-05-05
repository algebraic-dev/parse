import Parse.DSL

namespace Parse

set_option pp.rawOnError true

parser Http where
    def method : u8
    def res : u64
    def url : span
    def body : span

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
        otherwise (error 122)

    node beforeUrl where
        is " " beforeUrl
        is ["0" "1" "2" "3" "4" "5" "6" "7" "8" "9"] (call (loadNum res) url)

    node url where
        is ["0" "1" "2" "3" "4" "5" "6" "7" "8" "9"] (call (mulAdd res) url)
        otherwise (start body cap)

    node cap where
        otherwise (consume res endCap)

    node endCap where
        otherwise (end body method)
