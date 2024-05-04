import Parse.DSL

namespace Parse

set_option pp.rawOnError true

parser Http where
    def method : u8
    def url : span

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
        otherwise (start url url)

    node url where
        peek ' ' (end url http)
        any url

    node http where
        is " HTTP/1.1\r\n\r\n" http
        otherwise (error 3)
