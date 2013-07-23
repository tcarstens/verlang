Verlang-Coq
==========

Our Core Erlang extractor is written in Coq. To integrate it into Coq itself, we extract `coreerlang.v` into OCaml, which we then integrate into the Coq source. The `verlang.patch` file captures the changes introduced via this process (as well as some other changes which we introduced by hand).
