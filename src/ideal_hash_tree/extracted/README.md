Extraction Example: Ideal Hash Tree
================================


Open `iht.v` in Verlang-Coq. Quoting the final lines of that file:


```
Extraction Language CoreErlang.
(* The next generates several extracted modules. Grab the 'Top' module,
   rename it as 'Top.iht', and save as Top.iht.core. *)
Recursive Extraction iht.get iht.set.
```


The extractor has a bug in module extraction; in short, we need to perform the change mentioned above. Doing-so will reproduce the file `Top.iht.core`.


Experimenting with the output
-------------------------

Here is a sample session showing how to compile the extracted code, as well as a helper routine (`test:make_test`) which we can use to generate sample trees. This routine takes the given tree and populates it with key-value pairs `(x, 2*x)`, which we can then fetch using `Top.iht:get`.


```
[tcarstens@weibel extracted]$ erl
Erlang R16B01 (erts-5.10.2) [source] [64-bit] [smp:4:4] [async-threads:10] [hipe] [kernel-poll:false]

Eshell V5.10.2  (abort with ^G)
1> c('test', from_core).  
{ok,test}
2> c('Top.iht', from_core).
{ok,'Top.iht'}
3> T = 'test':'make_test' (32000, 'Ht_none').
{'Ht_bran',#Fun<Top.iht.6.46883918>}
4> 'Top.iht':'get' (T, 138).
{'Some',276}
5> 'Top.iht':'get' (T, 32001).
'None'
6> 
```
