verlang
=======

Verlang is a project seeking to enable formally-verified software development within the Erlang environment. It is currently highly experimental.


Background
----------

[*Coq*][1] is an environment for functional programming with an integrated proof agent. The software development process with Coq is a bit non-standard: one doesn't ordinarily compile Coq source directly, but instead "extracts" the computationally-relevant portions to another language. Coq supports extraction to [OCaml][2], [Haskell][3], and [Scheme][4], though at time of writing the OCaml target is the most mature.

[*Erlang*][5] is a functional programming language by [Ericsson][6]. Among Erlang's notable features is its support for hot-swapping of modules, enabling software updates with reduced downtime. To compile Erlang, one first converts it to [*Core Erlang*][7], which is then compiled to a specific Erlang VM.

*Verlang* adds Core Erlang as an extraction target to Coq. From here it is possible to compile the extracted code and run it along-side ordinary Erlang modules.

Challenges
----------

The theory behind Coq's extraction, as well as the majority of its present implementation, is due to [Pierre Letouzey][8]. His extraction mechanism is based on a two step process: first, Coq terms are translated into an internal language (MiniML); after that, target-specific code translates from MiniML into the target.

MiniML maps to Core Erlang in a more or less obvious manner, but as usual the devil's in the details:

* Core Erlang's notion of "modules" do not allow for nesting. Care must thus be taken when extracting MiniML into Core Erlang, as source in the former is likely to have nested modules.
* Core Erlang does not support currying. In fact, the (`->`) type constructor isn't even associative -- the arity of a function is encoded in its type, and a function of arity `x` which yields a function of arity `y` cannot be used as a function of arity (`x+y`).
* Core Erlang distinguishes between inner- and inter-module calls. The former are invoked with the <code>apply</code> construction, while the latter are invoked with `call`.
* Core Erlang's `receive` primitive is a special case of side-effecting `case...of` construction, for which there is no analog in MiniML. Thus one needs special trickery to provide "natural" access to this primitive from within Coq source.

There are other issues as well (dealing with Erlang's sum-type constructor `|`, for instance), but many of them can be managed through careful use of Coq's `Extract` command.

Status
----------

Our work is highly experimental. We have a prototype extractor which attempts to address most of the challenges mentioned above:

* We support "module nesting" in a boring way: the outter-most module is preserved in the translation to Core Erlang, and name mangling is used to encode the sub-modules.
* We don't yet address problems related to currying. For the time being, we have been programming in Coq in such a way to avoid these issues in the extracted code.
* We treat all top-level function calls as inter-module calls, noting that a module is permitted to <code>call</code> into itself.
* We have admitted an axiom which describes <code>receive</code> (with finite timeout). The extractor recognizes a <code>case...of</code> around this axiom, which it translates into the desired Core Erlang.
* We don't (yet) generate Erlang header files for our modules (<code>.hrl</code> files).

It is currently possible to generate Core Erlang which fails with run-time exceptions (if you curry a function, for instance). We are still evolving the extraction theory, and thus there may be other bugs as well. Our goal is to resolve these issues and provide a rigorous implementation.


   [1]: http://coq.inria.fr/ "Coq"
   [2]: http://caml.inria.fr/ "OCaml"
   [3]: http://haskell.org/ "Haskell"
   [4]: http://groups.csail.mit.edu/mac/projects/scheme/ "Scheme"
   [5]: http://erlang.org/ "Erlang"
   [6]: http://www.ericsson.org/ "Ericsson"
   [7]: http://www.it.uu.se/research/group/hipe/cerl/ "Core Erlang"
   [8]: http://www.pps.univ-paris-diderot.fr/~letouzey/index.fr.html "Pierre Letouzey"
