# Prime cyclic filtrations and local multiplicity

[Basic](Basic.lean), imported as `Aglib.RingTheory.PrimeFiltration.Basic`, constructs `Module.PrimeFiltrationFrom` from actual submodules and quotient equivalences with prime cyclic modules. A finite module over a Noetherian commutative ring admits a prime filtration; the relative constructor retains its Noetherian-module premise.

[Primes](Primes.lean) records the actual factor primes and their primality. [Support](Support.lean) identifies their actual module support; [Length](Length.lean) computes the starting-submodule plus factor-length sum in extended-natural length. These lower results have no principal-Euler dependency.

[Multiplicity](Multiplicity.lean) localizes the literal filtration. At a minimal support prime, `localized_length_eq_count_of_bot` identifies the actual localized module length with the occurrence count of that prime among the factors. Relative versions keep their starting-submodule contribution and stated flatness/localization hypotheses.

These objects supply the factors for [principal Euler filtration/associativity](../Multiplicity/PrincipalEuler/README.md). Generic quotient/filtration operations lie below their scalar-length computations. The source records the actual primes and equivalences, rather than only an existential list of weights.
