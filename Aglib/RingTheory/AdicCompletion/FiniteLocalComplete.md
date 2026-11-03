# Completeness of a finite local algebra

Import `Aglib.RingTheory.AdicCompletion.FiniteLocalComplete`.

`IsAdicComplete.maximalIdeal_of_finite_local R C` applies to an original
finite local algebra `R -> C`, with a local coefficient map, over a
Noetherian local ring `R` complete for its maximal ideal. It proves that
`C` is complete for **its own original maximal ideal**. Neither ring is
required to be a domain, normal, regular or of bounded dimension.

The proof uses existing finite-module completeness for the extended base
maximal ideal, then the existing `AdicCompletion.finiteLocalAlgEquiv` and
the native bijectivity characterization of completeness. The equivalence
retains original elements. No new completion, cofinality assumption or
completeness hypothesis on `C` is introduced.

This is the single generic owner of the completeness assembly previously
specialized in `integralClosure.completeIntermediate_complete`. That
intermediate-closure theorem retains its original statement and becomes
a thin application after installing its already proved actual finite,
local and local-coefficient-map dictionaries. This lower theorem makes
no assertion that a later birational-model stalk is finite or complete
over the original base.
