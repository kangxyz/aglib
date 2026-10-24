# Exact sequences and integer length

[ExactSequence](ExactSequence.lean), imported as `Aglib.RingTheory.Length.ExactSequence`, defines `Module.intLength` by the integer cast of `Module.length`'s `ENat.toNat`. The definition does not itself certify finite length.

`intLength_add_of_exact` gives `intLength V = intLength U + intLength W` for an injective/exact/surjective module sequence whose middle module has finite length. `intLength_exact_pair` needs only exactness and finite middle length and expresses that middle length as the sum of the two image lengths. `length_kernel_eq_cokernel` says that every endomorphism of a finite-length module has equal actual kernel and cokernel lengths. It requires neither injectivity nor flatness of the endomorphism.

These generic cancellation/exactness results lie below [scalar homology](../ScalarHomology/README.md) and [principal Euler](../Multiplicity/PrincipalEuler/README.md). Extended-natural length and its integer cast are distinct interfaces; using the cast does not supply a missing finiteness premise.

[ResidueDimension](ResidueDimension.lean), [PrimeQuotient](PrimeQuotient.lean)
and [PrincipalIntersection](PrincipalIntersection.lean) supply the lower length
comparisons used by operator multiplicities. These distinguish actual
extended-natural lengths from their natural or integer casts; finite-length
interpretations keep the stated finiteness premises.

[ScalarFactorization](ScalarFactorization.md) bounds the length of `M` by
its original scalar torsion plus the length of `N` when actual linear maps
`M → N → M` compose to scalar multiplication. Its local-ring restriction
form retains the residue-field degree and needs only base-linearity of the
maps. Lengths are in `ℕ∞`, without a splitting or finiteness premise.
The finite trace-coordinate cohomology estimate consumes this inequality.
