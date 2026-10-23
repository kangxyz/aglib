# The actual Cohen coefficient map into the original local ring

`IsDiscreteValuationRing.exists_complete_cohenMap` applies to a complete
characteristic-zero local domain A whose actual residue field has prime
characteristic p. It constructs a complete characteristic-zero DVR C
with the original natural p as uniformizer and an actual injective local
ring map f:C→A. The original composite C→A→ResidueField A is surjective.
There is no perfectness, finite p-basis, finite-degree, Noetherianity,
or dimension hypothesis on A in this coefficient-map theorem.

The construction first applies [`CohenRing`](CohenRing.lean) to exactly
K=ResidueField A. Its output is an actual Cohen DVR C and a surjective
point g:C→K with kernel maximalIdeal C. The target is the original
quotient A/maximalIdeal A. The map g is regarded as the same map of
integer algebras through native `RingHom.toIntAlgHom`.

To use [`Smooth/AdicLift`](../Smooth/AdicLift.lean), set
I=span{(p:Z)}. The three required hypotheses are proved. First, C is
torsion free over the integers because it is a characteristic-zero
domain, and the native torsion-free-over-Dedekind instance makes it
flat over Z. Second, p belongs to maximalIdeal A because its original
residue vanishes. Thus I A lies in that maximal ideal. Third, the
literal quotient map Z/I→C/IC is formally smooth.

For the third statement, IC is the actual maximal ideal of C by
irreducibility of p. The ring equivalence
`Int.quotientSpanNatEquivZMod p` proves that the original quotient Z/I
is a finite field. Explicit native quotient field structures preserve
the original quotient ring operations. The source is perfect because
it is finite. The unrestricted
`Algebra.FormallySmooth.field_of_perfectField` then applies to the
original quotient-algebra map into C/IC. Perfectness is imposed only
on this derived prime-field source, not on the residue field of A.

Adic lifting constructs f with the exact equation

```text
(residue A).comp f = g.
```

If c is a nonunit of C, the actual kernel equation gives g(c)=0, so
the displayed identity puts f(c) in maximalIdeal A. This proves
locality. A nonzero c has its native DVR factorization c=u*p^n. Its
image is a unit times a power of the original natural p in A, which
is nonzero because A is a characteristic-zero domain. Thus f is
injective; p need not be irreducible in A.

This closes the coefficient-map step in the mixed-characteristic R.F2
construction. The finite regular two-dimensional subring is a further
construction using actual parameters and a completed localized
polynomial ring. Its existence or finiteness is not a premise here.

Source basis: Aglib HEAD `8b93cc5940dc93f39a2eaf05e6985af28250a578`,
Lean 4.34.1, and Mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`.
The native suppliers are `Smooth/AdicLift`, the unrestricted field
smoothness theorem, the literal integer quotient equivalence, and
`Mathlib/RingTheory/Flat/TorsionFree.lean`.
