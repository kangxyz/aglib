# An actual Cohen DVR for an arbitrary residue field

`IsDiscreteValuationRing.exists_complete_residuePoint` constructs, for
every field K of prime characteristic p, a commutative ring C with
domain and DVR structures, characteristic zero, maximal-adic
completeness, and irreducible natural coefficient p. It also constructs
an actual surjective ring map g:C→K whose kernel is the actual maximal
ideal of C. No perfectness, finite transcendence degree, or finite p-basis
assumption is made on K.

The public theorem is an existence result for the actual marked ring and
point. The construction uses the original maps at each stage. Its two
immediate prerequisites are the combined residue-element extension and
the filtered-colimit DVR theorem, with their original maps and kernel
equations.

Fix K and p. Work in the actual category of commutative rings over K.
The marked-object predicate says that the source is a characteristic-zero
DVR, its natural p is irreducible, and the kernel of its actual map to K
is the maximal ideal. It does not require surjectivity.

The candidate proves this predicate closed under small filtered colimits
using `DiscreteValuationRing/FilteredColimit`. The over-category
projection gives the actual underlying ring colimit, and every cocone
triangle gives precisely the point-composition equation needed by that
theorem. The domain, DVR, common uniformizer, and kernel are therefore
proved for the literal colimit. Characteristic zero passes through any
one cocone map: it preserves the irreducible p, hence is injective, so
injectivity of natural casts in that stage implies injectivity of natural
casts in the colimit.

The marked full subcategory consequently has the required filtered
colimits. This closure instance is constructed from the preceding proof;
it is not an added hypothesis. A nonempty well-order and every nonempty
initial segment at a limit are filtered, giving the actual
`HasIterationOfShape` instance used by `SuccStruct`.

The starting object is the universe lift of the native p-adic integers.
Its point is the original map to `ZMod p`, followed by the prime-field
embedding into K. Native `PadicInt.ker_toZMod` and `irreducible_p` give
the marked-point data. The original coefficient p is unchanged by the
universe lift.

At a marked stage with nonsurjective point, choose an element a outside
its actual range. `IsDiscreteValuationRing.residueExtension` constructs
the next actual DVR, its point, the transition map, and a preimage of a.
The point triangle commutes, and the same p remains irreducible. This
also makes the transition injective and preserves characteristic zero.
At a surjective stage use the identity successor. The actual successor
object and transition form a native `SuccStruct`; its choices need not
be functorial.

Iterate on the well-order of cardinal
λ=succ(max(aleph0, |K|)). The native `SuccStruct.iterationFunctor` supplies
the coherent diagram and `iterationCocone` supplies its final colimit.
Suppose the final point were not surjective. Then every stage point
would fail to be surjective. Write aᵢ for the element chosen outside
the image at stage i. It lies in the image of the successor stage by
the explicit successor construction and the native successor-object
isomorphism. If i<j, the actual diagram map puts aᵢ in the image at
stage j, whereas aⱼ is outside that image. Hence i↦aᵢ is injective.
`Cardinal.mk_le_of_injective` contradicts λ>|K|. Thus surjectivity of
the final point is proved, not included in an existence witness.

Finally complete the resulting DVR B at the literal ideal `(p:B)`.
`AdicCompletion/PrincipalDiscreteValuationRing` gives the actual complete
DVR C with the same uniformizer. Its explicit residue equivalence is
composed with the quotient equivalence induced by the constructed
surjective point B→K. This defines the actual point C→K. The proof
retains the equation

```text
point_C (algebraMap B C b) = point_B b.
```

That equation is used to prove the final point surjective. Injectivity
of the field equivalence gives its exact kernel. The original B→C map
preserves the same irreducible p, so it is injective and characteristic
zero is retained. No flatness of a completion of a non-Noetherian ring
is used, and no intermediate completion is needed.

This is the arbitrary-residue Cohen-ring existence obligation in R.F2.
The map of this constructed ring into a prescribed complete local ring
uses the separate proved `Smooth/AdicLift` theorem together with explicit
prime-field quotient identifications. The finite injective regular
power-series subring of a given two-dimensional domain remains a further
assembly; this theorem alone does not close all of R.F2 or resolution.

The mathematical construction follows the residue-enlargement method of
[Stacks Project, Tag 03C3](https://stacks.math.columbia.edu/tag/03C3) and
the Cohen-ring theorem [Tag 0328](https://stacks.math.columbia.edu/tag/0328).
The marked same-uniformizer colimit proof and the native
`SuccStruct`/cardinal assembly above are explicit argument in this module.
The displayed 0328 proof was checked on 2026-10-23. Its 2026-01-19
correction record identifies
[`e7edf1286bfc2b77c248fad933d24ba905951dd9`](https://github.com/stacks/stacks-project/commit/e7edf1286bfc2b77c248fad933d24ba905951dd9);
the commit diff itself was not inspected. The completion argument here
uses the proved principal-parameter regularity and residue comparison.

Source basis: Aglib HEAD `8b93cc5940dc93f39a2eaf05e6985af28250a578`,
Lean 4.34.1, and Mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`.
Exact Lean source
`302d796c52db0084e4ff31f2cbb5b591e8bd3249010984f54dce52ab5d4ffa8b`
passed native compilation in 7.6 seconds at the default budgets in
`remote-f6f87058581a452e99a7ae1f8e42d3ea`; that shared graph contained a
separately failed Arc target. The completed ordinary complex v2 review
supports this exact public theorem and its reviewed dependencies, with
no mathematical gap identified in that scope and the v1 source defect
resolved for v2. This records the scoped native and ordinary-review
evidence; it does not assign established status or close full R.F2.
