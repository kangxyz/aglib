# Fibre dimensions under flatness

The parent [FiberDimension](../FiberDimension.lean) proves upper
semicontinuity for any finite module. [Flat](Flat.lean) gives
`Module.isLocallyConstant_finrank_fiber` when the module is also finitely
presented and flat. The proof uses the native `Module.rankAtStalk_eq` and
`Module.isLocallyConstant_rankAtStalk`, retaining the original residue
fibres. This result supplies local constancy for the finite flat terms of
the complexes used in cohomological Euler characteristic computations.

[Reduced](Reduced.lean) supplies the converse local criterion with the
essential reducedness hypothesis: a finite module over a reduced local ring
with locally constant original fibre dimensions is free. The proof lifts a
closed-fibre basis to the actual finite free surjection by Nakayama and uses
the [residue-fibre injectivity detector](../FiberInjectivity.lean) to make it
bijective. A separate equality compares the native prime-residue fibre at
the closed point with the usual quotient-residue fibre. This is the local
algebra behind the reduced-base Grauert criterion; no such freeness claim
is made for arbitrary nonreduced rings. The statements align with
[Stacks, Section 10.78](https://stacks.math.columbia.edu/tag/00NV).

[BaseChange](BaseChange.lean) proves equality of the original fibre ranks
under arbitrary scalar extension for finite modules. The source ring,
target ring and module-carrier universes are independent; flatness and
finite presentation are not assumed. [LocallyFree](LocallyFree.lean)
uses this comparison and the reduced local criterion to characterize
projectivity of a finitely presented module over a reduced ring by local
constancy of its original fibre dimensions. No local-ring or Noetherian
hypothesis is needed.
