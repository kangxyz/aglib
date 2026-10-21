# Principal projective ideals on a localization

`IsRegularLocalRing.isPrincipal_map_of_projective_localization` starts
with a regular local commutative ring `R`, a submonoid `W`, an actual
domain localization `S`, and an ideal `I` of `R`. Its projectivity premise
is about the actual extended ideal `I.map (algebraMap R S)`. The conclusion
is native principality of that same ideal.

The ideal `I` is finite over the Noetherian ring `R`, so the regular-local
projective-dimension theorem applies directly. The native localized
submodule is identified with the extended ideal and with the scalar
extension of `I`. Flat base change and projectivity give a finite free
stable complement. Rank-one cancellation makes a nonzero extended ideal
principal; the zero ideal is handled separately.

This supplies the part of the Picard-triviality argument needed by the
actual height-one ideals in [`Factorial.lean`](Factorial.lean). The module
being localized is already the finite ideal `I`, so no separate descent
theorem for arbitrary invertible modules is needed. There is no assumed
UFD, Cartier, or ideal-freeness theorem family.

The argument follows the finite-free-resolution idea in
[Stacks Project, tag 0AFZ](https://stacks.math.columbia.edu/tag/0AFZ), using
actual stable products and the cofactor cancellation construction in
place of a Grothendieck-group or determinant-functor construction.
