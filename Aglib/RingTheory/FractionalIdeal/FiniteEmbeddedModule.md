# A finite embedded module and its original numerator ideal

Source: [FiniteEmbeddedModule.lean](FiniteEmbeddedModule.lean).

For a domain R, its given fraction localization K, and a finite R-module M,
`finiteEmbeddedImage f` is the native fractional ideal with underlying range
of the specified linear map f:M→K. Native finite generation supplies its
fractional denominator. No new denominator or fraction-field realization is
selected.

If f is injective, `finiteEmbeddedModuleEquivNum` composes the native range
equivalence with `equivNumOfIsLocalization`. Its target is exactly the native
numerator ideal of that same fractional image. The algebra-map value theorem
retains multiplication by the original denominator and the original value f(m).
Nontriviality of M is needed only to conclude the numerator ideal is nonzero.

No field, GCD, regularity, locality, Noetherianity, invertibility of M, or
independent torsion-free premise is added. The fraction localization and module
can have independent universes. A geometric canonical-module consumer must
still produce its actual embedding; this leaf does not assume or construct a
canonical generic frame, a blowup, or a strict-transform comparison.

Direct consumers: [AlgebraicGeometry/Cohomology/Duality/Projective/Relative/NormalSurface/StalkEmbedding](../../AlgebraicGeometry/Cohomology/Duality/Projective/Relative/NormalSurface/StalkEmbedding.md).
