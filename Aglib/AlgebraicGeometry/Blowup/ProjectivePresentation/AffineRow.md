# The original affine row in full tensor-ideal coordinates

[AffineRow.lean](AffineRow.lean) retains the original affine centre
`affineCenter R I` and the actual pullback along `Spec S → Spec R`.

`originalIdealIso` uses the native kernel and closed-image comparisons to
identify the original ideal module with the associated sheaf of `I`.
`tensorIdealIso` composes its actual pullback with `tildePullbackIso` and
`extendScalarsAlgebraIso`, obtaining the associated sheaf of the full
module `S ⊗[R] I`. The original section associated to `b : I` is sent to
the section of `1 ⊗ b`; this equality is proved from the original unit
comparison and affine scalar adjunction. `pullback_tensorSection` gives
the same actual formula for a section of the full tensor ideal under a
further scalar change, retaining both native tilde-unit comparisons.

For a displayed coproduct epimorphism from copies of an affine module
`D` to this pulled ideal, and a specified actual frame `D ≅ O`, `row`
retains every original summand and morphism. `sheafPresentation` names
that same framed coproduct map once. `linearPresentation` recovers the
actual module map through the explicit fully faithful tilde provider;
its epimorphy uses the same native map equation.
`generators` evaluates it at the original basis entries.
`generators_reconstruct_row` proves equality with every original sheaf-map
entry, and `span_generators` proves that these elements span the full
tensor ideal. The native tilde/Finsupp comparison retains the original
coordinate index throughout.

No flatness, Noetherianity, domain, or image-ideal assumption is introduced.
A finite original index remains finite. These generators provide the
specified family required by `AffineEmbedding`; no compatibility of a
new family with the original row is assumed.

The remaining geometric consumer must identify the original tautological
quotient of this row with the polynomial Proj chart map. This leaf does
not assert that equality, global closedness, or projectivity of a
point-blowup chain.
