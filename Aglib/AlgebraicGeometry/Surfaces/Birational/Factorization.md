# Factorization of proper birational regular-surface morphisms

`Factorization.lean` constructs a finite chain of the original point blowups
for a proper dominant morphism `f : X ⟶ Y` between integral regular schemes
of dimension at most two, with `Y` Noetherian and the original
`functionFieldMap f` invertible. Properness then gives Noetherianity of `X`.
A wrapper accepts the native input `BirationalOver f (𝟙 Y)`.

`exists_pointBlowupChain_factorization` returns an actual scheme `Z`, an
actual `β : Z ⟶ Y`, a literal `Blowup.PointBlowupChain β`, and an explicit
`e : X ≅ Z` with `e.hom ≫ β = f`. Source isomorphisms remain explicit; an
arbitrary isomorphism is never asserted to be a literal point-blowup chain.
The chain starts at the original `Y`, so its existing regularity, integrality,
properness and dimension suppliers apply to every constructed stage.

The proof first constructs the lift through the original blowup of each
actual bad target point. A concrete resolving chain is produced by the
existing common-domination theorem over an actual affine neighborhood.
An internal minimum-length argument removes every source blowup: contraction
of the last literal exceptional fibre descends by proper-fibre descent;
noncontraction identifies the two actual exceptional curves and forces the
original bad fibre to be finite, contradicting the isomorphism-locus criterion.

The exceptional map uses the original residue-field morphism in its literal
pullback square. Its original generic stalk map becomes invertible using the
ambient Cartier-divisor DVR neighborhood and the closed-immersion stalk
surjection. Canonical global functions on the two projective lines identify
the actual centre-field map. Native coefficient base change of O(1) then
transports the original conormal comparisons to one field. The proved
canonical conormal and Cartier-neighborhood theorems apply to those exact
maps and include the whole target exceptional fibre.

Open restriction preserves the actual residue-point ideal through its
canonical residue-field square. The affine lift glues with the canonical
lift off the centre; on their overlap the inverse-image ideal is the unit
ideal and the original blowup universal property gives equality. No assumed
global gluing family or tensor/image-ideal identification is used.

Termination uses the proved finite `contractedCurveCount` from
[ExceptionalLocus](ExceptionalLocus.md). The newly extracted target point
blowup strictly lowers that count. The proof does not replace it with a sum
of local colengths or assume a global exceptional-curve isomorphism in the
count argument.

There is no excellence, perfectness, characteristic, ground-field
projectivity or algebraic-closure hypothesis. This factorization theorem
starts with regular schemes; it does not construct a regular model from an
arbitrary singular source.
