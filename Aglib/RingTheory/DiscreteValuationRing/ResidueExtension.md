# Adjoining a prescribed residue element

Let B be a DVR, let p be a natural number whose image in B is irreducible,
and let g:B→K be a ring map to an actual field K with kernel the maximal
ideal of B. The construction
`IsDiscreteValuationRing.residueExtension p hp g hg a` returns an actual
DVR D, actual maps f:B→D and h:D→K, and proofs that h∘f=g, p:D remains
irreducible, ker(h)=maximalIdeal(D), and a belongs to the image of h.
The result is packaged in `IsDiscreteValuationRing.ResidueExtension` so
that the exact ring and both maps can be used in a coherent diagram.

The field action used in the construction is derived from g: it is the
literal quotient lift `ResidueField B→K`. Its composite with the original
residue map is g. No coefficient section into B is assumed.

If a is algebraic over this actual residue-field image, take the literal
intermediate field L=(ResidueField B)⟮a⟯ inside K. Its native power basis
has generator the subtype element a. The new ring is
`PowerBasis.ResidueLiftRing B L b`, the literal monic root algebra from
`MonogenicResidueExtension`. Its constructed point to L, followed by the
actual inclusion L→K, is h. The coefficient, kernel, original-uniformizer,
and root equations give all required properties. Inseparable a is
included; there is no claim that every finite extension is simple.

If a is transcendental, take the existing literal DVR
`ParameterLocalization.Ring B Unit (p : B)`. Its actual residue field is
explicitly equivalent to the fraction field of the polynomial ring in
one variable over ResidueField B. Transcendence makes evaluation of that
variable at a injective, by `algebraicIndependent_unique_type_iff`.
`IsFractionRing.lift` extends this actual evaluation to the fraction
field. Composing with `residueFieldRingEquiv` and the original residue
map defines h. Injectivity of the two field maps proves the kernel
equation; the explicit polynomial formulas prove both the coefficient
equation and the image of the original variable.

The current consumer is the successor operation in the arbitrary-residue
Cohen construction. The new result proves the successor obligation with
its actual point square. It does not supply a coherent transfinite
diagram or final surjectivity. The actual DVR colimit proof is supplied
separately by [`FilteredColimit`](FilteredColimit.lean).

Source basis: Aglib HEAD `8b93cc5940dc93f39a2eaf05e6985af28250a578`,
Lean 4.34.1, and Mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`.
The mathematical successor construction uses the explicit suppliers
above and preserves their original hypotheses.
