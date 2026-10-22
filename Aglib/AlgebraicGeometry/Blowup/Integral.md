# Integral blowups and their original generic comparison

`Integral.lean` studies the existing `blowupDatum I`, with its original source
scheme, structural morphism and universal property. The base is an integral
scheme, and the actual centre ideal must miss its generic point:

```lean
genericPoint X ∉ (I.support : Set X)
```

Under this condition `blowup_isIntegral` proves that the constructed source is
integral. `BlowupDatum.isDominant_of_genericPoint_not_mem_support` proves
dominance of the specified map directly from its universal lift off the centre.
The results need no Noetherian, regularity, coherence or dimension assumption.

The proof uses the original Rees algebra and its homogeneous localizations.
Over a domain these local rings are reduced; if the affine Rees Proj is
nonempty, its zero homogeneous prime is its generic point. The native affine
local blowups then glue to a reduced scheme. Their generic points agree over
the original generic point because the original map is an isomorphism off the
centre, which proves global irreducibility.

`BlowupDatum.awayPartialIso` is the literal restriction of that map to the
inverse image of the centre complement. `BlowupDatum.birationalOver` records
the resulting native `BirationalOver B.map (𝟙 X)`. The generic comparison
`BlowupDatum.functionFieldEquiv` has underlying ring homomorphism exactly
`Scheme.functionFieldMap B.map`; its inverse comes from the same restriction
isomorphism. These comparisons also apply to any specified `BlowupDatum I` by
its unique comparison over the original base.

For a closed point `x`, `pointBlowup_isIntegral`, `pointBlowup_isDominant` and
`pointBlowup_birationalOver` specialize to the actual kernel ideal of
`X.fromSpecResidueField x`. They retain the necessary condition
`x ≠ genericPoint X`. Blowing up the zero ideal, including the point centre of
an integral zero-dimensional scheme, is not included. No regularity of the
blowup, resolution of an ideal, or transport of a Cartier factor through a
sequence is asserted here.
