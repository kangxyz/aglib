# Closed embeddings from degree-one generators

[DegreeOneEmbedding.lean](DegreeOneEmbedding.lean), in the native namespace
`AlgebraicGeometry.Proj.DegreeOneEmbedding`, starts with a graded
commutative `R`-algebra `C`, its actual graded submodules `G`, a family
`g : κ → C` spanning `G 1`, and the equations `(G 1)^n = G n` for every
natural number `n`.

The equation at zero is included. It requires `G 0` to be the submodule
of scalar multiples of one, so homogeneous polynomial evaluation is
surjective in degree zero as well. No injectivity of `R → C` is assumed.
The structural morphism is the original `Proj G → Spec (G 0) → Spec R`.

`presentation` is the original polynomial evaluation `T_i ↦ g i` as a
graded ring map. `presentation_degreewise_surjective` proves surjectivity
on every homogeneous component. `embedding` is its native `Proj.map`;
`embedding_isClosedImmersion` uses the existing proved closed-immersion
theorem for degreewise-surjective graded maps. `embedding_toSpec` proves
the exact triangle over the original coefficient ring.

No finiteness, Noetherianity or flatness is needed for this closed-immersion
result. When `κ` is finite, its target is finite-coordinate polynomial
projective space. The intended current consumer is the local scalar-extended
Rees algebra in the projective presentation of a base-changed blowup.
That consumer must still prove its degree-one generation equations and
the actual Proj/base-change and tautological-section comparisons. This
leaf assumes no surface-projectivity conclusion and proves none of those
remaining comparisons.
