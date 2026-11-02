# Same normalized-chain terminal over the original finite base map

Source: [FiniteBaseEmbedding.lean](FiniteBaseEmbedding.lean).

`Blowup.NormalizedPointBlowupChain.exists_projective_embedding_of_isFinite_base`
constructs a finite standard projective embedding of the SAME terminal of a
supplied proper normalized-point chain `f:T→X`. The initial X is integral and
locally Noetherian, and its ORIGINAL map `beta:X→Spec R` is finite. The final
closed immersion satisfies the literal equation `i ≫ toSpec = f ≫ beta`.

The coefficient ring R is arbitrary and commutative. No Noetherianity,
normality, regularity or dimension assumption on R is imposed. Neither source
regularity nor a supplied initial projective embedding is required.

The native `ProjectiveSpace.pointIsoSpec R` has finite nonempty coordinate type
`PUnit.{u+1}` in Type u, and its hom is exactly the original projective structure
map. The finite composite of beta with its inverse is fed to the existing
finite-map projective embedding theorem. This embeds SAME X; the accepted
proper normalized-chain embedding theorem then propagates that presentation
along SAME f. The two original structure triangles compose by the point
isomorphism cancellation.

This single generic consumer covers the affine identity starting case and the
original finite regular-parent situation by their actual finite scheme maps.
There is no redundant affine wrapper, replacement terminal, regularity oracle,
new normalization, resolution existence or canonical-frame assertion.
