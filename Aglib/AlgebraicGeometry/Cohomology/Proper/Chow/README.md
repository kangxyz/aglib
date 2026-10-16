# Chow modifications with proved cohomology inputs

Import `Aglib.AlgebraicGeometry.Cohomology.Proper.Chow`.
`Scheme.Cohomology.exists_chowModification_cohomology` starts with an
arbitrary proper morphism `f : X → Spec R` over a Noetherian commutative
ring. The only source local-Noetherian structure in its statement is
constructed from this actual proper morphism.

The theorem internally constructs one finite family of projective factors,
one scheme `Y`, maps `p : Y → X` and `q : Y → product(P_i)`, and an open
`V` of `X`. These data are chosen independently of all module coefficients.
The original `p` is proper and surjective, its original restriction over
`V` is an isomorphism, and `V` is dense in `X`. The original `q` is finite;
the structural factorization and the literal pair into `X × product(P_i)`
are retained, and that pair is a closed immersion.

For every original coherent coefficient `M` on this same `Y` and every
integer placement `k`, both actual derived images `Rp_*(M[k])` and
`R(p ≫ f)_*(M[k])` have coherent native homology and bounds
`[k, k + ∑ i, Fintype.card (σ i)]`. The dimensions refer to the actual
internally constructed factors `P_R(Option (σ i))`. For every natural
degree, the unchanged additive `Sheaf.H` of `M` is finite over `R` with
the original structural-ring action of `p ≫ f`.

The geometry is the sole unconditional
[`Morphisms.Proper.Chow.Basic`](../../../Morphisms/Proper/Chow/Basic.lean)
producer. The proof then applies the already proved
[finite-product image and finiteness interfaces](../../Projective/Products/README.md)
to its original closed pair and finite map. No Chow, coherent-image or
proper-finiteness family is supplied as an extra premise. Empty,
reducible and nonreduced sources are included. The theorem does not assert
that `p⁻¹(V)` is dense in every component of `Y`, or that `p` is
scheme-theoretically dominant.

These are the two cohomology inputs for the subsequent proper support
induction. General proper finiteness is not proved by this leaf alone:
the cone of the original ordinary modification unit can have degree
`-1` homology, which must remain in the boundary-support argument.
