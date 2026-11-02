# Original canonical trace-image annihilation of structural H1

`Scheme.Cohomology.structureH1_annihilates_of_chosenEmbedding_trace_image`
turns an ORIGINAL section-trace image condition into annihilation of ORIGINAL
structure-sheaf H1. The scalar d may be zero; nonvanishing belongs to the later
uniform-bound argument, not to this implication.

The coefficient ring R is a regular local domain of dimension two. The base A
is a complete Noetherian normal local domain of dimension two, with an actual
finite injective local map sigma:R→A. The source X is integral and normal,
of dimension at most two, and f:X→Spec A is the original proper dominant
birational morphism. The supplied closed embedding into a finite-dimensional
projective space over R has the exact original structural triangle.

The only image hypothesis says that every d-multiple in the literal coinduced
coefficient Hom_R(A,R) lies in the range of the original chosen-embedding
`normalSurfaceSectionsTraceCoinduced`. The embedding composite's dominance and
original generic-map finiteness are derived inside the statement from sigma,
f and that triangle. No auxiliary function field is selected.

The proof uses the same injective resolutions, original structural scalar map,
derived structure object and derived unit throughout:

1. Existing proper birational geometry supplies the actual [0,1] bound and H0
   unit isomorphism. The original H1 has finite A-length, and finite local scalar
   restriction gives finite R-length. Finite normal surface algebra gives the
   required restricted projectivity of A.
2. Chosen-embedding GR vanishing and the original A-linear cohomology-dual
   comparison annihilate the literal dual H1.
3. `normalSurfaceCohomologyDual_unit_trace` identifies the actual section trace
   with the original dual unit; the image hypothesis becomes the precise image
   input of the existing native unit-Postnikov annihilator theorem.
4. `unitPostnikov_scalar_annihilates_of_image` annihilates the same derived H1.
   Its original linear structure-cohomology equivalence transfers the result to
   actual Sheaf.H1 with the structural A-action of f.

There is no rationality assumption, trace-isomorphism assumption, derived-unit
isomorphism assumption, desired H1 vanishing, new Ext/Matlis model or assumed
comparison equation. The standard derived-category universe is u+1 over the
same ModuleCat universe u, and original sheaf cohomology retains universe u+1.

This is not a pure degree-p bound theorem. The differential/canonical trace
construction must still supply its original image condition and a fixed nonzero
scalar. Uniform scalar-torsion bounds and actual domination/H1 injection belong
to the subsequent assembly. No resolution or regular terminal is asserted here.
