# Structure cohomology on a closed projective line subscheme

`Scheme.Cohomology.subsingleton_structureCohomology_of_closedLine`
proves that the original structure-module cohomology of an actual closed
subscheme of `ProjectiveSpace A ι` vanishes in every positive degree when
`ι ≃ Fin 2`. The base `A` is any commutative ring in the common geometric
universe. The subscheme may be empty or nonreduced.

For the original closed immersion `i : Z → ProjectiveSpace A ι`, use the
native short exact sequence

```text
0 → kernel(structureModuleMap i) → O_P → i_* O_Z → 0.
```

The direct image is quasicoherent because `i` is affine. Its kernel is
quasicoherent by the native kernel theorem. The original zero-twist
cohomology and `twistingZeroIso` give `H^q(P,O_P)=0` for `q>0`. The two
standard affine charts give `H^(q+1)(P,J)=0` for the actual kernel `J`.
The native short exact cohomology consequence therefore kills
`H^q(P,i_*O_Z)`.

`projectiveEmbeddingCohomologyLinearEquiv` then identifies this with the
original `Sheaf.H` of the canonical structure module on `Z`. Its forward
map is the original `moduleCohomologyMapAlong i (identity i_*O_Z) q`;
the actual direct image and coefficient actions are retained.

The current consumer is positive structure cohomology of original
two-generator blowups in [RegularPoint](../Blowup/RegularPoint.md).
The actual Rees embedding and regular-point specialization belong to that
consumer; [Regular](../../Surfaces/RationalSingularities/Regular.md) assembles
the subsequent chain induction and original birational H1 injection.
This theorem requires no Noetherianity, field, completeness, Nagata,
normality, regularity, flatness or Cartier presentation.
