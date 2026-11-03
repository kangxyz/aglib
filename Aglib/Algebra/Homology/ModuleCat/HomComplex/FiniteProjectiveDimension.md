# Finite projective dimension of the same canonical homology

Let `q:R→S` be a finite map of commutative rings, with `R` regular local
of specified finite dimension and `S` Noetherian. Assume the original
ambient Ext from the restricted regular `S` module to `R` is concentrated
in degree `n`. Let `K` be the same degree-`n` homology of the installed
D+ coinduction of `R`.

`coinducedHomology_hasProjectiveDimensionLE` proves

`injdim_S(S) ≤ dS  ⇒  pdim_S(K) ≤ dS+n`.

The hypotheses use native injective and projective dimension. No
Gorenstein definition containing a canonical trivialization is introduced.
Locality or normality of `S` is not needed for this finite-dimension step.

The proof retains one actual coinduced injective resolution. Original
Hom/Ext comparisons put the dual of each finite module `L` in degrees
`[0,dim R]`; the existing signed shift comparison puts the dual of `L[i]`
in `[i,dim R+i]`. The original concentrated homothety identifies the dual
of `K` with `S[0][-n]`. Finite-injective-dimension vanishing therefore
kills a dualized Ext morphism when `i>dS+n`. The existing
`derivedDual_map_eq_zero_iff` detects that original morphism using the
actual bidual evaluation at the shifted finite target. Finally the native
finite-target Ext criterion yields the displayed projective-dimension bound.

Restriction of finite `S`-modules is proved finite by native finite-module
transitivity and the original restriction scalar tower, not by assuming
surjectivity or projectivity of `q`. No global duality or shift-coherence
instance, terminal projective resolution, or perfect model is a premise.
The original ambient Ext and both selected derived-category sizes are
retained. Projectivity and rank-one triviality require the separate
positive-self-Ext and local-ring arguments; they are not conclusions of
this leaf alone.
