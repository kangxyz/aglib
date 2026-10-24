# Splitting from a concrete finite normal graph

`Scheme.ProjectiveBundle.RankTwoExtension.splitting_of_finite_normal_graph`
splits an actual extension

```text
0 → O_X --i→ E --g→ O_X → 0
```

from a supplied finite map `h : N ⟶ P(E)` into its original projective
bundle. The original quotient section is `σ : X ⟶ P(E)` and the original
projection is `π : P(E) ⟶ X`.

The theorem assumes that `A` is a normal Noetherian local domain of
dimension two, `f : X ⟶ Spec A` is proper dominant birational, and `X`
and `N` are integral and normal. For the literal map `r = h ≫ π`, it
retains dominance and invertibility of the original function-field map.
It further assumes that `h(N)` is not contained in `σ(X)` and that every
point of the actual intersection `Z = X ×_(P(E)) N` lies over the closed
point under `r ≫ f`.

The canonical pullback map from the ideal of `σ` to the actual ideal of
`Z` is invertible because `N` is integral and its image avoids the divisor
at some point. The original quotient-section conormal trivialization then
trivializes the actual conormal of `Z`. If `Z` were nonempty, this would
contradict the native vertical Cartier theorem. This is the obstruction of
[Stacks Lemma 54.7.4 (0AXA)](https://stacks.math.columbia.edu/tag/0AXA).

Thus `h` factors through the original open complement of `σ`. That
complement is affine over `X`; since `h` is finite, the factorization and
then `r` are affine. The original proper birational structure-sheaf map
of `r` is invertible because `X` is normal. Its affine chart maps are
therefore isomorphisms, so `r` is an isomorphism. The resulting actual
section of the complement gives `globalComplementSplitting` for the
original short exact complex.

For the intended application, `τ` is the complementary section on the
punctured open, `W = τ.image` is its actual schematic image, and
`ν : N ⟶ W` is a concrete finite normalization. Use
`h = ν ≫ τ.imageι`. The graph still has to supply the original birational
map, avoidance, and verticality conditions. This is the conditional graph
step of [Stacks Lemma 54.7.5 (0AXB)](https://stacks.math.columbia.edu/tag/0AXB).

The theorem does not construct `ν` or itself prove punctured H1
injectivity, derived residue-field Hom vanishing, or a surface resolution.
There is no Nagata premise inside this conditional helper.
[Construction](ExtensionGraph/Construction.md) supplies the actual finite
normalization and the other graph inputs over a normal Nagata local
surface. Its complete-base corollary derives Nagata from the
complete-local dimension-two theorem; normality of an arbitrary local
ring is not substituted for that input.

Only the splitting theorem is public. The canonical Cartier/conormal
contradiction and the affine birational isomorphism argument are private
helpers for this consumer. The original projective bundle, ideal,
pullback square, open factorization, and function-field maps remain visible
in the statement and proof.
