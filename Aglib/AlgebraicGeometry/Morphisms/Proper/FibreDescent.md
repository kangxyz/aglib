# Descent along proper fibres

`existsUnique_factor_of_isProper_of_isIso_c` proves the following actual
factorization. Let `f : X ⟶ Y` be proper and surjective, and suppose the original
structure-sheaf map `f.c` is an isomorphism. For an arbitrary scheme `Z` and an
actual `g : X ⟶ Z` satisfying
`∀ x₁ x₂, f x₁ = f x₂ → g x₁ = g x₂`, there is a unique actual scheme morphism
`h : Y ⟶ Z` with `f ≫ h = g`.

No Noetherianity, normality, flatness or separation of `Z` is required. The
structure-sheaf isomorphism is the actual independent hypothesis; it can, for
example, be supplied by the proved normal-target birational-functions theorem.
Neither descent existence nor a desired factorization is taken as input.

Properness and surjectivity make the original underlying continuous map a
quotient map. The pointwise hypothesis therefore gives the actual descended
continuous map `b`. For this fixed `b`, the structural morphism is constructed
as the original `g.c` followed by the pushforward along `b` of `inv f.c`.
The actual composition is `g`, and cancellation of the pushforward of `f.c`
proves uniqueness of the whole structural morphism.

For each original `y`, choose `x` with `f x = y`. The composite of the descended
stalk map with the original `f.stalkMap x` is the stalk map of `g`, which is
local. The native local-homomorphism reflection lemma proves that the descended
stalk map is local. This constructs a scheme morphism, beyond its continuous
map. Surjectivity identifies the underlying map of every competing factor;
structural-map cancellation then gives full scheme-morphism uniqueness.

The primary geometric locator is [Stacks Tag 0C5J, Lemma 54.16.1](https://stacks.math.columbia.edu/tag/0C5J).
This module proves its descent mechanism for an actual given proper quotient
with the actual structure-sheaf isomorphism. It supplies no contraction
existence, blowdown construction or factorization into point blowups.
