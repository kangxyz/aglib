/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.HilbertScheme.Immersed.Representability
public import Aglib.AlgebraicGeometry.HilbertScheme.QuasiProjective

/-!
# The Hilbert scheme of a locally closed subscheme of projective space is quasi-projective

Let `A` be a Noetherian ring, `ι ≃ Fin (n + 1)`, `Φ ∈ ℚ[X]`, `r ≥ hilbertRegularityBound n Φ` a
natural number, `φ : 𝒪^J ⟶ 𝒪(r)` sections and `i : Y ⟶ P^n_A` an immersion. The Hilbert scheme
`H^Φ_Y = immersedHilbertScheme ι n e A Φ r hr φ i` (`HilbertScheme/Immersed/Representability`;
it represents the Hilbert functor of `Y` when the section pairing of `φ` cuts out the
scheme-theoretic image of `i`) is H-quasi-projective over `Spec A`
(`isHQuasiProjective_immersedHilbertSchemeOver_hom`): `immersedHilbertSchemeι` is an immersion
(an open immersion into the closed subscheme `H_C`, followed by the closed immersion into the
Hilbert scheme `H` of `P^n_A`), every immersion into an H-quasi-projective scheme over a Noetherian
ring is H-quasi-projective (`IsHQuasiProjective.comp_of_isImmersion`), and `H` is H-quasi-projective
(`isHQuasiProjective_hilbertSchemeOver_hom`, through the Grassmannian and the Plücker embedding).
In particular `H^Φ_Y` is separated and of finite type over `Spec A`.

Source: Nitsure, *Construction of Hilbert and Quot schemes*, arXiv:math/0504590v1, Theorem 6.1,
p. 28 (the Hilbert scheme "can be embedded over `S` as a locally closed subscheme of `P(F)`"), for
`E = 𝒪_Y` and trivial bundles, so that `P(F)` is a projective space over `Spec A`;
H-quasi-projective is Stacks, Definition 29.41.1 (Tag 01VW), over the affine base `Spec A`
(`ProjectiveSpace/QuasiProjective`). Nitsure's embedding is through his `Quot` scheme of the
closure; here it is the immersion into the Hilbert scheme of `P^n_A`.
-/

@[expose] public section

noncomputable section

open CategoryTheory
open scoped Polynomial

universe u

namespace AlgebraicGeometry.ProjectiveSpace

variable (ι : Type u) (n : ℕ) (e : ι ≃ Fin (n + 1)) (A : Type u) [CommRing A]
  [IsNoetherianRing A] (Φ : ℚ[X]) (r : ℕ) (hr : hilbertRegularityBound n Φ ≤ r) {J : Type u}
  (φ : SheafOfModules.free (R := (ProjectiveSpace A ι).ringCatSheaf) J ⟶
    twistingSheaf A ι (r : ℤ))
  {Y : Scheme.{u}} (i : Y ⟶ ProjectiveSpace A ι) [IsImmersion i]

/-- **The Hilbert scheme of a locally closed subscheme of `P^n_A` is H-quasi-projective over
`Spec A`** (Nitsure, arXiv:math/0504590v1, Theorem 6.1, p. 28, for `E = 𝒪_Y` and trivial
bundles): it is a locally closed subscheme of the H-quasi-projective Hilbert scheme of `P^n_A`. -/
instance isHQuasiProjective_immersedHilbertSchemeOver_hom :
    IsHQuasiProjective (immersedHilbertSchemeOver ι n e A Φ r hr φ i).obj.hom := by
  rw [← Over.w (immersedHilbertSchemeToHilbertScheme ι n e A Φ r hr φ i).hom]
  have : IsImmersion (immersedHilbertSchemeToHilbertScheme ι n e A Φ r hr φ i).hom.left :=
    isImmersion_immersedHilbertSchemeι ι n e A Φ r hr φ i
  exact IsHQuasiProjective.comp_of_isImmersion _ _

end AlgebraicGeometry.ProjectiveSpace
