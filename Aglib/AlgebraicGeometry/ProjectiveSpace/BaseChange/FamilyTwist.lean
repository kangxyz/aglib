/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.ProjectiveSpace.BaseChange.Point
public import Aglib.AlgebraicGeometry.ProjectiveSpace.BaseChange.Twisting
public import Aglib.AlgebraicGeometry.Modules.Invertible.Pullback
public import Aglib.AlgebraicGeometry.Modules.Invertible.Affine

/-!
# The twisting sheaf of a family of projective spaces

Let `g : T ⟶ Spec A` and `X_T = P^n_A ×_{Spec A} T` (`pullback (toSpec A ι) g`). The twisting
sheaf `𝒪(r)` on `X_T` is the pullback of `𝒪(r)` on `P^n_A` along the first projection
(`familyTwistingSheaf ι g r`). It is locally of rank one
(`isLocallyRankOne_familyTwistingSheaf`), hence finite locally free, and it is compatible with
base change:

* `pointMapTwistingPullbackIso`: for `x : Spec B ⟶ T`, `(pointMap ι g x)^* 𝒪(r) ≅ 𝒪(r)` on
  `P^n_B`, through `pointMap_fst` and `twistingPullbackIso`;
* `baseChangeMapTwistingPullbackIso`: for `f : T' ⟶ T` over `Spec A`,
  `(baseChangeMap ι g g' f h)^* 𝒪(r) ≅ 𝒪(r)` on `X_{T'}`, through `baseChangeMap_fst`.

For an open immersion `x`, the point map is an open immersion (`isOpenImmersion_pointMap`), as
the base change of `x` (`isPullback_pointMap`).

This is the twist `E_T(r)` of Nitsure, *Construction of Hilbert and Quot schemes*,
arXiv:math/0504590v1, §5, pp. 25–26, for `E = 𝒪`, shared by the direct image of `𝒪_Z(r)`
(`HilbertScheme/DirectImageSheaf`) and the twisted ideal sheaf `I_Z(r)`
(`HilbertScheme/IdealTwist/Family`).
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.ProjectiveSpace

variable (ι : Type u) {A : Type u} [CommRing A] {T : Scheme.{u}}
  (g : T ⟶ Spec (CommRingCat.of A))

/-- The twisting sheaf `𝒪(r)` on `X_T = P^n_A ×_{Spec A} T`: the pullback of `𝒪(r)` on `P^n_A`
along the first projection. -/
abbrev familyTwistingSheaf (r : ℤ) : (pullback (toSpec A ι) g).Modules :=
  (Scheme.Modules.pullback (pullback.fst (toSpec A ι) g)).obj (twistingSheaf A ι r)

/-- `𝒪(r)` on `P^n_A ×_{Spec A} T` is locally of rank one. -/
theorem isLocallyRankOne_familyTwistingSheaf (r : ℤ) :
    Scheme.Modules.Invertible.IsLocallyRankOne (pullback (toSpec A ι) g)
      (familyTwistingSheaf ι g r) :=
  Scheme.Modules.Invertible.pullback_locallyRankOne _ _ (isLocallyRankOne_twistingSheaf A ι r)

instance isFiniteLocallyFree_familyTwistingSheaf (r : ℤ) :
    Scheme.Modules.IsFiniteLocallyFree (pullback (toSpec A ι) g) (familyTwistingSheaf ι g r) :=
  Scheme.Modules.Invertible.isFiniteLocallyFree_of_isLocallyRankOne
    (isLocallyRankOne_familyTwistingSheaf ι g r)

/-- The pullback of the twisting sheaf of `X_T` along a point map is the twisting sheaf of
`P^n_B`: `pointMap ι g x ≫ pullback.fst = map (pointRingHom g x) ι` (`pointMap_fst`) and
`twistingPullbackIso`. -/
def pointMapTwistingPullbackIso {B : Type u} [CommRing B] (x : Spec (CommRingCat.of B) ⟶ T)
    (r : ℤ) :
    (Scheme.Modules.pullback (pointMap ι g x)).obj (familyTwistingSheaf ι g r) ≅
      twistingSheaf B ι r :=
  (Scheme.Modules.pullbackComp (pointMap ι g x) (pullback.fst (toSpec A ι) g)).app _ ≪≫
    (Scheme.Modules.pullbackCongr (pointMap_fst ι g x)).app _ ≪≫
      twistingPullbackIso (pointRingHom g x) ι r

/-- The point map of an open immersion `x : Spec B ⟶ T` is an open immersion, as the base change
of `x` along `X_T ⟶ T` (`isPullback_pointMap`). -/
instance isOpenImmersion_pointMap {B : Type u} [CommRing B] (x : Spec (CommRingCat.of B) ⟶ T)
    [IsOpenImmersion x] : IsOpenImmersion (pointMap ι g x) :=
  MorphismProperty.of_isPullback (P := @IsOpenImmersion) (isPullback_pointMap ι g x).flip
    inferInstance

variable {g} {T' : Scheme.{u}} {g' : T' ⟶ Spec (CommRingCat.of A)} (f : T' ⟶ T)
  (h : f ≫ g = g')

/-- The pullback of the twisting sheaf of `X_T` along the base-changed map is the twisting sheaf
of `X_{T'}`: `baseChangeMap ι g g' f h ≫ pullback.fst = pullback.fst` (`baseChangeMap_fst`). -/
def baseChangeMapTwistingPullbackIso (r : ℤ) :
    (Scheme.Modules.pullback (baseChangeMap ι g g' f h)).obj (familyTwistingSheaf ι g r) ≅
      familyTwistingSheaf ι g' r :=
  (Scheme.Modules.pullbackComp (baseChangeMap ι g g' f h) (pullback.fst (toSpec A ι) g)).app _ ≪≫
    (Scheme.Modules.pullbackCongr (baseChangeMap_fst ι g g' f h)).app _

end AlgebraicGeometry.ProjectiveSpace
