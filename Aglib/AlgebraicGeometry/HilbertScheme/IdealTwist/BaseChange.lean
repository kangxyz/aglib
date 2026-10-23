/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.HilbertScheme.IdealTwist.DirectImage
public import Aglib.AlgebraicGeometry.Modules.BaseChange.CartesianInvertibility

/-!
# Base change of the direct image of the twisted ideal sheaf of a Hilbert family

Let `f : T' ⟶ T` be a morphism over `Spec A` (`f ≫ g = g'`) and
`b = baseChangeMap ι g g' f h : X_{T'} ⟶ X_T`, which exhibits `X_{T'}` as the base change of
`X_T ⟶ T` along `f` (`isPullback_baseChangeMap`). For a closed subscheme `Z ⊆ X_T` flat over `T`:

* `baseChangeMapIdealTwistIso`: `b^* I_Z(r) ≅ I_{Z'}(r)` for `Z' = Z.comap b`, through the tensor
  comparison, `b^* 𝒪(r) ≅ 𝒪(r)` (`baseChangeMap_fst`) and `b^* I_Z ≅ I_{Z'}`
  (`flatQuotient_idealPullbackMap_isIso`).

For a point `Z` of `Hilb^Φ(T)`, `T` locally Noetherian, and a natural
`r ≥ hilbertRegularityBound n Φ`:

* `IsHilbertFamily.isIso_cartesianBaseChangeMap_baseChangeMap_familyIdealTwist`: the base-change
  map of the cartesian square `isPullback_baseChangeMap` at `I_Z(r)` is invertible (from
  `IsHilbertFamily.isIso_moduleBaseChangeMap_familyIdealTwist` and
  `isIso_cartesianBaseChangeMap_of_isIso_moduleBaseChangeMap`);
* `IsHilbertFamily.pushforwardFamilyIdealTwistBaseChangeIso`: **`f^* π_* I_Z(r) ≅ π'_* I_{Z'}(r)`**,
  the compatibility of the direct image with base change used by the Grassmannian point (Nitsure,
  *Construction of Hilbert and Quot schemes*, arXiv:math/0504590v1, §5, p. 25, from (*) via
  Theorem 3.7, and p. 26, "Embedding Quot into Grassmannian").
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped Polynomial

universe u

namespace AlgebraicGeometry.ProjectiveSpace

variable (ι : Type u) {A : Type u} [CommRing A] {T T' : Scheme.{u}}
  {g : T ⟶ Spec (CommRingCat.of A)} {g' : T' ⟶ Spec (CommRingCat.of A)} (f : T' ⟶ T)
  (h : f ≫ g = g')

/-- **Base change of the ideal module of a flat family along `baseChangeMap`**: the canonical
map `b^* I_Z ⟶ I_{Z.comap b}` is an isomorphism (`flatQuotient_idealPullbackMap_isIso` on the
cartesian square `isPullback_baseChangeMap`). -/
theorem isIso_idealPullbackMap_baseChangeMap (Z : (pullback (toSpec A ι) g).IdealSheafData)
    [Flat (Z.subschemeι ≫ pullback.snd (toSpec A ι) g)] :
    IsIso (Scheme.Hom.idealPullbackMap Z.subschemeι
      (Z.comap (baseChangeMap ι g g' f h)).subschemeι (baseChangeMap ι g g' f h)
      (Scheme.IdealSheafData.subschemeMap (Z.comap (baseChangeMap ι g g' f h)) Z
        (baseChangeMap ι g g' f h) (Z.le_map_comap (baseChangeMap ι g g' f h)))
      (Scheme.IdealSheafData.subschemeMap_subschemeι _ _ _ _)) :=
  Scheme.Hom.flatQuotient_idealPullbackMap_isIso (pullback.snd (toSpec A ι) g) f
    (pullback.snd (toSpec A ι) g') (baseChangeMap ι g g' f h) Z.subschemeι _ _ _
    (isPullback_baseChangeMap ι g g' f h) (Z.isPullback_subschemeMap_comap _)

/-- The isomorphism `b^* I_Z ≅ I_{Z.comap b}` of `isIso_idealPullbackMap_baseChangeMap`. -/
def baseChangeMapIdealPullbackIso (Z : (pullback (toSpec A ι) g).IdealSheafData)
    [Flat (Z.subschemeι ≫ pullback.snd (toSpec A ι) g)] :
    (Scheme.Modules.pullback (baseChangeMap ι g g' f h)).obj
        (Scheme.Hom.idealModule Z.subschemeι) ≅
      Scheme.Hom.idealModule (Z.comap (baseChangeMap ι g g' f h)).subschemeι :=
  haveI := isIso_idealPullbackMap_baseChangeMap ι f h Z
  asIso (Scheme.Hom.idealPullbackMap Z.subschemeι
    (Z.comap (baseChangeMap ι g g' f h)).subschemeι (baseChangeMap ι g g' f h)
    (Scheme.IdealSheafData.subschemeMap (Z.comap (baseChangeMap ι g g' f h)) Z
      (baseChangeMap ι g g' f h) (Z.le_map_comap (baseChangeMap ι g g' f h)))
    (Scheme.IdealSheafData.subschemeMap_subschemeι _ _ _ _))

-- The `IsIso` instance of the tensor comparison matches only up to the presentations of the
-- module-sheaf tensor, as in `twistingTensorPullbackIso`.
set_option backward.isDefEq.respectTransparency false in
/-- **Base change of `I_Z(r)`**: for `Z ⊆ X_T` flat over `T`,
`(baseChangeMap ι g g' f h)^* I_Z(r) ≅ I_{Z.comap b}(r)` on `X_{T'}`. -/
def baseChangeMapIdealTwistIso (Z : (pullback (toSpec A ι) g).IdealSheafData)
    [Flat (Z.subschemeι ≫ pullback.snd (toSpec A ι) g)] (r : ℤ) :
    (Scheme.Modules.pullback (baseChangeMap ι g g' f h)).obj (familyIdealTwist ι g Z r) ≅
      familyIdealTwist ι g' (Z.comap (baseChangeMap ι g g' f h)) r :=
  haveI := Scheme.Modules.Pullback.Tensor.pullbackTensorMap_isIso (baseChangeMap ι g g' f h)
    (familyTwistingSheaf ι g r) (Scheme.Hom.idealModule Z.subschemeι)
  asIso (Scheme.Modules.pullbackTensorMap (baseChangeMap ι g g' f h) (familyTwistingSheaf ι g r)
      (Scheme.Hom.idealModule Z.subschemeι)) ≪≫
    Scheme.Modules.tensorSheafIso _ (baseChangeMapTwistingPullbackIso ι f h r)
      (baseChangeMapIdealPullbackIso ι f h Z)

variable {Φ : ℚ[X]} {Z : (pullback (toSpec A ι) g).IdealSheafData} (n : ℕ) (e : ι ≃ Fin (n + 1))

include e in
/-- **The base-change map of `π_* I_Z(r)` along `baseChangeMap` is invertible** for a point `Z`
of `Hilb^Φ(T)`, `T` locally Noetherian, and a natural `r ≥ hilbertRegularityBound n Φ`. -/
theorem IsHilbertFamily.isIso_cartesianBaseChangeMap_baseChangeMap_familyIdealTwist
    [IsLocallyNoetherian T] (hZ : IsHilbertFamily ι Φ g Z) (r : ℕ)
    (hr : hilbertRegularityBound n Φ ≤ r) :
    IsIso ((Scheme.Modules.cartesianBaseChangeMap (baseChangeMap ι g g' f h)
      (pullback.snd (toSpec A ι) g') (pullback.snd (toSpec A ι) g) f
        (isPullback_baseChangeMap ι g g' f h)).app (familyIdealTwist ι g Z r)) :=
  Scheme.Modules.isIso_cartesianBaseChangeMap_of_isIso_moduleBaseChangeMap _ _ _ _ _ _
    (hZ.isIso_moduleBaseChangeMap_familyIdealTwist ι n e r hr f)

include e in
/-- **The direct image `π_* I_Z(r)` commutes with base change** (Nitsure, arXiv:math/0504590v1,
§5, p. 25, from (*) via Theorem 3.7): for a point `Z` of `Hilb^Φ(T)`, `T` locally Noetherian, a
natural `r ≥ hilbertRegularityBound n Φ` and `f : T' ⟶ T` over `Spec A`,
`f^* π_* I_Z(r) ≅ π'_* I_{Z'}(r)` for `Z' = Z.comap (baseChangeMap ι g g' f h)`: the base-change
map of `isPullback_baseChangeMap` followed by `π'_*` of `baseChangeMapIdealTwistIso`. -/
def IsHilbertFamily.pushforwardFamilyIdealTwistBaseChangeIso [IsLocallyNoetherian T]
    (hZ : IsHilbertFamily ι Φ g Z) (r : ℕ) (hr : hilbertRegularityBound n Φ ≤ r) :
    (Scheme.Modules.pullback f).obj
        ((Scheme.Modules.pushforward (pullback.snd (toSpec A ι) g)).obj
          (familyIdealTwist ι g Z r)) ≅
      (Scheme.Modules.pushforward (pullback.snd (toSpec A ι) g')).obj
        (familyIdealTwist ι g' (Z.comap (baseChangeMap ι g g' f h)) r) :=
  haveI := hZ.isIso_cartesianBaseChangeMap_baseChangeMap_familyIdealTwist ι f h n e r hr
  haveI := hZ.flat
  asIso ((Scheme.Modules.cartesianBaseChangeMap (baseChangeMap ι g g' f h)
      (pullback.snd (toSpec A ι) g') (pullback.snd (toSpec A ι) g) f
        (isPullback_baseChangeMap ι g g' f h)).app (familyIdealTwist ι g Z r)) ≪≫
    (Scheme.Modules.pushforward (pullback.snd (toSpec A ι) g')).mapIso
      (baseChangeMapIdealTwistIso ι f h Z r)

end AlgebraicGeometry.ProjectiveSpace
