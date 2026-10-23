/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.HilbertScheme.Affine
public import Aglib.AlgebraicGeometry.ProjectiveSpace.BaseChange.FamilyTwist
public import Aglib.AlgebraicGeometry.Modules.Pullback.Tensor.Isomorphism

/-!
# The twisted ideal sheaf of a family over a general base and its affine pieces

Let `g : T ⟶ Spec A` and `X_T = P^n_A ×_{Spec A} T` (`pullback (toSpec A ι) g`). For a closed
subscheme `Z ⊆ X_T`, with the twisting sheaf `𝒪(r) = familyTwistingSheaf ι g r` on `X_T`
(`ProjectiveSpace/BaseChange/FamilyTwist`), this file defines

* `familyIdealTwist ι g Z r = 𝒪(r) ⊗ I_Z`, the twisted ideal module of `Z`, and the twisted
  sequence `familyTwistedShortComplex ι g Z r : I_Z(r) ⟶ 𝒪(r) ⊗ 𝒪 ⟶ 𝒪_Z(r)`.

For a ring `B` and `x : Spec B ⟶ T`, the point map `pointMap ι g x : P^n_B ⟶ X_T` exhibits `P^n_B`
as the base change of `X_T ⟶ T` along `x` (`isPullback_pointMap`). When `Z` is flat over `T`:

* `pointMapIdealPullbackIso`: `(pointMap ι g x)^* I_Z ≅ I_{Z_x}` for
  `Z_x = Z.comap (pointMap ι g x)` (`flatQuotient_idealPullbackMap_isIso`);
* `pointMapIdealTwistIso`: `(pointMap ι g x)^* I_Z(r) ≅ idealTwist ι Z_x r`, the twisted ideal
  module of `Z_x ⊆ P^n_B` of `HilbertScheme/DirectImage`, through the tensor comparison
  (`pullbackTensorMap_isIso`) and the base change of the twisting sheaves (`twistingPullbackIso`).

For an open immersion `x`, the point map is an open immersion (`isOpenImmersion_pointMap`, in
`ProjectiveSpace/BaseChange/FamilyTwist`); over the affine opens of `T` these maps cover `X_T`.

These identify the pieces of `I_Z(r)` over affine opens and fibers of `T` with the objects of the
affine theory (`HilbertScheme/Affine`), as used in Nitsure, *Construction of Hilbert and Quot
schemes*, arXiv:math/0504590v1, §5, pp. 26–27.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.ProjectiveSpace

variable (ι : Type u) {A : Type u} [CommRing A] {T : Scheme.{u}}
  (g : T ⟶ Spec (CommRingCat.of A))

/-- The twisted ideal module `I_Z(r) = 𝒪(r) ⊗ I_Z` of a closed subscheme `Z` of
`X_T = P^n_A ×_{Spec A} T`. -/
abbrev familyIdealTwist (Z : (pullback (toSpec A ι) g).IdealSheafData) (r : ℤ) :
    (pullback (toSpec A ι) g).Modules :=
  (Scheme.Modules.moduleTensorLeftFunctor (pullback (toSpec A ι) g)
    (familyTwistingSheaf ι g r)).obj (Scheme.Hom.idealModule Z.subschemeι)

/-- The twisted sequence `I_Z(r) ⟶ 𝒪(r) ⊗ 𝒪 ⟶ 𝒪_Z(r)` of a closed subscheme `Z` of `X_T`. -/
abbrev familyTwistedShortComplex (Z : (pullback (toSpec A ι) g).IdealSheafData) (r : ℤ) :
    ShortComplex (pullback (toSpec A ι) g).Modules :=
  Z.shortComplex.map
    (Scheme.Modules.moduleTensorLeftFunctor (pullback (toSpec A ι) g) (familyTwistingSheaf ι g r))

variable {g}

/-- **Base change of the ideal module of a flat family to an affine piece**: for `Z ⊆ X_T` flat
over `T` and `x : Spec B ⟶ T`, the canonical map from the pullback of `I_Z` along
`pointMap ι g x` to the ideal module of `Z.comap (pointMap ι g x)` is an isomorphism
(`flatQuotient_idealPullbackMap_isIso` on the cartesian square `isPullback_pointMap`). -/
theorem isIso_idealPullbackMap_pointMap (Z : (pullback (toSpec A ι) g).IdealSheafData)
    [Flat (Z.subschemeι ≫ pullback.snd (toSpec A ι) g)] {B : Type u} [CommRing B]
    (x : Spec (CommRingCat.of B) ⟶ T) :
    IsIso (Scheme.Hom.idealPullbackMap Z.subschemeι (Z.comap (pointMap ι g x)).subschemeι
      (pointMap ι g x)
      (Scheme.IdealSheafData.subschemeMap (Z.comap (pointMap ι g x)) Z (pointMap ι g x)
        (Z.le_map_comap (pointMap ι g x)))
      (Scheme.IdealSheafData.subschemeMap_subschemeι _ _ _ _)) :=
  Scheme.Hom.flatQuotient_idealPullbackMap_isIso (pullback.snd (toSpec A ι) g) x (toSpec B ι)
    (pointMap ι g x) Z.subschemeι _ _ _ (isPullback_pointMap ι g x)
    (Z.isPullback_subschemeMap_comap _)

/-- The isomorphism `(pointMap ι g x)^* I_Z ≅ I_{Z_x}` of `isIso_idealPullbackMap_pointMap`. -/
def pointMapIdealPullbackIso (Z : (pullback (toSpec A ι) g).IdealSheafData)
    [Flat (Z.subschemeι ≫ pullback.snd (toSpec A ι) g)] {B : Type u} [CommRing B]
    (x : Spec (CommRingCat.of B) ⟶ T) :
    (Scheme.Modules.pullback (pointMap ι g x)).obj (Scheme.Hom.idealModule Z.subschemeι) ≅
      Scheme.Hom.idealModule (Z.comap (pointMap ι g x)).subschemeι :=
  haveI := isIso_idealPullbackMap_pointMap ι Z x
  asIso (Scheme.Hom.idealPullbackMap Z.subschemeι (Z.comap (pointMap ι g x)).subschemeι
    (pointMap ι g x)
    (Scheme.IdealSheafData.subschemeMap (Z.comap (pointMap ι g x)) Z (pointMap ι g x)
      (Z.le_map_comap (pointMap ι g x)))
    (Scheme.IdealSheafData.subschemeMap_subschemeι _ _ _ _))

-- The `IsIso` instance of the tensor comparison matches only up to the presentations of the
-- module-sheaf tensor, as in `twistingTensorPullbackIso`.
set_option backward.isDefEq.respectTransparency false in
/-- **The pullback of `I_Z(r)` to an affine piece** (Nitsure, arXiv:math/0504590v1, §5, p. 26):
for `Z ⊆ X_T` flat over `T` and `x : Spec B ⟶ T`,
`(pointMap ι g x)^* I_Z(r) ≅ idealTwist ι (Z.comap (pointMap ι g x)) r` on `P^n_B`. -/
def pointMapIdealTwistIso (Z : (pullback (toSpec A ι) g).IdealSheafData)
    [Flat (Z.subschemeι ≫ pullback.snd (toSpec A ι) g)] {B : Type u} [CommRing B]
    (x : Spec (CommRingCat.of B) ⟶ T) (r : ℤ) :
    (Scheme.Modules.pullback (pointMap ι g x)).obj (familyIdealTwist ι g Z r) ≅
      idealTwist ι (Z.comap (pointMap ι g x)) r :=
  haveI := Scheme.Modules.Pullback.Tensor.pullbackTensorMap_isIso (pointMap ι g x)
    (familyTwistingSheaf ι g r) (Scheme.Hom.idealModule Z.subschemeι)
  asIso (Scheme.Modules.pullbackTensorMap (pointMap ι g x) (familyTwistingSheaf ι g r)
      (Scheme.Hom.idealModule Z.subschemeι)) ≪≫
    Scheme.Modules.tensorSheafIso _ (pointMapTwistingPullbackIso ι g x r)
      (pointMapIdealPullbackIso ι Z x)

end AlgebraicGeometry.ProjectiveSpace
