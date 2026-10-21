/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.IdealPowers.Thickening
public import Aglib.AlgebraicGeometry.Modules.Pullback.UnitTriangle

/-!
# The original transition morphisms between ideal thickenings

Ideal inclusion gives the actual closed immersion of the smaller thickening.
The pushed coefficient map uses its original pullback unit and the native
composition comparisons. Naturality of the quotient comparison is proved
before taking cohomology, using the original quotient epimorphism.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.Modules

universe u
variable {A : Type u} [CommRing A] {X : Scheme.{u}}
  (f : X ⟶ Spec (CommRingCat.of A)) (F : X.Modules) {J K : Ideal A}

/-- Ideal inclusion gives the original morphism between quotient base schemes. -/
theorem idealThickeningBaseMap_comp (h : J ≤ K) :
    Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor h)) ≫
        Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)) =
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk K)) := by
  rw [← Spec.map_comp]
  congr 1

/-- The actual morphism from the `K` thickening to the `J` thickening. -/
def idealThickeningMap (h : J ≤ K) : idealThickeningSpace f K ⟶ idealThickeningSpace f J :=
  Limits.pullback.lift (idealThickeningι f K)
    (idealThickeningStructure f K ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor h)))
    (by rw [Category.assoc, idealThickeningBaseMap_comp]; exact Limits.pullback.condition)

@[reassoc (attr := simp)]
theorem idealThickeningMap_ι (h : J ≤ K) :
    idealThickeningMap f h ≫ idealThickeningι f J = idealThickeningι f K :=
  Limits.pullback.lift_fst _ _ _

/-- The actual coefficient comparison along the transition closed immersion. -/
def idealThickeningCoefficientIso (h : J ≤ K) :
    (pullback (idealThickeningMap f h)).obj (idealThickeningCoefficient f F J) ≅
      idealThickeningCoefficient f F K :=
  (pullbackComp (idealThickeningMap f h) (idealThickeningι f J)).app F ≪≫
    (pullbackCongr (idealThickeningMap_ι f h)).app F

/-- The actual coefficient arrow for geometric cohomology restriction. -/
def idealThickeningCoefficientMap (h : J ≤ K) :
    idealThickeningCoefficient f F J ⟶
      (pushforward (idealThickeningMap f h)).obj (idealThickeningCoefficient f F K) :=
  pullbackTriangleCoefficientMap F (idealThickeningι f J) (idealThickeningMap f h)
    (idealThickeningι f K) (idealThickeningMap_ι f h)

/-- Pushforward of the actual thickening coefficient transition, with its
original composition and equality comparisons. -/
def idealThickeningPushforwardMap (h : J ≤ K) :
    (pushforward (idealThickeningι f J)).obj (idealThickeningCoefficient f F J) ⟶
      (pushforward (idealThickeningι f K)).obj (idealThickeningCoefficient f F K) :=
  pullbackTrianglePushforwardMap F (idealThickeningι f J) (idealThickeningMap f h)
    (idealThickeningι f K) (idealThickeningMap_ι f h)

/-- The original geometric units commute with the actual thickening transition. -/
@[reassoc (attr := simp)]
theorem idealThickeningUnit_transition (h : J ≤ K) :
    idealThickeningUnit f F J ≫ idealThickeningPushforwardMap f F h =
      idealThickeningUnit f F K :=
  unit_pullbackTrianglePushforwardMap F (idealThickeningι f J) (idealThickeningMap f h)
    (idealThickeningι f K) (idealThickeningMap_ι f h)

variable [F.IsQuasicoherent]

/-- The canonical quotient/thickening comparison respects the original
coefficient reduction and geometric transition maps. -/
@[reassoc]
theorem idealQuotientThickeningIso_naturality (h : J ≤ K) :
    idealQuotientMap X
        (f.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom) F h ≫
        (idealQuotientThickeningIso f F K).hom =
      (idealQuotientThickeningIso f F J).hom ≫ idealThickeningPushforwardMap f F h := by
  apply (cancel_epi (idealQuotientπ X
    (f.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom) F J)).mp
  simp

end AlgebraicGeometry.Scheme.Modules
