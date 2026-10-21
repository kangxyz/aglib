/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.RationalPoint.LocalTriangles
public import Aglib.AlgebraicGeometry.RationalPoint.SmoothCurve
public import Aglib.AlgebraicGeometry.FunctionField.AffineCharts

/-!
# The actual scalar triangles at rational points

Source: `R5Lab.Aglib.AlgebraicGeometry.Stalk.RationalSectionConstants`, revision
`f8a3314ddecffcada2ec721d26d56a937bed9690`,
SHA-256 `31fc1fc3ca61dd9ec761992a8ab59bcbb217fdcc53253ef3eabbd779a277e810`, selected lines [[21,
109]].
The actual scheme objects, canonical maps, universes and conditions are retained.
-/

@[expose] public section

noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
universe u
namespace AlgebraicGeometry.Scheme.RationalPoint

/-- A commuting ring-map triangle gives its literal contravariant affine-scheme triangle. -/
theorem affine_triangle (F : Type u) [Field F]
    {R T : Type u} [CommRing R] [CommRing T]
    (i : F →+* R) (j : F →+* T) (f : R →+* T) (h : f.comp i = j) :
    Spec.map (CommRingCat.ofHom f) ≫ Spec.map (CommRingCat.ofHom i) =
      Spec.map (CommRingCat.ofHom j) := by
  rw [← Spec.map_comp]
  exact congrArg (fun a : F →+* T => Spec.map (CommRingCat.ofHom a)) h

variable {F : Type u} [Field F] {X : Scheme.{u}} (q : RationalPoint F X)

/-- The existing canonical field-stalk identification has the actual local-spectrum map. -/
theorem fieldStalkIso_spec (x : Spec (.of F)) :
    Spec.map (fieldStalkIso F x).inv = (Spec (.of F)).fromSpecStalk x := by
  have hx : x = IsLocalRing.closedPoint F := Subsingleton.elim _ _
  subst x
  change Spec.map ((stalkClosedPointIso (.of F)).inv ≫
      (Spec (.of F)).presheaf.stalkSpecializes
        (specializes_refl (IsLocalRing.closedPoint F))) = _
  rw [TopCat.Presheaf.stalkSpecializes_refl, Category.comp_id]
  exact Spec_stalkClosedPointIso (.of F)

/-- The original stalk's structural arrow is exactly Spec of its canonical constants map. -/
theorem origin_constants_triangle :
    X.fromSpecStalk q.point ≫ q.structureMap = Spec.map (CommRingCat.ofHom q.constants) := by
  rw [← Scheme.SpecMap_stalkMap_fromSpecStalk]
  rw [← fieldStalkIso_spec]
  rw [← Spec.map_comp]
  rfl

variable [IsIntegral X]

/-- Constants through the actual rational-point stalk equal the original global generic germ. -/
theorem origin_fraction_constants :
    (algebraMap q.localRing X.functionField).comp q.constants =
      Scheme.functionFieldConstants X q.structureMap := by
  apply CommRingCat.hom_ext_iff.mp
  apply Spec.map_injective
  change Spec.map (CommRingCat.ofHom
    ((algebraMap q.localRing X.functionField).comp q.constants)) = _
  calc
    _ = Spec.map (CommRingCat.ofHom (algebraMap q.localRing X.functionField)) ≫
        Spec.map (CommRingCat.ofHom q.constants) := by
      rw [← Spec.map_comp]
      rfl
    _ = Spec.map (CommRingCat.ofHom (algebraMap q.localRing X.functionField)) ≫
        (X.fromSpecStalk q.point ≫ q.structureMap) := by rw [origin_constants_triangle]
    _ = X.fromSpecStalk (genericPoint X) ≫ q.structureMap := by
      rw [← Category.assoc]
      congr 1
      exact Scheme.SpecMap_stalkSpecializes_fromSpecStalk (genericPoint_specializes q.point)
    _ = _ := (Scheme.functionFieldConstants_specMap q.structureMap).symm

variable [Smooth q.structureMap]

/-- Localizing the original smooth origin constants gives formal smoothness of its function field.
-/
theorem origin_fraction_formallySmooth :
    (Scheme.functionFieldConstants X q.structureMap).FormallySmooth := by
  rw [← origin_fraction_constants q]
  apply q.constants_formallySmooth.comp
  rw [RingHom.formallySmooth_algebraMap]
  exact Algebra.FormallySmooth.of_isLocalization (nonZeroDivisors q.localRing)

/-- The same actual function field is essentially finite type over the original field. -/
theorem origin_fraction_essFiniteType :
    (Scheme.functionFieldConstants X q.structureMap).EssFiniteType := by
  rw [← origin_fraction_constants q]
  apply q.constants_essFiniteType.comp
  rw [RingHom.essFiniteType_algebraMap]
  exact Algebra.EssFiniteType.of_isLocalization X.functionField (nonZeroDivisors q.localRing)

end AlgebraicGeometry.Scheme.RationalPoint
