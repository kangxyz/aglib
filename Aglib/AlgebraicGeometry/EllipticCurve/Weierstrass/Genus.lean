/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EllipticCurve.Weierstrass.Genus.Charts
public import Aglib.AlgebraicGeometry.Cohomology.MayerVietoris.StructuralFirstCohomology
public import Aglib.AlgebraicGeometry.Curves.Genus

/-!
# Arithmetic genus of every literal Weierstrass cubic

The canonical homogeneous basic-open section isomorphisms identify the actual
structural-field Mayer–Vietoris cokernel with the overlap quotient computed
in `Genus.Charts`. Original coherent H¹ is therefore the coefficient field,
including for singular equations and in every characteristic.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace WeierstrassCurve.Projective

open CategoryTheory AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme.Cohomology

universe u
variable {k : Type u} [Field k]

/-- The homogeneous basic open `Y ≠ 0` containing the original point at infinity. -/
abbrev infinityOpen (W : WeierstrassCurve k) : (curveOver W).left.Opens :=
  Proj.basicOpen (grading W) (coordinate W 1)

/-- The homogeneous basic open `Z ≠ 0` of the original affine Weierstrass chart. -/
abbrev affineOpen (W : WeierstrassCurve k) : (curveOver W).left.Opens :=
  Proj.basicOpen (grading W) (coordinate W 2)

/-- The structural field acts on sections of the original cubic over each open. -/
local instance (W : WeierstrassCurve k) (U : (curveOver W).left.Opens) :
    Module k Γ((curveOver W).left, U) :=
  structuralSectionModule (curveOver W) U

lemma basicOpenSections_inv_constant (W : WeierstrassCurve k)
    (f : homogeneousCoordinateRing W) {m : ℕ} (hf : f ∈ grading W m)
    (hm : 0 < m) (r : k) :
    (Proj.basicOpenIsoAway (grading W) f hf hm).inv
      (Scheme.constantSection (curveOver W) (Proj.basicOpen (grading W) f) r) =
        HomogeneousLocalization.fromZeroRingHom (grading W)
          (Submonoid.powers f) (constToGradeZero W r) := by
  rw [basicOpen_constantSection W f hf hm r]
  exact Iso.hom_inv_id_apply _ _

/-- Sections on `Y ≠ 0` identified with the original infinity-chart ring. -/
def infinitySectionsRingEquiv (W : WeierstrassCurve k) :
    Γ(scheme W, infinityOpen W) ≃+* infinityRing W :=
  (Proj.basicOpenIsoAway (grading W) (coordinate W 1) (coordinate_mem W 1)
    (by decide)).symm.commRingCatIsoToRingEquiv.trans (infinityChartRingEquiv W).symm

/-- Sections on `Z ≠ 0` identified with the original affine coordinate ring. -/
def affineSectionsRingEquiv (W : WeierstrassCurve k) :
    Γ(scheme W, affineOpen W) ≃+* affineRing W :=
  (Proj.basicOpenIsoAway (grading W) (coordinate W 2) (coordinate_mem W 2)
    (by decide)).symm.commRingCatIsoToRingEquiv.trans (affineChartRingEquiv W).symm

/-- Sections on the actual chart intersection identified with the infinity overlap ring. -/
def overlapSectionsRingEquiv (W : WeierstrassCurve k) :
    Γ(scheme W, infinityOpen W ⊓ affineOpen W) ≃+* infinityOverlapRing W :=
  (((curveOver W).left.presheaf.mapIso
      (eqToIso (Proj.basicOpen_mul (grading W) (coordinate W 1) (coordinate W 2))).op) ≪≫
    (Proj.basicOpenIsoAway (grading W) (coordinate W 1 * coordinate W 2)
      (SetLike.mul_mem_graded (coordinate_mem W 1) (coordinate_mem W 2))
      (by decide)).symm).commRingCatIsoToRingEquiv.trans (homogeneousOverlapEquiv W)

/-- The original infinity-chart section comparison preserves structural constants. -/
lemma infinitySectionsRingEquiv_constant (W : WeierstrassCurve k) (r : k) :
    infinitySectionsRingEquiv W (Scheme.constantSection (curveOver W) (infinityOpen W) r) =
      algebraMap k (infinityRing W) r := by
  change fromInfinityProjectiveChart W
    ((Proj.basicOpenIsoAway (grading W) (coordinate W 1) (coordinate_mem W 1) (by decide)).inv
      (Scheme.constantSection (curveOver W) (infinityOpen W) r)) = _
  rw [basicOpenSections_inv_constant]
  exact fromInfinityProjectiveChart_constant W r

/-- The original affine-chart section comparison preserves structural constants. -/
lemma affineSectionsRingEquiv_constant (W : WeierstrassCurve k) (r : k) :
    affineSectionsRingEquiv W (Scheme.constantSection (curveOver W) (affineOpen W) r) =
      algebraMap k (affineRing W) r := by
  change fromProjectiveChart W
    ((Proj.basicOpenIsoAway (grading W) (coordinate W 2) (coordinate_mem W 2) (by decide)).inv
      (Scheme.constantSection (curveOver W) (affineOpen W) r)) = _
  rw [basicOpenSections_inv_constant]
  exact fromProjectiveChart_constant W r

/-- The original overlap section comparison preserves structural constants. -/
lemma overlapSectionsRingEquiv_constant (W : WeierstrassCurve k) (r : k) :
    overlapSectionsRingEquiv W
      (Scheme.constantSection (curveOver W) (infinityOpen W ⊓ affineOpen W) r) =
        algebraMap k (infinityOverlapRing W) r := by
  change homogeneousOverlapEquiv W
    ((Proj.basicOpenIsoAway (grading W) (coordinate W 1 * coordinate W 2)
      (SetLike.mul_mem_graded (coordinate_mem W 1) (coordinate_mem W 2)) (by decide)).inv
      ((curveOver W).left.presheaf.map
        (eqToHom (Proj.basicOpen_mul (grading W) (coordinate W 1) (coordinate W 2))).op
        (Scheme.constantSection (curveOver W) (infinityOpen W ⊓ affineOpen W) r))) = _
  rw [Scheme.map_constantSection (curveOver W)
    (eqToHom (Proj.basicOpen_mul (grading W) (coordinate W 1) (coordinate W 2))) r,
    basicOpenSections_inv_constant]
  simpa only [affineChartToHomogeneousOverlap, chartConstant, RingHom.comp_apply,
    HomogeneousLocalization.awayMap_fromZeroRingHom] using
    homogeneousOverlapEquiv_affine_constant W r

/-- A ring equivalence preserving the original structural constants is linear
for the structural field action on sections of the same cubic. -/
def sectionsRingEquivLinear (W : WeierstrassCurve k) (U : (curveOver W).left.Opens)
    {B : Type u} [CommRing B] [Algebra k B] (e : Γ((curveOver W).left, U) ≃+* B)
    (he : ∀ r, e (Scheme.constantSection (curveOver W) U r) = algebraMap k B r) :
    Γ((curveOver W).left, U) ≃ₗ[k] B where
  __ := e.toAddEquiv
  map_smul' r a := by
    have hs : r • a = Scheme.constantSection (curveOver W) U r * a := rfl
    change e (r • a) = r • e a
    rw [hs, map_mul, he, Algebra.smul_def]

/-- The infinity-chart section comparison, linear for the original structural field. -/
def infinitySectionsLinearEquiv (W : WeierstrassCurve k) :
    Γ((curveOver W).left, infinityOpen W) ≃ₗ[k] infinityRing W :=
  sectionsRingEquivLinear W _ (infinitySectionsRingEquiv W)
    (infinitySectionsRingEquiv_constant W)

/-- The affine-chart section comparison, linear for the original structural field. -/
def affineSectionsLinearEquiv (W : WeierstrassCurve k) :
    Γ((curveOver W).left, affineOpen W) ≃ₗ[k] affineRing W :=
  sectionsRingEquivLinear W _ (affineSectionsRingEquiv W)
    (affineSectionsRingEquiv_constant W)

/-- The overlap section comparison, linear for the original structural field. -/
def overlapSectionsLinearEquiv (W : WeierstrassCurve k) :
    Γ((curveOver W).left, infinityOpen W ⊓ affineOpen W) ≃ₗ[k] infinityOverlapRing W :=
  sectionsRingEquivLinear W _ (overlapSectionsRingEquiv W)
    (overlapSectionsRingEquiv_constant W)

end WeierstrassCurve.Projective

namespace WeierstrassCurve.Projective

open CategoryTheory AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme.Cohomology

universe u
variable {k : Type u} [Field k]

/-- The structural field acts on sections of the original cubic over each open. -/
local instance (W : WeierstrassCurve k) (U : (curveOver W).left.Opens) :
    Module k Γ((curveOver W).left, U) :=
  structuralSectionModule (curveOver W) U

lemma overlapSectionsRingEquiv_restrict_infinity (W : WeierstrassCurve k)
    (a : Γ((curveOver W).left, infinityOpen W)) :
    overlapSectionsRingEquiv W
      ((curveOver W).left.presheaf.map (homOfLE (show infinityOpen W ⊓ affineOpen W ≤
        infinityOpen W from inf_le_left)).op a) =
      algebraMap (infinityRing W) (infinityOverlapRing W) (infinitySectionsRingEquiv W a) := by
  let eY := Proj.basicOpenIsoAway (grading W) (coordinate W 1) (coordinate_mem W 1) (by decide)
  let eP := Proj.basicOpenIsoAway (grading W) (coordinate W 1 * coordinate W 2)
    (SetLike.mul_mem_graded (coordinate_mem W 1) (coordinate_mem W 2)) (by decide)
  obtain ⟨b, rfl⟩ := eY.commRingCatIsoToRingEquiv.surjective a
  have ht : (curveOver W).left.presheaf.map
      (eqToHom (Proj.basicOpen_mul (grading W) (coordinate W 1) (coordinate W 2))).op
      ((curveOver W).left.presheaf.map (homOfLE (show infinityOpen W ⊓ affineOpen W ≤
        infinityOpen W from inf_le_left)).op (eY.hom b)) =
      eP.hom (infinityChartToHomogeneousOverlap W b) := by
    rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
    exact (ConcreteCategory.congr_hom (Proj.awayMap_awayToSection (grading W)
      (f := coordinate W 1) (coordinate_mem W 2) rfl) b).symm
  change homogeneousOverlapEquiv W (eP.inv
    ((curveOver W).left.presheaf.map
      (eqToHom (Proj.basicOpen_mul (grading W) (coordinate W 1) (coordinate W 2))).op
      ((curveOver W).left.presheaf.map (homOfLE
        (show infinityOpen W ⊓ affineOpen W ≤ infinityOpen W from inf_le_left)).op
        (eY.hom b)))) =
    algebraMap (infinityRing W) (infinityOverlapRing W)
      (fromInfinityProjectiveChart W (eY.inv (eY.hom b)))
  rw [ht, Iso.hom_inv_id_apply, Iso.hom_inv_id_apply]
  exact homogeneousOverlapEquiv_infinity W b

lemma overlapSectionsRingEquiv_restrict_affine (W : WeierstrassCurve k)
    (a : Γ((curveOver W).left, affineOpen W)) :
    overlapSectionsRingEquiv W
      ((curveOver W).left.presheaf.map (homOfLE (show infinityOpen W ⊓ affineOpen W ≤
        affineOpen W from inf_le_right)).op a) =
      affineToInfinityOverlap W (affineSectionsRingEquiv W a) := by
  let eZ := Proj.basicOpenIsoAway (grading W) (coordinate W 2) (coordinate_mem W 2) (by decide)
  let eP := Proj.basicOpenIsoAway (grading W) (coordinate W 1 * coordinate W 2)
    (SetLike.mul_mem_graded (coordinate_mem W 1) (coordinate_mem W 2)) (by decide)
  obtain ⟨b, rfl⟩ := eZ.commRingCatIsoToRingEquiv.surjective a
  have ht : (curveOver W).left.presheaf.map
      (eqToHom (Proj.basicOpen_mul (grading W) (coordinate W 1) (coordinate W 2))).op
      ((curveOver W).left.presheaf.map (homOfLE (show infinityOpen W ⊓ affineOpen W ≤
        affineOpen W from inf_le_right)).op (eZ.hom b)) =
      eP.hom (affineChartToHomogeneousOverlap W b) := by
    rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
    exact (ConcreteCategory.congr_hom (Proj.awayMap_awayToSection (grading W)
      (f := coordinate W 2) (coordinate_mem W 1) (mul_comm _ _)) b).symm
  change homogeneousOverlapEquiv W (eP.inv
    ((curveOver W).left.presheaf.map
      (eqToHom (Proj.basicOpen_mul (grading W) (coordinate W 1) (coordinate W 2))).op
      ((curveOver W).left.presheaf.map (homOfLE
        (show infinityOpen W ⊓ affineOpen W ≤ affineOpen W from inf_le_right)).op
        (eZ.hom b)))) =
    affineToInfinityOverlap W (fromProjectiveChart W (eZ.inv (eZ.hom b)))
  rw [ht, Iso.hom_inv_id_apply, Iso.hom_inv_id_apply]
  have h := DFunLike.congr_fun (homogeneousOverlapEquiv_affineMap W)
    (fromProjectiveChart W b)
  simpa only [RingHom.comp_apply, to_fromProjectiveChart,
    RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom] using h

lemma overlapSectionsLinearEquiv_restrict_infinity (W : WeierstrassCurve k) :
    (overlapSectionsLinearEquiv W).toLinearMap.comp
      (structuralRestrictionLinearMap (curveOver W)
        (show infinityOpen W ⊓ affineOpen W ≤ infinityOpen W from inf_le_left)) =
      (IsScalarTower.toAlgHom k (infinityRing W) (infinityOverlapRing W)).toLinearMap.comp
        (infinitySectionsLinearEquiv W).toLinearMap := by
  ext a
  exact overlapSectionsRingEquiv_restrict_infinity W a

lemma overlapSectionsLinearEquiv_restrict_affine (W : WeierstrassCurve k) :
    (overlapSectionsLinearEquiv W).toLinearMap.comp
      (structuralRestrictionLinearMap (curveOver W)
        (show infinityOpen W ⊓ affineOpen W ≤ affineOpen W from inf_le_right)) =
      (affineToInfinityOverlapAlgHom W).toLinearMap.comp
        (affineSectionsLinearEquiv W).toLinearMap := by
  ext a
  exact overlapSectionsRingEquiv_restrict_affine W a

/-- Transport of the native section cokernel through the canonical chart-section maps. -/
def twoAffineSectionsQuotientEquiv (W : WeierstrassCurve k) :
    (Γ((curveOver W).left, infinityOpen W ⊓ affineOpen W) ⧸
      (LinearMap.range (structuralRestrictionLinearMap (curveOver W)
        (show infinityOpen W ⊓ affineOpen W ≤ infinityOpen W from inf_le_left)) ⊔
      LinearMap.range (structuralRestrictionLinearMap (curveOver W)
        (show infinityOpen W ⊓ affineOpen W ≤ affineOpen W from inf_le_right)))) ≃ₗ[k]
      (infinityOverlapRing W ⧸ overlapChartSubmodule W) := by
  apply Submodule.Quotient.equiv _ _ (overlapSectionsLinearEquiv W)
  rw [Submodule.map_sup, ← LinearMap.range_comp, ← LinearMap.range_comp,
    overlapSectionsLinearEquiv_restrict_infinity, overlapSectionsLinearEquiv_restrict_affine,
    LinearMap.range_comp, LinearMap.range_comp, LinearEquiv.range, LinearEquiv.range,
    Submodule.map_top, Submodule.map_top, overlapChartSubmodule, sup_comm]

/-- Original structural-field H¹ of every literal Weierstrass cubic is the
coefficient field. No discriminant or smoothness hypothesis is used. -/
def curveOverH1Equiv (W : WeierstrassCurve k) :
    Scheme.coherentH1 k (curveOver W) ≃ₗ[k] k :=
  (structuralH1EquivTwoAffineQuotient (curveOver W) (infinityOpen W) (affineOpen W)
    (Proj.isAffineOpen_basicOpen _ _ (coordinate_mem W 1) (by decide))
    (Proj.isAffineOpen_basicOpen _ _ (coordinate_mem W 2) (by decide))
    (by simpa only [infinityAffineChart_range, affineChart_range] using
      infinity_affine_cover W)).trans
      ((twoAffineSectionsQuotientEquiv W).trans (overlapChartQuotientEquiv W))

/-- Arithmetic genus one for the same homogeneous-quotient Proj, including
singular Weierstrass cubics and all field characteristics. -/
theorem curveOver_coherentGenus (W : WeierstrassCurve k) :
    Scheme.OverField.Curve.coherentGenus k (curveOver W) = 1 :=
  (curveOverH1Equiv W).finrank_eq.trans (Module.finrank_self k)

end WeierstrassCurve.Projective
