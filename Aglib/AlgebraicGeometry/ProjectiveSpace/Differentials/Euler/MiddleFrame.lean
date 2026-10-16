/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.ProjectiveSpace.Differentials.Euler.PolynomialChart
public import Aglib.AlgebraicGeometry.Modules.Tensor.ToUnit

/-!
# The original Euler tensor middle frame on polynomial charts

The original inverse-coordinate twist frame, native tensor restriction, original left unitor,
and original coefficient free frame identify the actual Euler middle sheaf with the native
coordinate free sheaf. The original tensor generators and scalar actions are preserved.
-/

@[expose] public section
noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Opposite
open AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Modules.Invertible
universe u
attribute [local instance] MvPolynomial.gradedAlgebra

namespace AlgebraicGeometry.ProjectiveSpace
variable (R : Type u) [CommRing R] (ι : Type u)

/-- The original inverse twist frame on the actual restricted coordinate scheme. -/
def eulerInverseTwistOnPolynomialChartIso (i : ι) :
    (twistingSheaf R ι (-1)).restrict (eulerPolynomialChart R ι i) ≅
      SheafOfModules.unit
        (Spec (CommRingCat.of (MvPolynomial {j : ι // j ≠ i} R))).ringCatSheaf := by
  let X := Spec (CommRingCat.of (MvPolynomial {j : ι // j ≠ i} R))
  let g := eulerPolynomialChart R ι i
  let L := (twistingSheaf R ι (-1)).restrict g
  let e (V : X.Opens) :
      Γ(L, V) ≃ₗ[Γ(X, V)] Γ(X, V) := {
    toFun s := (g.appIso V).hom
      (twistingSectionsEquiv R ι (-1) i (eulerPolynomialChart_image_le R ι i V) s)
    invFun r := (twistingSectionsEquiv R ι (-1) i
      (eulerPolynomialChart_image_le R ι i V)).symm ((g.appIso V).inv r)
    left_inv s :=
      (congrArg (twistingSectionsEquiv R ι (-1) i
        (eulerPolynomialChart_image_le R ι i V)).symm
        (Iso.hom_inv_id_apply (g.appIso V)
          (twistingSectionsEquiv R ι (-1) i (eulerPolynomialChart_image_le R ι i V) s))).trans
        ((twistingSectionsEquiv R ι (-1) i
          (eulerPolynomialChart_image_le R ι i V)).symm_apply_apply s)
    right_inv r :=
      (congrArg (g.appIso V).hom
        ((twistingSectionsEquiv R ι (-1) i (eulerPolynomialChart_image_le R ι i V)).apply_symm_apply
          ((g.appIso V).inv r))).trans (Iso.inv_hom_id_apply (g.appIso V) r)
    map_add' s t :=
      (congrArg (g.appIso V).hom
        ((twistingSectionsEquiv R ι (-1) i
          (eulerPolynomialChart_image_le R ι i V)).map_add s t)).trans
        ((g.appIso V).hom.hom.map_add _ _)
    map_smul' r s := by
      let s' : Γ(twistingSheaf R ι (-1), g ''ᵁ V) := s
      let f := twistingSectionsEquiv R ι (-1) i (eulerPolynomialChart_image_le R ι i V)
      change (g.appIso V).hom (f (((g.appIso V).inv r) • s')) =
        r * (g.appIso V).hom (f s')
      have hf := f.map_smul ((g.appIso V).inv r) s'
      change f (((g.appIso V).inv r) • s') =
        ((g.appIso V).inv r) * f s' at hf
      exact (congrArg (g.appIso V).hom hf).trans
        (((g.appIso V).hom.hom.map_mul _ _).trans
          (congrArg (fun z => z * (g.appIso V).hom (f s'))
            (Iso.inv_hom_id_apply (g.appIso V) r))) }
  refine (SheafOfModules.fullyFaithfulForget X.ringCatSheaf).preimageIso
    (_root_.PresheafOfModules.isoMk (fun V => (e V.unop).toModuleIso) ?_)
  intro V W k
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro s
  exact (congrArg (g.appIso W.unop).hom
    (twistingSectionsEquiv_restrict R ι (-1) i
      (g.image_mono k.unop.le) (eulerPolynomialChart_image_le R ι i V.unop) s)).trans
    (ConcreteCategory.congr_hom (g.appIso_hom_naturality k) _)

/-- The original restricted inverse twist frame retains the original chart coefficient. -/
theorem eulerInverseTwistOnPolynomialChartIso_hom_app (i : ι)
    (V : (Spec (CommRingCat.of (MvPolynomial {j : ι // j ≠ i} R))).Opens)
    (s : Γ((twistingSheaf R ι (-1)).restrict (eulerPolynomialChart R ι i), V)) :
    (eulerInverseTwistOnPolynomialChartIso R ι i).hom.val.app (op V) s =
      ((eulerPolynomialChart R ι i).appIso V).hom
        (twistingSectionsEquiv R ι (-1) i (eulerPolynomialChart_image_le R ι i V) s) := by
  rfl

/-- The actual Euler middle sheaf is locally the original coefficient sheaf in the inverse
coordinate frame, using the native tensor restriction and original left unitor. -/
def eulerMiddleOnPolynomialChartIso (i : ι) :
    (eulerMiddle R ι).restrict (eulerPolynomialChart R ι i) ≅
      (eulerCoefficientSheaf R ι).restrict (eulerPolynomialChart R ι i) :=
  (tensorRestrictionIso (eulerPolynomialChart R ι i) (twistingSheaf R ι (-1))
    (eulerCoefficientSheaf R ι)).symm ≪≫
    ((SheafOfModulesOfCommRing.tensorFunctor
      (Spec (CommRingCat.of (MvPolynomial {j : ι // j ≠ i} R))).sheaf).mapIso
      (eulerInverseTwistOnPolynomialChartIso R ι i)).app
        ((eulerCoefficientSheaf R ι).restrict (eulerPolynomialChart R ι i)) ≪≫
    (SheafOfModulesOfCommRing.tensorLeftUnitIso
      (Spec (CommRingCat.of (MvPolynomial {j : ι // j ≠ i} R))).sheaf).app
      ((eulerCoefficientSheaf R ι).restrict (eulerPolynomialChart R ι i))


/-- The original inverse-coordinate tensor frame sends each original middle generator to the
same pulled-back coefficient generator. -/
theorem eulerMiddleOnPolynomialChartIso_hom_generator (i j : ι)
    (V : (Spec (CommRingCat.of (MvPolynomial {j : ι // j ≠ i} R))).Opens) :
    (eulerMiddleOnPolynomialChartIso R ι i).hom.app V
      (eulerMiddleGenerator R ι i j (eulerPolynomialChart_image_le R ι i V)) =
      (eulerCoefficientSection R ι j).val (op (eulerPolynomialChart R ι i ''ᵁ V)) := by
  let X := Spec (CommRingCat.of (MvPolynomial {j : ι // j ≠ i} R))
  let g := eulerPolynomialChart R ι i
  let L := twistingSheaf R ι (-1)
  let M := eulerCoefficientSheaf R ι
  let l : Γ(L.restrict g, V) :=
    twistingGenerator R ι (-1) i (eulerPolynomialChart_image_le R ι i V)
  let m : Γ(M.restrict g, V) := (eulerCoefficientSection R ι j).val (op (g ''ᵁ V))
  let t := moduleTensorSection X (L.restrict g) (M.restrict g) V l m
  let e := tensorRestrictionIso g L M
  let f := (eulerInverseTwistOnPolynomialChartIso R ι i).hom
  have ht : e.hom.app V t =
      eulerMiddleGenerator R ι i j (eulerPolynomialChart_image_le R ι i V) :=
    tensorRestrictionIso_section g L M V l m
  have hi : e.inv.app V
      (eulerMiddleGenerator R ι i j (eulerPolynomialChart_image_le R ι i V)) = t :=
    (congrArg (e.inv.app V) ht.symm).trans
      (congrArg (fun k => k.app V t) e.hom_inv_id)
  have hf : f.app V l = (1 : Γ(X, V)) :=
    (eulerInverseTwistOnPolynomialChartIso_hom_app R ι i V l).trans
      ((congrArg (g.appIso V).hom
        (twistingSectionsEquiv_generator R ι (-1) i
          (eulerPolynomialChart_image_le R ι i V))).trans (g.appIso V).hom.hom.map_one)
  have hunit : ((tensorToUnit f).app (M.restrict g)).app V t = m :=
    (tensorToUnit_section f (M.restrict g) V l m).trans
      ((congrArg (fun r : Γ(X, V) => r • m) hf).trans (one_smul _ _))
  change ((tensorToUnit f).app (M.restrict g)).app V
    (e.inv.app V (eulerMiddleGenerator R ι i j (eulerPolynomialChart_image_le R ι i V))) = m
  exact (congrArg (((tensorToUnit f).app (M.restrict g)).app V) hi).trans hunit

/-- The actual original Euler middle sheaf has its original coordinate free frame. -/
def eulerMiddlePolynomialFreeIso (i : ι) :
    (eulerMiddle R ι).restrict (eulerPolynomialChart R ι i) ≅
      SheafOfModules.free
        (R := (Spec (CommRingCat.of (MvPolynomial {j : ι // j ≠ i} R))).ringCatSheaf) ι := by
  letI : CategoryTheory.Limits.PreservesColimitsOfSize.{u, u}
      (Scheme.Modules.restrictFunctor (eulerPolynomialChart R ι i)) := inferInstance
  exact eulerMiddleOnPolynomialChartIso R ι i ≪≫
    (Scheme.Modules.restrictFunctor (eulerPolynomialChart R ι i)).mapIso
      (eulerCoefficientIsoFree R ι) ≪≫
    (SheafOfModules.mapFreeIso (Scheme.Modules.restrictFunctor (eulerPolynomialChart R ι i)) ι
      (Scheme.Modules.restrictUnitIso (eulerPolynomialChart R ι i)).symm).symm

/-- The native middle free frame preserves every original coordinate generator section. -/
theorem eulerMiddlePolynomialFreeIso_hom_generator (i j : ι)
    (V : (Spec (CommRingCat.of (MvPolynomial {j : ι // j ≠ i} R))).Opens) :
    (eulerMiddlePolynomialFreeIso R ι i).hom.app V
      (eulerMiddleGenerator R ι i j (eulerPolynomialChart_image_le R ι i V)) =
      (SheafOfModules.freeSection
        (R := (Spec (CommRingCat.of (MvPolynomial {j : ι // j ≠ i} R))).ringCatSheaf) j).val
          (op V) := by
  let X := Spec (CommRingCat.of (MvPolynomial {j : ι // j ≠ i} R))
  let g := eulerPolynomialChart R ι i
  let F := Scheme.Modules.restrictFunctor g
  let : CategoryTheory.Limits.PreservesColimitsOfSize.{u, u} F := inferInstance
  let η := (Scheme.Modules.restrictUnitIso g).symm
  let e := SheafOfModules.mapFreeIso F ι η
  have hc : (F.map (eulerCoefficientIsoFree R ι).hom).app V
      ((eulerCoefficientSection R ι j).val (op (g ''ᵁ V))) =
      (SheafOfModules.freeSection (R := (ProjectiveSpace R ι).ringCatSheaf) j).val
        (op (g ''ᵁ V)) :=
    congrArg (fun k => k.val.app (op (g ''ᵁ V))
      ((SheafOfModules.freeSection (R := (ProjectiveSpace R ι).ringCatSheaf) j).val
        (op (g ''ᵁ V)))) (eulerCoefficientIsoFree R ι).inv_hom_id
  have hu : (Scheme.Modules.restrictUnitIso g).hom.app V
      (1 : Γ(ProjectiveSpace R ι, g ''ᵁ V)) = (1 : Γ(X, V)) := by
    change (g.appIso V).hom 1 = 1
    exact (g.appIso V).hom.hom.map_one
  have hq := congrArg (fun k => k.val.app (op V) (1 : Γ(ProjectiveSpace R ι, g ''ᵁ V)))
    (SheafOfModules.map_ιFree_mapFreeIso_inv F ι η j)
  change e.inv.val.app (op V)
      ((SheafOfModules.freeSection (R := (ProjectiveSpace R ι).ringCatSheaf) j).val
        (op (g ''ᵁ V))) =
      (SheafOfModules.ιFree (R := X.ringCatSheaf) j).val.app (op V)
        ((Scheme.Modules.restrictUnitIso g).hom.app V
          (1 : Γ(ProjectiveSpace R ι, g ''ᵁ V))) at hq
  have hq' : e.inv.val.app (op V)
      ((SheafOfModules.freeSection (R := (ProjectiveSpace R ι).ringCatSheaf) j).val
        (op (g ''ᵁ V))) =
      (SheafOfModules.freeSection (R := X.ringCatSheaf) j).val (op V) :=
    hq.trans (congrArg ((SheafOfModules.ιFree (R := X.ringCatSheaf) j).val.app (op V)) hu)
  change e.inv.val.app (op V) ((F.map (eulerCoefficientIsoFree R ι).hom).app V
    ((eulerMiddleOnPolynomialChartIso R ι i).hom.app V
      (eulerMiddleGenerator R ι i j (eulerPolynomialChart_image_le R ι i V)))) = _
  exact (congrArg (fun z => e.inv.val.app (op V)
    ((F.map (eulerCoefficientIsoFree R ι).hom).app V z))
    (eulerMiddleOnPolynomialChartIso_hom_generator R ι i j V)).trans
      ((congrArg (e.inv.val.app (op V)) hc).trans hq')

/-- The native middle free frame converts the original chart scalar action through the
original structure-sheaf chart isomorphism. -/
theorem eulerMiddlePolynomialFreeIso_hom_smul (i : ι)
    (V : (Spec (CommRingCat.of (MvPolynomial {j : ι // j ≠ i} R))).Opens)
    (r : Γ(ProjectiveSpace R ι, eulerPolynomialChart R ι i ''ᵁ V))
    (m : Γ(eulerMiddle R ι, eulerPolynomialChart R ι i ''ᵁ V)) :
    (eulerMiddlePolynomialFreeIso R ι i).hom.app V (r • m) =
      ((eulerPolynomialChart R ι i).appIso V).hom r •
        (eulerMiddlePolynomialFreeIso R ι i).hom.app V m := by
  let g := eulerPolynomialChart R ι i
  let f := (eulerMiddlePolynomialFreeIso R ι i).hom
  let m' : Γ((eulerMiddle R ι).restrict g, V) := m
  have h := (f.val.app (op V)).hom.map_smul ((g.appIso V).hom r) m'
  change f.app V (((g.appIso V).inv ((g.appIso V).hom r)) • m) = _ at h
  exact (congrArg (fun a : Γ(ProjectiveSpace R ι, g ''ᵁ V) => f.app V (a • m))
    (Iso.hom_inv_id_apply (g.appIso V) r)).symm.trans h

/-- The original middle coordinate vector is recovered by the inverse native free frame. -/
theorem eulerMiddlePolynomialFreeIso_inv_freeSection (i j : ι)
    (V : (Spec (CommRingCat.of (MvPolynomial {j : ι // j ≠ i} R))).Opens) :
    (eulerMiddlePolynomialFreeIso R ι i).inv.app V
      ((SheafOfModules.freeSection
        (R := (Spec (CommRingCat.of (MvPolynomial {j : ι // j ≠ i} R))).ringCatSheaf) j).val
          (op V)) =
      eulerMiddleGenerator R ι i j (eulerPolynomialChart_image_le R ι i V) := by
  exact (congrArg ((eulerMiddlePolynomialFreeIso R ι i).inv.app V)
    (eulerMiddlePolynomialFreeIso_hom_generator R ι i j V).symm).trans
      (congrArg (fun k => k.val.app (op V)
        (eulerMiddleGenerator R ι i j (eulerPolynomialChart_image_le R ι i V)))
          (eulerMiddlePolynomialFreeIso R ι i).hom_inv_id)

end AlgebraicGeometry.ProjectiveSpace
