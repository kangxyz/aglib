/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Aglib.AlgebraicGeometry.ProjectiveSpace.Differentials.Euler.Gluing
public import Aglib.AlgebraicGeometry.Modules.ExteriorPower.LocallyFree
public import Aglib.AlgebraicGeometry.Modules.LocallyFree.FreeCover.Sections
public import Aglib.AlgebraicGeometry.Modules.Invertible.TensorFunctorAssociator.Sections
public import Mathlib.Logic.Equiv.Fin.Basic
/-!
# Original projective differential determinant chart frames

The actual relative top exterior sheaf has an ordered original ratio-differential
frame on each coordinate open. The target retains the actual top exterior power
of the original degree-one coefficient module and the original tensor orientation.
The pivot-first sign is proved by the original coefficient determinant. The
coefficient ring is arbitrary, and dimension zero is included.
-/

@[expose] public section
noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
namespace AlgebraicGeometry.ProjectiveSpace
variable (R : Type u) [CommRing R] (ι : Type u)

/-- The original coordinate-open chart map composes to its original open immersion. -/
theorem determinantCoordinateChart_comp (i : ι) :
    (coordinateOpenIsoSpecPolynomial R ι i).hom ≫ eulerPolynomialChart R ι i =
      (coordinateOpen R ι i).ι := by
  unfold eulerPolynomialChart
  rw [← Category.assoc, Iso.hom_inv_id, Category.id_comp]

/-- The original coordinate-open image equals the original polynomial-chart image. -/
theorem determinantCoordinateChart_image (i : ι)
    (W : (coordinateOpen R ι i).toScheme.Opens) :
    (coordinateOpen R ι i).ι ''ᵁ W = eulerPolynomialChart R ι i ''ᵁ
      ((coordinateOpenIsoSpecPolynomial R ι i).hom ''ᵁ W) := by
  apply TopologicalSpace.Opens.ext
  change Set.image (coordinateOpen R ι i).ι W =
    Set.image (eulerPolynomialChart R ι i)
      (Set.image (coordinateOpenIsoSpecPolynomial R ι i).hom W)
  rw [Set.image_image]
  exact congrArg (fun f : (coordinateOpen R ι i).toScheme ⟶ ProjectiveSpace R ι =>
    Set.image f W) (determinantCoordinateChart_comp R ι i).symm

/-- The native restriction-composition comparison on the original coordinate-open scheme. -/
def determinantCoordinateTransport (i : ι) (M : (ProjectiveSpace R ι).Modules) :
    (M.restrict (eulerPolynomialChart R ι i)).restrict
      (coordinateOpenIsoSpecPolynomial R ι i).hom ≅ M.restrict (coordinateOpen R ι i).ι :=
  ((Scheme.Modules.restrictFunctorComp (coordinateOpenIsoSpecPolynomial R ι i).hom
    (eulerPolynomialChart R ι i)).app M).symm ≪≫
    (Scheme.Modules.restrictFunctorCongr (determinantCoordinateChart_comp R ι i)).app M

/-- The native coordinate comparison preserves original sections through the image equality. -/
theorem determinantCoordinateTransport_hom_app (i : ι) (M : (ProjectiveSpace R ι).Modules)
    (W : (coordinateOpen R ι i).toScheme.Opens)
    (m : Γ(M, eulerPolynomialChart R ι i ''ᵁ
      ((coordinateOpenIsoSpecPolynomial R ι i).hom ''ᵁ W))) :
    (determinantCoordinateTransport R ι i M).hom.val.app (op W) m =
      M.presheaf.map (eqToHom (determinantCoordinateChart_image R ι i W)).op m := by
  let c := (coordinateOpenIsoSpecPolynomial R ι i).hom
  let g := eulerPolynomialChart R ι i
  let h₁ := Scheme.Hom.comp_image c g W
  let h₂ := h₁.trans (determinantCoordinateChart_image R ι i W).symm
  change (M.presheaf.map (eqToHom h₁).op ≫
    M.presheaf.map (eqToHom h₂.symm).op) m = _
  rw [← Functor.map_comp]
  congr 2

/-- The actual differential frame on the original coordinate-open scheme. -/
def determinantOmegaCoordinateFreeIso (i : ι) :
    SheafOfModules.free (R := (coordinateOpen R ι i).toScheme.ringCatSheaf)
      {j : ι // j ≠ i} ≅
      (Scheme.Modules.Differentials.relativeDifferentialSheaf (toSpec R ι)).restrict
        (coordinateOpen R ι i).ι :=
  eulerOmegaOverlapFreeIso R ι i (coordinateOpenIsoSpecPolynomial R ι i).hom ≪≫
    determinantCoordinateTransport R ι i _

/-- The original coordinate frame sends its original free section to the original ratio
differential. -/
theorem determinantOmegaCoordinateFreeIso_hom_freeSection (i : ι)
    (j : {j : ι // j ≠ i}) (W : (coordinateOpen R ι i).toScheme.Opens) :
    (determinantOmegaCoordinateFreeIso R ι i).hom.val.app (op W)
      ((SheafOfModules.freeSection (R := (coordinateOpen R ι i).toScheme.ringCatSheaf) j).val
        (op W)) =
      (Scheme.Modules.Differentials.relativeDifferentialDerivation (toSpec R ι)).d
        (eulerCoordinateRatio R ι i j.val (by
          exact (coordinateOpen R ι i).ι_image_le W)) := by
  let Ω := Scheme.Modules.Differentials.relativeDifferentialSheaf (toSpec R ι)
  let d := Scheme.Modules.Differentials.relativeDifferentialDerivation (toSpec R ι)
  let c := (coordinateOpenIsoSpecPolynomial R ι i).hom
  let g := eulerPolynomialChart R ι i
  let hi := eulerPolynomialChart_image_le R ι i (c ''ᵁ W)
  have h := determinantCoordinateChart_image R ι i W
  change (determinantCoordinateTransport R ι i Ω).hom.val.app (op W)
    ((eulerOmegaOverlapFreeIso R ι i c).hom.val.app (op W) _) = _
  rw [eulerOmegaOverlapFreeIso_hom_freeSection,
    determinantCoordinateTransport_hom_app]
  have hd := d.d_map (eqToHom h).op (eulerCoordinateRatio R ι i j.val hi)
  exact hd.symm.trans (congrArg d.d
    (eulerCoordinateRatio_restrict R ι i j.val h.le hi))

/-- The original differential free frame on the over-site of the coordinate open. -/
def determinantOmegaOverFreeIso (i : ι) :
    SheafOfModules.free (R := (ProjectiveSpace R ι).ringCatSheaf.over
      (coordinateOpen R ι i)) {j : ι // j ≠ i} ≅
      (Scheme.Modules.Differentials.relativeDifferentialSheaf (toSpec R ι)).over
        (coordinateOpen R ι i) :=
  Scheme.Modules.freeIsoOverOfRestrictFreeIso (coordinateOpen R ι i)
    (determinantOmegaCoordinateFreeIso R ι i)

theorem determinantOmegaOverFreeIso_hom_freeSection (i : ι)
    (j : {j : ι // j ≠ i}) (W : (coordinateOpen R ι i).toScheme.Opens) :
    (determinantOmegaOverFreeIso R ι i).hom.val.app
      (op ((coordinateOpen R ι i).overEquivalence.inverse.obj W))
      ((SheafOfModules.freeSection (R := (ProjectiveSpace R ι).ringCatSheaf.over
        (coordinateOpen R ι i)) j).val
          (op ((coordinateOpen R ι i).overEquivalence.inverse.obj W))) =
      (Scheme.Modules.Differentials.relativeDifferentialDerivation (toSpec R ι)).d
        (eulerCoordinateRatio R ι i j.val ((coordinateOpen R ι i).ι_image_le W)) :=
  (freeIsoOverOfRestrictFreeIso_hom_freeSection (coordinateOpen R ι i)
    (determinantOmegaCoordinateFreeIso R ι i) j W).trans
      (determinantOmegaCoordinateFreeIso_hom_freeSection R ι i j W)


/-- The displayed order with precisely its pivot deleted. -/
def determinantComplementEquiv (n : ℕ) (e : ι ≃ Fin (n + 1)) (i : ι) :
    {j : ι // j ≠ i} ≃ ULift.{u} (Fin n) := by
  let a : {j : ι // j ≠ i} ≃ {k : Fin (n + 1) // k ≠ e i} := {
    toFun j := ⟨e j.val, fun h => j.property (e.injective h)⟩
    invFun k := ⟨e.symm k.val, fun h => k.property
      ((e.apply_symm_apply k.val).symm.trans (congrArg e h))⟩
    left_inv j := Subtype.ext (e.symm_apply_apply j.val)
    right_inv k := Subtype.ext (e.apply_symm_apply k.val) }
  exact a.trans ((finSuccAboveEquiv (e i)).symm.trans Equiv.ulift.symm)

@[simp]
theorem determinantComplementEquiv_symm_apply (n : ℕ) (e : ι ≃ Fin (n + 1)) (i : ι)
    (a : Fin n) :
    ((determinantComplementEquiv ι n e i).symm (ULift.up a)).val =
      e.symm ((e i).succAbove a) := rfl

/-- The actual relative differential frame in the displayed complement order. -/
def determinantOmegaOrderedCoordinateFreeIso (n : ℕ) (e : ι ≃ Fin (n + 1)) (i : ι) :
    SheafOfModules.free (R := (coordinateOpen R ι i).toScheme.ringCatSheaf)
      (ULift.{u} (Fin n)) ≅
      (Scheme.Modules.Differentials.relativeDifferentialSheaf (toSpec R ι)).restrict
        (coordinateOpen R ι i).ι :=
  (SheafOfModules.freeFunctor
    (R := (coordinateOpen R ι i).toScheme.ringCatSheaf)).mapIso
      (determinantComplementEquiv ι n e i).symm.toIso ≪≫
    determinantOmegaCoordinateFreeIso R ι i

/-- The original actual differential sheaf has rank `n` on this projective space. -/
theorem projectiveDifferential_hasRank (n : ℕ) (e : ι ≃ Fin (n + 1)) :
    SheafHasRank (Scheme.Modules.Differentials.relativeDifferentialSheaf (toSpec R ι)) n :=
  sheafHasRank_of_coverFreeIso (coordinateOpen R ι) (iSup_coordinateOpen_eq_top R ι)
    (determinantOmegaOrderedCoordinateFreeIso R ι n e)

/-- The original top relative exterior sheaf is an actual line, including rank zero. -/
theorem projectiveTopDifferential_isLocallyRankOne (n : ℕ) (e : ι ≃ Fin (n + 1)) :
    Invertible.IsLocallyRankOne (ProjectiveSpace R ι)
      (moduleExteriorPower (ProjectiveSpace R ι)
        (Scheme.Modules.Differentials.relativeDifferentialSheaf (toSpec R ι)) n) :=
  moduleExteriorTop_isLocallyRankOne (ProjectiveSpace R ι) _ n
    (projectiveDifferential_hasRank R ι n e)

/-- The over-site differential frame has the same displayed complement order. -/
def determinantOmegaOrderedOverFreeIso (n : ℕ) (e : ι ≃ Fin (n + 1)) (i : ι) :
    SheafOfModules.free (R := (ProjectiveSpace R ι).ringCatSheaf.over
      (coordinateOpen R ι i)) (ULift.{u} (Fin n)) ≅
      (Scheme.Modules.Differentials.relativeDifferentialSheaf (toSpec R ι)).over
        (coordinateOpen R ι i) :=
  (SheafOfModules.freeFunctor (R := (ProjectiveSpace R ι).ringCatSheaf.over
    (coordinateOpen R ι i))).mapIso
      (determinantComplementEquiv ι n e i).symm.toIso ≪≫
    determinantOmegaOverFreeIso R ι i

/-- Its original basis vectors are the original displayed ratio differentials. -/
theorem determinantOmegaOrderedOverFreeIso_hom_freeSection (n : ℕ)
    (e : ι ≃ Fin (n + 1)) (i : ι) (a : Fin n)
    (W : (coordinateOpen R ι i).toScheme.Opens) :
    (determinantOmegaOrderedOverFreeIso R ι n e i).hom.val.app
      (op ((coordinateOpen R ι i).overEquivalence.inverse.obj W))
      ((SheafOfModules.freeSection (R := (ProjectiveSpace R ι).ringCatSheaf.over
        (coordinateOpen R ι i)) (ULift.up a)).val
          (op ((coordinateOpen R ι i).overEquivalence.inverse.obj W))) =
      (Scheme.Modules.Differentials.relativeDifferentialDerivation (toSpec R ι)).d
        (eulerCoordinateRatio R ι i (e.symm ((e i).succAbove a))
          ((coordinateOpen R ι i).ι_image_le W)) := by
  let U := coordinateOpen R ι i
  let f := (determinantComplementEquiv ι n e i).symm
  let V := op (U.overEquivalence.inverse.obj W)
  have h := congrArg (fun s => s.val V)
    (SheafOfModules.sectionMap_freeMap_freeSection (R := (ProjectiveSpace R ι).ringCatSheaf.over
      U) f (ULift.up a))
  change (SheafOfModules.freeMap f).val.app V
      ((SheafOfModules.freeSection (R := (ProjectiveSpace R ι).ringCatSheaf.over U)
        (ULift.up a)).val V) =
    (SheafOfModules.freeSection (R := (ProjectiveSpace R ι).ringCatSheaf.over U)
      (f (ULift.up a))).val V at h
  dsimp only [determinantOmegaOrderedOverFreeIso, Iso.trans_hom, Functor.mapIso_hom]
  rw [SheafOfModules.freeFunctor_map]
  change (determinantOmegaOverFreeIso R ι i).hom.val.app V
    ((SheafOfModules.freeMap f).val.app V
      ((SheafOfModules.freeSection (R := (ProjectiveSpace R ι).ringCatSheaf.over U)
        (ULift.up a)).val V)) = _
  exact (congrArg ((determinantOmegaOverFreeIso R ι i).hom.val.app V) h).trans
    (determinantOmegaOverFreeIso_hom_freeSection R ι i (f (ULift.up a)) W)

/-- The original top exterior sheaf in its original ordered ratio-differential frame. -/
def determinantOmegaOverIso (n : ℕ) (e : ι ≃ Fin (n + 1)) (i : ι) :
    (moduleExteriorPower (ProjectiveSpace R ι)
      (Scheme.Modules.Differentials.relativeDifferentialSheaf (toSpec R ι)) n).over
        (coordinateOpen R ι i) ≅
      SheafOfModules.unit ((ProjectiveSpace R ι).ringCatSheaf.over (coordinateOpen R ι i)) :=
  moduleExteriorTopOverIso (ProjectiveSpace R ι)
    (Scheme.Modules.Differentials.relativeDifferentialSheaf (toSpec R ι)) n
    (coordinateOpen R ι i) (determinantOmegaOrderedOverFreeIso R ι n e i).symm

/-- The inverse ordered frame recovers the original free section from the original ratio. -/
theorem determinantOmegaOrderedOverFreeIso_inv_d_ratio (n : ℕ)
    (e : ι ≃ Fin (n + 1)) (i : ι) (a : Fin n)
    (W : (coordinateOpen R ι i).toScheme.Opens) :
    let U := coordinateOpen R ι i
    let V := op (U.overEquivalence.inverse.obj W)
    let Ω := Scheme.Modules.Differentials.relativeDifferentialSheaf (toSpec R ι)
    let f := determinantOmegaOrderedOverFreeIso R ι n e i
    let b : (SheafOfModules.free (R := (ProjectiveSpace R ι).ringCatSheaf.over U)
        (ULift.{u} (Fin n))).val.obj V :=
      (SheafOfModules.freeSection (R := (ProjectiveSpace R ι).ringCatSheaf.over U)
        (ULift.up a)).val V
    let v : (Ω.over U).val.obj V :=
      (Scheme.Modules.Differentials.relativeDifferentialDerivation (toSpec R ι)).d
        (eulerCoordinateRatio R ι i (e.symm ((e i).succAbove a)) (U.ι_image_le W))
    f.inv.val.app V v = b := by
  intro U V Ω f b v
  let E := SheafOfModules.evaluation ((ProjectiveSpace R ι).ringCatSheaf.over U) V
  let q := E.mapIso f
  have h : q.hom b = v :=
    determinantOmegaOrderedOverFreeIso_hom_freeSection R ι n e i a W
  have H : q.inv v = b :=
    (congrArg (fun x : (Ω.over U).val.obj V => q.inv x) h.symm).trans
      (Iso.hom_inv_id_apply q b)
  exact H

private theorem topFrame_forward_basis (X : Scheme.{u}) (M : X.Modules) (n : ℕ)
    (U : X.Opens) (e : SheafOfModules.free (R := X.ringCatSheaf.over U)
      (ULift.{u} (Fin n)) ≅ M.over U) (V : (Over U)ᵒᵖ) :
    (moduleExteriorTopOverIso X M n U e.symm).hom.val.app V
      ((SheafOfModulesOfCommRing.exteriorPowerMk X.sheaf M n).app
        ((Over.forget U).op.obj V)
        (fun a => e.hom.val.app V
          ((SheafOfModules.freeSection (R := X.ringCatSheaf.over U) (ULift.up a)).val V))) =
      (1 : X.presheaf.obj ((Over.forget U).op.obj V)) := by
  let b := SheafOfModulesOfCommRing.freeFinSectionsBasis (X.sheaf.over U) n V
  have H : (fun a => e.inv.val.app V (e.hom.val.app V
      ((SheafOfModules.freeSection (R := X.ringCatSheaf.over U) (ULift.up a)).val V))) = b := by
    funext a
    let v : (SheafOfModules.free (R := X.ringCatSheaf.over U)
        (ULift.{u} (Fin n))).val.obj V :=
      (SheafOfModules.freeSection (R := X.ringCatSheaf.over U) (ULift.up a)).val V
    have h : e.inv.val.app V (e.hom.val.app V v) = v :=
      ConcreteCategory.congr_hom (congrArg (fun φ => φ.val.app V) e.hom_inv_id) v
    exact h.trans (SheafOfModulesOfCommRing.freeFinSectionsBasis_apply
      (X.sheaf.over U) n V a).symm
  exact (moduleExteriorTopOverIso_mk X M n U e.symm V _).trans
    ((congrArg b.det H).trans b.det_self)

/-- The ordered original ratio wedge has coefficient exactly one, also when `n = 0`. -/
theorem determinantOmegaOverIso_wedge (n : ℕ) (e : ι ≃ Fin (n + 1)) (i : ι)
    (W : (coordinateOpen R ι i).toScheme.Opens) :
    let U := coordinateOpen R ι i
    let V := op (U.overEquivalence.inverse.obj W)
    let Ω := Scheme.Modules.Differentials.relativeDifferentialSheaf (toSpec R ι)
    let _f := determinantOmegaOrderedOverFreeIso R ι n e i
    let _b := SheafOfModulesOfCommRing.freeFinSectionsBasis
      ((ProjectiveSpace R ι).sheaf.over U) n V
    let s : Fin n → (Ω.over U).val.obj V := fun a =>
      (Scheme.Modules.Differentials.relativeDifferentialDerivation (toSpec R ι)).d
        (eulerCoordinateRatio R ι i (e.symm ((e i).succAbove a)) (U.ι_image_le W))
    (determinantOmegaOverIso R ι n e i).hom.val.app V
      ((SheafOfModulesOfCommRing.exteriorPowerMk (ProjectiveSpace R ι).sheaf Ω n).app
        (op (U.ι ''ᵁ W)) s) = (1 : Γ(ProjectiveSpace R ι, U.ι ''ᵁ W)) := by
  intro U V Ω f b s
  have H : (fun a => f.hom.val.app V
      ((SheafOfModules.freeSection (R := (ProjectiveSpace R ι).ringCatSheaf.over U)
        (ULift.up a)).val V)) = s := by
    funext a
    exact determinantOmegaOrderedOverFreeIso_hom_freeSection R ι n e i a W
  have h := congrArg
    ((SheafOfModulesOfCommRing.exteriorPowerMk (ProjectiveSpace R ι).sheaf Ω n).app
      (op (U.ι ''ᵁ W))) H
  exact (congrArg ((determinantOmegaOverIso R ι n e i).hom.val.app V) h).symm.trans
    (topFrame_forward_basis (ProjectiveSpace R ι) Ω n U f V)


/-- The original top exterior power of the actual degree-one polynomial module. -/
def determinantCoefficientModule (n : ℕ) : ModuleCat (CommRingCat.of R) :=
  (eulerDegreeOneModule R ι).exteriorPower (n + 1)

/-- The displayed coordinate order on the original degree-one module. -/
def determinantDegreeOneBasis (n : ℕ) (e : ι ≃ Fin (n + 1)) :
    Module.Basis (Fin (n + 1)) R (eulerDegreeOneModule R ι) :=
  (MvPolynomial.homogeneousDegreeOneBasis R ι).reindex e

/-- The actual coefficient determinant generator in the displayed coordinate order. -/
def determinantCoefficientGenerator (n : ℕ) (e : ι ≃ Fin (n + 1)) :
    determinantCoefficientModule R ι n :=
  exteriorPower.ιMulti R (n + 1) (determinantDegreeOneBasis R ι n e)

/-- Only a displayed ordered basis trivializes the original coefficient determinant module. -/
def determinantCoefficientFrame (n : ℕ) (e : ι ≃ Fin (n + 1)) :
    determinantCoefficientModule R ι n ≃ₗ[R] R :=
  (determinantDegreeOneBasis R ι n e).exteriorPowerTopEquiv

@[simp]
theorem determinantCoefficientFrame_generator (n : ℕ) (e : ι ≃ Fin (n + 1)) :
    determinantCoefficientFrame R ι n e (determinantCoefficientGenerator R ι n e) = 1 :=
  Module.Basis.exteriorPowerTopEquiv_basis (determinantDegreeOneBasis R ι n e)

/-- The original coefficient wedge retains its determinant under any actual linear map. -/
theorem determinantCoefficientMap_generator (n : ℕ) (e : ι ≃ Fin (n + 1))
    (g : eulerDegreeOneModule R ι ⟶ eulerDegreeOneModule R ι) :
    ModuleCat.exteriorPower.map g (n + 1) (determinantCoefficientGenerator R ι n e) =
      (determinantDegreeOneBasis R ι n e).det (g ∘ determinantDegreeOneBasis R ι n e) •
        determinantCoefficientGenerator R ι n e := by
  change exteriorPower.map (n + 1) g.hom
    (exteriorPower.ιMulti R (n + 1) (determinantDegreeOneBasis R ι n e)) = _
  rw [exteriorPower.map_apply_ιMulti,
    exteriorPower.ιMulti_eq_det_smul (determinantDegreeOneBasis R ι n e)]
  rfl

/-- Arbitrary change of the coefficient basis retains the literal determinant factor. -/
theorem determinantCoefficientFrame_changeBasis (n : ℕ) (e : ι ≃ Fin (n + 1))
    (b : Module.Basis (Fin (n + 1)) R (eulerDegreeOneModule R ι))
    (x : determinantCoefficientModule R ι n) :
    determinantCoefficientFrame R ι n e x =
      (determinantDegreeOneBasis R ι n e).det b * b.exteriorPowerTopEquiv x :=
  Module.Basis.exteriorPowerTopEquiv_changeBasis (determinantDegreeOneBasis R ι n e) b x

/-- Changing the displayed coordinate order retains the actual coefficient determinant. -/
theorem determinantCoefficientGenerator_changeBasis (n : ℕ) (e e' : ι ≃ Fin (n + 1)) :
    determinantCoefficientGenerator R ι n e' =
      (determinantDegreeOneBasis R ι n e).det (determinantDegreeOneBasis R ι n e') •
        determinantCoefficientGenerator R ι n e :=
  exteriorPower.ιMulti_eq_det_smul (determinantDegreeOneBasis R ι n e)
    (determinantDegreeOneBasis R ι n e')

/-- The actual pullback of the untrivialized coefficient determinant. -/
def determinantCoefficientSheaf (n : ℕ) : (ProjectiveSpace R ι).Modules :=
  (Scheme.Modules.pullback (toSpec R ι)).obj (tilde (determinantCoefficientModule R ι n))

/-- A displayed ordered coordinate basis induces the original tilde/pullback unit comparison. -/
def determinantCoefficientIsoUnit (n : ℕ) (e : ι ≃ Fin (n + 1)) :
    determinantCoefficientSheaf R ι n ≅
      SheafOfModules.unit (ProjectiveSpace R ι).ringCatSheaf :=
  (Scheme.Modules.pullback (toSpec R ι)).mapIso
    ((tilde.functor (CommRingCat.of R)).mapIso
      (determinantCoefficientFrame R ι n e).toModuleIso ≪≫ tildeSelf) ≪≫
        Scheme.Modules.pullbackUnitIso (toSpec R ι)

/-- The original ordered coefficient wedge gives its actual singleton inclusion. -/
def determinantCoefficientPoint (n : ℕ) (e : ι ≃ Fin (n + 1)) :
    SheafOfModules.unit (ProjectiveSpace R ι).ringCatSheaf ⟶
      determinantCoefficientSheaf R ι n :=
  (Scheme.Modules.pullbackUnitIso (toSpec R ι)).inv ≫
    (Scheme.Modules.pullback (toSpec R ι)).map
      (tilde.map (ModuleCat.ofHom (LinearMap.toSpanSingleton R _
        (determinantCoefficientGenerator R ι n e))))

/-- The pulled-back original coefficient wedge has scalar coordinate exactly one. -/
theorem determinantCoefficientPoint_comp_frame (n : ℕ) (e : ι ≃ Fin (n + 1)) :
    determinantCoefficientPoint R ι n e ≫ (determinantCoefficientIsoUnit R ι n e).hom = 𝟙 _ := by
  let p : ModuleCat.of (CommRingCat.of R) R ⟶ determinantCoefficientModule R ι n :=
    ModuleCat.ofHom (LinearMap.toSpanSingleton R _ (determinantCoefficientGenerator R ι n e))
  let f : determinantCoefficientModule R ι n ≅ ModuleCat.of (CommRingCat.of R) R :=
    (determinantCoefficientFrame R ι n e).toModuleIso
  have hp : p ≫ f.hom = 𝟙 _ := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro r
    change determinantCoefficientFrame R ι n e (r • determinantCoefficientGenerator R ι n e) = r
    rw [(determinantCoefficientFrame R ι n e).map_smul r
      (determinantCoefficientGenerator R ι n e), determinantCoefficientFrame_generator,
      smul_eq_mul, mul_one]
  have ht : tilde.map p ≫ (tilde.map f.hom ≫ tildeSelf.hom) = 𝟙 _ := by
    change tilde.map p ≫ tilde.map f.hom ≫ 𝟙 _ = 𝟙 _
    rw [Category.comp_id, ← tilde.map_comp, hp, tilde.map_id]
  change (Scheme.Modules.pullbackUnitIso (toSpec R ι)).inv ≫
    (Scheme.Modules.pullback (toSpec R ι)).map (tilde.map p) ≫
    (Scheme.Modules.pullback (toSpec R ι)).map (tilde.map f.hom ≫ tildeSelf.hom) ≫
      (Scheme.Modules.pullbackUnitIso (toSpec R ι)).hom = _
  erw [← Functor.map_comp_assoc, ht]
  have hm := (Scheme.Modules.pullback (toSpec R ι)).map_id
    (SheafOfModules.unit (Spec (CommRingCat.of R)).ringCatSheaf)
  exact (congrArg (fun φ => (Scheme.Modules.pullbackUnitIso (toSpec R ι)).inv ≫
    φ ≫ (Scheme.Modules.pullbackUnitIso (toSpec R ι)).hom) hm).trans
      (by rw [Category.id_comp, Iso.inv_hom_id])

/-- The original pulled-back ordered coefficient generator on each original open. -/
def determinantCoefficientSection (n : ℕ) (e : ι ≃ Fin (n + 1)) :
    (determinantCoefficientSheaf R ι n).sections where
  val V := (determinantCoefficientPoint R ι n e).val.app V (1 : Γ(ProjectiveSpace R ι, V.unop))
  property {V W} f := by
    change (determinantCoefficientSheaf R ι n).val.map f
      ((determinantCoefficientPoint R ι n e).val.app V (1 : Γ(ProjectiveSpace R ι, V.unop))) = _
    rw [← PresheafOfModules.naturality_apply]
    change (determinantCoefficientPoint R ι n e).val.app W
      ((ProjectiveSpace R ι).presheaf.map f (1 : Γ(ProjectiveSpace R ι, V.unop))) = _
    rw [map_one]

@[simp]
theorem determinantCoefficientIsoUnit_section (n : ℕ) (e : ι ≃ Fin (n + 1))
    (W : (ProjectiveSpace R ι).Opensᵒᵖ) :
    (determinantCoefficientIsoUnit R ι n e).hom.val.app W
      ((determinantCoefficientSection R ι n e).val W) =
      (1 : Γ(ProjectiveSpace R ι, W.unop)) := by
  let a : (SheafOfModules.unit (ProjectiveSpace R ι).ringCatSheaf).val.obj W :=
    (1 : Γ(ProjectiveSpace R ι, W.unop))
  have H := ConcreteCategory.congr_hom (congrArg (fun φ => φ.val.app W)
    (determinantCoefficientPoint_comp_frame R ι n e)) a
  exact H

/-- The original tensor orientation, with the coefficient determinant still explicit. -/
def differentialDeterminantTarget (n : ℕ) : (ProjectiveSpace R ι).Modules :=
  (moduleTensorLeftFunctor (ProjectiveSpace R ι)
    (twistingSheaf R ι (-(n + 1 : ℤ)))).obj (determinantCoefficientSheaf R ι n)

/-- An ordered coefficient basis induces a comparison with the original twist. -/
def differentialDeterminantTargetIsoTwist (n : ℕ) (e : ι ≃ Fin (n + 1)) :
    differentialDeterminantTarget R ι n ≅ twistingSheaf R ι (-(n + 1 : ℤ)) :=
  (moduleTensorLeftFunctor (ProjectiveSpace R ι)
    (twistingSheaf R ι (-(n + 1 : ℤ)))).mapIso (determinantCoefficientIsoUnit R ι n e) ≪≫
    (SheafOfModulesOfCommRing.tensorRightUnitIso (ProjectiveSpace R ι).sheaf).app
      (twistingSheaf R ι (-(n + 1 : ℤ)))

/-- The original target generator is the original twist generator tensor the coefficient wedge. -/
def differentialDeterminantTargetGenerator (n : ℕ) (e : ι ≃ Fin (n + 1)) (i : ι)
    {W : (ProjectiveSpace R ι).Opens} (hi : W ≤ coordinateOpen R ι i) :
    Γ(differentialDeterminantTarget R ι n, W) :=
  moduleTensorSection (ProjectiveSpace R ι) (twistingSheaf R ι (-(n + 1 : ℤ)))
    (determinantCoefficientSheaf R ι n) W
    (twistingGenerator R ι (-(n + 1 : ℤ)) i hi)
    ((determinantCoefficientSection R ι n e).val (op W))

/-- The coefficient comparison preserves the original pure tensor of the two generators. -/
theorem differentialDeterminantTarget_map_generator (n : ℕ) (e : ι ≃ Fin (n + 1))
    (i : ι) {W : (ProjectiveSpace R ι).Opens} (hi : W ≤ coordinateOpen R ι i) :
    ((moduleTensorLeftFunctor (ProjectiveSpace R ι)
      (twistingSheaf R ι (-(n + 1 : ℤ)))).map
        (determinantCoefficientIsoUnit R ι n e).hom).val.app (op W)
      (differentialDeterminantTargetGenerator R ι n e i hi) =
      moduleTensorSection (ProjectiveSpace R ι) (twistingSheaf R ι (-(n + 1 : ℤ)))
        (SheafOfModules.unit (ProjectiveSpace R ι).ringCatSheaf) W
        (twistingGenerator R ι (-(n + 1 : ℤ)) i hi) (1 : Γ(ProjectiveSpace R ι, W)) :=
  (moduleTensorLeftFunctor_map_section (twistingSheaf R ι (-(n + 1 : ℤ)))
    (determinantCoefficientIsoUnit R ι n e).hom W
    (twistingGenerator R ι (-(n + 1 : ℤ)) i hi)
    ((determinantCoefficientSection R ι n e).val (op W))).trans
      (congrArg (moduleTensorSection (ProjectiveSpace R ι)
        (twistingSheaf R ι (-(n + 1 : ℤ)))
        (SheafOfModules.unit (ProjectiveSpace R ι).ringCatSheaf) W
        (twistingGenerator R ι (-(n + 1 : ℤ)) i hi))
          (determinantCoefficientIsoUnit_section R ι n e (op W)))

/-- The ordered target comparison preserves the original pure tensor of generators. -/
theorem differentialDeterminantTargetIsoTwist_generator (n : ℕ) (e : ι ≃ Fin (n + 1))
    (i : ι) {W : (ProjectiveSpace R ι).Opens} (hi : W ≤ coordinateOpen R ι i) :
    (differentialDeterminantTargetIsoTwist R ι n e).hom.val.app (op W)
      (differentialDeterminantTargetGenerator R ι n e i hi) =
      twistingGenerator R ι (-(n + 1 : ℤ)) i hi :=
  (congrArg (((SheafOfModulesOfCommRing.tensorRightUnitIso (ProjectiveSpace R ι).sheaf).hom.app
    (twistingSheaf R ι (-(n + 1 : ℤ)))).val.app (op W))
      (differentialDeterminantTarget_map_generator R ι n e i hi)).trans
        ((tensorRightUnitIso_hom_section (ProjectiveSpace R ι)
          (twistingSheaf R ι (-(n + 1 : ℤ))) W
          (twistingGenerator R ι (-(n + 1 : ℤ)) i hi) 1).trans (one_smul _ _))

/-- The actual target's standard local trivialization, retaining its tensor orientation. -/
def differentialDeterminantTargetOverIso (n : ℕ) (e : ι ≃ Fin (n + 1)) (i : ι) :
    (differentialDeterminantTarget R ι n).over (coordinateOpen R ι i) ≅
      SheafOfModules.unit ((ProjectiveSpace R ι).ringCatSheaf.over (coordinateOpen R ι i)) :=
  (SheafOfModules.overFunctor (ProjectiveSpace R ι).ringCatSheaf
    (coordinateOpen R ι i)).mapIso (differentialDeterminantTargetIsoTwist R ι n e) ≪≫
      twistingLocalIso R ι (-(n + 1 : ℤ)) i

@[simp]
theorem differentialDeterminantTargetOverIso_generator (n : ℕ) (e : ι ≃ Fin (n + 1))
    (i : ι) (V : (Over (coordinateOpen R ι i))ᵒᵖ) :
    (differentialDeterminantTargetOverIso R ι n e i).hom.val.app V
      (differentialDeterminantTargetGenerator R ι n e i (leOfHom V.unop.hom)) =
      (1 : Γ(ProjectiveSpace R ι, V.unop.left)) := by
  change twistingSectionsEquiv R ι (-(n + 1 : ℤ)) i (leOfHom V.unop.hom)
    ((differentialDeterminantTargetIsoTwist R ι n e).hom.val.app _ _) = _
  rw [differentialDeterminantTargetIsoTwist_generator, twistingSectionsEquiv_generator]



/-- The actual pivot-first Euler coordinate matrix: pivot column, then kernel columns. -/
def determinantPivotFirstMatrix {S : Type u} [CommRing S] (n : ℕ) (p : Fin (n + 1))
    (h : Fin n → S) : Matrix (Fin (n + 1)) (Fin (n + 1)) S :=
  fun r => Fin.cases (if r = p then 1 else 0)
    (fun a => (if r = p.succAbove a then 1 else 0) - h a * (if r = p then 1 else 0))

/-- Removing the pivot row and first column leaves the identity, over every commutative ring. -/
theorem determinantPivotFirstMatrix_minor {S : Type u} [CommRing S] (n : ℕ)
    (p : Fin (n + 1)) (h : Fin n → S) :
    (determinantPivotFirstMatrix n p h).submatrix p.succAbove Fin.succ = 1 := by
  ext a b
  simp [determinantPivotFirstMatrix, Matrix.submatrix_apply, Fin.succAbove_ne,
    Matrix.one_apply]

/-- Pivot first gives exactly the parity of its displayed coordinate position, including `n = 0`. -/
theorem determinantPivotFirstMatrix_det {S : Type u} [CommRing S] (n : ℕ)
    (p : Fin (n + 1)) (h : Fin n → S) :
    (determinantPivotFirstMatrix n p h).det = (-1 : S) ^ p.val := by
  rw [Matrix.det_succ_column_zero, Finset.sum_eq_single p]
  · rw [determinantPivotFirstMatrix_minor, Matrix.det_one]
    simp [determinantPivotFirstMatrix]
  · intro r _ hr
    simp [determinantPivotFirstMatrix, hr]
  · simp

/-- The original degree-one coefficient wedge has the same pivot-first Euler determinant. -/
theorem determinantCoefficientGenerator_pivotFirst (n : ℕ) (e : ι ≃ Fin (n + 1))
    (i : ι) (h : Fin n → R) :
    exteriorPower.ιMulti R (n + 1)
      (Fin.cases (determinantDegreeOneBasis R ι n e (e i))
        (fun a => determinantDegreeOneBasis R ι n e ((e i).succAbove a) -
          h a • determinantDegreeOneBasis R ι n e (e i))) =
      (-1 : R) ^ (e i).val • determinantCoefficientGenerator R ι n e := by
  let b := determinantDegreeOneBasis R ι n e
  rw [exteriorPower.ιMulti_eq_det_smul b]
  have H : b.toMatrix (Fin.cases (b (e i))
      (fun a => b ((e i).succAbove a) - h a • b (e i))) =
      determinantPivotFirstMatrix n (e i) h := by
    ext r c
    refine Fin.cases ?_ (fun a => ?_) c
    · simp [Module.Basis.toMatrix_apply, determinantPivotFirstMatrix, Finsupp.single_apply, eq_comm]
    · simp [Module.Basis.toMatrix_apply, determinantPivotFirstMatrix, Finsupp.single_apply, eq_comm]
  change (b.toMatrix _).det • determinantCoefficientGenerator R ι n e = _
  rw [H, determinantPivotFirstMatrix_det]


/-- The proposed original pivot-first chart normalization, before proving overlap compatibility. -/
def differentialDeterminantChartIso (n : ℕ) (e : ι ≃ Fin (n + 1)) (i : ι) :
    (moduleExteriorPower (ProjectiveSpace R ι)
      (Scheme.Modules.Differentials.relativeDifferentialSheaf (toSpec R ι)) n).over
        (coordinateOpen R ι i) ≅
      (differentialDeterminantTarget R ι n).over (coordinateOpen R ι i) :=
  ((-1 : ℤˣ) ^ (e i).val) •
    (determinantOmegaOverIso R ι n e i ≪≫
      (differentialDeterminantTargetOverIso R ι n e i).symm)

/-- The original ordered ratio-differential wedge maps to the signed original target tensor. -/
theorem differentialDeterminantChartIso_wedge (n : ℕ) (e : ι ≃ Fin (n + 1)) (i : ι)
    (W : (coordinateOpen R ι i).toScheme.Opens) :
    (differentialDeterminantChartIso R ι n e i).hom.val.app
      (op ((coordinateOpen R ι i).overEquivalence.inverse.obj W))
      ((SheafOfModulesOfCommRing.exteriorPowerMk (ProjectiveSpace R ι).sheaf
        (Scheme.Modules.Differentials.relativeDifferentialSheaf (toSpec R ι)) n).app
          (op ((coordinateOpen R ι i).ι ''ᵁ W))
          (fun a => (Scheme.Modules.Differentials.relativeDifferentialDerivation (toSpec R ι)).d
            (eulerCoordinateRatio R ι i (e.symm ((e i).succAbove a))
              ((coordinateOpen R ι i).ι_image_le W)))) =
      (-1 : Γ(ProjectiveSpace R ι, (coordinateOpen R ι i).ι ''ᵁ W)) ^ (e i).val •
        differentialDeterminantTargetGenerator R ι n e i
          ((coordinateOpen R ι i).ι_image_le W) := by
  let U := coordinateOpen R ι i
  let V := op (U.overEquivalence.inverse.obj W)
  let f := differentialDeterminantTargetOverIso R ι n e i
  let w : ((moduleExteriorPower (ProjectiveSpace R ι)
      (Scheme.Modules.Differentials.relativeDifferentialSheaf (toSpec R ι)) n).over U).val.obj V :=
    (SheafOfModulesOfCommRing.exteriorPowerMk (ProjectiveSpace R ι).sheaf
    (Scheme.Modules.Differentials.relativeDifferentialSheaf (toSpec R ι)) n).app
      (op (U.ι ''ᵁ W))
      (fun a => (Scheme.Modules.Differentials.relativeDifferentialDerivation (toSpec R ι)).d
        (eulerCoordinateRatio R ι i (e.symm ((e i).succAbove a)) (U.ι_image_le W)))
  let t : ((differentialDeterminantTarget R ι n).over U).val.obj V :=
    differentialDeterminantTargetGenerator R ι n e i (U.ι_image_le W)
  have hf : f.inv.val.app V (1 : Γ(ProjectiveSpace R ι, U.ι ''ᵁ W)) = t := by
    have h := congrArg (f.inv.val.app V)
      (differentialDeterminantTargetOverIso_generator R ι n e i V).symm
    exact h.trans (ConcreteCategory.congr_hom
      (congrArg (fun φ => φ.val.app V) f.hom_inv_id) t)
  have h : (determinantOmegaOverIso R ι n e i ≪≫ f.symm).hom.val.app V w = t :=
    (congrArg (f.inv.val.app V) (determinantOmegaOverIso_wedge R ι n e i W)).trans hf
  let z : ℤ := (-1) ^ (e i).val
  let c := determinantOmegaOverIso R ι n e i ≪≫ f.symm
  have hz : ((z • c.hom).val.app V) w = z • (c.hom.val.app V w) := by
    change (((SheafOfModules.forget ((ProjectiveSpace R ι).ringCatSheaf.over U)).map
      (z • c.hom)).app V) w = _
    erw [Functor.map_zsmul, PresheafOfModules.zsmul_app]
    rfl
  change ((z • c.hom).val.app V) w = _
  exact hz.trans ((congrArg (fun a => z • a) h).trans (by
    rw [← Int.cast_smul_eq_zsmul Γ(ProjectiveSpace R ι, U.ι ''ᵁ W)]
    simp only [z, t, Int.cast_pow, Int.cast_neg, Int.cast_one]))


end AlgebraicGeometry.ProjectiveSpace
