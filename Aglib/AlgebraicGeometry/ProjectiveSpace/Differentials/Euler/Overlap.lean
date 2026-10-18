/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Aglib.AlgebraicGeometry.ProjectiveSpace.Differentials.Euler.LocalExact
public import Aglib.AlgebraicGeometry.Modules.InternalHom.Restriction
public import Aglib.AlgebraicGeometry.Modules.Restriction.Overlap
public import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing
public import Mathlib.RingTheory.Derivation.Basic
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.Ring

/-!
# Original transition and overlap formulas for the actual relative Euler arrows

The original coordinate transition unit is the inverse of the original chart ratio. The
original inverse twist and Euler tensor generators retain that same unit. The original
relative differential and the original kernel vectors obey the same quotient transition
formula. The checked actual chart differential formula extends to every native chart open.
The actual restricted Ω frame and its original ratio differential values identify the literal
native chart arrows through the native pullback-overlap restriction comparison. No field,
finiteness, nontriviality, or exactness-family hypothesis is used.
-/

@[expose] public section
noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.Invertible
open AlgebraicGeometry.Scheme.Modules.InternalHom
open scoped TensorProduct
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
namespace AlgebraicGeometry.ProjectiveSpace
variable (R : Type u) [CommRing R] (ι : Type u)

/-- The original coordinate coefficients obey the original inverse transition-unit rule. -/
theorem eulerCoordinateRatio_transition (i k j : ι)
    {V : (ProjectiveSpace R ι).Opens} (hi : V ≤ coordinateOpen R ι i)
    (hk : V ≤ coordinateOpen R ι k) :
    eulerCoordinateRatio R ι i j hi =
      ((coordinateTransitionOn R ι i k hi hk)⁻¹).val * eulerCoordinateRatio R ι k j hk := by
  simpa only [eulerCoordinateRatio, zpow_neg_one] using
    twistingSectionsEquiv_transition R ι 1 i k hi hk
    ((homogeneousSectionFamily R ι 1 (coordinatePower R ι 1 j)).val (op V))

/-- The inverse of the original transition unit is the original ratio `X_k/X_i`. -/
theorem eulerCoordinateRatio_transition_inverse (i k : ι)
    {V : (ProjectiveSpace R ι).Opens} (hi : V ≤ coordinateOpen R ι i)
    (hk : V ≤ coordinateOpen R ι k) :
    eulerCoordinateRatio R ι i k hi = ((coordinateTransitionOn R ι i k hi hk)⁻¹).val :=
  (eulerCoordinateRatio_transition R ι i k k hi hk).trans
    ((congrArg (fun s : Γ(ProjectiveSpace R ι, V) =>
      ((coordinateTransitionOn R ι i k hi hk)⁻¹).val * s)
        (eulerCoordinateRatio_self R ι k hk)).trans (mul_one _))

/-- The original chart ratios transform by the original transition unit. -/
theorem eulerCoordinateRatio_transition_reverse (i k j : ι)
    {V : (ProjectiveSpace R ι).Opens} (hi : V ≤ coordinateOpen R ι i)
    (hk : V ≤ coordinateOpen R ι k) :
    eulerCoordinateRatio R ι k j hk =
      (coordinateTransitionOn R ι i k hi hk).val * eulerCoordinateRatio R ι i j hi := by
  let u := coordinateTransitionOn R ι i k hi hk
  have h := congrArg (fun s : Γ(ProjectiveSpace R ι, V) => u.val * s)
    (eulerCoordinateRatio_transition R ι i k j hi hk)
  have hu : u.val * ((u⁻¹).val * eulerCoordinateRatio R ι k j hk) =
      eulerCoordinateRatio R ι k j hk := by
    change u.val * (u.inv * eulerCoordinateRatio R ι k j hk) = _
    rw [← mul_assoc, u.val_inv, one_mul]
  exact (h.trans hu).symm

/-- The original inverse-twist coordinate frames use that same transition unit. -/
theorem eulerInverseTwistGenerator_transition (i k : ι)
    {V : (ProjectiveSpace R ι).Opens} (hi : V ≤ coordinateOpen R ι i)
    (hk : V ≤ coordinateOpen R ι k) :
    twistingGenerator R ι (-1) k hk =
      (coordinateTransitionOn R ι i k hi hk).val • twistingGenerator R ι (-1) i hi := by
  simpa only [neg_neg, zpow_one] using twistingGenerator_transition R ι (-1) i k hi hk

/-- The original Euler tensor generators transform in the same original inverse-twist frame. -/
theorem eulerMiddleGenerator_transition (i k j : ι)
    {V : (ProjectiveSpace R ι).Opens} (hi : V ≤ coordinateOpen R ι i)
    (hk : V ≤ coordinateOpen R ι k) :
    eulerMiddleGenerator R ι k j hk =
      (coordinateTransitionOn R ι i k hi hk).val • eulerMiddleGenerator R ι i j hi := by
  let X := ProjectiveSpace R ι
  let L := twistingSheaf R ι (-1)
  let M := eulerCoefficientSheaf R ι
  let m : Γ(M, V) := (eulerCoefficientSection R ι j).val (op V)
  let η := (SheafOfModulesOfCommRing.associatedSheafUnit X.sheaf).app
    (((SheafOfModulesOfCommRing.toPresheaf X.sheaf).obj L) ⊗
      ((SheafOfModulesOfCommRing.toPresheaf X.sheaf).obj M))
  change η.app (op V) (twistingGenerator R ι (-1) k hk ⊗ₜ[Γ(X, V)] m) =
    (coordinateTransitionOn R ι i k hi hk).val •
      η.app (op V) (twistingGenerator R ι (-1) i hi ⊗ₜ[Γ(X, V)] m)
  exact (congrArg (fun s : Γ(L, V) => η.app (op V) (s ⊗ₜ[Γ(X, V)] m))
    (eulerInverseTwistGenerator_transition R ι i k hi hk)).trans (by
      rw [← TensorProduct.smul_tmul', (η.app (op V)).hom.map_smul])

/-- The original relative differential obeys the quotient rule in the original transition unit. -/
theorem eulerRelativeDifferential_ratio_transition (i k j : ι)
    {V : (ProjectiveSpace R ι).Opens} (hi : V ≤ coordinateOpen R ι i)
    (hk : V ≤ coordinateOpen R ι k) :
    let u := coordinateTransitionOn R ι i k hi hk
    let d := Scheme.Modules.Differentials.relativeDifferentialDerivation (toSpec R ι)
    d.d (eulerCoordinateRatio R ι k j hk) =
      u.val • d.d (eulerCoordinateRatio R ι i j hi) -
        (eulerCoordinateRatio R ι i j hi * u.val ^ 2) •
          d.d (eulerCoordinateRatio R ι i k hi) := by
  let u := coordinateTransitionOn R ι i k hi hk
  let d := Scheme.Modules.Differentials.relativeDifferentialDerivation (toSpec R ι)
  let D : Derivation ℤ Γ(ProjectiveSpace R ι, V)
      Γ(Scheme.Modules.Differentials.relativeDifferentialSheaf (toSpec R ι), V) :=
    Derivation.mk' (d.d (X := op V)).toIntLinearMap (d.d_mul (X := op V))
  have hdu : D u.val = -(u.val ^ 2) • D (eulerCoordinateRatio R ι i k hi) :=
    (D.leibniz_of_mul_eq_one (a := u.val) (b := u.inv) u.val_inv).trans
      (congrArg (fun s : Γ(ProjectiveSpace R ι, V) => -(u.val ^ 2) • D s)
        (eulerCoordinateRatio_transition_inverse R ι i k hi hk).symm)
  change D (eulerCoordinateRatio R ι k j hk) =
    u.val • D (eulerCoordinateRatio R ι i j hi) -
      (eulerCoordinateRatio R ι i j hi * u.val ^ 2) • D (eulerCoordinateRatio R ι i k hi)
  calc
    _ = D (u.val * eulerCoordinateRatio R ι i j hi) :=
      congrArg D (eulerCoordinateRatio_transition_reverse R ι i k j hi hk)
    _ = u.val • D (eulerCoordinateRatio R ι i j hi) +
        eulerCoordinateRatio R ι i j hi • D u.val := D.leibniz _ _
    _ = u.val • D (eulerCoordinateRatio R ι i j hi) +
        eulerCoordinateRatio R ι i j hi •
          (-(u.val ^ 2) • D (eulerCoordinateRatio R ι i k hi)) :=
      congrArg (fun s => u.val • D (eulerCoordinateRatio R ι i j hi) +
        eulerCoordinateRatio R ι i j hi • s) hdu
    _ = _ := by simp only [neg_smul, smul_neg, smul_smul, sub_eq_add_neg]

/-- The original Euler kernel vectors obey the same original quotient transition formula. -/
theorem eulerKernelGenerator_transition (i k j : ι)
    {V : (ProjectiveSpace R ι).Opens} (hi : V ≤ coordinateOpen R ι i)
    (hk : V ≤ coordinateOpen R ι k) :
    let u := coordinateTransitionOn R ι i k hi hk
    eulerKernelGenerator R ι k j hk =
      u.val • eulerKernelGenerator R ι i j hi -
        (eulerCoordinateRatio R ι i j hi * u.val ^ 2) • eulerKernelGenerator R ι i k hi := by
  let u := coordinateTransitionOn R ι i k hi hk
  let r : Γ(ProjectiveSpace R ι, V) := eulerCoordinateRatio R ι i j hi
  let t : Γ(ProjectiveSpace R ι, V) := eulerCoordinateRatio R ι i k hi
  have ht : t = u.inv := eulerCoordinateRatio_transition_inverse R ι i k hi hk
  have hmul : (u.val * r) * u.val = r * u.val ^ 2 := by ring
  have hcoeff : r * u.val ^ 2 * t = u.val * r := by
    rw [ht]
    calc
      _ = (u.val * r) * (u.val * u.inv) := by ring
      _ = _ := by rw [u.val_inv, mul_one]
  simp only [eulerKernelGenerator]
  rw [eulerMiddleGenerator_transition R ι i k j hi hk,
    eulerMiddleGenerator_transition R ι i k k hi hk,
    eulerCoordinateRatio_transition_reverse R ι i k j hi hk]
  change u.val • eulerMiddleGenerator R ι i j hi -
      (u.val * r) • (u.val • eulerMiddleGenerator R ι i k hi) =
    u.val • (eulerMiddleGenerator R ι i j hi - r • eulerMiddleGenerator R ι i i hi) -
      (r * u.val ^ 2) •
        (eulerMiddleGenerator R ι i k hi - t • eulerMiddleGenerator R ι i i hi)
  simp only [smul_sub, smul_smul]
  rw [hmul, hcoeff]
  abel

/-- The original relative-d formula of the actual chart arrow holds on every chart open. -/
theorem eulerDifferentialOnPolynomialChart_d_ratio_open (i : ι)
    (j : {j : ι // j ≠ i})
    (V : (Spec (CommRingCat.of (MvPolynomial {j : ι // j ≠ i} R))).Opens) :
    (eulerDifferentialOnPolynomialChart R ι i).val.app (op V)
      ((Scheme.Modules.Differentials.relativeDifferentialDerivation (toSpec R ι)).d
        (eulerCoordinateRatio R ι i j.val (eulerPolynomialChart_image_le R ι i V))) =
      eulerKernelGenerator R ι i j.val (eulerPolynomialChart_image_le R ι i V) := by
  let g := eulerPolynomialChart R ι i
  let Ω := Scheme.Modules.Differentials.relativeDifferentialSheaf (toSpec R ι)
  let d := Scheme.Modules.Differentials.relativeDifferentialDerivation (toSpec R ι)
  let f := eulerDifferentialOnPolynomialChart R ι i
  apply TopCat.Presheaf.IsSheaf.section_ext ((eulerMiddle R ι).restrict g).isSheaf
  intro x hx
  obtain ⟨_, ⟨_, ⟨r, rfl⟩, rfl⟩, hxr, hrV : PrimeSpectrum.basicOpen _ ≤ _⟩ :=
    PrimeSpectrum.isBasis_basic_opens.exists_subset_of_mem_open hx V.2
  refine ⟨_, hrV, hxr, ?_⟩
  let W := PrimeSpectrum.basicOpen r
  let h := g.image_mono hrV
  let t := eulerCoordinateRatio R ι i j.val (eulerPolynomialChart_image_le R ι i V)
  have hd : (Ω.restrict g).val.map (homOfLE hrV).op (d.d t) =
      d.d (eulerCoordinateRatio R ι i j.val (eulerPolynomialChart_image_le R ι i W)) :=
    (d.d_map (homOfLE h).op t).symm.trans
      (congrArg d.d (eulerCoordinateRatio_restrict R ι i j.val h
        (eulerPolynomialChart_image_le R ι i V)))
  have hn := _root_.PresheafOfModules.naturality_apply f.val (homOfLE hrV).op (d.d t)
  exact hn.symm.trans ((congrArg (f.val.app (op W)) hd).trans
    ((eulerDifferentialOnPolynomialChart_d_ratio R ι i r j).trans
      (eulerKernelGenerator_restrict R ι i j.val h
        (eulerPolynomialChart_image_le R ι i V)).symm))

/-- The actual chart arrow formula includes the distinguished constant ratio. -/
theorem eulerDifferentialOnPolynomialChart_d_ratio_any_open (i j : ι)
    (V : (Spec (CommRingCat.of (MvPolynomial {j : ι // j ≠ i} R))).Opens) :
    (eulerDifferentialOnPolynomialChart R ι i).val.app (op V)
      ((Scheme.Modules.Differentials.relativeDifferentialDerivation (toSpec R ι)).d
        (eulerCoordinateRatio R ι i j (eulerPolynomialChart_image_le R ι i V))) =
      eulerKernelGenerator R ι i j (eulerPolynomialChart_image_le R ι i V) := by
  by_cases h : j ≠ i
  · exact eulerDifferentialOnPolynomialChart_d_ratio_open R ι i ⟨j, h⟩ V
  · have hji : j = i := not_not.mp h
    subst j
    let T := eulerPolynomialChart R ι i ''ᵁ V
    let hi := eulerPolynomialChart_image_le R ι i V
    let d := Scheme.Modules.Differentials.relativeDifferentialDerivation (toSpec R ι)
    let A := (eulerDifferentialOnPolynomialChart R ι i).val.app (op V)
    have h0 : A (d.d (1 : Γ(ProjectiveSpace R ι, T))) = 0 :=
      (congrArg A (d.d_one (op T))).trans A.hom.map_zero
    have hk : eulerKernelGenerator R ι i i hi = 0 := by
      simp only [eulerKernelGenerator, eulerCoordinateRatio_self, one_smul, sub_self]
    exact (congrArg (fun s : Γ(ProjectiveSpace R ι, T) => A (d.d s))
      (eulerCoordinateRatio_self R ι i hi)).trans (h0.trans hk.symm)

/-- The actual chart arrow has the prescribed original-d value in every other coordinate frame
on every common image subopen. -/
theorem eulerDifferentialOnPolynomialChart_d_other_ratio (i k j : ι)
    (V : (Spec (CommRingCat.of (MvPolynomial {j : ι // j ≠ i} R))).Opens)
    (hk : eulerPolynomialChart R ι i ''ᵁ V ≤ coordinateOpen R ι k) :
    (eulerDifferentialOnPolynomialChart R ι i).val.app (op V)
      ((Scheme.Modules.Differentials.relativeDifferentialDerivation (toSpec R ι)).d
        (eulerCoordinateRatio R ι k j hk)) = eulerKernelGenerator R ι k j hk := by
  let T := eulerPolynomialChart R ι i ''ᵁ V
  let hi := eulerPolynomialChart_image_le R ι i V
  let u := coordinateTransitionOn R ι i k hi hk
  let d := Scheme.Modules.Differentials.relativeDifferentialDerivation (toSpec R ι)
  let f := eulerDifferentialOnPolynomialChart R ι i
  let A := f.val.app (op V)
  let c : Γ(ProjectiveSpace R ι, T) := eulerCoordinateRatio R ι i j hi * u.val ^ 2
  have hj := (restrictionHom_original_smul (eulerPolynomialChart R ι i) f V u.val
    (d.d (eulerCoordinateRatio R ι i j hi))).trans
      (congrArg (fun s : Γ(eulerMiddle R ι, T) => u.val • s)
        (eulerDifferentialOnPolynomialChart_d_ratio_any_open R ι i j V))
  have hik := (restrictionHom_original_smul (eulerPolynomialChart R ι i) f V c
    (d.d (eulerCoordinateRatio R ι i k hi))).trans
      (congrArg (fun s : Γ(eulerMiddle R ι, T) => c • s)
        (eulerDifferentialOnPolynomialChart_d_ratio_any_open R ι i k V))
  exact (congrArg A (eulerRelativeDifferential_ratio_transition R ι i k j hi hk)).trans
    ((A.hom.map_sub _ _).trans
      ((congrArg₂ (fun a b : Γ(eulerMiddle R ι, T) => a - b) hj hik).trans
        (eulerKernelGenerator_transition R ι i k j hi hk).symm))

/-- The original actual differential free frame retains every original ratio differential on
all native chart opens. -/
theorem eulerPolynomialOmegaFreeIso_hom_d_ratio_open (i : ι)
    (j : {j : ι // j ≠ i})
    (V : (Spec (CommRingCat.of (MvPolynomial {j : ι // j ≠ i} R))).Opens) :
    (eulerPolynomialOmegaFreeIso R ι i).hom.val.app (op V)
      ((Scheme.Modules.Differentials.relativeDifferentialDerivation (toSpec R ι)).d
        (eulerCoordinateRatio R ι i j.val (eulerPolynomialChart_image_le R ι i V))) =
      (SheafOfModules.freeSection
        (R := (Spec (CommRingCat.of (MvPolynomial {j : ι // j ≠ i} R))).ringCatSheaf) j).val
          (op V) := by
  let S : CommRingCat.{u} := .of (MvPolynomial {j : ι // j ≠ i} R)
  let g := eulerPolynomialChart R ι i
  let Ω := Scheme.Modules.Differentials.relativeDifferentialSheaf (toSpec R ι)
  let N : (Spec S).Modules := SheafOfModules.free (R := (Spec S).ringCatSheaf) {j : ι // j ≠ i}
  let d := Scheme.Modules.Differentials.relativeDifferentialDerivation (toSpec R ι)
  let f := (eulerPolynomialOmegaFreeIso R ι i).hom
  apply TopCat.Presheaf.IsSheaf.section_ext N.isSheaf
  intro x hx
  obtain ⟨_, ⟨_, ⟨r, rfl⟩, rfl⟩, hxr, hrV : PrimeSpectrum.basicOpen _ ≤ _⟩ :=
    PrimeSpectrum.isBasis_basic_opens.exists_subset_of_mem_open hx V.2
  refine ⟨_, hrV, hxr, ?_⟩
  let W := PrimeSpectrum.basicOpen r
  let h := g.image_mono hrV
  let t := eulerCoordinateRatio R ι i j.val (eulerPolynomialChart_image_le R ι i V)
  have hd : (Ω.restrict g).val.map (homOfLE hrV).op (d.d t) =
      d.d (eulerCoordinateRatio R ι i j.val (eulerPolynomialChart_image_le R ι i W)) :=
    (d.d_map (homOfLE h).op t).symm.trans
      (congrArg d.d (eulerCoordinateRatio_restrict R ι i j.val h
        (eulerPolynomialChart_image_le R ι i V)))
  have hl := (congrArg (fun s : Γ(ProjectiveSpace R ι, g ''ᵁ W) =>
    f.val.app (op W) (d.d s)) (eulerCoordinateRatio_eq_polynomialSection R ι i j W)).trans
      (eulerPolynomialOmegaFreeIso_hom_d R ι i r j)
  have hn := _root_.PresheafOfModules.naturality_apply f.val (homOfLE hrV).op (d.d t)
  exact hn.symm.trans ((congrArg (f.val.app (op W)) hd).trans
    (hl.trans ((SheafOfModules.freeSection (R := (Spec S).ringCatSheaf) j).property
      (homOfLE hrV).op).symm))

/-- The inverse original differential free frame recovers the actual relative differential of
the original chart ratio on every chart open. -/
theorem eulerPolynomialOmegaFreeIso_inv_freeSection (i : ι)
    (j : {j : ι // j ≠ i})
    (V : (Spec (CommRingCat.of (MvPolynomial {j : ι // j ≠ i} R))).Opens) :
    (eulerPolynomialOmegaFreeIso R ι i).inv.val.app (op V)
      ((SheafOfModules.freeSection
        (R := (Spec (CommRingCat.of (MvPolynomial {j : ι // j ≠ i} R))).ringCatSheaf) j).val
          (op V)) =
      (Scheme.Modules.Differentials.relativeDifferentialDerivation (toSpec R ι)).d
        (eulerCoordinateRatio R ι i j.val (eulerPolynomialChart_image_le R ι i V)) := by
  exact (congrArg ((eulerPolynomialOmegaFreeIso R ι i).inv.val.app (op V))
    (eulerPolynomialOmegaFreeIso_hom_d_ratio_open R ι i j V).symm).trans
      (congrArg (fun f => f.val.app (op V)
        ((Scheme.Modules.Differentials.relativeDifferentialDerivation (toSpec R ι)).d
          (eulerCoordinateRatio R ι i j.val (eulerPolynomialChart_image_le R ι i V))))
            (eulerPolynomialOmegaFreeIso R ι i).hom_inv_id)

/-- The original actual Ω free frame restricts canonically to any further open immersion. -/
def eulerOmegaOverlapFreeIso (k : ι) {Z : Scheme.{u}}
    (q : Z ⟶ Spec (CommRingCat.of (MvPolynomial {j : ι // j ≠ k} R))) [IsOpenImmersion q] :
    SheafOfModules.free (R := Z.ringCatSheaf) {j : ι // j ≠ k} ≅
      ((Scheme.Modules.Differentials.relativeDifferentialSheaf (toSpec R ι)).restrict
        (eulerPolynomialChart R ι k)).restrict q := by
  letI : PreservesColimitsOfSize.{u, u} (Scheme.Modules.restrictFunctor q) := inferInstance
  exact SheafOfModules.mapFreeIso (Scheme.Modules.restrictFunctor q) {j : ι // j ≠ k}
      (Scheme.Modules.restrictUnitIso q).symm ≪≫
    (Scheme.Modules.restrictFunctor q).mapIso (eulerPolynomialOmegaFreeIso R ι k).symm

/-- The restricted actual Ω basis vector is the original relative differential of the original
ratio on the original image open. -/
theorem eulerOmegaOverlapFreeIso_hom_freeSection (k : ι) {Z : Scheme.{u}}
    (q : Z ⟶ Spec (CommRingCat.of (MvPolynomial {j : ι // j ≠ k} R))) [IsOpenImmersion q]
    (j : {j : ι // j ≠ k}) (W : Z.Opens) :
    (eulerOmegaOverlapFreeIso R ι k q).hom.val.app (op W)
      ((SheafOfModules.freeSection (R := Z.ringCatSheaf) j).val (op W)) =
      (Scheme.Modules.Differentials.relativeDifferentialDerivation (toSpec R ι)).d
        (eulerCoordinateRatio R ι k j.val
          (eulerPolynomialChart_image_le R ι k (q ''ᵁ W))) := by
  let S : CommRingCat.{u} := .of (MvPolynomial {j : ι // j ≠ k} R)
  let F := Scheme.Modules.restrictFunctor q
  let : PreservesColimitsOfSize.{u, u} F := inferInstance
  let η := (Scheme.Modules.restrictUnitIso q).symm
  let e := SheafOfModules.mapFreeIso F {j : ι // j ≠ k} η
  have hu : η.hom.val.app (op W) (1 : Γ(Z, W)) = (1 : Γ(Spec S, q ''ᵁ W)) := by
    change (q.appIso W).inv 1 = 1
    exact (q.appIso W).inv.hom.map_one
  have he := congrArg (fun f => f.val.app (op W) (1 : Γ(Z, W)))
    (SheafOfModules.ιFree_mapFreeIso_hom F {j : ι // j ≠ k} η j)
  change e.hom.val.app (op W)
      ((SheafOfModules.freeSection (R := Z.ringCatSheaf) j).val (op W)) =
    (F.map (SheafOfModules.ιFree (R := (Spec S).ringCatSheaf) j)).val.app (op W)
      (η.hom.val.app (op W) (1 : Γ(Z, W))) at he
  have he' : e.hom.val.app (op W)
      ((SheafOfModules.freeSection (R := Z.ringCatSheaf) j).val (op W)) =
      (SheafOfModules.freeSection (R := (Spec S).ringCatSheaf) j).val (op (q ''ᵁ W)) :=
    he.trans (congrArg
      ((F.map (SheafOfModules.ιFree (R := (Spec S).ringCatSheaf) j)).val.app (op W)) hu)
  change ((F.map (eulerPolynomialOmegaFreeIso R ι k).inv).val.app (op W))
    (e.hom.val.app (op W)
      ((SheafOfModules.freeSection (R := Z.ringCatSheaf) j).val (op W))) = _
  exact (congrArg ((F.map (eulerPolynomialOmegaFreeIso R ι k).inv).val.app (op W)) he').trans
    (eulerPolynomialOmegaFreeIso_inv_freeSection R ι k j (q ''ᵁ W))

/-- The two original images of a native polynomial-chart pullback open are equal. -/
theorem eulerPolynomialOverlap_image (i k : ι)
    (W : (CategoryTheory.Limits.pullback
      (eulerPolynomialChart R ι i) (eulerPolynomialChart R ι k)).Opens) :
    eulerPolynomialChart R ι i ''ᵁ
        (pullback.fst (eulerPolynomialChart R ι i) (eulerPolynomialChart R ι k) ''ᵁ W) =
      eulerPolynomialChart R ι k ''ᵁ
        (pullback.snd (eulerPolynomialChart R ι i) (eulerPolynomialChart R ι k) ''ᵁ W) := by
  apply TopologicalSpace.Opens.ext
  change Set.image (eulerPolynomialChart R ι i)
      (Set.image (pullback.fst (eulerPolynomialChart R ι i) (eulerPolynomialChart R ι k)) W) =
    Set.image (eulerPolynomialChart R ι k)
      (Set.image (pullback.snd (eulerPolynomialChart R ι i) (eulerPolynomialChart R ι k)) W)
  rw [Set.image_image, Set.image_image]
  exact congrArg (fun f : CategoryTheory.Limits.pullback
      (eulerPolynomialChart R ι i) (eulerPolynomialChart R ι k) ⟶ ProjectiveSpace R ι =>
        Set.image f W) (pullback.condition (f := eulerPolynomialChart R ι i)
          (g := eulerPolynomialChart R ι k))

/-- The original overlap comparison transports sections by the original image-open equality. -/
theorem eulerPolynomialOverlapIso_hom_app (i k : ι) (M : (ProjectiveSpace R ι).Modules)
    (W : (CategoryTheory.Limits.pullback
      (eulerPolynomialChart R ι i) (eulerPolynomialChart R ι k)).Opens)
    (m : Γ(M, eulerPolynomialChart R ι i ''ᵁ
      (pullback.fst (eulerPolynomialChart R ι i) (eulerPolynomialChart R ι k) ''ᵁ W))) :
    ((Scheme.Modules.overlapRestrictIso
      (eulerPolynomialChart R ι i) (eulerPolynomialChart R ι k)).hom.app M).val.app (op W) m =
      M.presheaf.map (eqToHom (eulerPolynomialOverlap_image R ι i k W).symm).op m := by
  let a := eulerPolynomialChart R ι i
  let b := eulerPolynomialChart R ι k
  let p := pullback.fst a b
  let q := pullback.snd a b
  let h := eulerPolynomialOverlap_image R ι i k W
  let h₁ := Scheme.Hom.comp_image p a W
  let h₃ := Scheme.Hom.comp_image q b W
  let h₂ := h₁.trans (h.trans h₃.symm)
  change (M.presheaf.map (eqToHom h₁).op ≫
    M.presheaf.map (eqToHom h₂.symm).op ≫
      M.presheaf.map (eqToHom h₃.symm).op) m = M.presheaf.map (eqToHom h.symm).op m
  have hh : M.presheaf.map (eqToHom h₁).op ≫
      M.presheaf.map (eqToHom h₂.symm).op ≫ M.presheaf.map (eqToHom h₃.symm).op =
        M.presheaf.map (eqToHom h.symm).op := by
    rw [← Functor.map_comp, ← Functor.map_comp]
    congr 1
  exact ConcreteCategory.congr_hom hh m

/-- The inverse native overlap transport preserves the original relative differential of the
original ratio, on the original common image open. -/
theorem eulerPolynomialOverlapIso_inv_d_ratio (i k j : ι)
    (W : (CategoryTheory.Limits.pullback
      (eulerPolynomialChart R ι i) (eulerPolynomialChart R ι k)).Opens) :
    let Ω := Scheme.Modules.Differentials.relativeDifferentialSheaf (toSpec R ι)
    let a := eulerPolynomialChart R ι i
    let b := eulerPolynomialChart R ι k
    let q := pullback.snd a b
    let hk := eulerPolynomialChart_image_le R ι k (q ''ᵁ W)
    let hki := (eulerPolynomialOverlap_image R ι i k W).le.trans hk
    let d := Scheme.Modules.Differentials.relativeDifferentialDerivation (toSpec R ι)
    ((Scheme.Modules.overlapRestrictIso a b).app Ω).inv.val.app (op W)
      (d.d (eulerCoordinateRatio R ι k j hk)) =
      d.d (eulerCoordinateRatio R ι k j hki) := by
  dsimp only
  let Ω := Scheme.Modules.Differentials.relativeDifferentialSheaf (toSpec R ι)
  let a := eulerPolynomialChart R ι i
  let b := eulerPolynomialChart R ι k
  let q := pullback.snd a b
  let c := (Scheme.Modules.overlapRestrictIso a b).app Ω
  let he := eulerPolynomialOverlap_image R ι i k W
  let hk := eulerPolynomialChart_image_le R ι k (q ''ᵁ W)
  let hki := he.le.trans hk
  let d := Scheme.Modules.Differentials.relativeDifferentialDerivation (toSpec R ι)
  let ti := eulerCoordinateRatio R ι k j hki
  let tk := eulerCoordinateRatio R ι k j hk
  have hd : c.hom.val.app (op W) (d.d ti) = d.d tk :=
    (eulerPolynomialOverlapIso_hom_app R ι i k Ω W (d.d ti)).trans
      ((d.d_map (eqToHom he.symm).op ti).symm.trans
        (congrArg d.d (eulerCoordinateRatio_restrict R ι k j he.symm.le hki)))
  exact (congrArg (c.inv.val.app (op W)) hd.symm).trans
    (congrArg (fun f => f.val.app (op W) (d.d ti)) c.hom_inv_id)

/-- The original-image section comparison of the actual chart arrows on the original ratio
relative differential, before applying either native overlap transport. -/
theorem eulerDifferentialOnPolynomialChart_overlap_d (i k j : ι)
    (W : (CategoryTheory.Limits.pullback
      (eulerPolynomialChart R ι i) (eulerPolynomialChart R ι k)).Opens) :
    let a := eulerPolynomialChart R ι i
    let b := eulerPolynomialChart R ι k
    let Vi := pullback.fst a b ''ᵁ W
    let Vk := pullback.snd a b ''ᵁ W
    let he := eulerPolynomialOverlap_image R ι i k W
    let hk := eulerPolynomialChart_image_le R ι k Vk
    let hki := he.le.trans hk
    let d := Scheme.Modules.Differentials.relativeDifferentialDerivation (toSpec R ι)
    (eulerMiddle R ι).presheaf.map (eqToHom he.symm).op
      ((eulerDifferentialOnPolynomialChart R ι i).val.app (op Vi)
        (d.d (eulerCoordinateRatio R ι k j hki))) =
      (eulerDifferentialOnPolynomialChart R ι k).val.app (op Vk)
        (d.d (eulerCoordinateRatio R ι k j hk)) := by
  dsimp only
  let a := eulerPolynomialChart R ι i
  let b := eulerPolynomialChart R ι k
  let Vi := pullback.fst a b ''ᵁ W
  let Vk := pullback.snd a b ''ᵁ W
  let he := eulerPolynomialOverlap_image R ι i k W
  let hk := eulerPolynomialChart_image_le R ι k Vk
  let hki := he.le.trans hk
  let B : Γ(eulerMiddle R ι, a ''ᵁ Vi) → Γ(eulerMiddle R ι, b ''ᵁ Vk) :=
    (eulerMiddle R ι).presheaf.map (eqToHom he.symm).op
  have hi := eulerDifferentialOnPolynomialChart_d_other_ratio R ι i k j Vi hki
  have hk' := eulerDifferentialOnPolynomialChart_d_ratio_any_open R ι k j Vk
  have hh := congrArg B hi
  exact hh.trans ((eulerKernelGenerator_restrict R ι k j he.symm.le hki).trans hk'.symm)

/-- The actual native overlap transports identify the original relative differential values
of the actual chart Euler arrows. -/
theorem eulerDifferentialOnPolynomialChart_overlap_d_transport (i k j : ι)
    (W : (CategoryTheory.Limits.pullback
      (eulerPolynomialChart R ι i) (eulerPolynomialChart R ι k)).Opens) :
    let Ω := Scheme.Modules.Differentials.relativeDifferentialSheaf (toSpec R ι)
    let a := eulerPolynomialChart R ι i
    let b := eulerPolynomialChart R ι k
    let p := pullback.fst a b
    let q := pullback.snd a b
    let cΩ := (Scheme.Modules.overlapRestrictIso a b).app Ω
    let cE := (Scheme.Modules.overlapRestrictIso a b).app (eulerMiddle R ι)
    let tk := eulerCoordinateRatio R ι k j
      (eulerPolynomialChart_image_le R ι k (q ''ᵁ W))
    let d := Scheme.Modules.Differentials.relativeDifferentialDerivation (toSpec R ι)
    (cΩ.inv ≫ (Scheme.Modules.restrictFunctor p).map
      (eulerDifferentialOnPolynomialChart R ι i) ≫ cE.hom).val.app (op W) (d.d tk) =
      ((Scheme.Modules.restrictFunctor q).map
        (eulerDifferentialOnPolynomialChart R ι k)).val.app (op W) (d.d tk) := by
  intro Ω a b p q cΩ cE tk d
  change cE.hom.val.app (op W) ((eulerDifferentialOnPolynomialChart R ι i).val.app
    (op (p ''ᵁ W)) (cΩ.inv.val.app (op W) (d.d tk))) =
      (eulerDifferentialOnPolynomialChart R ι k).val.app (op (q ''ᵁ W)) (d.d tk)
  let E := eulerMiddle R ι
  let Vi := p ''ᵁ W
  let Vk := q ''ᵁ W
  let Ti := a ''ᵁ Vi
  let Tk := b ''ᵁ Vk
  let he := eulerPolynomialOverlap_image R ι i k W
  let hk := eulerPolynomialChart_image_le R ι k Vk
  let hki := he.le.trans hk
  let ti := eulerCoordinateRatio R ι k j hki
  let A : Γ(Ω, Ti) → Γ(E, Ti) :=
    (eulerDifferentialOnPolynomialChart R ι i).val.app (op Vi)
  let B : Γ(E, Ti) → Γ(E, Tk) := E.presheaf.map (eqToHom he.symm).op
  have hd : cΩ.inv.val.app (op W) (d.d tk) = d.d ti :=
    eulerPolynomialOverlapIso_inv_d_ratio R ι i k j W
  have hA : A (cΩ.inv.val.app (op W) (d.d tk)) = A (d.d ti) := congrArg A hd
  have h₀ : cE.hom.val.app (op W) (A (cΩ.inv.val.app (op W) (d.d tk))) =
      B (A (cΩ.inv.val.app (op W) (d.d tk))) :=
    eulerPolynomialOverlapIso_hom_app R ι i k E W _
  have h₁ : B (A (cΩ.inv.val.app (op W) (d.d tk))) = B (A (d.d ti)) :=
    congrArg B hA
  have h₂ : B (A (d.d ti)) =
      (eulerDifferentialOnPolynomialChart R ι k).val.app (op Vk) (d.d tk) :=
    eulerDifferentialOnPolynomialChart_overlap_d R ι i k j W
  exact h₀.trans (h₁.trans h₂)

/-- The literal transported actual chart arrows agree on every original restricted differential
basis section. -/
theorem eulerDifferentialOnPolynomialChart_overlap_freeSection (i k : ι)
    (j : {j : ι // j ≠ k})
    (W : (CategoryTheory.Limits.pullback
      (eulerPolynomialChart R ι i) (eulerPolynomialChart R ι k)).Opens) :
    let Ω := Scheme.Modules.Differentials.relativeDifferentialSheaf (toSpec R ι)
    let a := eulerPolynomialChart R ι i
    let b := eulerPolynomialChart R ι k
    let p := pullback.fst a b
    let q := pullback.snd a b
    let cΩ := (Scheme.Modules.overlapRestrictIso a b).app Ω
    let cE := (Scheme.Modules.overlapRestrictIso a b).app (eulerMiddle R ι)
    let frame := (eulerOmegaOverlapFreeIso R ι k q).hom
    let v := (SheafOfModules.freeSection
      (R := (CategoryTheory.Limits.pullback a b).ringCatSheaf) j).val (op W)
    (frame ≫ cΩ.inv ≫ (Scheme.Modules.restrictFunctor p).map
      (eulerDifferentialOnPolynomialChart R ι i) ≫ cE.hom).val.app (op W) v =
      (frame ≫ (Scheme.Modules.restrictFunctor q).map
        (eulerDifferentialOnPolynomialChart R ι k)).val.app (op W) v := by
  intro Ω a b p q cΩ cE frame s
  let F := (cΩ.inv ≫ (Scheme.Modules.restrictFunctor p).map
    (eulerDifferentialOnPolynomialChart R ι i) ≫ cE.hom).val.app (op W)
  let G := ((Scheme.Modules.restrictFunctor q).map
    (eulerDifferentialOnPolynomialChart R ι k)).val.app (op W)
  let d := Scheme.Modules.Differentials.relativeDifferentialDerivation (toSpec R ι)
  let t := eulerCoordinateRatio R ι k j.val
    (eulerPolynomialChart_image_le R ι k (q ''ᵁ W))
  let v := frame.val.app (op W) s
  have hv : v = d.d t := eulerOmegaOverlapFreeIso_hom_freeSection R ι k q j W
  have hD₀ := eulerDifferentialOnPolynomialChart_overlap_d_transport R ι i k j.val W
  dsimp only at hD₀
  have hD : F (d.d t) = G (d.d t) := by
    unfold F G cΩ cE d t p q Ω a b
    exact hD₀
  have hFv : F v = F (d.d t) := congrArg F hv
  have hGv : G v = G (d.d t) := congrArg G hv
  change F v = G v
  exact hFv.trans (hD.trans hGv.symm)

/-- The literal actual relative Euler chart arrows agree through the native pullback-overlap
restriction comparison. -/
theorem eulerDifferentialOnPolynomialChart_overlap (i k : ι) :
    (Scheme.Modules.restrictFunctor (pullback.fst
      (eulerPolynomialChart R ι i) (eulerPolynomialChart R ι k))).map
        (eulerDifferentialOnPolynomialChart R ι i) ≫
      (Scheme.Modules.overlapRestrictIso
        (eulerPolynomialChart R ι i) (eulerPolynomialChart R ι k)).hom.app (eulerMiddle R ι) =
    (Scheme.Modules.overlapRestrictIso
      (eulerPolynomialChart R ι i) (eulerPolynomialChart R ι k)).hom.app
        (Scheme.Modules.Differentials.relativeDifferentialSheaf (toSpec R ι)) ≫
      (Scheme.Modules.restrictFunctor (pullback.snd
        (eulerPolynomialChart R ι i) (eulerPolynomialChart R ι k))).map
          (eulerDifferentialOnPolynomialChart R ι k) := by
  have hfree {Z : Scheme.{u}} {J : Type u} {N : Z.Modules}
      (f g : SheafOfModules.free (R := Z.ringCatSheaf) J ⟶ N)
      (h : ∀ (j : J) (V : Z.Opens), f.val.app (op V)
        ((SheafOfModules.freeSection (R := Z.ringCatSheaf) j).val (op V)) =
          g.val.app (op V)
            ((SheafOfModules.freeSection (R := Z.ringCatSheaf) j).val (op V))) : f = g := by
    apply N.freeHomEquiv.injective
    funext j
    ext V
    change f.val.app V ((SheafOfModules.freeSection (R := Z.ringCatSheaf) j).val V) =
      g.val.app V ((SheafOfModules.freeSection (R := Z.ringCatSheaf) j).val V)
    exact h j V.unop
  change (Scheme.Modules.restrictFunctor (pullback.fst
      (eulerPolynomialChart R ι i) (eulerPolynomialChart R ι k))).map
        (eulerDifferentialOnPolynomialChart R ι i) ≫
      ((Scheme.Modules.overlapRestrictIso
        (eulerPolynomialChart R ι i) (eulerPolynomialChart R ι k)).app (eulerMiddle R ι)).hom =
    ((Scheme.Modules.overlapRestrictIso
      (eulerPolynomialChart R ι i) (eulerPolynomialChart R ι k)).app
        (Scheme.Modules.Differentials.relativeDifferentialSheaf (toSpec R ι))).hom ≫
      (Scheme.Modules.restrictFunctor (pullback.snd
        (eulerPolynomialChart R ι i) (eulerPolynomialChart R ι k))).map
          (eulerDifferentialOnPolynomialChart R ι k)
  apply (cancel_epi ((Scheme.Modules.overlapRestrictIso
    (eulerPolynomialChart R ι i) (eulerPolynomialChart R ι k)).app
      (Scheme.Modules.Differentials.relativeDifferentialSheaf (toSpec R ι))).inv).1
  simp only [Iso.inv_hom_id_assoc]
  apply (cancel_epi (eulerOmegaOverlapFreeIso R ι k
    (pullback.snd (eulerPolynomialChart R ι i) (eulerPolynomialChart R ι k))).hom).1
  apply hfree
  intro j W
  exact eulerDifferentialOnPolynomialChart_overlap_freeSection R ι i k j W

end AlgebraicGeometry.ProjectiveSpace
