/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Aglib.AlgebraicGeometry.ProjectiveSpace.Differentials.Euler.LocalExact
public import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing
public import Mathlib.RingTheory.Derivation.Basic
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.Ring

/-!
# Original transition formulas for the actual relative Euler arrows

The original coordinate transition unit is the inverse of the original chart ratio. The
original inverse twist and Euler tensor generators retain that same unit. The original
relative differential and the original kernel vectors obey the same quotient transition
formula. The checked actual chart differential formula extends to every native chart open.
No field, finiteness, nontriviality, or exactness-family hypothesis is used.
-/

@[expose] public section
noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.MonoidalCategory Opposite
open AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.Invertible
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

end AlgebraicGeometry.ProjectiveSpace
