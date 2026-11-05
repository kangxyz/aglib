/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import
  Aglib.AlgebraicGeometry.EtaleCohomology.SupportInduction.ArithmeticPointedDegreeEffacement
public import Aglib.AlgebraicGeometry.Morphisms.Etale.PointedTargetRestriction
public import Aglib.AlgebraicGeometry.EtaleCohomology.Localization.CoefficientCartesianTargetZero

/-! # Arithmetic curve fixed-degree effacement without an affine target assumption

The same geometric point factors through an actual affine open. The proved
affine producer kills its original restricted class. Canonical Cartesian
transport returns that zero to the unchanged original family and coefficient.
Only the coefficient and base spectra remain affine.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme.EtaleCohomology
open Coefficients
universe u
attribute [local instance] hasSheafifyLarge hasSheafifyModules HasExt.standard

/-- The original arithmetic curve class is locally zero at its original mark. -/
theorem exists_arithmetic_curve_pointed_degree_refinement_of_all_ranks
    (k : ℕ) (ih : ∀ d, ArithmeticPointedCurveModuleEffacement.{u} k d)
    (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.FiniteType ℤ R] [Algebra.FiniteType ℤ S]
    {X Y : Scheme.{u}} (p : X ⟶ Spec (.of R)) [SmoothOfRelativeDimension 1 p]
    (a : Y ⟶ X) (b : Y ⟶ Spec (.of S))
    (H : IsPullback a b p (Spec.algebraMap R S))
    (n : ℕ) (hn : 0 < n) (hunit : IsUnit (n : R))
    (I : ModuleSheaf (Spec (.of S)) (ULift.{u + 1} (ZMod n))) [Injective I]
    (c : Sheaf.H.{u + 2} ((inverseImage b).obj
      ((SheafOfModules.toSheaf (constantRing (Spec (.of S))
        (ULift.{u + 1} (ZMod n)))).obj I)) k)
    (Ω : Type u) [Field Ω] [IsSepClosed Ω] (x : Spec (.of Ω) ⟶ X) :
    ∃ (U : X.Etale) (xU : Spec (.of Ω) ⟶ U.left), xU ≫ U.hom = x ∧
      cohomologyPullback.{u, u + 2, u + 2} (pullback.snd U.hom a) _ k c = 0 := by
  obtain ⟨C, hC, hCΩ, j, hj, hx⟩ := Scheme.exists_affineSpec_chart_of_fieldPoint Ω x
  let : CommRing C := hC
  let : Algebra C Ω := hCΩ
  let : IsOpenImmersion j := hj
  let : Algebra R C := (Spec.preimage (j ≫ p)).hom.toAlgebra
  have hpC : Spec.algebraMap R C = j ≫ p := Spec.map_preimage (j ≫ p)
  let : SmoothOfRelativeDimension 1 (j ≫ p) := by
    simpa only [Nat.zero_add] using smoothOfRelativeDimension_comp 0 1 j p
  let : SmoothOfRelativeDimension 1 (Spec.algebraMap R C) := hpC.symm ▸ inferInstance
  let v := pullback.snd j a
  let aC := pullback.fst j a
  let bC := v ≫ b
  have Hopen : IsPullback aC v j a := IsPullback.of_hasPullback j a
  have HC : IsPullback aC bC (Spec.algebraMap R C) (Spec.algebraMap R S) := by
    rw [hpC]
    exact Hopen.paste_vert H
  let Λ := ULift.{u + 1} (ZMod n)
  let i := 𝟙 (Spec (.of S))
  have hi : v ≫ b = bC ≫ i := (Category.comp_id _).symm
  let J := (moduleInverseImage i Λ).obj I
  let : Injective J := moduleInverseImage_etale_injective i Λ I
  let cC := moduleCoefficientComponentClass i v b bC hi Λ I k c
  obtain ⟨V, z, hz, hc⟩ := exists_arithmetic_pointed_degree_refinement_of_all_ranks
    k ih R S C aC bC HC n hn hunit J cC Ω (Spec.algebraMap C Ω)
  let t : V.left ⟶ Spec (.of C) := V.hom
  let : Etale t := V.prop
  let U : X.Etale := Scheme.Etale.mk (t ≫ j)
  refine ⟨U, z, ?_, ?_⟩
  · exact (Category.assoc z t j).symm.trans
      ((congrArg (fun k : Spec (.of Ω) ⟶ Spec (.of C) => k ≫ j) hz).trans hx)
  · exact moduleCoefficientComponentClass_target_zero i v b bC hi j a aC Hopen
      t Λ I k c hc

end AlgebraicGeometry.Scheme.EtaleCohomology
