/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.SupportInduction.ArithmeticEtaleSection
public import Aglib.AlgebraicGeometry.EtaleCohomology.Localization.JacobsonPointedClassZero
public import Aglib.AlgebraicGeometry.Morphisms.Smooth.ArithmeticClosedPointSection

/-! # Arbitrary original arithmetic curve marks from the all-ranks property

Closed points of the original arithmetic smooth affine curve have finite
residue fields. Each unchanged residue point admits a genuine etale base
section. The all-ranks property produces a zero after restriction of the
same injective coefficient, and Cartesian transport returns the original
class. These actual etale zero charts cover all closed points. Jacobson
coverage and native etale point lifting then retain any prescribed original
separably closed field-valued point over that same field.

The all-ranks property remains an explicit theorem input; it is not proved
here. There is no additional local-zero, point-lifting, injectivity-preserving,
or open-vanishing-locus premise.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.EtaleCohomology

open Coefficients

universe u

attribute [local instance] hasSheafifyLarge hasSheafifyModules HasExt.standard

/-- The genuine all-ranks curve property implies arbitrary-point effacement
for every original affine arithmetic smooth relative curve and arithmetic
coefficient arrow. The target point, its field, the injective and the original
class are retained in the final whole-pullback zero. -/
theorem exists_arithmetic_pointed_H1_refinement_of_all_ranks
    (ih : ∀ d, PointedCurveModuleInjectiveH1Effacement.{u} d)
    (R S B : Type u) [CommRing R] [CommRing S] [CommRing B]
    [Algebra R S] [Algebra R B]
    [Algebra.FiniteType ℤ R] [Algebra.FiniteType ℤ S]
    [SmoothOfRelativeDimension 1 (Spec.algebraMap R B)]
    {Y : Scheme.{u}} (a : Y ⟶ Spec (.of B)) (b : Y ⟶ Spec (.of S))
    (H : IsPullback a b (Spec.algebraMap R B) (Spec.algebraMap R S))
    (n : ℕ) (hn : 0 < n) (hunit : IsUnit (n : R))
    (I : ModuleSheaf (Spec (.of S)) (ULift.{u + 1} (ZMod n))) [Injective I]
    (c : Sheaf.H.{u + 2} ((inverseImage b).obj
      ((SheafOfModules.toSheaf (constantRing (Spec (.of S))
        (ULift.{u + 1} (ZMod n)))).obj I)) 1)
    (Ω : Type u) [Field Ω] [IsSepClosed Ω] (x : Spec (.of Ω) ⟶ Spec (.of B)) :
    ∃ (U : (Spec (.of B)).Etale) (xU : Spec (.of Ω) ⟶ U.left),
      xU ≫ U.hom = x ∧
      cohomologyPullback.{u, u + 2, u + 2} (pullback.snd U.hom a) _ 1 c = 0 := by
  let p := Spec.algebraMap R B
  let : Smooth p := SmoothOfRelativeDimension.smooth 1 p
  let : Algebra.Smooth R B := RingHom.smooth_algebraMap.mp
    (HasRingHomProperty.Spec_iff.mp (inferInstance : Smooth p))
  let : IsJacobsonRing ℤ := Algebra.Smooth.integers_jacobson
  let : IsJacobsonRing R := isJacobsonRing_of_finiteType (A := ℤ) (B := R)
  let : JacobsonSpace (Spec (.of B)) := LocallyOfFiniteType.jacobsonSpace p
  apply exists_pointed_class_zero_of_closedPoint_charts a _ 1 c ?_ Ω x
  intro x₀ hx₀
  obtain ⟨E, hE, hRE, het, hft, σ, l, hσ, hl⟩ :=
    exists_etale_baseChangeSection_through_arithmetic_closedPoint R B x₀ hx₀
  let : CommRing E := hE
  let : Algebra R E := hRE
  let : Algebra.Etale R E := het
  let : Algebra.FiniteType ℤ E := hft
  let L := (Spec (.of B)).residueField x₀
  let K := AlgebraicClosure L
  let ξ : Spec (.of K) ⟶ Spec (.of E) := Spec.algebraMap L K ≫ l
  obtain ⟨U, z, hz, hc⟩ := exists_pointed_H1_refinement_of_arithmetic_etale_section
    ih R S E p σ hσ a b H n hn hunit I c K ξ
  have hz' : z ≫ U.hom =
      Spec.algebraMap L K ≫ (Spec (.of B)).fromSpecResidueField x₀ := by
    calc
      z ≫ U.hom = Spec.algebraMap L K ≫
          (l ≫ σ ≫ pullback.fst p (Spec.algebraMap R E)) := by
        simpa only [ξ, Category.assoc] using hz
      _ = _ := congrArg (fun f : Spec (.of L) ⟶ Spec (.of B) =>
        Spec.algebraMap L K ≫ f) hl
  refine ⟨U, z default, ?_, hc⟩
  have hpoint := congrArg (fun f : Spec (.of K) ⟶ Spec (.of B) => f default) hz'
  exact hpoint.trans (Scheme.fromSpecResidueField_apply (X := Spec (.of B)) x₀
    ((Spec.algebraMap L K) default))

end AlgebraicGeometry.Scheme.EtaleCohomology
