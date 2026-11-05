/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.SmoothBaseChange.ArithmeticHigherProducer
public import Aglib.AlgebraicGeometry.EtaleCohomology.SupportInduction.ArithmeticCurvePointedDegree
public import
  Aglib.AlgebraicGeometry.EtaleCohomology.SupportInduction.ArithmeticCurvePointedProducer

/-! # Arithmetic pointed curve effacement in every positive degree

The accepted degree-one producer and the completed outer degree induction
supply the original pointed rank producer in every positive degree. No
lower-degree vanishing or coefficient-rank premise remains. The original
curve, coefficient, class and separably closed geometric point are unchanged.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme.EtaleCohomology
open Coefficients
universe u
attribute [local instance] hasSheafifyLarge hasSheafifyModules HasExt.standard

/-- The original arithmetic curve class is locally zero at its original mark. -/
theorem exists_arithmetic_curve_pointed_positive_refinement
    (q : ℕ) (hq : 0 < q)
    (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.FiniteType ℤ R] [Algebra.FiniteType ℤ S]
    {X Y : Scheme.{u}} (p : X ⟶ Spec (.of R)) [SmoothOfRelativeDimension 1 p]
    (a : Y ⟶ X) (b : Y ⟶ Spec (.of S))
    (H : IsPullback a b p (Spec.algebraMap R S))
    (n : ℕ) (hn : 0 < n) (hunit : IsUnit (n : R))
    (I : ModuleSheaf (Spec (.of S)) (ULift.{u + 1} (ZMod n))) [Injective I]
    (c : Sheaf.H.{u + 2} ((inverseImage b).obj
      ((SheafOfModules.toSheaf (constantRing (Spec (.of S))
        (ULift.{u + 1} (ZMod n)))).obj I)) q)
    (Ω : Type u) [Field Ω] [IsSepClosed Ω] (x : Spec (.of Ω) ⟶ X) :
    ∃ (U : X.Etale) (xU : Spec (.of Ω) ⟶ U.left), xU ≫ U.hom = x ∧
      cohomologyPullback.{u, u + 2, u + 2} (pullback.snd U.hom a) _ q c = 0 := by
  by_cases hq1 : q = 1
  · subst q
    exact exists_arithmetic_curve_pointed_H1_refinement R S p a b H n hn hunit I c Ω x
  have hq2 : 2 ≤ q := by omega
  have hranks : ∀ d, ArithmeticPointedCurveModuleEffacement.{u} q d :=
    arithmeticPointedCurveModuleEffacement_of_lower_degrees q hq2
      (fun r hr _ => arithmeticCurveModuleInjectiveVanishing_positive r (by omega))
  exact exists_arithmetic_curve_pointed_degree_refinement_of_all_ranks
    q hranks R S p a b H n hn hunit I c Ω x

end AlgebraicGeometry.Scheme.EtaleCohomology
