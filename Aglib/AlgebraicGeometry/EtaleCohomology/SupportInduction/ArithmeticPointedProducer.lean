/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.SupportInduction.ArithmeticPointedEffacement
public import Aglib.AlgebraicGeometry.EtaleCohomology.SupportInduction.NagataPointedProducer

/-! # Arithmetic curve H1 effacement at the original geometric point

The general rank construction supplies its full property internally. The
arithmetic closed-point and Jacobson argument retains the same original
geometric point, coefficient, class and target pullback. This leaf only
specializes those constructions; it adds neither a vanishing premise nor
a new model. Its conclusion is curve H1 effacement, not full smooth base
change in arbitrary relative dimension and degree.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.EtaleCohomology

open Coefficients

universe u

attribute [local instance] hasSheafifyLarge hasSheafifyModules HasExt.standard

/-- An original class pulled from an injective finite-torsion coefficient
admits an etale zero chart retaining any original separably closed geometric
point of an affine arithmetic smooth curve. The rank property is produced
internally, rather than assumed by this endpoint. -/
theorem exists_arithmetic_pointed_H1_refinement
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
      cohomologyPullback.{u, u + 2, u + 2} (pullback.snd U.hom a) _ 1 c = 0 :=
  exists_arithmetic_pointed_H1_refinement_of_all_ranks
    (fun d => pointedCurveModuleInjectiveH1Effacement.{u} d)
    R S B a b H n hn hunit I c Ω x

end AlgebraicGeometry.Scheme.EtaleCohomology
