/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aglib contributors
-/
module

public import Aglib.Algebra.Homology.DerivedCategory.KInjective.Existence.Tower.QuasiIso
public import Aglib.Algebra.Homology.DerivedCategory.KInjective.Existence.Detection.Basic

/-!
# The actual functorial unbounded K-injective replacement

The uniform regular stage is specialized to the constructed small acyclic tests.
Its original natural augmentation is monic and a quasi-isomorphism. Its terms
are injective, and the native detection theorem proves K-injectivity.
-/

@[expose] public noncomputable section

universe w v u

open CategoryTheory CategoryTheory.Limits

namespace CochainComplex

variable {C : Type u} [Category.{v} C] [Abelian C] [IsGrothendieckAbelian.{w} C]
  {G : C} (hG : IsSeparator G)

/-- The actual uniform regular-stage replacement, with a chosen separator. -/
abbrev kInjectiveReplacementFunctor : CochainComplex C ℤ ⥤ CochainComplex C ℤ :=
  regularReplacementFunctor (smallAcyclicTests hG) G

/-- The original natural augmentation of the constructed replacement. -/
abbrev kInjectiveReplacementUnit :
    𝟭 (CochainComplex C ℤ) ⟶ kInjectiveReplacementFunctor hG :=
  regularReplacementUnit (smallAcyclicTests hG) G

instance kInjectiveReplacementUnit_mono (K : CochainComplex C ℤ) :
    Mono ((kInjectiveReplacementUnit hG).app K) := inferInstance

instance kInjectiveReplacementUnit_quasiIso (K : CochainComplex C ℤ) :
    QuasiIso ((kInjectiveReplacementUnit hG).app K) :=
  regularReplacementUnit_quasiIso (smallAcyclicTests hG)
    (smallAcyclicTests_acyclic hG) G K

instance kInjectiveReplacement_injective (K : CochainComplex C ℤ) (n : ℤ) :
    Injective (((kInjectiveReplacementFunctor hG).obj K).X n) :=
  regularReplacement_injective (smallAcyclicTests hG) G hG K n

instance kInjectiveReplacement_isKInjective (K : CochainComplex C ℤ) :
    ((kInjectiveReplacementFunctor hG).obj K).IsKInjective := by
  apply isKInjective_of_smallAcyclicTests hG
  intro i f
  exact regularReplacement_test_nullhomotopic (smallAcyclicTests hG) G K i f

end CochainComplex
