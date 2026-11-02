/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.DerivedCategory.UnboundedRightDerived.Comparison
public import Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.SingleHomology
public import Mathlib.Algebra.Homology.DerivedCategory.SingleTriangle

/-! # Dimension shifting for the original unbounded derived functor

The single-object cohomology comparison uses the existing bounded-below comparison.
All exact sequences below come from the original short-exact single triangle.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

universe s u v w u' v' w'

namespace CategoryTheory.Functor

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
  [IsGrothendieckAbelian.{s} C]
  {D : Type u'} [Category.{v'} D] [Abelian D] [HasDerivedCategory.{w'} D]
  (F : C ⥤ D) [F.Additive]

/-- Original higher derived objects are the cohomology of the same unbounded functor. -/
def rightDerivedUnboundedSingleHomologyIso (n : ℕ) :
    F.rightDerived n ≅ DerivedCategory.singleFunctor C 0 ⋙
      F.unboundedRightDerivedFunctor ⋙ DerivedCategory.homologyFunctor D (n : ℤ) :=
  F.rightDerivedSingleHomologyIso n ≪≫
    isoWhiskerLeft (DerivedCategory.Plus.singleFunctor C 0)
      (isoWhiskerRight F.unboundedRightDerivedFunctorPlusIso
        (DerivedCategory.homologyFunctor D (n : ℤ)))

/-- One vanishing step in the original long exact sequence. No finite dimension
assumption is used in this local dimension-shift step. -/
theorem isZero_rightDerived_X₃_of_shortExact
    {S : ShortComplex C} (hS : S.ShortExact) (n : ℕ)
    (h₂ : IsZero ((F.rightDerived n).obj S.X₂))
    (h₁ : IsZero ((F.rightDerived (n + 1)).obj S.X₁)) :
    IsZero ((F.rightDerived n).obj S.X₃) := by
  let T := F.unboundedRightDerivedFunctor.mapTriangle.obj hS.singleTriangle
  have hT : T ∈ distTriang (DerivedCategory D) :=
    F.unboundedRightDerivedFunctor.map_distinguished _ hS.singleTriangle_distinguished
  have hz₂ : IsZero ((DerivedCategory.homologyFunctor D (n : ℤ)).obj T.obj₂) :=
    (F.rightDerivedUnboundedSingleHomologyIso n).app S.X₂ |>.isZero_iff.mp h₂
  have hz₁ : IsZero ((DerivedCategory.homologyFunctor D ((n + 1 : ℕ) : ℤ)).obj T.obj₁) :=
    (F.rightDerivedUnboundedSingleHomologyIso (n + 1)).app S.X₁ |>.isZero_iff.mp h₁
  have hz₃ := (DerivedCategory.HomologySequence.exact₃ T hT
    (n : ℤ) ((n + 1 : ℕ) : ℤ) (by omega)).isZero_X₂
      (hz₂.eq_of_src _ _) (hz₁.eq_of_tgt _ _)
  exact (F.rightDerivedUnboundedSingleHomologyIso n).app S.X₃ |>.isZero_iff.mpr hz₃

variable [PreservesFiniteLimits F]

/-- Vanishing of the actual first derived object of the kernel makes the original
image of a short exact sequence short exact. -/
theorem shortExact_map_of_isZero_rightDerived_one
    {S : ShortComplex C} (hS : S.ShortExact)
    (h₁ : IsZero ((F.rightDerived 1).obj S.X₁)) : (S.map F).ShortExact := by
  let T := F.unboundedRightDerivedFunctor.mapTriangle.obj hS.singleTriangle
  have hT : T ∈ distTriang (DerivedCategory D) :=
    F.unboundedRightDerivedFunctor.map_distinguished _ hS.singleTriangle_distinguished
  have hz₁ : IsZero ((DerivedCategory.homologyFunctor D 1).obj T.obj₁) :=
    (F.rightDerivedUnboundedSingleHomologyIso 1).app S.X₁ |>.isZero_iff.mp h₁
  have he : Epi ((DerivedCategory.homologyFunctor D 0).map T.mor₂) :=
    (DerivedCategory.HomologySequence.epi_homologyMap_mor₂_iff T hT 0 1).mpr
      (hz₁.eq_of_tgt _ _)
  change Epi ((DerivedCategory.singleFunctor C 0 ⋙ F.unboundedRightDerivedFunctor ⋙
    DerivedCategory.homologyFunctor D (0 : ℕ)).map S.g) at he
  let e := (F.rightDerivedUnboundedSingleHomologyIso 0).symm ≪≫ F.rightDerivedZeroIsoSelf
  have he' : Epi ((e.hom.app S.X₂) ≫ F.map S.g) := by
    rw [← e.hom.naturality S.g]
    exact epi_comp _ _
  have : Epi (F.map S.g) := epi_of_epi (e.hom.app S.X₂) _
  have := hS.mono_f
  exact { exact := hS.exact.map_of_mono_of_preservesKernel F inferInstance inferInstance
          mono_f := by change Mono (F.map S.f); infer_instance
          epi_g := by change Epi (F.map S.g); infer_instance }

end CategoryTheory.Functor
