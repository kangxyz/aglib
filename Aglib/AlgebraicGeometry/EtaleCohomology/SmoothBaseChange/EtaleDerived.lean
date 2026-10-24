/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.SmoothBaseChange.Etale
public import Aglib.Algebra.Homology.DerivedCategory.Plus.SingleComparison
public import Aglib.Algebra.Homology.DerivedCategory.Plus.Postnikov.Comparison

/-! # Canonical étale base change on the actual bounded-below derived category

The original all-degree comparison gives the degree-zero single theorem.
Native shift compatibility and finite Postnikov comparison give the original
D+ exchange, retaining four independent derived-category universes.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits

universe u dX dS dX' dS'

namespace AlgebraicGeometry.Scheme.EtaleCohomology

attribute [local instance] hasSheafifyLarge

variable {X S S' : Scheme.{u}} (f : X ⟶ S) (g : S' ⟶ S) [Etale g]
  [HasDerivedCategory.{dX} (AbelianSheaf.{u, u + 1} X)]
  [HasDerivedCategory.{dS} (AbelianSheaf.{u, u + 1} S)]
  [HasDerivedCategory.{dX'} (AbelianSheaf.{u, u + 1} (pullback g f))]
  [HasDerivedCategory.{dS'} (AbelianSheaf.{u, u + 1} S')]

/-- The original étale derived exchange is invertible on singles in every
integer degree, using its original shift compatibility. -/
theorem derivedBaseChangeMap_etale_single_degree_isIso
    (F : AbelianSheaf.{u, u + 1} X) (i : ℤ) :
    IsIso ((derivedBaseChangeMap f (pullback.fst g f) g (pullback.snd g f)
      pullback.condition).app
        ((DerivedCategory.Plus.singleFunctor (AbelianSheaf.{u, u + 1} X) i).obj F)) := by
  let τ := derivedBaseChangeMap f (pullback.fst g f) g (pullback.snd g f)
    pullback.condition
  let : NatTrans.CommShift τ ℤ :=
    Proper.Reduction.derivedBaseChangeMap_commShift f (pullback.fst g f) g
      (pullback.snd g f) pullback.condition
  let : IsIso (τ.app
      ((DerivedCategory.Plus.singleFunctor (AbelianSheaf.{u, u + 1} X) 0).obj F)) :=
    derivedBaseChangeMap_etale_single_isIso f g F
  exact DerivedCategory.Plus.isIso_app_single_of_zero τ F i

/-- Canonical étale base change on the actual bounded-below derived category.
The four derived-category universes remain independent. -/
theorem derivedBaseChangeMap_etale_isIso :
    IsIso (derivedBaseChangeMap f (pullback.fst g f) g (pullback.snd g f)
      pullback.condition) := by
  let τ := derivedBaseChangeMap f (pullback.fst g f) g (pullback.snd g f)
    pullback.condition
  let : NatTrans.CommShift τ ℤ :=
    Proper.Reduction.derivedBaseChangeMap_commShift f (pullback.fst g f) g
      (pullback.snd g f) pullback.condition
  apply DerivedCategory.Plus.isIso_of_singles τ
  · intro K n hK
    let : K.IsGE n := hK
    let : ((derivedDirectImage f).obj K).IsGE n :=
      (directImage f).rightDerivedFunctorPlus_isGE K n
    exact (inverseImage g).rightDerivedFunctorPlus_isGE ((derivedDirectImage f).obj K) n
  · intro K n hK
    let : K.IsGE n := hK
    let : ((derivedInverseImage (pullback.snd g f)).obj K).IsGE n :=
      (inverseImage (pullback.snd g f)).rightDerivedFunctorPlus_isGE K n
    exact (directImage (pullback.fst g f)).rightDerivedFunctorPlus_isGE
      ((derivedInverseImage (pullback.snd g f)).obj K) n
  · exact derivedBaseChangeMap_etale_single_degree_isIso f g

end AlgebraicGeometry.Scheme.EtaleCohomology
