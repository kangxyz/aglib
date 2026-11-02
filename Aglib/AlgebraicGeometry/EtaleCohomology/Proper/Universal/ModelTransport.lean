/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Proper.Universal.Basic

/-!
# Original bounded exchange in independently supplied derived models

The original source/mate/target transport is exactly the intrinsic ordinary
higher map in every degree. Its selected derived models remain explicit at
this compatibility boundary. The original bounded-exchange predicate therefore
supplies invertibility of the original transport without another reference model.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Proper

private theorem isIso_iff_of_normalization
    {C : Type*} [Category* C] {A B D E : C}
    (s : A ≅ B) (t : D ≅ E) (a : B ⟶ E) (b : A ⟶ D)
    (h : s.hom ≫ a = b ≫ t.hom) : IsIso b ↔ IsIso a := by
  constructor
  · intro hb
    have := hb
    have hs : IsIso (s.hom ≫ a) := by rw [h]; infer_instance
    exact (isIso_comp_left_iff _ _).mp hs
  · intro ha
    have := ha
    have ht : IsIso (b ≫ t.hom) := by rw [← h]; infer_instance
    exact (isIso_comp_right_iff _ _).mp ht

universe u dX dS dX' dS'

attribute [local instance] hasSheafifyLarge

variable {X S X' S' : Scheme.{u}}
  [HasDerivedCategory.{dX} (AbelianSheaf.{u, u + 1} X)]
  [HasDerivedCategory.{dS} (AbelianSheaf.{u, u + 1} S)]
  [HasDerivedCategory.{dX'} (AbelianSheaf.{u, u + 1} X')]
  [HasDerivedCategory.{dS'} (AbelianSheaf.{u, u + 1} S')]
  (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
  (h : f' ≫ g = g' ≫ f)

/-- In every selected model, original degree-zero transport is invertible exactly
when the original ordinary exchange is invertible. -/
theorem higherBaseChangeMap_zero_isIso_iff (F : AbelianSheaf.{u, u + 1} X) :
    IsIso ((higherBaseChangeMapFromDerived f f' g g' h 0).app F) ↔
      IsIso ((baseChangeMap f f' g g' h).app F) := by
  rw [higherBaseChangeMapFromDerived_eq]
  exact isIso_iff_of_normalization
    ((inverseImage g).mapIso ((directImage f).rightDerivedZeroIsoSelf.app F))
    ((directImage f').rightDerivedZeroIsoSelf.app ((inverseImage g').obj F))
    ((baseChangeMap f f' g g' h).app F) ((higherBaseChangeMap f f' g g' h 0).app F)
    (higherBaseChangeMap_zero f f' g g' h F)

/-- Bounded exchange gives the ORIGINAL transport in four independently supplied
derived models and universes, through its exact all-degree equality bridge. -/
theorem higherBaseChangeMap_isIso_of_boundedExchange (n : ℕ)
    (hf : boundedExchange n f f' g g' h)
    (F : AbelianSheaf.{u, u + 1} X) (hF : n • 𝟙 F = 0) (q : ℕ) :
    IsIso ((higherBaseChangeMapFromDerived f f' g g' h q).app F) := by
  rw [higherBaseChangeMapFromDerived_eq]
  exact hf F hF q

end AlgebraicGeometry.Scheme.EtaleCohomology.Proper
