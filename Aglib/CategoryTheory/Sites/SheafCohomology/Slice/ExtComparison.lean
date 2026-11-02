/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.Ext.MapAdjunction

/-!
# Exact adjunction comparison with an identified source

All Ext equations are proved for abstract exact functors and the supplied
source isomorphism before instantiating the concrete slice construction.
-/

@[expose] public noncomputable section

universe w₁ w₂

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian

namespace CategoryTheory.Adjunction

variable {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
  [HasExt.{w₁} C] [HasExt.{w₂} D]
  {L : C ⥤ D} {R : D ⥤ C} [L.Additive] [R.Additive]
  [PreservesFiniteLimits L] [PreservesFiniteColimits L]
  [PreservesFiniteLimits R] [PreservesFiniteColimits R]
  (adj : L ⊣ R) {X : C} {Z : D} (e : L.obj X ≅ Z)

/-- The original Ext adjunction after the supplied source identification. -/
def sourceExtComparison (Y : D) (n : ℕ) : Ext.{w₂} Z Y n ≃+ Ext.{w₁} X (R.obj Y) n :=
  (((extFunctor n).mapIso e.op).app Y).addCommGroupIsoToAddEquiv.trans adj.extEquiv

/-- The comparison retains the original unit and source-isomorphism formula. -/
theorem sourceExtComparison_apply (Y : D) (n : ℕ) (x : Ext.{w₂} Z Y n) :
    adj.sourceExtComparison e Y n x =
      (Ext.mk₀ (adj.unit.app X ≫ R.map e.hom)).comp
        (x.mapExactFunctor R) (Nat.zero_add n) := by
  change (Ext.mk₀ (adj.unit.app X)).comp
    (((Ext.mk₀ e.hom).comp x (Nat.zero_add n)).mapExactFunctor R) (Nat.zero_add n) = _
  rw [Ext.mapExactFunctor_comp, Ext.mapExactFunctor_mk₀,
    ← Ext.comp_assoc _ _ _ (Nat.zero_add 0) (Nat.zero_add n) (Nat.zero_add n),
    Ext.mk₀_comp_mk₀]

/-- The comparison commutes with the original coefficient morphisms. -/
theorem sourceExtComparison_naturality {Y Y' : D} (f : Y ⟶ Y') (n : ℕ)
    (x : Ext.{w₂} Z Y n) :
    adj.sourceExtComparison e Y' n (x.comp (Ext.mk₀ f) (Nat.add_zero n)) =
      (adj.sourceExtComparison e Y n x).comp (Ext.mk₀ (R.map f)) (Nat.add_zero n) := by
  rw [sourceExtComparison_apply, sourceExtComparison_apply,
    Ext.mapExactFunctor_comp, Ext.mapExactFunctor_mk₀,
    Ext.comp_assoc _ _ _ (Nat.zero_add n) (Nat.add_zero n) (Nat.zero_add n)]

/-- In degree zero the exact comparison is the original Hom adjunction. -/
theorem sourceExtComparison_mk₀ (Y : D) (a : Z ⟶ Y) :
    adj.sourceExtComparison e Y 0 (Ext.mk₀ a) =
      Ext.mk₀ (adj.homEquiv X Y (e.hom ≫ a)) := by
  change adj.extEquiv ((Ext.mk₀ e.hom).comp (Ext.mk₀ a) (Nat.zero_add 0)) = _
  rw [Ext.mk₀_comp_mk₀, Adjunction.extEquiv_mk₀]

/-- Applying the exact left adjoint and the supplied inverse source transport
becomes postcomposition by the original coefficient unit. -/
theorem sourceExtComparison_mapExactFunctor (Y : C) (n : ℕ) (x : Ext.{w₁} X Y n) :
    adj.sourceExtComparison e (L.obj Y) n
        ((Ext.mk₀ e.inv).comp (x.mapExactFunctor L) (Nat.zero_add n)) =
      x.comp (Ext.mk₀ (adj.unit.app Y)) (Nat.add_zero n) := by
  change adj.extEquiv
      ((Ext.mk₀ e.hom).comp
        ((Ext.mk₀ e.inv).comp (x.mapExactFunctor L) (Nat.zero_add n))
          (Nat.zero_add n)) = _
  rw [Ext.mk₀_comp_mk₀_assoc, e.hom_inv_id, Ext.mk₀_id_comp]
  have h := adj.extEquiv_naturality_left x
    (Ext.mk₀ (𝟙 (L.obj Y))) (Nat.add_zero n)
  rw [Ext.comp_mk₀_id, Adjunction.extEquiv_mk₀] at h
  exact h.trans (congrArg (fun k => x.comp (Ext.mk₀ k) (Nat.add_zero n))
    (adj.homEquiv_id Y))

/-- The original exact-functor Ext map with inverse source transport is
bijective whenever the actual coefficient unit is an isomorphism. -/
theorem mapExactFunctor_precomp_bijective_of_isIso_unit
    (Y : C) [IsIso (adj.unit.app Y)] (n : ℕ) :
    Function.Bijective (fun x : Ext.{w₁} X Y n =>
      (Ext.mk₀ e.inv).comp (x.mapExactFunctor L) (Nat.zero_add n)) := by
  have hunit : Function.Bijective (fun x : Ext.{w₁} X Y n =>
      x.comp (Ext.mk₀ (adj.unit.app Y)) (Nat.add_zero n)) :=
    ((extFunctorObj X n).mapIso (asIso (adj.unit.app Y))).addCommGroupIsoToAddEquiv.bijective
  apply Function.Bijective.of_comp_left
    (f := adj.sourceExtComparison e (L.obj Y) n)
  · simpa only [Function.comp_def, sourceExtComparison_mapExactFunctor] using hunit
  · exact (adj.sourceExtComparison e (L.obj Y) n).injective

end CategoryTheory.Adjunction
