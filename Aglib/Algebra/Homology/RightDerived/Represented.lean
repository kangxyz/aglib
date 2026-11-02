/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.DerivedCategory.ExtRightDerived
public import Aglib.Algebra.Homology.RightDerived.Postcomp

/-!
# Represented additive sections and their native right-derived functors

The represented functor is the actual preadditive coyoneda functor. Its
comparison with Ext specializes the existing injective-resolution constructor;
the Hom-group and Ext universes remain independent. Exact postcomposition
also supplies the comparison for an originally module-valued functor.

The current consumers are intrinsic site-global sections and the original
terminal module-section comparisons.
-/

@[expose] public noncomputable section

universe u v u₁ v₁ e r

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]

/-- Additive sections represented by the specified actual object. -/
abbrev additiveGamma [Preadditive C] (P : C) : C ⥤ AddCommGrpCat.{v} :=
  preadditiveCoyoneda.obj (op P)

namespace Abelian

variable [Abelian C] [EnoughInjectives C] [HasExt.{e} C]

/-- Original Ext computed by the native right-derived represented functor. -/
abbrev extRightDerivedRepresentedAddEquiv (P M : C) (n : ℕ) :
    Ext.{e} P M n ≃+ ((additiveGamma P).rightDerived n).obj M :=
  (injectiveResolution M).extRightDerivedAddEquiv P n

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The represented comparison retains the original coefficient morphism. -/
lemma extRightDerivedRepresentedAddEquiv_naturality
    (P : C) {M N : C} (f : M ⟶ N) (n : ℕ) (x : Ext.{e} P M n) :
    extRightDerivedRepresentedAddEquiv P N n (x.comp (Ext.mk₀ f) (add_zero n)) =
      ((additiveGamma P).rightDerived n).map f
        (extRightDerivedRepresentedAddEquiv P M n x) := by
  let φ : (injectiveResolution M).Hom (injectiveResolution N) f :=
    { hom := InjectiveResolution.desc f (injectiveResolution N) (injectiveResolution M)
      ι_f_zero_comp_hom_f_zero := by
        rw [CochainComplex.single₀_map_f_zero]
        exact InjectiveResolution.desc_commutes_zero f
          (injectiveResolution N) (injectiveResolution M) }
  exact (injectiveResolution M).extRightDerivedAddEquiv_naturality_right P n φ x

/-- In degree zero the comparison is the original derived-functor unit. -/
lemma extRightDerivedRepresentedAddEquiv_mk₀ {P M : C} (f : P ⟶ M) :
    extRightDerivedRepresentedAddEquiv P M 0 (Ext.mk₀ f) =
      (additiveGamma P).toRightDerivedZero.app M f :=
  (injectiveResolution M).extRightDerivedAddEquiv_mk₀ P f

variable {B : Type r} [Ring B]

/-- An actual module-valued comparison followed by the native represented Ext comparison. -/
abbrev representedDerivedModuleAddEquiv (P : C) (F : C ⥤ ModuleCat.{v} B) (n : ℕ)
    (β : F ⋙ forget₂ (ModuleCat.{v} B) AddCommGrpCat ≅
      (additiveGamma P).rightDerived n) (M : C) :
    F.obj M ≃+ Ext.{e} P M n :=
  (β.app M).addCommGroupIsoToAddEquiv.trans
    (extRightDerivedRepresentedAddEquiv P M n).symm

end Abelian

namespace Functor

variable [Abelian C] [EnoughInjectives C]
  {D : Type u₁} [Category.{v₁} D] [Abelian D]

/-- The native derived comparison for an actual represented exact postcomposition. -/
def representedRightDerivedPostcompIso (P : C) (F : C ⥤ D)
    (G : D ⥤ AddCommGrpCat.{v}) [F.Additive] [G.Additive] [G.PreservesHomology]
    (α : additiveGamma P ≅ F ⋙ G) (n : ℕ) :
    F.rightDerived n ⋙ G ≅ (additiveGamma P).rightDerived n :=
  (rightDerivedPostcompIso F G n).symm ≪≫ rightDerivedNatIsoOfAdditive α.symm n

end Functor

end CategoryTheory
