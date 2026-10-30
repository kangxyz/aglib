/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Abelian.Ext.CoefficientSquare
public import Aglib.Algebra.Homology.DerivedCategory.Ext.Equivalence
public import Aglib.CategoryTheory.Adjunction.Mates.Whole
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.MapAdjunction

/-! # Actual adjoint/source Ext comparisons and original factor transport

The original exact adjunction and original source Iso construct the comparison.
The actual mate counit and one original factorization/source square give the
whole four-category comparison square and its reverse bijectivity consequence.
No desired cohomology square or arbitrary endpoint equivalence is supplied.
-/

@[expose] public noncomputable section

open CategoryTheory.Limits CategoryTheory.Abelian

namespace CategoryTheory.Abelian.Ext

universe v w

/-- Original isomorphism transport on additive Ext, without a choice of scalar module. -/
def precompIsoAddEquiv {C : Type*} [Category.{v} C] [Abelian C] [HasExt.{w} C]
    {A B : C} (e : A ≅ B) (F : C) (q : ℕ) : Ext.{w} B F q ≃+ Ext.{w} A F q :=
  (((extFunctor q).mapIso e.op).app F).addCommGroupIsoToAddEquiv

/-- Forward transport is the original precomposition by the actual Iso hom. -/
@[simp]
theorem precompIsoAddEquiv_apply {C : Type*} [Category.{v} C] [Abelian C]
    [HasExt.{w} C] {A B : C} (e : A ≅ B) (F : C) (q : ℕ) (x : Ext.{w} B F q) :
    precompIsoAddEquiv e F q x = (mk₀ e.hom).comp x (zero_add q) := rfl

/-- Inverse transport is the original precomposition by the actual Iso inverse. -/
@[simp]
theorem precompIsoAddEquiv_symm_apply {C : Type*} [Category.{v} C] [Abelian C]
    [HasExt.{w} C] {A B : C} (e : A ≅ B) (F : C) (q : ℕ) (x : Ext.{w} A F q) :
    (precompIsoAddEquiv e F q).symm x = (mk₀ e.inv).comp x (zero_add q) := rfl

end CategoryTheory.Abelian.Ext

namespace CategoryTheory.Adjunction

universe uC vC uD vD eC eD

variable {C : Type uC} [Category.{vC} C] [Abelian C] [HasExt.{eC} C]
  {D : Type uD} [Category.{vD} D] [Abelian D] [HasExt.{eD} D]
  {L : C ⥤ D} {R : D ⥤ C} [L.Additive] [R.Additive]
  [PreservesFiniteLimits L] [PreservesFiniteColimits L]
  [PreservesFiniteLimits R] [PreservesFiniteColimits R]
  (adj : L ⊣ R) {U : C} {V : D} (e : L.obj U ≅ V)

/-- The actual exact adjunction followed by the original inverse source transport. -/
def originalExtSourceComparison (M : D) (n : ℕ) : Ext.{eC} U (R.obj M) n ≃+ Ext.{eD} V M n :=
  adj.extEquiv.symm.trans (Ext.precompIsoAddEquiv e.symm M n)

/-- The comparison is the original exact/source map followed by the actual counit. -/
theorem originalExtSourceComparison_apply (M : D) (n : ℕ) (x : Ext.{eC} U (R.obj M) n) :
    originalExtSourceComparison adj e M n x =
      (L.extPrecompMap e.inv (R.obj M) n x).comp (Ext.mk₀ (adj.counit.app M)) (add_zero n) := by
  simp only [originalExtSourceComparison, AddEquiv.trans_apply, Ext.precompIsoAddEquiv_apply,
    Adjunction.extEquiv_symm_apply, Functor.extPrecompMap_apply]
  exact (Ext.comp_assoc (a₁ := 0) (a₂ := n) (a₃ := 0) (a := n) _ _ _
    (zero_add n) (add_zero n) (by omega)).symm

/-- The original coefficient unit maps to the original exact/source pullback. -/
theorem originalExtSourceComparison_unit (M : C) (n : ℕ) (x : Ext.{eC} U M n) :
    originalExtSourceComparison adj e (L.obj M) n
        (x.comp (Ext.mk₀ (adj.unit.app M)) (add_zero n)) = L.extPrecompMap e.inv M n x := by
  rw [originalExtSourceComparison_apply, Functor.extPrecompMap_comp, Ext.mapExactFunctor_mk₀]
  rw [Ext.comp_assoc_of_third_deg_zero, Ext.mk₀_comp_mk₀, adj.left_triangle_components]
  exact Ext.comp_mk₀_id _

/-- Full coefficient naturality retains both original exact-adjoint maps. -/
theorem originalExtSourceComparison_naturality {M N : D} (q : M ⟶ N) (n : ℕ)
    (x : Ext.{eC} U (R.obj M) n) :
    originalExtSourceComparison adj e N n (x.comp (Ext.mk₀ (R.map q)) (add_zero n)) =
      (originalExtSourceComparison adj e M n x).comp (Ext.mk₀ q) (add_zero n) := by
  rw [originalExtSourceComparison_apply, originalExtSourceComparison_apply,
    Functor.extPrecompMap_comp, Ext.mapExactFunctor_mk₀]
  simp only [Ext.comp_assoc_of_third_deg_zero, Ext.mk₀_comp_mk₀]
  have hq := adj.counit.naturality q
  change L.map (R.map q) ≫ adj.counit.app N = adj.counit.app M ≫ q at hq
  rw [hq]

end CategoryTheory.Adjunction

namespace CategoryTheory.Functor

universe u₀ v₀ e₀ u₁ v₁ e₁ u₂ v₂ e₂

variable {C₀ : Type u₀} [Category.{v₀} C₀] [Abelian C₀] [HasExt.{e₀} C₀]
  {C₁ : Type u₁} [Category.{v₁} C₁] [Abelian C₁] [HasExt.{e₁} C₁]
  {C₂ : Type u₂} [Category.{v₂} C₂] [Abelian C₂] [HasExt.{e₂} C₂]

/-- Actual composition with an equivalence factor reflects bijectivity
of the original source map. -/
theorem extPrecompMap_bijective_of_equivalence_factor
    (F : C₀ ⥤ C₁) (G : C₁ ⥤ C₂) (H : C₀ ⥤ C₂)
    [F.Additive] [G.Additive] [H.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    [G.IsEquivalence] [EnoughInjectives C₁]
    (c : H ≅ F ⋙ G) {U₀ : C₀} {U₁ : C₁} {U₂ : C₂}
    (s₁ : U₁ ⟶ F.obj U₀) (s₂ : U₂ ⟶ G.obj U₁) [IsIso s₂] (s₀ : U₂ ⟶ H.obj U₀)
    (hs : s₀ ≫ c.hom.app U₀ = s₂ ≫ G.map s₁) (M : C₀) (n : ℕ)
    (hF : Function.Bijective (F.extPrecompMap s₁ M n)) :
    Function.Bijective (H.extPrecompMap s₀ M n) := by
  have hG := G.extPrecompMap_bijective_of_isEquivalence s₂ (F.obj M) n
  let p : Ext.{e₂} U₂ (H.obj M) n ≃+ Ext.{e₂} U₂ ((F ⋙ G).obj M) n :=
    ((extFunctorObj U₂ n).mapIso (c.app M)).addCommGroupIsoToAddEquiv
  apply Function.Bijective.of_comp_left (f := p)
  · have he : (fun x => p (H.extPrecompMap s₀ M n x)) =
        fun x => G.extPrecompMap s₂ (F.obj M) n (F.extPrecompMap s₁ M n x) := by
      funext x
      exact extPrecompMap_comparison F G H c s₁ s₂ s₀ hs M n x
    rw [Function.comp_def, he]
    exact hG.comp hF
  · exact p.injective

end CategoryTheory.Functor

namespace CategoryTheory.Adjunction

universe u₀ v₀ e₀ u₁ v₁ e₁ u₂ v₂ e₂ u₃ v₃ e₃

variable {C₀ : Type u₀} [Category.{v₀} C₀] [Abelian C₀] [HasExt.{e₀} C₀]
  {C₁ : Type u₁} [Category.{v₁} C₁] [Abelian C₁] [HasExt.{e₁} C₁]
  {C₂ : Type u₂} [Category.{v₂} C₂] [Abelian C₂] [HasExt.{e₂} C₂]
  {C₃ : Type u₃} [Category.{v₃} C₃] [Abelian C₃] [HasExt.{e₃} C₃]
  {L : C₀ ⥤ C₁} {R : C₁ ⥤ C₀} {L' : C₂ ⥤ C₃} {R' : C₃ ⥤ C₂}
  [L.Additive] [R.Additive] [L'.Additive] [R'.Additive]
  [PreservesFiniteLimits L] [PreservesFiniteColimits L]
  [PreservesFiniteLimits R] [PreservesFiniteColimits R]
  [PreservesFiniteLimits L'] [PreservesFiniteColimits L']
  [PreservesFiniteLimits R'] [PreservesFiniteColimits R']
  (adj : L ⊣ R) (adj' : L' ⊣ R')
  (G : C₀ ⥤ C₂) (H : C₁ ⥤ C₃) (L₀ : C₀ ⥤ C₃)
  [G.Additive] [H.Additive] [L₀.Additive]
  [PreservesFiniteLimits G] [PreservesFiniteColimits G]
  [PreservesFiniteLimits H] [PreservesFiniteColimits H]
  [PreservesFiniteLimits L₀] [PreservesFiniteColimits L₀]
  (c : L₀ ≅ G ⋙ L') (d : L₀ ≅ L ⋙ H)
  {U₀ : C₀} {U₁ : C₁} {U₂ : C₂} {U₃ : C₃}
  (e : L.obj U₀ ≅ U₁) (e' : L'.obj U₂ ≅ U₃)
  (sG : U₂ ⟶ G.obj U₀) (sH : U₃ ⟶ H.obj U₁) (s₀ : U₃ ⟶ L₀.obj U₀)
  (hs : s₀ ≫ c.hom.app U₀ = e'.inv ≫ L'.map sG)
  (ht : s₀ ≫ d.hom.app U₀ = sH ≫ H.map e.inv)

include hs ht in
/-- The actual mate counit and original four-category source square give
the complete Ext comparison square. -/
theorem originalExtSourceComparison_mate_square (M : C₁) (n : ℕ)
    (x : Ext.{e₀} U₀ (R.obj M) n) :
    let β := (mateEquiv adj adj' (TwoSquare.mk G L L' H (c.symm ≪≫ d).hom)).natTrans
    originalExtSourceComparison adj' e' (H.obj M) n
        ((G.extPrecompMap sG (R.obj M) n x).comp (Ext.mk₀ (β.app M)) (add_zero n)) =
      H.extPrecompMap sH M n (originalExtSourceComparison adj e M n x) := by
  dsimp only
  let β := (mateEquiv adj adj' (TwoSquare.mk G L L' H (c.symm ≪≫ d).hom)).natTrans
  have hm := mateEquiv_counit adj adj' (TwoSquare.mk G L L' H (c.symm ≪≫ d).hom) M
  have hc : c.hom.app (R.obj M) ≫ L'.map (β.app M) ≫ adj'.counit.app (H.obj M) =
      d.hom.app (R.obj M) ≫ H.map (adj.counit.app M) ≫ 𝟙 _ := by
    rw [Category.comp_id, hm]
    simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Category.assoc,
      Iso.hom_inv_id_app_assoc]
  have h := Functor.extCoefficientTransfer_square G L' L H L₀ c d sG e'.inv e.inv sH s₀
    hs ht (β.app M) (adj'.counit.app (H.obj M)) (adj.counit.app M) (𝟙 _) hc n x
  simp only [originalExtSourceComparison_apply, Ext.comp_mk₀_id] at h ⊢
  exact h

include hs ht in
/-- Actual mate invertibility transfers base-source bijectivity back through
the actual adjoint comparisons. -/
theorem originalExtSourceComparison_bijective_of_mate (M : C₁) (n : ℕ)
    [IsIso ((mateEquiv adj adj' (TwoSquare.mk G L L' H (c.symm ≪≫ d).hom)).natTrans.app M)]
    (hG : Function.Bijective (G.extPrecompMap sG (R.obj M) n)) :
    Function.Bijective (H.extPrecompMap sH M n) := by
  let β := (mateEquiv adj adj' (TwoSquare.mk G L L' H (c.symm ≪≫ d).hom)).natTrans.app M
  let E := originalExtSourceComparison adj e M n
  let E' := originalExtSourceComparison adj' e' (H.obj M) n
  have hb : Function.Bijective (fun a : Ext.{e₁} U₁ M n =>
      E' ((G.extPrecompMap sG (R.obj M) n (E.symm a)).comp (Ext.mk₀ β) (add_zero n))) :=
    E'.bijective.comp
      ((((extFunctorObj U₂ n).mapIso (asIso β)).addCommGroupIsoToAddEquiv.bijective).comp
        (hG.comp E.symm.bijective))
  have he : (fun a : Ext.{e₁} U₁ M n =>
      E' ((G.extPrecompMap sG (R.obj M) n (E.symm a)).comp (Ext.mk₀ β) (add_zero n))) =
      H.extPrecompMap sH M n := by
    funext a
    have h := originalExtSourceComparison_mate_square adj adj' G H L₀ c d
      e e' sG sH s₀ hs ht M n (E.symm a)
    exact h.trans (congrArg (H.extPrecompMap sH M n) (E.apply_symm_apply a))
  rw [he] at hb
  exact hb

end CategoryTheory.Adjunction
