/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Sites.ConstantRestriction
public import Aglib.CategoryTheory.Abelian.Ext.SourceTransfer
public import Mathlib.CategoryTheory.Adjunction.CompositionIso

/-! # Original constant restriction through actual adjunctions

The same whole constant transport supplies the inverse generator arrow and
the coefficient arrow. Ordinary adjunction mates give its identity and
composition normalization before any site or geometric realization is chosen.
-/

@[expose] public noncomputable section

open CategoryTheory.Limits CategoryTheory.Abelian

namespace CategoryTheory.Functor

universe uV vV u₀ v₀ u₁ v₁ u₂ v₂ e₀ e₁ e₂

section Restriction

variable {V : Type uV} [Category.{vV} V]
  {C₀ : Type u₀} [Category.{v₀} C₀] [Abelian C₀] [HasExt.{e₀} C₀]
  {C₁ : Type u₁} [Category.{v₁} C₁] [Abelian C₁] [HasExt.{e₁} C₁]

/-- The complete original constant restriction uses one whole transport at
both the generator and the coefficient value. -/
def constantExtRestriction (L : C₀ ⥤ C₁) [L.Additive]
    [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    {K₀ : V ⥤ C₀} {K₁ : V ⥤ C₁} (c : K₀ ⋙ L ≅ K₁)
    (P M : V) (n : ℕ) :
    Ext.{e₀} (K₀.obj P) (K₀.obj M) n →+ Ext.{e₁} (K₁.obj P) (K₁.obj M) n :=
  L.extCoefficientTransfer (c.inv.app P) (c.hom.app M) n

end Restriction

section Composition

variable {V : Type uV} [Category.{vV} V]
  {C₀ : Type u₀} [Category.{v₀} C₀]
  {C₁ : Type u₁} [Category.{v₁} C₁]
  {C₂ : Type u₂} [Category.{v₂} C₂]
  {K₀ : V ⥤ C₀} {K₁ : V ⥤ C₁} {K₂ : V ⥤ C₂}
  {Γ₀ : C₀ ⥤ V} {Γ₁ : C₁ ⥤ V} {Γ₂ : C₂ ⥤ V}
  {L₁ : C₀ ⥤ C₁} {L₂ : C₁ ⥤ C₂} {L₀ : C₀ ⥤ C₂}
  {R₁ : C₁ ⥤ C₀} {R₂ : C₂ ⥤ C₁} {R₀ : C₂ ⥤ C₀}
  (constantAdj₀ : K₀ ⊣ Γ₀) (imageAdj₁ : L₁ ⊣ R₁) (imageAdj₂ : L₂ ⊣ R₂)
  (constantAdj₁ : K₁ ⊣ Γ₁) (imageAdj₀ : L₀ ⊣ R₀) (constantAdj₂ : K₂ ⊣ Γ₂)
  (sections₁ : R₁ ⋙ Γ₀ ≅ Γ₁) (imageComp : R₂ ⋙ R₁ ≅ R₀)
  (sections₀ : R₀ ⋙ Γ₀ ≅ Γ₂) (sections₂ : R₂ ⋙ Γ₁ ≅ Γ₂)
  (hsections : isoWhiskerLeft R₂ sections₁ ≪≫ sections₂ =
    (associator R₂ R₁ Γ₀).symm ≪≫ isoWhiskerRight imageComp Γ₀ ≪≫ sections₀)

include hsections in
/-- The whole constant triangle is the original adjunction-mate associativity
law, evaluated only after its canonical transports have been constructed. -/
theorem constantTransport_triangle (M : V) :
    (Adjunction.leftAdjointCompIso imageAdj₁ imageAdj₂ imageAdj₀ imageComp).hom.app
        (K₀.obj M) ≫
      (Adjunction.leftAdjointCompIso constantAdj₀ imageAdj₀ constantAdj₂ sections₀).hom.app M =
    L₂.map
        ((Adjunction.leftAdjointCompIso constantAdj₀ imageAdj₁ constantAdj₁ sections₁).hom.app M) ≫
      (Adjunction.leftAdjointCompIso constantAdj₁ imageAdj₂ constantAdj₂ sections₂).hom.app M := by
  let c₁ := Adjunction.leftAdjointCompIso constantAdj₀ imageAdj₁ constantAdj₁ sections₁
  let c₂ := Adjunction.leftAdjointCompIso constantAdj₁ imageAdj₂ constantAdj₂ sections₂
  let c₀ := Adjunction.leftAdjointCompIso constantAdj₀ imageAdj₀ constantAdj₂ sections₀
  let c := Adjunction.leftAdjointCompIso imageAdj₁ imageAdj₂ imageAdj₀ imageComp
  have h := congrArg (fun c => c.hom.app M)
    (Adjunction.leftAdjointCompIso_assoc constantAdj₀ imageAdj₁ imageAdj₂
      constantAdj₁ imageAdj₀ constantAdj₂ sections₁ imageComp sections₀ sections₂ hsections)
  simp only [Iso.trans_hom, NatTrans.comp_app] at h
  change c.hom.app (K₀.obj M) ≫ c₀.hom.app M =
    (𝟙 _) ≫ L₂.map (c₁.hom.app M) ≫ c₂.hom.app M at h
  exact h.trans (Category.id_comp _)

section CohomologyComposition

variable [Abelian C₀] [HasExt.{e₀} C₀]
  [Abelian C₁] [HasExt.{e₁} C₁] [Abelian C₂] [HasExt.{e₂} C₂]
  [L₁.Additive] [PreservesFiniteLimits L₁] [PreservesFiniteColimits L₁]
  [L₂.Additive] [PreservesFiniteLimits L₂] [PreservesFiniteColimits L₂]
  [L₀.Additive] [PreservesFiniteLimits L₀] [PreservesFiniteColimits L₀]

include hsections in
/-- Complete constant restrictions compose through the original constant and
image adjunctions, with three independent Ext worlds. -/
theorem constantExtRestriction_comp (P M : V) (n : ℕ) :
    (L₂.constantExtRestriction
      (Adjunction.leftAdjointCompIso constantAdj₁ imageAdj₂ constantAdj₂ sections₂) P M n).comp
        (L₁.constantExtRestriction
          (Adjunction.leftAdjointCompIso constantAdj₀ imageAdj₁ constantAdj₁ sections₁) P M n) =
      L₀.constantExtRestriction
        (Adjunction.leftAdjointCompIso constantAdj₀ imageAdj₀ constantAdj₂ sections₀) P M n := by
  let c₁ := Adjunction.leftAdjointCompIso constantAdj₀ imageAdj₁ constantAdj₁ sections₁
  let c₂ := Adjunction.leftAdjointCompIso constantAdj₁ imageAdj₂ constantAdj₂ sections₂
  let c₀ := Adjunction.leftAdjointCompIso constantAdj₀ imageAdj₀ constantAdj₂ sections₀
  let c := (Adjunction.leftAdjointCompIso imageAdj₁ imageAdj₂ imageAdj₀ imageComp).symm
  have ht (N : V) : c.inv.app (K₀.obj N) ≫ c₀.hom.app N =
      L₂.map (c₁.hom.app N) ≫ c₂.hom.app N :=
    constantTransport_triangle constantAdj₀ imageAdj₁ imageAdj₂ constantAdj₁ imageAdj₀
      constantAdj₂ sections₁ imageComp sections₀ sections₂ hsections N
  have hc (N : V) : c.hom.app (K₀.obj N) ≫ L₂.map (c₁.hom.app N) ≫ c₂.hom.app N =
      c₀.hom.app N := by
    apply (cancel_epi (c.inv.app (K₀.obj N))).mp
    simp only [← Category.assoc, Iso.inv_hom_id_app, Category.id_comp]
    exact (ht N).symm
  have hs : c₀.inv.app P ≫ c.hom.app (K₀.obj P) =
      c₂.inv.app P ≫ L₂.map (c₁.inv.app P) := by
    apply (cancel_mono (L₂.map (c₁.hom.app P) ≫ c₂.hom.app P)).mp
    simp only [Category.assoc]
    rw [hc P]
    simp [← Functor.map_comp_assoc]
  exact extCoefficientTransfer_comp_of_eq L₁ L₂ L₀ c
    (c₁.inv.app P) (c₂.inv.app P) (c₀.inv.app P) hs
    (c₁.hom.app M) (c₂.hom.app M) (c₀.hom.app M) (hc M) n

end CohomologyComposition

section TriangleCohomology

variable [Abelian C₁] [HasExt.{e₁} C₁] [Abelian C₂] [HasExt.{e₂} C₂]
  [L₂.Additive] [PreservesFiniteLimits L₂] [PreservesFiniteColimits L₂]

include hsections in
/-- The complete triangle transfer becomes the original constant restriction
after its actual coefficient transports, with independent source and target worlds. -/
theorem constantExtRestriction_triangleTransfer (P M : V) (n : ℕ) :
    ((Ext.mk₀
      ((Adjunction.leftAdjointCompIso constantAdj₀ imageAdj₀
        constantAdj₂ sections₀).hom.app M)).postcomp
        (K₂.obj P) (add_zero n)).comp
      (L₂.extCoefficientTransfer
        ((Adjunction.leftAdjointCompIso constantAdj₁ imageAdj₂ constantAdj₂ sections₂).inv.app P)
        ((Adjunction.leftAdjointCompIso imageAdj₁ imageAdj₂ imageAdj₀ imageComp).hom.app
          (K₀.obj M)) n) =
    (L₂.constantExtRestriction
      (Adjunction.leftAdjointCompIso constantAdj₁ imageAdj₂ constantAdj₂ sections₂) P M n).comp
        ((Ext.mk₀
          ((Adjunction.leftAdjointCompIso constantAdj₀ imageAdj₁
            constantAdj₁ sections₁).hom.app M)).postcomp
            (K₁.obj P) (add_zero n)) := by
  exact extCoefficientTransfer_naturality L₂
    ((Adjunction.leftAdjointCompIso constantAdj₁ imageAdj₂ constantAdj₂ sections₂).inv.app P)
    ((Adjunction.leftAdjointCompIso imageAdj₁ imageAdj₂ imageAdj₀ imageComp).hom.app (K₀.obj M))
    ((Adjunction.leftAdjointCompIso constantAdj₁ imageAdj₂ constantAdj₂ sections₂).hom.app M)
    ((Adjunction.leftAdjointCompIso constantAdj₀ imageAdj₁ constantAdj₁ sections₁).hom.app M)
    ((Adjunction.leftAdjointCompIso constantAdj₀ imageAdj₀ constantAdj₂ sections₀).hom.app M)
    (constantTransport_triangle constantAdj₀ imageAdj₁ imageAdj₂ constantAdj₁ imageAdj₀
      constantAdj₂ sections₁ imageComp sections₀ sections₂ hsections M).symm n

end TriangleCohomology

end Composition

section Identity

variable {V : Type uV} [Category.{vV} V]
  {C : Type u₀} [Category.{v₀} C] [Abelian C] [HasExt.{e₀} C]
  {K : V ⥤ C} {Γ : C ⥤ V} {L R : C ⥤ C}
  [L.Additive] [PreservesFiniteLimits L] [PreservesFiniteColimits L]
  (constantAdj : K ⊣ Γ) (imageAdj : L ⊣ R)
  (sections : R ⋙ Γ ≅ Γ) (imageId : R ≅ 𝟭 C)
  (hsections : sections = isoWhiskerRight imageId Γ ≪≫ leftUnitor Γ)

include hsections in
/-- The canonical identity constant transport yields the identity of the
original constant Ext group, through its actual source and coefficient units. -/
theorem constantExtRestriction_id (P M : V) (n : ℕ) :
    L.constantExtRestriction
      (Adjunction.leftAdjointCompIso constantAdj imageAdj constantAdj sections) P M n =
        AddMonoidHom.id (Ext.{e₀} (K.obj P) (K.obj M) n) := by
  let c := Adjunction.leftAdjointIdIso imageAdj imageId
  have hc : Adjunction.leftAdjointCompIso constantAdj imageAdj constantAdj sections =
      isoWhiskerLeft K c ≪≫ rightUnitor K :=
    Adjunction.leftAdjointCompIso_comp_id constantAdj imageAdj sections imageId hsections
  have hs :
      (Adjunction.leftAdjointCompIso constantAdj imageAdj constantAdj sections).inv.app P =
        c.inv.app (K.obj P) := by
    rw [hc]
    change (𝟙 _) ≫ c.inv.app (K.obj P) = _
    exact Category.id_comp _
  have ht :
      (Adjunction.leftAdjointCompIso constantAdj imageAdj constantAdj sections).hom.app M =
        c.hom.app (K.obj M) := by
    rw [hc]
    change c.hom.app (K.obj M) ≫ 𝟙 _ = _
    exact Category.comp_id _
  unfold constantExtRestriction
  rw [hs, ht]
  exact extCoefficientTransfer_id L c (c.inv.app (K.obj P))
    (c.inv_hom_id_app (K.obj P)) (K.obj M) n

end Identity

end CategoryTheory.Functor
