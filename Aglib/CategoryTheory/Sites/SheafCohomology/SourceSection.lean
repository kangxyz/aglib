/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Abelian.Ext.SourceTransfer

/-! # Original source comparisons and section retraction

The original composition comparison and original comparison to the identity
construct the whole coefficient isomorphism. Exact Ext pullback then retracts
from the actual source unit and composition equations. No section cohomology
law, auxiliary source system or reference realization is supplied as input.
-/

@[expose] public noncomputable section

open CategoryTheory.Limits CategoryTheory.Abelian

namespace CategoryTheory.Functor

universe uC vC uD vD eC eD uI uV vV

section Ordinary

variable {C : Type uC} [Category.{vC} C] {D : Type uD} [Category.{vD} D]
  {F : C ⥤ D} {H : D ⥤ C} {K : C ⥤ C}

/-- The whole original section coefficient comparison. -/
def sourceSectionIso (c : K ≅ F ⋙ H) (e : K ≅ 𝟭 C) : F ⋙ H ≅ 𝟭 C :=
  c.symm ≪≫ e

/-- The coefficient arrow is literally inverse composition followed by the original unit. -/
theorem sourceSectionIso_hom_app (c : K ≅ F ⋙ H) (e : K ≅ 𝟭 C) (L : C) :
    (sourceSectionIso c e).hom.app L = c.inv.app L ≫ e.hom.app L := rfl

/-- Coefficient naturality holds before applying Ext or evaluating elements. -/
@[reassoc]
theorem sourceSectionIso_naturality (c : K ≅ F ⋙ H) (e : K ≅ 𝟭 C)
    {L M : C} (q : L ⟶ M) :
    H.map (F.map q) ≫ (sourceSectionIso c e).hom.app M =
      (sourceSectionIso c e).hom.app L ≫ q :=
  (sourceSectionIso c e).hom.naturality q

end Ordinary

section EqualityTransport

variable {I : Type uI} {C : Type uC} [Category.{vC} C]
  {D : Type uD} [Category.{vD} D] {V : Type uV} [Category.{vV} V]
  (L : I → C ⥤ D) {T : V ⥤ C} {S : V ⥤ D} (c : ∀ i, T ⋙ L i ≅ S)

/-- Equality of the original indexing arrows transports the same inverse source map. -/
theorem sourceInverse_eq_transport {i j : I} (h : i = j) (A : V) :
    (c i).inv.app A ≫ eqToHom (congrArg (fun k => (L k).obj (T.obj A)) h) =
      (c j).inv.app A := by
  cases h
  simp only [eqToHom_refl, Category.comp_id]

end EqualityTransport

section Ext

variable {C : Type uC} [Category.{vC} C] [Abelian C] [HasExt.{eC} C]
  {D : Type uD} [Category.{vD} D] [Abelian D] [HasExt.{eD} D]
  (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  (H : D ⥤ C) [H.Additive] [PreservesFiniteLimits H] [PreservesFiniteColimits H]
  (K : C ⥤ C) [K.Additive] [PreservesFiniteLimits K] [PreservesFiniteColimits K]
  (c : K ≅ F ⋙ H) (e : K ≅ 𝟭 C)
  {U : C} {V : D} (sF : V ⟶ F.obj U) (sH : U ⟶ H.obj V) (sK : U ⟶ K.obj U)
  (hcomp : sK ≫ c.hom.app U = sH ≫ H.map sF)
  (hunit : sK ≫ e.hom.app U = 𝟙 U)

omit [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [K.Additive] [PreservesFiniteLimits K] [PreservesFiniteColimits K] in
/-- Pullback along the actual section, followed by its original coefficient comparison. -/
def extSectionPullback (L : C) (n : ℕ) :
    Ext.{eD} V (F.obj L) n →+ Ext.{eC} U L n :=
  H.extCoefficientTransfer sH ((sourceSectionIso c e).hom.app L) n

include hcomp hunit in
/-- The original source unit and composition equations give section retraction. -/
theorem extSectionPullback_inflation (L : C) (n : ℕ) (a : Ext.{eC} U L n) :
    extSectionPullback F H K c e sH L n (F.extPrecompMap sF L n a) = a := by
  have he : c.hom.app L ≫ H.map (𝟙 (F.obj L)) ≫
      (sourceSectionIso c e).hom.app L = e.hom.app L := by
    rw [Functor.map_id]
    change c.hom.app L ≫ (𝟙 ((F ⋙ H).obj L)) ≫ c.inv.app L ≫ e.hom.app L = e.hom.app L
    rw [Category.id_comp, Iso.hom_inv_id_app_assoc]
  have ht := extCoefficientTransfer_comp_of_eq F H K c sF sH sK hcomp
    (𝟙 (F.obj L)) ((sourceSectionIso c e).hom.app L) (e.hom.app L) he n
  have ht' := congrArg (fun k => k a) ht
  have hi := congrArg (fun k => k a) (extCoefficientTransfer_id K e sK hunit L n)
  calc
    extSectionPullback F H K c e sH L n (F.extPrecompMap sF L n a) =
        K.extCoefficientTransfer sK (e.hom.app L) n a := by
      simpa only [extSectionPullback, extCoefficientTransfer_apply,
        AddMonoidHom.comp_apply, Ext.comp_mk₀_id] using ht'
    _ = a := hi

omit [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [K.Additive] [PreservesFiniteLimits K] [PreservesFiniteColimits K] in
/-- Full coefficient naturality of the same actual section Ext map. -/
theorem extSectionPullback_coefficient {L M : C} (q : L ⟶ M) (n : ℕ)
    (a : Ext.{eD} V (F.obj L) n) :
    extSectionPullback F H K c e sH M n
        (a.comp (Ext.mk₀ (F.map q)) (add_zero n)) =
      (extSectionPullback F H K c e sH L n a).comp (Ext.mk₀ q) (add_zero n) := by
  have h := extCoefficientTransfer_naturality H sH
    ((sourceSectionIso c e).hom.app L) ((sourceSectionIso c e).hom.app M)
    (F.map q) q (sourceSectionIso_naturality c e q) n
  exact (congrArg (fun k => k a) h).symm

end Ext

end CategoryTheory.Functor
