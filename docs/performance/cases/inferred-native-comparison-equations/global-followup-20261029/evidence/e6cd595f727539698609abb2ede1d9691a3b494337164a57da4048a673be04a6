/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Functor.ActualDiagramLift
public import Mathlib.CategoryTheory.Whiskering
public import Mathlib.CategoryTheory.HomCongr

/-! # Restriction through the specified CopyObj comparisons

The whole original restriction isomorphism is conjugated by the native
isoCopyObj maps. Its complete normalization retains those exact comparisons,
before any component carriers or chosen realizations are unfolded.
-/

@[expose] public noncomputable section

namespace CategoryTheory.Functor

universe uI vI uJ vJ uC vC uD vD

variable {I : Type uI} [Category.{vI} I] {J : Type uJ} [Category.{vJ} J]
  {C : Type uC} [Category.{vC} C] {D : Type uD} [Category.{vD} D]
  (P : I ⥤ C) (Q : J ⥤ D) (K : C ⥤ D) (R : I ⥤ J)
  (p : I → C) (ep : ∀ i, P.obj i ≅ p i)
  (q : J → D) (eqv : ∀ j, Q.obj j ≅ q j)

private theorem isoChainCancelRight
    {E : Type*} [Category* E] {A B C D : E}
    (a : A ≅ B) (b : B ≅ C) (c : D ≅ C) :
    (a ≪≫ b ≪≫ c.symm).hom ≫ c.hom = a.hom ≫ b.hom := by
  simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc,
    Iso.inv_hom_id, Category.comp_id]

/-- Transport the whole restriction through its specified original copyObj data. -/
def copyObjRestrictionIso
    (h : P.copyObj p ep ⋙ K ≅ R ⋙ Q.copyObj q eqv) : P ⋙ K ≅ R ⋙ Q :=
  isoWhiskerRight (P.isoCopyObj p ep) K ≪≫ h ≪≫
    isoWhiskerLeft R (Q.isoCopyObj q eqv).symm

/-- The entire transported restriction has its original coordinate equation. -/
theorem copyObjRestrictionIso_normalization
    (h : P.copyObj p ep ⋙ K ≅ R ⋙ Q.copyObj q eqv) :
    (copyObjRestrictionIso P Q K R p ep q eqv h).hom ≫
        (isoWhiskerLeft R (Q.isoCopyObj q eqv)).hom =
      (isoWhiskerRight (P.isoCopyObj p ep) K).hom ≫ h.hom := by
  exact isoChainCancelRight (isoWhiskerRight (P.isoCopyObj p ep) K) h
    (isoWhiskerLeft R (Q.isoCopyObj q eqv))



/-- The original coordinate-map constructor cancels its given target comparison. -/
theorem homCongr_symm_comp_hom
    {E : Type*} [Category* E] {A A' B B' : E}
    (e : A ≅ A') (t : B ≅ B') (f : A' ⟶ B') :
    (e.homCongr t).symm f ≫ t.hom = e.hom ≫ f := by
  change (e.hom ≫ f ≫ t.inv) ≫ t.hom = _
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- Both specified coordinate comparisons cancel around that same map. -/
theorem homCongr_symm_cancel
    {E : Type*} [Category* E] {A A' B B' : E}
    (e : A ≅ A') (t : B ≅ B') (f : A' ⟶ B') :
    e.inv ≫ (e.homCongr t).symm f ≫ t.hom = f := by
  rw [homCongr_symm_comp_hom]
  exact e.inv_hom_id_assoc f

/-- The whole source comparison has its original CopyObj component. -/
theorem isoCopyObj_whiskerRight_hom_app
    (P₀ : I ⥤ C) (p₀ : I → C) (e₀ : ∀ i, P₀.obj i ≅ p₀ i)
    (W : C ⥤ D) (i : I) :
    (isoWhiskerRight (P₀.isoCopyObj p₀ e₀) W).hom.app i = W.map (e₀ i).hom := rfl

/-- The whole target comparison has the same original CopyObj component. -/
theorem isoCopyObj_whiskerLeft_hom_app
    (Q₀ : J ⥤ D) (q₀ : J → D) (e₀ : ∀ j, Q₀.obj j ≅ q₀ j)
    (R₀ : I ⥤ J) (i : I) :
    (isoWhiskerLeft R₀ (Q₀.isoCopyObj q₀ e₀)).hom.app i = (e₀ (R₀.obj i)).hom := rfl

section FullyFaithful

variable {U V : I ⥤ C} {A B : I ⥤ D} (F : C ⥤ D) (hF : F.FullyFaithful)
  (s : U ⋙ F ≅ A) (h : A ≅ B) (t : V ⋙ F ≅ B)

/-- Lift the same complete coordinate comparison through a fully faithful functor. -/
def liftRestrictionIso : U ≅ V :=
  (hF.whiskeringRight I).preimageIso (s ≪≫ h ≪≫ t.symm)

/-- The original fully faithful lift retains the entire coordinate equation. -/
theorem liftRestrictionIso_normalization :
    whiskerRight (liftRestrictionIso F hF s h t).hom F ≫ t.hom = s.hom ≫ h.hom := by
  have hm := (hF.whiskeringRight I).map_preimage (s ≪≫ h ≪≫ t.symm).hom
  change whiskerRight (liftRestrictionIso F hF s h t).hom F =
    (s ≪≫ h ≪≫ t.symm).hom at hm
  rw [hm]
  exact isoChainCancelRight s h t


/-- Assemble the original lift, CopyObj component values, original coordinate
map and whole comparison before supplying any concrete coefficient data. -/
theorem liftRestrictionIso_app_eq_of_coordinates
    (i : I) {M N : C} {E : D}
    (source : F.obj (U.obj i) ≅ A.obj i)
    (target : F.obj (V.obj i) ≅ B.obj i) (e : F.obj N ≅ E)
    (middle : A.obj i ⟶ B.obj i) (relative : E ⟶ B.obj i)
    (u : U.obj i ⟶ M) (v : M ⟶ N) (k : N ⟶ V.obj i)
    (hs : s.hom.app i = source.hom) (hh : h.hom.app i = middle)
    (ht : t.hom.app i = target.hom)
    (hk : F.map k = (e.homCongr target).symm relative)
    (hc : source.hom ≫ middle = F.map u ≫ F.map v ≫ e.hom ≫ relative) :
    (liftRestrictionIso F hF s h t).hom.app i = u ≫ v ≫ k := by
  apply hF.map_injective
  apply (cancel_mono target.hom).mp
  have hLift := congrArg (fun a => a.app i)
    (liftRestrictionIso_normalization F hF s h t)
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, hs, hh, ht] at hLift
  calc
    F.map ((liftRestrictionIso F hF s h t).hom.app i) ≫ target.hom =
        source.hom ≫ middle := hLift
    _ = F.map u ≫ F.map v ≫ e.hom ≫ relative := hc
    _ = F.map (u ≫ v ≫ k) ≫ target.hom := by
      rw [F.map_comp, F.map_comp, hk]
      change _ = (F.map u ≫ F.map v ≫ (e.hom ≫ relative ≫ target.inv)) ≫ target.hom
      simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]

end FullyFaithful

end CategoryTheory.Functor
