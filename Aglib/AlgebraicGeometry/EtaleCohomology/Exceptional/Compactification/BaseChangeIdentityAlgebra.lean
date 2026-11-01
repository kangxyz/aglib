/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Adjunction.CompositeUnitMateNormalization
public import Aglib.CategoryTheory.NatTrans.CompositeExchange
public import Aglib.CategoryTheory.Functor.ImageComparison

/-! # Original identity-base exchange contracts to the original unit comparison -/

@[expose] public section
namespace CategoryTheory

variable {S A B V : Type*} [Category* S] [Category* A] [Category* B] [Category* V]
  {R : A ⥤ S} {H : A ⥤ B} {Q : B ⥤ A} {U : B ⥤ S} {I : S ⥤ S}
  {J : V ⥤ A} {J' : V ⥤ B} {F : V ⥤ V}

/-- Whole identity-base contraction retaining the original pasted map, source
identity and refinement transformation. -/
def CompactifiedIdentityBaseEquation
    (θ : (J ⋙ R) ⋙ I ⟶ F ⋙ (J' ⋙ U)) (i : I ≅ 𝟭 S) (s : F ≅ 𝟭 V)
    (δ : J ⟶ J' ⋙ Q) (d : U ≅ Q ⋙ R) : Prop :=
  ∀ K, θ.app K ≫ (J' ⋙ U).map (s.hom.app K) =
    i.hom.app (R.obj (J.obj K)) ≫ (imageComparison δ d.symm).app K

/-- The original proper identity-base unit equation and normalized open
comparison identify the full pasted exchange with the original refinement map. -/
theorem compactifiedIdentityBaseEquation
    (h : H ⊣ Q) (d : U ≅ Q ⋙ R) (i : I ≅ 𝟭 S) (s : F ≅ 𝟭 V)
    (β : R ⋙ I ⟶ H ⋙ U) (e : J ⋙ H ≅ F ⋙ J') (p : J ⋙ H ≅ J')
    (δ : J ⟶ J' ⋙ Q)
    (hβ : CompositeIdentityBaseMateEquation h d i β)
    (hp : p = e ≪≫ Functor.isoWhiskerRight s J' ≪≫ Functor.leftUnitor J')
    (hδ : ∀ K, δ.app K = h.unit.app (J.obj K) ≫ Q.map (p.hom.app K))
    (θ : (J ⋙ R) ⋙ I ⟶ F ⋙ (J' ⋙ U)) (hθ : θ = compositeExchange β e) :
    CompactifiedIdentityBaseEquation θ i s δ d := by
  subst θ
  intro K
  have hpK : p.hom.app K = e.hom.app K ≫ J'.map (s.hom.app K) := by
    rw [hp]
    simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
      Functor.whiskerRight_app, Functor.leftUnitor_hom_app]
    exact congrArg (fun z => e.hom.app K ≫ z)
      (Category.comp_id (J'.map (s.hom.app K)))
  have hb : β.app (J.obj K) =
      (i.hom.app (R.obj (J.obj K)) ≫ R.map (h.unit.app (J.obj K))) ≫
        d.inv.app (H.obj (J.obj K)) := by
    have he := congrArg (fun z => z ≫ d.inv.app (H.obj (J.obj K))) (hβ (J.obj K))
    simp only [Category.assoc, Iso.hom_inv_id_app] at he
    exact ((Category.comp_id (β.app (J.obj K))).symm.trans he).trans
      (Category.assoc _ _ _).symm
  have hn : d.inv.app (H.obj (J.obj K)) ≫ U.map (p.hom.app K) =
      R.map (Q.map (p.hom.app K)) ≫ d.inv.app (J'.obj K) :=
    (d.inv.naturality (p.hom.app K)).symm
  change (compositeExchange β e).app K ≫ U.map (J'.map (s.hom.app K)) = _
  rw [compositeExchange_app, Category.assoc, ← U.map_comp, ← hpK, hb]
  simp only [Category.assoc]
  rw [hn]
  simp only [imageComparison_app, Iso.symm_hom, hδ, Functor.map_comp, Category.assoc]

end CategoryTheory
