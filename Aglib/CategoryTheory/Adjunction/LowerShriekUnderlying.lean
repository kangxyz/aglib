/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Adjunction.UnderlyingHomEquiv
public import Aglib.CategoryTheory.Adjunction.LeftAdjointComparison
public import Aglib.CategoryTheory.Adjunction.Mates.ScalarForgettingCoherence

/-!
# Whole underlying counit and composition equations for left adjoints

The supplied comparisons are the original maps. Their mate equation determines the entire
counit square before evaluation. Equivalence transport is normalized by its original unit
and counit. No new underlying comparison or adjunction is selected here.
-/

@[expose] public section

namespace CategoryTheory

open CategoryTheory.Functor CategoryTheory.TwoSquare

universe uA vA uB vB uC vC uD vD

section Underlying

variable {A : Type uA} [Category.{vA} A] {B : Type uB} [Category.{vB} B]
  {C : Type uC} [Category.{vC} C] {D : Type uD} [Category.{vD} D]
  {L₁ : A ⥤ B} {R₁ : B ⥤ A} {L₂ : C ⥤ D} {R₂ : D ⥤ C}
  {U : A ⥤ C} {V : B ⥤ D}

/-- The whole counit square is forced by the original mate equation. -/
theorem Adjunction.underlying_counit
    (a : L₁ ⊣ R₁) (b : L₂ ⊣ R₂)
    (e : L₁ ⋙ V ≅ U ⋙ L₂) (d : R₁ ⋙ U ≅ V ⋙ R₂)
    (h : (mateEquiv a b (TwoSquare.mk _ _ _ _ e.inv)).natTrans = d.hom) :
    whiskerRight a.counit V ≫ (leftUnitor V).hom =
      (associator R₁ L₁ V).hom ≫ whiskerLeft R₁ e.hom ≫
        (associator R₁ U L₂).inv ≫ whiskerRight d.hom L₂ ≫
        (associator V R₂ L₂).hom ≫ whiskerLeft V b.counit ≫ (rightUnitor V).hom := by
  ext N
  have hc := mateEquiv_counit a b (TwoSquare.mk _ _ _ _ e.inv) N
  change L₂.map ((mateEquiv a b (TwoSquare.mk _ _ _ _ e.inv)).natTrans.app N) ≫
      b.counit.app (V.obj N) = e.inv.app (R₁.obj N) ≫ V.map (a.counit.app N) at hc
  rw [h] at hc
  have ht := congrArg (fun k => e.hom.app (R₁.obj N) ≫ k) hc
  simp only [Iso.hom_inv_id_app_assoc] at ht
  change V.map (a.counit.app N) ≫ 𝟙 (V.obj N) =
    𝟙 _ ≫ e.hom.app (R₁.obj N) ≫ 𝟙 _ ≫ L₂.map (d.hom.app N) ≫
      𝟙 _ ≫ b.counit.app (V.obj N) ≫ 𝟙 _
  simpa only [Functor.comp_obj, Functor.id_obj, Category.id_comp, Category.assoc] using
    congrArg (fun k => k ≫ 𝟙 (V.obj N)) ht.symm

/-- Evaluation of the whole underlying counit equation. -/
theorem Adjunction.underlying_counit_app
    (a : L₁ ⊣ R₁) (b : L₂ ⊣ R₂)
    (e : L₁ ⋙ V ≅ U ⋙ L₂) (d : R₁ ⋙ U ≅ V ⋙ R₂)
    (h : (mateEquiv a b (TwoSquare.mk _ _ _ _ e.inv)).natTrans = d.hom) (N : B) :
    V.map (a.counit.app N) = e.hom.app (R₁.obj N) ≫
      L₂.map (d.hom.app N) ≫ b.counit.app (V.obj N) := by
  have hc := congr_app (Adjunction.underlying_counit a b e d h) N
  change V.map (a.counit.app N) ≫ 𝟙 (V.obj N) =
    𝟙 _ ≫ e.hom.app (R₁.obj N) ≫ 𝟙 _ ≫ L₂.map (d.hom.app N) ≫
      𝟙 _ ≫ b.counit.app (V.obj N) ≫ 𝟙 _ at hc
  simpa only [Functor.comp_obj, Functor.id_obj, Category.id_comp, Category.comp_id] using hc

/-- The original equivalence-transport formula is exactly the inverse mate of its right square. -/
theorem mateEquiv_equivalence_comparison
    (a : A ≌ B) (b : C ≌ D) (r : V ⋙ b.inverse ≅ a.inverse ⋙ U)
    (e : a.functor ⋙ V ≅ U ⋙ b.functor)
    (he : e = (rightUnitor _).symm ≪≫
      isoWhiskerLeft _ b.counitIso.symm ≪≫ associator _ _ _ ≪≫
      isoWhiskerLeft _ (associator _ _ _).symm ≪≫
      isoWhiskerLeft _ (isoWhiskerRight r _) ≪≫
      isoWhiskerLeft _ (associator _ _ _) ≪≫ (associator _ _ _).symm ≪≫
      isoWhiskerRight a.unitIso.symm _ ≪≫ leftUnitor _) :
    (mateEquiv a.toAdjunction b.toAdjunction (TwoSquare.mk _ _ _ _ e.inv)).natTrans =
      r.inv := by
  have hh : (mateEquiv a.toAdjunction b.toAdjunction).symm
      (TwoSquare.mk _ _ _ _ r.inv) = TwoSquare.mk _ _ _ _ e.inv := by
    subst e
    ext M
    simp [mateEquiv, Equivalence.toAdjunction]
  have h' := congrArg (fun x => (mateEquiv a.toAdjunction b.toAdjunction x).natTrans) hh
  simpa only [Equiv.apply_symm_apply] using h'.symm

end Underlying

section Composition

variable {A : Type uA} [Category.{vA} A] {B : Type uB} [Category.{vB} B]
  {C : Type uC} [Category.{vC} C]
  {L : A ⥤ C} {R : C ⥤ A} {L₁ : A ⥤ B} {R₁ : B ⥤ A}
  {L₂ : B ⥤ C} {R₂ : C ⥤ B}

/-- The whole counit law of the specified composite left-adjoint comparison. -/
theorem Adjunction.comparison_counit
    (a : L ⊣ R) (a₁ : L₁ ⊣ R₁) (a₂ : L₂ ⊣ R₂) (d : R ≅ R₂ ⋙ R₁) :
    whiskerLeft (R₂ ⋙ R₁) ((a.ofNatIsoRight d).leftAdjointUniq (a₁.comp a₂)).hom ≫
      (a₁.comp a₂).counit = (a.ofNatIsoRight d).counit :=
  Adjunction.leftAdjointUniq_hom_counit (a.ofNatIsoRight d) (a₁.comp a₂)

/-- Evaluation retains both original counits and the original right comparison. -/
theorem Adjunction.comparison_counit_app
    (a : L ⊣ R) (a₁ : L₁ ⊣ R₁) (a₂ : L₂ ⊣ R₂) (d : R ≅ R₂ ⋙ R₁) (M : C) :
    ((a.ofNatIsoRight d).leftAdjointUniq (a₁.comp a₂)).hom.app (R₁.obj (R₂.obj M)) ≫
      L₂.map (a₁.counit.app (R₂.obj M)) ≫ a₂.counit.app M =
        L.map (d.inv.app M) ≫ a.counit.app M := by
  have h := congr_app (Adjunction.comparison_counit a a₁ a₂ d) M
  change ((a.ofNatIsoRight d).leftAdjointUniq (a₁.comp a₂)).hom.app (R₁.obj (R₂.obj M)) ≫
    (a₁.comp a₂).counit.app M = L.map (d.inv.app M) ≫ a.counit.app M at h
  rw [Adjunction.comp_counit_app] at h
  exact h

end Composition


section MateUnit

variable {A : Type*} [Category* A] {B : Type*} [Category* B]
  {C : Type*} [Category* C] {D : Type*} [Category* D]
  {L₁ : A ⥤ B} {R₁ : B ⥤ A} {L₂ : C ⥤ D} {R₂ : D ⥤ C}
  {U : A ⥤ C} {V : B ⥤ D}

/-- The whole underlying unit square follows from the original mate equation. -/
theorem Adjunction.underlying_unit (a : L₁ ⊣ R₁) (b : L₂ ⊣ R₂)
    (e : L₁ ⋙ V ≅ U ⋙ L₂) (d : R₁ ⋙ U ≅ V ⋙ R₂)
    (h : (mateEquiv a b (TwoSquare.mk _ _ _ _ e.inv)).natTrans = d.hom) :
    (leftUnitor U).inv ≫ whiskerRight a.unit U ≫ (associator L₁ R₁ U).hom ≫
      whiskerLeft L₁ d.hom ≫ (associator L₁ V R₂).inv ≫ whiskerRight e.hom R₂ ≫
      (associator U L₂ R₂).hom = (rightUnitor U).inv ≫ whiskerLeft U b.unit := by
  ext M
  have hu := unit_mateEquiv a b (TwoSquare.mk _ _ _ _ e.inv) M
  change U.map (a.unit.app M) ≫
    (mateEquiv a b (TwoSquare.mk _ _ _ _ e.inv)).natTrans.app (L₁.obj M) =
      b.unit.app (U.obj M) ≫ R₂.map (e.inv.app M) at hu
  rw [h] at hu
  have ht := congrArg (fun k => k ≫ R₂.map (e.hom.app M)) hu
  simp only [Functor.comp_obj, Functor.id_obj, Category.assoc, ← R₂.map_comp,
    Iso.inv_hom_id_app] at ht
  rw [Functor.map_id, Category.comp_id] at ht
  change 𝟙 _ ≫ U.map (a.unit.app M) ≫ 𝟙 _ ≫ d.hom.app (L₁.obj M) ≫
    𝟙 _ ≫ R₂.map (e.hom.app M) ≫ 𝟙 _ = 𝟙 _ ≫ b.unit.app (U.obj M)
  simpa only [Functor.comp_obj, Functor.id_obj, Category.id_comp, Category.comp_id] using ht

/-- Evaluation of the whole underlying unit identity. -/
theorem Adjunction.underlying_unit_app (a : L₁ ⊣ R₁) (b : L₂ ⊣ R₂)
    (e : L₁ ⋙ V ≅ U ⋙ L₂) (d : R₁ ⋙ U ≅ V ⋙ R₂)
    (h : (mateEquiv a b (TwoSquare.mk _ _ _ _ e.inv)).natTrans = d.hom) (M : A) :
    U.map (a.unit.app M) ≫ d.hom.app (L₁.obj M) ≫ R₂.map (e.hom.app M) =
      b.unit.app (U.obj M) := by
  have hu := congr_app (Adjunction.underlying_unit a b e d h) M
  change 𝟙 _ ≫ U.map (a.unit.app M) ≫ 𝟙 _ ≫ d.hom.app (L₁.obj M) ≫
    𝟙 _ ≫ R₂.map (e.hom.app M) ≫ 𝟙 _ = 𝟙 _ ≫ b.unit.app (U.obj M) at hu
  simpa only [Functor.comp_obj, Functor.id_obj, Category.id_comp, Category.comp_id] using hu

/-- Right-adjoint transport retains the same actual left comparison and its transported mate. -/
theorem mateEquiv_ofNatIsoRight_comparison
    (a : L₁ ⊣ R₁) (b : L₂ ⊣ R₂) {R₁' : B ⥤ A} {R₂' : D ⥤ C}
    (q₁ : R₁ ≅ R₁') (q₂ : R₂ ≅ R₂')
    (e : L₁ ⋙ V ≅ U ⋙ L₂) (d : R₁ ⋙ U ≅ V ⋙ R₂)
    (d' : R₁' ⋙ U ≅ V ⋙ R₂')
    (h : (mateEquiv a b (TwoSquare.mk _ _ _ _ e.inv)).natTrans = d.hom)
    (hd : whiskerRight q₁.hom U ≫ d'.hom = d.hom ≫ whiskerLeft V q₂.hom) :
    (mateEquiv (a.ofNatIsoRight q₁) (b.ofNatIsoRight q₂)
      (TwoSquare.mk _ _ _ _ e.inv)).natTrans = d'.hom := by
  apply mateEquiv_inv_natTrans_eq_of_unit _ _ e
  intro M
  have hdc := congr_app hd (L₁.obj M)
  change U.map (q₁.hom.app (L₁.obj M)) ≫ d'.hom.app (L₁.obj M) =
    d.hom.app (L₁.obj M) ≫ q₂.hom.app (V.obj (L₁.obj M)) at hdc
  change U.map (a.unit.app M ≫ q₁.hom.app (L₁.obj M)) ≫
    d'.hom.app (L₁.obj M) ≫ R₂'.map (e.hom.app M) =
      b.unit.app (U.obj M) ≫ q₂.hom.app (L₂.obj (U.obj M))
  rw [U.map_comp, Category.assoc, ← Category.assoc
    (U.map (q₁.hom.app (L₁.obj M))), hdc, Category.assoc,
    ← q₂.hom.naturality, ← Category.assoc]
  simpa only [Category.assoc, Functor.comp_obj] using
    congrArg (fun k => k ≫ q₂.hom.app (L₂.obj (U.obj M)))
      (Adjunction.underlying_unit_app a b e d h M)

end MateUnit

section Pasting

variable {A B C D E F : Type*}
  [Category* A] [Category* B] [Category* C] [Category* D] [Category* E] [Category* F]
  {G : A ⥤ D} {H : B ⥤ E} {K : C ⥤ F}
  {L₁ : A ⥤ B} {R₁ : B ⥤ A} {L₂ : D ⥤ E} {R₂ : E ⥤ D}
  {L₃ : B ⥤ C} {R₃ : C ⥤ B} {L₄ : E ⥤ F} {R₄ : F ⥤ E}

/-- Composition of the specified underlying comparisons retains their original mates. -/
theorem mateEquiv_composite_comparison
    (a₁ : L₁ ⊣ R₁) (a₂ : L₂ ⊣ R₂) (a₃ : L₃ ⊣ R₃) (a₄ : L₄ ⊣ R₄)
    (e₁ : L₁ ⋙ H ≅ G ⋙ L₂) (e₂ : L₃ ⋙ K ≅ H ⋙ L₄)
    (e : (L₁ ⋙ L₃) ⋙ K ≅ G ⋙ (L₂ ⋙ L₄))
    (he : e = associator _ _ _ ≪≫ isoWhiskerLeft L₁ e₂ ≪≫
      (associator _ _ _).symm ≪≫ isoWhiskerRight e₁ L₄ ≪≫ associator _ _ _)
    (d₁ : R₁ ⋙ G ≅ H ⋙ R₂) (d₂ : R₃ ⋙ H ≅ K ⋙ R₄)
    (d : (R₃ ⋙ R₁) ⋙ G ≅ K ⋙ (R₄ ⋙ R₂))
    (hd : d = associator _ _ _ ≪≫ isoWhiskerLeft R₃ d₁ ≪≫
      (associator _ _ _).symm ≪≫ isoWhiskerRight d₂ R₂ ≪≫ associator _ _ _)
    (h₁ : (mateEquiv a₁ a₂ (TwoSquare.mk _ _ _ _ e₁.inv)).natTrans = d₁.hom)
    (h₂ : (mateEquiv a₃ a₄ (TwoSquare.mk _ _ _ _ e₂.inv)).natTrans = d₂.hom) :
    (mateEquiv (a₁.comp a₃) (a₂.comp a₄) (TwoSquare.mk _ _ _ _ e.inv)).natTrans =
      d.hom := by
  have he' : TwoSquare.mk _ _ _ _ e.inv =
      (TwoSquare.mk _ _ _ _ e₁.inv) ≫ᵥ (TwoSquare.mk _ _ _ _ e₂.inv) := by
    subst e
    ext M
    simp
  rw [he', mateEquiv_hcomp]
  ext M
  simp only [TwoSquare.hComp_app, TwoSquare.mk, TwoSquare.natTrans]
  rw [congr_app h₁, congr_app h₂]
  subst d
  simp

end Pasting

section Uniqueness

variable {A B C D : Type*} [Category* A] [Category* B] [Category* C] [Category* D]
  {L L' : A ⥤ B} {R : B ⥤ A} {K K' : C ⥤ D} {S : D ⥤ C}
  {U : A ⥤ C} {V : B ⥤ D}

/-- The whole original left-adjoint uniqueness comparison commutes with forgetting. -/
theorem Adjunction.underlying_leftAdjointUniq
    (a : L ⊣ R) (a' : L' ⊣ R) (b : K ⊣ S) (b' : K' ⊣ S)
    (e : L ⋙ V ≅ U ⋙ K) (e' : L' ⋙ V ≅ U ⋙ K') (d : R ⋙ U ≅ V ⋙ S)
    (h : (mateEquiv a b (TwoSquare.mk _ _ _ _ e.inv)).natTrans = d.hom)
    (h' : (mateEquiv a' b' (TwoSquare.mk _ _ _ _ e'.inv)).natTrans = d.hom) :
    whiskerRight (a.leftAdjointUniq a').hom V ≫ e'.hom =
      e.hom ≫ whiskerLeft U (b.leftAdjointUniq b').hom := by
  ext M
  change V.map ((a.leftAdjointUniq a').hom.app M) ≫ e'.hom.app M =
    e.hom.app M ≫ (b.leftAdjointUniq b').hom.app (U.obj M)
  apply (cancel_epi (e.inv.app M)).mp
  rw [Iso.inv_hom_id_app_assoc]
  apply (b.homEquiv _ _).injective
  have hval := underlying_homEquiv_of_mate a b (TwoSquare.mk _ _ _ _ e.inv) d.hom h
    M (L'.obj M) ((a.leftAdjointUniq a').hom.app M)
  rw [Adjunction.homEquiv_leftAdjointUniq_hom_app] at hval
  change U.map (a'.unit.app M) ≫ d.hom.app (L'.obj M) =
    b.homEquiv _ _ (e.inv.app M ≫ V.map ((a.leftAdjointUniq a').hom.app M)) at hval
  rw [← Category.assoc, Adjunction.homEquiv_naturality_right, ← hval,
    Category.assoc, Adjunction.underlying_unit_app a' b' e' d h']
  exact (Adjunction.homEquiv_leftAdjointUniq_hom_app b b' (U.obj M)).symm

end Uniqueness


section WholeComparison

variable {A B C A' B' C' : Type*}
  [Category* A] [Category* B] [Category* C]
  [Category* A'] [Category* B'] [Category* C']
  {L : A ⥤ B} {H : B ⥤ C} {T : A ⥤ C}
  {L' : A' ⥤ B'} {H' : B' ⥤ C'} {T' : A' ⥤ C'}
  {QA : A ⥤ A'} {QB : B ⥤ B'} {QC : C ⥤ C'}

/-- Componentwise original composition coherence determines the whole specified iso chain. -/
theorem Functor.underlying_comp_iso
    (eL : L ⋙ QB ≅ QA ⋙ L') (eH : H ⋙ QC ≅ QB ⋙ H')
    (eT : T ⋙ QC ≅ QA ⋙ T') (c : T ≅ L ⋙ H) (d : T' ≅ L' ⋙ H')
    (h : ∀ M, d.hom.app (QA.obj M) ≫ H'.map (eL.inv.app M) ≫
      eH.inv.app (L.obj M) = eT.inv.app M ≫ QC.map (c.hom.app M)) :
    isoWhiskerLeft QA d ≪≫ (associator QA L' H').symm ≪≫
      isoWhiskerRight eL.symm H' ≪≫ associator L QB H' ≪≫
      isoWhiskerLeft L eH.symm ≪≫ (associator L H QC).symm =
      eT.symm ≪≫ isoWhiskerRight c QC := by
  apply Iso.ext
  apply NatTrans.ext
  funext M
  simpa only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    isoWhiskerLeft_hom, isoWhiskerRight_hom, whiskerLeft_app, whiskerRight_app,
    associator_hom_app, associator_inv_app, Category.id_comp, Category.comp_id,
    Category.assoc] using h M

/-- The forward equation evaluates the same whole comparison, with no new map chosen. -/
theorem Functor.underlying_comp_hom_app
    (eL : L ⋙ QB ≅ QA ⋙ L') (eH : H ⋙ QC ≅ QB ⋙ H')
    (eT : T ⋙ QC ≅ QA ⋙ T') (c : T ≅ L ⋙ H) (d : T' ≅ L' ⋙ H')
    (h : isoWhiskerLeft QA d ≪≫ (associator QA L' H').symm ≪≫
      isoWhiskerRight eL.symm H' ≪≫ associator L QB H' ≪≫
      isoWhiskerLeft L eH.symm ≪≫ (associator L H QC).symm =
      eT.symm ≪≫ isoWhiskerRight c QC) (M : A) :
    QC.map (c.hom.app M) ≫ eH.hom.app (L.obj M) ≫ H'.map (eL.hom.app M) =
      eT.hom.app M ≫ d.hom.app (QA.obj M) := by
  have hi := congrArg (fun f => f.hom.app M) h
  have hf := hom_square_of_inv (eT.app M)
    ((eH.app (L.obj M)) ≪≫ H'.mapIso (eL.app M))
    (QC.map (c.hom.app M)) (d.hom.app (QA.obj M)) (by
      simpa only [Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, NatTrans.comp_app,
        isoWhiskerLeft_hom, isoWhiskerRight_hom, whiskerLeft_app, whiskerRight_app,
        associator_hom_app, associator_inv_app, Functor.mapIso_inv,
        Iso.app_inv, Category.id_comp, Category.comp_id, Category.assoc] using hi)
  simpa only [Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom, Category.assoc] using hf

end WholeComparison

section Coefficients

variable {A B C : Type*} [Category* A] [Category* B] [Category* C]
  {L : A ⥤ C} {R : C ⥤ A} {Li : A ⥤ B} {Ri : B ⥤ A}
  {Lj : B ⥤ C} {Rj : C ⥤ B}

/-- Original coefficient isomorphisms compatible with right composition give counit composition. -/
theorem Adjunction.coefficient_counit_comp
    (a : L ⊣ R) (ai : Li ⊣ Ri) (aj : Lj ⊣ Rj) (d : R ≅ Rj ⋙ Ri)
    {M : C} {N : B} {P : A} (p : Rj.obj M ≅ N) (q : Ri.obj N ≅ P) (r : R.obj M ≅ P)
    (hp : d.hom.app M ≫ Ri.map p.hom ≫ q.hom = r.hom) :
    ((a.ofNatIsoRight d).leftAdjointUniq (ai.comp aj)).hom.app P ≫
      Lj.map (Li.map q.inv ≫ ai.counit.app N) ≫ (Lj.map p.inv ≫ aj.counit.app M) =
        L.map r.inv ≫ a.counit.app M := by
  let c := (a.ofNatIsoRight d).leftAdjointUniq (ai.comp aj)
  have hi : r.inv ≫ d.hom.app M = q.inv ≫ Ri.map p.inv := by
    apply (cancel_epi r.hom).mp
    rw [Iso.hom_inv_id_assoc, ← hp]
    simp only [Category.assoc, Iso.hom_inv_id_assoc, ← Ri.map_comp,
      Iso.hom_inv_id, Ri.map_id]
    exact (Category.comp_id _).symm
  have hc : Li.map (Ri.map p.inv) ≫ ai.counit.app (Rj.obj M) =
      ai.counit.app N ≫ p.inv := ai.counit.naturality p.inv
  have hcm : Lj.map (ai.counit.app N) ≫ Lj.map p.inv =
      Lj.map (Li.map (Ri.map p.inv)) ≫ Lj.map (ai.counit.app (Rj.obj M)) :=
    (Lj.map_comp _ _).symm.trans ((congrArg Lj.map hc.symm).trans (Lj.map_comp _ _))
  change c.hom.app P ≫ Lj.map (Li.map q.inv ≫ ai.counit.app N) ≫
    (Lj.map p.inv ≫ aj.counit.app M) = _
  rw [Lj.map_comp]
  calc
    _ = c.hom.app P ≫ Lj.map (Li.map q.inv) ≫ Lj.map (Li.map (Ri.map p.inv)) ≫
        Lj.map (ai.counit.app (Rj.obj M)) ≫ aj.counit.app M := by
      simp only [Category.assoc]
      rw [reassoc_of% hcm]
    _ = L.map (q.inv ≫ Ri.map p.inv) ≫ c.hom.app (Ri.obj (Rj.obj M)) ≫
        Lj.map (ai.counit.app (Rj.obj M)) ≫ aj.counit.app M := by
      have hn := c.hom.naturality (q.inv ≫ Ri.map p.inv)
      change L.map (q.inv ≫ Ri.map p.inv) ≫ c.hom.app (Ri.obj (Rj.obj M)) =
        c.hom.app P ≫ Lj.map (Li.map (q.inv ≫ Ri.map p.inv)) at hn
      rw [← Lj.map_comp_assoc (Li.map q.inv) (Li.map (Ri.map p.inv)), ← Li.map_comp]
      simpa only [Category.assoc] using
        congrArg (fun z => z ≫ Lj.map (ai.counit.app (Rj.obj M)) ≫ aj.counit.app M) hn.symm
    _ = L.map (r.inv ≫ d.hom.app M) ≫ c.hom.app (Ri.obj (Rj.obj M)) ≫
        Lj.map (ai.counit.app (Rj.obj M)) ≫ aj.counit.app M := by rw [← hi]
    _ = L.map r.inv ≫ a.counit.app M := by
      rw [L.map_comp, Category.assoc, Adjunction.comparison_counit_app a ai aj d]
      rw [← L.map_comp_assoc (d.hom.app M) (d.inv.app M),
        Iso.hom_inv_id_app, L.map_id, Category.id_comp]

/-- The same compatible coefficients identify the original counit extension square. -/
theorem Adjunction.coefficient_counit_extension
    (a : L ⊣ R) (ai : Li ⊣ Ri) (aj : Lj ⊣ Rj) (d : R ≅ Rj ⋙ Ri)
    {M : C} {N : B} {P : A} (p : Rj.obj M ≅ N) (q : Ri.obj N ≅ P) (r : R.obj M ≅ P)
    (hp : d.hom.app M ≫ Ri.map p.hom ≫ q.hom = r.hom) :
    L.map q.hom ≫ (L.map r.inv ≫ a.counit.app M) =
      ((a.ofNatIsoRight d).leftAdjointUniq (ai.comp aj)).hom.app (Ri.obj N) ≫
        Lj.map (ai.counit.app N) ≫ (Lj.map p.inv ≫ aj.counit.app M) := by
  let c := (a.ofNatIsoRight d).leftAdjointUniq (ai.comp aj)
  rw [← Adjunction.coefficient_counit_comp a ai aj d p q r hp]
  have hc := c.hom.naturality q.hom
  change L.map q.hom ≫ c.hom.app P =
    c.hom.app (Ri.obj N) ≫ Lj.map (Li.map q.hom) at hc
  rw [reassoc_of% hc, Lj.map_comp]
  simp only [Category.assoc]
  rw [← Lj.map_comp_assoc (Li.map q.hom) (Li.map q.inv),
    ← Li.map_comp, q.hom_inv_id, Li.map_id, Lj.map_id, Category.id_comp]

end Coefficients

/-- A whole isomorphism factorization gives the corresponding inverse-prefix equation. -/
theorem Iso.inv_comp_of_hom_eq_comp {C : Type*} [Category* C] {A B D : C}
    (c : A ≅ D) (a : A ≅ B) (b : B ≅ D) (h : c.hom = a.hom ≫ b.hom) :
    c.inv ≫ a.hom = b.inv := by
  apply c.inv_comp_eq.mpr
  rw [h, Category.assoc, b.hom_inv_id, Category.comp_id]


section UnderlyingCoefficient

variable {A B C D : Type*} [Category* A] [Category* B] [Category* C] [Category* D]
  {L₁ : A ⥤ B} {R₁ : B ⥤ A} {L₂ : C ⥤ D} {R₂ : D ⥤ C}
  {U : A ⥤ C} {V : B ⥤ D}

/-- Compatible coefficient isomorphisms retain the original underlying counit square. -/
theorem Adjunction.underlying_coefficient_counit
    (a : L₁ ⊣ R₁) (b : L₂ ⊣ R₂) (e : L₁ ⋙ V ≅ U ⋙ L₂)
    (d : R₁ ⋙ U ≅ V ⋙ R₂)
    (hm : (mateEquiv a b (TwoSquare.mk _ _ _ _ e.inv)).natTrans = d.hom)
    {M : B} {N : A} {M' : D} {N' : C}
    (p : R₁.obj M ≅ N) (q : R₂.obj M' ≅ N') (t : V.obj M ≅ M') (s : U.obj N ≅ N')
    (hp : U.map p.hom ≫ s.hom = d.hom.app M ≫ R₂.map t.hom ≫ q.hom) :
    V.map (L₁.map p.inv ≫ a.counit.app M) ≫ t.hom =
      e.hom.app N ≫ L₂.map s.hom ≫ (L₂.map q.inv ≫ b.counit.app M') := by
  have hi : U.map p.inv ≫ d.hom.app M ≫ R₂.map t.hom = s.hom ≫ q.inv := by
    apply (cancel_epi (U.map p.hom)).mp
    rw [← Category.assoc, ← U.map_comp, p.hom_inv_id, U.map_id, Category.id_comp]
    rw [← Category.assoc, hp]
    simp only [Category.assoc, q.hom_inv_id, Category.comp_id]
  have he := e.hom.naturality p.inv
  change V.map (L₁.map p.inv) ≫ e.hom.app (R₁.obj M) =
    e.hom.app N ≫ L₂.map (U.map p.inv) at he
  have hb := b.counit.naturality t.hom
  change L₂.map (R₂.map t.hom) ≫ b.counit.app M' =
    b.counit.app (V.obj M) ≫ t.hom at hb
  rw [V.map_comp, Category.assoc, Adjunction.underlying_counit_app a b e d hm]
  simp only [Category.assoc]
  rw [reassoc_of% he, ← hb]
  rw [← L₂.map_comp_assoc (d.hom.app M) (R₂.map t.hom),
    ← L₂.map_comp_assoc (U.map p.inv) (d.hom.app M ≫ R₂.map t.hom), hi,
    L₂.map_comp]
  simp only [Category.assoc]

end UnderlyingCoefficient

section ActualConstructor

variable {A B C D E G : Type*}
  [Category* A] [Category* B] [Category* C] [Category* D] [Category* E] [Category* G]

/-- Evaluate the inverse of the actual six-factor underlying construction before native input. -/
theorem Functor.underlyingLowerShriek_inv_app
    (I : A ⥤ B) (L : B ⥤ C) (F : C ⥤ D) (U : D ⥤ E) (V : C ⥤ E)
    (W : B ⥤ G) (K : G ⥤ E) (T : A ⥤ G)
    (c : F ⋙ U ≅ V) (l : L ⋙ V ≅ W ⋙ K) (d : I ⋙ W ≅ T)
    (e : ((I ⋙ L) ⋙ F) ⋙ U ≅ T ⋙ K)
    (he : e = associator _ _ _ ≪≫ isoWhiskerLeft (I ⋙ L) c ≪≫
      associator _ _ _ ≪≫ isoWhiskerLeft I l ≪≫
      (associator _ _ _).symm ≪≫ isoWhiskerRight d K) (M : A) :
    e.inv.app M = K.map (d.inv.app M) ≫ l.inv.app (I.obj M) ≫ c.inv.app (L.obj (I.obj M)) := by
  subst e
  simp

end ActualConstructor

end CategoryTheory
