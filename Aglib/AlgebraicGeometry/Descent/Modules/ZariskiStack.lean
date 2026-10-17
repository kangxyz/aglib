/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Descent.Modules.OpenCoverGluing

/-!
# Module sheaves form a Zariski stack

For a family of open immersions `f : ∀ i, X i ⟶ S` and a descent datum `D` for `f`, the glued
sheaf of `OpenCoverGluing` restricts to `D.obj l` on `X l`: every section of `D.obj l` over an
open `V ≤ (f l).opensRange` is the `l`-component of a matching family (`projectionSurjective`).
The matching condition is the cocycle identity of the transitions on the triple overlap
`Limits.pullback (snd f l i) (fst f i k)`, obtained from `D.hom_comp` and `D.pullHom_hom`
(Stacks, Section 6.33, Tag 00AK, and Lemma 6.33.2, Tag 00AL; the tags are those of Stacks
revision a04446e5; their statements were read on the Stacks website on 2026-10-17).
This gives the instances `IsStack Scheme.zariskiTopology` for `pullbackPseudofunctor`,
`quasicoherentPseudofunctor` and `lineBundlePseudofunctor`, which contain the statement of
Stacks Project (revision a04446e5), Tag 023E.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory Opposite Bicategory Pseudofunctor TopologicalSpace

namespace AlgebraicGeometry.Scheme.Modules

/-- Restriction form of `pullHom` along an open immersion, for arbitrary composites. -/
lemma pullbackPseudofunctor_pullHom_restrict' {X₁ X₂ Y Y' : Scheme.{u}} (a : Y ⟶ X₁)
    (b : Y ⟶ X₂) (c : Y' ⟶ Y) [IsOpenImmersion a] [IsOpenImmersion b] [IsOpenImmersion c]
    {M₁ : X₁.Modules} {M₂ : X₂.Modules}
    (φ : (pullback a).obj M₁ ⟶ (pullback b).obj M₂) (g₁ : Y' ⟶ X₁) (g₂ : Y' ⟶ X₂)
    (h₁ : c ≫ a = g₁) (h₂ : c ≫ b = g₂) [IsOpenImmersion g₁] [IsOpenImmersion g₂] :
    (restrictFunctorIsoPullback g₁).hom.app M₁ ≫
        Pseudofunctor.LocallyDiscreteOpToCat.pullHom (F := pullbackPseudofunctor) φ c
          g₁ g₂ h₁ h₂ ≫ (restrictFunctorIsoPullback g₂).inv.app M₂ =
      (restrictFunctorCongr h₁).inv.app M₁ ≫ (restrictFunctorComp c a).hom.app M₁ ≫
        (restrictFunctor c).map ((restrictFunctorIsoPullback a).hom.app M₁ ≫ φ ≫
          (restrictFunctorIsoPullback b).inv.app M₂) ≫
        (restrictFunctorComp c b).inv.app M₂ ≫ (restrictFunctorCongr h₂).hom.app M₂ := by
  subst h₁ h₂
  have e₁ : (restrictFunctorCongr (rfl : c ≫ a = c ≫ a)).inv.app M₁ = 𝟙 _ := by
    ext U : 1
    simp only [restrictFunctorCongr_inv_app_app, eqToHom_refl, op_id, Hom.id_app]
    exact M₁.presheaf.map_id _
  have e₂ : (restrictFunctorCongr (rfl : c ≫ b = c ≫ b)).hom.app M₂ = 𝟙 _ := by
    ext U : 1
    simp only [restrictFunctorCongr_hom_app_app, eqToHom_refl, op_id, Hom.id_app]
    exact M₂.presheaf.map_id _
  rw [e₁, e₂, Category.id_comp, Category.comp_id]
  exact pullbackPseudofunctor_pullHom_restrict a b c φ

namespace OpenCoverGluing

variable {S : Scheme.{u}} {ι : Type u} {X : ι → Scheme.{u}} (f : ∀ i, X i ⟶ S)
  [∀ i, IsOpenImmersion (f i)] (D : pullbackPseudofunctor.{u}.DescentData f)

/-- The triple overlap, as the fibre product of `X l ×_S X i` and `X i ×_S X k` over `X i`. -/
abbrev triple (l i k : ι) : Scheme.{u} := Limits.pullback (snd f l i) (fst f i k)

/-- The projection from the triple overlap to `X l ×_S X i`. -/
abbrev tr₁ (l i k : ι) : triple f l i k ⟶ Limits.pullback (f l) (f i) := Limits.pullback.fst _ _

/-- The projection from the triple overlap to `X i ×_S X k`. -/
abbrev tr₂ (l i k : ι) : triple f l i k ⟶ Limits.pullback (f i) (f k) := Limits.pullback.snd _ _

omit [∀ i, IsOpenImmersion (f i)] in
lemma tr_condition (l i k : ι) : tr₁ f l i k ≫ snd f l i = tr₂ f l i k ≫ fst f i k :=
  Limits.pullback.condition

omit [∀ i, IsOpenImmersion (f i)] in
lemma tr_lift_condition (l i k : ι) :
    (tr₁ f l i k ≫ fst f l i) ≫ f l = (tr₂ f l i k ≫ snd f i k) ≫ f k := by
  simp only [Category.assoc]
  rw [fst_ι_eq_snd_ι, reassoc_of% (tr_condition f l i k), fst_ι_eq_snd_ι]

/-- The map from the triple overlap to `X l ×_S X k`. -/
def tr₃ (l i k : ι) : triple f l i k ⟶ Limits.pullback (f l) (f k) :=
  Limits.pullback.lift (tr₁ f l i k ≫ fst f l i) (tr₂ f l i k ≫ snd f i k)
    (tr_lift_condition f l i k)

instance (l i k : ι) : IsOpenImmersion (tr₃ f l i k) := by
  have : IsOpenImmersion (tr₃ f l i k ≫ fst f l k) := by
    rw [tr₃, Limits.pullback.lift_fst]
    infer_instance
  exact IsOpenImmersion.of_comp _ (fst f l k)

omit [∀ i, IsOpenImmersion (f i)] in
lemma tr_yi (l i k : ι) :
    (tr₁ f l i k ≫ snd f l i) ≫ f i = (tr₂ f l i k ≫ snd f i k) ≫ f k := by
  rw [tr_condition, Category.assoc, Category.assoc, fst_ι_eq_snd_ι]

-- The descent-datum morphisms are compared with module-sheaf maps: relaxed instance
-- transparency lets `pullbackPseudofunctor.obj _` (a `Cat.of`) be seen as `X.Modules`.
set_option backward.isDefEq.respectTransparency false in
/-- The cocycle condition on the triple overlap, in restriction form. -/
lemma cocycle_restrict (l i k : ι) :
    ((restrictFunctorIsoPullback (tr₁ f l i k ≫ fst f l i)).hom.app (obj f D l) ≫
        D.hom ((tr₂ f l i k ≫ snd f i k) ≫ f k) (tr₁ f l i k ≫ fst f l i)
          (tr₁ f l i k ≫ snd f l i) (tr_lift_condition f l i k) (tr_yi f l i k) ≫
        (restrictFunctorIsoPullback (tr₁ f l i k ≫ snd f l i)).inv.app (obj f D i)) ≫
      ((restrictFunctorIsoPullback (tr₁ f l i k ≫ snd f l i)).hom.app (obj f D i) ≫
        D.hom ((tr₂ f l i k ≫ snd f i k) ≫ f k) (tr₁ f l i k ≫ snd f l i)
          (tr₂ f l i k ≫ snd f i k) (tr_yi f l i k) rfl ≫
        (restrictFunctorIsoPullback (tr₂ f l i k ≫ snd f i k)).inv.app (obj f D k)) =
      (restrictFunctorIsoPullback (tr₁ f l i k ≫ fst f l i)).hom.app (obj f D l) ≫
        D.hom ((tr₂ f l i k ≫ snd f i k) ≫ f k) (tr₁ f l i k ≫ fst f l i)
          (tr₂ f l i k ≫ snd f i k) (tr_lift_condition f l i k) rfl ≫
        (restrictFunctorIsoPullback (tr₂ f l i k ≫ snd f i k)).inv.app (obj f D k) := by
  simp only [Category.assoc, Iso.inv_hom_id_app_assoc]
  rw [D.hom_comp_assoc]

omit [∀ i, IsOpenImmersion (f i)] in
lemma tr₃_fst (l i k : ι) : tr₃ f l i k ≫ fst f l k = tr₁ f l i k ≫ fst f l i := by
  unfold tr₃
  exact Limits.pullback.lift_fst _ _ _

omit [∀ i, IsOpenImmersion (f i)] in
lemma tr₃_snd (l i k : ι) : tr₃ f l i k ≫ snd f l k = tr₂ f l i k ≫ snd f i k := by
  unfold tr₃
  exact Limits.pullback.lift_snd _ _ _

omit [∀ i, IsOpenImmersion (f i)] in
lemma tr₁_q (l i k : ι) :
    tr₁ f l i k ≫ (snd f l i ≫ f i) = (tr₂ f l i k ≫ snd f i k) ≫ f k := by
  rw [← Category.assoc, tr_yi]

omit [∀ i, IsOpenImmersion (f i)] in
lemma tr₂_q (l i k : ι) :
    tr₂ f l i k ≫ (snd f i k ≫ f k) = (tr₂ f l i k ≫ snd f i k) ≫ f k :=
  (Category.assoc _ _ _).symm

omit [∀ i, IsOpenImmersion (f i)] in
lemma tr₃_q (l i k : ι) :
    tr₃ f l i k ≫ (snd f l k ≫ f k) = (tr₂ f l i k ≫ snd f i k) ≫ f k := by
  rw [← Category.assoc, tr₃_snd]

lemma cocycle_li (l i k : ι) :
    (restrictFunctorIsoPullback (tr₁ f l i k ≫ fst f l i)).hom.app (obj f D l) ≫
        D.hom ((tr₂ f l i k ≫ snd f i k) ≫ f k) (tr₁ f l i k ≫ fst f l i)
          (tr₁ f l i k ≫ snd f l i) (tr_lift_condition f l i k) (tr_yi f l i k) ≫
        (restrictFunctorIsoPullback (tr₁ f l i k ≫ snd f l i)).inv.app (obj f D i) =
      (restrictFunctorComp (tr₁ f l i k) (fst f l i)).hom.app (obj f D l) ≫
        (restrictFunctor (tr₁ f l i k)).map (transition f D l i) ≫
          (restrictFunctorComp (tr₁ f l i k) (snd f l i)).inv.app (obj f D i) := by
  rw [← D.pullHom_hom (tr₁ f l i k) (snd f l i ≫ f i) ((tr₂ f l i k ≫ snd f i k) ≫ f k)
    (tr₁_q f l i k) (fst f l i) (snd f l i) (fst_ι_eq_snd_ι f l i) rfl _ _ rfl rfl]
  exact pullbackPseudofunctor_pullHom_restrict (fst f l i) (snd f l i) (tr₁ f l i k) _

lemma cocycle_ik (l i k : ι) :
    (restrictFunctorIsoPullback (tr₁ f l i k ≫ snd f l i)).hom.app (obj f D i) ≫
        D.hom ((tr₂ f l i k ≫ snd f i k) ≫ f k) (tr₁ f l i k ≫ snd f l i)
          (tr₂ f l i k ≫ snd f i k) (tr_yi f l i k) rfl ≫
        (restrictFunctorIsoPullback (tr₂ f l i k ≫ snd f i k)).inv.app (obj f D k) =
      (restrictFunctorCongr (tr_condition f l i k).symm).inv.app (obj f D i) ≫
        (restrictFunctorComp (tr₂ f l i k) (fst f i k)).hom.app (obj f D i) ≫
          (restrictFunctor (tr₂ f l i k)).map (transition f D i k) ≫
            (restrictFunctorComp (tr₂ f l i k) (snd f i k)).inv.app (obj f D k) ≫
              (restrictFunctorCongr (rfl : tr₂ f l i k ≫ snd f i k = _)).hom.app (obj f D k) := by
  rw [← D.pullHom_hom (tr₂ f l i k) (snd f i k ≫ f k) ((tr₂ f l i k ≫ snd f i k) ≫ f k)
    (tr₂_q f l i k) (fst f i k) (snd f i k) (fst_ι_eq_snd_ι f i k) rfl _ _
    (tr_condition f l i k).symm rfl]
  exact pullbackPseudofunctor_pullHom_restrict' (fst f i k) (snd f i k) (tr₂ f l i k) _ _ _ _ _

lemma cocycle_lk (l i k : ι) :
    (restrictFunctorIsoPullback (tr₁ f l i k ≫ fst f l i)).hom.app (obj f D l) ≫
        D.hom ((tr₂ f l i k ≫ snd f i k) ≫ f k) (tr₁ f l i k ≫ fst f l i)
          (tr₂ f l i k ≫ snd f i k) (tr_lift_condition f l i k) rfl ≫
        (restrictFunctorIsoPullback (tr₂ f l i k ≫ snd f i k)).inv.app (obj f D k) =
      (restrictFunctorCongr (tr₃_fst f l i k)).inv.app (obj f D l) ≫
        (restrictFunctorComp (tr₃ f l i k) (fst f l k)).hom.app (obj f D l) ≫
          (restrictFunctor (tr₃ f l i k)).map (transition f D l k) ≫
            (restrictFunctorComp (tr₃ f l i k) (snd f l k)).inv.app (obj f D k) ≫
              (restrictFunctorCongr (tr₃_snd f l i k)).hom.app (obj f D k) := by
  rw [← D.pullHom_hom (tr₃ f l i k) (snd f l k ≫ f k) ((tr₂ f l i k ≫ snd f i k) ≫ f k)
    (tr₃_q f l i k) (fst f l k) (snd f l k) (fst_ι_eq_snd_ι f l k) rfl _ _
    (tr₃_fst f l i k) (tr₃_snd f l i k)]
  exact pullbackPseudofunctor_pullHom_restrict' (fst f l k) (snd f l k) (tr₃ f l i k) _ _ _ _ _

/-- The cocycle condition on the triple overlap, in terms of the overlap transitions. -/
lemma cocycle_transition (l i k : ι) :
    ((restrictFunctorComp (tr₁ f l i k) (fst f l i)).hom.app (obj f D l) ≫
        (restrictFunctor (tr₁ f l i k)).map (transition f D l i) ≫
          (restrictFunctorComp (tr₁ f l i k) (snd f l i)).inv.app (obj f D i)) ≫
      ((restrictFunctorCongr (tr_condition f l i k).symm).inv.app (obj f D i) ≫
        (restrictFunctorComp (tr₂ f l i k) (fst f i k)).hom.app (obj f D i) ≫
          (restrictFunctor (tr₂ f l i k)).map (transition f D i k) ≫
            (restrictFunctorComp (tr₂ f l i k) (snd f i k)).inv.app (obj f D k) ≫
              (restrictFunctorCongr (rfl : tr₂ f l i k ≫ snd f i k = _)).hom.app (obj f D k)) =
      (restrictFunctorCongr (tr₃_fst f l i k)).inv.app (obj f D l) ≫
        (restrictFunctorComp (tr₃ f l i k) (fst f l k)).hom.app (obj f D l) ≫
          (restrictFunctor (tr₃ f l i k)).map (transition f D l k) ≫
            (restrictFunctorComp (tr₃ f l i k) (snd f l k)).inv.app (obj f D k) ≫
              (restrictFunctorCongr (tr₃_snd f l i k)).hom.app (obj f D k) := by
  rw [← cocycle_li, ← cocycle_ik, ← cocycle_lk]
  exact cocycle_restrict f D l i k

lemma map_map_apply {Y : Scheme.{u}} (M : Y.Modules) {A B C : Y.Opensᵒᵖ} (g₁ : B ⟶ C)
    (g₂ : A ⟶ B) (g₃ : A ⟶ C) (x : M.presheaf.obj A) :
    M.presheaf.map g₁ (M.presheaf.map g₂ x) = M.presheaf.map g₃ x := by
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
  rfl

lemma app_map_apply {Y : Scheme.{u}} {M N : Y.Modules} (φ : M ⟶ N) {A B : Y.Opens}
    (h : B ≤ A) (x : Γ(M, A)) :
    φ.app B (M.presheaf.map (homOfLE h).op x) = N.presheaf.map (homOfLE h).op (φ.app A x) :=
  _root_.PresheafOfModules.naturality_apply φ.val (homOfLE h).op x

lemma second_app_apply (i k : ι) (V : S.Opens) (y : Γ(ambient f D k, V)) :
    (second f D i k).app V y =
      (obj f D k).presheaf.map (homOfLE ((snd f i k).image_preimage_le ((f k) ⁻¹ᵁ V))).op y :=
  rfl

-- The descent-datum morphism is compared with `pullbackCongr`: relaxed instance transparency
-- lets `pullbackPseudofunctor.obj _` (a `Cat.of`) be seen as `X.Modules`.
omit [∀ i, IsOpenImmersion (f i)] in
set_option backward.isDefEq.respectTransparency false in
/-- On equal maps, the descent-datum morphism is the canonical identification. -/
lemma hom_of_eq {Y : Scheme.{u}} (i : ι) (q : Y ⟶ S) (g₁ g₂ : Y ⟶ X i) (h : g₁ = g₂)
    (hg₁ : g₁ ≫ f i = q) (hg₂ : g₂ ≫ f i = q) :
    D.hom q g₁ g₂ hg₁ hg₂ = (pullbackCongr h).hom.app (obj f D i) := by
  subst h
  rw [D.hom_self q g₁ hg₁]
  simp [pullbackCongr]

/-- The transition on the diagonal overlap is the canonical identification. -/
lemma transition_self (i : ι) :
    transition f D i i = (restrictFunctorCongr (Limits.fst_eq_snd_of_mono_eq (f i))).hom.app
      (obj f D i) := by
  have hc := restrictFunctorIsoPullback_congr_hom_app (Limits.fst_eq_snd_of_mono_eq (f i))
    (obj f D i)
  have key : (restrictFunctorIsoPullback (fst f i i)).hom.app (obj f D i) ≫
      (pullbackCongr (Limits.fst_eq_snd_of_mono_eq (f i))).hom.app (obj f D i) ≫
        (restrictFunctorIsoPullback (snd f i i)).inv.app (obj f D i) =
      (restrictFunctorCongr (Limits.fst_eq_snd_of_mono_eq (f i))).hom.app (obj f D i) := by
    rw [← Category.assoc, hc, Category.assoc, Iso.hom_inv_id_app, Category.comp_id]
  rw [transition, hom_of_eq f D i _ _ _ (Limits.fst_eq_snd_of_mono_eq (f i))]
  exact key

omit [∀ i, IsOpenImmersion (f i)] in
lemma first_eq_second_of_eq {P : Scheme.{u}} (i : ι) (a b : P ⟶ X i) [IsOpenImmersion a]
    [IsOpenImmersion b] (h : a = b) (h' : a ≫ f i = b ≫ f i) (M : (X i).Modules) :
    (pushforward (f i)).map ((restrictAdjunction a).unit.app M ≫
        (pushforward a).map ((restrictFunctorCongr h).hom.app M)) ≫
      (pushforwardComp a (f i)).hom.app _ ≫ (pushforwardCongr h').hom.app _ ≫
        (pushforwardComp b (f i)).inv.app _ =
      (pushforward (f i)).map ((restrictAdjunction b).unit.app M) := by
  subst h
  have e₁ : (restrictFunctorCongr (rfl : a = a)).hom.app M = 𝟙 _ := by
    ext U : 1
    simp only [restrictFunctorCongr_hom_app_app, eqToHom_refl, op_id, Hom.id_app]
    exact M.presheaf.map_id _
  have e₂ : (pushforwardCongr h').hom.app ((restrictFunctor a).obj M) = 𝟙 _ := by
    ext U : 1
    simp only [pushforwardCongr_hom_app_app, eqToHom_refl, op_id, Hom.id_app]
    exact ((restrictFunctor a).obj M).presheaf.map_id _
  rw [e₁, e₂]
  simp

/-- On the diagonal overlap, the two restriction maps agree. -/
lemma first_self (i : ι) : first f D i i = second f D i i := by
  rw [first, transition_self]
  exact first_eq_second_of_eq f i _ _ (Limits.fst_eq_snd_of_mono_eq (f i)) _ _

lemma map_comp_map {Y : Scheme.{u}} (M : Y.Modules) {A B C : Y.Opensᵒᵖ} (g₁ : A ⟶ B)
    (g₂ : B ⟶ C) (g₃ : A ⟶ C) :
    M.presheaf.map g₁ ≫ M.presheaf.map g₂ = M.presheaf.map g₃ := by
  rw [← Functor.map_comp]
  rfl

omit [∀ i, IsOpenImmersion (f i)] in
lemma preimage_fst_eq (i k : ι) (V : S.Opens) :
    (fst f i k) ⁻¹ᵁ ((f i) ⁻¹ᵁ V) = (snd f i k) ⁻¹ᵁ ((f k) ⁻¹ᵁ V) :=
  congrArg (· ⁻¹ᵁ V) (fst_ι_eq_snd_ι f i k)

-- Sections of the pushforwards are sections of restrictions; matching the two descriptions
-- needs relaxed instance transparency.
set_option backward.isDefEq.respectTransparency false in
/-- Restricting `first` to a smaller open of the overlap gives the transition there. -/
lemma first_app_restrict (i k : ι) (V : S.Opens) (W : (Limits.pullback (f i) (f k)).Opens)
    (hW : W ≤ (snd f i k) ⁻¹ᵁ ((f k) ⁻¹ᵁ V)) (hW' : fst f i k ''ᵁ W ≤ (f i) ⁻¹ᵁ V) :
    (first f D i k).app V ≫ ((obj f D k).restrict (snd f i k)).presheaf.map (homOfLE hW).op =
      (obj f D i).presheaf.map (homOfLE hW').op ≫ (transition f D i k).app W := by
  have hW₀ : W ≤ (fst f i k) ⁻¹ᵁ ((f i) ⁻¹ᵁ V) := hW.trans (preimage_fst_eq f i k V).ge
  have nat := (transition f D i k).mapPresheaf.naturality (homOfLE hW₀).op
  simp only [mapPresheaf_app] at nat
  simp only [first, Hom.comp_app, pushforward_map_app, restrictAdjunction_unit_app_app,
    pushforwardComp_hom_app_app, pushforwardComp_inv_app_app, pushforwardCongr_hom_app_app,
    Functor.comp_obj, Category.id_comp, Category.assoc]
  erw [map_comp_map _ _ _ (homOfLE hW₀).op, ← nat]
  rw [← Category.assoc]
  congr 1
  exact map_comp_map (obj f D i) _ _ _

lemma map_comp_map₃ {Y : Scheme.{u}} (M : Y.Modules) {A B C E : Y.Opensᵒᵖ} (g₁ : A ⟶ B)
    (g₂ : B ⟶ C) (g₃ : C ⟶ E) (g₄ : A ⟶ E) :
    M.presheaf.map g₁ ≫ M.presheaf.map g₂ ≫ M.presheaf.map g₃ = M.presheaf.map g₄ := by
  rw [← Functor.map_comp, ← Functor.map_comp]
  rfl

/-- A restriction map between equal opens is invertible. -/
lemma isIso_map_homOfLE {Y : Scheme.{u}} (M : Y.Modules) {A B : Y.Opens} (h : A ≤ B)
    (h' : B ≤ A) : IsIso (M.presheaf.map (homOfLE h).op) :=
  ⟨⟨M.presheaf.map (homOfLE h').op,
    by rw [← Functor.map_comp, ← M.presheaf.map_id]; rfl,
    by rw [← Functor.map_comp, ← M.presheaf.map_id]; rfl⟩⟩

lemma image_le_of_le_preimage {Y₁ Y₂ : Scheme.{u}} (g : Y₁ ⟶ Y₂) [IsOpenImmersion g]
    {A : Y₁.Opens} {B : Y₂.Opens} (h : A ≤ g ⁻¹ᵁ B) : g ''ᵁ A ≤ B :=
  (g.image_mono h).trans (g.image_preimage_le B)

lemma restrictFunctor_map_app_eq {Y₁ Y₂ : Scheme.{u}} (c : Y₁ ⟶ Y₂) [IsOpenImmersion c]
    {M N : Y₂.Modules} (T : M ⟶ N) (Z : Y₁.Opens) :
    ((restrictFunctor c).map T).app Z = T.app (c ''ᵁ Z) :=
  rfl

lemma second_app_eq (i k : ι) (V : S.Opens) :
    (second f D i k).app V =
      (obj f D k).presheaf.map (homOfLE ((snd f i k).image_preimage_le ((f k) ⁻¹ᵁ V))).op :=
  rfl

lemma second_app_restrict (i k : ι) (V : S.Opens) (W : (Limits.pullback (f i) (f k)).Opens)
    (hW : W ≤ (snd f i k) ⁻¹ᵁ ((f k) ⁻¹ᵁ V)) (hW' : snd f i k ''ᵁ W ≤ (f k) ⁻¹ᵁ V) :
    (second f D i k).app V ≫ ((obj f D k).restrict (snd f i k)).presheaf.map (homOfLE hW).op =
      (obj f D k).presheaf.map (homOfLE hW').op := by
  rw [second_app_eq]
  exact map_comp_map (obj f D k) _ _ _

-- As for `first_app_restrict`.
set_option backward.isDefEq.respectTransparency false in
/-- A lift `σ` of `first` through `second` restricts to the transition on an open of the
overlap. -/
lemma comp_restrict (l j : ι) (V : S.Opens) (σ : Γ(ambient f D l, V) ⟶ Γ(ambient f D j, V))
    (hσ : σ ≫ (second f D l j).app V = (first f D l j).app V)
    (O : (Limits.pullback (f l) (f j)).Opens) (hO : O ≤ (snd f l j) ⁻¹ᵁ ((f j) ⁻¹ᵁ V))
    (hO' : fst f l j ''ᵁ O ≤ (f l) ⁻¹ᵁ V) {B : (X j).Opens} (hB : B ≤ snd f l j ''ᵁ O)
    (hB' : B ≤ (f j) ⁻¹ᵁ V) :
    σ ≫ (obj f D j).presheaf.map (homOfLE hB').op =
      (obj f D l).presheaf.map (homOfLE hO').op ≫ (transition f D l j).app O ≫
        (obj f D j).presheaf.map (homOfLE hB).op := by
  have e : (obj f D j).presheaf.map (homOfLE hB').op = (second f D l j).app V ≫
      ((obj f D j).restrict (snd f l j)).presheaf.map (homOfLE hO).op ≫
        (obj f D j).presheaf.map (homOfLE hB).op := by
    rw [second_app_eq]
    exact (map_comp_map₃ (obj f D j) _ _ _ _).symm
  rw [e, reassoc_of% hσ, reassoc_of% (first_app_restrict f D l j V O hO hO')]

/-- Over an open contained in the range of `f l`, the triple overlap covers the part of the
overlap `X i ×_S X k` lying over it. -/
lemma le_image_tr₂ {l : ι} {V : S.Opens} (hV : V ≤ (f l).opensRange) (i k : ι) :
    (snd f i k) ⁻¹ᵁ ((f k) ⁻¹ᵁ V) ≤
      tr₂ f l i k ''ᵁ (tr₂ f l i k ⁻¹ᵁ ((snd f i k) ⁻¹ᵁ ((f k) ⁻¹ᵁ V))) := by
  rw [Scheme.Hom.image_preimage_eq_opensRange_inf]
  refine le_inf ?_ le_rfl
  rw [Scheme.Hom.opensRange_pullbackSnd, Scheme.Hom.opensRange_pullbackSnd,
    ← preimage_fst_eq f i k V]
  exact Scheme.Hom.preimage_mono _ (Scheme.Hom.preimage_mono _ hV)

lemma map_endo {Y : Scheme.{u}} (M : Y.Modules) {A : Y.Opensᵒᵖ} (g : A ⟶ A) :
    M.presheaf.map g = 𝟙 _ := by
  rw [← M.presheaf.map_id]
  rfl

lemma eqToHom_opens {Y : Scheme.{u}} {A B : Y.Opens} (p : A = B) : eqToHom p = homOfLE p.le :=
  Subsingleton.elim _ _

lemma image_tr₂_fst (l i k : ι) (Z : (triple f l i k).Opens) :
    (tr₂ f l i k ≫ fst f i k) ''ᵁ Z = (tr₁ f l i k ≫ snd f l i) ''ᵁ Z := by
  simp only [tr_condition]

lemma image_tr₃_fst (l i k : ι) (Z : (triple f l i k).Opens) :
    (tr₃ f l i k ≫ fst f l k) ''ᵁ Z = (tr₁ f l i k ≫ fst f l i) ''ᵁ Z := by
  simp only [tr₃_fst]

lemma image_tr₃_snd (l i k : ι) (Z : (triple f l i k).Opens) :
    (tr₃ f l i k ≫ snd f l k) ''ᵁ Z = (tr₂ f l i k ≫ snd f i k) ''ᵁ Z := by
  simp only [tr₃_snd]

/-- The cocycle condition on the sections over the images of an open of the triple overlap. -/
lemma cocycle_app (l i k : ι) (Z : (triple f l i k).Opens) :
    (obj f D l).presheaf.map (homOfLE (Scheme.Hom.comp_image (tr₁ f l i k) (fst f l i) Z).ge).op ≫
      (transition f D l i).app (tr₁ f l i k ''ᵁ Z) ≫
        (obj f D i).presheaf.map
          (homOfLE (Scheme.Hom.comp_image (tr₁ f l i k) (snd f l i) Z).le).op ≫
          (obj f D i).presheaf.map (homOfLE (image_tr₂_fst f l i k Z).le).op ≫
            (obj f D i).presheaf.map
              (homOfLE (Scheme.Hom.comp_image (tr₂ f l i k) (fst f i k) Z).ge).op ≫
              (transition f D i k).app (tr₂ f l i k ''ᵁ Z) ≫
                (obj f D k).presheaf.map
                  (homOfLE (Scheme.Hom.comp_image (tr₂ f l i k) (snd f i k) Z).le).op ≫
                  (obj f D k).presheaf.map (homOfLE le_rfl).op =
      (obj f D l).presheaf.map (homOfLE (image_tr₃_fst f l i k Z).le).op ≫
        (obj f D l).presheaf.map
          (homOfLE (Scheme.Hom.comp_image (tr₃ f l i k) (fst f l k) Z).ge).op ≫
          (transition f D l k).app (tr₃ f l i k ''ᵁ Z) ≫
            (obj f D k).presheaf.map
              (homOfLE (Scheme.Hom.comp_image (tr₃ f l i k) (snd f l k) Z).le).op ≫
              (obj f D k).presheaf.map (homOfLE (image_tr₃_snd f l i k Z).ge).op := by
  have h := congrArg (fun φ ↦ φ.app Z) (cocycle_transition f D l i k)
  simp only [Hom.comp_app, restrictFunctorComp_hom_app_app, restrictFunctorComp_inv_app_app,
    restrictFunctorCongr_hom_app_app, restrictFunctorCongr_inv_app_app,
    restrictFunctor_map_app_eq, Category.assoc, eqToHom_opens] at h
  exact h

-- As for `cocycle_restrict`.
set_option backward.isDefEq.respectTransparency false in
/-- The matching step: lifts `σ i`, `σ k` of `first` through `second` from `U l` agree on
`U i ⊓ U k` after restriction to the part covered by the triple overlap. -/
lemma comp_first_restrict_eq (l i k : ι) (V : S.Opens)
    (σi : Γ(ambient f D l, V) ⟶ Γ(ambient f D i, V))
    (σk : Γ(ambient f D l, V) ⟶ Γ(ambient f D k, V))
    (hi : σi ≫ (second f D l i).app V = (first f D l i).app V)
    (hk : σk ≫ (second f D l k).app V = (first f D l k).app V) :
    σi ≫ (first f D i k).app V ≫ ((obj f D k).restrict (snd f i k)).presheaf.map
        (homOfLE ((tr₂ f l i k).image_preimage_le ((snd f i k) ⁻¹ᵁ ((f k) ⁻¹ᵁ V)))).op =
      σk ≫ (second f D i k).app V ≫ ((obj f D k).restrict (snd f i k)).presheaf.map
        (homOfLE ((tr₂ f l i k).image_preimage_le ((snd f i k) ⁻¹ᵁ ((f k) ⁻¹ᵁ V)))).op := by
  have hO₂W := (tr₂ f l i k).image_preimage_le ((snd f i k) ⁻¹ᵁ ((f k) ⁻¹ᵁ V))
  have hW'₂ : fst f i k ''ᵁ (tr₂ f l i k ''ᵁ (tr₂ f l i k ⁻¹ᵁ ((snd f i k) ⁻¹ᵁ ((f k) ⁻¹ᵁ V)))) ≤
      (f i) ⁻¹ᵁ V := image_le_of_le_preimage _ (hO₂W.trans (preimage_fst_eq f i k V).ge)
  have hW''₂ : snd f i k ''ᵁ (tr₂ f l i k ''ᵁ (tr₂ f l i k ⁻¹ᵁ ((snd f i k) ⁻¹ᵁ ((f k) ⁻¹ᵁ V)))) ≤
      (f k) ⁻¹ᵁ V := image_le_of_le_preimage _ hO₂W
  have hc1 : (tr₁ f l i k ≫ fst f l i) ''ᵁ (tr₂ f l i k ⁻¹ᵁ ((snd f i k) ⁻¹ᵁ ((f k) ⁻¹ᵁ V))) ≤
      (f l) ⁻¹ᵁ V :=
    image_le_of_le_preimage _ (congrArg (· ⁻¹ᵁ V) (tr_lift_condition f l i k)).ge
  have hO₁ : tr₁ f l i k ''ᵁ (tr₂ f l i k ⁻¹ᵁ ((snd f i k) ⁻¹ᵁ ((f k) ⁻¹ᵁ V))) ≤
      (snd f l i) ⁻¹ᵁ ((f i) ⁻¹ᵁ V) :=
    image_le_of_le_preimage _ (congrArg (· ⁻¹ᵁ V) (tr_yi f l i k)).ge
  have hO₁' : fst f l i ''ᵁ (tr₁ f l i k ''ᵁ (tr₂ f l i k ⁻¹ᵁ ((snd f i k) ⁻¹ᵁ ((f k) ⁻¹ᵁ V)))) ≤
      (f l) ⁻¹ᵁ V := (Scheme.Hom.comp_image _ _ _).ge.trans hc1
  have hO₃ : tr₃ f l i k ''ᵁ (tr₂ f l i k ⁻¹ᵁ ((snd f i k) ⁻¹ᵁ ((f k) ⁻¹ᵁ V))) ≤
      (snd f l k) ⁻¹ᵁ ((f k) ⁻¹ᵁ V) :=
    image_le_of_le_preimage _ (congrArg (fun g ↦ (g ≫ f k) ⁻¹ᵁ V) (tr₃_snd f l i k)).ge
  have hO₃' : fst f l k ''ᵁ (tr₃ f l i k ''ᵁ (tr₂ f l i k ⁻¹ᵁ ((snd f i k) ⁻¹ᵁ ((f k) ⁻¹ᵁ V)))) ≤
      (f l) ⁻¹ᵁ V :=
    (Scheme.Hom.comp_image _ _ _).ge.trans ((image_tr₃_fst f l i k _).le.trans hc1)
  have hB_i : fst f i k ''ᵁ (tr₂ f l i k ''ᵁ (tr₂ f l i k ⁻¹ᵁ ((snd f i k) ⁻¹ᵁ ((f k) ⁻¹ᵁ V)))) ≤
      snd f l i ''ᵁ (tr₁ f l i k ''ᵁ (tr₂ f l i k ⁻¹ᵁ ((snd f i k) ⁻¹ᵁ ((f k) ⁻¹ᵁ V)))) :=
    (Scheme.Hom.comp_image _ _ _).ge.trans
      ((image_tr₂_fst f l i k _).le.trans (Scheme.Hom.comp_image _ _ _).le)
  have hB_k : snd f i k ''ᵁ (tr₂ f l i k ''ᵁ (tr₂ f l i k ⁻¹ᵁ ((snd f i k) ⁻¹ᵁ ((f k) ⁻¹ᵁ V)))) ≤
      snd f l k ''ᵁ (tr₃ f l i k ''ᵁ (tr₂ f l i k ⁻¹ᵁ ((snd f i k) ⁻¹ᵁ ((f k) ⁻¹ᵁ V)))) :=
    (Scheme.Hom.comp_image _ _ _).ge.trans
      ((image_tr₃_snd f l i k _).ge.trans (Scheme.Hom.comp_image _ _ _).le)
  rw [first_app_restrict f D i k V _ hO₂W hW'₂, second_app_restrict f D i k V _ hO₂W hW''₂,
    reassoc_of% (comp_restrict f D l i V σi hi _ hO₁ hO₁' hB_i hW'₂),
    comp_restrict f D l k V σk hk _ hO₃ hO₃' hB_k hW''₂]
  have hc := ((obj f D l).presheaf.map (homOfLE hc1).op ≫= cocycle_app f D l i k
    (tr₂ f l i k ⁻¹ᵁ ((snd f i k) ⁻¹ᵁ ((f k) ⁻¹ᵁ V)))) =≫
      (obj f D k).presheaf.map (homOfLE (Scheme.Hom.comp_image (tr₂ f l i k) (snd f i k) _).ge).op
  simp only [Category.assoc, ← Functor.map_comp, ← Functor.map_comp_assoc] at hc
  rw [map_endo] at hc
  -- `Category.comp_id` must see through the two descriptions of the target sections.
  erw [Category.comp_id] at hc
  exact hc

end OpenCoverGluing

open OpenCoverGluing in
/-- The cocycle step: over an open contained in `U l`, every section of the object over `U l`
is the component of a matching family. -/
theorem projectionSurjective : ProjectionSurjective.{u} := by
  intro S ι X f hf D l V hV t
  have hiso : ∀ j, IsIso ((second f D l j).app V) := fun j ↦ isIso_second_app f D hV
  let σ : ∀ j, Γ(ambient f D l, V) ⟶ Γ(ambient f D j, V) :=
    fun j ↦ (first f D l j).app V ≫ inv ((second f D l j).app V)
  have hσ : ∀ j, σ j ≫ (second f D l j).app V = (first f D l j).app V := fun j ↦ by
    simp only [σ, Category.assoc, IsIso.inv_hom_id, Category.comp_id]
  refine ⟨(⟨fun j ↦ σ j t, fun i k ↦ ?_⟩ : matching f D V), ?_⟩
  · have hR := isIso_map_homOfLE ((obj f D k).restrict (snd f i k))
      ((tr₂ f l i k).image_preimage_le ((snd f i k) ⁻¹ᵁ ((f k) ⁻¹ᵁ V))) (le_image_tr₂ f hV i k)
    apply (ConcreteCategory.bijective_of_isIso (((obj f D k).restrict (snd f i k)).presheaf.map
      (homOfLE ((tr₂ f l i k).image_preimage_le ((snd f i k) ⁻¹ᵁ ((f k) ⁻¹ᵁ V)))).op)).1
    exact ConcreteCategory.congr_hom
      (comp_first_restrict_eq f D l i k V (σ i) (σ k) (hσ i) (hσ k)) t
  · change σ l t = t
    have h1 : σ l = 𝟙 _ := by simp only [σ, first_self, IsIso.hom_inv_id]
    rw [h1]
    rfl

/-- Module sheaves form a stack for the Zariski topology. This contains the statement of Stacks
Project (revision a04446e5), Tag 023E, and more:
* every covering sieve of Mathlib's big Zariski site `Scheme.zariskiTopology`, not only the
  sieve of an open covering;
* all module sheaves, not only quasi-coherent ones;
* Mathlib's `Pseudofunctor.DescentData`, which is equivalent to the fibre-product form of
  Stacks' descent data (Mathlib's `descentDataEquivalence` in
  `Sites/Descent/DescentDataPrime.lean`). -/
instance isStack_pullbackPseudofunctor_zariskiTopology :
    pullbackPseudofunctor.{u}.IsStack Scheme.zariskiTopology :=
  isStack_zariskiTopology_of_projectionSurjective projectionSurjective

/-- Quasi-coherent sheaves form a stack for the Zariski topology. This is the statement of Stacks
Project (revision a04446e5), Tag 023E, for every covering sieve of Mathlib's big Zariski site
`Scheme.zariskiTopology`, with Mathlib's `Pseudofunctor.DescentData`. -/
instance isStack_quasicoherentPseudofunctor_zariskiTopology :
    quasicoherentPseudofunctor.{u}.IsStack Scheme.zariskiTopology :=
  isStack_quasicoherentPseudofunctor_of_projectionSurjective projectionSurjective

/-- Line bundles (`Invertible.IsLocallyRankOne`) form a stack for the Zariski topology, for every
covering sieve of Mathlib's big Zariski site `Scheme.zariskiTopology` and with Mathlib's
`Pseudofunctor.DescentData`. This is the analogue of Stacks Project (revision a04446e5),
Tag 023E, for the full subpseudofunctor of locally rank-one module sheaves. -/
instance isStack_lineBundlePseudofunctor_zariskiTopology :
    lineBundlePseudofunctor.{u}.IsStack Scheme.zariskiTopology :=
  isStack_lineBundlePseudofunctor_of_projectionSurjective projectionSurjective

end AlgebraicGeometry.Scheme.Modules
