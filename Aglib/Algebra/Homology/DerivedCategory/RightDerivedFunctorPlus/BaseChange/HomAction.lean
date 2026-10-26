/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Adjunction.Mates.Whole
public import
  Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.BaseChange.H1Normalization

/-!
# Action of the canonical mate on adjoint morphisms

The original mate carries adjoint representatives through the original square.
Fixed source comparisons normalize this action without choosing another exchange
map. The generic result applies in particular to degree-one derived representatives.
-/

@[expose] public section

namespace CategoryTheory

universe uC uD uE uF vC vD vE vF

section HomAction
variable {C : Type uC} {D : Type uD} {E : Type uE} {F : Type uF}
  [Category.{vC} C] [Category.{vD} D] [Category.{vE} E] [Category.{vF} F]
  {G : C ⥤ E} {H : D ⥤ F}
  {L₁ : C ⥤ D} {R₁ : D ⥤ C} {L₂ : E ⥤ F} {R₂ : F ⥤ E}
  (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂)

/-- Literal action equation retaining the supplied actual square and exchange. -/
def MateHomActionEquation
    (α : TwoSquare G L₁ L₂ H) (β : R₁ ⋙ G ⟶ H ⋙ R₂)
    {A : C} {K : D} (a : L₁.obj A ⟶ K) : Prop :=
  G.map (adj₁.homEquiv A K a) ≫ β.app K =
    adj₂.homEquiv (G.obj A) (H.obj K) (α.app A ≫ H.map a)

/-- Exchange on adjoint morphisms is precisely the original square on their
left-adjoint representatives. In a derived category this applies to shifted
single representatives in every degree, in particular the original H¹ classes.
There is no assertion that taking sections commutes with cohomology. -/
theorem mateEquiv_homEquiv_action
    (α : TwoSquare G L₁ L₂ H) {A : C} {K : D} (a : L₁.obj A ⟶ K) :
    G.map (adj₁.homEquiv A K a) ≫ (mateEquiv adj₁ adj₂ α).natTrans.app K =
      adj₂.homEquiv (G.obj A) (H.obj K) (α.app A ≫ H.map a) := by
  have hn := (mateEquiv adj₁ adj₂ α).natTrans.naturality a
  change G.map (R₁.map a) ≫ (mateEquiv adj₁ adj₂ α).natTrans.app K =
    (mateEquiv adj₁ adj₂ α).natTrans.app (L₁.obj A) ≫ R₂.map (H.map a) at hn
  rw [Adjunction.homEquiv_unit, Functor.map_comp, Category.assoc, hn]
  rw [← Category.assoc, unit_mateEquiv]
  rw [Adjunction.homEquiv_unit, Functor.map_comp, Category.assoc]
  rfl

/-- After fixed source/constant comparisons, adjoint exchange recovers the
original pullback on morphisms. The sole hypothesis is a degree-zero
coherence of the source comparisons; it is not an H¹ compatibility assumption. -/
theorem mateEquiv_normalized_hom_action
    (α : TwoSquare G L₁ L₂ H) {A : C} {B : E} {Z K : D} {Z' : F}
    (c : L₁.obj A ≅ Z) (d : G.obj A ≅ B)
    (e : L₂.obj B ≅ Z') (t : H.obj Z ≅ Z')
    (hc : α.app A ≫ H.map c.hom ≫ t.hom = L₂.map d.hom ≫ e.hom)
    (a : Z ⟶ K) :
    e.inv ≫ L₂.map d.inv ≫
        (adj₂.homEquiv (G.obj A) (H.obj K)).symm
          (G.map (adj₁.homEquiv A K (c.hom ≫ a)) ≫
            (mateEquiv adj₁ adj₂ α).natTrans.app K) =
      t.inv ≫ H.map a := by
  have hs : e.inv ≫ L₂.map d.inv ≫ α.app A ≫ H.map c.hom = t.inv := by
    apply (cancel_mono t.hom).mp
    simp only [Category.assoc]
    rw [hc]
    simp only [← L₂.map_comp_assoc, Iso.inv_hom_id, Functor.map_id,
      Category.id_comp, Iso.inv_hom_id]
  rw [mateEquiv_homEquiv_action, Equiv.symm_apply_apply, Functor.map_comp]
  simpa only [Category.assoc] using congrArg (fun k => k ≫ H.map a) hs

/-- Actual-map adapter preserves both chosen adjunctions and the actual exchange. -/
theorem mateEquiv_homEquiv_action_actual
    (adj₁' : L₁ ⊣ R₁) (adj₂' : L₂ ⊣ R₂)
    (h₁ : adj₁ = adj₁') (h₂ : adj₂ = adj₂')
    (α : TwoSquare G L₁ L₂ H) (β : R₁ ⋙ G ⟶ H ⋙ R₂)
    (hβ : β = (mateEquiv adj₁' adj₂' α).natTrans)
    {A : C} {K : D} (a : L₁.obj A ⟶ K) :
    G.map (adj₁.homEquiv A K a) ≫ β.app K =
      adj₂.homEquiv (G.obj A) (H.obj K) (α.app A ≫ H.map a) := by
  subst adj₁'
  subst adj₂'
  subst β
  exact mateEquiv_homEquiv_action adj₁ adj₂ α a

/-- The shared equation is proved for the actual exchange through canonical aliases. -/
theorem mateHomActionEquation_actual
    (adj₁' : L₁ ⊣ R₁) (adj₂' : L₂ ⊣ R₂)
    (h₁ : adj₁ = adj₁') (h₂ : adj₂ = adj₂')
    (α : TwoSquare G L₁ L₂ H) (β : R₁ ⋙ G ⟶ H ⋙ R₂)
    (hβ : β = (mateEquiv adj₁' adj₂' α).natTrans)
    {A : C} {K : D} (a : L₁.obj A ⟶ K) :
    MateHomActionEquation adj₁ adj₂ α β a :=
  mateEquiv_homEquiv_action_actual adj₁ adj₂ adj₁' adj₂' h₁ h₂ α β hβ a

/-- Normalized action retains the actual exchange and the actual adjunctions. -/
theorem mateEquiv_normalized_hom_action_actual
    (adj₁' : L₁ ⊣ R₁) (adj₂' : L₂ ⊣ R₂)
    (h₁ : adj₁ = adj₁') (h₂ : adj₂ = adj₂')
    (α : TwoSquare G L₁ L₂ H) (β : R₁ ⋙ G ⟶ H ⋙ R₂)
    (hβ : β = (mateEquiv adj₁' adj₂' α).natTrans)
    {A : C} {B : E} {Z K : D} {Z' : F}
    (c : L₁.obj A ≅ Z) (d : G.obj A ≅ B)
    (e : L₂.obj B ≅ Z') (t : H.obj Z ≅ Z')
    (hc : α.app A ≫ H.map c.hom ≫ t.hom = L₂.map d.hom ≫ e.hom)
    (a : Z ⟶ K) :
    e.inv ≫ L₂.map d.inv ≫
        (adj₂.homEquiv (G.obj A) (H.obj K)).symm
          (G.map (adj₁.homEquiv A K (c.hom ≫ a)) ≫ β.app K) =
      t.inv ≫ H.map a := by
  subst adj₁'
  subst adj₂'
  subst β
  exact mateEquiv_normalized_hom_action adj₁ adj₂ α c d e t hc a

/-- Literal source-comparison square, independent of any chosen mate. -/
def ConstantSourceSquareEquation
    (α : G ⋙ L₂ ⟶ L₁ ⋙ H) {A : C} {B : E} {Z : D} {Z' : F}
    (c : L₁.obj A ≅ Z) (d : G.obj A ≅ B)
    (e : L₂.obj B ≅ Z') (t : H.obj Z ≅ Z') : Prop :=
  α.app A ≫ H.map c.hom ≫ t.hom = L₂.map d.hom ≫ e.hom

/-- Literal normalized mate action with supplied actual representative and target map. -/
def NormalizedMateHomActionEquation
    (β : R₁ ⋙ G ⟶ H ⋙ R₂) {A : C} {B : E} {K : D} {Z' W : F}
    (d : G.obj A ≅ B) (e : L₂.obj B ≅ Z')
    (r : L₁.obj A ⟶ K) (p : H.obj K ⟶ W) (b : Z' ⟶ W) : Prop :=
  e.inv ≫ L₂.map d.inv ≫
    (adj₂.homEquiv (G.obj A) (H.obj K)).symm
      (G.map (adj₁.homEquiv A K r) ≫ β.app K) ≫ p = b

/-- Normalize the actual mate using canonical representative and target equations.
Substitution takes place only in abstract categories. -/
theorem normalizedMateHomActionEquation_actual
    (adj₁' : L₁ ⊣ R₁) (adj₂' : L₂ ⊣ R₂)
    (h₁ : adj₁ = adj₁') (h₂ : adj₂ = adj₂')
    (α : TwoSquare G L₁ L₂ H) (β : R₁ ⋙ G ⟶ H ⋙ R₂)
    (hβ : β = (mateEquiv adj₁' adj₂' α).natTrans)
    {A : C} {B : E} {Z K : D} {Z' W : F}
    (c : L₁.obj A ≅ Z) (d : G.obj A ≅ B)
    (e : L₂.obj B ≅ Z') (t : H.obj Z ≅ Z')
    (hc : ConstantSourceSquareEquation α.natTrans c d e t)
    (a : Z ⟶ K) (r : L₁.obj A ⟶ K) (hr : r = c.hom ≫ a)
    (p : H.obj K ⟶ W) (b : Z' ⟶ W)
    (hb : t.inv ≫ H.map a ≫ p = b) :
    NormalizedMateHomActionEquation adj₁ adj₂ β d e r p b := by
  subst r
  have hc' : α.app A ≫ H.map c.hom ≫ t.hom = L₂.map d.hom ≫ e.hom := hc
  have hm := mateEquiv_normalized_hom_action_actual adj₁ adj₂
    adj₁' adj₂' h₁ h₂ α β hβ c d e t hc' a
  have hp := congrArg (fun k => k ≫ p) hm
  dsimp only [NormalizedMateHomActionEquation]
  simpa only [Category.assoc, hb] using hp

/-- Transport only the named target of the literal normalized-action equation. -/
theorem normalizedMateHomActionEquation_congr_target
    (β : R₁ ⋙ G ⟶ H ⋙ R₂) {A : C} {B : E} {K : D} {Z' W : F}
    (d : G.obj A ≅ B) (e : L₂.obj B ≅ Z')
    (r : L₁.obj A ⟶ K) (p : H.obj K ⟶ W) (b b' : Z' ⟶ W)
    (hb : b = b') (he : NormalizedMateHomActionEquation adj₁ adj₂ β d e r p b) :
    NormalizedMateHomActionEquation adj₁ adj₂ β d e r p b' := by
  subst b'
  exact he


end HomAction
section NativeConstants

universe uA vA wA uB vB wB wC wD
variable {A : Type uA} [Category.{vA} A] [Abelian A]
  {B : Type uB} [Category.{vB} B] [Abelian B]
  {C : Type uC} [Category.{vC} C] [Abelian C]
  {D : Type uD} [Category.{vD} D] [Abelian D]
  [HasDerivedCategory.{wA} A] [EnoughInjectives A]
  [HasDerivedCategory.{wB} B] [EnoughInjectives B]
  [HasDerivedCategory.{wC} C] [EnoughInjectives C]
  [HasDerivedCategory.{wD} D]
  (F : A ⥤ B) (H : B ⥤ D) (G : A ⥤ C) (V : C ⥤ D)
  [F.Additive] [H.Additive] [G.Additive] [V.Additive]
  [F.PreservesHomology] [H.PreservesHomology] [G.PreservesHomology] [V.PreservesHomology]
  (αD : G.rightDerivedFunctorPlus ⋙ V.rightDerivedFunctorPlus ⟶
    F.rightDerivedFunctorPlus ⋙ H.rightDerivedFunctorPlus)
  {T : A} {ZB : B} {ZC : C} {ZD : D}
  (cD : F.rightDerivedFunctorPlus.obj ((DerivedCategory.Plus.singleFunctor A 0).obj T) ≅
    (DerivedCategory.Plus.singleFunctor B 0).obj ZB)
  (dD : G.rightDerivedFunctorPlus.obj ((DerivedCategory.Plus.singleFunctor A 0).obj T) ≅
    (DerivedCategory.Plus.singleFunctor C 0).obj ZC)
  (eD : V.rightDerivedFunctorPlus.obj ((DerivedCategory.Plus.singleFunctor C 0).obj ZC) ≅
    (DerivedCategory.Plus.singleFunctor D 0).obj ZD)
  (tD : H.rightDerivedFunctorPlus.obj ((DerivedCategory.Plus.singleFunctor B 0).obj ZB) ≅
    (DerivedCategory.Plus.singleFunctor D 0).obj ZD)

omit [F.PreservesHomology] [H.PreservesHomology]
    [G.PreservesHomology] [V.PreservesHomology] in
/-- Convert the native constant-square proposition before any concrete scheme
functors or original H¹ representatives enter the mate-normalization proof. -/
theorem constantSourceSquareEquation_of_derivedConstant
    (h : DerivedConstantSquareEquation F H G V αD cD dD eD tD) :
    ConstantSourceSquareEquation αD cD dD eD tD := h

end NativeConstants

end CategoryTheory
