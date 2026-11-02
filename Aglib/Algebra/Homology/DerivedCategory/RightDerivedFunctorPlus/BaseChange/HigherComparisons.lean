/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.SingleHomology
public import Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.BaseChange.HigherWholePasting

/-!
# Native source and target comparisons for higher exchange

The source uses the original higher-image and exact-homology comparisons.
The target uses the original exact-single and higher-image comparisons. The
whole NatIso constructors retain their native factor order before specialization.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Functor

universe u₁ v₁ w₁ u₂ v₂ w₂ u₃ v₃ w₃

variable {A : Type u₁} [Category.{v₁} A] [Abelian A] [HasDerivedCategory.{w₁} A]
  [EnoughInjectives A]
  {B : Type u₂} [Category.{v₂} B] [Abelian B] [HasDerivedCategory.{w₂} B]
  [EnoughInjectives B]
  {C : Type u₃} [Category.{v₃} C] [Abelian C] [HasDerivedCategory.{w₃} C]

/-- The native comparison from an ordinary higher image followed by an exact functor. -/
def higherExchangeSourceIso (R : A ⥤ B) (G : B ⥤ C)
    [R.Additive] [G.Additive] [G.PreservesHomology] (q : ℕ) :
    R.rightDerived q ⋙ G ≅ DerivedCategory.Plus.singleFunctor A 0 ⋙
      (R.rightDerivedFunctorPlus ⋙ G.rightDerivedFunctorPlus) ⋙
        DerivedCategory.Plus.homologyFunctor C (q : ℤ) :=
  isoWhiskerRight (R.rightDerivedSingleHomologyIso q) G ≪≫
    associator _ _ _ ≪≫
    isoWhiskerLeft _ (associator _ _ _) ≪≫
    isoWhiskerLeft _ (isoWhiskerLeft _
      (G.rightDerivedFunctorPlusHomologyIso (q : ℤ)).symm) ≪≫
    isoWhiskerLeft _ (associator _ _ _).symm

/-- The native source component retains the original higher-image and homology factors. -/
theorem higherExchangeSourceIso_hom_app (R : A ⥤ B) (G : B ⥤ C)
    [R.Additive] [G.Additive] [G.PreservesHomology] (q : ℕ) (M : A) :
    (higherExchangeSourceIso R G q).hom.app M =
      G.map ((R.rightDerivedSingleHomologyIso q).hom.app M) ≫
        (G.rightDerivedFunctorPlusHomologyIso (q : ℤ)).inv.app
          (R.rightDerivedFunctorPlus.obj ((DerivedCategory.Plus.singleFunctor A 0).obj M)) := by
  simp only [higherExchangeSourceIso, Iso.trans_hom, Iso.symm_hom,
    NatTrans.comp_app, isoWhiskerRight_hom, isoWhiskerLeft_hom,
    whiskerRight_app, whiskerLeft_app, associator_hom_app, associator_inv_app,
    Category.id_comp]
  change G.map ((R.rightDerivedSingleHomologyIso q).hom.app M) ≫
    (𝟙 _ ≫ ((G.rightDerivedFunctorPlusHomologyIso (q : ℤ)).inv.app
      (R.rightDerivedFunctorPlus.obj ((DerivedCategory.Plus.singleFunctor A 0).obj M)) ≫
        𝟙 _)) = _
  rw [Category.id_comp, Category.comp_id]

/-- The native comparison from exact inverse image followed by a derived image to ordinary Rq. -/
def higherExchangeTargetIso (H : A ⥤ B) (R : B ⥤ C)
    [H.Additive] [R.Additive] [H.PreservesHomology] (q : ℕ) :
    DerivedCategory.Plus.singleFunctor A 0 ⋙
      (H.rightDerivedFunctorPlus ⋙ R.rightDerivedFunctorPlus) ⋙
        DerivedCategory.Plus.homologyFunctor C (q : ℤ) ≅ H ⋙ R.rightDerived q :=
  isoWhiskerLeft _ (associator _ _ _) ≪≫
    (associator _ _ _).symm ≪≫
    isoWhiskerRight (H.rightDerivedFunctorPlusSingleIso 0) _ ≪≫
    associator _ _ _ ≪≫
    isoWhiskerLeft _ (R.rightDerivedSingleHomologyIso q).symm

/-- The native target component retains the original exact-single and higher-image factors. -/
theorem higherExchangeTargetIso_hom_app (H : A ⥤ B) (R : B ⥤ C)
    [H.Additive] [R.Additive] [H.PreservesHomology] (q : ℕ) (M : A) :
    (higherExchangeTargetIso H R q).hom.app M =
      (DerivedCategory.Plus.homologyFunctor C (q : ℤ)).map
          (R.rightDerivedFunctorPlus.map ((H.rightDerivedFunctorPlusSingleIso 0).hom.app M)) ≫
        (R.rightDerivedSingleHomologyIso q).inv.app (H.obj M) := by
  simp only [higherExchangeTargetIso, Iso.trans_hom, Iso.symm_hom,
    NatTrans.comp_app, isoWhiskerRight_hom, isoWhiskerLeft_hom,
    whiskerRight_app, whiskerLeft_app, associator_hom_app, associator_inv_app,
    comp_map, Category.id_comp]
  change (𝟙 _) ≫ ((DerivedCategory.Plus.homologyFunctor C (q : ℤ)).map
      (R.rightDerivedFunctorPlus.map ((H.rightDerivedFunctorPlusSingleIso 0).hom.app M)) ≫
        (R.rightDerivedSingleHomologyIso q).inv.app (H.obj M)) = _
  exact Category.id_comp _

/-- The native inverse target component retains the same original factors in reverse order. -/
theorem higherExchangeTargetIso_inv_app (H : A ⥤ B) (R : B ⥤ C)
    [H.Additive] [R.Additive] [H.PreservesHomology] (q : ℕ) (M : A) :
    (higherExchangeTargetIso H R q).inv.app M =
      (R.rightDerivedSingleHomologyIso q).hom.app (H.obj M) ≫
        (DerivedCategory.Plus.homologyFunctor C (q : ℤ)).map
          (R.rightDerivedFunctorPlus.map ((H.rightDerivedFunctorPlusSingleIso 0).inv.app M)) :=
  mapped_target_inverse
    (R.rightDerivedFunctorPlus ⋙ DerivedCategory.Plus.homologyFunctor C (q : ℤ))
    ((H.rightDerivedFunctorPlusSingleIso 0).app M)
    ((R.rightDerivedSingleHomologyIso q).app (H.obj M))
    ((higherExchangeTargetIso H R q).app M)
    (higherExchangeTargetIso_hom_app H R q M)

end CategoryTheory.Functor

namespace CategoryTheory.HigherPastingLadder

section HigherExchange

variable {K₀ K₁ K₂ C₀ C₁ C₂ A₀ A₁ A₂ D₀ D₁ D₂ : Type*}
  [Category* K₀] [Category* K₁] [Category* K₂]
  [Category* C₀] [Category* C₁] [Category* C₂]
  [Category* A₀] [Category* A₁] [Category* A₂]
  [Category* D₀] [Category* D₁] [Category* D₂]
  {J₀ : K₀ ⥤ C₀} {J₁ : K₁ ⥤ C₁} {H₁ : D₁ ⥤ A₁} {H₂ : D₂ ⥤ A₂}
  {R₀ : C₀ ⥤ D₀} {R₁ : C₁ ⥤ D₁} {R₂ : C₂ ⥤ D₂}
  {d₁ : D₀ ⥤ D₁} {d₂ : D₁ ⥤ D₂} {d₁₂ : D₀ ⥤ D₂}
  {e₁ : C₀ ⥤ C₁} {e₂ : C₁ ⥤ C₂} {e₁₂ : C₀ ⥤ C₂}
  {G₁ : A₀ ⥤ A₁} {G₂ : A₁ ⥤ A₂} {G₁₂ : A₀ ⥤ A₂}
  {L₁ : K₀ ⥤ K₁} {L₂ : K₁ ⥤ K₂} {L₁₂ : K₀ ⥤ K₂}
  {V₀ : K₀ ⥤ A₀} {V₁ : K₁ ⥤ A₁} {V₂ : K₂ ⥤ A₂}
  (cG : G₁₂ ≅ G₁ ⋙ G₂) (cd : d₁₂ ≅ d₁ ⋙ d₂)
  (cL : L₁₂ ≅ L₁ ⋙ L₂) (ce : e₁₂ ≅ e₁ ⋙ e₂)
  (β₁ : R₀ ⋙ d₁ ⟶ e₁ ⋙ R₁) (β₂ : R₁ ⋙ d₂ ⟶ e₂ ⋙ R₂)
  (β₁₂ : R₀ ⋙ d₁₂ ⟶ e₁₂ ⋙ R₂)
  (b₁ : V₀ ⋙ G₁ ⟶ L₁ ⋙ V₁) (b₂ : V₁ ⋙ G₂ ⟶ L₂ ⋙ V₂)
  (b₁₂ : V₀ ⋙ G₁₂ ⟶ L₁₂ ⋙ V₂)
  (s₁ : V₀ ⋙ G₁ ≅ J₀ ⋙ (R₀ ⋙ d₁) ⋙ H₁)
  (t₁ : J₀ ⋙ (e₁ ⋙ R₁) ⋙ H₁ ≅ L₁ ⋙ V₁)
  (t₂ : J₁ ⋙ (e₂ ⋙ R₂) ⋙ H₂ ≅ L₂ ⋙ V₂)
  (s₁₂ : V₀ ⋙ G₁₂ ≅ J₀ ⋙ (R₀ ⋙ d₁₂) ⋙ H₂)
  (t₁₂ : J₀ ⋙ (e₁₂ ⋙ R₂) ⋙ H₂ ≅ L₁₂ ⋙ V₂)
  (γ : d₂ ⋙ H₂ ≅ H₁ ⋙ G₂) (σ : J₀ ⋙ e₁ ≅ L₁ ⋙ J₁)

/-- The complete native higher-exchange diagram, formed before specializing its functors. -/
def ofHigherExchange : HigherPastingLadder (K₀ ⥤ A₂) where
  A := J₀ ⋙ (R₀ ⋙ d₁₂) ⋙ H₂
  B := J₀ ⋙ (R₀ ⋙ d₁ ⋙ d₂) ⋙ H₂
  C₀ := J₀ ⋙ (e₁ ⋙ R₁ ⋙ d₂) ⋙ H₂
  D := J₀ ⋙ (e₁ ⋙ e₂ ⋙ R₂) ⋙ H₂
  T := J₀ ⋙ (e₁₂ ⋙ R₂) ⋙ H₂
  A' := V₀ ⋙ G₁₂
  B' := (V₀ ⋙ G₁) ⋙ G₂
  C' := (L₁ ⋙ V₁) ⋙ G₂
  D' := L₁ ⋙ L₂ ⋙ V₂
  T' := L₁₂ ⋙ V₂
  a := Functor.whiskerLeft J₀ (Functor.whiskerRight (Functor.whiskerLeft R₀ cd.hom) H₂)
  b := Functor.whiskerLeft J₀ (Functor.whiskerRight (Functor.whiskerRight β₁ d₂) H₂)
  c := Functor.whiskerLeft J₀ (Functor.whiskerRight (Functor.whiskerLeft e₁ β₂) H₂)
  d := Functor.whiskerLeft J₀ (Functor.whiskerRight β₁₂ H₂)
  e := Functor.whiskerLeft J₀ (Functor.whiskerRight (Functor.whiskerRight ce.hom R₂) H₂)
  a' := Functor.whiskerLeft V₀ cG.hom
  b' := Functor.whiskerRight b₁ G₂
  c' := Functor.whiskerLeft L₁ b₂
  d' := b₁₂
  e' := Functor.whiskerRight cL.hom V₂
  iA := s₁₂
  iB := Functor.isoWhiskerRight s₁ G₂ ≪≫
    Functor.isoWhiskerLeft (J₀ ⋙ R₀ ⋙ d₁) γ.symm
  iC := Functor.isoWhiskerRight t₁.symm G₂ ≪≫
    Functor.isoWhiskerLeft (J₀ ⋙ e₁ ⋙ R₁) γ.symm
  iD := Functor.isoWhiskerLeft L₁ t₂.symm ≪≫
    Functor.isoWhiskerRight σ.symm (e₂ ⋙ R₂ ⋙ H₂)
  iT := t₁₂.symm

local notation "Δ" => ofHigherExchange cG cd cL ce β₁ β₂ β₁₂ b₁ b₂ b₁₂
  s₁ t₁ t₂ s₁₂ t₁₂ γ σ

/-- The original pointwise source-composition law gives the whole source facet. -/
theorem ofHigherExchange_source
    (hs : ∀ M, cG.hom.app (V₀.obj M) ≫ G₂.map (s₁.hom.app M) ≫
        γ.inv.app (d₁.obj (R₀.obj (J₀.obj M))) =
      s₁₂.hom.app M ≫ H₂.map (cd.hom.app (R₀.obj (J₀.obj M)))) :
    (Δ).SourceEquation :=
  whole_three_edge_of_app
    (Functor.whiskerLeft V₀ cG.hom) (Functor.whiskerRight s₁.hom G₂)
    (Functor.whiskerLeft (J₀ ⋙ R₀ ⋙ d₁) γ.inv) s₁₂.hom
    (Functor.whiskerLeft J₀ (Functor.whiskerRight (Functor.whiskerLeft R₀ cd.hom) H₂)) hs

/-- The original first exchange and comparison equation give the whole first facet. -/
theorem ofHigherExchange_first
    (hb₁ : b₁ ≫ t₁.inv =
      s₁.hom ≫ Functor.whiskerLeft J₀ (Functor.whiskerRight β₁ H₁)) :
    (Δ).FirstEquation :=
  mapped_horizontal_first_canonical J₀ H₁ H₂ G₂ d₂ γ β₁ s₁ t₁.symm b₁ hb₁

/-- The original outer exchange and comparison equation give the whole outer facet. -/
theorem ofHigherExchange_outer
    (hb₁₂ : b₁₂ ≫ t₁₂.inv =
      s₁₂.hom ≫ Functor.whiskerLeft J₀ (Functor.whiskerRight β₁₂ H₂)) :
    (Δ).OuterEquation := hb₁₂

/-- The original exact-single composition law gives the whole target facet. -/
theorem ofHigherExchange_target
    (ht : ∀ M, V₂.map (cL.hom.app M) ≫ t₂.inv.app (L₁.obj M) ≫
        H₂.map (R₂.map (e₂.map (σ.inv.app M))) =
      t₁₂.inv.app M ≫ H₂.map (R₂.map (ce.hom.app (J₀.obj M)))) :
    (Δ).TargetEquation :=
  whole_three_edge_of_app
    (Functor.whiskerRight cL.hom V₂) (Functor.whiskerLeft L₁ t₂.inv)
    (Functor.whiskerRight σ.inv (e₂ ⋙ R₂ ⋙ H₂)) t₁₂.inv
    (Functor.whiskerLeft J₀ (Functor.whiskerRight (Functor.whiskerRight ce.hom R₂) H₂)) ht

/-- The native target/source factorizations and second exchange give the second facet. -/
theorem ofHigherExchange_second
    (ε : V₁ ≅ J₁ ⋙ R₁ ⋙ H₁)
    (s₂ : V₁ ⋙ G₂ ≅ J₁ ⋙ (R₁ ⋙ d₂) ⋙ H₂)
    (ht₁ : t₁.inv = Functor.whiskerLeft L₁ ε.hom ≫
      Functor.whiskerRight σ.inv (R₁ ⋙ H₁))
    (hs₂ : s₂.hom = Functor.whiskerRight ε.hom G₂ ≫
      Functor.whiskerLeft (J₁ ⋙ R₁) γ.inv)
    (hb₂ : b₂ ≫ t₂.inv = s₂.hom ≫
      Functor.whiskerLeft J₁ (Functor.whiskerRight β₂ H₂)) :
    (Δ).SecondEquation :=
  whole_second_reassociate J₀ e₁ R₁ γ.inv _ _ _
    (mapped_horizontal_second_native J₀ e₁ L₁ J₁ H₁ H₂ G₂ d₂ γ
      R₁ (e₂ ⋙ R₂) β₂ σ.inv t₁.symm ε s₂ ht₁ hs₂ t₂.symm b₂ hb₂)

/-- Homology of the original derived path gives the upper equation of this exact diagram. -/
theorem ofHigherExchange_derived
    (hp : ∀ K, cd.hom.app (R₀.obj K) ≫ d₂.map (β₁.app K) ≫ β₂.app (e₁.obj K) =
      β₁₂.app K ≫ R₂.map (ce.hom.app K)) :
    (Δ).DerivedEquation :=
  whole_mapped_pasting_single J₀ H₂ (Functor.whiskerLeft R₀ cd.hom)
    (Functor.whiskerRight β₁ d₂) (Functor.whiskerLeft e₁ β₂)
    β₁₂ (Functor.whiskerRight ce.hom R₂) hp

/-- The complete native higher diagram satisfies pasting from its original comparison laws. -/
theorem ofHigherExchange_pasting
    (hs : ∀ M, cG.hom.app (V₀.obj M) ≫ G₂.map (s₁.hom.app M) ≫
        γ.inv.app (d₁.obj (R₀.obj (J₀.obj M))) =
      s₁₂.hom.app M ≫ H₂.map (cd.hom.app (R₀.obj (J₀.obj M))))
    (ht : ∀ M, V₂.map (cL.hom.app M) ≫ t₂.inv.app (L₁.obj M) ≫
        H₂.map (R₂.map (e₂.map (σ.inv.app M))) =
      t₁₂.inv.app M ≫ H₂.map (R₂.map (ce.hom.app (J₀.obj M))))
    (ε : V₁ ≅ J₁ ⋙ R₁ ⋙ H₁)
    (s₂ : V₁ ⋙ G₂ ≅ J₁ ⋙ (R₁ ⋙ d₂) ⋙ H₂)
    (ht₁ : t₁.inv = Functor.whiskerLeft L₁ ε.hom ≫
      Functor.whiskerRight σ.inv (R₁ ⋙ H₁))
    (hs₂ : s₂.hom = Functor.whiskerRight ε.hom G₂ ≫
      Functor.whiskerLeft (J₁ ⋙ R₁) γ.inv)
    (hb₁ : b₁ ≫ t₁.inv =
      s₁.hom ≫ Functor.whiskerLeft J₀ (Functor.whiskerRight β₁ H₁))
    (hb₂ : b₂ ≫ t₂.inv = s₂.hom ≫
      Functor.whiskerLeft J₁ (Functor.whiskerRight β₂ H₂))
    (hb₁₂ : b₁₂ ≫ t₁₂.inv =
      s₁₂.hom ≫ Functor.whiskerLeft J₀ (Functor.whiskerRight β₁₂ H₂))
    (hp : ∀ K, cd.hom.app (R₀.obj K) ≫ d₂.map (β₁.app K) ≫ β₂.app (e₁.obj K) =
      β₁₂.app K ≫ R₂.map (ce.hom.app K)) :
    (Δ).HigherEquation :=
  (Δ).pasting
    (ofHigherExchange_source cG cd cL ce β₁ β₂ β₁₂ b₁ b₂ b₁₂ s₁ t₁ t₂ s₁₂ t₁₂ γ σ hs)
    (ofHigherExchange_first cG cd cL ce β₁ β₂ β₁₂ b₁ b₂ b₁₂ s₁ t₁ t₂ s₁₂ t₁₂ γ σ hb₁)
    (ofHigherExchange_second cG cd cL ce β₁ β₂ β₁₂ b₁ b₂ b₁₂ s₁ t₁ t₂ s₁₂ t₁₂ γ σ
      ε s₂ ht₁ hs₂ hb₂)
    (ofHigherExchange_outer cG cd cL ce β₁ β₂ β₁₂ b₁ b₂ b₁₂ s₁ t₁ t₂ s₁₂ t₁₂ γ σ hb₁₂)
    (ofHigherExchange_target cG cd cL ce β₁ β₂ β₁₂ b₁ b₂ b₁₂ s₁ t₁ t₂ s₁₂ t₁₂ γ σ ht)
    (ofHigherExchange_derived cG cd cL ce β₁ β₂ β₁₂ b₁ b₂ b₁₂ s₁ t₁ t₂ s₁₂ t₁₂ γ σ hp)

end HigherExchange

end CategoryTheory.HigherPastingLadder
