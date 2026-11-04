/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.Adjunction.SingleAdjunct
public import Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.BaseChange.ActualZeroComparison
public import Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.SingleUnit.ShortExact
public import Aglib.Algebra.Homology.DerivedCategory.Plus.ExtTransport
public import Aglib.CategoryTheory.Adjunction.UnderlyingHomEquiv
public import Aglib.CategoryTheory.Shift.AdjunctValue

/-! Original normalized adjuncts through the original single-unit exchange. -/

@[expose] public noncomputable section

open CategoryTheory

namespace CategoryTheory

variable {A B C D : Type*} [Category* A] [Category* B] [Category* C] [Category* D]
  {L₁ : A ⥤ B} {R₁ : B ⥤ A} {L₂ : C ⥤ D} {R₂ : D ⥤ C}
  {U : A ⥤ C} {V : B ⥤ D}

/-- The original mate preserves the adjunct of the original transported unit. -/
private theorem unitAdjunct_of_mate_of_unitSquare (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂)
    (s : TwoSquare U L₁ L₂ V) (d : R₁ ⋙ U ⟶ V ⋙ R₂)
    (hd : (mateEquiv adj₁ adj₂ s).natTrans = d)
    {I : A} {J : B} {I' : C} {J' : D}
    (e : L₁.obj I ≅ J) (e' : L₂.obj I' ≅ J')
    (u : U.obj I ≅ I') (v : V.obj J ≅ J')
    (h : s.app I ≫ V.map e.hom ≫ v.hom = L₂.map u.hom ≫ e'.hom) :
    u.inv ≫ U.map (adj₁.homEquiv I J e.hom) ≫ d.app J ≫ R₂.map v.hom =
      adj₂.homEquiv I' J' e'.hom := by
  have hs := underlying_homEquiv_of_mate adj₁ adj₂ s d hd I J e.hom
  have hh : L₂.map u.inv ≫ s.app I ≫ V.map e.hom ≫ v.hom = e'.hom := by
    rw [h, ← L₂.map_comp_assoc, u.inv_hom_id, L₂.map_id, Category.id_comp]
  calc
    _ = u.inv ≫ adj₂.homEquiv (U.obj I) (V.obj J) (s.app I ≫ V.map e.hom) ≫ R₂.map v.hom := by
      rw [← Category.assoc (U.map (adj₁.homEquiv I J e.hom)), hs]
    _ = u.inv ≫ adj₂.homEquiv (U.obj I) J' ((s.app I ≫ V.map e.hom) ≫ v.hom) :=
      congrArg (fun z => u.inv ≫ z)
        (adj₂.homEquiv_naturality_right (s.app I ≫ V.map e.hom) v.hom).symm
    _ = adj₂.homEquiv I' J' (L₂.map u.inv ≫ s.app I ≫ V.map e.hom ≫ v.hom) := by
      rw [adj₂.homEquiv_naturality_left]
      simp only [Category.assoc]
    _ = _ := by rw [hh]

end CategoryTheory

namespace CategoryTheory

variable {A B C D : Type*} [Category* A] [Category* B] [Category* C] [Category* D]
  [Abelian A] [Abelian B] [Abelian C] [Abelian D]
  [HasDerivedCategory A] [HasDerivedCategory B] [HasDerivedCategory C] [HasDerivedCategory D]
  [EnoughInjectives A] [EnoughInjectives B] [EnoughInjectives C] [EnoughInjectives D]
  {L₁ : A ⥤ B} {R₁ : B ⥤ A} {L₂ : C ⥤ D} {R₂ : D ⥤ C}
  {G : A ⥤ C} {H : B ⥤ D}
  [L₁.Additive] [R₁.Additive] [L₂.Additive] [R₂.Additive] [G.Additive] [H.Additive]
  [L₁.PreservesHomology] [L₂.PreservesHomology] [G.PreservesHomology] [H.PreservesHomology]

/-- The original single-unit exchange retains the normalized underived adjunct
after applying the original derived adjunction. -/
theorem derivedUnitAdjunct_of_originalSingleExchange (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂)
    (s : TwoSquare G L₁ L₂ H)
    (β : R₁.rightDerivedFunctorPlus ⋙ G.rightDerivedFunctorPlus ⟶
      H.rightDerivedFunctorPlus ⋙ R₂.rightDerivedFunctorPlus)
    (hβ : ∀ K, Functor.ActualDerivedUnitEquation R₁ R₂ G H
      (mateEquiv adj₁ adj₂ s).natTrans β K)
    {I : A} {J : B} {I' : C} {J' : D}
    (e : L₁.obj I ≅ J) (e' : L₂.obj I' ≅ J')
    (u : G.obj I ≅ I') (v : H.obj J ≅ J')
    (hs : s.app I ≫ H.map e.hom ≫ v.hom = L₂.map u.hom ≫ e'.hom) :
    let eD := L₁.rightDerivedFunctorPlusSingleIsoOfIso 0 e
    let eD' := L₂.rightDerivedFunctorPlusSingleIsoOfIso 0 e'
    let uD := G.rightDerivedFunctorPlusSingleIsoOfIso 0 u
    let vD := H.rightDerivedFunctorPlusSingleIsoOfIso 0 v
    UnitAdjunctValue adj₁.rightDerivedFunctorPlus adj₂.rightDerivedFunctorPlus β eD eD' uD vD := by
  intro eD eD' uD vD
  dsimp only [UnitAdjunctValue]
  let I₀ := (DerivedCategory.Plus.singleFunctor A 0).obj I
  let J₀ := (DerivedCategory.Plus.singleFunctor B 0).obj J
  let I₀' := (DerivedCategory.Plus.singleFunctor C 0).obj I'
  let J₀' := (DerivedCategory.Plus.singleFunctor D 0).obj J'
  let S₁ := DerivedCategory.Plus.singleFunctor A 0
  let S₂ := DerivedCategory.Plus.singleFunctor C 0
  let T₂ := DerivedCategory.Plus.singleFunctor D 0
  let a := adj₁.homEquiv I J e.hom
  let a' := adj₂.homEquiv I' J' e'.hom
  let G' := G.rightDerivedFunctorPlus
  let R' := R₂.rightDerivedFunctorPlus
  let g := G.rightDerivedFunctorPlusSingleIso 0
  let h := H.rightDerivedFunctorPlusSingleIso 0
  let c := (mateEquiv adj₁ adj₂ s).natTrans.app J
  have h₁ : adj₁.rightDerivedFunctorPlus.homEquiv I₀ J₀ eD.hom =
      S₁.map a ≫ R₁.rightDerivedSingleUnit J :=
    adj₁.rightDerivedFunctorPlus_homEquiv_single e.hom
  have h₂ : adj₂.rightDerivedFunctorPlus.homEquiv I₀' J₀' eD'.hom =
      S₂.map a' ≫ R₂.rightDerivedSingleUnit J' :=
    adj₂.rightDerivedFunctorPlus_homEquiv_single e'.hom
  have hv : vD.hom = h.hom.app J ≫ T₂.map v.hom := rfl
  have hU : uD.inv ≫ G'.map (S₁.map a) ≫ g.hom.app (R₁.obj J) =
      S₂.map (u.inv ≫ G.map a) := by
    have hn : G'.map (S₁.map a) ≫ g.hom.app (R₁.obj J) = g.hom.app I ≫ S₂.map (G.map a) :=
      g.hom.naturality a
    change (S₂.map u.inv ≫ g.inv.app I) ≫ G'.map (S₁.map a) ≫ g.hom.app (R₁.obj J) = _
    rw [Category.assoc, hn, Iso.inv_hom_id_app_assoc, S₂.map_comp]
  have hS : G'.map (R₁.rightDerivedSingleUnit J) ≫ β.app J₀ ≫ R'.map (h.hom.app J) =
      g.hom.app (R₁.obj J) ≫ S₂.map c ≫ R₂.rightDerivedSingleUnit (H.obj J) :=
    Functor.singleUnit_square_of_complexUnit R₁ R₂ G H (mateEquiv adj₁ adj₂ s).natTrans β J hβ
  have hn : R₂.rightDerivedSingleUnit (H.obj J) ≫ R'.map (T₂.map v.hom) =
      S₂.map (R₂.map v.hom) ≫ R₂.rightDerivedSingleUnit J' :=
    (R₂.rightDerivedSingleUnit_naturality v.hom).symm
  have ho : u.inv ≫ G.map a ≫ c ≫ R₂.map v.hom = a' :=
    unitAdjunct_of_mate_of_unitSquare adj₁ adj₂ s (mateEquiv adj₁ adj₂ s).natTrans
      rfl e e' u v hs
  rw [h₁, h₂, hv, G'.map_comp, R'.map_comp]
  simp only [Category.assoc]
  rw [reassoc_of% hS, reassoc_of% hU, hn]
  change S₂.map (u.inv ≫ G.map a) ≫ S₂.map c ≫ S₂.map (R₂.map v.hom) ≫
    R₂.rightDerivedSingleUnit J' = S₂.map a' ≫ R₂.rightDerivedSingleUnit J'
  have hm : S₂.map (u.inv ≫ G.map a) ≫ S₂.map c ≫ S₂.map (R₂.map v.hom) = S₂.map a' := by
    rw [← S₂.map_comp, ← S₂.map_comp, Category.assoc, ho]
  exact (reassoc_of% hm) (R₂.rightDerivedSingleUnit J')

end CategoryTheory
