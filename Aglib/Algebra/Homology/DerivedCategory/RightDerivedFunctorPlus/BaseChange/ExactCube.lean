/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import
  Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.BaseChange.ExactSquare

/-!
# Exact comparison transports horizontal cubes

A commuting cube of exact additive functors induces the same cube for their
installed bounded-below right-derived functors. The six supplied derived faces
are retained literally; their exact-comparison equations identify the cube on
actual complexes, and localization extends the equality to every object.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

namespace CategoryTheory

open CategoryTheory.Functor
open scoped TwoSquare

universe uA vA wA uB vB wB uC vC wC uD vD wD uE vE wE
  uA' vA' wA' uB' vB' wB' uC' vC' wC' uD' vD' wD'

section TripleComparison

variable {A : Type uA} [Category.{vA} A] [Abelian A] [HasDerivedCategory.{wA} A]
  [EnoughInjectives A]
  {B : Type uB} [Category.{vB} B] [Abelian B] [HasDerivedCategory.{wB} B]
  [EnoughInjectives B]
  {C : Type uC} [Category.{vC} C] [Abelian C] [HasDerivedCategory.{wC} C]
  [EnoughInjectives C]
  {D : Type uD} [Category.{vD} D] [Abelian D] [HasDerivedCategory.{wD} D]
  (F : A ⥤ B) (G : B ⥤ C) (H : C ⥤ D)
  [F.Additive] [G.Additive] [H.Additive]
  [F.PreservesHomology] [G.PreservesHomology] [H.PreservesHomology]

private def exactComparisonTriple (Z : CochainComplex.Plus A) :
    H.rightDerivedFunctorPlus.obj
        (G.rightDerivedFunctorPlus.obj
          (F.rightDerivedFunctorPlus.obj (DerivedCategory.Plus.Q.obj Z))) ⟶
      DerivedCategory.Plus.Q.obj
        (H.mapCochainComplexPlus.obj
          (G.mapCochainComplexPlus.obj (F.mapCochainComplexPlus.obj Z))) :=
  H.rightDerivedFunctorPlus.map
      (G.rightDerivedFunctorPlus.map (F.rightDerivedFunctorPlusExactComparison.hom.app Z) ≫
        G.rightDerivedFunctorPlusExactComparison.hom.app (F.mapCochainComplexPlus.obj Z)) ≫
    H.rightDerivedFunctorPlusExactComparison.hom.app
      (G.mapCochainComplexPlus.obj (F.mapCochainComplexPlus.obj Z))

private instance exactComparisonTriple_isIso (Z : CochainComplex.Plus A) :
    IsIso (exactComparisonTriple F G H Z) := by
  unfold exactComparisonTriple
  infer_instance

end TripleComparison

section Whiskering

variable {A : Type uA} [Category.{vA} A] [Abelian A] [HasDerivedCategory.{wA} A]
  [EnoughInjectives A]
  {B : Type uB} [Category.{vB} B] [Abelian B] [HasDerivedCategory.{wB} B]
  [EnoughInjectives B]
  {C : Type uC} [Category.{vC} C] [Abelian C] [HasDerivedCategory.{wC} C]
  [EnoughInjectives C]
  {D : Type uD} [Category.{vD} D] [Abelian D] [HasDerivedCategory.{wD} D]
  {E : Type uE} [Category.{vE} E] [Abelian E] [HasDerivedCategory.{wE} E]
  {F : A ⥤ B} {H : B ⥤ D} {G : A ⥤ C} {V : C ⥤ D}
  [F.Additive] [H.Additive] [G.Additive] [V.Additive]
  [F.PreservesHomology] [H.PreservesHomology]
  [G.PreservesHomology] [V.PreservesHomology]
  (α : TwoSquare G F V H)
  (αD : TwoSquare G.rightDerivedFunctorPlus F.rightDerivedFunctorPlus
    V.rightDerivedFunctorPlus H.rightDerivedFunctorPlus)

private theorem exactComparisonTriple_post [EnoughInjectives D]
    (hα : ∀ Z, ExactComparisonSquareEquation F H G V α αD Z)
    (J : D ⥤ E) [J.Additive] [J.PreservesHomology] (Z : CochainComplex.Plus A) :
    J.rightDerivedFunctorPlus.map (αD.app (DerivedCategory.Plus.Q.obj Z)) ≫
        exactComparisonTriple F H J Z =
      exactComparisonTriple G V J Z ≫
        DerivedCategory.Plus.Q.map
          (J.mapCochainComplexPlus.map (α.mapCochainComplexPlus.app Z)) := by
  have h : (V.rightDerivedFunctorPlus.map
        (G.rightDerivedFunctorPlusExactComparison.hom.app Z) ≫
      V.rightDerivedFunctorPlusExactComparison.hom.app (G.mapCochainComplexPlus.obj Z)) ≫
        DerivedCategory.Plus.Q.map (α.mapCochainComplexPlus.app Z) =
      αD.app (DerivedCategory.Plus.Q.obj Z) ≫
        (H.rightDerivedFunctorPlus.map (F.rightDerivedFunctorPlusExactComparison.hom.app Z) ≫
          H.rightDerivedFunctorPlusExactComparison.hom.app
            (F.mapCochainComplexPlus.obj Z)) := by
    simpa only [ExactComparisonSquareEquation, Category.assoc] using hα Z
  unfold exactComparisonTriple
  rw [← Category.assoc, ← Functor.map_comp, ← h, Functor.map_comp]
  simp only [Category.assoc]
  exact congrArg (fun k ↦ J.rightDerivedFunctorPlus.map
      (V.rightDerivedFunctorPlus.map (G.rightDerivedFunctorPlusExactComparison.hom.app Z) ≫
        V.rightDerivedFunctorPlusExactComparison.hom.app (G.mapCochainComplexPlus.obj Z)) ≫ k)
    (J.rightDerivedFunctorPlusExactComparison.hom.naturality
      (α.mapCochainComplexPlus.app Z))

private theorem exactComparisonTriple_pre [EnoughInjectives E]
    (hα : ∀ Z, ExactComparisonSquareEquation F H G V α αD Z)
    (J : E ⥤ A) [J.Additive] [J.PreservesHomology] (Z : CochainComplex.Plus E) :
    αD.app (J.rightDerivedFunctorPlus.obj (DerivedCategory.Plus.Q.obj Z)) ≫
        exactComparisonTriple J F H Z =
      exactComparisonTriple J G V Z ≫
        DerivedCategory.Plus.Q.map
          (α.mapCochainComplexPlus.app (J.mapCochainComplexPlus.obj Z)) := by
  have hn := αD.naturality (J.rightDerivedFunctorPlusExactComparison.hom.app Z)
  change V.rightDerivedFunctorPlus.map
      (G.rightDerivedFunctorPlus.map (J.rightDerivedFunctorPlusExactComparison.hom.app Z)) ≫
        αD.app (DerivedCategory.Plus.Q.obj (J.mapCochainComplexPlus.obj Z)) =
      αD.app (J.rightDerivedFunctorPlus.obj (DerivedCategory.Plus.Q.obj Z)) ≫
        H.rightDerivedFunctorPlus.map
          (F.rightDerivedFunctorPlus.map (J.rightDerivedFunctorPlusExactComparison.hom.app Z))
    at hn
  have h := hα (J.mapCochainComplexPlus.obj Z)
  unfold ExactComparisonSquareEquation at h
  unfold exactComparisonTriple
  simp only [Functor.map_comp, Category.assoc]
  rw [← reassoc_of% hn, ← h]

end Whiskering

section Cube

variable {A : Type uA} [Category.{vA} A] [Abelian A] [HasDerivedCategory.{wA} A]
  [EnoughInjectives A]
  {B : Type uB} [Category.{vB} B] [Abelian B] [HasDerivedCategory.{wB} B]
  [EnoughInjectives B]
  {C : Type uC} [Category.{vC} C] [Abelian C] [HasDerivedCategory.{wC} C]
  [EnoughInjectives C]
  {D : Type uD} [Category.{vD} D] [Abelian D] [HasDerivedCategory.{wD} D]
  [EnoughInjectives D]
  {A' : Type uA'} [Category.{vA'} A'] [Abelian A'] [HasDerivedCategory.{wA'} A']
  [EnoughInjectives A']
  {B' : Type uB'} [Category.{vB'} B'] [Abelian B'] [HasDerivedCategory.{wB'} B']
  [EnoughInjectives B']
  {C' : Type uC'} [Category.{vC'} C'] [Abelian C'] [HasDerivedCategory.{wC'} C']
  [EnoughInjectives C']
  {D' : Type uD'} [Category.{vD'} D'] [Abelian D'] [HasDerivedCategory.{wD'} D']
  {L₁ : A ⥤ B} {L₂ : C ⥤ D} {L₁' : A' ⥤ B'} {L₂' : C' ⥤ D'}
  {G : A ⥤ C} {H : B ⥤ D} {G' : A' ⥤ C'} {H' : B' ⥤ D'}
  {QA : A ⥤ A'} {QB : B ⥤ B'} {QC : C ⥤ C'} {QD : D ⥤ D'}
  [L₁.Additive] [L₂.Additive] [L₁'.Additive] [L₂'.Additive]
  [G.Additive] [H.Additive] [G'.Additive] [H'.Additive]
  [QA.Additive] [QB.Additive] [QC.Additive] [QD.Additive]
  [L₁.PreservesHomology] [L₂.PreservesHomology]
  [L₁'.PreservesHomology] [L₂'.PreservesHomology]
  [G.PreservesHomology] [H.PreservesHomology]
  [G'.PreservesHomology] [H'.PreservesHomology]
  [QA.PreservesHomology] [QB.PreservesHomology]
  [QC.PreservesHomology] [QD.PreservesHomology]

/-- Six literal exact-comparison squares transport an original horizontal cube to
the same supplied squares of installed bounded-below right-derived functors. -/
theorem rightDerivedFunctorPlus_exactHorizontalCube
    (s₁ : TwoSquare QA L₁ L₁' QB) (s₂ : TwoSquare QC L₂ L₂' QD)
    (α : TwoSquare G L₁ L₂ H) (α' : TwoSquare G' L₁' L₂' H')
    (γ : TwoSquare QA G G' QC) (δ : TwoSquare QB H H' QD)
    (s₁D : TwoSquare QA.rightDerivedFunctorPlus L₁.rightDerivedFunctorPlus
      L₁'.rightDerivedFunctorPlus QB.rightDerivedFunctorPlus)
    (s₂D : TwoSquare QC.rightDerivedFunctorPlus L₂.rightDerivedFunctorPlus
      L₂'.rightDerivedFunctorPlus QD.rightDerivedFunctorPlus)
    (αD : TwoSquare G.rightDerivedFunctorPlus L₁.rightDerivedFunctorPlus
      L₂.rightDerivedFunctorPlus H.rightDerivedFunctorPlus)
    (α'D : TwoSquare G'.rightDerivedFunctorPlus L₁'.rightDerivedFunctorPlus
      L₂'.rightDerivedFunctorPlus H'.rightDerivedFunctorPlus)
    (γD : TwoSquare QA.rightDerivedFunctorPlus G.rightDerivedFunctorPlus
      G'.rightDerivedFunctorPlus QC.rightDerivedFunctorPlus)
    (δD : TwoSquare QB.rightDerivedFunctorPlus H.rightDerivedFunctorPlus
      H'.rightDerivedFunctorPlus QD.rightDerivedFunctorPlus)
    (hs₁ : ∀ Z, ExactComparisonSquareEquation L₁ QB QA L₁' s₁ s₁D Z)
    (hs₂ : ∀ Z, ExactComparisonSquareEquation L₂ QD QC L₂' s₂ s₂D Z)
    (hα : ∀ Z, ExactComparisonSquareEquation L₁ H G L₂ α αD Z)
    (hα' : ∀ Z, ExactComparisonSquareEquation L₁' H' G' L₂' α' α'D Z)
    (hγ : ∀ Z, ExactComparisonSquareEquation G QC QA G' γ γD Z)
    (hδ : ∀ Z, ExactComparisonSquareEquation H QD QB H' δ δD Z)
    (h : ∀ X, L₂'.map (γ.app X) ≫ (α ≫ₕ s₂).app X =
      (s₁ ≫ₕ α').app X ≫ δ.app (L₁.obj X))
    (K : DerivedCategory.Plus A) :
    L₂'.rightDerivedFunctorPlus.map (γD.app K) ≫ (αD ≫ₕ s₂D).app K =
      (s₁D ≫ₕ α'D).app K ≫ δD.app (L₁.rightDerivedFunctorPlus.obj K) := by
  have hQ (Z : CochainComplex.Plus A) :
      L₂'.rightDerivedFunctorPlus.map (γD.app (DerivedCategory.Plus.Q.obj Z)) ≫
          (αD ≫ₕ s₂D).app (DerivedCategory.Plus.Q.obj Z) =
        (s₁D ≫ₕ α'D).app (DerivedCategory.Plus.Q.obj Z) ≫
          δD.app (L₁.rightDerivedFunctorPlus.obj (DerivedCategory.Plus.Q.obj Z)) := by
    have hC :
        L₂'.mapCochainComplexPlus.map (γ.mapCochainComplexPlus.app Z) ≫
            s₂.mapCochainComplexPlus.app (G.mapCochainComplexPlus.obj Z) ≫
            QD.mapCochainComplexPlus.map (α.mapCochainComplexPlus.app Z) =
          α'.mapCochainComplexPlus.app (QA.mapCochainComplexPlus.obj Z) ≫
            H'.mapCochainComplexPlus.map (s₁.mapCochainComplexPlus.app Z) ≫
            δ.mapCochainComplexPlus.app (L₁.mapCochainComplexPlus.obj Z) := by
      apply ObjectProperty.hom_ext
      ext n
      change L₂'.map (𝟙 _ ≫ γ.app (Z.obj.X n) ≫ 𝟙 _) ≫
          (𝟙 _ ≫ s₂.app (G.obj (Z.obj.X n)) ≫ 𝟙 _) ≫
          QD.map (𝟙 _ ≫ α.app (Z.obj.X n) ≫ 𝟙 _) =
        (𝟙 _ ≫ α'.app (QA.obj (Z.obj.X n)) ≫ 𝟙 _) ≫
          H'.map (𝟙 _ ≫ s₁.app (Z.obj.X n) ≫ 𝟙 _) ≫
          (𝟙 _ ≫ δ.app (L₁.obj (Z.obj.X n)) ≫ 𝟙 _)
      simpa only [TwoSquare.hComp_app, Category.id_comp, Category.comp_id,
        Category.assoc] using h (Z.obj.X n)
    have h₁ := exactComparisonTriple_post γ γD hγ L₂' Z
    have h₂ := exactComparisonTriple_pre s₂ s₂D hs₂ G Z
    have h₃ := exactComparisonTriple_post α αD hα QD Z
    have h₄ := exactComparisonTriple_pre α' α'D hα' QA Z
    have h₅ := exactComparisonTriple_post s₁ s₁D hs₁ H' Z
    have h₆ := exactComparisonTriple_pre δ δD hδ L₁ Z
    apply (cancel_mono (exactComparisonTriple L₁ H QD Z)).mp
    simp only [TwoSquare.hComp_app, Category.assoc]
    rw [h₃, reassoc_of% h₂, reassoc_of% h₁,
      h₆, reassoc_of% h₅, reassoc_of% h₄]
    simp only [← Functor.map_comp]
    rw [hC]
  have he :
      whiskerRight γD.natTrans L₂'.rightDerivedFunctorPlus ≫ (αD ≫ₕ s₂D).natTrans =
        (s₁D ≫ₕ α'D).natTrans ≫ whiskerLeft L₁.rightDerivedFunctorPlus δD.natTrans := by
    apply Localization.natTrans_ext DerivedCategory.Plus.Q (CochainComplex.Plus.quasiIso A)
    intro Z
    simpa only [NatTrans.comp_app, Functor.whiskerLeft_app,
      Functor.whiskerRight_app] using hQ Z
  simpa only [NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app] using congr_app he K

end Cube

end CategoryTheory
