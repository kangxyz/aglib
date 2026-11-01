/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.DerivedCategory.UnboundedRightDerived.ExactSquare
public import Mathlib.CategoryTheory.Functor.TwoSquare

/-!
# Exact comparison transports horizontal cubes

A commuting cube of exact additive functors induces the same cube for their
native unbounded localized functors. The six supplied derived faces
are retained literally; their exact-comparison equations identify the cube on
actual complexes, and localization extends the equality to every object.
-/

@[expose] public section

noncomputable section


namespace CategoryTheory

open CategoryTheory.Functor CategoryTheory.Limits
open scoped TwoSquare

universe uA vA wA uB vB wB uC vC wC uD vD wD uE vE wE
  uA' vA' wA' uB' vB' wB' uC' vC' wC' uD' vD' wD'

section SquareEquation

variable {A : Type uA} [Category.{vA} A] [Abelian A] [HasDerivedCategory.{wA} A]
  {B : Type uB} [Category.{vB} B] [Abelian B] [HasDerivedCategory.{wB} B]
  {C : Type uC} [Category.{vC} C] [Abelian C] [HasDerivedCategory.{wC} C]
  {D : Type uD} [Category.{vD} D] [Abelian D] [HasDerivedCategory.{wD} D]
  (F : A ⥤ B) (H : B ⥤ D) (G : A ⥤ C) (V : C ⥤ D)
  [F.Additive] [H.Additive] [G.Additive] [V.Additive]
  [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [PreservesFiniteLimits H] [PreservesFiniteColimits H]
  [PreservesFiniteLimits G] [PreservesFiniteColimits G]
  [PreservesFiniteLimits V] [PreservesFiniteColimits V]

/-- The specified derived face preserves the original all-complex localization factors. -/
def ExactFactorSquareEquation (α : TwoSquare G F V H)
    (αD : TwoSquare G.mapDerivedCategory F.mapDerivedCategory
      V.mapDerivedCategory H.mapDerivedCategory) (Z : CochainComplex A ℤ) : Prop :=
  V.mapDerivedCategory.map (G.mapDerivedCategoryFactors.hom.app Z) ≫
      V.mapDerivedCategoryFactors.hom.app ((G.mapHomologicalComplex (.up ℤ)).obj Z) ≫
      DerivedCategory.Q.map ((α.natTrans.mapHomologicalComplex (.up ℤ)).app Z) =
    αD.app (DerivedCategory.Q.obj Z) ≫
      H.mapDerivedCategory.map (F.mapDerivedCategoryFactors.hom.app Z) ≫
      H.mapDerivedCategoryFactors.hom.app ((F.mapHomologicalComplex (.up ℤ)).obj Z)

end SquareEquation

section TripleComparison

variable {A : Type uA} [Category.{vA} A] [Abelian A] [HasDerivedCategory.{wA} A]
  {B : Type uB} [Category.{vB} B] [Abelian B] [HasDerivedCategory.{wB} B]
  {C : Type uC} [Category.{vC} C] [Abelian C] [HasDerivedCategory.{wC} C]
  {D : Type uD} [Category.{vD} D] [Abelian D] [HasDerivedCategory.{wD} D]
  (F : A ⥤ B) (G : B ⥤ C) (H : C ⥤ D)
  [F.Additive] [G.Additive] [H.Additive]
  [PreservesFiniteLimits F]
  [PreservesFiniteColimits F]
  [PreservesFiniteLimits G]
  [PreservesFiniteColimits G]
  [PreservesFiniteLimits H]
  [PreservesFiniteColimits H]

private def exactComparisonTriple (Z : CochainComplex A ℤ) :
    H.mapDerivedCategory.obj
        (G.mapDerivedCategory.obj
          (F.mapDerivedCategory.obj (DerivedCategory.Q.obj Z))) ⟶
      DerivedCategory.Q.obj
        ((H.mapHomologicalComplex (.up ℤ)).obj
          ((G.mapHomologicalComplex (.up ℤ)).obj ((F.mapHomologicalComplex (.up ℤ)).obj Z))) :=
  H.mapDerivedCategory.map
      (G.mapDerivedCategory.map (F.mapDerivedCategoryFactors.hom.app Z) ≫
        G.mapDerivedCategoryFactors.hom.app ((F.mapHomologicalComplex (.up ℤ)).obj Z)) ≫
    H.mapDerivedCategoryFactors.hom.app
      ((G.mapHomologicalComplex (.up ℤ)).obj ((F.mapHomologicalComplex (.up ℤ)).obj Z))

private instance exactComparisonTriple_isIso (Z : CochainComplex A ℤ) :
    IsIso (exactComparisonTriple F G H Z) := by
  unfold exactComparisonTriple
  infer_instance

end TripleComparison

section Whiskering

variable {A : Type uA} [Category.{vA} A] [Abelian A] [HasDerivedCategory.{wA} A]
  {B : Type uB} [Category.{vB} B] [Abelian B] [HasDerivedCategory.{wB} B]
  {C : Type uC} [Category.{vC} C] [Abelian C] [HasDerivedCategory.{wC} C]
  {D : Type uD} [Category.{vD} D] [Abelian D] [HasDerivedCategory.{wD} D]
  {E : Type uE} [Category.{vE} E] [Abelian E] [HasDerivedCategory.{wE} E]
  {F : A ⥤ B} {H : B ⥤ D} {G : A ⥤ C} {V : C ⥤ D}
  [F.Additive] [H.Additive] [G.Additive] [V.Additive]
  [PreservesFiniteLimits F]
  [PreservesFiniteColimits F]
  [PreservesFiniteLimits H]
  [PreservesFiniteColimits H]
  [PreservesFiniteLimits G]
  [PreservesFiniteColimits G]
  [PreservesFiniteLimits V]
  [PreservesFiniteColimits V]
  (α : TwoSquare G F V H)
  (αD : TwoSquare G.mapDerivedCategory F.mapDerivedCategory
    V.mapDerivedCategory H.mapDerivedCategory)

private theorem exactComparisonTriple_post
    (hα : ∀ Z, ExactFactorSquareEquation F H G V α αD Z)
    (J : D ⥤ E) [J.Additive] [PreservesFiniteLimits J] [PreservesFiniteColimits J]
    (Z : CochainComplex A ℤ) :
    J.mapDerivedCategory.map (αD.app (DerivedCategory.Q.obj Z)) ≫
        exactComparisonTriple F H J Z =
      exactComparisonTriple G V J Z ≫
        DerivedCategory.Q.map
          ((J.mapHomologicalComplex (.up ℤ)).map ((α.natTrans.mapHomologicalComplex
            (.up ℤ)).app Z)) := by
  have h : (V.mapDerivedCategory.map
        (G.mapDerivedCategoryFactors.hom.app Z) ≫
      V.mapDerivedCategoryFactors.hom.app ((G.mapHomologicalComplex (.up ℤ)).obj Z)) ≫
        DerivedCategory.Q.map ((α.natTrans.mapHomologicalComplex (.up ℤ)).app Z) =
      αD.app (DerivedCategory.Q.obj Z) ≫
        (H.mapDerivedCategory.map (F.mapDerivedCategoryFactors.hom.app Z) ≫
          H.mapDerivedCategoryFactors.hom.app
            ((F.mapHomologicalComplex (.up ℤ)).obj Z)) := by
    simpa only [ExactFactorSquareEquation, Category.assoc] using hα Z
  unfold exactComparisonTriple
  rw [← Category.assoc, ← Functor.map_comp, ← h, Functor.map_comp]
  simp only [Category.assoc]
  exact congrArg (fun k ↦ J.mapDerivedCategory.map
      (V.mapDerivedCategory.map (G.mapDerivedCategoryFactors.hom.app Z) ≫
        V.mapDerivedCategoryFactors.hom.app ((G.mapHomologicalComplex (.up ℤ)).obj Z)) ≫ k)
    (J.mapDerivedCategoryFactors.hom.naturality
      ((α.natTrans.mapHomologicalComplex (.up ℤ)).app Z))

private theorem exactComparisonTriple_pre
    (hα : ∀ Z, ExactFactorSquareEquation F H G V α αD Z)
    (J : E ⥤ A) [J.Additive] [PreservesFiniteLimits J] [PreservesFiniteColimits J]
    (Z : CochainComplex E ℤ) :
    αD.app (J.mapDerivedCategory.obj (DerivedCategory.Q.obj Z)) ≫
        exactComparisonTriple J F H Z =
      exactComparisonTriple J G V Z ≫
        DerivedCategory.Q.map
          ((α.natTrans.mapHomologicalComplex (.up ℤ)).app ((J.mapHomologicalComplex
            (.up ℤ)).obj Z)) := by
  have hn := αD.naturality (J.mapDerivedCategoryFactors.hom.app Z)
  change V.mapDerivedCategory.map
      (G.mapDerivedCategory.map (J.mapDerivedCategoryFactors.hom.app Z)) ≫
        αD.app (DerivedCategory.Q.obj ((J.mapHomologicalComplex (.up ℤ)).obj Z)) =
      αD.app (J.mapDerivedCategory.obj (DerivedCategory.Q.obj Z)) ≫
        H.mapDerivedCategory.map
          (F.mapDerivedCategory.map (J.mapDerivedCategoryFactors.hom.app Z))
    at hn
  have h := hα ((J.mapHomologicalComplex (.up ℤ)).obj Z)
  unfold ExactFactorSquareEquation at h
  unfold exactComparisonTriple
  simp only [Functor.map_comp, Category.assoc]
  rw [← reassoc_of% hn, ← h]

end Whiskering

section Cube

variable {A : Type uA} [Category.{vA} A] [Abelian A] [HasDerivedCategory.{wA} A]
  {B : Type uB} [Category.{vB} B] [Abelian B] [HasDerivedCategory.{wB} B]
  {C : Type uC} [Category.{vC} C] [Abelian C] [HasDerivedCategory.{wC} C]
  {D : Type uD} [Category.{vD} D] [Abelian D] [HasDerivedCategory.{wD} D]
  {A' : Type uA'} [Category.{vA'} A'] [Abelian A'] [HasDerivedCategory.{wA'} A']
  {B' : Type uB'} [Category.{vB'} B'] [Abelian B'] [HasDerivedCategory.{wB'} B']
  {C' : Type uC'} [Category.{vC'} C'] [Abelian C'] [HasDerivedCategory.{wC'} C']
  {D' : Type uD'} [Category.{vD'} D'] [Abelian D'] [HasDerivedCategory.{wD'} D']
  {L₁ : A ⥤ B} {L₂ : C ⥤ D} {L₁' : A' ⥤ B'} {L₂' : C' ⥤ D'}
  {G : A ⥤ C} {H : B ⥤ D} {G' : A' ⥤ C'} {H' : B' ⥤ D'}
  {QA : A ⥤ A'} {QB : B ⥤ B'} {QC : C ⥤ C'} {QD : D ⥤ D'}
  [L₁.Additive] [L₂.Additive] [L₁'.Additive] [L₂'.Additive]
  [G.Additive] [H.Additive] [G'.Additive] [H'.Additive]
  [QA.Additive] [QB.Additive] [QC.Additive] [QD.Additive]
  [PreservesFiniteLimits L₁]
  [PreservesFiniteColimits L₁]
  [PreservesFiniteLimits L₂]
  [PreservesFiniteColimits L₂]
  [PreservesFiniteLimits L₁']
  [PreservesFiniteColimits L₁']
  [PreservesFiniteLimits L₂']
  [PreservesFiniteColimits L₂']
  [PreservesFiniteLimits G]
  [PreservesFiniteColimits G]
  [PreservesFiniteLimits H]
  [PreservesFiniteColimits H]
  [PreservesFiniteLimits G']
  [PreservesFiniteColimits G']
  [PreservesFiniteLimits H']
  [PreservesFiniteColimits H']
  [PreservesFiniteLimits QA]
  [PreservesFiniteColimits QA]
  [PreservesFiniteLimits QB]
  [PreservesFiniteColimits QB]
  [PreservesFiniteLimits QC]
  [PreservesFiniteColimits QC]
  [PreservesFiniteLimits QD]
  [PreservesFiniteColimits QD]

/-- Six literal exact-comparison squares transport an original horizontal cube to
the same supplied squares of native unbounded localized functors. -/
theorem mapDerivedCategory_exactHorizontalCube
    (s₁ : TwoSquare QA L₁ L₁' QB) (s₂ : TwoSquare QC L₂ L₂' QD)
    (α : TwoSquare G L₁ L₂ H) (α' : TwoSquare G' L₁' L₂' H')
    (γ : TwoSquare QA G G' QC) (δ : TwoSquare QB H H' QD)
    (s₁D : TwoSquare QA.mapDerivedCategory L₁.mapDerivedCategory
      L₁'.mapDerivedCategory QB.mapDerivedCategory)
    (s₂D : TwoSquare QC.mapDerivedCategory L₂.mapDerivedCategory
      L₂'.mapDerivedCategory QD.mapDerivedCategory)
    (αD : TwoSquare G.mapDerivedCategory L₁.mapDerivedCategory
      L₂.mapDerivedCategory H.mapDerivedCategory)
    (α'D : TwoSquare G'.mapDerivedCategory L₁'.mapDerivedCategory
      L₂'.mapDerivedCategory H'.mapDerivedCategory)
    (γD : TwoSquare QA.mapDerivedCategory G.mapDerivedCategory
      G'.mapDerivedCategory QC.mapDerivedCategory)
    (δD : TwoSquare QB.mapDerivedCategory H.mapDerivedCategory
      H'.mapDerivedCategory QD.mapDerivedCategory)
    (hs₁ : ∀ Z, ExactFactorSquareEquation L₁ QB QA L₁' s₁ s₁D Z)
    (hs₂ : ∀ Z, ExactFactorSquareEquation L₂ QD QC L₂' s₂ s₂D Z)
    (hα : ∀ Z, ExactFactorSquareEquation L₁ H G L₂ α αD Z)
    (hα' : ∀ Z, ExactFactorSquareEquation L₁' H' G' L₂' α' α'D Z)
    (hγ : ∀ Z, ExactFactorSquareEquation G QC QA G' γ γD Z)
    (hδ : ∀ Z, ExactFactorSquareEquation H QD QB H' δ δD Z)
    (h : ∀ X, L₂'.map (γ.app X) ≫ (α ≫ₕ s₂).app X =
      (s₁ ≫ₕ α').app X ≫ δ.app (L₁.obj X))
    (K : DerivedCategory A) :
    L₂'.mapDerivedCategory.map (γD.app K) ≫ (αD ≫ₕ s₂D).app K =
      (s₁D ≫ₕ α'D).app K ≫ δD.app (L₁.mapDerivedCategory.obj K) := by
  have hQ (Z : CochainComplex A ℤ) :
      L₂'.mapDerivedCategory.map (γD.app (DerivedCategory.Q.obj Z)) ≫
          (αD ≫ₕ s₂D).app (DerivedCategory.Q.obj Z) =
        (s₁D ≫ₕ α'D).app (DerivedCategory.Q.obj Z) ≫
          δD.app (L₁.mapDerivedCategory.obj (DerivedCategory.Q.obj Z)) := by
    have hC :
        (L₂'.mapHomologicalComplex (.up ℤ)).map ((γ.natTrans.mapHomologicalComplex (.up ℤ)).app Z) ≫
            (s₂.natTrans.mapHomologicalComplex (.up ℤ)).app ((G.mapHomologicalComplex
              (.up ℤ)).obj Z) ≫
            (QD.mapHomologicalComplex (.up ℤ)).map ((α.natTrans.mapHomologicalComplex
              (.up ℤ)).app Z) =
          (α'.natTrans.mapHomologicalComplex (.up ℤ)).app ((QA.mapHomologicalComplex
            (.up ℤ)).obj Z) ≫
            (H'.mapHomologicalComplex (.up ℤ)).map ((s₁.natTrans.mapHomologicalComplex
              (.up ℤ)).app Z) ≫
            (δ.natTrans.mapHomologicalComplex (.up ℤ)).app ((L₁.mapHomologicalComplex
              (.up ℤ)).obj Z) := by
      ext n
      change L₂'.map (γ.app (Z.X n)) ≫ s₂.app (G.obj (Z.X n)) ≫
          QD.map (α.app (Z.X n)) =
        α'.app (QA.obj (Z.X n)) ≫ H'.map (s₁.app (Z.X n)) ≫
          δ.app (L₁.obj (Z.X n))
      simpa only [TwoSquare.hComp_app, Category.assoc] using h (Z.X n)
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
      whiskerRight γD.natTrans L₂'.mapDerivedCategory ≫ (αD ≫ₕ s₂D).natTrans =
        (s₁D ≫ₕ α'D).natTrans ≫ whiskerLeft L₁.mapDerivedCategory δD.natTrans := by
    apply Localization.natTrans_ext DerivedCategory.Q (HomologicalComplex.quasiIso A (.up ℤ))
    intro Z
    simpa only [NatTrans.comp_app, Functor.whiskerLeft_app,
      Functor.whiskerRight_app] using hQ Z
  simpa only [NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app] using congr_app he K

end Cube

end CategoryTheory
