/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Sites.SheafCohomology.Continuity.CoefficientDimensionShift
public import Aglib.CategoryTheory.Sites.SheafCohomology.Continuity.InjectiveDiagram

/-! # A dimension-shift criterion for canonical coefficient continuity -/

@[expose] public noncomputable section

namespace CategoryTheory.ShortComplex

open Limits

universe u v uI vI

variable {A : Type u} [Category.{v} A] [Abelian A]
  {I : Type uI} [Category.{vI} I] [HasColimitsOfShape I A]

/-- The componentwise colimit cocone of a short complex of diagrams. -/
def componentwiseColimitCocone (S : ShortComplex (I ⥤ A)) :
    Cocone ((functorEquivalence I A).functor.obj S) where
  pt := S.map colim
  ι :=
    { app := fun i => Hom.mk (colimit.ι S.X₁ i) (colimit.ι S.X₂ i) (colimit.ι S.X₃ i)
        (colimit.ι_map S.f i) (colimit.ι_map S.g i)
      naturality := fun i j f => by
        ext1
        · change S.X₁.map f ≫ colimit.ι S.X₁ j = colimit.ι S.X₁ i ≫ 𝟙 _
          simpa only [Category.comp_id] using colimit.w S.X₁ f
        · change S.X₂.map f ≫ colimit.ι S.X₂ j = colimit.ι S.X₂ i ≫ 𝟙 _
          simpa only [Category.comp_id] using colimit.w S.X₂ f
        · change S.X₃.map f ≫ colimit.ι S.X₃ j = colimit.ι S.X₃ i ≫ 𝟙 _
          simpa only [Category.comp_id] using colimit.w S.X₃ f }

end CategoryTheory.ShortComplex

namespace CategoryTheory.Sheaf.H

open Limits Abelian Functor.InjectiveDiagram

universe u v w e uI vI

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [HasSheafify J AddCommGrpCat.{w}] [HasExt.{e} (Sheaf J AddCommGrpCat.{w})]
  {I : Type uI} [Category.{vI} I]
  [EnoughInjectives (Sheaf J AddCommGrpCat.{w})]
  [HasProductsOfShape I (Sheaf J AddCommGrpCat.{w})]
  [∀ i j : I, HasProductsOfShape (i ⟶ j) (Sheaf J AddCommGrpCat.{w})]
  [HasColimitsOfShape I (Sheaf J AddCommGrpCat.{w})]
  [HasExactColimitsOfShape I (Sheaf J AddCommGrpCat.{w})]
  [HasColimitsOfShape I AddCommGrpCat.{e}]
  [HasExactColimitsOfShape I AddCommGrpCat.{e}]
  [PreservesColimitsOfShape I (functorH J 0)]

/-- Exact colimits, degree-zero continuity, and injective-diagram acyclicity imply
invertibility of the original comparison in every degree. -/
lemma isIso_coefficientColimitComparison_of_injective_colimit_acyclic
    (hvan : ∀ (Q : I ⥤ Sheaf J AddCommGrpCat.{w}), (∀ i, Injective (Q.obj i)) →
      ∀ n, ∀ x : Sheaf.H (colimit Q) (n + 1), x = 0)
    (n : ℕ) (G : I ⥤ Sheaf J AddCommGrpCat.{w}) :
    IsIso (coefficientColimitComparison G n) := by
  induction n generalizing G with
  | zero =>
      change IsIso (colimit.post G (functorH J 0))
      infer_instance
  | succ n ih =>
      let S : ShortComplex (I ⥤ Sheaf J AddCommGrpCat.{w}) :=
        ShortComplex.mk (ι G) (cokernel.π (ι G)) (cokernel.condition (ι G))
      have hS : S.ShortExact := { exact := ShortComplex.exact_cokernel (ι G) }
      let D := (ShortComplex.functorEquivalence I (Sheaf J AddCommGrpCat.{w})).functor.obj S
      let hD : ∀ i, (D.obj i).ShortExact := fun i => hS.map ((evaluation _ _).obj i)
      let c := S.componentwiseColimitCocone
      have hc : c.pt.ShortExact := hS.map colim
      have h₁ : IsIso (coefficientCoconeDesc D c ShortComplex.π₂ n) := ih (replacement G)
      have h₂ : IsIso (coefficientCoconeDesc D c ShortComplex.π₃ n) := ih (cokernel (ι G))
      change IsIso (coefficientCoconeDesc D c ShortComplex.π₁ (n + 1))
      apply isIso_coefficientCoconeDesc_succ D hD n c hc
      · intro i x
        let : Injective (D.obj i).X₂ := by
          change Injective ((replacement G).obj i)
          infer_instance
        exact Ext.eq_zero_of_injective x
      · exact hvan (replacement G) (fun _ => inferInstance) n

end CategoryTheory.Sheaf.H
