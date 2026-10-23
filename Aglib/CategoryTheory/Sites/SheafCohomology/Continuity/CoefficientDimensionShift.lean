/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Sites.SheafCohomology.Continuity.CoefficientComparison
public import Aglib.CategoryTheory.Sites.SheafCohomology.Continuity.ShortComplexColimit
public import Mathlib.CategoryTheory.Abelian.DiagramLemmas.Four

/-! # Dimension shifting for the original coefficient-colimit comparison -/

@[expose] public noncomputable section

namespace CategoryTheory.Sheaf.H

open Limits Abelian

universe u v w e uI vI

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [HasSheafify J AddCommGrpCat.{w}] [HasExt.{e} (Sheaf J AddCommGrpCat.{w})]
  {I : Type uI} [Category.{vI} I]
  (D : I ⥤ ShortComplex (Sheaf J AddCommGrpCat.{w}))
  (hD : ∀ i, (D.obj i).ShortExact) (n : ℕ)

/-- The original right-exact part of the cohomology sequence, as a complex of diagrams. -/
def connectingShortComplex : ShortComplex (I ⥤ AddCommGrpCat.{e}) where
  f := Functor.whiskerRight (Functor.whiskerLeft D ShortComplex.π₂Toπ₃) (functorH J n)
  g := connectingDiagram D hD n
  zero := by
    apply NatTrans.ext
    funext i
    exact (longSequence_exact (hD i) n (n + 1) rfl).zero 1

/-- Exactness is detected pointwise and is the original long-exact-sequence theorem. -/
lemma connectingShortComplex_exact : (connectingShortComplex D hD n).Exact := by
  apply ShortComplex.exact_of_evaluation
  intro i
  exact longSequence_exact₃' (hD i) n (n + 1) rfl

/-- Vanishing of the middle coefficient's next cohomology makes the original boundary epic. -/
lemma connecting_epi {S : ShortComplex (Sheaf J AddCommGrpCat.{w})} (hS : S.ShortExact)
    (hvan : ∀ x : Sheaf.H S.X₂ (n + 1), x = 0) :
    Epi (AddCommGrpCat.ofHom (δ hS n (n + 1) rfl)) := by
  apply (AddCommGrpCat.epi_iff_surjective _).mpr
  intro x
  exact longSequence_exact₁ hS x (hvan _) rfl

variable [HasColimitsOfShape I AddCommGrpCat.{e}]
  [HasExactColimitsOfShape I AddCommGrpCat.{e}]

/-- A cocone of coefficient short complexes induces the actual comparison of right-exact rows. -/
def connectingComparison (c : Cocone D) (hc : c.pt.ShortExact) :
    (connectingShortComplex D hD n).map colim ⟶
      ShortComplex.mk (AddCommGrpCat.ofHom (map c.pt.g n))
        (AddCommGrpCat.ofHom (δ hc n (n + 1) rfl))
        ((longSequence_exact hc n (n + 1) rfl).zero 1) := by
  refine ShortComplex.Hom.mk (coefficientCoconeDesc D c ShortComplex.π₂ n)
    (coefficientCoconeDesc D c ShortComplex.π₃ n)
    (coefficientCoconeDesc D c ShortComplex.π₁ (n + 1)) ?_ ?_
  · apply colimit.hom_ext
    intro i
    dsimp only [coefficientCoconeDesc]
    erw [colimit.ι_desc_assoc, colimit.ι_map_assoc, colimit.ι_desc]
    change (functorH J n).map (c.ι.app i).τ₂ ≫ (functorH J n).map c.pt.g =
      (functorH J n).map (D.obj i).g ≫ (functorH J n).map (c.ι.app i).τ₃
    have hi : (c.ι.app i).τ₂ ≫ c.pt.g = (D.obj i).g ≫ (c.ι.app i).τ₃ :=
      (c.ι.app i).comm₂₃
    simpa only [Functor.map_comp] using (functorH J n).congr_map hi
  · exact (connectingDiagram_colimit D hD n c hc).symm

include hD in
/-- The dimension-shift step uses vanishing, not the desired comparison's invertibility. -/
lemma isIso_coefficientCoconeDesc_succ (c : Cocone D) (hc : c.pt.ShortExact)
    (hvan : ∀ i, ∀ x : Sheaf.H (D.obj i).X₂ (n + 1), x = 0)
    (hcvan : ∀ x : Sheaf.H c.pt.X₂ (n + 1), x = 0)
    [Epi (coefficientCoconeDesc D c ShortComplex.π₂ n)]
    [IsIso (coefficientCoconeDesc D c ShortComplex.π₃ n)] :
    IsIso (coefficientCoconeDesc D c ShortComplex.π₁ (n + 1)) := by
  let φ := connectingComparison D hD n c hc
  have (i : I) : Epi ((connectingShortComplex D hD n).g.app i) :=
    connecting_epi n (hD i) (hvan i)
  have : Epi (connectingShortComplex D hD n).g := NatTrans.epi_of_epi_app _
  have : Epi (AddCommGrpCat.ofHom (δ hc n (n + 1) rfl)) := connecting_epi n hc hcvan
  refine Abelian.isIso_of_epi_of_isIso
    (ShortComplex.mapToComposableArrows φ)
    ((connectingShortComplex_exact D hD n).map colim).exact_toComposableArrows
    (longSequence_exact₃' hc n (n + 1) rfl).exact_toComposableArrows
    ?_ ?_ ?_ ?_
  · change Epi (colim.map (connectingShortComplex D hD n).g)
    infer_instance
  · change Epi (AddCommGrpCat.ofHom (δ hc n (n + 1) rfl))
    infer_instance
  · change Epi (coefficientCoconeDesc D c ShortComplex.π₂ n)
    infer_instance
  · change IsIso (coefficientCoconeDesc D c ShortComplex.π₃ n)
    infer_instance

end CategoryTheory.Sheaf.H
