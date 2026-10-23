/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.CategoryTheory.Sites.SheafCohomology.ExactSequences
public import Mathlib.CategoryTheory.Limits.Preserves.Limits

/-! # Canonical coefficient-colimit maps on original sheaf cohomology

These maps use the original `Sheaf.functorH` and `Sheaf.H.δ`. Their compatibility
with the connecting homomorphisms is the comparison square needed for dimension
shifting. No invertibility of the comparison is assumed or asserted here.
-/

@[expose] public noncomputable section

namespace CategoryTheory.Sheaf.H

open Limits Abelian

universe u v w e uI vI

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [HasSheafify J AddCommGrpCat.{w}] [HasExt.{e} (Sheaf J AddCommGrpCat.{w})]
  {I : Type uI} [Category.{vI} I]

/-- The actual colimit comparison, induced by the coefficient cocone maps. -/
def coefficientColimitComparison (G : I ⥤ Sheaf J AddCommGrpCat.{w}) (n : ℕ)
    [HasColimit G] [HasColimit (G ⋙ functorH J n)] :
    colimit (G ⋙ functorH J n) ⟶ (functorH J n).obj (colimit G) :=
  colimit.post G (functorH J n)

/-- Normalization on every original coefficient-diagram injection. -/
@[reassoc]
lemma ι_coefficientColimitComparison (G : I ⥤ Sheaf J AddCommGrpCat.{w}) (n : ℕ)
    [HasColimit G] [HasColimit (G ⋙ functorH J n)] (i : I) :
    colimit.ι (G ⋙ functorH J n) i ≫ coefficientColimitComparison G n =
      (functorH J n).map (colimit.ι G i) :=
  colimit.ι_post G (functorH J n) i

variable (D : I ⥤ ShortComplex (Sheaf J AddCommGrpCat.{w}))
  (hD : ∀ i, (D.obj i).ShortExact) (n : ℕ)

/-- The original connecting maps form a natural transformation on the diagram. -/
def connectingDiagram :
    D ⋙ ShortComplex.π₃ ⋙ functorH J n ⟶
      D ⋙ ShortComplex.π₁ ⋙ functorH J (n + 1) where
  app i := AddCommGrpCat.ofHom (δ (hD i) n (n + 1) rfl)
  naturality i j f := by
    ext x
    exact δ_naturality n (n + 1) rfl (hD i) (hD j) (D.map f) x

/-- A short-complex cocone induces the original cohomology cocone at each vertex. -/
def coefficientCocone (c : Cocone D) (P : ShortComplex (Sheaf J AddCommGrpCat.{w}) ⥤
    Sheaf J AddCommGrpCat.{w}) (q : ℕ) : Cocone (D ⋙ P ⋙ functorH J q) :=
  (P ⋙ functorH J q).mapCocone c

/-- The map out of the actual colimit of a vertex's cohomology diagram. -/
def coefficientCoconeDesc (c : Cocone D)
    (P : ShortComplex (Sheaf J AddCommGrpCat.{w}) ⥤ Sheaf J AddCommGrpCat.{w})
    (q : ℕ) [HasColimit (D ⋙ P ⋙ functorH J q)] :
    colimit (D ⋙ P ⋙ functorH J q) ⟶ (functorH J q).obj (P.obj c.pt) :=
  colimit.desc _ (coefficientCocone D c P q)

/-- The comparison square with the original connecting homomorphism commutes. -/
lemma connectingDiagram_colimit (c : Cocone D) (hc : c.pt.ShortExact)
    [HasColimitsOfShape I AddCommGrpCat.{e}] :
    colim.map (connectingDiagram D hD n) ≫
        coefficientCoconeDesc D c ShortComplex.π₁ (n + 1) =
      coefficientCoconeDesc D c ShortComplex.π₃ n ≫
        AddCommGrpCat.ofHom (δ hc n (n + 1) rfl) := by
  apply colimit.hom_ext
  intro i
  dsimp only [coefficientCoconeDesc]
  erw [colimit.ι_map_assoc, colimit.ι_desc, colimit.ι_desc_assoc]
  ext x
  exact (δ_naturality n (n + 1) rfl (hD i) hc (c.ι.app i) x).symm

end CategoryTheory.Sheaf.H
