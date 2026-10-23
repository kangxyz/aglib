/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Sites.SheafCohomology.Slice.Adjunction
public import Aglib.CategoryTheory.Sites.Hypercohomology.Basic
public import Mathlib.CategoryTheory.Adjunction.Additive
public import Mathlib.Algebra.Category.Grp.ForgetCorepresentable

/-!
# The slice constant integer sheaf and the free representable

The actual slice lower shriek sends the constant integer sheaf to the original
lifted free representable. The comparison is constructed from the additive
representation of evaluation, retaining its degree-zero normalization.
-/

@[expose] public noncomputable section

universe t v u

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory.Sheaf.SliceCohomology

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C) (U : C)
  [HasSheafify J AddCommGrpCat.{max v t}]
  [HasSheafify (J.over U) AddCommGrpCat.{max v t}]

/-- The original constant integer sheaf on the slice site. -/
abbrev sliceIntegers : Sheaf (J.over U) AddCommGrpCat.{max v t} :=
  (constantSheaf (J.over U) AddCommGrpCat.{max v t}).obj
    (AddCommGrpCat.of (ULift.{max v t} ℤ))

/-- Evaluation represented by lower shriek of the actual slice integer sheaf. -/
def lowerShriekSectionsAddEquiv (F : Sheaf J AddCommGrpCat.{max v t}) :
    ((lowerShriek J AddCommGrpCat.{max v t} U).obj (sliceIntegers J U) ⟶ F) ≃+
      F.obj.obj (op U) :=
  ((lowerShriekAdjunction J AddCommGrpCat.{max v t} U).homAddEquiv _ F).trans
    (((constantSheafAdj (J.over U) AddCommGrpCat.{max v t} Over.mkIdTerminal).homAddEquiv
      (AddCommGrpCat.of (ULift.{max v t} ℤ)) (F.over U)).trans
      (AddCommGrpCat.uliftZMultiplesAddEquiv _))

/-- The representing equivalence uses the original coefficient morphism. -/
theorem lowerShriekSectionsAddEquiv_naturality
    {F G : Sheaf J AddCommGrpCat.{max v t}}
    (a : (lowerShriek J AddCommGrpCat.{max v t} U).obj (sliceIntegers J U) ⟶ F)
    (g : F ⟶ G) :
    lowerShriekSectionsAddEquiv J U G (a ≫ g) =
      g.hom.app (op U) (lowerShriekSectionsAddEquiv J U F a) := by
  change (AddCommGrpCat.uliftZMultiplesAddEquiv _)
    ((constantSheafAdj (J.over U) AddCommGrpCat.{max v t} Over.mkIdTerminal).homEquiv _ _
      ((lowerShriekAdjunction J AddCommGrpCat.{max v t} U).homEquiv _ _ (a ≫ g))) =
    g.hom.app (op U) ((AddCommGrpCat.uliftZMultiplesAddEquiv _)
      ((constantSheafAdj (J.over U) AddCommGrpCat.{max v t} Over.mkIdTerminal).homEquiv _ _
        ((lowerShriekAdjunction J AddCommGrpCat.{max v t} U).homEquiv _ _ a)))
  rw [Adjunction.homEquiv_naturality_right, Adjunction.homEquiv_naturality_right]
  rfl

/-- The actual free representable corepresents the evaluation functor. -/
def freeRepresentableCorepresentable :
    (((sheafSections J AddCommGrpCat.{max v t}).obj (op U)) ⋙
      forget AddCommGrpCat.{max v t}).CorepresentableBy
      (Hypercohomology.freeAbelianSheaf.{t} J U) where
  homEquiv := (Hypercohomology.sectionsAddEquiv J U _).toEquiv
  homEquiv_comp g a := Hypercohomology.sectionsEquiv_naturality J U a g

/-- The original slice left adjoint gives a second representation of evaluation. -/
def lowerShriekIntegersCorepresentable :
    (((sheafSections J AddCommGrpCat.{max v t}).obj (op U)) ⋙
      forget AddCommGrpCat.{max v t}).CorepresentableBy
      ((lowerShriek J AddCommGrpCat.{max v t} U).obj (sliceIntegers J U)) where
  homEquiv := (lowerShriekSectionsAddEquiv J U _).toEquiv
  homEquiv_comp g a := lowerShriekSectionsAddEquiv_naturality J U a g

/-- Canonical source comparison, built from the actual evaluation representations. -/
def lowerShriekIntegersIso :
    (lowerShriek J AddCommGrpCat.{max v t} U).obj (sliceIntegers J U) ≅
      Hypercohomology.freeAbelianSheaf.{t} J U :=
  (lowerShriekIntegersCorepresentable J U).uniqueUpToIso
    (freeRepresentableCorepresentable J U)

/-- The forward source comparison is the element classified by the original free identity. -/
theorem lowerShriekIntegersIso_hom :
    (lowerShriekIntegersIso J U).hom =
      (lowerShriekSectionsAddEquiv J U _).symm
        (Hypercohomology.sectionsAddEquiv J U _ (𝟙 _)) := rfl

/-- The source comparison preserves the actual evaluation of every coefficient morphism. -/
theorem lowerShriekIntegersIso_evaluation
    (F : Sheaf J AddCommGrpCat.{max v t})
    (a : Hypercohomology.freeAbelianSheaf.{t} J U ⟶ F) :
    lowerShriekSectionsAddEquiv J U F ((lowerShriekIntegersIso J U).hom ≫ a) =
      Hypercohomology.sectionsAddEquiv J U F a := by
  rw [lowerShriekSectionsAddEquiv_naturality, lowerShriekIntegersIso_hom,
    AddEquiv.apply_symm_apply]
  simpa only [Category.id_comp] using!
    (Hypercohomology.sectionsEquiv_naturality J U (𝟙 _) a).symm

end CategoryTheory.Sheaf.SliceCohomology
