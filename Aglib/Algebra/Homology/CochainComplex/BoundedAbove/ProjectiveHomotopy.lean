/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.CochainComplex.BoundedAbove.Basic
public import Aglib.Algebra.Homology.CochainComplex.BoundedAbove.ProjectiveReplacement
public import Aglib.Algebra.Homology.DerivedCategory.KProjective.Comparison


/-!
# Functorial bounded-above projective replacements up to chain homotopy

The proved projective replacement theorem supplies actual complexes and
augmentations. Genuine K-projective lifting constructs comparison chain maps;
uniqueness up to homotopy proves identity, composition, and addition. Thus the
replacement is an actual additive functor into the homotopy category, with
natural augmentation. No additive or zero-preserving original free cover is assumed.
-/
/-!
Source: frozen dirty Quillen `6db56ddd3fdb898ef5de29d5fe51a0c61f9ba116`.
`Quillen/Algebra/Homology/BoundedProjectiveHomotopy.lean`.
SHA-256: `d004a22d7d3509cb4e702eecfd99fdbbd1ef7e312d58021e0c03075cd999dce4`.
Selected source lines: 1–134.
Actual source objects, maps, hypotheses and independent universes are preserved.
-/

@[expose] public section


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u v
open CategoryTheory CategoryTheory.Limits HomologicalComplex
namespace CochainComplex

variable {C : Type u} [Category.{v} C] [Abelian C]

variable [EnoughProjectives C]

/-- In an abelian category with enough projectives, every bounded-above complex admits a
quasi-isomorphism from a termwise projective complex with the same selected strict upper
bound. -/
theorem model_exists (K : BoundedAboveComplex C) :
    ∃ (P : CochainComplex C ℤ) (p : P ⟶ K.obj), QuasiIso p ∧
      (∀ n, Projective (P.X n)) ∧ P.IsStrictlyLE (chosenUpperBound K) :=
  exists_boundedAbove_projective_replacement K.obj (chosenUpperBound K)

/-- A genuine chosen projective replacement, obtained from the proved existence theorem. -/
def projectiveModel (K : BoundedAboveComplex C) : CochainComplex C ℤ :=
  (model_exists K).choose

/-- The chosen quasi-isomorphism from the bounded-above termwise projective replacement
`projectiveModel K` to the original complex `K.obj`. -/
def projectiveModelπ (K : BoundedAboveComplex C) : projectiveModel K ⟶ K.obj :=
  (model_exists K).choose_spec.choose

instance projectiveModelπ_quasiIso (K : BoundedAboveComplex C) : QuasiIso (projectiveModelπ K) :=
  (model_exists K).choose_spec.choose_spec.1

instance projectiveModel_projective (K : BoundedAboveComplex C) (n : ℤ) :
    Projective ((projectiveModel K).X n) :=
  (model_exists K).choose_spec.choose_spec.2.1 n

instance projectiveModel_boundedAbove (K : BoundedAboveComplex C) :
    (projectiveModel K).IsStrictlyLE (chosenUpperBound K) :=
  (model_exists K).choose_spec.choose_spec.2.2

instance projectiveModel_isKProjective (K : BoundedAboveComplex C) :
    (projectiveModel K).IsKProjective :=
  CochainComplex.isKProjective_of_projective (projectiveModel K) (chosenUpperBound K)

/-- The actual chain comparison, chosen using genuine K-projective lifting. -/
def projectiveModelMap {K L : BoundedAboveComplex C} (f : K ⟶ L) :
    projectiveModel K ⟶ projectiveModel L :=
  (exists_lift_quasiIso_up_to_homotopy (projectiveModelπ L) (projectiveModelπ K ≫ f.hom)).choose

/-- The comparison triangle commutes by an actual chain homotopy. -/
def projectiveModelMapHomotopy {K L : BoundedAboveComplex C} (f : K ⟶ L) :
    Homotopy (projectiveModelMap f ≫ projectiveModelπ L) (projectiveModelπ K ≫ f.hom) :=
  (exists_lift_quasiIso_up_to_homotopy (projectiveModelπ L)
    (projectiveModelπ K ≫ f.hom)).choose_spec.some

@[reassoc]
theorem projectiveModelMap_Q_comp_π [HasDerivedCategory C] {K L : BoundedAboveComplex C} (f : K ⟶ L)
  :
    DerivedCategory.Q.map (projectiveModelMap f) ≫ DerivedCategory.Q.map (projectiveModelπ L) =
      DerivedCategory.Q.map (projectiveModelπ K) ≫ DerivedCategory.Q.map f.hom := by
  simpa only [Functor.map_comp] using
    DerivedCategory.Q_map_eq_of_homotopy C (projectiveModelMapHomotopy f)

attribute [local instance] HasDerivedCategory.standard

variable (C)

/-- Projective replacements form a genuine functor after passing to chain homotopy. -/
def projectiveModelHomotopyFunctor : BoundedAboveComplex C ⥤ HomotopyCategory C (.up ℤ) where
  obj K := (HomotopyCategory.quotient C (.up ℤ)).obj (projectiveModel K)
  map f := (HomotopyCategory.quotient C (.up ℤ)).map (projectiveModelMap f)
  map_id K := by
    rw [← (HomotopyCategory.quotient C (.up ℤ)).map_id]
    apply HomotopyCategory.eq_of_homotopy
    apply homotopyOfDerivedEqOfIsKProjective
    apply (cancel_mono (DerivedCategory.Q.map (projectiveModelπ K))).mp
    rw [projectiveModelMap_Q_comp_π]
    simp
  map_comp {K L M} f g := by
    rw [← Functor.map_comp]
    apply HomotopyCategory.eq_of_homotopy
    apply homotopyOfDerivedEqOfIsKProjective
    apply (cancel_mono (DerivedCategory.Q.map (projectiveModelπ M))).mp
    rw [projectiveModelMap_Q_comp_π, Functor.map_comp, Category.assoc,
      projectiveModelMap_Q_comp_π, ← Category.assoc, projectiveModelMap_Q_comp_π]
    simp

/-- The functor on homotopy categories is additive, despite the nonadditive original covers. -/
instance projectiveModelHomotopyFunctor_additive : (projectiveModelHomotopyFunctor C).Additive where
  map_add {K L} f g := by
    change (HomotopyCategory.quotient C (.up ℤ)).map (projectiveModelMap (f + g)) =
      (HomotopyCategory.quotient C (.up ℤ)).map (projectiveModelMap f) +
        (HomotopyCategory.quotient C (.up ℤ)).map (projectiveModelMap g)
    rw [← Functor.map_add]
    apply HomotopyCategory.eq_of_homotopy
    apply homotopyOfDerivedEqOfIsKProjective
    apply (cancel_mono (DerivedCategory.Q.map (projectiveModelπ L))).mp
    rw [projectiveModelMap_Q_comp_π, Functor.map_add, Preadditive.add_comp,
      projectiveModelMap_Q_comp_π, projectiveModelMap_Q_comp_π]
    change DerivedCategory.Q.map (projectiveModelπ K) ≫ DerivedCategory.Q.map (f.hom + g.hom) = _
    rw [Functor.map_add, Preadditive.comp_add]

/-- Its augmentation is genuinely natural in the homotopy category. -/
def projectiveModelHomotopyAugmentation : projectiveModelHomotopyFunctor C ⟶
    (boundedAbove C).ι ⋙ HomotopyCategory.quotient C (.up ℤ) where
  app K := (HomotopyCategory.quotient C (.up ℤ)).map (projectiveModelπ K)
  naturality {K L} f := by
    dsimp [projectiveModelHomotopyFunctor]
    rw [← Functor.map_comp, ← Functor.map_comp]
    exact HomotopyCategory.eq_of_homotopy _ _ (projectiveModelMapHomotopy f)

end CochainComplex
