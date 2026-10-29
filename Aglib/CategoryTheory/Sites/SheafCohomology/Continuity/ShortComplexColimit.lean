/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.Algebra.Category.Grp.Ulift
public import Mathlib.Algebra.Homology.ShortComplex.FunctorEquivalence
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic

/-! # Exactness and componentwise colimit preservation

A short-complex-valued functor takes a colimit of pointwise exact objects to an
exact short complex whenever its three components preserve that colimit and
colimits of the indexing shape are exact in the target. The comparison uses the
three canonical preservation isomorphisms, not a preservation hypothesis on the
short-complex-valued functor itself.
-/

@[expose] public noncomputable section

namespace CategoryTheory.ShortComplex

open Limits

universe uI vI uA vA uB vB

variable {I : Type uI} [Category.{vI} I]
  {A : Type uA} [Category.{vA} A]
  {B : Type uB} [Category.{vB} B] [Abelian B]

/-- Exactness of a short complex of functors is detected by evaluation. -/
lemma exact_of_evaluation (S : ShortComplex (I ⥤ B))
    (h : ∀ i, (S.map ((CategoryTheory.evaluation I B).obj i)).Exact) : S.Exact := by
  simp only [exact_iff_isZero_homology] at h ⊢
  rw [IsZero.iff_id_eq_zero]
  ext i
  apply (IsZero.of_iso (h i)
    (S.mapHomologyIso ((CategoryTheory.evaluation I B).obj i)).symm).eq_of_src

variable [HasColimitsOfShape I B] [HasExactColimitsOfShape I B]
  (T : A ⥤ ShortComplex B) (G : I ⥤ A) [HasColimit G]
  [PreservesColimit G (T ⋙ π₁)] [PreservesColimit G (T ⋙ π₂)]
  [PreservesColimit G (T ⋙ π₃)]

omit [Abelian B] [HasExactColimitsOfShape I B] in
/-- Naturality of the inverse preservation comparison in the target functor. -/
lemma preservation_inv_naturality
    (F H : A ⥤ B) (α : F ⟶ H) [PreservesColimit G F] [PreservesColimit G H] :
    (preservesColimitIso F G).inv ≫ α.app (colimit G) =
      colim.map (Functor.whiskerLeft G α) ≫ (preservesColimitIso H G).inv := by
  apply colimit.hom_ext
  intro i
  rw [ι_preservesColimitIso_inv_assoc, colimit.ι_map_assoc,
    ι_preservesColimitIso_inv]
  exact α.naturality (colimit.ι G i)

/-- The componentwise canonical comparison for a short-complex-valued functor. -/
def colimitComparisonIso :
    (((functorEquivalence I B).inverse.obj (G ⋙ T)).map colim) ≅
      T.obj (colimit G) := by
  refine isoMk (preservesColimitIso (T ⋙ π₁) G).symm
    (preservesColimitIso (T ⋙ π₂) G).symm
    (preservesColimitIso (T ⋙ π₃) G).symm ?_ ?_
  · exact preservation_inv_naturality G (T ⋙ π₁) (T ⋙ π₂)
      (Functor.whiskerLeft T π₁Toπ₂)
  · exact preservation_inv_naturality G (T ⋙ π₂) (T ⋙ π₃)
      (Functor.whiskerLeft T π₂Toπ₃)

/-- Componentwise preservation and exact colimits transport pointwise exactness. -/
lemma exact_obj_colimit (h : ∀ i, (T.obj (G.obj i)).Exact) :
    (T.obj (colimit G)).Exact := by
  let S := (functorEquivalence I B).inverse.obj (G ⋙ T)
  have hS : S.Exact := exact_of_evaluation S (fun i => by
    change (T.obj (G.obj i)).Exact
    exact h i)
  exact exact_of_iso (colimitComparisonIso T G) (hS.map colim)

end CategoryTheory.ShortComplex

namespace CategoryTheory

open Limits

universe e uI vI

/-- Existing filtered colimits of abelian groups are exact with independent
index-object, index-morphism and original coefficient universes. -/
lemma hasExactFilteredColimitsOfShape_addCommGrpCat_of_category
    (I : Type uI) [Category.{vI} I] [IsFiltered I]
    [HasColimitsOfShape I AddCommGrpCat.{e}] :
    HasExactColimitsOfShape I AddCommGrpCat.{e} := by
  let E : I ≌ AsSmall.{max e uI vI} I := AsSmall.equiv (C := I)
  have : IsFiltered (AsSmall.{max e uI vI} I) := IsFiltered.of_equivalence E
  let : HasExactColimitsOfShape I AddCommGrpCat.{max e uI vI} :=
    HasExactColimitsOfShape.of_domain_equivalence AddCommGrpCat.{max e uI vI} E.symm
  exact HasExactColimitsOfShape.domain_of_functor I AddCommGrpCat.uliftFunctor.{max uI vI, e}

end CategoryTheory
