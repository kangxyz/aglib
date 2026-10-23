/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Sites.SheafCohomology.Continuity.CoefficientContinuity
public import Aglib.CategoryTheory.Sites.SheafCohomology.Continuity.CoefficientDegreeZero
public import Aglib.CategoryTheory.Sites.SheafCohomology.Continuity.FiniteFamilyColimit
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf

/-! # Original cohomology continuity on finite-hypercover sites -/

@[expose] public noncomputable section

namespace CategoryTheory

open Limits

universe k e

/-- Existing filtered colimits of abelian groups are exact even when the
indexing universe is larger than the coefficient universe. -/
lemma hasExactFilteredColimitsOfShape_addCommGrpCat
    (I : Type k) [SmallCategory I] [IsFiltered I]
    [HasColimitsOfShape I AddCommGrpCat.{e}] :
    HasExactColimitsOfShape I AddCommGrpCat.{e} := by
  let E : I ≌ AsSmall.{max e k} I := AsSmall.equiv (C := I)
  let : IsFiltered (AsSmall.{max e k} I) := IsFiltered.of_equivalence E
  let : HasExactColimitsOfShape I AddCommGrpCat.{max e k} :=
    HasExactColimitsOfShape.of_domain_equivalence AddCommGrpCat.{max e k} E.symm
  exact HasExactColimitsOfShape.domain_of_functor I AddCommGrpCat.uliftFunctor.{k, e}

end CategoryTheory

namespace CategoryTheory.GrothendieckTopology.OneHypercoverFamily

open Limits Opposite

universe u v e

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [HasSheafify J AddCommGrpCat.{max u v}]
  [HasExt.{e} (Sheaf J AddCommGrpCat.{max u v})]
  [EnoughInjectives (Sheaf J AddCommGrpCat.{max u v})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
  [J.HasSheafCompose (forget AddCommGrpCat.{max u v})]
  [∀ W : C, HasFiniteProducts (Over W)]
  (H : J.OneHypercoverFamily.{max u v}) [H.IsGenerating]
  (hfin : ∀ ⦃X : C⦄ (E : J.OneHypercover.{max u v} X), H E →
    Finite E.I₀ ∧ ∀ i j : E.I₀, Finite (E.I₁ i j))
  {I : Type (max u v)} [SmallCategory I] [IsFiltered I]
  [HasColimitsOfShape I AddCommGrpCat.{e}]
  {T : C} (hT : IsTerminal T)

include H hfin hT in
/-- The original canonical comparison is invertible in every degree; all
cohomological inputs come from finite hypercovers and original injective acyclicity. -/
lemma isIso_cohomologyFilteredColimitComparison
    (G : I ⥤ Sheaf J AddCommGrpCat.{max u v}) (n : ℕ) :
    IsIso (Sheaf.H.coefficientColimitComparison G n) := by
  let : HasExactColimitsOfShape I (Sheaf J AddCommGrpCat.{max u v}) := inferInstance
  let : HasExactColimitsOfShape I AddCommGrpCat.{e} :=
    hasExactFilteredColimitsOfShape_addCommGrpCat I
  let := preservesFilteredColimitsDegreeZero (I := I) H hfin hT
  apply Sheaf.H.isIso_coefficientColimitComparison_of_injective_colimit_acyclic
  intro Q hQ q x
  let (i : I) : Injective (Q.obj i) := hQ i
  exact Sheaf.ModuleCoefficients.colimit_injective_cohomology_eq_zero H hfin Q hT q x

end CategoryTheory.GrothendieckTopology.OneHypercoverFamily
