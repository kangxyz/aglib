/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Continuity.QcqsSections
public import Aglib.CategoryTheory.Sites.Torsion.FinitePresentation
public import Aglib.AlgebraicGeometry.EtaleCohomology.H1.Basic
public import Mathlib.Algebra.Category.Grp.FilteredColimits

/-!
# Finite-presentation compactness on actual qcqs etale generators

The original sections functor on a qcqs object of the native small-etale
site preserves filtered coefficient colimits. Forgetting its abelian-group
structure gives the real evaluation-continuity premise for the existing
integer free representable and its native scalar-quotient cokernel.

An explicitly supplied finite generator/relation cokernel presentation on
such objects therefore gives native finite presentability and literal
factorization of an original map through an original filtered cocone stage.
The coefficient and indexing size is one universe above schemes. No qcqs
condition on the base, modulus restriction, or existence of presentations
for constructible or finite locally constant sheaves is asserted.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.Sheaf.TorsionFinitePresentation

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Constructible

universe u

attribute [local instance] AlgebraicGeometry.Scheme.EtaleCohomology.hasSheafifyLarge

variable {X : Scheme.{u}}

/-- The actual set-valued evaluation on a qcqs original etale object preserves
filtered colimits in the coefficient/index universe, with its original maps. -/
theorem qcqsEvaluation_preservesFilteredColimits (U : X.Etale)
    [CompactSpace U.left] [QuasiSeparatedSpace U.left] :
    PreservesFilteredColimitsOfSize.{u + 1, u + 1}
      (Sheaf.TorsionFinitePresentation.evaluation.{u + 1} X.smallEtaleTopology U) where
  preserves_filtered_colimits I _ _ := by
    let : PreservesColimitsOfShape I
        ((sheafSections X.smallEtaleTopology AddCommGrpCat.{u + 1}).obj (op U)) :=
      Continuity.qcqsSectionsPreservesFilteredColimits (I := I) U
    change PreservesColimitsOfShape I
      (((sheafSections X.smallEtaleTopology AddCommGrpCat.{u + 1}).obj (op U)) ⋙
        CategoryTheory.forget AddCommGrpCat.{u + 1})
    infer_instance

/-- The existing original integer free representable on a qcqs etale object is compact. -/
theorem qcqs_freeAbelianSheaf_isFinitelyPresentable (U : X.Etale)
    [CompactSpace U.left] [QuasiSeparatedSpace U.left] :
    IsFinitelyPresentable.{u + 1}
      (Sheaf.Hypercohomology.freeAbelianSheaf.{u + 1} X.smallEtaleTopology U) :=
  isFinitelyPresentable_freeAbelianSheaf_of_evaluation.{u + 1, u + 1}
    X.smallEtaleTopology U (qcqsEvaluation_preservesFilteredColimits U)

/-- The actual free mod-n cokernel on a qcqs etale object is compact, including n = 0. -/
theorem qcqs_freeZModRepresentable_isFinitelyPresentable (n : ℕ) (U : X.Etale)
    [CompactSpace U.left] [QuasiSeparatedSpace U.left] :
    IsFinitelyPresentable.{u + 1}
      (freeZModRepresentable.{u + 1} X.smallEtaleTopology n U) :=
  isFinitelyPresentable_freeZModRepresentable_of_evaluation.{u + 1, u + 1}
    X.smallEtaleTopology n U (qcqsEvaluation_preservesFilteredColimits U)

/-- Finite sums of the original scalar-quotient generators on qcqs objects are compact. -/
theorem qcqs_finiteFreeZMod_isFinitelyPresentable (n : ℕ) {r : ℕ}
    (U : Fin r → X.Etale) [∀ i, CompactSpace (U i).left]
    [∀ i, QuasiSeparatedSpace (U i).left] :
    IsFinitelyPresentable.{u + 1} (finiteFreeZMod.{u + 1} X.smallEtaleTopology n U) :=
  isFinitelyPresentable_finiteFreeZMod_of_evaluation.{u + 1, u + 1}
    X.smallEtaleTopology n U (fun i => qcqsEvaluation_preservesFilteredColimits (U i))

/-- Actual finite generator/relation cokernel data on qcqs objects prove compactness.
The presentation remains explicit data; no constructible-presentation existence is used. -/
theorem isFinitelyPresentable_of_qcqs_finiteZModPresentation (n : ℕ) {r0 r1 : ℕ}
    (U0 : Fin r0 → X.Etale) (U1 : Fin r1 → X.Etale)
    [∀ i, CompactSpace (U0 i).left] [∀ i, QuasiSeparatedSpace (U0 i).left]
    [∀ j, CompactSpace (U1 j).left] [∀ j, QuasiSeparatedSpace (U1 j).left]
    {F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}}
    (d : finiteFreeZMod.{u + 1} X.smallEtaleTopology n U1 ⟶
      finiteFreeZMod.{u + 1} X.smallEtaleTopology n U0)
    (q : finiteFreeZMod.{u + 1} X.smallEtaleTopology n U0 ⟶ F)
    (hdq : d ≫ q = 0) (hq : IsColimit (CokernelCofork.ofπ q hdq)) :
    IsFinitelyPresentable.{u + 1} F :=
  isFinitelyPresentable_of_finiteZModPresentation.{u + 1, u + 1}
    X.smallEtaleTopology n U0 U1
    (fun i => qcqsEvaluation_preservesFilteredColimits (U0 i))
    (fun j => qcqsEvaluation_preservesFilteredColimits (U1 j)) d q hdq hq

/-- The original map from an explicitly presented sheaf factors through an original stage. -/
theorem exists_factor_of_qcqs_finiteZModPresentation (n : ℕ) {r0 r1 : ℕ}
    (U0 : Fin r0 → X.Etale) (U1 : Fin r1 → X.Etale)
    [∀ i, CompactSpace (U0 i).left] [∀ i, QuasiSeparatedSpace (U0 i).left]
    [∀ j, CompactSpace (U1 j).left] [∀ j, QuasiSeparatedSpace (U1 j).left]
    {F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}}
    (d : finiteFreeZMod.{u + 1} X.smallEtaleTopology n U1 ⟶
      finiteFreeZMod.{u + 1} X.smallEtaleTopology n U0)
    (q : finiteFreeZMod.{u + 1} X.smallEtaleTopology n U0 ⟶ F)
    (hdq : d ≫ q = 0) (hq : IsColimit (CokernelCofork.ofπ q hdq))
    {I : Type (u + 1)} [SmallCategory I] [IsFiltered I]
    {D : I ⥤ Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}}
    {c : Cocone D} (hc : IsColimit c) (a : F ⟶ c.pt) :
    ∃ i, ∃ b : F ⟶ D.obj i, b ≫ c.ι.app i = a :=
  exists_factor_of_finiteZModPresentation.{u + 1, u + 1}
    X.smallEtaleTopology n U0 U1
    (fun i => qcqsEvaluation_preservesFilteredColimits (U0 i))
    (fun j => qcqsEvaluation_preservesFilteredColimits (U1 j)) d q hdq hq hc a

/-- The literal original Hom functor preserves the original filtered cocone of coefficients. -/
def homCoconeIsColimitOfQcqsFiniteZModPresentation (n : ℕ) {r0 r1 : ℕ}
    (U0 : Fin r0 → X.Etale) (U1 : Fin r1 → X.Etale)
    [∀ i, CompactSpace (U0 i).left] [∀ i, QuasiSeparatedSpace (U0 i).left]
    [∀ j, CompactSpace (U1 j).left] [∀ j, QuasiSeparatedSpace (U1 j).left]
    {F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}}
    (d : finiteFreeZMod.{u + 1} X.smallEtaleTopology n U1 ⟶
      finiteFreeZMod.{u + 1} X.smallEtaleTopology n U0)
    (q : finiteFreeZMod.{u + 1} X.smallEtaleTopology n U0 ⟶ F)
    (hdq : d ≫ q = 0) (hq : IsColimit (CokernelCofork.ofπ q hdq))
    {I : Type (u + 1)} [SmallCategory I] [IsFiltered I]
    {D : I ⥤ Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}}
    {c : Cocone D} (hc : IsColimit c) :
    IsColimit ((coyoneda.obj (op F)).mapCocone c) :=
  homCoconeIsColimitOfFiniteZModPresentation.{u + 1, u + 1}
    X.smallEtaleTopology n U0 U1
    (fun i => qcqsEvaluation_preservesFilteredColimits (U0 i))
    (fun j => qcqsEvaluation_preservesFilteredColimits (U1 j)) d q hdq hq hc

end AlgebraicGeometry.Scheme.EtaleCohomology.Constructible
