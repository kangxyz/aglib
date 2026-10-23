/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Continuity.QcqsAcyclic
public import Aglib.CategoryTheory.Sites.SheafCohomology.Continuity.FiniteCoefficientContinuity

/-! # Canonical coefficient continuity on qcqs schemes

This is continuity in coefficients on the original fixed small étale site.
It is not the varying-scheme inverse-limit continuity theorem.
-/

@[expose] public noncomputable section

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Continuity

universe u e

attribute [local instance] hasSheafifyLarge

variable {S : Scheme.{u}} [CompactSpace S] [QuasiSeparatedSpace S]
  {I : Type (u + 1)} [SmallCategory I] [IsFiltered I]
  [HasExt.{e} (AbelianSheaf.{u, u + 1} S)]
  [HasColimitsOfShape I AddCommGrpCat.{e}]

/-- Filtered coefficient colimits commute with original étale cohomology
on a qcqs scheme, through the original coefficient-colimit comparison. -/
theorem isIso_qcqsCoefficientColimitComparison
    (G : I ⥤ AbelianSheaf.{u, u + 1} S) (n : ℕ) :
    IsIso (Sheaf.H.coefficientColimitComparison G n) := by
  let : CompactSpace (etaleTerminal S).left := by
    change CompactSpace S
    infer_instance
  let : QuasiSeparatedSpace (etaleTerminal S).left := by
    change QuasiSeparatedSpace S
    infer_instance
  let := qcqsSectionsPreservesFilteredColimits (I := I) (etaleTerminal S)
  let : PreservesColimitsOfShape I
      (Sheaf.functorH S.smallEtaleTopology 0 :
        AbelianSheaf.{u, u + 1} S ⥤ AddCommGrpCat.{e}) :=
    Sheaf.H.preservesColimitsOfShape_degreeZero
      (etaleTerminalIsTerminal S)
  let : HasExactColimitsOfShape I AddCommGrpCat.{e} :=
    hasExactFilteredColimitsOfShape_addCommGrpCat I
  apply Sheaf.H.isIso_coefficientColimitComparison_of_injective_colimit_acyclic
  intro Q hQ q x
  let (i : I) : Injective (Q.obj i) := hQ i
  exact qcqs_colimit_injective_cohomology_eq_zero Q q x

/-- The isomorphism whose forward map is the original universal comparison. -/
def qcqsCoefficientFilteredColimitIso
    (G : I ⥤ AbelianSheaf.{u, u + 1} S) (n : ℕ) :
    colimit (G ⋙ Sheaf.functorH S.smallEtaleTopology n) ≅
      (Sheaf.functorH S.smallEtaleTopology n).obj (colimit G) := by
  let := isIso_qcqsCoefficientColimitComparison G n
  exact asIso (Sheaf.H.coefficientColimitComparison G n)

/-- Normalization at every actual coefficient-diagram injection. -/
@[reassoc]
theorem ι_qcqsCoefficientFilteredColimitIso
    (G : I ⥤ AbelianSheaf.{u, u + 1} S) (n : ℕ) (i : I) :
    colimit.ι (G ⋙ Sheaf.functorH S.smallEtaleTopology n) i ≫
        (qcqsCoefficientFilteredColimitIso G n).hom =
      (Sheaf.functorH S.smallEtaleTopology n).map (colimit.ι G i) :=
  Sheaf.H.ι_coefficientColimitComparison G n i

end AlgebraicGeometry.Scheme.EtaleCohomology.Continuity
