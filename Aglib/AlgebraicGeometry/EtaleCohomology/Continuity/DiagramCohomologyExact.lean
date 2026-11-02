/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Continuity.DiagramCohomologyConnecting
public import Aglib.AlgebraicGeometry.EtaleCohomology.Continuity.DiagramCohomologyNaturality
public import Aglib.CategoryTheory.Sites.SheafCohomology.Continuity.ShortComplexColimit

/-! # Actual long-exact-sequence fragments for varying étale sites

Exactness comes from the original stage long exact sequences and exact filtered
colimits of abelian groups. No vanishing of a limit coefficient is assumed.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme.EtaleCohomology.Continuity
universe u e uI vI
attribute [local instance] hasSheafifyLarge
variable {I : Type uI} [Category.{vI} I] (X : I ⥤ Scheme.{u}ᵒᵖ)
  [∀ i, HasExt.{e} (AbelianSheaf.{u, u + 1} (X.obj i).unop)]
  {F Q : DiagramCoefficientSystem X}
  (η : InjectiveSystem.System.Hom (diagramAdjunctionData X) F Q)
  (hη : ∀ i, Mono (η.app i)) (n : ℕ)

attribute [local instance] diagramLeftAdditive diagramLeftPreservesFiniteLimits
  diagramLeftPreservesFiniteColimits diagramIntegerCartesian

/-- The original varying-site fragment Hⁿ(Q) → Hⁿ(coker η) → Hⁿ⁺¹(F). -/
abbrev diagramCohomologyConnectingComplex : ShortComplex (I ⥤ AddCommGrpCat.{e}) :=
  InjectiveSystem.representedCohomologyConnectingComplex (diagramAdjunctionData X) η
    (diagramIntegerSystem X) hη n

/-- Exactness is the native Ext sequence at every original index. -/
lemma diagramCohomologyConnectingComplex_exact :
    (diagramCohomologyConnectingComplex X η hη n).Exact :=
  InjectiveSystem.representedCohomologyConnectingComplex_exact (diagramAdjunctionData X) η
    (diagramIntegerSystem X) hη n

variable [HasColimitsOfShape I AddCommGrpCat.{e}]

private abbrev exactCohomologyFilteredColimits [IsFiltered I] :
    HasExactColimitsOfShape I AddCommGrpCat.{e} := by
  exact hasExactFilteredColimitsOfShape_addCommGrpCat_of_category I

/-- The actual colimit of the varying-site fragment is exact. -/
lemma diagramCohomologyConnectingComplex_colimit_exact [IsFiltered I] :
    ((diagramCohomologyConnectingComplex X η hη n).map colim).Exact := by
  let : HasExactColimitsOfShape I AddCommGrpCat.{e} := exactCohomologyFilteredColimits
  exact InjectiveSystem.representedCohomologyConnectingComplex_colimit_exact
    (diagramAdjunctionData X) η (diagramIntegerSystem X) hη n

variable (c : Cocone X) [HasExt.{e} (AbelianSheaf.{u, u + 1} c.pt.unop)]
  [IsFiltered I] [HasColimitsOfShape I AddCommGrpCat.{u + 1}]

/-- The original corresponding fragment on the actual limit coefficients. -/
abbrev limitCohomologyConnectingComplex : ShortComplex AddCommGrpCat.{e} :=
  representedExtConnectingComplex
    ((constantSheaf (Scheme.smallEtaleTopology c.pt.unop) AddCommGrpCat.{u + 1}).obj
      (AddCommGrpCat.of (ULift.{u + 1} ℤ)))
    (coneCoefficientColimitCokernelComplex_shortExact X c η hη) n

omit [∀ i, HasExt.{e} (AbelianSheaf.{u, u + 1} (X.obj i).unop)]
  [HasColimitsOfShape I AddCommGrpCat.{e}] in
lemma limitCohomologyConnectingComplex_exact :
    (limitCohomologyConnectingComplex X η hη n c).Exact :=
  representedExtConnectingComplex_exact _
    (coneCoefficientColimitCokernelComplex_shortExact X c η hη) n

/-- The three literal comparison maps form a morphism between the original exact rows. -/
def diagramCohomologyConnectingComparison :
    (diagramCohomologyConnectingComplex X η hη n).map colim ⟶
      limitCohomologyConnectingComplex X η hη n c :=
  InjectiveSystem.representedCohomologyConnectingComparison
    (B := AbelianSheaf.{u, u + 1} c.pt.unop)
    (diagramAdjunctionData X) η (diagramIntegerSystem X) hη n
    (fun i => inverseImage (c.ι.app i).unop)
    ((constantSheaf (Scheme.smallEtaleTopology c.pt.unop) AddCommGrpCat.{u + 1}).obj
      (AddCommGrpCat.of (ULift.{u + 1} ℤ)))
    (diagramIntegerConePrecomp X c)
    (coneCoefficientColimitCokernelComplex_shortExact X c η hη)
    (diagramCokernelLimitLeg X η c)
    (schemeLimitCohomologyComparison X c Q n)
    (schemeLimitCohomologyComparison X c (diagramCokernelSystem X η) n)
    (schemeLimitCohomologyComparison X c F (n + 1))
    (ι_schemeLimitCohomologyComparison X c Q n)
    (ι_schemeLimitCohomologyComparison X c (diagramCokernelSystem X η) n)
    (ι_schemeLimitCohomologyComparison X c F (n + 1))

end AlgebraicGeometry.Scheme.EtaleCohomology.Continuity
