/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Continuity.DiagramCohomologyConnecting
public import Aglib.AlgebraicGeometry.EtaleCohomology.Continuity.DiagramCohomologyNaturality

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

/-- The original varying-site fragment Hⁿ(Q) → Hⁿ(coker η) → Hⁿ⁺¹(F). -/
def diagramCohomologyConnectingComplex : ShortComplex (I ⥤ AddCommGrpCat.{e}) where
  f := diagramCohomologyNatTrans X n
    (InjectiveSystem.System.cokernelπ (diagramAdjunctionData X) η)
  g := diagramCohomologyConnecting X η hη n
  zero := by
    apply NatTrans.ext
    funext i
    exact (Sheaf.H.longSequence_exact
      (diagramCokernelComplex_shortExact X η hη i) n (n + 1) rfl).zero 1

/-- Exactness is the original stage cohomology theorem at every index. -/
lemma diagramCohomologyConnectingComplex_exact :
    (diagramCohomologyConnectingComplex X η hη n).Exact := by
  apply ShortComplex.exact_of_evaluation
  intro i
  exact Sheaf.H.longSequence_exact₃'
    (diagramCokernelComplex_shortExact X η hη i) n (n + 1) rfl

variable [HasColimitsOfShape I AddCommGrpCat.{e}]

private abbrev exactCohomologyFilteredColimits [IsFiltered I] :
    HasExactColimitsOfShape I AddCommGrpCat.{e} := by
  let E : I ≌ AsSmall.{max e uI vI} I := AsSmall.equiv (C := I)
  have : IsFiltered (AsSmall.{max e uI vI} I) := IsFiltered.of_equivalence E
  let : HasExactColimitsOfShape I AddCommGrpCat.{max e uI vI} :=
    HasExactColimitsOfShape.of_domain_equivalence AddCommGrpCat.{max e uI vI} E.symm
  exact HasExactColimitsOfShape.domain_of_functor I AddCommGrpCat.uliftFunctor.{max uI vI, e}

/-- The actual colimit of the varying-site fragment is exact. -/
lemma diagramCohomologyConnectingComplex_colimit_exact [IsFiltered I] :
    ((diagramCohomologyConnectingComplex X η hη n).map colim).Exact := by
  let : HasExactColimitsOfShape I AddCommGrpCat.{e} := exactCohomologyFilteredColimits
  exact (diagramCohomologyConnectingComplex_exact X η hη n).map colim

variable (c : Cocone X) [HasExt.{e} (AbelianSheaf.{u, u + 1} c.pt.unop)]
  [IsFiltered I] [HasColimitsOfShape I AddCommGrpCat.{u + 1}]

/-- The original corresponding fragment on the actual limit coefficients. -/
def limitCohomologyConnectingComplex : ShortComplex AddCommGrpCat.{e} :=
  ShortComplex.mk
    (AddCommGrpCat.ofHom (Sheaf.H.map (coneCoefficientColimitCokernelComplex X c η).g n))
    (AddCommGrpCat.ofHom
      (Sheaf.H.δ (coneCoefficientColimitCokernelComplex_shortExact X c η hη)
        n (n + 1) rfl))
    ((Sheaf.H.longSequence_exact
      (coneCoefficientColimitCokernelComplex_shortExact X c η hη) n (n + 1) rfl).zero 1)

omit [∀ i, HasExt.{e} (AbelianSheaf.{u, u + 1} (X.obj i).unop)]
  [HasColimitsOfShape I AddCommGrpCat.{e}] in
lemma limitCohomologyConnectingComplex_exact :
    (limitCohomologyConnectingComplex X η hη n c).Exact :=
  Sheaf.H.longSequence_exact₃'
    (coneCoefficientColimitCokernelComplex_shortExact X c η hη) n (n + 1) rfl

/-- The three literal comparison maps form a morphism between the original exact rows. -/
def diagramCohomologyConnectingComparison :
    (diagramCohomologyConnectingComplex X η hη n).map colim ⟶
      limitCohomologyConnectingComplex X η hη n c where
  τ₁ := schemeLimitCohomologyComparison X c Q n
  τ₂ := schemeLimitCohomologyComparison X c (diagramCokernelSystem X η) n
  τ₃ := schemeLimitCohomologyComparison X c F (n + 1)
  comm₁₂ := (schemeLimitCohomologyComparison_naturality X c
    (InjectiveSystem.System.cokernelπ (diagramAdjunctionData X) η) n).symm
  comm₂₃ := (schemeLimitCohomologyComparison_connecting X η hη n c).symm

end AlgebraicGeometry.Scheme.EtaleCohomology.Continuity
