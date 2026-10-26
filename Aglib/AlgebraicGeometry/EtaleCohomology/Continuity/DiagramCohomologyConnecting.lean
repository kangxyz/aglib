/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Continuity.CohomologyConnectingTransfer
public import Aglib.AlgebraicGeometry.EtaleCohomology.Continuity.DiagramCohomologyCocone
public import Aglib.AlgebraicGeometry.EtaleCohomology.Continuity.DiagramCokernelTransitions

/-! # Original connecting squares for the scheme-limit comparison

All sequences, stage transitions, limit injections, and connecting homomorphisms
are the original ones. This establishes compatibility, not invertibility.
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

/-- The original pointwise connecting homomorphisms form a natural transformation. -/
def diagramCohomologyConnecting :
    diagramCohomologyFunctor X (diagramCokernelSystem X η) n ⟶
      diagramCohomologyFunctor X F (n + 1) where
  app i := AddCommGrpCat.ofHom
    (Sheaf.H.δ (diagramCokernelComplex_shortExact X η hη i) n (n + 1) rfl)
  naturality i j a := by
    change diagramCohomologyMap X (diagramCokernelSystem X η) n a ≫ _ =
      _ ≫ diagramCohomologyMap X F (n + 1) a
    simp only [diagramCohomologyMap_eq_transfer]
    exact (cohomologyTransfer_connecting
      (X := (X.obj i).unop) (Y := (X.obj j).unop) (X.map a).unop
      (diagramCokernelComplex X η i) (diagramCokernelComplex X η j)
      (diagramCokernelComplex_shortExact X η hη i)
      (diagramCokernelComplex_shortExact X η hη j)
      (diagramCokernelTransition X η a) n).symm

variable (c : Cocone X) [HasExt.{e} (AbelianSheaf.{u, u + 1} c.pt.unop)]
  [IsFiltered I] [HasColimitsOfShape I AddCommGrpCat.{u + 1}]

/-- Each original stage-to-limit leg respects the original connecting map. -/
lemma diagramCohomologyLeg_connecting (i : I) :
    AddCommGrpCat.ofHom
        (Sheaf.H.δ (diagramCokernelComplex_shortExact X η hη i) n (n + 1) rfl) ≫
      diagramCohomologyLeg X c F (n + 1) i =
    diagramCohomologyLeg X c (diagramCokernelSystem X η) n i ≫
      AddCommGrpCat.ofHom
        (Sheaf.H.δ (coneCoefficientColimitCokernelComplex_shortExact X c η hη)
          n (n + 1) rfl) :=
  cohomologyTransfer_connecting (X := (X.obj i).unop) (Y := c.pt.unop)
    (c.ι.app i).unop
    (diagramCokernelComplex X η i) (coneCoefficientColimitCokernelComplex X c η)
    (diagramCokernelComplex_shortExact X η hη i)
    (coneCoefficientColimitCokernelComplex_shortExact X c η hη)
    (diagramCokernelLimitLeg X η c i) n

variable [HasColimitsOfShape I AddCommGrpCat.{e}]

/-- The literal scheme-limit comparison commutes with the original connecting homomorphisms. -/
lemma schemeLimitCohomologyComparison_connecting :
    colim.map (diagramCohomologyConnecting X η hη n) ≫
      schemeLimitCohomologyComparison X c F (n + 1) =
    schemeLimitCohomologyComparison X c (diagramCokernelSystem X η) n ≫
      AddCommGrpCat.ofHom
        (Sheaf.H.δ (coneCoefficientColimitCokernelComplex_shortExact X c η hη)
          n (n + 1) rfl) := by
  apply colimit.hom_ext
  intro i
  let δ : AddCommGrpCat.of
      (Sheaf.H.{e} (colimit (coneCoefficientFunctor X c (diagramCokernelSystem X η))) n) ⟶
      AddCommGrpCat.of (Sheaf.H.{e} (colimit (coneCoefficientFunctor X c F)) (n + 1)) :=
    AddCommGrpCat.ofHom
      (Sheaf.H.δ (coneCoefficientColimitCokernelComplex_shortExact X c η hη)
        n (n + 1) rfl)
  have hr : colimit.ι (diagramCohomologyFunctor X (diagramCokernelSystem X η) n) i ≫
      (schemeLimitCohomologyComparison X c (diagramCokernelSystem X η) n ≫ δ) =
        diagramCohomologyLeg X c (diagramCokernelSystem X η) n i ≫ δ :=
    (Category.assoc _ _ _).symm.trans
      (congrArg (fun k => k ≫ δ)
        (ι_schemeLimitCohomologyComparison X c (diagramCokernelSystem X η) n i))
  rw [colimit.ι_map_assoc, ι_schemeLimitCohomologyComparison]
  exact (diagramCohomologyLeg_connecting X η hη n c i).trans hr.symm

end AlgebraicGeometry.Scheme.EtaleCohomology.Continuity
