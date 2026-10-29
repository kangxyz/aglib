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

attribute [local instance] diagramLeftAdditive diagramLeftPreservesFiniteLimits
  diagramLeftPreservesFiniteColimits diagramIntegerCartesian

/-- The original pointwise connecting maps are the native represented Ext transformation. -/
abbrev diagramCohomologyConnecting :
    diagramCohomologyFunctor X (diagramCokernelSystem X η) n ⟶
      diagramCohomologyFunctor X F (n + 1) :=
  InjectiveSystem.representedCohomologyConnecting (diagramAdjunctionData X) η
    (diagramIntegerSystem X) hη n

variable (c : Cocone X) [HasExt.{e} (AbelianSheaf.{u, u + 1} c.pt.unop)]
  [IsFiltered I] [HasColimitsOfShape I AddCommGrpCat.{u + 1}]

/-- The original constant-source inverse transport at the literal representing objects. -/
abbrev diagramIntegerConePrecomp (i : I) :
    ((constantSheaf (Scheme.smallEtaleTopology c.pt.unop) AddCommGrpCat.{u + 1}).obj
      (AddCommGrpCat.of (ULift.{u + 1} ℤ))) ⟶
      (inverseImage (c.ι.app i).unop).obj ((diagramIntegerSystem X).obj i) := by
  dsimp only [diagramIntegerSystem, InjectiveSystem.System.ofLeft]
  exact (inverseImageConstantIso (c.ι.app i).unop).inv.app
    (AddCommGrpCat.of (ULift.{u + 1} ℤ))

/-- Each original stage-to-limit leg respects the original connecting map. -/
lemma diagramCohomologyLeg_connecting (i : I) :
    AddCommGrpCat.ofHom
        (Sheaf.H.δ (diagramCokernelComplex_shortExact X η hη i) n (n + 1) rfl) ≫
      diagramCohomologyLeg X c F (n + 1) i =
    diagramCohomologyLeg X c (diagramCokernelSystem X η) n i ≫
      AddCommGrpCat.ofHom
        (Sheaf.H.δ (coneCoefficientColimitCokernelComplex_shortExact X c η hη)
          n (n + 1) rfl) := by
  letI connectingLegApexExt : HasExt.{e} (AbelianSheaf.{u, u + 1}
      (((Functor.const I).obj c.pt).obj i).unop) :=
    inferInstanceAs (HasExt.{e} (AbelianSheaf.{u, u + 1} c.pt.unop))
  exact Functor.extPrecompMap_connecting_naturality
    (C := AbelianSheaf.{u, u + 1} (X.obj i).unop)
    (B := AbelianSheaf.{u, u + 1} c.pt.unop)
    (X := (diagramIntegerSystem X).obj i)
    (V := (constantSheaf (Scheme.smallEtaleTopology c.pt.unop) AddCommGrpCat.{u + 1}).obj
      (AddCommGrpCat.of (ULift.{u + 1} ℤ)))
    (inverseImage (c.ι.app i).unop) (diagramIntegerConePrecomp X c i)
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
  exact InjectiveSystem.representedCohomologyConnecting_colimit_connecting
    (B := AbelianSheaf.{u, u + 1} c.pt.unop)
    (diagramAdjunctionData X) η (diagramIntegerSystem X) hη n
    (fun i => inverseImage (c.ι.app i).unop)
    ((constantSheaf (Scheme.smallEtaleTopology c.pt.unop) AddCommGrpCat.{u + 1}).obj
      (AddCommGrpCat.of (ULift.{u + 1} ℤ)))
    (diagramIntegerConePrecomp X c)
    (coneCoefficientColimitCokernelComplex_shortExact X c η hη)
    (diagramCokernelLimitLeg X η c)
    (schemeLimitCohomologyComparison X c F (n + 1))
    (schemeLimitCohomologyComparison X c (diagramCokernelSystem X η) n)
    (ι_schemeLimitCohomologyComparison X c F (n + 1))
    (ι_schemeLimitCohomologyComparison X c (diagramCokernelSystem X η) n)

end AlgebraicGeometry.Scheme.EtaleCohomology.Continuity
