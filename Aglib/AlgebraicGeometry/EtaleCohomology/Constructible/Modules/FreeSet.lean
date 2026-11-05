/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Category.ModuleCat.Sheaf.FreeRepresentable
public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.Modules.Basic
public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.PositivePresentation.FreeSet

/-! # Original free module sheaves on finite étale objects

Native adjunction uniqueness identifies the free module sheaf on original set
sheaves with original free representables and transports it through original
inverse images. Finite étale splitting supplies finite-type local constant
module values without assuming that their additive groups are finite.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Constructible.Modules

universe u

attribute [local instance] hasSheafifyLarge ModuleCat.Sheaf.hasSheafify

variable (R : Type (u + 1)) [Ring R]


private instance originalFree_isLeftAdjoint :
    (ModuleCat.freeWideFunctor.{u + 1, u + 1} R).IsLeftAdjoint :=
  (ModuleCat.freeWideForgetAdjunction.{u + 1, 0} R).isLeftAdjoint

/-- The native sheafified free-module functor on the original set sheaves. -/
def freeModuleOfSet (X : Scheme.{u}) : SetSheaf X ⥤ ModuleSheaf R X :=
  Sheaf.composeAndSheafify X.smallEtaleTopology (ModuleCat.freeWideFunctor.{u + 1, u + 1} R)

/-- Its original module-valued free/forgetful adjunction. -/
def freeModuleOfSetAdj (X : Scheme.{u}) :
    freeModuleOfSet R X ⊣
      sheafCompose X.smallEtaleTopology (CategoryTheory.forget (ModuleCat.{u + 1} R)) :=
  Sheaf.adjunction X.smallEtaleTopology (ModuleCat.freeWideForgetAdjunction.{u + 1, 0} R)

/-- Original scheme inverse image commutes with the original free module functor. -/
def freeModuleOfSetInverseImageIso {X S : Scheme.{u}} (f : S ⟶ X) :
    freeModuleOfSet R X ⋙ moduleInverseImage R f ≅
      setInverseImage f ⋙ freeModuleOfSet R S :=
  ((freeModuleOfSetAdj R X).comp (moduleImageAdjunction R f)).leftAdjointUniq
    ((setInverseImageAdjunction f).comp (freeModuleOfSetAdj R S))

/-- Original constant set values become original constant free modules. -/
def freeModuleOfSetConstantIso (X : Scheme.{u}) :
    constantSheaf X.smallEtaleTopology (Type (u + 1)) ⋙ freeModuleOfSet R X ≅
      ModuleCat.freeWideFunctor.{u + 1, u + 1} R ⋙
        constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} R) :=
  ((constantSheafAdj X.smallEtaleTopology (Type (u + 1))
    (etaleTerminalIsTerminal X)).comp (freeModuleOfSetAdj R X)).leftAdjointUniq
      ((ModuleCat.freeWideForgetAdjunction.{u + 1, 0} R).comp
        (constantSheafAdj X.smallEtaleTopology (ModuleCat.{u + 1} R)
          (etaleTerminalIsTerminal X)))

/-- Actual finite set charts give finite-type module charts over the same ring. -/
theorem freeModuleOfSet_isFiniteTypeLocallyConstant (X : Scheme.{u})
    {F : SetSheaf X} (hF : IsFiniteLocallyConstantSet F) :
    IsFiniteTypeLocallyConstant ((freeModuleOfSet R X).obj F) := by
  obtain ⟨t⟩ := hF
  refine ⟨{
    index := t.index
    chart := t.chart
    covers := t.covers
    value := fun i => ModuleCat.freeWide R (t.value i)
    finite_value := ?_
    trivialization := fun i =>
      (freeModuleOfSetInverseImageIso R (t.chart i).hom).app F ≪≫
        (freeModuleOfSet R (t.chart i).left).mapIso (t.trivialization i) ≪≫
        (freeModuleOfSetConstantIso R (t.chart i).left).app (t.value i) }⟩
  intro i
  let := t.finite_value i
  change Module.Finite R ((t.value i) →₀ R)
  infer_instance

/-- Native sheafification identifies the selected original free representable. -/
def freeModuleOfSetRepresentableIso (X : Scheme.{u}) (U : X.Etale) :
    (freeModuleOfSet R X).obj (PositivePresentation.sheafifiedEtaleRepresentable X U) ≅
      ModuleCat.Sheaf.freeRepresentable.{u + 1, u + 1, u, 0} X.smallEtaleTopology R U := by
  let : X.smallEtaleTopology.PreservesSheafification
      (ModuleCat.freeWideFunctor.{u + 1, u + 1} R) :=
    Sheaf.preservesSheafification_of_adjunction X.smallEtaleTopology
      (ModuleCat.freeWideForgetAdjunction.{u + 1, 0} R)
  exact (presheafToSheafCompComposeAndSheafifyIso X.smallEtaleTopology
    (ModuleCat.freeWideFunctor.{u + 1, u + 1} R)).app (uliftYoneda.{u + 1}.obj U)

/-- Original free modules on finite étale objects are finite-type locally
constant, including empty bases and zero-rank fibres. -/
theorem finiteEtale_freeModule_isFiniteTypeLocallyConstant
    {X : Scheme.{u}} (Y : Scheme.FiniteEtale X) :
    IsFiniteTypeLocallyConstant
      (ModuleCat.Sheaf.freeRepresentable.{u + 1, u + 1, u, 0} X.smallEtaleTopology R
      ((Scheme.FiniteEtale.toEtale X).obj Y)) := by
  let e := (freeModuleOfSetRepresentableIso R X
    ((Scheme.FiniteEtale.toEtale X).obj Y)).symm ≪≫
      (freeModuleOfSet R X).mapIso (PositivePresentation.sheafifiedFiniteEtaleRepresentableIso Y)
  exact (isFiniteTypeLocallyConstant_iff_of_iso e).mpr
    (freeModuleOfSet_isFiniteTypeLocallyConstant R X
      (Scheme.FiniteEtale.finiteRepresentedSetSheaf_isFiniteLocallyConstant Y))

end AlgebraicGeometry.Scheme.EtaleCohomology.Constructible.Modules
