/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.Modules.FinitePresentation.Basic
public import Aglib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent.Pushforward
/-!
# Finite presentation is local on actual open covers

Finite local presentations are transported by the geometric restriction and
by the equivalence between opens of an open subscheme and the over-site.
Their covers can be composed, giving locality on a binary open cover.
-/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u w w' t t'
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace

namespace AlgebraicGeometry.Scheme.Modules


/-- Actual open restriction preserves finite local presentation. -/
theorem finitePresentation_restrict {U X : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] (M : X.Modules) [M.IsFinitePresentation] :
    (M.restrict j).IsFinitePresentation := by
  let α : U.presheaf ⟶ j.opensFunctor.op ⋙ X.presheaf := { app V := (j.appIso V.unop).inv }
  have hα : IsIso α := NatIso.isIso_of_isIso_app _
  let φ : U.ringCatSheaf ⟶
      (j.opensFunctor.sheafPushforwardContinuous _ _ _).obj X.ringCatSheaf :=
    ⟨Functor.whiskerRight α (forget₂ CommRingCat RingCat)⟩
  have : IsIso φ := by
    rw [← isIso_iff_of_reflects_iso _ (ObjectProperty.ι _)]
    dsimp [φ]
    infer_instance
  exact SheafOfModules.finitePresentation_pushforward_of_isLeftAdjoint j.opensFunctor φ
    (Scheme.Modules.restrictUnitIso j) M

/-- Finite presentation transports from an open subscheme to its over-site. -/
theorem finitePresentation_over_of_restrict {X : Scheme.{u}} (M : X.Modules)
    (U : X.Opens) [(M.restrict U.ι).IsFinitePresentation] :
    (M.over U).IsFinitePresentation := by
  let E := Scheme.Modules.overEquiv U
  let φ := (U.sheafRestrictSheafEquivOver.app X.ringCatSheaf).inv
  have := U.instIsDenseSubsiteOverSubtypeMemOverGrothendieckTopologyFunctorOverEquivalence
  have : U.overEquivalence.functor.IsContinuous
      ((Opens.grothendieckTopology X).over U) (Opens.grothendieckTopology U.toScheme) :=
    inferInstanceAs (U.overEquivalence.functor.IsContinuous
      ((Opens.grothendieckTopology X).over U) (Opens.grothendieckTopology U.carrier))
  have : Functor.PreservesOneHypercovers.{u} U.overEquivalence.functor
      ((Opens.grothendieckTopology X).over U) (Opens.grothendieckTopology U.toScheme) :=
    Functor.PreservesOneHypercovers.of_coverPreserving
      (CoverPreserving.of_isContinuous _ _ _)
  have hpost (A : Over U) :
      (Over.post (X := A) U.overEquivalence.functor).IsContinuous
        (((Opens.grothendieckTopology X).over U).over A)
        ((Opens.grothendieckTopology U.toScheme).over (U.overEquivalence.functor.obj A)) := by
    exact Functor.isContinuous_of_preservesOneHypercovers _ _ _
  have h : (E.inverse.obj (M.restrict U.ι)).IsFinitePresentation :=
    SheafOfModules.finitePresentation_pushforward_of_isLeftAdjoint (hpost := hpost)
      U.overEquivalence.functor φ
      (U.sheafOfModulesEquivOverInverseUnit X.ringCatSheaf) _
  let e : E.inverse.obj (M.restrict U.ι) ≅ M.over U :=
    (E.inverse.mapIso ((Scheme.Modules.overFunctorEquiv U).app M)).symm ≪≫
      (E.unitIso.app (M.over U)).symm
  exact (SheafOfModules.isFinitePresentation (X.ringCatSheaf.over U)).prop_of_iso e h

/-- Actual finite local presentations compose over an arbitrary open cover. -/
theorem finitePresentation_of_openCover {X : Scheme.{u}} (M : X.Modules)
    {ι : Type u} (U : ι → X.Opens) (hU : IsOpenCover U)
    (hM : ∀ i, (M.restrict (U i).ι).IsFinitePresentation) :
    M.IsFinitePresentation := by
  classical
  have h (i : ι) : (M.over (U i)).IsFinitePresentation := by
    have := hM i
    exact finitePresentation_over_of_restrict M (U i)
  have hc : (Opens.grothendieckTopology X).CoversTop U :=
    (Opens.coversTop_iff X U).mpr hU
  have hqex (i : ι) :=
    SheafOfModules.IsFinitePresentation.exists_quasicoherentData (M.over (U i))
  choose q hq using hqex
  let q' := SheafOfModules.QuasicoherentData.bind M U hc q
  refine SheafOfModules.IsFinitePresentation.mk (M := M) ⟨q', ?_⟩
  constructor
  intro i
  dsimp [q', SheafOfModules.QuasicoherentData.bind]
  infer_instance

end AlgebraicGeometry.Scheme.Modules
