/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Morphisms.FormallyUnramified.SectionDescent
public import Aglib.AlgebraicGeometry.EtaleCohomology.H1.RepresentedBaseChange
public import Aglib.AlgebraicGeometry.EtaleCohomology.H1.CoefficientRepresentation
public import Aglib.AlgebraicGeometry.EtaleCohomology.H1.FiniteSetRepresentation
public import Aglib.AlgebraicGeometry.EtaleCohomology.H1.DegreeZeroPullback

/-! # Original H0 under flat geometrically connected pullback

Actual section descent proves that the original inverse-image adjunction unit
is invertible for finite locally constant coefficients. The represented unit
is the existing scheme-section pullback, and its comparison with inverse image
is the existing canonical comparison. Flat quasi-compact or flat locally
finitely presented morphisms supply the descent hypotheses on every etale test.
No cohomology model, coefficient-order condition or smooth base-change theorem
is assumed or constructed here.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.MonObj

universe u w w'

namespace AlgebraicGeometry.Scheme.EtaleCohomology.GeometricallyConnectedH0

attribute [local instance] hasSheafifyLarge

variable {X Y : Scheme.{u}} (q : Y ⟶ X) [GeometricallyConnected q]
  (hE : ∀ U : X.Etale, EffectiveEpi (pullback.fst U.hom q))

include hE

/-- Section descent on the actual etale tests proves invertibility of the
literal represented coefficient unit. Finiteness is not needed here. -/
theorem representedCoefficientUnit_isIso (A : Grp (Over X))
    [IsCommMonObj A.X] [Etale A.X.hom] [IsSeparated A.X.hom] :
    IsIso (SchemeTorsorBaseChange.representedCoefficientUnit q A) := by
  rw [← ObjectProperty.isIso_hom_iff, NatTrans.isIso_iff_isIso_app]
  intro U
  let : EffectiveEpi
      (pullback.fst ((Scheme.Etale.forget X).obj U.unop).hom q) := by
    change EffectiveEpi (pullback.fst U.unop.hom q)
    exact hE U.unop
  apply (ConcreteCategory.isIso_iff_bijective (C := AddCommGrpCat.{u + 1}) _).mpr
  have hmap := Scheme.Hom.bijective_overPullback_map q
    ((Scheme.Etale.forget X).obj U.unop) A.X
  constructor
  · intro a b hab
    apply ULift.ext
    apply Additive.toMul.injective
    apply hmap.injective
    exact congrArg (fun z => z.down.toMul) hab
  · intro b
    obtain ⟨a, ha⟩ := hmap.surjective b.down.toMul
    refine ⟨ULift.up (Additive.ofMul a), ?_⟩
    apply ULift.ext
    apply Additive.toMul.injective
    exact ha

/-- The original represented-sheaf unit equation identifies the proved
section descent with the actual inverse-image adjunction unit. -/
theorem representedAdjunctionUnit_isIso (A : Grp (Over X))
    [IsCommMonObj A.X] [Etale A.X.hom] [IsSeparated A.X.hom] :
    IsIso ((inverseImageAdjunction q).unit.app (representedSheaf A)) := by
  let e := representedSheafBaseChangeIso q A
  let := representedCoefficientUnit_isIso q hE A
  have hu : (inverseImageAdjunction q).unit.app (representedSheaf A) ≫
      (directImage q).map e.hom =
        SchemeTorsorBaseChange.representedCoefficientUnit q A :=
    SchemeTorsorBaseChange.representedSheafBaseChangeIso_unit q A
  have : IsIso ((inverseImageAdjunction q).unit.app (representedSheaf A) ≫
      (directImage q).map e.hom) := by
    rw [hu]
    infer_instance
  exact IsIso.of_isIso_comp_right _ ((directImage q).map e.hom)

/-- Finite local constancy constructs the coefficient representative; the
original unit is transported through its actual coefficient isomorphism. -/
theorem adjunctionUnit_isIso (F : AbelianSheaf.{u, u + 1} X)
    (hF : IsFiniteLocallyConstant F) :
    IsIso ((inverseImageAdjunction q).unit.app F) := by
  let r := CoefficientRepresentation.ofFiniteLocallyConstant F (stacks03RV X) hF
  let := representedAdjunctionUnit_isIso q hE r.group
  exact (NatTrans.isIso_app_iff_of_iso (inverseImageAdjunction q).unit r.iso).mp
    inferInstance

/-- The existing global-section pullback is invertible, not a replacement
bijection between independently represented section groups. -/
theorem globalSectionsPullback_isIso (F : AbelianSheaf.{u, u + 1} X)
    (hF : IsFiniteLocallyConstant F) : IsIso (globalSectionsPullback q F) := by
  let := adjunctionUnit_isIso q hE F hF
  dsimp only [globalSectionsPullback]
  infer_instance

/-- The original Ext-defined H0 pullback is bijective, with independent Ext
universes and its existing terminal-section normalization. -/
theorem h0Pullback_bijective
    [HasExt.{w} (AbelianSheaf.{u, u + 1} X)]
    [HasExt.{w'} (AbelianSheaf.{u, u + 1} Y)]
    (F : AbelianSheaf.{u, u + 1} X) (hF : IsFiniteLocallyConstant F) :
    Function.Bijective (h0Pullback q F) := by
  let := globalSectionsPullback_isIso q hE F hF
  let eX := Sheaf.H.equiv₀ F (etaleTerminalIsTerminal X)
  let eY := Sheaf.H.equiv₀ ((inverseImage q).obj F) (etaleTerminalIsTerminal Y)
  have hs : eY ∘ h0Pullback q F = globalSectionsPullback q F ∘ eX :=
    funext (h0Pullback_equiv₀ q F)
  have hc : Function.Bijective (eY ∘ h0Pullback q F) := by
    rw [hs]
    exact (ConcreteCategory.bijective_of_isIso (globalSectionsPullback q F)).comp eX.bijective
  exact hc.of_comp_left eY.injective

end AlgebraicGeometry.Scheme.EtaleCohomology.GeometricallyConnectedH0

namespace AlgebraicGeometry.Scheme.EtaleCohomology

attribute [local instance] hasSheafifyLarge

variable {X Y : Scheme.{u}} (q : Y ⟶ X) [Flat q] [GeometricallyConnected q]

/-- Flat quasi-compact geometrically connected pullback preserves the original
unit for every finite locally constant coefficient. -/
theorem adjunctionUnit_isIso_of_flat_quasiCompact_geometricallyConnected
    [QuasiCompact q] (F : AbelianSheaf.{u, u + 1} X) (hF : IsFiniteLocallyConstant F) :
    IsIso ((inverseImageAdjunction q).unit.app F) :=
  GeometricallyConnectedH0.adjunctionUnit_isIso q (fun _ => inferInstance) F hF

/-- The fppf version does not require quasi-compactness. -/
theorem adjunctionUnit_isIso_of_flat_lfp_geometricallyConnected
    [LocallyOfFinitePresentation q]
    (F : AbelianSheaf.{u, u + 1} X) (hF : IsFiniteLocallyConstant F) :
    IsIso ((inverseImageAdjunction q).unit.app F) :=
  GeometricallyConnectedH0.adjunctionUnit_isIso q (fun _ => inferInstance) F hF

/-- Actual sections descend along flat quasi-compact geometrically connected maps. -/
theorem globalSectionsPullback_isIso_of_flat_quasiCompact_geometricallyConnected
    [QuasiCompact q] (F : AbelianSheaf.{u, u + 1} X) (hF : IsFiniteLocallyConstant F) :
    IsIso (globalSectionsPullback q F) :=
  GeometricallyConnectedH0.globalSectionsPullback_isIso q (fun _ => inferInstance) F hF

/-- Actual sections descend along flat locally finitely presented geometrically
connected maps, without a quasi-compactness condition. -/
theorem globalSectionsPullback_isIso_of_flat_lfp_geometricallyConnected
    [LocallyOfFinitePresentation q]
    (F : AbelianSheaf.{u, u + 1} X) (hF : IsFiniteLocallyConstant F) :
    IsIso (globalSectionsPullback q F) :=
  GeometricallyConnectedH0.globalSectionsPullback_isIso q (fun _ => inferInstance) F hF

/-- The original H0 map for the fpqc case. -/
theorem h0Pullback_bijective_of_flat_quasiCompact_geometricallyConnected
    [QuasiCompact q]
    [HasExt.{w} (AbelianSheaf.{u, u + 1} X)]
    [HasExt.{w'} (AbelianSheaf.{u, u + 1} Y)]
    (F : AbelianSheaf.{u, u + 1} X) (hF : IsFiniteLocallyConstant F) :
    Function.Bijective (h0Pullback q F) :=
  GeometricallyConnectedH0.h0Pullback_bijective q (fun _ => inferInstance) F hF

/-- The original H0 map for the fppf case. -/
theorem h0Pullback_bijective_of_flat_lfp_geometricallyConnected
    [LocallyOfFinitePresentation q]
    [HasExt.{w} (AbelianSheaf.{u, u + 1} X)]
    [HasExt.{w'} (AbelianSheaf.{u, u + 1} Y)]
    (F : AbelianSheaf.{u, u + 1} X) (hF : IsFiniteLocallyConstant F) :
    Function.Bijective (h0Pullback q F) :=
  GeometricallyConnectedH0.h0Pullback_bijective q (fun _ => inferInstance) F hF

end AlgebraicGeometry.Scheme.EtaleCohomology
