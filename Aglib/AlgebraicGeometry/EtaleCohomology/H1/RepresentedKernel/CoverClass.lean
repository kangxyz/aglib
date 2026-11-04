/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.H1.RepresentedKernel.Marked
public import Aglib.AlgebraicGeometry.EtaleCohomology.H1.RepresentedMultiplicationBaseChange
public import Aglib.AlgebraicGeometry.EtaleCohomology.H1.RepresentedTorsor
public import Aglib.AlgebraicGeometry.EtaleCohomology.H1.TorsorBaseChange
public import Aglib.AlgebraicGeometry.Group.BaseChange.MarkedKernel
public import Aglib.AlgebraicGeometry.Torsors.Restriction.Graph
public import Aglib.CategoryTheory.Sites.Torsor.SectionClass

/-! The original class of a relative cover at the target diagonal. -/

open CategoryTheory CategoryTheory.Limits Opposite
open MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.MonObj

@[expose] public noncomputable section

namespace AlgebraicGeometry.Scheme.EtaleCohomology.RepresentedKernel

open Scheme.Group Scheme.Group.BaseChange Scheme.Torsors.Restriction

universe u w

attribute [local instance] Over.cartesianMonoidalCategory hasSheafifyLarge
  groupSchemeBaseChange_isCommMonObj

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {S : Scheme.{u}} {K G H : Grp (Over S)} {q : G ⟶ H}
  [IsCommMonObj K.X] [IsCommMonObj G.X] [IsCommMonObj H.X]

set_option hygiene false in
local notation "X" => H.X.left
set_option hygiene false in
local notation "Kₓ" => BaseChange.baseChangedGroup H.X.hom K
set_option hygiene false in
local notation "Gₓ" => BaseChange.baseChangedGroup H.X.hom G
set_option hygiene false in
local notation "Hₓ" => BaseChange.baseChangedGroup H.X.hom H
set_option hygiene false in
local notation "qₓ" => (groupSchemeBaseChange H.X.hom).functor.map q
set_option hygiene false in
local notation "J" => Scheme.smallEtaleTopology X

/-- The original target diagonal regarded as an additive section of the represented sheaf. -/
def representedTargetDiagonal :
    CategoryTheory.Sheaf.constantIntegerSheaf J ⟶ representedSheaf Hₓ :=
  (CategoryTheory.Sheaf.constantIntegerHomGlobalPointEquiv (representedSheaf Hₓ)).symm
    (globalSectionSetMap (representedSheaf Hₓ)
      (ULift.up (Additive.ofMul (relativeTargetDiagonal H.X))))

private theorem representedTargetDiagonal_one (U : (Scheme.Etale X)ᵒᵖ) :
    (representedTargetDiagonal (H := H)).hom.app U
        ((CategoryTheory.Sheaf.constantIntegerOne J).hom.app U PUnit.unit) =
      ULift.up (Additive.ofMul
        ((Over.homMk U.unop.hom (by simp) :
          (Scheme.Etale.forget X).obj U.unop ⟶ Over.mk (𝟙 X)) ≫
          relativeTargetDiagonal H.X)) := by
  let D := representedSheaf Hₓ
  let E := CategoryTheory.Sheaf.constantIntegerHomGlobalPointEquiv D
  let z : D.obj.obj (op (etaleTerminal X)) :=
    ULift.up (Additive.ofMul (relativeTargetDiagonal H.X))
  have h := E.apply_symm_apply (globalSectionSetMap D z)
  have hU := congrArg
    (fun (p : Topos.GlobalPoint (underlyingSetSheaf D)) => p.hom.app U PUnit.unit) h
  refine hU.trans ?_
  rw [Topos.globalPointTerminalEquiv_symm_app]
  let b : (Scheme.Etale.forget X).obj U.unop ⟶ Over.mk (𝟙 X) :=
    (Scheme.Etale.forget X).map ((etaleTerminalIsTerminal X).from U.unop)
  let t : (Scheme.Etale.forget X).obj U.unop ⟶ Over.mk (𝟙 X) :=
    Over.homMk U.unop.hom (by simp)
  change ULift.up (Additive.ofMul (b ≫ relativeTargetDiagonal H.X)) =
    ULift.up (Additive.ofMul (t ≫ relativeTargetDiagonal H.X))
  have hbt : b = t := by
    apply Over.OverMorphism.ext
    rfl
  rw [hbt]

variable (m : KernelMarking K G H q)
  [IsFinite q.hom.hom.left] [Etale q.hom.hom.left] [Surjective q.hom.hom.left]

set_option hygiene false in
local notation "Y" => Scheme.FiniteEtale.mk q.hom.hom.left

/-- The original cover map is surjective. -/
local instance relativeCoverSurjective : Surjective (Y).obj.hom :=
  inferInstanceAs (Surjective q.hom.hom.left)

set_option hygiene false in
local notation "σ" => relativeTorsorRestrictionOfMap H.X K q.hom.hom m.toTorsorAction
omit [IsCommMonObj G.X] [IsCommMonObj H.X] in
/-- The sheaf torsor of the original relative cover with its marked action. -/
abbrev relativeCoverTorsor : CategoryTheory.Sheaf.Torsor (representedSheaf Kₓ) :=
  torsorOfSchemeAction Kₓ Y σ

set_option hygiene false in
local notation "P" => relativeCoverTorsor m

omit [IsFinite q.hom.hom.left] in
/-- The represented kernel sequence at the original target of the cover is short exact. -/
theorem relativeMarkedKernelSequence_shortExact :
    (markedKernelSequence (BaseChange.kernelMarking H.X.hom m)).ShortExact := by
  let : Etale (qₓ).hom.hom.left := BaseChange.map_etale H.X.hom q inferInstance
  let : Surjective (qₓ).hom.hom.left := BaseChange.map_surjective H.X.hom q inferInstance
  let : Epi (representedSheafMap qₓ) := representedSheafMap_epi_of_etale_surjective qₓ
  exact markedKernelSequence_shortExact (BaseChange.kernelMarking H.X.hom m)

private def relativeCoverLiftSet :
    (P).carrier ⟶ underlyingSetSheaf (representedSheaf Gₓ) :=
  ⟨LiftedRestrictedYoneda.map.{u + 1} (Scheme.Etale.forget X)
    (relativeCoverLift q.hom.hom)⟩

variable [HasExt.{w} (AbelianSheaf.{u, u + 1} X)]

/-- The original cover class is the original represented extension at its diagonal section. -/
theorem relativeCoverExtClass_eq :
    let hR := relativeMarkedKernelSequence_shortExact m
    torsorExtClass (P) =
      (Abelian.Ext.mk₀ (representedTargetDiagonal (H := H))).comp hR.extClass (zero_add 1) := by
  dsimp only
  let R := markedKernelSequence (BaseChange.kernelMarking H.X.hom m)
  let hR := relativeMarkedKernelSequence_shortExact m
  let a := representedTargetDiagonal (H := H)
  apply CategoryTheory.Sheaf.torsorExtClass_of_extensionLift_of_section R hR a
    (P) (relativeCoverLiftSet m)
  · intro U b t
    exact congrArg (fun v => (ULift.up (Additive.ofMul v) : R.X₂.obj.obj U))
      (relativeCoverLift_act m b.down.toMul t.down)
  · intro U t
    refine Eq.trans ?_ (representedTargetDiagonal_one U).symm
    exact congrArg (fun v => (ULift.up (Additive.ofMul v) : R.X₃.obj.obj U))
      (relativeCoverLift_over q.hom.hom t.down)

/-- Transport the original cover boundary through a specified identification
of the original cover torsor. -/
theorem relativeCoverExtClass_of_eq (P' : CategoryTheory.Sheaf.Torsor (representedSheaf Kₓ))
    (hP : P' = relativeCoverTorsor m) :
    let hR := relativeMarkedKernelSequence_shortExact m
    torsorExtClass P' =
      (Abelian.Ext.mk₀ (representedTargetDiagonal (H := H))).comp hR.extClass (zero_add 1) := by
  rw [hP]
  exact relativeCoverExtClass_eq m

end AlgebraicGeometry.Scheme.EtaleCohomology.RepresentedKernel
