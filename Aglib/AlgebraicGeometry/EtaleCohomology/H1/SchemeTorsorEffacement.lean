/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.H1.SchemeTorsorBaseChange
public import Aglib.AlgebraicGeometry.EtaleCohomology.H1.TorsorTrivial

/-! # Original H1 classes killed by an actual lift to their scheme torsor

An arbitrary morphism admitting a lift to the original torsor kills its
represented H1 class. The section is constructed by the actual Over adjunction,
and the conclusion retains the original H1 pullback before coefficient transport.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.MonObj

namespace AlgebraicGeometry.Scheme.EtaleCohomology.SchemeTorsorEffacement

universe u w w'

attribute [local instance] hasSheafifyLarge Over.cartesianMonoidalCategory

variable {X S : Scheme.{u}} (f : S ⟶ X) (Y : Scheme.FiniteEtale X)
  (s : Over.mk f ⟶ Y.obj)

/-- The actual lift, viewed over the image of the terminal test scheme. -/
def terminalLift : (Over.map f).obj (Over.mk (𝟙 S)) ⟶ Y.obj :=
  Over.homMk s.left (by
    change s.left ≫ Y.obj.hom = (𝟙 S) ≫ f
    rw [Category.id_comp]
    have hs := Over.w s
    change s.left ≫ Y.obj.hom = f at hs
    exact hs)

/-- The actual adjunction constructs a section of the literal pulled-back cover. -/
def pullbackSection :
    Over.mk (𝟙 S) ⟶ ((Scheme.FiniteEtale.baseChange f).obj Y).obj :=
  SchemeTorsorBaseChange.pullbackSectionEquiv f (Over.mk (𝟙 S)) Y.obj
    (terminalLift f Y s)

/-- The section recovers the given original lift under the same Over adjunction. -/
theorem pullbackSection_recovers_lift :
    (SchemeTorsorBaseChange.pullbackSectionEquiv f (Over.mk (𝟙 S)) Y.obj).symm
      (pullbackSection f Y s) = terminalLift f Y s :=
  (SchemeTorsorBaseChange.pullbackSectionEquiv f (Over.mk (𝟙 S)) Y.obj).symm_apply_apply _

variable (G : Grp (Over X)) [IsCommMonObj G.X]
  [Surjective Y.obj.hom] (τ : TorsorAction G (toUnit Y.obj))
  [HasExt.{w'} (AbelianSheaf.{u, u + 1} S)]

include s in
/-- The constructed original section kills the class of the actual pulled-back action. -/
theorem pullbackSchemeAction_class_eq_zero :
    torsorExtClass (torsorOfSchemeAction (baseChangedGroup f G)
      ((Scheme.FiniteEtale.baseChange f).obj Y)
      (SchemeTorsorBaseChange.pullbackSchemeAction f G Y τ)) = 0 :=
  torsorExtClass_eq_zero_of_section _ (ULift.up (pullbackSection f Y s))

variable [HasExt.{w} (AbelianSheaf.{u, u + 1} X)] [Etale G.X.hom]

include s in
/-- A genuine lift to the original scheme torsor kills its original H1 pullback.
Neither a classification premise nor finiteness or connectedness of `S` is required. -/
theorem h1Pullback_torsorExtClass_eq_zero :
    h1Pullback f (representedSheaf G) (torsorExtClass (torsorOfSchemeAction G Y τ)) = 0 := by
  apply (coefficientIso (representedSheafBaseChangeIso f G)).injective
  change coefficientMap (representedSheafBaseChangeIso f G).hom _ =
    coefficientMap (representedSheafBaseChangeIso f G).hom 0
  rw [SchemeTorsorBaseChange.torsorExtClass_pullbackSchemeAction f G Y τ, map_zero]
  exact pullbackSchemeAction_class_eq_zero f Y s G τ

end AlgebraicGeometry.Scheme.EtaleCohomology.SchemeTorsorEffacement
