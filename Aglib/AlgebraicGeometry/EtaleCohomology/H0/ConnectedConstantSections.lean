/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Limits.ConnectedCoproduct
public import Aglib.AlgebraicGeometry.EtaleCohomology.H0.ConstantSections

/-! # Original finite constant sections on connected schemes

Connectedness, rather than a one-point underlying space, suffices. The original
constant-adjunction unit is retained with its literal label normalization.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry.Scheme.FiniteEtale

universe u

namespace AlgebraicGeometry.Scheme.FiniteEtale

/-- The sections of the actual trivial cover on a connected scheme are its labels. -/
theorem trivialCoverSection_terminal_bijective_of_connected
    (X : Scheme.{u}) [ConnectedSpace X] (A : Type u) [Finite A] :
    Function.Bijective (trivialCoverSection X A (Etale.mk (𝟙 X))) := by
  classical
  let x : X := Classical.choice inferInstance
  refine ⟨fun a b h => trivialCoverSection_label X A _ x a b h, ?_⟩
  intro s
  let q : X ⟶ ∐ fun _ : A => X := s.left ≫ (trivialCoverSigmaIso X A).hom
  obtain ⟨a, r, hfac⟩ := Hom.exists_factor_sigma_of_connected (fun _ : A => X) q
  have hsection : s.left = r ≫ (trivialCoverι X A a).hom.left := by
    apply (cancel_mono (trivialCoverSigmaIso X A).hom).mp
    rw [Category.assoc, trivialCoverSigmaIso_ι]
    exact hfac.symm
  have hr : r = 𝟙 X := by
    have h := congrArg (fun f => f ≫ (trivialCover X A).obj.hom) hsection
    have h' : r = (Over.mk (Etale.mk (𝟙 X)).hom).hom := by
      simpa only [Category.assoc, trivialCoverι_struct, Category.comp_id, Over.w s] using h.symm
    change r = 𝟙 X at h'
    exact h'
  refine ⟨a, ?_⟩
  apply Over.OverMorphism.ext
  change (𝟙 X) ≫ (trivialCoverι X A a).hom.left = s.left
  rw [hsection, hr]

end AlgebraicGeometry.Scheme.FiniteEtale

namespace AlgebraicGeometry.Scheme.EtaleCohomology.ConstantFinite

attribute [local instance] hasSheafifyLarge

/-- The original finite constant-adjunction unit is bijective on a connected scheme. -/
theorem constantUnit_bijective_of_connected
    (X : Scheme.{u}) [ConnectedSpace X] (A : Type u) [AddCommGroup A] [Finite A] :
    Function.Bijective ((constantAdjunction X).unit.app (value A)) := by
  let e := (setRepresentationIso A X).inv.hom.app (op (etaleTerminal X))
  have he : Function.Bijective e := ConcreteCategory.bijective_of_isIso e
  have hb := trivialCoverSection_terminal_bijective_of_connected X A
  have hl : Function.Bijective (fun a : value A =>
      ULift.up.{u + 1} (trivialCoverSection X A (etaleTerminal X) a.down)) := by
    constructor
    · intro a b h
      apply ULift.ext
      exact hb.injective (congrArg ULift.down h)
    · intro s
      obtain ⟨a, ha⟩ := hb.surjective s.down
      exact ⟨ULift.up a, congrArg ULift.up ha⟩
  apply (Function.Bijective.of_comp_iff' he _).mp
  have hcomp : (fun a => e (((constantAdjunction X).unit.app (value A)) a)) =
      (fun a : value A => ULift.up.{u + 1} (trivialCoverSection X A (etaleTerminal X) a.down)) := by
    funext a
    exact setRepresentationIso_unit_apply X A a
  change Function.Bijective (fun a => e (((constantAdjunction X).unit.app (value A)) a))
  rw [hcomp]
  exact hl

end AlgebraicGeometry.Scheme.EtaleCohomology.ConstantFinite
