/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.CategoryTheory.Sites.LocallyInjective
public import Mathlib.Algebra.Category.Grp.Basic

/-! # Local injectivity from actual pointed kernel effacement

For an original additive presheaf map, annihilate the difference of two
sections on a refinement above each scheme point. The original equalizer
sieve then covers. Site and coefficient universes remain independent.
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

namespace AlgebraicGeometry.Scheme.Etale

universe u v

/-- Pointed local annihilation of the actual kernel makes the original
presheaf map locally injective. No Noetherian or finiteness hypothesis is used. -/
theorem isLocallyInjective_of_pointed_kernelZero {X : Scheme.{u}}
    {F G : X.Etaleᵒᵖ ⥤ AddCommGrpCat.{v}} (φ : F ⟶ G)
    (H : ∀ (U : X.Etale) (c : F.obj (op U)), φ.app (op U) c = 0 →
      ∀ x : U.left, ∃ (V : X.Etale) (a : V ⟶ U) (y : V.left),
        a.left y = x ∧ F.map a.op c = 0) :
    Presheaf.IsLocallyInjective X.smallEtaleTopology φ := by
  let : @MorphismProperty.IsStableUnderComposition Scheme.{u} _
      (@AlgebraicGeometry.Etale.{u}) := {
    comp_mem := fun f g hf hg => @AlgebraicGeometry.Etale.etale_comp _ _ f _ g hf hg }
  constructor
  intro U c d h
  change _ ∈ X.smallGrothendieckTopology @AlgebraicGeometry.Etale U.unop
  have he := Scheme.smallGrothendieckTopology_eq_toGrothendieck_smallPretopology X
    (P := @AlgebraicGeometry.Etale) (Q := @AlgebraicGeometry.Etale) le_rfl
  apply (congrArg (fun J => Presheaf.equalizerSieve c d ∈ J U.unop) he).mpr
  apply (Scheme.mem_toGrothendieck_smallPretopology U.unop _).mpr
  intro x
  have hz : φ.app U (c - d) = 0 := by rw [map_sub, h, sub_self]
  obtain ⟨V, a, y, hy, ha⟩ := H U.unop (c - d) hz x
  refine ⟨V, a, y, ?_, inferInstance, hy⟩
  change F.map a.op c = F.map a.op d
  exact sub_eq_zero.mp (((F.map a.op).hom.map_sub c d).symm.trans ha)

end AlgebraicGeometry.Scheme.Etale
