/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.StrictHenselianSection

/-! # A pointed section after the original strict-local base change

An original geometric point supplies a point of the literal pullback over the
specified original covering point. The pointed Henselian section lifts it.
The resulting map still targets the unchanged covering scheme and retains
both the original base triangle and its specified closed-point value.
-/

@[expose] public noncomputable section

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme.FiniteEtale

universe u

/-- An actual geometric point over a strict-local base lifts the chosen
original covering point to a section, with both original equations retained.
Etaleness, not an arbitrary finite residue extension, supplies separability. -/
theorem exists_lift_through_closedPoint_of_strictHenselian
    (S Ω : Type u) [CommRing S] [HenselianLocalRing S]
    [IsSepClosed (IsLocalRing.ResidueField S)] [Field Ω] [IsSepClosed Ω]
    {X E : Scheme.{u}} (p : E ⟶ X) [IsFinite p] [Etale p]
    (g : Spec (.of S) ⟶ X) (u : Spec (.of Ω) ⟶ Spec (.of S))
    (hu : u default = IsLocalRing.closedPoint S)
    (y : E) (hy : p y = g (IsLocalRing.closedPoint S)) :
    ∃ a : Spec (.of S) ⟶ E,
      a ≫ p = g ∧ a (IsLocalRing.closedPoint S) = y := by
  have hyu : p y = (u ≫ g) default := by
    rw [Scheme.Hom.comp_apply, hu]
    exact hy
  obtain ⟨t, ht, hty⟩ := Scheme.exists_fac_of_etale_of_isSepClosed p (u ≫ g) y hyu
  let z : Spec (.of Ω) ⟶ pullback p g := pullback.lift t u ht
  have hzy : pullback.snd p g (z default) = IsLocalRing.closedPoint S := by
    have hz : (z ≫ pullback.snd p g) default = u default :=
      congrArg (fun h : Spec (.of Ω) ⟶ Spec (.of S) => h default)
        (pullback.lift_snd t u ht)
    exact hz.trans hu
  obtain ⟨s, hs, hsp⟩ := exists_section_through_closedPoint S (pullback.snd p g)
    (z default) hzy
  refine ⟨s ≫ pullback.fst p g, ?_, ?_⟩
  · rw [Category.assoc, pullback.condition, ← Category.assoc, hs, Category.id_comp]
  · change pullback.fst p g (s (IsLocalRing.closedPoint S)) = y
    rw [hsp]
    exact (congrArg (fun h : Spec (.of Ω) ⟶ E => h default)
      (pullback.lift_fst t u ht)).trans hty

end AlgebraicGeometry.Scheme.FiniteEtale
