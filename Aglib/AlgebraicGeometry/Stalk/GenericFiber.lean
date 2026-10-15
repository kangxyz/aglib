/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.Preimmersion
public import Mathlib.RingTheory.Flat.Localization
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.Tactic.Algebraize

/-!
# Stalks on an actual generic fibre

Source application: `K2-018#sec:k2018-splitting`, mathematical revision
`e73d98b1b5c1e5abcdebf7d058e436d792b87982`.
This module proves only ordinary generic-fibre scheme and local-ring geometry.
The generic-fibre projection's actual stalk map is an isomorphism, with no
supplied stalk comparison and no K-theoretic premise.
Implementation: Lean 4.34.1/mathlib d13f23b723b8a846827a245b89c10fc7d3f11612.
-/

@[expose] public section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry

universe u
namespace AlgebraicGeometry.Scheme.LocalRing.GenericFiber

/-- Flatness and surjectivity on stalks make each actual local homomorphism an iso. -/
theorem stalkMap_isIso_of_flat_of_surjectiveOnStalks
    {X Y : Scheme.{u}} (f : X ⟶ Y) [Flat f] [SurjectiveOnStalks f] (x : X) :
    IsIso (f.stalkMap x) := by
  rw [ConcreteCategory.isIso_iff_bijective]
  refine ⟨?_, f.stalkMap_surjective x⟩
  algebraize [(f.stalkMap x).hom]
  have : Module.FaithfullyFlat (Y.presheaf.stalk (f x)) (X.presheaf.stalk x) :=
    @Module.FaithfullyFlat.of_flat_of_isLocalHom _ _ _ _ _ _ _
      (Flat.stalkMap f x) (f.toLRSHom.prop x)
  exact ‹RingHom.FaithfullyFlat _›.injective

variable (A F : Type u) [CommRing A] [Field F]
  [Algebra A F] [IsFractionRing A F]

/-- The morphism `Spec F ⟶ Spec A` induced by the fraction-ring algebra map from `A` to `F`. -/
def baseMap : Spec (.of F) ⟶ Spec (.of A) :=
  Spec.map (CommRingCat.ofHom (algebraMap A F))

variable {Y : Scheme.{u}} (p : Y ⟶ Spec (.of A))

/-- The generic fibre of `p` obtained by base change from `A` to its supplied fraction field `F`. -/
abbrev scheme : Scheme.{u} := Limits.pullback p (baseMap A F)
/-- The canonical projection from the generic fibre of `p` to `Y`. -/
abbrev projection : scheme A F p ⟶ Y := Limits.pullback.fst p (baseMap A F)

theorem baseMap_flat : Flat (baseMap A F) := by
  let : Module.Flat A F := IsLocalization.flat F (nonZeroDivisors A)
  apply Flat.SpecMap_iff.mpr
  change (algebraMap A F).Flat
  exact RingHom.flat_algebraMap_iff.mpr inferInstance

theorem baseMap_preimmersion : IsPreimmersion (baseMap A F) :=
  IsPreimmersion.of_isLocalization (nonZeroDivisors A)

/-- Localization of the base changes no local ring at a point of the generic fibre. -/
theorem projection_stalkMap_isIso (x : scheme A F p) :
    IsIso ((projection A F p).stalkMap x) := by
  let := baseMap_flat A F
  let := baseMap_preimmersion A F
  exact stalkMap_isIso_of_flat_of_surjectiveOnStalks (projection A F p) x

/-- The canonical ring equivalence is the actual projection's stalk map. -/
def stalkEquiv (x : scheme A F p) :
    Y.presheaf.stalk (projection A F p x) ≃+* (scheme A F p).presheaf.stalk x := by
  letI := projection_stalkMap_isIso A F p x
  exact (asIso ((projection A F p).stalkMap x)).commRingCatIsoToRingEquiv

@[simp] theorem stalkEquiv_apply (x : scheme A F p)
    (a : Y.presheaf.stalk (projection A F p x)) :
    stalkEquiv A F p x a = (projection A F p).stalkMap x a := rfl

end AlgebraicGeometry.Scheme.LocalRing.GenericFiber
