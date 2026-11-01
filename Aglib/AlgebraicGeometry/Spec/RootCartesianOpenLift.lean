/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.Kummer.RootComplement
public import Aglib.AlgebraicGeometry.Spec.Localization
public import Mathlib.AlgebraicGeometry.Properties

/-! # Root-complement lifts through the original Cartesian open square

A lift on the whole root chart gives a lift to the actual covering source on
the root complement. If the original target is integral, this proves the
actual cover integral, without assuming the whole base-changed cover connected.
-/

@[expose] public noncomputable section

open CategoryTheory Limits Algebra.Kummer

namespace AlgebraicGeometry.Scheme.Kummer

universe u

variable (R : Type u) [CommRing R] (N : ℕ) (f : R)

local notation "T" => RootAlgebra N f
local notation "V" => Localization.Away (AdjoinRoot.root (rootPolynomial N f))
local notation "U" => Localization.Away f

/-- The original root-complement map commutes with the original base projection. -/
theorem rootComplement_structure :
    Spec.algebraMap T V ≫ Spec.algebraMap R T =
      Spec.map (CommRingCat.ofHom (rootComplementHom N f)) ≫ Spec.algebraMap R U := by
  simp only [Spec.algebraMap, ← Spec.map_comp]
  congr 1
  exact CommRingCat.hom_ext (rootComplementHom_comp N f).symm

/-- Retain the exact covering source and both projections of its open lift. -/
theorem exists_rootComplementLift_of_isPullback {E C : Scheme.{u}}
    (i : E ⟶ C) (p : E ⟶ Spec (.of U)) (c : C ⟶ Spec (.of R))
    (H : IsPullback i p c (Spec.algebraMap R U))
    (a : Spec (.of T) ⟶ C) (ha : a ≫ c = Spec.algebraMap R T) :
    ∃ b : Spec (.of V) ⟶ E,
      b ≫ i = Spec.algebraMap T V ≫ a ∧
      b ≫ p = Spec.map (CommRingCat.ofHom (rootComplementHom N f)) := by
  have h : (Spec.algebraMap T V ≫ a) ≫ c =
      Spec.map (CommRingCat.ofHom (rootComplementHom N f)) ≫ Spec.algebraMap R U := by
    rw [Category.assoc, ha]
    exact rootComplement_structure R N f
  exact ⟨H.lift _ _ h, H.lift_fst _ _ h, H.lift_snd _ _ h⟩

/-- A nonempty root complement forces the original open covering source to be
integral when its original target is integral. -/
theorem isIntegral_of_rootComplementLift [Nonempty (Spec (.of V))]
    {E C : Scheme.{u}} [IsIntegral C]
    (i : E ⟶ C) (p : E ⟶ Spec (.of U)) (c : C ⟶ Spec (.of R))
    (H : IsPullback i p c (Spec.algebraMap R U))
    (a : Spec (.of T) ⟶ C) (ha : a ≫ c = Spec.algebraMap R T) : IsIntegral E := by
  obtain ⟨b, _, _⟩ := exists_rootComplementLift_of_isPullback R N f i p c H a ha
  let : Nonempty E := Nonempty.map b inferInstance
  let : IsOpenImmersion i := MorphismProperty.of_isPullback H.flip inferInstance
  exact isIntegral_of_isOpenImmersion i

end AlgebraicGeometry.Scheme.Kummer
