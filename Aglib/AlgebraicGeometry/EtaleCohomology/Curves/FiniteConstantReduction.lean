/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Curves.CharacteristicPrimaryRestriction
public import Aglib.AlgebraicGeometry.EtaleCohomology.Curves.PrimePowerReduction
public import Mathlib.Algebra.CharP.Basic

/-! # Remaining invertible-order reduction for the original restriction map

The characteristic-primary case is proved geometrically. Together with the actual
split finite-abelian decomposition, it reduces the final theorem to positive
invertible cyclic coefficients. The displayed invertible-order premise remains
an explicit intermediate input, not an assertion of the final curve theorem.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u w w'

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Curves

attribute [local instance] hasSheafifyLarge

variable {R : Type u} [CommRing R] [HenselianLocalRing R]
  [IsSepClosed (IsLocalRing.ResidueField R)]
  {Y : Scheme.{u}} (f : Y ⟶ ProjectiveLine.projectiveP1 R) [IsFinite f]
  [HasExt.{w} (AbelianSheaf.{u, u + 1} Y)]
  [HasExt.{w'} (AbelianSheaf.{u, u + 1} (residueFiber f))]

/-- The only remaining coefficients are positive cyclic groups of invertible order.
This uses the original restriction throughout and permits a non-Noetherian local base. -/
theorem finite_projectiveLine_constantRestriction_surjective_of_invertible_cyclic
    (q : ℕ)
    (hinvertible : ∀ n : ℕ, 0 < n → IsUnit (n : Γ(Spec (.of R), ⊤)) →
      Function.Surjective (constantRestriction (ULift.{u} (ZMod n))
        (pullback.fst (f ≫ ProjectiveLine.structureMap R) (LocalRing.residueSpecMap R)) q))
    (A : Type u) [AddCommGroup A] [Finite A] :
    Function.Surjective (constantRestriction A
      (pullback.fst (f ≫ ProjectiveLine.structureMap R) (LocalRing.residueSpecMap R)) q) := by
  apply constantRestriction_surjective_of_prime_powers
  intro p hp r
  by_cases hz : (p : IsLocalRing.ResidueField R) = 0
  · let : Fact p.Prime := ⟨hp⟩
    let : CharP (IsLocalRing.ResidueField R) p :=
      (CharP.charP_iff_prime_eq_zero hp).mpr hz
    exact finite_projectiveLine_characteristicPrimaryRestriction_surjective.{u, w, w'} f p r q
  · have hu : IsUnit (p : R) :=
      (IsLocalRing.residue_ne_zero_iff_isUnit (p : R)).mp (by simpa using hz)
    have hn : IsUnit ((p ^ r : ℕ) : R) := by simpa using hu.pow r
    have hΓ : IsUnit ((p ^ r : ℕ) : Γ(Spec (.of R), ⊤)) := by
      simpa using hn.map (Scheme.ΓSpecIso (.of R)).inv.hom
    exact hinvertible (p ^ r) (pow_pos hp.pos r) hΓ

end AlgebraicGeometry.Scheme.EtaleCohomology.Curves
