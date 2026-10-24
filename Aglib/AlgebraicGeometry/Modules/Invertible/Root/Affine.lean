/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Invertible.Root.Basic
public import Aglib.AlgebraicGeometry.Modules.Invertible.SquareZero.ClosedImmersion

/-! # Affine square-zero lifting of fixed-target root pairs

An actual affine line bundle and an actual prescribed affine isomorphism
lift across the original square-zero closed immersion. Applying these to
the root bundle and its specified power map lifts a root of the fixed
target, including its original reduction isomorphism. This affine object
lifting itself holds at every level.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory

namespace AlgebraicGeometry.Scheme.Modules.Invertible.Root

universe u

/-- An affine fixed-target root pair lifts across the original square-zero
closed immersion, retaining the specified power map on the original reduction. -/
theorem exists_pair_lift_affine_of_square_zero
    {X₀ X : Scheme.{u}} [IsAffine X₀] [IsAffine X]
    (i : X₀ ⟶ X) [IsClosedImmersion i] (hi : i.ker ^ 2 = ⊥)
    (L : LineBundle X) (n : ℕ) (P₀ : Pair (pullbackLineBundle i L) n) :
    ∃ P : Pair L n, Nonempty (Iso (P.pullback i) P₀) := by
  obtain ⟨M, ⟨e⟩⟩ := exists_lineBundle_lift_affine_closed_of_square_zero i hi P₀.bundle
  let ePower : (Scheme.Modules.pullback i).obj (tensorPowerLineBundle X M n).val ≅
      (Scheme.Modules.pullback i).obj L.val :=
    PowerPullback.pullbackPowerIso i M n ≪≫
      TrivializedPower.powerIso X₀ e n ≪≫ P₀.powerIso
  obtain ⟨φ, hφ⟩ := exists_lineBundle_iso_lift_affine_closed_of_square_zero i hi
    (tensorPowerLineBundle X M n) L ePower
  let P : Pair L n := ⟨M, φ⟩
  refine ⟨P, ⟨{ bundleIso := e, comm := ?_ }⟩⟩
  change (TrivializedPower.powerIso X₀ e n).hom ≫ P₀.powerIso.hom =
    (PowerPullback.pullbackPowerIso i M n).inv ≫ (Scheme.Modules.pullback i).map φ.hom
  rw [hφ]
  simp only [ePower, CategoryTheory.Iso.trans_hom,
    CategoryTheory.Iso.inv_hom_id_assoc]

end AlgebraicGeometry.Scheme.Modules.Invertible.Root
