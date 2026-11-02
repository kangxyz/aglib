/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Vanishing.ProperFiniteDimension

/-! # Actual geometric bounds for both sides of an original Cartesian square

A quasi-compact original target supplies a finite geometric fibre dimension
bound. Pasting the specified Cartesian square with the actual geometric fibre
square transports that same bound to its given base change, whose target need
not be quasi-compact. No source-isomorphism replacement of the exchange is made.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Proper

universe u

attribute [local instance] hasSheafifyLarge

/-- Actual geometric fibre bounds yield simultaneous all-torsion vanishing for
the two given proper maps. The base-changed target is arbitrary. -/
theorem exists_higherDirectImage_torsion_bounds_of_isPullback
    {X S X' S' : Scheme.{u}} [CompactSpace S]
    (f : X ⟶ S) [IsProper f] (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
    (sq : IsPullback g' f' f g) :
    ∃ D : ℕ,
      (∀ F : AbelianSheaf.{u, u + 1} X, Sheaf.IsTorsion F →
        IsZero ((higherDirectImage f (D + 1)).obj F)) ∧
      (∀ F : AbelianSheaf.{u, u + 1} X', Sheaf.IsTorsion F →
        IsZero ((higherDirectImage f' (D + 1)).obj F)) := by
  let : IsProper f' := MorphismProperty.of_isPullback sq inferInstance
  obtain ⟨d, hd⟩ := f.exists_geometricFiber_dimension_le
  refine ⟨3 * d - 1, ?_, ?_⟩
  · intro F hF
    exact Vanishing.isZero_higherDirectImage_obj_of_geometricFibres_dimension_le
      f d (fun K _ _ η => hd K η) F hF (3 * d - 1 + 1) (Nat.lt_succ_self _)
  · intro F hF
    apply Vanishing.isZero_higherDirectImage_obj_of_geometricFibres_dimension_le
      f' d ?_ F hF (3 * d - 1 + 1) (Nat.lt_succ_self _)
    intro K _ _ η
    have htotal := (IsPullback.of_hasPullback f' η).paste_horiz sq
    have he := IsHomeomorph.topologicalKrullDim_eq _
      htotal.isoPullback.hom.homeomorph.isHomeomorph
    exact he.le.trans (hd K (η ≫ g))

end AlgebraicGeometry.Scheme.EtaleCohomology.Proper
