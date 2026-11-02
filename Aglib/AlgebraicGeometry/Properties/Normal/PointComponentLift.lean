/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Properties.Normal.PointComponent
public import Mathlib.AlgebraicGeometry.Stalk

/-! # Local-source factorization through the original normal component

A map from a local spectrum whose closed point maps to the specified point
factors through that point's actual open component. The factorization retains
the original inclusion and point, and is unique.
-/

@[expose] public noncomputable section

open CategoryTheory

namespace AlgebraicGeometry.Scheme

universe u

variable (X : Scheme.{u}) [IsLocallyNoetherian X] (hX : NormalStalks X) (x : X)
  {R : Type u} [CommRing R] [IsLocalRing R]
  (a : Spec (.of R) ⟶ X) (ha : a (IsLocalRing.closedPoint R) = x)

include ha in
/-- The entire local spectrum maps into the original component containing
its closed-point image. -/
theorem range_subset_normalComponentOpen :
    Set.range a ⊆ Set.range (normalComponentOpen X hX x).ι := by
  rw [Opens.range_ι]
  have hpre : a ⁻¹ᵁ normalComponentOpen X hX x = ⊤ :=
    preimage_eq_top_of_closedPoint_mem a (by
      rw [ha]
      exact mem_normalComponentOpen X hX x)
  rintro _ ⟨z, rfl⟩
  have hz : z ∈ a ⁻¹ᵁ normalComponentOpen X hX x := by
    rw [hpre]
    trivial
  exact hz

/-- The canonical factorization through the same actual component open. -/
def normalComponentLift : Spec (.of R) ⟶ normalComponentOpen X hX x :=
  IsOpenImmersion.lift _ a (range_subset_normalComponentOpen X hX x a ha)

@[reassoc (attr := simp)] theorem normalComponentLift_fac :
    normalComponentLift X hX x a ha ≫ (normalComponentOpen X hX x).ι = a :=
  IsOpenImmersion.lift_fac _ _ _

/-- The factorization retains the specified point as a point of the actual open. -/
theorem normalComponentLift_closedPoint :
    normalComponentLift X hX x a ha (IsLocalRing.closedPoint R) =
      ⟨x, mem_normalComponentOpen X hX x⟩ := by
  apply Subtype.ext
  have h := congrArg (fun b => b (IsLocalRing.closedPoint R))
    (normalComponentLift_fac X hX x a ha)
  exact h.trans ha

/-- No second lift to the same open component is possible. -/
theorem normalComponentLift_unique
    (b : Spec (.of R) ⟶ normalComponentOpen X hX x)
    (hb : b ≫ (normalComponentOpen X hX x).ι = a) :
    b = normalComponentLift X hX x a ha := by
  apply (cancel_mono (normalComponentOpen X hX x).ι).mp
  exact hb.trans (normalComponentLift_fac X hX x a ha).symm

end AlgebraicGeometry.Scheme
