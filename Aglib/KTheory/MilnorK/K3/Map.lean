/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.KTheory.MilnorK.K3.ResidueChange
public import Mathlib.LinearAlgebra.TensorProduct.Map

/-!
# Field functoriality of the actual Milnor K₃ quotient

The tensor map induced on units and the original Milnor K₂ descends through
the first-adjacent Steinberg relations. The resulting map has the literal
field-image symbol formula and preserves identities and composition.
-/

@[expose] public section

namespace MilnorK.K3

open MilnorK.K2

variable {K L M : Type*} [Field K] [Field L] [Field M]

/-- Field functoriality, descended through the actual nested tensor quotient. -/
def map (f : K →+* L) : Group K →ₗ[ℤ] Group L :=
  (R3 K).liftQ
    ((R3 L).mkQ.comp (TensorProduct.map (unitsLinear f) (MilnorK.K2.map f))) (by
      rw [R3, Submodule.span_le]
      rintro t ⟨a, b, c, hab, rfl⟩
      change symbol3 (Units.map f.toMonoidHom a) (Units.map f.toMonoidHom b)
        (Units.map f.toMonoidHom c) = 0
      apply symbol3_steinberg_left
      change f (a : K) + f (b : K) = 1
      rw [← map_add, hab, map_one])

@[simp]
theorem map_symbol3 (f : K →+* L) (a b c : Kˣ) :
    map f (symbol3 a b c) = symbol3 (Units.map f.toMonoidHom a)
      (Units.map f.toMonoidHom b) (Units.map f.toMonoidHom c) := rfl

@[simp]
theorem map_id : map (RingHom.id K) = LinearMap.id := by
  apply linearMap_ext
  intro a b c
  simp [map_symbol3, Units.map]

/-- Composition of actual field maps is preserved by the Milnor K₃ map. -/
theorem map_comp (f : K →+* L) (g : L →+* M) :
    map (g.comp f) = (map g).comp (map f) := by
  apply linearMap_ext
  intro a b c
  simp only [LinearMap.comp_apply, map_symbol3]
  congr 1

end MilnorK.K3
