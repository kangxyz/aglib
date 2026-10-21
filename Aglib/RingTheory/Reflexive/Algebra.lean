/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.RingTheory.Reflexive.DoubleDualFraction

/-! The generic image of the double dual of a finite algebra is closed under multiplication. -/

@[expose] public section

noncomputable section

namespace Module.Dual

variable {R K B L : Type*} [CommRing R]
  [Field K] [Algebra R K] [IsFractionRing R K]
  [CommRing B] [Algebra R B] [Field L] [Algebra R L] [Algebra K L]
  [IsScalarTower R K L] [FinitePresentation R B]
  [IsReflexive K L] (j : B →ₐ[R] L) [IsLocalizedModule (nonZeroDivisors R) j.toLinearMap]

omit [FinitePresentation R B] [IsReflexive K L] in
/-- Extending a dual functional commutes with multiplication by an original algebra element. -/
theorem localizedDual_comp_mulLeft (l : Dual R B) (b : B) :
    IsLocalizedModule.mapExtendScalars (nonZeroDivisors R) j.toLinearMap
      (Algebra.linearMap R K) K (l.comp (LinearMap.mulLeft R b)) =
    (IsLocalizedModule.mapExtendScalars (nonZeroDivisors R) j.toLinearMap
      (Algebra.linearMap R K) K l).comp (LinearMap.mulLeft K (j b)) := by
  apply LinearMap.restrictScalars_injective R
  apply IsLocalizedModule.linearMap_ext (nonZeroDivisors R) j.toLinearMap
    (Algebra.linearMap R K)
  apply LinearMap.ext
  intro c
  change IsLocalizedModule.map (nonZeroDivisors R) j.toLinearMap (Algebra.linearMap R K)
    (l.comp (LinearMap.mulLeft R b)) (j.toLinearMap c) =
    IsLocalizedModule.map (nonZeroDivisors R) j.toLinearMap (Algebra.linearMap R K) l (j b * j c)
  rw [IsLocalizedModule.map_apply, ← map_mul]
  exact (IsLocalizedModule.map_apply (nonZeroDivisors R) j.toLinearMap
    (Algebra.linearMap R K) l (b * c)).symm

/-- Multiplication preserves the actual image of the double dual in the generic algebra. -/
theorem mul_mem_range_doubleDualToFraction {x y : L}
    (hx : x ∈ Set.range (doubleDualToFraction (K := K) j.toLinearMap))
    (hy : y ∈ Set.range (doubleDualToFraction (K := K) j.toLinearMap)) :
    x * y ∈ Set.range (doubleDualToFraction (K := K) j.toLinearMap) := by
  rw [mem_range_doubleDualToFraction_iff] at hx hy ⊢
  intro l
  let d := IsLocalizedModule.mapExtendScalars (nonZeroDivisors R) j.toLinearMap
    (Algebra.linearMap R K) K
  let e : B →ₗ[R] K :=
    (((d l).comp (LinearMap.mulRight K y)).restrictScalars R).comp j.toLinearMap
  have he (b : B) : e b ∈ LinearMap.range (Algebra.linearMap R K) := by
    have hb := hy (l.comp (LinearMap.mulLeft R b))
    rw [localizedDual_comp_mulLeft] at hb
    exact hb
  let ly : Dual R B := e.codRestrictOfInjective (Algebra.linearMap R K)
    (IsFractionRing.injective R K) he
  have hly : d ly = (d l).comp (LinearMap.mulRight K y) := by
    apply LinearMap.restrictScalars_injective R
    apply IsLocalizedModule.linearMap_ext (nonZeroDivisors R) j.toLinearMap
      (Algebra.linearMap R K)
    apply LinearMap.ext
    intro b
    change IsLocalizedModule.map (nonZeroDivisors R) j.toLinearMap
      (Algebra.linearMap R K) ly (j.toLinearMap b) = e b
    rw [IsLocalizedModule.map_apply]
    exact LinearMap.codRestrictOfInjective_comp_apply e (Algebra.linearMap R K)
      (IsFractionRing.injective R K) he b
  have hx' := hx ly
  change d ly x ∈ Set.range (algebraMap R K) at hx'
  rw [hly] at hx'
  exact hx'

end Module.Dual
