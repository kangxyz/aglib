/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Blowup.ClosedPointPrefix.Height
public import Aglib.AlgebraicGeometry.Blowup.ClosedPointPrefix.BaseChange

/-!
# Original singular height under flat preimmersion base change

The existing original prefix equivalence preserves empty levels and their least
index. No new height, path, or geometric finiteness premise is introduced.
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme.Blowup.ClosedPointPrefix

variable {U X : Scheme.{u}} (j : U ⟶ X) [IsPreimmersion j] [Flat j]
    (xU : U) (hx : IsClosed ({j xU} : Set X))

include hx

/-- The original flat-preimmersion prefix equivalence preserves each empty level. -/
theorem singularPrefix_isEmpty_iff (n : ℕ) :
    IsEmpty (SingularPrefix U xU n) ↔ IsEmpty (SingularPrefix X (j xU) n) := by
  let e := singularPrefixEquiv j xU hx n
  exact ⟨fun h => ⟨fun q => h.false (e.symm q)⟩,
    fun h => ⟨fun p => h.false (e p)⟩⟩

/-- Finiteness of original singular height is local for this actual base change. -/
theorem exists_empty_singularPrefix_level_iff :
    (∃ n : ℕ, IsEmpty (SingularPrefix U xU n)) ↔
      ∃ n : ℕ, IsEmpty (SingularPrefix X (j xU) n) := by
  constructor
  · rintro ⟨n, hn⟩
    exact ⟨n, (singularPrefix_isEmpty_iff j xU hx n).mp hn⟩
  · rintro ⟨n, hn⟩
    exact ⟨n, (singularPrefix_isEmpty_iff j xU hx n).mpr hn⟩

/-- The same least empty level is preserved, independently of its existence proof. -/
theorem singularHeight_baseChange
    (hU : ∃ n : ℕ, IsEmpty (SingularPrefix U xU n))
    (hX : ∃ n : ℕ, IsEmpty (SingularPrefix X (j xU) n)) :
    height hU = height hX := by
  classical
  apply Nat.le_antisymm
  · exact Nat.find_min' hU
      ((singularPrefix_isEmpty_iff j xU hx (height hX)).mpr (height_empty hX))
  · exact Nat.find_min' hX
      ((singularPrefix_isEmpty_iff j xU hx (height hU)).mp (height_empty hU))

end AlgebraicGeometry.Scheme.Blowup.ClosedPointPrefix
