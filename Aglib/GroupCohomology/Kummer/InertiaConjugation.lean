/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.GroupCohomology.Kummer.InertiaCharacter
public import Aglib.GroupCohomology.H1.Continuous.CocycleValues

/-!
# Conjugation of actual inertia Kummer characters

A decomposition-group element at the supplied absolute prime conjugates the actual inertia
subgroup to itself. The uniformizer Kummer character is equivariant for this conjugation, with
its original positive invertible level and DVR/fraction-field hypotheses. The generic cocycle
identity delegates to ContinuousH1.Cocycle.conjugation_value. The base ring and field retain
independent universes.

Extraction source: `R5Lab.Aglib.GroupCohomology.Kummer.InertiaConjugation`, R5 revision
`f8a3314ddecffcada2ec721d26d56a937bed9690`, SHA-256
`b2a90f315e905795f836b6de8917e8ea57d893844882d5e24a7428ebc9af09d5`.
The source conditions, actual objects and canonical maps are retained under native names.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false

open scoped TensorProduct Pointwise

namespace GroupCohomology.Kummer

open Field.absoluteGaloisGroup.RootsOfUnity integralClosure.Inertia
  _root_.GroupCohomology.ContinuousH1

/-- On elements acting trivially on coefficients, a global cocycle transforms
under conjugation by the actual coefficient action. -/
theorem cocycle_conjugate
    {G A : Type*} [Group G] [TopologicalSpace G]
    [AddCommGroup A] [TopologicalSpace A] [IsTopologicalAddGroup A]
    [DistribMulAction G A] (c : Cocycle G A) (d h : G)
    (htriv : ∀ a : A, h • a = a) :
    c.val (d * h * d⁻¹) = d • c.val h :=
  c.conjugation_value d h htriv

universe u v
variable (R : Type u) (K : Type v) [CommRing R] [Field K] [Algebra R K]
  (Q : Ideal (IntegralModel R K)) [Q.IsPrime]
  (n : ℕ) (hn : 0 < n) (hnunit : IsUnit (n : R))

local notation "Γ" => Field.absoluteGaloisGroup K
local notation "I" => inertia R K Q

/-- Conjugation in the actual decomposition group preserves actual inertia. -/
def inertiaConjugate (d : decomposition R K Q) (g : I) : I :=
  ⟨d.val * g.val * d.val⁻¹, by
    have h : d.val * g.val * d.val⁻¹ ∈
        (inertia R K Q).map (MulAut.conj d.val) := ⟨g.val, g.property, rfl⟩
    rw [← Ideal.inertia_smul, d.property] at h
    exact h⟩

variable [IsDomain R] [IsDiscreteValuationRing R] [IsFractionRing R K]
variable {π : R} (hπ : Irreducible π)
/-- The exact uniformizer tame character is equivariant for actual
decomposition conjugation. -/
theorem tameCharacter_conjugate (d : decomposition R K Q) (g : I) :
    (tameCharacter R K Q n hn hnunit hπ (inertiaConjugate R K Q d g)).toAdd =
      d.val • (tameCharacter R K Q n hn hnunit hπ g).toAdd := by
  exact cocycle_conjugate
    (Kummer.cocycle K n (Kummer.chosenRoot K n hn (IsDiscreteValuationRing.uniformizerUnit (K
      := K) hπ))
      (Kummer.chosenRoot_pow K n hn _)) d.val g.val
    (fun x => inertia_fixes_roots R K Q n hn hnunit x g)

end GroupCohomology.Kummer
