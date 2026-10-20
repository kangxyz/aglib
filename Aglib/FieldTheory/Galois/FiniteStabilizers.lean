/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Mathlib.FieldTheory.AbsoluteGaloisGroup
public import Mathlib.Topology.Algebra.OpenSubgroup

/-!
# Open stabilizers from finite algebraic coefficients

Source: `R5Lab.Aglib.FieldTheory.Galois.FiniteStabilizers`,
revision `f8a3314ddecffcada2ec721d26d56a937bed9690`. Exact field, action, embedding and
explicit-data hypotheses are retained. Native objects and maps are reused.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false
open scoped Topology
namespace Field.absoluteGaloisGroup
universe u
variable (K : Type u) [Field K]

local instance closureFieldAction :
    MulSemiringAction (Field.absoluteGaloisGroup K) (AlgebraicClosure K) :=
  inferInstanceAs (MulSemiringAction
    (AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) (AlgebraicClosure K))

def fixingCoefficients (s : Finset (AlgebraicClosure K)) : Subgroup (Field.absoluteGaloisGroup K) :=
  ⨅ a ∈ s, MulAction.stabilizer (Field.absoluteGaloisGroup K) a

theorem mem_fixingCoefficients (s : Finset (AlgebraicClosure K)) (g : Field.absoluteGaloisGroup K) :
    g ∈ fixingCoefficients K s ↔ ∀ a ∈ s, g.toRingHom a = a := by
  simp only [fixingCoefficients, Subgroup.mem_iInf, MulAction.mem_stabilizer_iff]
  rfl

theorem fixingCoefficients_isOpen (s : Finset (AlgebraicClosure K)) :
    IsOpen (fixingCoefficients K s : Set (Field.absoluteGaloisGroup K)) := by
  simp only [fixingCoefficients, Subgroup.coe_iInf]
  apply isOpen_biInter_finset
  intro a _
  exact stabilizer_isOpen_of_isIntegral (K := K) a

theorem stabilizer_open_of_finite {X : Type*} [MulAction (Field.absoluteGaloisGroup K) X]
    (x : X) (h : ∃ s : Finset (AlgebraicClosure K), ∀ g : Field.absoluteGaloisGroup K,
      (∀ a ∈ s, g.toRingHom a = a) → g • x = x) :
    IsOpen (MulAction.stabilizer (Field.absoluteGaloisGroup K) x : Set
      (Field.absoluteGaloisGroup K)) := by
  classical
  obtain ⟨s, hs⟩ := h
  have hle : fixingCoefficients K s ≤ MulAction.stabilizer (Field.absoluteGaloisGroup K) x := by
    intro g hg
    exact hs g ((mem_fixingCoefficients K s g).mp hg)
  exact Subgroup.isOpen_mono hle (fixingCoefficients_isOpen K s)

end Field.absoluteGaloisGroup
