/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.ReesAlgebra.DegreeOne

/-!
# Original degree-one generators after scalar extension of the Rees algebra

The original map `b ↦ bX` has the first Rees component as its range.
Scalar extension of that actual linear map has the full base-changed
component as its range. Thus any spanning family of the full tensor
ideal supplies an actual spanning family of degree-one Rees elements.

No injectivity, flatness, or comparison with an image ideal is required.
The resulting family is the input to the degreewise-surjective
polynomial presentation of the full scalar-extended Rees algebra.
-/

@[expose] public noncomputable section

open Polynomial TensorProduct

universe u

namespace reesAlgebra

variable {R : Type u} [CommRing R] (I : Ideal R)

/-- The original ideal element as its actual degree-one Rees monomial. -/
def degreeOneLinearMap : I →ₗ[R] reesAlgebra I where
  toFun := degreeOne I
  map_add' a b := by
    apply Subtype.ext
    exact map_add (Polynomial.monomial 1) (a : R) (b : R)
  map_smul' r b := by
    apply Subtype.ext
    change Polynomial.monomial 1 (r • (b : R)) =
      r • Polynomial.monomial 1 (b : R)
    exact map_smul (Polynomial.monomial 1) r (b : R)

@[simp]
theorem degreeOneLinearMap_apply (b : I) : degreeOneLinearMap I b = degreeOne I b := rfl

/-- The actual degree-one map has exactly the original first homogeneous component as range. -/
theorem degreeOneLinearMap_range : LinearMap.range (degreeOneLinearMap I) = grading I 1 := by
  apply le_antisymm
  · rintro _ ⟨b, rfl⟩
    exact degreeOne_mem I b
  · intro p hp
    refine ⟨⟨(p : R[X]).coeff 1, ?_⟩, ?_⟩
    · simpa only [pow_one] using p.property 1
    · apply Subtype.ext
      exact (eq_monomial_coeff hp).symm

variable (S : Type u) [CommRing S] [Algebra R S]

/-- The scalar extension of the original map from the full tensor ideal. -/
def scalarDegreeOneMap : S ⊗[R] I →ₗ[S] S ⊗[R] reesAlgebra I :=
  (degreeOneLinearMap I).baseChange S

/-- Every original pure tensor retains its literal coefficient and Rees monomial. -/
@[simp]
theorem scalarDegreeOneMap_tmul (s : S) (b : I) :
    scalarDegreeOneMap I S (s ⊗ₜ[R] b) = s ⊗ₜ[R] degreeOne I b := rfl

/-- The scalar map surjects onto the full first component of the tensor Rees algebra. -/
theorem scalarDegreeOneMap_range :
    LinearMap.range (scalarDegreeOneMap I S) = (grading I 1).baseChange S := by
  apply le_antisymm
  · rintro _ ⟨z, rfl⟩
    induction z using TensorProduct.inductionOn with
    | tmul s b =>
      exact Submodule.tmul_mem_baseChange_of_mem s (degreeOne_mem I b)
    | add z w hz hw =>
      simpa only [map_add] using Submodule.add_mem ((grading I 1).baseChange S) hz hw
  · rw [Submodule.baseChange_eq_span, Submodule.span_le]
    rintro _ ⟨p, hp, rfl⟩
    have hp' : p ∈ LinearMap.range (degreeOneLinearMap I) := by
      rw [degreeOneLinearMap_range]
      exact hp
    obtain ⟨b, rfl⟩ := hp'
    exact ⟨(1 : S) ⊗ₜ[R] b, rfl⟩

/-- The same actual scalar map with its degree-one codomain retained. -/
def scalarDegreeOneQuotient : S ⊗[R] I →ₗ[S] (grading I 1).baseChange S :=
  (scalarDegreeOneMap I S).codRestrict ((grading I 1).baseChange S) fun z => by
    rw [← scalarDegreeOneMap_range]
    exact ⟨z, rfl⟩

/-- The quotient keeps the original pure tensor in the full tensor Rees algebra. -/
@[simp]
theorem scalarDegreeOneQuotient_tmul (s : S) (b : I) :
    (scalarDegreeOneQuotient I S (s ⊗ₜ[R] b) : S ⊗[R] reesAlgebra I) =
      s ⊗ₜ[R] degreeOne I b := rfl

/-- Surjectivity is onto the full first component, without a flatness hypothesis. -/
theorem scalarDegreeOneQuotient_surjective :
    Function.Surjective (scalarDegreeOneQuotient I S) := by
  intro c
  have hc : (c : S ⊗[R] reesAlgebra I) ∈ LinearMap.range (scalarDegreeOneMap I S) := by
    rw [scalarDegreeOneMap_range]
    exact c.property
  obtain ⟨z, hz⟩ := hc
  exact ⟨z, Subtype.ext hz⟩

/-- A specified spanning family of the full tensor ideal generates the original tensor
Rees degree-one component under the actual scalar monomial map. -/
theorem span_scalarDegreeOneMap {κ : Type u} (v : κ → S ⊗[R] I)
    (hv : Submodule.span S (Set.range v) = ⊤) :
    Submodule.span S (Set.range fun i => scalarDegreeOneMap I S (v i)) =
      (grading I 1).baseChange S := by
  have h := congrArg (Submodule.map (scalarDegreeOneMap I S)) hv
  simpa only [Submodule.map_span, ← Set.range_comp, Function.comp_def,
    Submodule.map_top, scalarDegreeOneMap_range] using h

end reesAlgebra
