/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.AssociatedGraded.Cotangent
public import Mathlib.RingTheory.GradedAlgebra.AlgHom
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.Algebra.Algebra.Tower

/-!
# The original graded polynomial map on actual ideal generators

The canonical coefficient quotient action preserves every original associated
graded component. The native scalar-span equality and `Submodule.copy` retain
its literal carrier, and the existing decomposition and graded multiplication are
reused. No second decomposition of the associated graded ring is constructed.

The polynomial map sends each variable to the original degree-one Rees symbol
of its displayed ideal element. It is a native `GradedAlgHom`. Actual spanning
of the cotangent quotient proves surjectivity; actual ideal generation implies
that spanning without any Noetherian, basis, presentation or Hilbert premise.
-/

@[expose] public noncomputable section
set_option autoImplicit false

universe u v

namespace Ideal

variable {A : Type u} [CommRing A] (I : Ideal A)

/-- The original homogeneous component with its canonical coefficient-quotient action.
The native copy retains the original carrier definitionally. -/
def associatedGradedQuotientGrading (n : ℕ) : Submodule (A ⧸ I) I.associatedGraded := by
  refine (Submodule.span (A ⧸ I) (I.associatedGradedGrading n : Set I.associatedGraded)).copy
    (I.associatedGradedGrading n : Set I.associatedGraded) ?_
  rw [Submodule.coe_span_eq_span_of_surjective A (A ⧸ I) Ideal.Quotient.mk_surjective,
    Submodule.span_eq]

/-- Coefficient extension retains exactly the original homogeneous elements. -/
theorem mem_associatedGradedQuotientGrading (n : ℕ) (x : I.associatedGraded) :
    x ∈ associatedGradedQuotientGrading I n ↔ x ∈ I.associatedGradedGrading n := Iff.rfl

/-- Restriction recovers the original native homogeneous submodule. -/
theorem associatedGradedQuotientGrading_restrictScalars (n : ℕ) :
    (associatedGradedQuotientGrading I n).restrictScalars A = I.associatedGradedGrading n :=
  Submodule.ext fun _ => Iff.rfl

/-- Reuse the original graded multiplication and original homogeneous decomposition. -/
instance associatedGradedQuotientGradedAlgebra :
    GradedAlgebra (associatedGradedQuotientGrading I) :=
  { (inferInstance : GradedAlgebra I.associatedGradedGrading) with }

/-- The coefficient-quotient grading uses the very same original homogeneous components. -/
theorem associatedGradedQuotientGrading_decompose (x : I.associatedGraded) (n : ℕ) :
    (DirectSum.decompose (associatedGradedQuotientGrading I) x n : I.associatedGraded) =
      (DirectSum.decompose I.associatedGradedGrading x n : I.associatedGraded) := rfl

variable {ι : Type v}

/-- The original coefficient-linear polynomial map on the displayed ideal elements. -/
def cotangentPolynomialMap (g : ι → I) :
    MvPolynomial ι (A ⧸ I) →ₐ[A ⧸ I] I.associatedGraded := by
  let _ : CommSemiring I.associatedGraded := Ideal.Quotient.commSemiring I.associatedGradedIdeal
  exact MvPolynomial.aeval fun i => cotangentSymbol I (I.toCotangent (g i))

/-- Every original variable goes to the canonical symbol of its actual cotangent class. -/
theorem cotangentPolynomialMap_X_cotangent (g : ι → I) (i : ι) :
    cotangentPolynomialMap I g (MvPolynomial.X i) =
      cotangentSymbol I (I.toCotangent (g i)) := by
  rw [cotangentPolynomialMap, MvPolynomial.aeval_X]

/-- Every original variable retains the literal original Rees numerator. -/
theorem cotangentPolynomialMap_X (g : ι → I) (i : ι) :
    cotangentPolynomialMap I g (MvPolynomial.X i) =
      Ideal.Quotient.mk I.associatedGradedIdeal (reesAlgebra.degreeOne I (g i)) := by
  rw [cotangentPolynomialMap_X_cotangent, cotangentSymbol_toCotangent]

/-- Every original coefficient class retains the canonical quotient action. -/
theorem cotangentPolynomialMap_C (g : ι → I) (a : A ⧸ I) :
    cotangentPolynomialMap I g (MvPolynomial.C a) = associatedGradedCoefficientMap I a := by
  rw [cotangentPolynomialMap, MvPolynomial.aeval_C]
  rfl

/-- An original scalar uses the original coefficient map of the actual Rees quotient. -/
theorem cotangentPolynomialMap_C_mk (g : ι → I) (a : A) :
    cotangentPolynomialMap I g (MvPolynomial.C (Ideal.Quotient.mk I a)) =
      algebraMap A I.associatedGraded a := by
  rw [cotangentPolynomialMap_C, associatedGradedCoefficientMap_mk]

private theorem cotangentPolynomialMap_X_mem (g : ι → I) (i : ι) :
    cotangentPolynomialMap I g (MvPolynomial.X i) ∈ associatedGradedQuotientGrading I 1 := by
  rw [cotangentPolynomialMap_X]
  change Ideal.Quotient.mk I.associatedGradedIdeal (reesAlgebra.degreeOne I (g i)) ∈
    (reesAlgebra.grading I 1).map (Ideal.Quotient.mkₐ A I.associatedGradedIdeal).toLinearMap
  exact Submodule.mem_map.mpr
    ⟨reesAlgebra.degreeOne I (g i), reesAlgebra.degreeOne_mem I (g i), rfl⟩

/-- The original polynomial map preserves each original total homogeneous degree. -/
theorem cotangentPolynomialMap_mem (g : ι → I) {n : ℕ}
    {p : MvPolynomial ι (A ⧸ I)}
    (hp : p ∈ MvPolynomial.homogeneousSubmodule ι (A ⧸ I) n) :
    cotangentPolynomialMap I g p ∈ associatedGradedQuotientGrading I n := by
  let f := cotangentPolynomialMap I g
  let M := (MvPolynomial.homogeneousSubmodule ι (A ⧸ I) 1).map f.toLinearMap
  have h₁ : M ≤ associatedGradedQuotientGrading I 1 := by
    dsimp only [M]
    rw [MvPolynomial.homogeneousSubmodule_one_eq_span_X, Submodule.map_span, ← Set.range_comp']
    apply Submodule.span_le.mpr
    rintro x ⟨i, rfl⟩
    exact cotangentPolynomialMap_X_mem I g i
  have hpow (m : ℕ) : M ^ m ≤ associatedGradedQuotientGrading I m := by
    induction m with
    | zero =>
      rw [pow_zero, Submodule.one_eq_span]
      apply Submodule.span_le.mpr
      rintro x (rfl : x = 1)
      exact SetLike.one_mem_graded (associatedGradedQuotientGrading I)
    | succ m ih =>
      rw [pow_succ]
      apply Submodule.mul_le.mpr
      intro x hx y hy
      exact SetLike.mul_mem_graded (A := associatedGradedQuotientGrading I) (ih hx) (h₁ hy)
  have hmap : f p ∈ (MvPolynomial.homogeneousSubmodule ι (A ⧸ I) n).map f.toLinearMap :=
    Submodule.mem_map.mpr ⟨p, hp, rfl⟩
  rw [← MvPolynomial.homogeneousSubmodule_one_pow, Submodule.map_pow] at hmap
  exact hpow n hmap

attribute [local instance] MvPolynomial.gradedAlgebra

/-- The native graded polynomial map with the original coefficient and symbol maps. -/
def cotangentGradedPolynomialMap (g : ι → I) :
    MvPolynomial.homogeneousSubmodule ι (A ⧸ I) →ₐᵍ[A ⧸ I]
      associatedGradedQuotientGrading I where
  __ := cotangentPolynomialMap I g
  map_mem := by
    intro n p hp
    exact cotangentPolynomialMap_mem I g hp

/-- The graded map is the original ordinary algebra map on the same rings. -/
theorem cotangentGradedPolynomialMap_toAlgHom (g : ι → I) :
    (cotangentGradedPolynomialMap I g).toAlgHom = cotangentPolynomialMap I g := rfl

/-- The graded map retains every literal original Rees numerator. -/
theorem cotangentGradedPolynomialMap_X (g : ι → I) (i : ι) :
    cotangentGradedPolynomialMap I g (MvPolynomial.X i) =
      Ideal.Quotient.mk I.associatedGradedIdeal (reesAlgebra.degreeOne I (g i)) :=
  cotangentPolynomialMap_X I g i

/-- The graded map retains the canonical action of every original coefficient class. -/
theorem cotangentGradedPolynomialMap_C (g : ι → I) (a : A ⧸ I) :
    cotangentGradedPolynomialMap I g (MvPolynomial.C a) = associatedGradedCoefficientMap I a :=
  cotangentPolynomialMap_C I g a

/-- The graded map retains the original scalar map before coefficient reduction. -/
theorem cotangentGradedPolynomialMap_C_mk (g : ι → I) (a : A) :
    cotangentGradedPolynomialMap I g (MvPolynomial.C (Ideal.Quotient.mk I a)) =
      algebraMap A I.associatedGraded a := cotangentPolynomialMap_C_mk I g a

/-- Actual cotangent spanning makes the original polynomial map onto. -/
theorem cotangentPolynomialMap_surjective_of_cotangent_span (g : ι → I)
    (hgen : Submodule.span (A ⧸ I) (Set.range fun i => I.toCotangent (g i)) = ⊤) :
    Function.Surjective (cotangentPolynomialMap I g) := by
  let f := cotangentPolynomialMap I g
  have hs (v : I.Cotangent) : cotangentSymbol I v ∈ f.range := by
    have hv : v ∈ Submodule.span (A ⧸ I) (Set.range fun i => I.toCotangent (g i)) := by
      rw [hgen]
      trivial
    induction hv using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      exact ⟨MvPolynomial.X i, cotangentPolynomialMap_X_cotangent I g i⟩
    | zero => simpa only [map_zero] using f.range.zero_mem
    | add x y hx hy ihx ihy => simpa only [map_add] using f.range.add_mem ihx ihy
    | smul r x hx ih => simpa only [map_smul] using f.range.smul_mem ih r
  have hsym (v : SymmetricAlgebra (A ⧸ I) I.Cotangent) :
      symmetricCotangentMap I v ∈ f.range := by
    induction v using SymmetricAlgebra.induction with
    | algebraMap r =>
      rw [AlgHom.commutes]
      exact f.range.algebraMap_mem r
    | ι v =>
      obtain ⟨a, rfl⟩ := I.toCotangent_surjective v
      simpa only [symmetricCotangentMap_iota_toCotangent, cotangentSymbol_toCotangent] using
        hs (I.toCotangent a)
    | mul x y hx hy => simpa only [map_mul] using f.range.mul_mem hx hy
    | add x y hx hy => simpa only [map_add] using f.range.add_mem hx hy
  intro x
  obtain ⟨v, rfl⟩ := symmetricCotangentMap_surjective I x
  exact hsym v

/-- Actual ideal generation gives actual cotangent spanning over the coefficient quotient. -/
theorem cotangent_span_of_ideal_span (g : ι → I)
    (hgen : Ideal.span (Set.range fun i => (g i : A)) = I) :
    Submodule.span (A ⧸ I) (Set.range fun i => I.toCotangent (g i)) = ⊤ := by
  have hg : Submodule.span A (Set.range g) = ⊤ :=
    (Submodule.span_range_subtype_eq_top_iff I (s := fun i => (g i : A))
      (fun i => (g i).property)).mpr hgen
  have hmap := congrArg (Submodule.map I.toCotangent) hg
  rw [Submodule.map_span, ← Set.range_comp', Submodule.map_top, I.toCotangent_range] at hmap
  rw [← Submodule.restrictScalars_eq_top_iff A,
    Submodule.restrictScalars_span A (A ⧸ I) Ideal.Quotient.mk_surjective]
  exact hmap

/-- Actual cotangent generation proves surjectivity of the literal graded map. -/
theorem cotangentGradedPolynomialMap_surjective_of_cotangent_span (g : ι → I)
    (hgen : Submodule.span (A ⧸ I) (Set.range fun i => I.toCotangent (g i)) = ⊤) :
    Function.Surjective (cotangentGradedPolynomialMap I g) :=
  cotangentPolynomialMap_surjective_of_cotangent_span I g hgen

/-- Actual ideal generation proves surjectivity of the literal graded map.
No basis, presentation, Hilbert function or Noetherian hypothesis is used. -/
theorem cotangentGradedPolynomialMap_surjective (g : ι → I)
    (hgen : Ideal.span (Set.range fun i => (g i : A)) = I) :
    Function.Surjective (cotangentGradedPolynomialMap I g) :=
  cotangentGradedPolynomialMap_surjective_of_cotangent_span I g
    (cotangent_span_of_ideal_span I g hgen)

end Ideal
