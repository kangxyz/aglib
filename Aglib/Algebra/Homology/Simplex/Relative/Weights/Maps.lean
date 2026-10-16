/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.Simplex.Relative.Weights.Terms

/-!
# The original single-weight maps into the Laurent tuple complex

On a tuple permitting the selected weight, the map is the original Laurent
single monomial with the original relative-simplex cochain coefficient.
Other tuples get zero. The maps commute with every tuple-position map and
therefore give native cosimplicial maps and native chain maps. The finite
term exchange identifies them with the original DFinsupp summand inclusions.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Limits
open AlgebraicTopology

universe u v

namespace MvPolynomial

variable {ι : Type v} (R : Type u) [CommRing R]

/-- The actual scalar-linear insertion of one permitted Laurent monomial into
the original native degree piece. -/
def coordinateLaurentTupleWeightSingle (d : ℤ) {n : ℕ} (a : Fin (n + 1) → ι)
    (e : coordinateLaurentWeight (ι := ι) d) (he : coordinateWeightAllowed a e) :
    R →ₗ[R] coordinateGrading R (coordinateTupleSet a) d :=
  (coordinateGradeEquivFinsupp R (coordinateTupleSet a) d).symm.toLinearMap.comp
    (Finsupp.lsingle ⟨coordinateWeightExponent a e he, e.property⟩)

@[simp]
theorem coordinateLaurentTupleWeightSingle_val (d : ℤ) {n : ℕ} (a : Fin (n + 1) → ι)
    (e : coordinateLaurentWeight (ι := ι) d) (he : coordinateWeightAllowed a e) (r : R) :
    (coordinateLaurentTupleWeightSingle R d a e he r).val =
      AddMonoidAlgebra.single (coordinateWeightExponent a e he) r :=
  coordinateGradeEquivFinsupp_symm_single R (coordinateTupleSet a) d _ r

/-- A relative-simplex cochain in one actual weight, inserted into the original
Laurent tuple module by its literal single monomial. -/
def coordinateLaurentTupleWeightInjection (d : ℤ) (e : coordinateLaurentWeight (ι := ι) d)
    (n : ℕ) :
    RelativeSimplex.Cochains R (coordinateNegativeSupport e.val) n →ₗ[R]
      coordinateLaurentTupleCochains (ι := ι) R d n := by
  classical
  refine {
    toFun := fun x a => if ha : coordinateWeightAllowed a e then
      coordinateLaurentTupleWeightSingle R d a e ha (x ⟨a, ha⟩) else 0
    map_add' := ?_
    map_smul' := ?_ }
  · intro x y
    funext a
    by_cases ha : coordinateNegativeSupport e.val ⊆ Set.range a
    · simp only [coordinateWeightAllowed, dite_eq_left ha, Pi.add_apply]
      exact (coordinateLaurentTupleWeightSingle R d a e ha).map_add
        (x ⟨a, ha⟩) (y ⟨a, ha⟩)
    · simp [coordinateWeightAllowed, ha]
  · intro r x
    funext a
    by_cases ha : coordinateNegativeSupport e.val ⊆ Set.range a
    · simp only [coordinateWeightAllowed, dite_eq_left ha, Pi.smul_apply]
      exact (coordinateLaurentTupleWeightSingle R d a e ha).map_smul r (x ⟨a, ha⟩)
    · simp [coordinateWeightAllowed, ha]

open Classical in
/-- The finite term exchange identifies the original weight injection with the
native dependent finitely supported summand inclusion. -/
theorem coordinateLaurentTupleWeightsEquiv_injection [Finite ι] (d : ℤ)
    (e : coordinateLaurentWeight (ι := ι) d) (n : ℕ)
    (x : RelativeSimplex.Cochains R (coordinateNegativeSupport e.val) n) :
    coordinateLaurentTupleWeightsEquiv (ι := ι) R d n
        (coordinateLaurentTupleWeightInjection R d e n x) = DFinsupp.single e x := by
  classical
  apply DFinsupp.ext
  intro e'
  funext a
  rw [coordinateLaurentTupleWeightsEquiv_apply]
  by_cases he : e = e'
  · subst e'
    simp [coordinateLaurentTupleWeightInjection, a.property,
      AddMonoidAlgebra.coeff_single]
  · by_cases ha : coordinateWeightAllowed a.val e
    · have hne : coordinateWeightExponent a.val e ha ≠
          coordinateWeightExponent a.val e' a.property := by
        intro h
        exact he (Subtype.ext (congrArg
          (fun z : coordinateExponentMonoid (coordinateTupleSet a.val) => z.val) h))
      simp [coordinateLaurentTupleWeightInjection, ha, coordinateLaurentTupleWeightSingle_val,
        AddMonoidAlgebra.coeff_single, hne, he]
    · simp [coordinateLaurentTupleWeightInjection, ha, he]

/-- The single-weight inclusion commutes with the actual native coordinate
restriction for every map of tuple positions. -/
theorem coordinateLaurentTupleWeightInjection_naturality (d : ℤ)
    (e : coordinateLaurentWeight (ι := ι) d) {m n : ℕ}
    (f : Fin (m + 1) → Fin (n + 1))
    (x : RelativeSimplex.Cochains R (coordinateNegativeSupport e.val) m) :
    coordinateLaurentTuplePositionMap R d f (coordinateLaurentTupleWeightInjection R d e m x) =
      coordinateLaurentTupleWeightInjection R d e n (RelativeSimplex.positionMap f x) := by
  classical
  funext a
  change coordinateLaurentDegreeMap R (coordinateTupleSet_comp_subset a f) d
      (coordinateLaurentTupleWeightInjection R d e m x (a ∘ f)) =
    coordinateLaurentTupleWeightInjection R d e n (RelativeSimplex.positionMap f x) a
  by_cases ha : coordinateWeightAllowed a e
  · by_cases hf : coordinateWeightAllowed (a ∘ f) e
    · simp only [coordinateLaurentTupleWeightInjection, LinearMap.coe_mk, AddHom.coe_mk,
        dite_eq_left ha, dite_eq_left hf, RelativeSimplex.positionMap,
        RelativeSimplex.extendByZero]
      apply Subtype.ext
      change coordinateLaurentMap R (coordinateTupleSet_comp_subset a f)
          (coordinateLaurentTupleWeightSingle R d (a ∘ f) e hf (x ⟨a ∘ f, hf⟩)).val = _
      rw [coordinateLaurentTupleWeightSingle_val, coordinateLaurentMap_single,
        coordinateLaurentTupleWeightSingle_val]
      congr 1
    · simp [coordinateLaurentTupleWeightInjection, ha, hf, RelativeSimplex.positionMap,
        RelativeSimplex.extendByZero]
  · have hf : ¬ coordinateWeightAllowed (a ∘ f) e :=
      fun h => ha (RelativeSimplex.supported_of_comp h)
    simp [coordinateLaurentTupleWeightInjection, ha, hf]

/-- The original single-weight maps form a genuine cosimplicial map. -/
def coordinateLaurentWeightCosimplicialMap (d : ℤ) (e : coordinateLaurentWeight (ι := ι) d) :
    RelativeSimplex.cosimplicial R (coordinateNegativeSupport e.val) ⟶
      coordinateLaurentTupleCosimplicial (ι := ι) R d where
  app n := ModuleCat.ofHom (coordinateLaurentTupleWeightInjection R d e n.len)
  naturality {_ _} f := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    exact (coordinateLaurentTupleWeightInjection_naturality R d e f.toOrderHom x).symm

/-- The actual native chain map from one unchanged relative-simplex weight
complex into the original unbounded Laurent tuple complex. -/
def coordinateLaurentWeightComplexMap (d : ℤ) (e : coordinateLaurentWeight (ι := ι) d) :
    RelativeSimplex.complex R (coordinateNegativeSupport e.val) ⟶
      coordinateLaurentTupleComplex (ι := ι) R d :=
  (alternatingCofaceMapComplex _).map (coordinateLaurentWeightCosimplicialMap R d e)

@[simp]
theorem coordinateLaurentWeightComplexMap_f (d : ℤ)
    (e : coordinateLaurentWeight (ι := ι) d) (n : ℕ) :
    (coordinateLaurentWeightComplexMap R d e).f n =
      ModuleCat.ofHom (coordinateLaurentTupleWeightInjection R d e n) := rfl

end MvPolynomial
