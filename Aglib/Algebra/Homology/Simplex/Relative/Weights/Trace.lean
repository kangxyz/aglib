/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Aglib.Algebra.Homology.Simplex.Relative.FiniteReindex
public import Aglib.Algebra.Homology.Simplex.Relative.Weights.ProjectionHomology

/-!
# Literal original-coefficient traces on full-support Laurent weights

The actual coefficient chain projection, followed by the native finite-simplex
top comparison, defines a scalar-linear trace on original raw homology. Its
cycles formula is exactly the original Laurent coefficient at the chosen
enumeration, preserving the original cycles quotient and positive sign.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory HomologicalComplex AlgebraicTopology

universe u

namespace MvPolynomial

variable {ι : Type u} (R : Type u) [CommRing R]

/-- The original coefficient projection followed by the native top scalar
comparison of a full-support weight, in the original geometric universe. -/
def coordinateLaurentWeightTrace (n : ℕ) (e : ι ≃ Fin (n + 1)) (d : ℤ)
    (w : coordinateLaurentWeight (ι := ι) d)
    (hw : coordinateNegativeSupport w.val = Set.univ) :
    (coordinateLaurentTupleComplex (ι := ι) R d).homology n →ₗ[R] R :=
  (RelativeSimplex.topHomologyLinearEquivOfEqUnivOfEquivFin (R := R) n e _ hw).toLinearMap.comp
    (homologyMap (coordinateLaurentWeightComplexProjection R d w) n).hom

/-- The actual raw trace is the literal original coefficient on the enumerated
tuple, after the unchanged cycles quotient, with no additional sign. -/
theorem coordinateLaurentWeightTrace_homologyπ (n : ℕ) (e : ι ≃ Fin (n + 1)) (d : ℤ)
    (w : coordinateLaurentWeight (ι := ι) d)
    (hw : coordinateNegativeSupport w.val = Set.univ)
    (c : (coordinateLaurentTupleComplex (ι := ι) R d).cycles n) :
    coordinateLaurentWeightTrace R n e d w hw
        ((coordinateLaurentTupleComplex (ι := ι) R d).homologyπ n c) =
      ((coordinateLaurentTupleComplex (ι := ι) R d).iCycles n c e.symm).val.coeff
        (coordinateWeightExponent e.symm w (fun i _ => ⟨e i, e.symm_apply_apply i⟩)) := by
  change RelativeSimplex.topHomologyLinearEquivOfEqUnivOfEquivFin (R := R) n e _ hw
    (homologyMap (coordinateLaurentWeightComplexProjection R d w) n
      ((coordinateLaurentTupleComplex (ι := ι) R d).homologyπ n c)) = _
  have hπ := ConcreteCategory.congr_hom
    (homologyπ_naturality (coordinateLaurentWeightComplexProjection R d w) n) c
  change homologyMap (coordinateLaurentWeightComplexProjection R d w) n
      ((coordinateLaurentTupleComplex (ι := ι) R d).homologyπ n c) =
    (RelativeSimplex.complex R (coordinateNegativeSupport w.val)).homologyπ n
      (cyclesMap (coordinateLaurentWeightComplexProjection R d w) n c) at hπ
  rw [hπ, RelativeSimplex.topHomologyLinearEquivOfEqUnivOfEquivFin_homologyπ]
  have hi := ConcreteCategory.congr_hom
    (cyclesMap_i (coordinateLaurentWeightComplexProjection R d w) n) c
  change (RelativeSimplex.complex R (coordinateNegativeSupport w.val)).iCycles n
      (cyclesMap (coordinateLaurentWeightComplexProjection R d w) n c) =
    (coordinateLaurentWeightComplexProjection R d w).f n
      ((coordinateLaurentTupleComplex (ι := ι) R d).iCycles n c) at hi
  rw [hi]
  rfl

/-- The same trace uses the original weight-homology component of the existing
native decomposition, rather than a replacement cohomology map. -/
theorem coordinateLaurentWeightTrace_eq_component [Finite ι]
    (n : ℕ) (e : ι ≃ Fin (n + 1)) (d : ℤ)
    (w : coordinateLaurentWeight (ι := ι) d)
    (hw : coordinateNegativeSupport w.val = Set.univ)
    (x : (coordinateLaurentTupleComplex (ι := ι) R d).homology n) :
    coordinateLaurentWeightTrace R n e d w hw x =
      RelativeSimplex.topHomologyLinearEquivOfEqUnivOfEquivFin (R := R) n e _ hw
        (coordinateLaurentTupleHomologyWeightsEquiv (ι := ι) R d n x w) := by
  rw [coordinateLaurentTupleHomologyWeightsEquiv_apply_eq_projection]
  rfl

end MvPolynomial
