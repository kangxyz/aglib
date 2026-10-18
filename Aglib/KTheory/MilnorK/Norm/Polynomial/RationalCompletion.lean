/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.KTheory.MilnorK.Norm.Polynomial.RationalFunction
public import Aglib.KTheory.MilnorK.Residue.Polynomial.LaurentSeries

/-!
# The actual rational norm at the complete linear place

Whenever the whole constant presentation stays irreducible over Laurent series,
singleton coefficient base change and the proved local residue map reduce the
original rational norm to its complete-DVR polynomial norm. No complete norm
compatibility or upper residue identification is assumed in this reduction.
-/

@[expose] public noncomputable section

namespace MilnorK.PolynomialNorm

open Polynomial Polynomial.LocalResidue PolynomialResidue
open scoped RatFunc
attribute [local instance] Polynomial.algebra

variable {k : Type*} [Field k] [CharZero k]

local instance (p : MonicIrreducible k) :
    Fact (Irreducible (p.val.map (RatFunc.C : k →+* RatFunc k))) :=
  ⟨p.property.1.irreducible_map_ratFunc_C p.property.2⟩

/-- The literal root-field map from rational functions to the completed root field. -/
def rationalCompletionRootMap (p : MonicIrreducible k)
    (q : MonicIrreducible (LaurentSeries k))
    (hq : q.val = (rationalCoefficientPolynomial p).val.map
      (algebraMap (RatFunc k) (LaurentSeries k))) :
    RatFunc (AdjoinRoot p.val) →+* AdjoinRoot q.val :=
  (adjoinRootMap (algebraMap (RatFunc k) (LaurentSeries k))
    (rationalCoefficientPolynomial p).val q.val (hq ▸ dvd_rfl)).comp
      (AdjoinRoot.rationalCoefficientAlgEquiv p.val p.property.1).symm.toRingHom

/-- The rational norm restricts to the actual complete-field polynomial norm. -/
theorem rationalFunctionNorm_restrict_completion (n : ℕ) (p : MonicIrreducible k)
    (q : MonicIrreducible (LaurentSeries k))
    (hq : q.val = (rationalCoefficientPolynomial p).val.map
      (algebraMap (RatFunc k) (LaurentSeries k)))
    (x : K (RatFunc (AdjoinRoot p.val)) n) :
    map n (algebraMap (RatFunc k) (LaurentSeries k)) (rationalFunctionNorm n p x) =
      polynomialNorm n q (map n (rationalCompletionRootMap p q hq) x) := by
  unfold rationalFunctionNorm rationalCompletionRootMap
  rw [LinearMap.comp_apply, polynomialNorm_restrict_irreducible _ n _ q hq]
  unfold rationalCoefficientPolynomial
  rw [map_comp, LinearMap.comp_apply]

local instance : Fact (Irreducible (X : k[X])) := ⟨irreducible_X⟩

/-- The original rational norm's finite linear residue is its complete-field
norm's actual DVR residue, with the literal root-field restriction retained. -/
theorem residueAt_X_rationalFunctionNorm_eq_complete (n : ℕ) (p : MonicIrreducible k)
    (q : MonicIrreducible (LaurentSeries k))
    (hq : q.val = (rationalCoefficientPolynomial p).val.map
      (algebraMap (RatFunc k) (LaurentSeries k)))
    (x : K (RatFunc (AdjoinRoot p.val)) (n + 1)) :
    map n (InfinityResidue.rootXEquiv k).toRingHom
      (residueAt (X : k[X]) n (rationalFunctionNorm (n + 1) p x)) =
      map n PowerSeries.residueFieldOfPowerSeries.toRingHom
        (DVR.residue (PowerSeries k) (LaurentSeries k) n
          (polynomialNorm (n + 1) q (map (n + 1) (rationalCompletionRootMap p q hq) x))) := by
  rw [residueAt_X_eq_laurentSeries_residue, rationalFunctionNorm_restrict_completion _ p q hq]

end MilnorK.PolynomialNorm
