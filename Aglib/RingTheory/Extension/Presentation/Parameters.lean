/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.Extension.Generators.Parameters
public import Mathlib.RingTheory.Extension.Presentation.Basic

/-! # Presentations after absorbing polynomial parameters

The same relation index presents the algebra over the polynomial parameter ring.
Every relation is transported by the actual iterated-polynomial equivalence. Thus
native presentation base change applies with the whole relation ideal, not merely
with a selected family of Jacobian minors.
-/

@[expose] public noncomputable section

open MvPolynomial

namespace Algebra.Presentation

variable {R B α β σ : Type*} [CommRing R] [CommRing B] [Algebra R B]
variable [Algebra (MvPolynomial α R) B] [IsScalarTower R (MvPolynomial α R) B]

set_option backward.isDefEq.respectTransparency false in
/-- Absorb polynomial parameter coordinates while retaining an actual generating
family for the entire relation ideal. -/
def absorbPolynomialParameters (P : Presentation R B (β ⊕ α) σ)
    (ha : ∀ i, algebraMap (MvPolynomial α R) B (X i) = P.val (.inr i)) :
    Presentation (MvPolynomial α R) B β σ where
  toGenerators := P.toGenerators.absorbParameters X ha
  relation j := parameterSubstitution X (P.relation j)
  span_range_relation_eq_ker := by
    have h := congrArg
      (Ideal.map (parameterSubstitution (R := R) (β := β)
        (X : α → MvPolynomial α R)).toRingHom) P.span_range_relation_eq_ker
    rw [Ideal.map_span, ← Set.range_comp'] at h
    exact h.trans (P.toGenerators.map_ker_absorbPolynomialParameters ha)

end Algebra.Presentation
