/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.NoetherNormalization.Dimension

/-! The intrinsic conclusion exposes no chosen normalization or number of variables. -/

@[expose] public noncomputable section

universe u v

example (k : Type u) [Field k] (A : Type v) [CommRing A] [IsDomain A]
    [Algebra k A] [Algebra.FiniteType k A] (p : Ideal A) [p.IsMaximal] :
    (p.height : WithBot ℕ∞) = ringKrullDim A :=
  Ideal.height_eq_ringKrullDim_of_finiteType_field k A p

end
