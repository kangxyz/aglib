/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.Algebra.Module.Equiv.Basic

/-! # Linearity through original scalar-map value laws -/

@[expose] public section

namespace AddEquiv

/-- Translate both original scalar maps to the complete native linearity law
before instantiating the cohomology carriers and their module dictionaries. -/
theorem map_smul_of_scalarMaps {R A B : Type*} [Semiring R]
    [AddCommGroup A] [AddCommGroup B] [Module R A] [Module R B]
    (e : A ≃+ B) (a : R → A → A) (b : R → B → B)
    (ha : ∀ (r : R) (x : A), r • x = a r x)
    (hb : ∀ (r : R) (y : B), r • y = b r y)
    (he : ∀ (r : R) (x : A), e (a r x) = b r (e x)) :
    ∀ (r : R) (x : A), e (r • x) = r • e x :=
  fun r x => (congrArg e (ha r x)).trans ((he r x).trans (hb r (e x)).symm)

end AddEquiv
