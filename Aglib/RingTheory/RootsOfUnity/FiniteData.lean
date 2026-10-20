/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots

/-!
# Finite data preserving prime roots

Source: `R5Lab.Aglib.RingTheory.RootsOfUnity.FiniteData`,
revision `f8a3314ddecffcada2ec721d26d56a937bed9690`. Exact field, action, embedding and
explicit-data hypotheses are retained. Native objects and maps are reused.
-/

@[expose] public section

namespace RootsOfUnity
universe u
variable {K : Type u} [Field K]
/-- Finite additional values that retain the root and prevent its collapse to
one or to characteristic equal to the prime. -/
noncomputable def primeRootExtraData (q : ℕ) (ζ : Kˣ) (extra : Finset K) : Finset K := by
  classical
  exact extra ∪ {(ζ : K), ((ζ⁻¹ : Kˣ) : K), (ζ : K) - 1, ((ζ : K) - 1)⁻¹,
    (q : K), (q : K)⁻¹}

end RootsOfUnity
