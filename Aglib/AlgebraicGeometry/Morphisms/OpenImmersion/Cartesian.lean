/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.AlgebraicGeometry.Limits

/-!
Source:
`Quillen/AlgebraicGeometry/PerfectComplexes/ProjectiveLine/NativeBinaryUnion.lean`
at LOCAL Quillen
`189a8e779f0c68b2dfc6f8195daebb3e684a5905`.
Source SHA-256: `753edb4d726375560ba033777b732becd608e08ed46eed0408de42c90ba10b91`.
Selected declaration ranges: [[44, 50]].
Actual maps and premises are preserved; the generic truncation lift is recorded explicitly.
-/

/-! # Open ranges in a cartesian scheme square -/
@[expose] public section
noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.Hom

/-- In a displayed pullback square, an open range is the exact inverse-image open. -/
theorem opensRange_of_isPullback {W U V X : Scheme.{u}}
    (a : W ⟶ U) (b : W ⟶ V) (f : U ⟶ X) (g : V ⟶ X)
    [IsOpenImmersion a] [IsOpenImmersion g] (h : IsPullback a b f g) :
    a.opensRange = f ⁻¹ᵁ g.opensRange := by
  have hh : (h.isoPullback.hom ≫ pullback.fst f g).opensRange = f ⁻¹ᵁ g.opensRange := by
    rw [Scheme.Hom.opensRange_comp_of_isIso, Scheme.Hom.opensRange_pullbackFst]
  simpa only [h.isoPullback_hom_fst] using hh

end AlgebraicGeometry.Scheme.Hom
