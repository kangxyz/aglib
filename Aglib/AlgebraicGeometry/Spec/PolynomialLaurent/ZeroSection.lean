/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Spec.PolynomialLaurent.Basic

/-!
Source:
`Quillen/AlgebraicGeometry/PerfectComplexes/ProjectiveLine/BassPositiveCharts.lean`
at LOCAL Quillen
`189a8e779f0c68b2dfc6f8195daebb3e684a5905`.
Source SHA-256: `0db622409af6393aa5dd691ccba71a7f4ea6809bac45fe9d1c4a24cfe15bc9d7`.
Selected declaration ranges: [[141, 152]].
Actual maps and premises are preserved; the generic truncation lift is recorded explicitly.
-/

/-! # The zero section of the affine polynomial projection -/
@[expose] public section
noncomputable section
universe u
open CategoryTheory AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.PolynomialLaurent

/-- Polynomial evaluation at zero gives the literal scheme zero section. -/
def polynomialZeroSection (R : CommRingCat.{u}) : Spec R ⟶ Spec (.of (Polynomial R)) :=
  Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : R)))

@[reassoc (attr := simp)]
lemma polynomialZeroSection_projection (R : CommRingCat.{u}) :
    polynomialZeroSection R ≫ polynomialProjection R = 𝟙 (Spec R) := by
  have h : CommRingCat.ofHom (Polynomial.C : R →+* Polynomial R) ≫
      CommRingCat.ofHom (Polynomial.evalRingHom (0 : R)) = 𝟙 R := by
    ext r
    exact Polynomial.eval_C
  change Spec.map _ ≫ Spec.map _ = _
  rw [← Spec.map_comp, h, Spec.map_id]

end AlgebraicGeometry.Scheme.PolynomialLaurent
