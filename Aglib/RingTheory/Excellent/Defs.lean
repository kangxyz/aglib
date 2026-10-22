/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.Excellent.GeometricConditions
public import Aglib.RingTheory.Excellent.RegularMap
public import Mathlib.RingTheory.AdicCompletion.Algebra

/-! # G-rings, quasi-excellent rings, and excellent rings

These definitions use only standard ring properties. No approximation property,
DVR condition, or completed fraction-field conclusion is included in them.
The second universe of quasi-excellence and excellence is an auxiliary universe
parameter `v`: finite-type test algebras live in `Type (max u v)` over a base in
`Type u`. No invariance under a change of the auxiliary universe is assumed.
-/

@[expose] public section

universe u v

/-- A Noetherian ring whose prime-local completion maps are regular. -/
def IsGRing (R : Type u) [CommRing R] : Prop :=
  IsNoetherianRing R ∧
  ∀ (p : Ideal R) [p.IsPrime],
    Algebra.IsRegularMap (Localization.AtPrime p)
      (AdicCompletion (IsLocalRing.maximalIdeal (Localization.AtPrime p))
        (Localization.AtPrime p))

/-- Quasi-excellence is the G-ring condition together with J-2. -/
def IsQuasiExcellentRing (R : Type u) [CommRing R] : Prop :=
  IsGRing R ∧ IsJ2Ring.{u, v} R

/-- Excellence is quasi-excellence together with universal catenarity. -/
def IsExcellentRing (R : Type u) [CommRing R] : Prop :=
  IsQuasiExcellentRing.{u, v} R ∧ IsUniversallyCatenaryRing.{u, v} R

/-- Only this standard component of excellence is needed for formal fibres. -/
theorem IsExcellentRing.isGRing {R : Type u} [CommRing R]
    (h : IsExcellentRing.{u, v} R) : IsGRing R := h.1.1
