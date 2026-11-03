/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.Blowup.RegularPair.Exterior
public import Aglib.RingTheory.Kaehler.Exterior.BaseChange
public import Aglib.RingTheory.Kaehler.Exterior.Map


/-!
# RingTheory / Blowup / RegularPair / RawExterior

Source: `IntegralTrace/RawImageBound.lean`.
Incoming SHA256: `cb04954aedb63ec4a5105adff32da7b556b8d14eaada1dbceb2ba93a787cda12`.
The original constructors, maps, universe bounds and mathematical hypotheses are retained.
-/

@[expose] public noncomputable section


open scoped TensorProduct

universe u v w


open KaehlerDifferential

namespace Localization.Away

variable {R : Type u} [CommRing R] (x y : R)
  (Λ : Type w) [CommRing Λ] [Algebra Λ R]

/-- The genuine regular-pair exceptional image bound on the actual saturated
chart, expressed using the scalar extension of the original raw exterior. -/
theorem saturatedPair_exceptional_smul_rawExterior_mem_range
    (hx : IsSMulRegular R x) (hy : IsSMulRegular (R ⧸ Ideal.span {x}) y)
    (n : ℕ) (α : ⋀[saturatedChart R (Ideal.span {x, y}) x]^n
      (KaehlerDifferential Λ (saturatedChart R (Ideal.span {x, y}) x))) :
    algebraMap R (saturatedChart R (Ideal.span {x, y}) x) x • α ∈
      LinearMap.range (KaehlerDifferential.mapExteriorBaseChange Λ R
        (saturatedChart R (Ideal.span {x, y}) x) n) := by
  rw [KaehlerDifferential.mapExteriorBaseChange_range]
  exact saturatedPair_exceptional_smul_exterior_mem_range x y Λ hx hy n α

end Localization.Away
