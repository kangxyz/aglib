/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.Algebra.Module.CommutingAutomorphisms.SupportDominance
public import Mathlib.RingTheory.Length
public import Mathlib.RingTheory.HopkinsLevitzki
public import Mathlib.RingTheory.KrullDimension.Zero
public import Mathlib.RingTheory.Localization.Submodule

/-!
# Finite local lengths on the actual Grayson support

These are lengths of the original represented module localized on its ACTUAL
support algebra. Finiteness is derived at minimal support primes. They are the
intrinsic multiplicities needed for the cycle map; no length parameter is
supplied. Ambient-localization comparison, object invariance, and the direct-sum
and base-change multiplicity formulas are not claimed in this leaf.
-/
/-!
## Migration source

Native extraction from
`lean/R5Lab/Aglib/Algebra/Module/CommutingAutomorphisms/LocalMultiplicity.lean` at R5 revision
`f8a3314ddecffcada2ec721d26d56a937bed9690`, SHA-256
`5f0c16b054207e326bb018499074de71f1b4ee03e0a60634dcd8dc3ca6b091a2`.
-/

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped _root_.TensorProduct
namespace Module.CommutingAutomorphisms.LaurentSupport
universe u
attribute [local instance] supportModule
variable {R : Type u} [CommRing R]

/-- Localization of the original module over its actual support algebra. -/
abbrev LocalSupportModule (X : Object R) (p : Ideal (Support X)) [p.IsPrime] :=
  Localization.AtPrime p ⊗[Support X] X.carrier

instance localSupportAddCommGroup (X : Object R) (p : Ideal (Support X)) [p.IsPrime] :
    AddCommGroup (LocalSupportModule X p) :=
  @TensorProduct.addCommGroup (Support X) _ (Localization.AtPrime p) X.carrier _ _ _ _

/-- Intrinsic local length, before proving that it is finite. -/
def localLength (X : Object R) (p : Ideal (Support X)) [p.IsPrime] : ℕ∞ :=
  Module.length (Localization.AtPrime p) (LocalSupportModule X p)

/-- Minimal support localizations are Artinian by finite support over the
Noetherian base and the zero-dimensional minimal-prime localization. -/
theorem minimal_support_local_artinian [IsNoetherianRing R] (X : Object R)
    (p : Ideal (Support X)) [p.IsPrime] (hp : p ∈ minimalPrimes (Support X)) :
    IsArtinianRing (Localization.AtPrime p) := by
  let : IsNoetherianRing (Support X) := IsNoetherianRing.of_finite R (Support X)
  let : Ring.KrullDimLE 0 (Localization.AtPrime p) :=
    Ring.KrullDimLE.of_isLocalization p hp (Localization.AtPrime p)
  exact IsNoetherianRing.isArtinianRing_of_krullDimLE_zero (R := Localization.AtPrime p)

/-- The actual localized module has finite length at every minimal support prime. -/
theorem localLength_ne_top [IsNoetherianRing R] (X : Object R)
    (p : Ideal (Support X)) [p.IsPrime] (hp : p ∈ minimalPrimes (Support X)) :
    localLength X p ≠ ⊤ := by
  let := supportModule_finite X
  let : IsNoetherianRing (Support X) := IsNoetherianRing.of_finite R (Support X)
  let : IsArtinianRing (Localization.AtPrime p) := minimal_support_local_artinian X p hp
  apply Module.length_ne_top_iff.mpr
  apply isFiniteLength_iff_isNoetherian_isArtinian.mpr
  exact ⟨inferInstance, inferInstance⟩

/-- The numerical local multiplicity of this actual module. -/
def multiplicity (X : Object R) (p : Ideal (Support X)) [p.IsPrime] : ℕ :=
  (localLength X p).toNat

/-- At minimal support primes the numerical multiplicity retains the full
module length; no infinite value has been silently discarded. -/
theorem multiplicity_coe [IsNoetherianRing R] (X : Object R)
    (p : Ideal (Support X)) [p.IsPrime] (hp : p ∈ minimalPrimes (Support X)) :
    (multiplicity X p : ℕ∞) = localLength X p :=
  ENat.natCast_toNat (localLength_ne_top X p hp)

end Module.CommutingAutomorphisms.LaurentSupport
