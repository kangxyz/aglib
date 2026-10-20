/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.RingTheory.Localization.LengthSurjective
public import Aglib.Algebra.Module.CommutingAutomorphisms.Realization
public import Aglib.Algebra.Module.CommutingAutomorphisms.LocalMultiplicity
public import Mathlib.RingTheory.Localization.BaseChange
public import Mathlib.LinearAlgebra.TensorProduct.Prod

/-!
# Actual lengths over the ambient Laurent local ring

The localized original modules are compared over a common ring. The support
quotient comparison uses only a surjective coefficient map, not a supplied
length equality or a supplied multiplicity rule.
-/
/-!
## Migration source

Native extraction from `lean/R5Lab/Aglib/Algebra/Module/CommutingAutomorphisms/LocalLength.lean` at
R5 revision
`f8a3314ddecffcada2ec721d26d56a937bed9690`, SHA-256
`d0287170e11008925458d09686eea67be6f06fa3972e6f4c0eac860aafcd9550`.
-/

@[expose] public section

open _root_.Module (length_localization_of_surjective)

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped _root_.TensorProduct
namespace Module.CommutingAutomorphisms
open LaurentSupport
universe u v w

variable {R : Type u} [CommRing R]

/-- The tag also carries the already constructed ACTUAL support action. -/
instance realizationSupportModule (X : Object R) : Module (Support X) (Realization X) :=
  supportModule X

instance realizationSupportTower (X : Object R) :
    IsScalarTower (Laurent R) (Support X) (Realization X) where
  smul_assoc a b x := by
    induction b using Quotient.inductionOn' with
    | h b =>
      change representation X (a * b) x = representation X a (representation X b x)
      rw [map_mul]
      rfl

/-- The original Laurent module localized at an ambient torus prime. -/
abbrev LocalRealization (X : Object R) (p : Ideal (Laurent R)) [p.IsPrime] :=
  Localization.AtPrime p ⊗[Laurent R] Realization X

/-- Extended-natural length over the COMMON ambient Laurent local ring. -/
def ambientLength (X : Object R) (p : Ideal (Laurent R)) [p.IsPrime] : ℕ∞ :=
  Module.length (Localization.AtPrime p) (LocalRealization X p)

/-- Object isomorphisms localize as maps of the actual original modules. -/
def localRealizationIso {X Y : Object R} (e : Object.Iso X Y)
    (p : Ideal (Laurent R)) [p.IsPrime] :
    LocalRealization X p ≃ₗ[Localization.AtPrime p] LocalRealization Y p :=
  (realizationIso e).baseChange (Laurent R) (Localization.AtPrime p) _ _

/-- The original sum localizes to the product over the SAME local ring. -/
def localRealizationSum (X Y : Object R) (p : Ideal (Laurent R)) [p.IsPrime] :
    LocalRealization (X.sum Y) p ≃ₗ[Localization.AtPrime p]
      LocalRealization X p × LocalRealization Y p :=
  ((realizationSum X Y).baseChange (Laurent R) (Localization.AtPrime p) _ _).trans
    (TensorProduct.prodRight (Laurent R) (Localization.AtPrime p)
      (Localization.AtPrime p) (Realization X) (Realization Y))

theorem ambientLength_iso {X Y : Object R} (e : Object.Iso X Y)
    (p : Ideal (Laurent R)) [p.IsPrime] : ambientLength X p = ambientLength Y p :=
  (localRealizationIso e p).length_eq

/-- Additivity of actual local module lengths; support union alone is not used. -/
theorem ambientLength_sum (X Y : Object R) (p : Ideal (Laurent R)) [p.IsPrime] :
    ambientLength (X.sum Y) p = ambientLength X p + ambientLength Y p := by
  exact (localRealizationSum X Y p).length_eq.trans (Module.length_prod _ _ _)

/-- The intrinsic support length is EXACTLY the ambient local length of the
original module at the corresponding torus prime. -/
theorem ambientLength_eq_intrinsic (X : Object R) (p : Ideal (Support X)) [p.IsPrime] :
    ambientLength X (p.under (Laurent R)) = localLength X p :=
  length_localization_of_surjective (Realization X) Ideal.Quotient.mk_surjective p

/-- Actual ambient local lengths are finite on the original minimal components. -/
theorem ambientLength_ne_top [IsNoetherianRing R] (X : Object R)
    (p : Ideal (Laurent R)) [p.IsPrime] (hp : p ∈ (supportIdeal X).minimalPrimes) :
    ambientLength X p ≠ ⊤ := by
  rw [Ideal.minimalPrimes_eq_comap] at hp
  obtain ⟨q, hq, rfl⟩ := hp
  let : q.IsPrime := hq.isPrime
  change ambientLength X (q.under (Laurent R)) ≠ ⊤
  rw [ambientLength_eq_intrinsic]
  exact localLength_ne_top X q hq

end Module.CommutingAutomorphisms
