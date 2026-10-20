/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.Torus.FiniteCorrespondence.FibreLength
public import Aglib.Algebra.Module.CommutingAutomorphisms.PrincipalRegularity
public import Mathlib.Algebra.FreeAbelianGroup.Finsupp

/-!
# PrincipalFibres for finite correspondences on the two-dimensional torus

Native migration from `lean/R5Lab/Aglib/AlgebraicGeometry/Torus/FiniteCorrespondence/`
leaf `PrincipalFibres.lean` at R5 revision
`f8a3314ddecffcada2ec721d26d56a937bed9690`, SHA-256
`e23e14980356427a867270dd0897ee3f9162f628a244160be57a5caacf8ce6b6`.

The Laurent object is `MonoidAlgebra R (Multiplicative (ℤ × ℤ))` in its original
coordinate order. Statements retain their displayed finiteness, normality,
Noetherianity, flatness, regularity and scalar-map hypotheses.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped TensorProduct AlgebraMonoidAlgebra
namespace AlgebraicGeometry.Torus.FiniteCorrespondence
open _root_.Module.CommutingAutomorphisms
open _root_.Module.CommutingAutomorphisms.LaurentSupport
open MonoidAlgebra (FiniteDominantPrime)
open LaurentSupport
universe u
variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]

/-- Literal local length of the fibre of a source prime quotient. In a nonflat face this
depends on p as well as q.

Source mapping: supporting generalized local construction for
`K2-018#prop:k2018-arithmetic-characters`, source snapshot
`e73d98b1b5c1e5abcdebf7d058e436d792b87982`.
Encoded prerequisite subset: the literal ENat fibre length for source and target FiniteDominantPrime
labels using the actual coefficient map; finiteness and faithful Nat casting require the
separate IsNoetherianRing S hypotheses. -/
def quotientFibreLength (p : FiniteDominantPrime R) (q : FiniteDominantPrime S) : ℕ∞ :=
  Module.length (Localization.AtPrime q.val)
    (Localization.AtPrime q.val ⊗[Laurent S]
      (Laurent S ⧸ p.val.map (coefficientMap (algebraMap R S))))

theorem quotientFibreLength_ne_zero_iff (p : FiniteDominantPrime R) (q : FiniteDominantPrime S) :
    quotientFibreLength (S := S) p q ≠ 0 ↔
      p.val.map (coefficientMap (algebraMap R S)) ≤ q.val := by
  let C := Laurent S ⧸ p.val.map (coefficientMap (algebraMap R S))
  let : Module.Finite (Laurent S) (Laurent S) := Module.Finite.self _
  let : Module.Finite (Laurent S) C := Module.Finite.of_surjective
    (p.val.map (coefficientMap (algebraMap R S))).mkQ (Submodule.mkQ_surjective _)
  let e := IsLocalizedModule.iso q.val.primeCompl
    (TensorProduct.mk (Laurent S) (Localization.AtPrime q.val) C 1)
  have hs : Nontrivial (Localization.AtPrime q.val ⊗[Laurent S] C) ↔
      Nontrivial (LocalizedModule q.val.primeCompl C) :=
    ⟨fun h => by let := h; exact e.nontrivial,
      fun h => by let := h; exact e.symm.nontrivial⟩
  change Module.length (Localization.AtPrime q.val)
    (Localization.AtPrime q.val ⊗[Laurent S] C) ≠ 0 ↔ _
  rw [ne_eq, Module.length_eq_zero_iff, not_subsingleton_iff_nontrivial, hs]
  change (⟨q.val, inferInstance⟩ : PrimeSpectrum (Laurent S)) ∈ Module.support (Laurent S) C ↔ _
  rw [Module.mem_support_iff_of_finite, Ideal.annihilator_quotient]

theorem quotientFibreLength_ne_top [IsNoetherianRing S] (p : FiniteDominantPrime R) (q :
    FiniteDominantPrime S) :
    quotientFibreLength (S := S) p q ≠ ⊤ := by
  by_cases h : p.val.map (coefficientMap (algebraMap R S)) ≤ q.val
  · let := quotientBaseChange_finite (S := S) p.val
    let : IsNoetherianRing (Laurent S ⧸ p.val.map (coefficientMap (algebraMap R S))) :=
      IsNoetherianRing.of_finite S _
    exact Module.length_localized_quotient_ne_top _ q.val
      (minimal_of_finite_quotient_le _ q.val q.under_eq_bot h)
  · have hz : quotientFibreLength (S := S) p q = 0 := by
      by_contra hn
      exact h ((quotientFibreLength_ne_zero_iff p q).mp hn)
    rw [hz]
    exact ENat.zero_ne_top

/-- The natural-number interpretation of the extended localized quotient-fibre length at `q`. -/
def quotientFibreMultiplicity (p : FiniteDominantPrime R) (q : FiniteDominantPrime S) : ℕ :=
  (quotientFibreLength (S := S) p q).toNat

theorem quotientFibreMultiplicity_coe [IsNoetherianRing S] (p : FiniteDominantPrime R) (q :
    FiniteDominantPrime S) :
    (quotientFibreMultiplicity (S := S) p q : ℕ∞) = quotientFibreLength (S := S) p q :=
  ENat.natCast_toNat (quotientFibreLength_ne_top p q)

theorem quotientFibreMultiplicity_ne_zero_iff [IsNoetherianRing S] (p : FiniteDominantPrime R) (q
    : FiniteDominantPrime S) :
    quotientFibreMultiplicity (S := S) p q ≠ 0 ↔
      p.val.map (coefficientMap (algebraMap R S)) ≤ q.val := by
  rw [← quotientFibreLength_ne_zero_iff p q, ← quotientFibreMultiplicity_coe p q]
  exact_mod_cast Iff.rfl

theorem finite_pointQuotientFibre [IsNoetherianRing S] (p : FiniteDominantPrime R) :
    {q : FiniteDominantPrime S | p.val.map (coefficientMap (algebraMap R S)) ≤ q.val}.Finite := by
  apply ((finite_minimalFibre (S := S) p).preimage
    (f := fun q : FiniteDominantPrime S => q.val) Subtype.val_injective.injOn).subset
  intro q hq
  let := quotientBaseChange_finite (S := S) p.val
  exact minimal_of_finite_quotient_le _ q.val q.under_eq_bot hq

/-- The finitely supported integer coefficients obtained from the quotient-fibre multiplicities. -/
def quotientFibreCoefficients [IsNoetherianRing S] (p : FiniteDominantPrime R) :
    FiniteDominantPrime S →₀ ℤ :=
  Finsupp.ofSupportFinite (fun q => (quotientFibreMultiplicity (S := S) p q : ℤ)) (by
    apply (finite_pointQuotientFibre (S := S) p).subset
    intro q hq
    apply (quotientFibreMultiplicity_ne_zero_iff p q).mp
    intro h
    exact hq (by simp [h]))

/-- The additive cycle map sending each prime label to its quotient-fibre cycle. -/
def quotientFibreCycleMap [IsNoetherianRing S] :
    FreeAbelianGroup (FiniteDominantPrime R) →+ FreeAbelianGroup (FiniteDominantPrime S) :=
  FreeAbelianGroup.lift (fun p => Finsupp.toFreeAbelianGroup (quotientFibreCoefficients (S := S) p))

theorem quotientFibreCycleMap_of_coeff [IsNoetherianRing S] (p : FiniteDominantPrime R) (q :
    FiniteDominantPrime S) :
    FreeAbelianGroup.coeff q (quotientFibreCycleMap (S := S) (FreeAbelianGroup.of p)) =
      (quotientFibreMultiplicity (S := S) p q : ℤ) := by
  simp [quotientFibreCycleMap, FreeAbelianGroup.coeff, quotientFibreCoefficients]

theorem quotientFibreCycleMap_of_support [IsNoetherianRing S] (p : FiniteDominantPrime R) (q :
    FiniteDominantPrime S) :
    q ∈ (quotientFibreCycleMap (S := S) (FreeAbelianGroup.of p)).support ↔
      p.val.map (coefficientMap (algebraMap R S)) ≤ q.val := by
  rw [FreeAbelianGroup.mem_support_iff, quotientFibreCycleMap_of_coeff]
  simpa only [Nat.cast_ne_zero] using quotientFibreMultiplicity_ne_zero_iff p q

end AlgebraicGeometry.Torus.FiniteCorrespondence
