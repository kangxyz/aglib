/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.Algebra.Module.CommutingAutomorphisms.SupportNaturality
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Ideal.MinimalPrime.Localization

/-!
# Dominant finite components of the actual Grayson support

Regular base scalars remain injective on the support algebra, because they are
injective on the original finite projective module. Consequently a minimal
prime of its actual Laurent annihilator contracts to zero over a domain.
Together with the derived finite support algebra this supplies actual dominant
finite irreducible supports. Localized length multiplicities and their scalar
and direct-sum formulas remain the next cycle construction.
-/
/-!
## Migration source

Native extraction from
`lean/R5Lab/Aglib/Algebra/Module/CommutingAutomorphisms/SupportDominance.lean` at R5 revision
`f8a3314ddecffcada2ec721d26d56a937bed9690`, SHA-256
`79a420ae9d782ca570a36bf781e7ab073568da4c9466f40e5412cf5ff920c4dc`.
-/

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace Module.CommutingAutomorphisms.LaurentSupport
universe u
variable {R : Type u} [CommRing R]

/-- Regular base scalars act injectively on the actual support algebra. -/
theorem support_scalar_regular (X : Object R) {r : R} (hr : IsRegular r) :
    IsSMulRegular (Support X) r := by
  intro a b h
  apply supportRepresentation_injective X
  apply LinearMap.ext
  intro x
  apply Module.Flat.isSMulRegular_of_isRegular (M := X.carrier) hr
  have hx := congrArg (fun z : Support X => supportRepresentation X z x) h
  simpa only [map_smul, LinearMap.smul_apply] using hx

instance support_torsionFree (X : Object R) : Module.IsTorsionFree R (Support X) :=
  ⟨fun _ hr => support_scalar_regular X hr⟩

/-- The zero module has precisely empty affine support; the construction does
not require or infer that every generator is nonzero. -/
theorem supportIdeal_eq_top_iff (X : Object R) :
    supportIdeal X = ⊤ ↔ Subsingleton X.carrier := by
  constructor
  · intro h
    have h1 : representation X (1 : Laurent R) = 0 := by
      change (1 : Laurent R) ∈ supportIdeal X
      rw [h]
      trivial
    rw [map_one] at h1
    refine ⟨fun x y => ?_⟩
    have hx : x = 0 := congrArg (fun f : Module.End R X.carrier => f x) h1
    have hy : y = 0 := congrArg (fun f : Module.End R X.carrier => f y) h1
    exact hx.trans hy.symm
  · intro h
    let := h
    apply top_unique
    intro p _
    change representation X p = 0
    exact Subsingleton.elim _ _

/-- Every actual minimal support prime lies above the generic base point. -/
theorem minimalPrime_contract [IsDomain R] (X : Object R) (p : Ideal (Laurent R))
    (hp : p ∈ (supportIdeal X).minimalPrimes) :
    p.comap (algebraMap R (Laurent R)) = ⊥ := by
  let := laurentModule X
  have hp' : p ∈ (Module.annihilator (Laurent R) X.carrier).minimalPrimes := by
    rw [← supportIdeal_eq_annihilator X]
    exact hp
  ext r
  rw [Ideal.mem_bot]
  change algebraMap R (Laurent R) r ∈ p ↔ r = 0
  constructor
  · intro hin
    by_contra hr
    have hreg : IsSMulRegular X.carrier (algebraMap R (Laurent R) r) := by
      change Function.Injective
        (fun x : X.carrier => representation X (algebraMap R (Laurent R) r) x)
      rw [AlgHom.commutes]
      exact Module.Flat.isSMulRegular_of_isRegular
        (R := R) (M := X.carrier) (IsRegular.of_ne_zero hr)
    exact hreg.notMem_of_mem_minimalPrimes hp' hin
  · rintro rfl
    simp

/-- Each component quotient is an actual finite algebra over the base. -/
theorem minimal_component_finite [IsNoetherianRing R] (X : Object R)
    (p : Ideal (Laurent R)) (hp : p ∈ (supportIdeal X).minimalPrimes) :
    Module.Finite R (Laurent R ⧸ p) :=
  Module.Finite.of_surjective (Ideal.Quotient.factorₐ R hp.le).toLinearMap
    (Ideal.Quotient.factor_surjective hp.le)

/-- Its coefficient homomorphism is injective, the affine dominance statement. -/
theorem minimal_component_dominant [IsDomain R] (X : Object R)
    (p : Ideal (Laurent R)) (hp : p ∈ (supportIdeal X).minimalPrimes) :
    Function.Injective (algebraMap R (Laurent R ⧸ p)) := by
  rw [RingHom.injective_iff_ker_eq_bot]
  ext r
  rw [Ideal.mem_bot]
  change Ideal.Quotient.mk p (algebraMap R (Laurent R) r) = 0 ↔ r = 0
  rw [Ideal.Quotient.eq_zero_iff_mem]
  have h := congrArg (fun I : Ideal R => r ∈ I) (minimalPrime_contract X p hp)
  exact Iff.of_eq h

end Module.CommutingAutomorphisms.LaurentSupport
