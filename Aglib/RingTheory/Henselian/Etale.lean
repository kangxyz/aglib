/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.Unramified.LocalStructure

/-!
# Etale points over a Henselian local ring

Simple-root Hensel lifting and the native standard-etale chart at the kernel
of the given residue point give a unique lift to the original ring. Both maps
are actual algebra homomorphisms, and reduction is their literal composition.
The target of a lift here is the base ring itself; this does not assert the
finite-etale algebra equivalence with the residue field.
-/

@[expose] public section

noncomputable section
open Polynomial IsLocalRing

namespace HenselianLocalRing

variable (R : Type*) [CommRing R] [HenselianLocalRing R]

/-- Residue-valued points of a standard etale algebra lift uniquely to the
original Henselian local ring, along the literal residue map. -/
theorem standardEtale_residue_comp_bijective (P : StandardEtalePair R) :
    Function.Bijective (fun f : P.Ring →ₐ[R] R =>
      (Algebra.ofId R (ResidueField R)).comp f) := by
  constructor
  · intro f g h
    apply P.hom_ext
    have hf := P.hasMap_X.map f
    have hg := P.hasMap_X.map g
    apply IsLocalRing.eq_of_eval_eq_zero_of_not_isUnit_sub hf.1 hg.1
    · have he : residue R (f P.X - g P.X) = 0 := by
        simpa only [AlgHom.comp_apply, Algebra.ofId_apply, ResidueField.algebraMap_eq,
          map_sub, sub_eq_zero] using AlgHom.congr_fun h P.X
      exact (mem_nonunits_iff).mp ((mem_maximalIdeal _).mp
        ((residue_eq_zero_iff _).mp he))
    · exact hf.isUnit_derivative_f
  · intro f
    have hx : P.HasMap (f P.X) := P.hasMap_X.map f
    have hensel := ((HenselianLocalRing.TFAE R).out 1 2).mp
      (inferInstance : HenselianLocalRing R)
    obtain ⟨a, ha, har⟩ := hensel P.f P.monic_f (f P.X) hx.1
      (isUnit_iff_ne_zero.mp hx.isUnit_derivative_f)
    have hr (q : R[X]) : residue R (q.eval a) = aeval (f P.X) q := by
      calc
        _ = aeval (residue R a) q :=
          by simpa only [ResidueField.algebraMap_eq] using
            (aeval_algebraMap_apply_eq_algebraMap_eval
              (A := ResidueField R) a q).symm
        _ = _ := by rw [har]
    have hag : IsUnit (aeval a P.g : R) := by
      apply (residue_ne_zero_iff_isUnit _).mp
      change residue R (P.g.eval a) ≠ 0
      rw [hr]
      exact isUnit_iff_ne_zero.mp hx.2
    have haf : (aeval a) P.f = 0 := by
      change P.f.eval a = 0
      exact ha
    have hma : P.HasMap a := ⟨haf, hag⟩
    refine ⟨P.lift a hma, ?_⟩
    apply P.hom_ext
    change residue R (P.lift a hma P.X) = f P.X
    rw [P.lift_X]
    exact har


/-- Transfer unique residue lifting across an actual standard etale presentation. -/
theorem residue_comp_bijective_of_isStandardEtale (A : Type*) [CommRing A] [Algebra R A]
    [Algebra.IsStandardEtale R A] :
    Function.Bijective (fun f : A →ₐ[R] R =>
      (Algebra.ofId R (ResidueField R)).comp f) := by
  let P : StandardEtalePresentation R A :=
    Classical.choice Algebra.IsStandardEtale.nonempty_standardEtalePresentation
  let e : A ≃ₐ[R] P.P.Ring := P.equivRing
  constructor
  · intro f g h
    have he := (standardEtale_residue_comp_bijective R P.P).1
      (a₁ := f.comp e.symm.toAlgHom) (a₂ := g.comp e.symm.toAlgHom)
      (by apply AlgHom.ext; intro x; exact AlgHom.congr_fun h (e.symm x))
    ext x
    simpa only [AlgHom.comp_apply, AlgEquiv.coe_toAlgHom, AlgEquiv.symm_apply_apply]
      using AlgHom.congr_fun he (e x)
  · intro f
    obtain ⟨g, hg⟩ := (standardEtale_residue_comp_bijective R P.P).2
      (f.comp e.symm.toAlgHom)
    refine ⟨g.comp e.toAlgHom, ?_⟩
    ext x
    simpa only [AlgHom.comp_apply, AlgEquiv.coe_toAlgHom, AlgEquiv.symm_apply_apply]
      using AlgHom.congr_fun hg (e x)

/-- Every residue-valued point of an etale algebra over a Henselian local ring
has a unique lift to the original ring. The reduction is composition with the
actual residue homomorphism. No finite-module, Noetherian or DVR input is used. -/
theorem residue_comp_bijective_of_etale (A : Type*) [CommRing A] [Algebra R A]
    [Algebra.Etale R A] :
    Function.Bijective (fun f : A →ₐ[R] R =>
      (Algebra.ofId R (ResidueField R)).comp f) := by
  let res : R →ₐ[R] ResidueField R := Algebra.ofId R (ResidueField R)
  constructor
  · intro f g h
    let Q : Ideal A := RingHom.ker (res.comp f).toRingHom
    let : Q.IsPrime := RingHom.ker_isPrime _
    obtain ⟨s, hs, hstd⟩ := Algebra.IsEtaleAt.exists_isStandardEtale (R := R) Q
    let := hstd
    have hsunitf : IsUnit (f s) := by
      apply (residue_ne_zero_iff_isUnit _).mp
      exact hs
    have hsunitg : IsUnit (g s) := by
      apply (residue_ne_zero_iff_isUnit _).mp
      rw [← show residue R (f s) = residue R (g s) from AlgHom.congr_fun h s]
      exact hs
    let fl : Localization.Away s →ₐ[R] R := IsLocalization.Away.liftAlgHom s hsunitf
    let gl : Localization.Away s →ₐ[R] R := IsLocalization.Away.liftAlgHom s hsunitg
    have he : res.comp fl = res.comp gl := by
      apply IsLocalization.algHom_ext (Submonoid.powers s)
      apply AlgHom.ext
      intro x
      change residue R (fl (algebraMap A (Localization.Away s) x)) =
        residue R (gl (algebraMap A (Localization.Away s) x))
      simpa [fl, gl, IsLocalization.Away.liftAlgHom] using AlgHom.congr_fun h x
    have hl := (residue_comp_bijective_of_isStandardEtale R (Localization.Away s)).1 he
    ext x
    simpa [fl, gl, IsLocalization.Away.liftAlgHom] using
      AlgHom.congr_fun hl (algebraMap A (Localization.Away s) x)
  · intro f
    let Q : Ideal A := RingHom.ker f.toRingHom
    let : Q.IsPrime := RingHom.ker_isPrime _
    obtain ⟨s, hs, hstd⟩ := Algebra.IsEtaleAt.exists_isStandardEtale (R := R) Q
    let := hstd
    have hsunit : IsUnit (f s) := isUnit_iff_ne_zero.mpr hs
    let fl : Localization.Away s →ₐ[R] ResidueField R :=
      IsLocalization.Away.liftAlgHom s hsunit
    obtain ⟨g, hg⟩ := (residue_comp_bijective_of_isStandardEtale R (Localization.Away s)).2 fl
    refine ⟨g.comp (Algebra.algHom R A (Localization.Away s)), ?_⟩
    apply AlgHom.ext
    intro x
    change residue R (g (algebraMap A (Localization.Away s) x)) = f x
    simpa [fl, IsLocalization.Away.liftAlgHom] using
      AlgHom.congr_fun hg (algebraMap A (Localization.Away s) x)

end HenselianLocalRing
