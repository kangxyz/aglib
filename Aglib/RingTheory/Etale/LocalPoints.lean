/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.Unramified.LocalStructure

/-!
# Uniqueness of etale points with local targets

Two points of an etale algebra with values in a local ring agree if their
reductions to its residue field agree. The target is not assumed Henselian.
The proof uses standard-etale charts and simple-root uniqueness, not existence
of Hensel lifts or nilpotence of the maximal ideal.
-/

@[expose] public section

noncomputable section
open Polynomial IsLocalRing

universe u v w

namespace Algebra.Etale

variable (R : Type u) [CommRing R]
  (T : Type w) [CommRing T] [IsLocalRing T] [Algebra R T]

private theorem standardEtale_residue_comp_injective (P : StandardEtalePair R) :
    Function.Injective (fun f : P.Ring →ₐ[R] T =>
      ((Algebra.ofId T (ResidueField T)).restrictScalars R).comp f) := by
  intro f g h
  apply P.hom_ext
  have hf := P.hasMap_X.map f
  have hg := P.hasMap_X.map g
  have hf0 : (P.f.map (algebraMap R T)).eval (f P.X) = 0 := by
    simpa only [Polynomial.eval_map, Polynomial.aeval_def] using hf.1
  have hg0 : (P.f.map (algebraMap R T)).eval (g P.X) = 0 := by
    simpa only [Polynomial.eval_map, Polynomial.aeval_def] using hg.1
  apply IsLocalRing.eq_of_eval_eq_zero_of_not_isUnit_sub hf0 hg0
  · have hx : residue T (f P.X) = residue T (g P.X) := AlgHom.congr_fun h P.X
    have he : residue T (f P.X - g P.X) = 0 := by rw [map_sub, hx, sub_self]
    exact (mem_nonunits_iff).mp ((mem_maximalIdeal _).mp
      ((residue_eq_zero_iff _).mp he))
  · simpa only [Polynomial.derivative_map, Polynomial.eval_map, Polynomial.aeval_def]
      using hf.isUnit_derivative_f

private theorem residue_comp_injective_of_isStandardEtale (B : Type v)
    [CommRing B] [Algebra R B] [Algebra.IsStandardEtale R B] :
    Function.Injective (fun f : B →ₐ[R] T =>
      ((Algebra.ofId T (ResidueField T)).restrictScalars R).comp f) := by
  let P : StandardEtalePresentation R B :=
    Classical.choice Algebra.IsStandardEtale.nonempty_standardEtalePresentation
  let e : B ≃ₐ[R] P.P.Ring := P.equivRing
  intro f g h
  have he := standardEtale_residue_comp_injective R T P.P
    (a₁ := f.comp e.symm.toAlgHom) (a₂ := g.comp e.symm.toAlgHom)
    (by apply AlgHom.ext; intro x; exact AlgHom.congr_fun h (e.symm x))
  ext x
  simpa only [AlgHom.comp_apply, AlgEquiv.coe_toAlgHom, AlgEquiv.symm_apply_apply]
    using AlgHom.congr_fun he (e x)

/-- Points of an etale algebra in any local target are determined by their
compositions with the target's actual residue map. No Henselian hypothesis is
needed on the base or the target. -/
theorem residue_comp_injective (B : Type v) [CommRing B] [Algebra R B]
    [Algebra.Etale R B] :
    Function.Injective (fun f : B →ₐ[R] T =>
      ((Algebra.ofId T (ResidueField T)).restrictScalars R).comp f) := by
  let res : T →ₐ[R] ResidueField T :=
    (Algebra.ofId T (ResidueField T)).restrictScalars R
  intro f g h
  let Q : Ideal B := RingHom.ker (res.comp f).toRingHom
  let : Q.IsPrime := RingHom.ker_isPrime _
  obtain ⟨s, hs, hstd⟩ := Algebra.IsEtaleAt.exists_isStandardEtale (R := R) Q
  let := hstd
  have hsunitf : IsUnit (f s) := by
    apply (residue_ne_zero_iff_isUnit _).mp
    exact hs
  have hsunitg : IsUnit (g s) := by
    apply (residue_ne_zero_iff_isUnit _).mp
    rw [← show residue T (f s) = residue T (g s) from AlgHom.congr_fun h s]
    exact hs
  let fl : Localization.Away s →ₐ[R] T := IsLocalization.Away.liftAlgHom s hsunitf
  let gl : Localization.Away s →ₐ[R] T := IsLocalization.Away.liftAlgHom s hsunitg
  have he : res.comp fl = res.comp gl := by
    apply IsLocalization.algHom_ext (Submonoid.powers s)
    apply AlgHom.ext
    intro x
    change residue T (fl (algebraMap B (Localization.Away s) x)) =
      residue T (gl (algebraMap B (Localization.Away s) x))
    simpa [fl, gl, IsLocalization.Away.liftAlgHom] using AlgHom.congr_fun h x
  have hl := residue_comp_injective_of_isStandardEtale R T (Localization.Away s) he
  ext x
  simpa [fl, gl, IsLocalization.Away.liftAlgHom] using
    AlgHom.congr_fun hl (algebraMap B (Localization.Away s) x)

end Algebra.Etale
