/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis

/-!
# Injectivity detected on an actual transcendence basis

A map from a domain is injective if an actual source transcendence basis
remains algebraically independent in the target. For a finite family, a bound
on the source transcendence degree produces the required basis. All families
live in the actual source ring; no map between fraction fields is postulated.
-/

@[expose] public noncomputable section

open Algebra Cardinal

universe u v w z

namespace AlgHom

variable {R : Type u} {A : Type v} {D : Type w} {ι : Type z}
variable [CommRing R] [Nontrivial R] [CommRing A] [IsDomain A]
variable [CommRing D] [Algebra R A] [Algebra R D]

/-- A map out of a domain is injective if an actual source transcendence basis
remains independent in the target. The target need not be a field or domain. -/
theorem injective_of_isTranscendenceBasis (f : A →ₐ[R] D) {x : ι → A}
    (hx : IsTranscendenceBasis R x)
    (hfx : AlgebraicIndependent R (f ∘ x)) : Function.Injective f := by
  algebraize [f.toRingHom]
  let T := Algebra.adjoin R (Set.range x)
  let : Algebra.IsAlgebraic T A := hx.isAlgebraic
  have hT : Function.Injective (algebraMap T D) := by
    intro a b hab
    obtain ⟨p, rfl⟩ := hx.1.aevalEquiv.surjective a
    obtain ⟨q, rfl⟩ := hx.1.aevalEquiv.surjective b
    apply congrArg hx.1.aevalEquiv
    apply hfx
    have he : MvPolynomial.aeval (f ∘ x) = f.comp (MvPolynomial.aeval x) := by
      ext
      simp
    rw [he]
    change f (MvPolynomial.aeval x p) = f (MvPolynomial.aeval x q) at hab
    exact hab
  exact Algebra.IsAlgebraic.injective_tower_top (R := T) A hT

/-- Finite source trdeg bounded by the size of an independent image family
forces injectivity. The displayed family lives in the source ring itself. -/
theorem injective_of_lift_trdeg_le_of_finite [_root_.Finite ι]
    (f : A →ₐ[R] D) {x : ι → A}
    (hfx : AlgebraicIndependent R (f ∘ x))
    (hdeg : Cardinal.lift.{z} (Algebra.trdeg R A) ≤ Cardinal.lift.{v} (#ι)) :
    Function.Injective f := by
  have hx : AlgebraicIndependent R x := hfx.of_comp f
  exact f.injective_of_isTranscendenceBasis
    (hx.isTranscendenceBasis_of_lift_trdeg_le_of_finite hdeg) hfx

/-- A surjection of domains cannot preserve finite transcendence degree while
having a nonzero kernel. The target basis and its actual source lifts are
constructed here, rather than required from the caller. -/
theorem injective_of_surjective_of_lift_trdeg_le [IsDomain D] [FaithfulSMul R D]
    (f : A →ₐ[R] D) (hf : Function.Surjective f)
    (hfinite : Algebra.trdeg R D < Cardinal.aleph0)
    (hdeg : Cardinal.lift.{w} (Algebra.trdeg R A) ≤
      Cardinal.lift.{v} (Algebra.trdeg R D)) : Function.Injective f := by
  classical
  obtain ⟨s, hs⟩ := exists_isTranscendenceBasis R D
  let : _root_.Finite s := Cardinal.lt_aleph0_iff_finite.mp (by
    simpa only [hs.cardinalMk_eq_trdeg] using hfinite)
  choose x hx using fun d : s => hf (d : D)
  have he : f ∘ x = ((↑) : s → D) := funext hx
  have hfx : AlgebraicIndependent R (f ∘ x) := by
    rw [he]
    exact hs.1
  exact f.injective_of_lift_trdeg_le_of_finite hfx
    (by simpa only [hs.cardinalMk_eq_trdeg] using hdeg)

end AlgHom
