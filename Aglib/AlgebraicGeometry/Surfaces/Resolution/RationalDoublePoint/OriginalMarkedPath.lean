/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Surfaces.Resolution.RationalDoublePoint.OriginalMarkedStep

/-!
# Constructing the existing marking on the original continuing path

A finite initial full cubic marker and genuine original child Case-II data
produce successive full markers through the actual original blowdowns.
The native scalar recursion then constructs the existing path Marking.
No future marker, centre identity or residue isomorphism is assumed.
-/

@[expose] public noncomputable section
set_option autoImplicit false

open CategoryTheory IsLocalRing
open AlgebraicGeometry.Scheme.Blowup

universe u

namespace AlgebraicGeometry.Scheme.RationalDoublePoint.OriginalMarkedPath

/-- Recursively construct the actual original path marking from one finite
initial full marker and the genuine full kernels of its continuing children. -/
theorem exists_marking_of_initial_marker
    (P : Arc.ClosedPointBlowupPath.{u})
    (t0 : maximalIdeal (P.localRing 0)) (M0 : MarkedCubic t0)
    (hmin0 : (t0 : P.localRing 0) ∉ maximalIdeal (P.localRing 0) ^ 2)
    (hsing : ∀ n : ℕ, ¬ IsRegularLocalRing (P.localRing (n + 1)))
    (hII : ∀ n : ℕ, ∃ t s z : maximalIdeal (P.localRing (n + 1)),
      maximalIdeal (P.localRing (n + 1)) = Ideal.span
        ({(t : P.localRing (n + 1)), (s : P.localRing (n + 1)),
          (z : P.localRing (n + 1))} : Set (P.localRing (n + 1))) ∧
      Module.finrank ((P.localRing (n + 1)) ⧸ maximalIdeal (P.localRing (n + 1)))
        (maximalIdeal (P.localRing (n + 1))).Cotangent = 3 ∧
      doubleLineChildCotangentKernel (P.localRing (n + 1)) ![s, z, t] =
        Ideal.span {(MvPolynomial.X 1 :
          MvPolynomial (Fin 3) (ResidueField (P.localRing (n + 1)))) ^ 2}) :
    ∃ K : P.Marking, K.parameter = (t0 : P.localRing 0) := by
  classical
  choose t s z hgen hrank hkernel using hII
  have hstep (n : ℕ) (p : maximalIdeal (P.localRing n)) (M : MarkedCubic p) :
      ∃ q : maximalIdeal (P.localRing (n + 1)), ∃ N : MarkedCubic q,
        (q : P.localRing (n + 1)) = (P.transition n).hom (p : P.localRing n) ∧
        (maximalIdeal (P.localRing n)).map (P.transition n).hom =
          Ideal.span {(q : P.localRing (n + 1))} ∧
        Function.Bijective (ResidueField.map (P.transition n).hom) := by
    obtain ⟨q, hq, N, _, _, hc, hr⟩ := OriginalMarkedStep.exists_marked_continuation
      (P.point n) (P.point_closed n) (P.datum n)
      (P.point (n + 1)) (P.point_closed (n + 1)) (P.point_down n)
      M (hsing n) (t n) (s n) (z n) (hgen n) (hrank n) (hkernel n)
    exact ⟨q, N, hq, hc, hr⟩
  choose nextP nextM hnext hcenter hres using hstep
  let state : (n : ℕ) → (Σ p : maximalIdeal (P.localRing n), MarkedCubic p) :=
    fun n => Nat.rec (motive := fun n => Σ p : maximalIdeal (P.localRing n), MarkedCubic p)
      ⟨t0, M0⟩ (fun n S => ⟨nextP n S.1 S.2, nextM n S.1 S.2⟩) n
  have hparam (n : ℕ) : ((state n).1 : P.localRing n) =
      (P.scalar n).hom (t0 : P.localRing 0) := by
    induction n with
    | zero => rfl
    | succ n ih =>
      change (nextP n (state n).1 (state n).2 : P.localRing (n + 1)) =
        (P.transition n).hom ((P.scalar n).hom (t0 : P.localRing 0))
      exact (hnext n (state n).1 (state n).2).trans
        (congrArg (P.transition n).hom ih)
  refine ⟨{
    parameter := t0
    mem_maximal := t0.property
    not_mem_sq := hmin0
    residue := fun n => hres n (state n).1 (state n).2
    exceptional := fun n => ?_
  }, rfl⟩
  have hc := hcenter n (state n).1 (state n).2
  change (maximalIdeal (P.localRing n)).map (P.transition n).hom =
    Ideal.span {((state (n + 1)).1 : P.localRing (n + 1))} at hc
  rw [hparam (n + 1)] at hc
  exact hc

end AlgebraicGeometry.Scheme.RationalDoublePoint.OriginalMarkedPath
