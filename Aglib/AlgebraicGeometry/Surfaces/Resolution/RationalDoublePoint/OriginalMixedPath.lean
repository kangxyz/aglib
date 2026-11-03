/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Surfaces.Resolution.RationalDoublePoint.OriginalPathCones
public import Aglib.AlgebraicGeometry.Surfaces.Resolution.RationalDoublePoint.OriginalMarkedPath
public import Aglib.AlgebraicGeometry.Surfaces.Resolution.RationalDoublePoint.OriginalEntryStep
public import Aglib.AlgebraicGeometry.Surfaces.Resolution.RationalDoublePoint.OriginalTripleEntryStep
public import Aglib.AlgebraicGeometry.Surfaces.Resolution.RationalDoublePoint.PrefixResidue

/-!
# Actual marked tails and the original complete-base contradiction

Finite initial geometry produces the mixed-case path and its native marking.
The earlier complete base is retained through the original finite scalar map;
no later stalk is assumed complete.
-/

@[expose] public noncomputable section
set_option autoImplicit false

open CategoryTheory IsLocalRing Localization.Away Localization.Away.SaturatedChart
open AlgebraicGeometry.Scheme.Blowup AlgebraicGeometry.Scheme.RationalSingularities

universe u

namespace AlgebraicGeometry.Scheme.RationalDoublePoint

/-- Construct a native marked tail from the genuine original mixed-case geometry. -/
theorem exists_marked_original_tail
    (P : Arc.ClosedPointBlowupPath.{u})
    [IsIntegrallyClosed (P.localRing 0)]
    (hA : IsNagataRing.{u, 0} (P.localRing 0))
    (hd : ringKrullDim (P.localRing 0) = 2)
    (hRat : NormalModificationH1Vanishing (P.localRing 0))
    (t0 : maximalIdeal (P.localRing 0))
    (g0 : Fin 2 → maximalIdeal (P.localRing 0))
    (hgen0 : Ideal.span (Set.range fun i =>
      (CaseOne.orderedGenerators t0 g0 i : P.localRing 0)) = maximalIdeal (P.localRing 0))
    (q0 : MvPolynomial (Fin 3) (ResidueField (P.localRing 0)))
    (hq00 : q0 ≠ 0) (hq0 : q0.IsHomogeneous 2)
    (hker0 : RingHom.ker (CaseOne.canonicalConeMap t0 g0) = Ideal.span {q0})
    (hsing : ∀ n, ¬ IsRegularLocalRing (P.localRing n)) :
    ∃ r : ℕ, Nonempty ((P.tail r).Marking) := by
  classical
  have hprops := original_path_geometry_and_cones P hA hd hRat hsing t0 g0 hgen0 q0 hq00 hq0 hker0
  let CaseIAt (n : ℕ) : Prop :=
    ∃ (t : maximalIdeal (P.localRing n)) (g : Fin 2 → maximalIdeal (P.localRing n))
        (q : MvPolynomial (Fin 3) (ResidueField (P.localRing n))),
      Ideal.span (Set.range fun i => (CaseOne.orderedGenerators t g i : P.localRing n)) =
        maximalIdeal (P.localRing n) ∧ q ≠ 0 ∧ q.IsHomogeneous 2 ∧
      RingHom.ker (CaseOne.canonicalConeMap t g) = Ideal.span {q} ∧
      (¬ ∃ c : ResidueField (P.localRing n), c ≠ 0 ∧
        ∃ L : MvPolynomial (Fin 3) (ResidueField (P.localRing n)),
          L.IsHomogeneous 1 ∧ L ≠ 0 ∧ q = MvPolynomial.C c * L ^ 2)
  by_cases hcase : ∃ r, CaseIAt r
  · obtain ⟨r, t, g, q, hgen, hq0, hq, hker, hns⟩ := hcase
    obtain ⟨hnormal, hNagata, hdim, hRational, _⟩ := hprops r
    let : IsIntegrallyClosed (P.localRing r) := hnormal
    obtain ⟨t', g', q', hgen', hq'0, hq', hker', hr0, hrns⟩ :=
      OriginalCaseOneStep.exists_good_parameter
        (P.point r) (P.point_closed r) (P.datum r)
        (P.point (r + 1)) (P.point_closed (r + 1)) (P.point_down r) (hsing (r + 1))
        t g hgen q hq0 hq hker hns
    obtain ⟨p, gNext, qNext, _, hgenNext, hmin, _, _, hqNext0, hqNext,
        hkerNext, _, hrNext0, hrNextns, _⟩ :=
      OriginalCaseOneStep.exists_fixed_parameter_successor
        (P.point r) (P.point_closed r) hdim hNagata hRational (P.datum r)
        (P.point (r + 1)) (P.point_closed (r + 1)) (P.point_down r) (hsing (r + 1))
        t' g' hgen' q' hq'0 hq' hker' hr0 hrns
    let Q := P.tail (r + 1)
    let Good (n : ℕ) :=
      {a : (Σ _ : maximalIdeal (Q.localRing n),
          (Fin 2 → maximalIdeal (Q.localRing n)) ×
            MvPolynomial (Fin 3) (ResidueField (Q.localRing n))) //
        Ideal.span (Set.range fun i =>
          (CaseOne.orderedGenerators a.1 a.2.1 i : Q.localRing n)) =
            maximalIdeal (Q.localRing n) ∧
        a.2.2 ≠ 0 ∧ a.2.2.IsHomogeneous 2 ∧
        RingHom.ker (CaseOne.canonicalConeMap a.1 a.2.1) = Ideal.span {a.2.2} ∧
        MvPolynomial.eval₂Hom
          (MvPolynomial.C : ResidueField (Q.localRing n) →+*
            MvPolynomial (Fin 2) (ResidueField (Q.localRing n)))
          ![0, MvPolynomial.X 0, MvPolynomial.X 1] a.2.2 ≠ 0 ∧
        (¬ ∃ c : ResidueField (Q.localRing n), c ≠ 0 ∧
          ∃ L : MvPolynomial (Fin 2) (ResidueField (Q.localRing n)),
            L.IsHomogeneous 1 ∧ L ≠ 0 ∧
            MvPolynomial.eval₂Hom MvPolynomial.C
              ![0, MvPolynomial.X 0, MvPolynomial.X 1] a.2.2 = MvPolynomial.C c * L ^ 2)}
    let initial : Good 0 :=
      ⟨⟨p, gNext, qNext⟩, hgenNext, hqNext0, hqNext, hkerNext, hrNext0, hrNextns⟩
    have hstep (n : ℕ) (a : Good n) : ∃ b : Good (n + 1),
        (b.1.1 : Q.localRing (n + 1)) = (Q.transition n).hom (a.1.1 : Q.localRing n) ∧
        (maximalIdeal (Q.localRing n)).map (Q.transition n).hom =
          Ideal.span {(b.1.1 : Q.localRing (n + 1))} ∧
        Function.Bijective (ResidueField.map (Q.transition n).hom) := by
      obtain ⟨hn, hN, hdN, hRatN, _⟩ := hprops ((r + 1) + n)
      let : IsIntegrallyClosed (Q.localRing n) := hn
      obtain ⟨hg, hq0, hq, hk, hr0, hrns⟩ := a.2
      obtain ⟨p', g', q', hp', hg', _, hc', hres', hq'0, hq', hk', _, hr'0, hrns', _⟩ :=
        OriginalCaseOneStep.exists_fixed_parameter_successor
          (Q.point n) (Q.point_closed n) hdN hN hRatN (Q.datum n)
          (Q.point (n + 1)) (Q.point_closed (n + 1)) (Q.point_down n)
          (hsing ((r + 1) + (n + 1))) a.1.1 a.1.2.1 hg a.1.2.2 hq0 hq hk hr0 hrns
      exact ⟨⟨⟨p', g', q'⟩, hg', hq'0, hq', hk', hr'0, hrns'⟩, hp', hc', hres'⟩
    choose next hnext hcenter hres using hstep
    let state : (n : ℕ) → Good n := fun n =>
      Nat.rec (motive := Good) initial (fun n a => next n a) n
    have hparam (n : ℕ) : ((state n).1.1 : Q.localRing n) =
        (Q.scalar n).hom (p.val : Q.localRing 0) := by
      induction n with
      | zero => rfl
      | succ n ih =>
        change ((next n (state n)).1.1 : Q.localRing (n + 1)) =
          (Q.transition n).hom ((Q.scalar n).hom (p.val : Q.localRing 0))
        exact (hnext n (state n)).trans (congrArg (Q.transition n).hom ih)
    refine ⟨r + 1, ⟨{
      parameter := p.val
      mem_maximal := p.property
      not_mem_sq := hmin
      residue := fun n => hres n (state n)
      exceptional := fun n => ?_
    }⟩⟩
    have hc := hcenter n (state n)
    change (maximalIdeal (Q.localRing n)).map (Q.transition n).hom =
      Ideal.span {((state (n + 1)).1.1 : Q.localRing (n + 1))} at hc
    rw [hparam (n + 1)] at hc
    exact hc
  · have hII (n : ℕ) : ∃ t s z : maximalIdeal (P.localRing n),
        maximalIdeal (P.localRing n) = Ideal.span
          ({(t : P.localRing n), (s : P.localRing n), (z : P.localRing n)} :
            Set (P.localRing n)) ∧
        doubleLineChildCotangentKernel (P.localRing n) ![s, z, t] =
          Ideal.span {(MvPolynomial.X 1 :
            MvPolynomial (Fin 3) (ResidueField (P.localRing n))) ^ 2} ∧
        ∃ F : CubicRelation t s z, F.coefficients.residueCubic ≠ 0 := by
      obtain ⟨hn, hN, hdN, hRatN, _, t, g, q, hg, hq0, hq, hk⟩ := hprops n
      let : IsIntegrallyClosed (P.localRing n) := hn
      obtain hI | hII :=
        MaximalIdealBlowup.exceptional_original_quadratic_alternatives_of_quadratic_kernel
          (P.localRing n) hdN hN hRatN (hsing n) t g hg q hq0 hq hk
      · obtain ⟨t, g, q, hg, hq0, hq, hk, _, _, _, _, hns, _⟩ := hI
        exact (hcase ⟨n, t, g, q, hg, hq0, hq, hk, hns⟩).elim
      · obtain ⟨t, s, z, hg, hk, F, _, hF⟩ := hII
        exact ⟨t, s, z, hg, hk, F, hF⟩
    have hmark (r : ℕ) (t : maximalIdeal (P.localRing r)) (M : MarkedCubic t) :
        Nonempty ((P.tail r).Marking) := by
      have hmin := M.parameter_not_mem_sq (hprops r).2.2.1 (hsing r)
      obtain ⟨K, _⟩ := OriginalMarkedPath.exists_marking_of_initial_marker
        (P.tail r) t M hmin (fun n => hsing (r + (n + 1))) (fun n => by
          obtain ⟨t, s, z, hg, hk, _⟩ := hII (r + (n + 1))
          exact ⟨t, s, z, hg, (hprops (r + (n + 1))).2.2.2.2.1, hk⟩)
      exact ⟨K⟩
    obtain ⟨t, s, z, hg, hk, F, hF⟩ := hII 0
    obtain ⟨t1, s1, z1, hg1, hk1, _⟩ := hII 1
    obtain hmarker | ⟨p, u, w, T, _, _, _, _⟩ := OriginalEntryStep.marker_or_tripleEntry
      (P.point 0) (P.point_closed 0) (P.datum 0)
      (P.point 1) (P.point_closed 1) (P.point_down 0) t s z hg hk F hF (hsing 1)
      t1 s1 z1 hg1 (hprops 1).2.2.2.2.1 hk1
    · obtain ⟨t, M, _⟩ := hmarker
      exact ⟨0, hmark 0 t M⟩
    obtain ⟨hn, hN, hdN, hRatN, _⟩ := hprops 1
    let : IsIntegrallyClosed (P.localRing 1) := hn
    obtain ⟨t2, s2, z2, hg2, hk2, _⟩ := hII 2
    obtain hmarker | ⟨r, N, _⟩ := OriginalTripleEntryStep.marker_or_next_marker
      (P.point 1) (P.point_closed 1) hdN hN hRatN (hsing 1) (P.datum 1)
      (P.point 2) (P.point_closed 2) (P.point_down 1) T (hsing 2)
      t2 s2 z2 hg2 (hprops 2).2.2.2.2.1 hk2
    · obtain ⟨t, M, _⟩ := hmarker
      exact ⟨1, hmark 1 t M⟩
    · exact ⟨2, hmark 2 r N⟩

/-- An earlier complete base rules out an everywhere singular original path.
The initial and all later stalks need not be complete. -/
theorem exists_regular_original_point_of_initial_cone_of_complete_base
    (P : Arc.ClosedPointBlowupPath.{u})
    [IsIntegrallyClosed (P.localRing 0)]
    (hA : IsNagataRing.{u, 0} (P.localRing 0))
    (hd : ringKrullDim (P.localRing 0) = 2)
    (hRat : NormalModificationH1Vanishing (P.localRing 0))
    (t0 : maximalIdeal (P.localRing 0))
    (g0 : Fin 2 → maximalIdeal (P.localRing 0))
    (hgen0 : Ideal.span (Set.range fun i =>
      (CaseOne.orderedGenerators t0 g0 i : P.localRing 0)) = maximalIdeal (P.localRing 0))
    (q0 : MvPolynomial (Fin 3) (ResidueField (P.localRing 0)))
    (hq00 : q0 ≠ 0) (hq0 : q0.IsHomogeneous 2)
    (hker0 : RingHom.ker (CaseOne.canonicalConeMap t0 g0) = Ideal.span {q0})
    (A : Type u) [CommRing A] [IsDomain A] [IsLocalRing A]
    [IsAdicComplete (maximalIdeal A) A] (hdA : ringKrullDim A = 2)
    (a : A →+* P.localRing 0) [IsLocalHom a]
    (hinj : Function.Injective a) (hres : (ResidueField.map a).Finite) :
    ∃ n : ℕ, IsRegularLocalRing (P.localRing n) := by
  by_contra hregular
  have hsing (n : ℕ) : ¬ IsRegularLocalRing (P.localRing n) :=
    fun hn => hregular ⟨n, hn⟩
  obtain ⟨r, ⟨M⟩⟩ :=
    exists_marked_original_tail P hA hd hRat t0 g0 hgen0 q0 hq00 hq0 hker0 hsing
  obtain ⟨hn, hN, hdr, _⟩ :=
    original_path_geometry_and_cones P hA hd hRat hsing t0 g0 hgen0 q0 hq00 hq0 hker0 r
  let Q := P.tail r
  let b : A →+* Q.localRing 0 := (P.scalar r).hom.comp a
  let : IsIntegrallyClosed (Q.localRing 0) := hn
  let : Algebra A (Q.localRing 0) := b.toAlgebra
  let : IsLocalHom (algebraMap A (Q.localRing 0)) :=
    RingHom.isLocalHom_comp (P.scalar r).hom a
  have hb : (ResidueField.map b).Finite := by
    change (ResidueField.map ((P.scalar r).hom.comp a)).Finite
    rw [ResidueField.map_comp]
    exact (P.scalar_residue_finite r).comp hres
  have hmap : algebraMap (ResidueField A) (ResidueField (Q.localRing 0)) =
      ResidueField.map b := Ideal.Quotient.ringHom_ext (RingHom.ext fun _ => rfl)
  let : Module.Finite (ResidueField A) (ResidueField (Q.localRing 0)) :=
    RingHom.finite_algebraMap.mp (hmap.symm ▸ hb)
  have hinjB : Function.Injective (algebraMap A (Q.localRing 0)) :=
    (P.scalar_injective r).comp hinj
  obtain ⟨n, hn⟩ := M.exists_regular_original_point_of_complete_base A hinjB hdA hdr hN
  exact hregular ⟨r + n, hn⟩

end AlgebraicGeometry.Scheme.RationalDoublePoint
