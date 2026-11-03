/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Surfaces.Resolution.RationalDoublePoint.CaseOneCharts
public import Aglib.RingTheory.Blowup.DoubleLine.Marked.Chart
public import Aglib.AlgebraicGeometry.Blowup.GeneratorAtlas
public import Aglib.RingTheory.Blowup.QuadraticPresentation

/-!
# The actual two plane charts and original Case-II child primes

Fixed original permutations supply the existing exceptional presentations.
The square-coordinate chart has no closed exceptional point, and the native
generator cover gives the two actual plane charts. Original stalk comparisons
and the existing child-prime producer retain the original structural map.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits IsLocalRing
open Localization.Away Localization.Away.SaturatedChart
open AlgebraicGeometry.Scheme.Blowup

universe u

namespace AlgebraicGeometry.Scheme.RationalDoublePoint.CaseTwoPoint

variable {A : Type u} [CommRing A] [IsLocalRing A]

private theorem permuted_square_kernel
    (g g' : Fin 3 → maximalIdeal A) (e : Fin 3 ≃ Fin 3) (j : Fin 3)
    (hg : g' = fun i => g (e i)) (he : e j = 1)
    (hker : doubleLineChildCotangentKernel A g =
      Ideal.span {(MvPolynomial.X 1 : MvPolynomial (Fin 3) (ResidueField A)) ^ 2}) :
    doubleLineChildCotangentKernel A g' =
      Ideal.span {(MvPolynomial.X j : MvPolynomial (Fin 3) (ResidueField A)) ^ 2} := by
  let σ := MvPolynomial.renameEquiv (ResidueField A) e
  have hp := cotangentPolynomialMap_permutation g e
  rw [← hg] at hp
  have hmap : (Ideal.cotangentPolynomialMap (maximalIdeal A) g').toRingHom =
      (Ideal.cotangentPolynomialMap (maximalIdeal A) g).toRingHom.comp σ.toRingHom := by
    apply RingHom.ext
    intro p
    change Ideal.cotangentPolynomialMap (maximalIdeal A) g' p =
      Ideal.cotangentPolynomialMap (maximalIdeal A) g (σ p)
    rw [hp]
    rfl
  have hcomp : doubleLineChildCotangentKernel A g' =
      (doubleLineChildCotangentKernel A g).comap σ.toRingHom := by
    ext p
    change (Ideal.cotangentPolynomialMap (maximalIdeal A) g').toRingHom p = 0 ↔
      (Ideal.cotangentPolynomialMap (maximalIdeal A) g).toRingHom (σ p) = 0
    rw [hmap]
    rfl
  have hspan : (Ideal.span {(MvPolynomial.X j :
      MvPolynomial (Fin 3) (ResidueField A)) ^ 2}).map σ.toRingHom =
      Ideal.span {(MvPolynomial.X 1 : MvPolynomial (Fin 3) (ResidueField A)) ^ 2} := by
    rw [Ideal.map_span, Set.image_singleton, map_pow]
    change Ideal.span {(σ (MvPolynomial.X j)) ^ 2} = _
    simp only [σ, MvPolynomial.renameEquiv_apply, MvPolynomial.rename_X, he]
  rw [hcomp, hker, ← hspan]
  exact Ideal.comap_map_of_bijective σ.toRingHom σ.bijective

private theorem ordered_generators_span (t s z : maximalIdeal A)
    (hgen : maximalIdeal A = Ideal.span ({(t : A), (s : A), (z : A)} : Set A)) :
    Ideal.span (Set.range fun i => (CaseOne.orderedGenerators t ![s, z] i : A)) =
      maximalIdeal A := by
  have hr : Set.range (fun i => (CaseOne.orderedGenerators t ![s, z] i : A)) =
      ({(t : A), (s : A), (z : A)} : Set A) := by
    ext a
    constructor
    · rintro ⟨i, rfl⟩
      fin_cases i <;> simp [CaseOne.orderedGenerators]
    · intro h
      rcases h with h | h | h
      · exact ⟨0, h.symm⟩
      · exact ⟨1, h.symm⟩
      · exact ⟨2, h.symm⟩
  rw [hr]
  exact hgen.symm

private theorem parameter_kernel (t s z : maximalIdeal A)
    (hker : doubleLineChildCotangentKernel A ![s, z, t] =
      Ideal.span {(MvPolynomial.X 1 : MvPolynomial (Fin 3) (ResidueField A)) ^ 2}) :
    RingHom.ker (CaseOne.canonicalConeMap t ![s, z]) =
      Ideal.span {(MvPolynomial.X 2 : MvPolynomial (Fin 3) (ResidueField A)) ^ 2} := by
  apply permuted_square_kernel ![s, z, t] (CaseOne.orderedGenerators t ![s, z])
    ((Equiv.swap 0 2).trans (Equiv.swap 0 1)) 2 ?_ (by decide) hker
  funext i
  fin_cases i <;> simp [CaseOne.orderedGenerators, Equiv.swap_apply_def]

private theorem square_kernel (t s z : maximalIdeal A)
    (hker : doubleLineChildCotangentKernel A ![s, z, t] =
      Ideal.span {(MvPolynomial.X 1 : MvPolynomial (Fin 3) (ResidueField A)) ^ 2}) :
    RingHom.ker (CaseOne.canonicalConeMap z ![s, t]) =
      Ideal.span {(MvPolynomial.X 0 : MvPolynomial (Fin 3) (ResidueField A)) ^ 2} := by
  apply permuted_square_kernel ![s, z, t] (CaseOne.orderedGenerators z ![s, t])
    (Equiv.swap 0 1) 0 ?_ (by decide) hker
  funext i
  fin_cases i <;> simp [CaseOne.orderedGenerators, Equiv.swap_apply_def]

variable (B : BlowupDatum (affineCenter A (maximalIdeal A)))
    (t s z : maximalIdeal A)
    (hgen : maximalIdeal A = Ideal.span ({(t : A), (s : A), (z : A)} : Set A))
    (hker : doubleLineChildCotangentKernel A ![s, z, t] =
      Ideal.span {(MvPolynomial.X 1 : MvPolynomial (Fin 3) (ResidueField A)) ^ 2})

include hgen hker in
/-- The actual square-coordinate chart contains no globally closed point of
the original exceptional fibre: its original dehomogenized equation is one. -/
theorem not_mem_squareChart_of_closed_exceptional_point
    (x : B.Y) (hx : IsClosed ({x} : Set B.Y)) (hbase : B.map x = closedPoint A) :
    x ∉ Set.range (CaseOneChart.chart B z) := by
  intro hchart
  have hgen' : maximalIdeal A = Ideal.span ({(z : A), (s : A), (t : A)} : Set A) := by
    have hset : ({(t : A), (s : A), (z : A)} : Set A) = {(z : A), (s : A), (t : A)} := by
      ext a
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      tauto
    exact hgen.trans (congrArg Ideal.span hset)
  let D := CaseOne.presentationOfKernel z ![s, t]
    (ordered_generators_span z s t hgen')
    ((MvPolynomial.X 0 : MvPolynomial (Fin 3) (ResidueField A)) ^ 2)
    (square_kernel t s z hker)
  obtain ⟨M, hM, hQM, _⟩ := CaseOneChart.exists_plane_point B D x hx hbase hchart
  let : M.IsMaximal := hM
  have hone : (1 : CaseOne.Plane A) ∈ M := by
    simpa only [map_pow, MvPolynomial.FirstCoordinate.dehom_X_zero, one_pow] using hQM
  exact (inferInstance : M.IsPrime).ne_top (Ideal.eq_top_of_isUnit_mem M hone isUnit_one)

include hgen hker in
/-- The two original plane charts cover every globally closed exceptional
point; the third chart is excluded by the full original square kernel. -/
theorem mem_planeChart_or_opposite_of_closed_exceptional_point
    (x : B.Y) (hx : IsClosed ({x} : Set B.Y)) (hbase : B.map x = closedPoint A) :
    x ∈ Set.range (CaseOneChart.chart B t) ∨ x ∈ Set.range (CaseOneChart.chart B s) := by
  obtain ⟨i, hi⟩ := AffineAtlas.generator_covers (CaseOne.orderedGenerators t ![s, z])
    (ordered_generators_span t s z hgen) (affineAtlas B) x
  fin_cases i
  · left
    exact hi
  · right
    exact hi
  · exact False.elim (not_mem_squareChart_of_closed_exceptional_point
      B t s z hgen hker x hx hbase hi)

/-- An actual closed singular point on the original parameter chart gives
its own monic irreducible polynomial prime and original lift. The native stalk
comparison retains the exact original structural coefficient homomorphism. -/
theorem exists_actual_prime_parameter_at_closed_singular_point
    [IsDomain A] [IsNoetherianRing A] (F : CubicRelation t s z)
    (x : B.Y) (hx : IsClosed ({x} : Set B.Y)) (hbase : B.map x = closedPoint A)
    (hsing : ¬ IsRegularLocalRing (B.Y.presheaf.stalk x))
    (hchart : x ∈ Set.range (CaseOneChart.chart B t)) :
    let E := DoubleLinePresentation.ofKernel t s z hgen hker
    ∃ (P : Ideal (saturatedChart A (maximalIdeal A) (t : A))) (hP : P.IsPrime),
      letI := hP
      ∃ (q : Polynomial (ResidueField A))
        (Q : saturatedChart A (maximalIdeal A) (t : A)),
        q.Monic ∧ Irreducible q ∧ P = (Ideal.span {q}).comap E.reduction ∧
        E.reduction Q = q ∧
        algebraMap A (saturatedChart A (maximalIdeal A) (t : A)) (t : A) ∈ P ∧
        CaseOneChart.chart B t ⟨P, hP⟩ = x ∧
        ringKrullDim (Localization.AtPrime P) = 2 ∧
        ¬ IsRegularLocalRing (Localization.AtPrime P) ∧
        ∃ ε : B.Y.presheaf.stalk x ≅ CommRingCat.of (Localization.AtPrime P),
          ε.hom.hom.comp (B.map.stalkScalar x) =
            localizedChartMap (maximalIdeal A) (t : A) P := by
  let E := DoubleLinePresentation.ofKernel t s z hgen hker
  let q0 := (MvPolynomial.X 2 : MvPolynomial (Fin 3) (ResidueField A)) ^ 2
  have hq0 : q0 ≠ 0 := pow_ne_zero 2 (MvPolynomial.X_ne_zero (2 : Fin 3))
  have hk := parameter_kernel t s z hker
  have ht : (t : A) ≠ 0 := CaseOne.denominator_ne_zero_of_kernel t ![s, z]
    q0 hq0 (MvPolynomial.isHomogeneous_X_pow 2 2) hk
  let D := CaseOne.presentationOfKernel t ![s, z]
    (ordered_generators_span t s z hgen) q0 hk
  have hQ0 : MvPolynomial.FirstCoordinate.dehom q0 ≠ 0 := by
    change MvPolynomial.FirstCoordinate.dehom
      ((MvPolynomial.X 2 : MvPolynomial (Fin 3) (ResidueField A)) ^ 2) ≠ 0
    rw [map_pow, show (2 : Fin 3) = (1 : Fin 2).succ from rfl,
      MvPolynomial.FirstCoordinate.dehom_X_succ]
    exact pow_ne_zero 2 (MvPolynomial.X_ne_zero (1 : Fin 2))
  obtain ⟨M, hM, hQM, hx'⟩ := CaseOneChart.exists_plane_point B D x hx hbase hchart
  let : M.IsMaximal := hM
  subst x
  let P := D.prime M hQM
  let : P.IsPrime := inferInstance
  have htP : algebraMap A (saturatedChart A (maximalIdeal A) (t : A)) (t : A) ∈ P := by
    change (t : A) ∈ P.comap (algebraMap A (saturatedChart A (maximalIdeal A) (t : A)))
    rw [show P.comap (algebraMap A (saturatedChart A (maximalIdeal A) (t : A))) =
      maximalIdeal A from D.prime_comap_base M hQM]
    exact t.property
  have hd : ringKrullDim (Localization.AtPrime P) = 2 := D.local_dimension M hQM ht hQ0
  have hs : ¬ IsRegularLocalRing (Localization.AtPrime P) := fun h =>
    hsing ((CaseOneChart.isRegular_iff B D M hQM).mpr h)
  obtain ⟨q, hmonic, hirr, hP, Q, hQ⟩ :=
    exists_actual_child_prime_parameter ht E F P htP hd
  refine ⟨P, inferInstance, q, Q, hmonic, hirr, hP, hQ, htP, rfl, hd, hs,
    CaseOneChart.stalkIso B D M hQM, ?_⟩
  exact CaseOneChart.stalkIso_stalkScalar B D M hQM

end AlgebraicGeometry.Scheme.RationalDoublePoint.CaseTwoPoint
