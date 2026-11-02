/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Blowup.PairIdeal.Cover
public import Aglib.RingTheory.Localization.Away.SaturatedChart.FractionRing
public import Aglib.RingTheory.Regular.PairPermutation


/-!
# Nonempty original parameter charts

The original saturated-chart map to the same fraction field gives an actual
point. Both parameter orders are covered using the proved proper regular-pair
swap; no replacement affine chart or field is selected.
-/

@[expose] public noncomputable section

open CategoryTheory
open AlgebraicGeometry.Scheme.Blowup.RegularPoint

universe u vK


open AlgebraicGeometry.Scheme.Blowup.PairIdeal
open Localization.Away

namespace AlgebraicGeometry.Scheme.Blowup

/-- The original map to the same fraction field gives a point of the actual saturated chart. -/
theorem saturatedChart_nonempty (R : Type u) (K : Type vK) [CommRing R] [IsDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K] (I : Ideal R) (x : R) (hx : x ≠ 0) :
    Nonempty (Spec (.of (Localization.Away.saturatedChart R I x))) :=
  ⟨PrimeSpectrum.comap
    (Localization.Away.saturatedChartFractionMap R K I x hx).toRingHom
      (genericPoint (Spec (.of K)))⟩

/-- Each member of the original two-chart cover is nonempty under the actual proper-pair inputs. -/
theorem pairIdealChart_nonempty (R : Type u) (K : Type vK) [CommRing R] [IsDomain R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    (I : Ideal R) (x y : R) (hI : Ideal.span {x, y} = I)
    (hx : IsSMulRegular R x) (hy : IsSMulRegular (R ⧸ Ideal.span {x}) y)
    (hproper : I ≠ ⊤) (i : Bool) : Nonempty (pairIdealChartScheme I x y hI i) := by
  have hx0 : x ≠ 0 := by
    intro h
    exact one_ne_zero (hx (by simp [h]))
  have hs := IsSMulRegular.proper_pair_swap_of_isDomain x y hx hy (hI.symm ▸ hproper)
  have hy0 : y ≠ 0 := by
    intro h
    exact one_ne_zero (hs.1 (by simp [h]))
  cases i
  · exact saturatedChart_nonempty R K I y hy0
  · exact saturatedChart_nonempty R K I x hx0

end AlgebraicGeometry.Scheme.Blowup
