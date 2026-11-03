/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Blowup.ChartNonempty
public import Aglib.AlgebraicGeometry.Blowup.Differentials.PairIdeal.RawGluing
public import Aglib.AlgebraicGeometry.Blowup.Differentials.PairIdeal.RawUnitSquare
public import Aglib.AlgebraicGeometry.Blowup.Differentials.UnitMap
public import Aglib.AlgebraicGeometry.Blowup.Integral.NonzeroIdeal
public import Aglib.AlgebraicGeometry.Blowup.PairIdeal.Cover
public import Aglib.AlgebraicGeometry.Modules.Differentials.Relative.ExteriorCoefficient
public import Aglib.AlgebraicGeometry.Modules.Invertible.GenericUniqueness.Open


/-!
# Extend the original glued raw one-pole map once

The original raw map has the intrinsic global unit equation. Its single
canonical extension to the actual bidual retains that equation by forward
evaluation. Equality with existing bidual local maps is a separate restriction
comparison, not a consequence of canceling raw evaluation.
-/

@[expose] public noncomputable section

open CategoryTheory
open AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.Differentials
open AlgebraicGeometry.Scheme.Blowup.RegularPoint

universe u vK


open AlgebraicGeometry.Scheme.Blowup
open AlgebraicGeometry.Scheme.Modules.Differentials
open AlgebraicGeometry.Scheme.Modules.Invertible

namespace AlgebraicGeometry.Scheme.Blowup.PairIdeal

variable (Λ R : Type u) (K : Type vK) [CommRing Λ] [CommRing R] [IsDomain R]
  [IsNoetherianRing R] [Field K]
  [Algebra Λ R] [Algebra R K] [Algebra Λ K] [IsScalarTower Λ R K]
  [IsFractionRing R K] (I : Ideal R) (x y : R) (hI : Ideal.span {x, y} = I)
  (hx : IsSMulRegular R x) (hy : IsSMulRegular (R ⧸ Ideal.span {x}) y)
  (hproper : I ≠ ⊤) (n : ℕ) (L : Invertible.LineBundle (Spec (.of R)))
  (φ : moduleExteriorPower (Spec (.of R))
    (relativeDifferentialSheaf (Spec.map (CommRingCat.ofHom (algebraMap Λ R)))) n ⟶ L.val)

local notation "X" => canonicalBlowup I
local notation "α" => CommRingCat.ofHom (algebraMap Λ R)
local notation "M" => moduleExteriorPower X
  (relativeDifferentialSheaf (blowdown I ≫ Spec.map α)) n
local notation "T" => Invertible.tensorLineBundle X
  (Invertible.pullbackLineBundle (blowdown I) L)
  (Invertible.dualLineBundle X (centreIdealLine I))

omit [IsNoetherianRing R] in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The uniquely glued original raw map has the original global coefficient/unit equation. -/
theorem pairIdealOnePoleRawMap_unit :
    rawFormsPullback (Spec.map α) (blowdown I) n ≫
        pairIdealOnePoleRawMap Λ R K I x y hI hx hy hproper n L φ =
      pairIdealOnePoleUnitMap Λ R I n L φ := by
  have hx0 : x ≠ 0 := by
    intro h
    exact one_ne_zero (hx (by simp [h]))
  have hxI : x ∈ I := hI ▸ Ideal.subset_span (Set.mem_insert x {y})
  let _ : IsIntegral X := idealBlowup_isIntegral_of_mem_ne_zero I x hxI hx0
  let _ : Nonempty (pairIdealChartScheme I x y hI true) :=
    pairIdealChart_nonempty R K I x y hI hx hy hproper true
  apply Invertible.hom_ext_of_nonempty_restrict (pairIdealChart I x y hI true) (Subtype.property T)
  rw [CategoryTheory.Functor.map_comp,
    pairIdealOnePoleRawMap_restrict Λ R K I x y hI hx hy hproper n L φ true]
  exact pairIdealOnePoleRawRestrictionMap_unit Λ R K I x y hI hx hy n L φ

/-- The single canonical bidual extension of the same uniquely glued original raw map. -/
def pairIdealOnePoleMap :
    Invertible.dualSheaf X (Invertible.dualSheaf X M) ⟶ Subtype.val T :=
  Invertible.extendToBidualLine X T (pairIdealOnePoleRawMap Λ R K I x y hI hx hy hproper n L φ)

omit [IsNoetherianRing R] in
/-- Forward raw evaluation recovers the same original raw map, without any epi cancellation. -/
theorem pairIdealOnePoleMap_evaluation :
    Invertible.bidualMap X M ≫ pairIdealOnePoleMap Λ R K I x y hI hx hy hproper n L φ =
      pairIdealOnePoleRawMap Λ R K I x y hI hx hy hproper n L φ :=
  Invertible.extendToBidualLine_evaluation X T
    (pairIdealOnePoleRawMap Λ R K I x y hI hx hy hproper n L φ)

omit [IsNoetherianRing R] in
/-- The canonical extension retains the original global coefficient and exceptional-unit map. -/
theorem pairIdealOnePoleMap_unit :
    rawFormsPullback (Spec.map α) (blowdown I) n ≫
        Invertible.bidualMap X M ≫ pairIdealOnePoleMap Λ R K I x y hI hx hy hproper n L φ =
      pairIdealOnePoleUnitMap Λ R I n L φ :=
  (congrArg (fun z => rawFormsPullback (Spec.map α) (blowdown I) n ≫ z)
    (pairIdealOnePoleMap_evaluation Λ R K I x y hI hx hy hproper n L φ)).trans
      (pairIdealOnePoleRawMap_unit Λ R K I x y hI hx hy hproper n L φ)

end AlgebraicGeometry.Scheme.Blowup.PairIdeal
