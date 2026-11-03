/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Blowup.Differentials.PairIdeal.RawRestriction
public import Aglib.AlgebraicGeometry.Blowup.Differentials.PairIdeal.RawUnitSquare
public import Aglib.AlgebraicGeometry.Blowup.Differentials.UnitMap
public import Aglib.AlgebraicGeometry.Blowup.PairIdeal.Cover
public import Aglib.AlgebraicGeometry.Modules.Differentials.Relative.ExteriorCoefficient
public import Aglib.RingTheory.Regular.PairPermutation


/-!
# The actual raw family on the full original two-chart cover

Both original parameter orders use the same supplied ideal and coefficient.
The reversed regular pair is derived under the actual proper-centre and domain
hypotheses, without locality or Noetherianity. Overlap compatibility is not assumed here.
-/

@[expose] public noncomputable section

open CategoryTheory
open AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.Differentials
open AlgebraicGeometry.Scheme.Blowup.RegularPoint

universe u vK


open AlgebraicGeometry.Scheme.Blowup
open AlgebraicGeometry.Scheme.Modules.Differentials

namespace AlgebraicGeometry.Scheme.Blowup.PairIdeal

variable (Λ R : Type u) (K : Type vK) [CommRing Λ] [CommRing R] [IsDomain R]
  [Field K]
  [Algebra Λ R] [Algebra R K] [Algebra Λ K] [IsScalarTower Λ R K]
  [IsFractionRing R K] (I : Ideal R) (x y : R) (hI : Ideal.span {x, y} = I)
  (hx : IsSMulRegular R x) (hy : IsSMulRegular (R ⧸ Ideal.span {x}) y)
  (hproper : I ≠ ⊤) (n : ℕ) (L : Invertible.LineBundle (Spec (.of R)))
  (φ : moduleExteriorPower (Spec (.of R))
    (relativeDifferentialSheaf (Spec.map (CommRingCat.ofHom (algebraMap Λ R)))) n ⟶ L.val)

local notation "Y" => canonicalBlowup I
local notation "M" => moduleExteriorPower Y (relativeDifferentialSheaf
  (blowdown I ≫ Spec.map (CommRingCat.ofHom (algebraMap Λ R)))) n
local notation "N" => Subtype.val (Invertible.tensorLineBundle Y
  (Invertible.pullbackLineBundle (blowdown I) L)
  (Invertible.dualLineBundle Y (centreIdealLine I)))

/-- The two actual raw maps on the proved full original chart cover, with no overlap premise. -/
def pairIdealOnePoleRawFamily (i : Bool) :
    (Scheme.Modules.restrictFunctor (pairIdealChart I x y hI i)).obj M ⟶
      (Scheme.Modules.restrictFunctor (pairIdealChart I x y hI i)).obj N := by
  cases i
  · have hs := IsSMulRegular.proper_pair_swap_of_isDomain x y hx hy (hI.symm ▸ hproper)
    exact pairIdealOnePoleRawRestrictionMap Λ R K I y x (Ideal.span_pair_comm.trans hI)
      hs.1 hs.2 n L φ
  · exact pairIdealOnePoleRawRestrictionMap Λ R K I x y hI hx hy n L φ

/-- The true index is the original raw map on the first parameter chart. -/
theorem pairIdealOnePoleRawFamily_true :
    pairIdealOnePoleRawFamily Λ R K I x y hI hx hy hproper n L φ true =
      pairIdealOnePoleRawRestrictionMap Λ R K I x y hI hx hy n L φ := by
  rfl

/-- The false index is the original reversed-chart raw map with the same derived pair. -/
theorem pairIdealOnePoleRawFamily_false :
    pairIdealOnePoleRawFamily Λ R K I x y hI hx hy hproper n L φ false =
      let hs := IsSMulRegular.proper_pair_swap_of_isDomain x y hx hy (hI.symm ▸ hproper)
      pairIdealOnePoleRawRestrictionMap Λ R K I y x (Ideal.span_pair_comm.trans hI)
        hs.1 hs.2 n L φ := by
  rfl

/-- Every original raw chart map satisfies the original coefficient/unit equation. -/
theorem pairIdealOnePoleRawFamily_unit :
    ∀ i : Bool, (Scheme.Modules.restrictFunctor (pairIdealChart I x y hI i)).map
        (rawFormsPullback (Spec.map (CommRingCat.ofHom (algebraMap Λ R))) (blowdown I) n) ≫
        pairIdealOnePoleRawFamily Λ R K I x y hI hx hy hproper n L φ i =
      (Scheme.Modules.restrictFunctor (pairIdealChart I x y hI i)).map
        (pairIdealOnePoleUnitMap Λ R I n L φ) := by
  intro i
  cases i
  · have hs := IsSMulRegular.proper_pair_swap_of_isDomain x y hx hy (hI.symm ▸ hproper)
    rw [pairIdealOnePoleRawFamily_false Λ R K I x y hI hx hy hproper n L φ]
    exact pairIdealOnePoleRawRestrictionMap_unit Λ R K I y x (Ideal.span_pair_comm.trans hI)
      hs.1 hs.2 n L φ
  · rw [pairIdealOnePoleRawFamily_true Λ R K I x y hI hx hy hproper n L φ]
    exact pairIdealOnePoleRawRestrictionMap_unit Λ R K I x y hI hx hy n L φ

end AlgebraicGeometry.Scheme.Blowup.PairIdeal
