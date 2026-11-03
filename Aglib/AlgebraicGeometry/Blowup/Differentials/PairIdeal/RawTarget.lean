/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Blowup.Differentials.PairIdeal.Target
public import Aglib.AlgebraicGeometry.Blowup.Differentials.RegularPair.OnePoleRaw


/-!
# The original raw target map on the supplied ideal's chart

Transport the sole regular-pair raw construction along the proved equality
with the original ideal. Its canonical extension is the existing bidual
map on the same chart of the same blowup, not an alternative construction.
-/

@[expose] public noncomputable section

open CategoryTheory
open AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.Differentials
open AlgebraicGeometry.Scheme.Blowup.RegularPoint AlgebraicGeometry.Scheme.Blowup.IdealFrames

universe u vK


open AlgebraicGeometry.Scheme.Blowup.RegularPair

namespace AlgebraicGeometry.Scheme.Blowup.PairIdeal

variable (Λ R : Type u) (K : Type vK) [CommRing Λ] [CommRing R] [IsDomain R] [Field K]
  [Algebra Λ R] [Algebra R K] [Algebra Λ K] [IsScalarTower Λ R K]
  [IsFractionRing R K] (I : Ideal R) (x y : R) (hI : Ideal.span {x, y} = I)
  (hx : IsSMulRegular R x) (hy : IsSMulRegular (R ⧸ Ideal.span {x}) y)
  (n : ℕ) (L : Invertible.LineBundle (Spec (.of R)))
  (φ : moduleExteriorPower (Spec (.of R))
    (relativeDifferentialSheaf (Spec.map (CommRingCat.ofHom (algebraMap Λ R)))) n ⟶ L.val)

local notation "S" => Localization.Away.saturatedChart R I x
local notation "B" => Blowup.blowupDatum (Blowup.affineCenter R I)
local notation "T" => centreTwistedPullbackLine I L

/-- The sole raw chart map with the same original global target. -/
def pairIdealOnePoleRawTargetMap :
    let f : Spec (.of S) ⟶ canonicalBlowup I := chartMap B (firstGenerator I x y hI)
    moduleExteriorPower (Spec (.of S))
      (relativeDifferentialSheaf
        (Spec.map (CommRingCat.ofHom (algebraMap R S)) ≫
          Spec.map (CommRingCat.ofHom (algebraMap Λ R)))) n ⟶
    (pullback f).obj (T).val := by
  subst I
  exact saturatedPairOnePoleRawTargetMap Λ R K x y hx hy n L φ

/-- The existing bidual target map is the extension of the same original raw target map. -/
theorem pairIdealOnePoleTargetMap_eq_extension :
    let f : Spec (.of S) ⟶ canonicalBlowup I := chartMap B (firstGenerator I x y hI)
    pairIdealOnePoleTargetMap Λ R K I x y hI hx hy n L φ =
      Invertible.extendToBidualLine (Spec (.of S)) (Invertible.pullbackLineBundle f T)
        (pairIdealOnePoleRawTargetMap Λ R K I x y hI hx hy n L φ) := by
  subst I
  exact saturatedPairOnePoleTargetMap_eq_extension Λ R K x y hx hy n L φ

end AlgebraicGeometry.Scheme.Blowup.PairIdeal
