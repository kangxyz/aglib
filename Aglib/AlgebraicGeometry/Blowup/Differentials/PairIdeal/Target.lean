/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Blowup.Differentials.RegularPair.OnePoleTarget


/-!
# The same original ideal and blowup for both parameter charts

An explicit equality of the parameter ideal with the original ideal
transports the sole regular-pair construction. The output is on the
original chart of the original blowup, with its original global tensor
line. Swapping parameters therefore need not select a second blowup.
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

/-- The sole chart construction, transported to the supplied original centre ideal. -/
def pairIdeal_onePoleTargetMap :
    let S := Localization.Away.saturatedChart R I x
    let f : Spec (.of S) ⟶ canonicalBlowup I :=
      chartMap (Blowup.blowupDatum (Blowup.affineCenter R I)) (firstGenerator I x y hI)
    Invertible.dualSheaf (Spec (.of S)) (Invertible.dualSheaf (Spec (.of S))
      (moduleExteriorPower (Spec (.of S))
        (relativeDifferentialSheaf
          (Spec.map (CommRingCat.ofHom (algebraMap R S)) ≫
            Spec.map (CommRingCat.ofHom (algebraMap Λ R)))) n)) ⟶
    (pullback f).obj
      (centreTwistedPullbackLine I L).val := by
  subst I
  exact saturatedPair_onePoleTargetMap Λ R K x y hx hy n L φ

end AlgebraicGeometry.Scheme.Blowup.PairIdeal
