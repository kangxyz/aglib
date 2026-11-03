/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Blowup.Differentials.RegularPair.ScaledSheaf
public import Aglib.AlgebraicGeometry.Modules.Differentials.Relative.ExteriorCoefficient
public import Aglib.AlgebraicGeometry.Modules.Invertible.Bidual.Map


/-!
# The actual regular-pair scaled map on the original bidual

The constructed raw map extends by native double dualization and the
original evaluation isomorphism of the pulled-back line. No isomorphism
between pullback and bidual is used. The original x-scaled normalization
is retained through the original raw evaluation.
-/

@[expose] public noncomputable section

open CategoryTheory
open AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.Differentials

universe u vK


open AlgebraicGeometry.Scheme.Modules.Differentials

namespace AlgebraicGeometry.Scheme.Blowup.RegularPair

variable (Λ R : Type u) (K : Type vK) [CommRing Λ] [CommRing R] [IsDomain R] [Field K]
  [Algebra Λ R] [Algebra R K] [Algebra Λ K] [IsScalarTower Λ R K]
  [IsFractionRing R K] (x y : R)
  (hx : IsSMulRegular R x) (hy : IsSMulRegular (R ⧸ Ideal.span {x}) y)
  (n : ℕ) (L : Invertible.LineBundle (Spec (.of R)))
  (φ : moduleExteriorPower (Spec (.of R))
    (relativeDifferentialSheaf (Spec.map (CommRingCat.ofHom (algebraMap Λ R)))) n ⟶ L.val)

local notation "S" =>
  Localization.Away.saturatedChart R (Ideal.span (Set.insert x (Set.singleton y))) x
local notation "α" => CommRingCat.ofHom (algebraMap Λ R)
local notation "σ" => CommRingCat.ofHom (algebraMap R S)

/-- Extend the constructed scaled raw map to its actual source bidual. -/
def saturatedPairScaledBidualMap :
    Invertible.dualSheaf (Spec (.of S)) (Invertible.dualSheaf (Spec (.of S))
      (moduleExteriorPower (Spec (.of S))
        (relativeDifferentialSheaf (Spec.map σ ≫ Spec.map α)) n)) ⟶
    (pullback (Spec.map σ)).obj L.val :=
  Invertible.extendToBidualLine (Spec (.of S))
    (Invertible.pullbackLineBundle (Spec.map σ) L)
    (saturatedPairScaledRawMap Λ R K x y hx hy n L φ)

/-- The native extension agrees with the original scaled map on raw forms. -/
theorem saturatedPairScaledBidualMap_evaluation :
    Invertible.bidualMap (Spec (.of S))
        (moduleExteriorPower (Spec (.of S))
          (relativeDifferentialSheaf (Spec.map σ ≫ Spec.map α)) n) ≫
      saturatedPairScaledBidualMap Λ R K x y hx hy n L φ =
    saturatedPairScaledRawMap Λ R K x y hx hy n L φ :=
  Invertible.extendToBidualLine_evaluation _ _ _

/-- Original raw pullback sections retain exactly the original exceptional
coordinate under bidual evaluation followed by the constructed map. -/
theorem saturatedPairScaledBidualMap_comp_apply
    (p : moduleSpecΓFunctor.obj ((pullback (Spec.map σ)).obj
      (moduleExteriorPower (Spec (.of R)) (relativeDifferentialSheaf (Spec.map α)) n))) :
    moduleSpecΓFunctor.map
      (Invertible.bidualMap (Spec (.of S))
          (moduleExteriorPower (Spec (.of S))
            (relativeDifferentialSheaf (Spec.map σ ≫ Spec.map α)) n) ≫
        saturatedPairScaledBidualMap Λ R K x y hx hy n L φ)
      (moduleSpecΓFunctor.map (rawFormsPullback (Spec.map α) (Spec.map σ) n) p) =
    algebraMap R S x • (moduleSpecΓFunctor.map ((pullback (Spec.map σ)).map φ) p) := by
  have h := congrArg (fun f => moduleSpecΓFunctor.map f)
    (saturatedPairScaledBidualMap_evaluation Λ R K x y hx hy n L φ)
  exact (ConcreteCategory.congr_hom h
    (moduleSpecΓFunctor.map (rawFormsPullback (Spec.map α) (Spec.map σ) n) p)).trans
      (saturatedPairScaledRawMap_comp_apply Λ R K x y hx hy n L φ p)

end AlgebraicGeometry.Scheme.Blowup.RegularPair
