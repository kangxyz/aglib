/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Blowup.Differentials.RegularPair.ScaledBidual
public import Aglib.AlgebraicGeometry.Modules.Differentials.Relative.AffineRawSections
public import Aglib.AlgebraicGeometry.Modules.Differentials.Relative.ExteriorCoefficient
public import Aglib.AlgebraicGeometry.Modules.StructureSheaf.AffineMultiplication
public import Aglib.AlgebraicGeometry.Modules.Tensor.Monoidal.UnitScalar


/-!
# The original scaled coefficient square as an ordinary sheaf equality

The original raw pullback, actual bidual evaluation and constructed scaled
map compose to the original pulled coefficient followed by actual scalar
multiplication through the tensor unit. Equality follows from native affine
faithfulness and the already proved original section equations.
-/

@[expose] public noncomputable section

open CategoryTheory
open AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.Differentials

universe u vK


open AlgebraicGeometry.Scheme.Modules
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

/-- The actual raw/bidual coefficient square, with the original scalar
inserted through the native tensor unit rather than an assumed square. -/
theorem saturatedPair_scaledBidualSquare :
    rawFormsPullback (Spec.map α) (Spec.map σ) n ≫
      (Invertible.bidualMap (Spec (.of S))
          (moduleExteriorPower (Spec (.of S))
            (relativeDifferentialSheaf (Spec.map σ ≫ Spec.map α)) n) ≫
        saturatedPairScaledBidualMap Λ R K x y hx hy n L φ) =
    (pullback (Spec.map σ)).map φ ≫
      ((tensorSheafLeftUnit (Spec (.of S)) ((pullback (Spec.map σ)).obj L.val)).inv ≫
        (moduleTensorCoefficientMap (Spec (.of S))
          (affineMultiplication S (algebraMap R S x))).app
            ((pullback (Spec.map σ)).obj L.val) ≫
        (tensorSheafLeftUnit (Spec (.of S)) ((pullback (Spec.map σ)).obj L.val)).hom) := by
  let : ((pullback (Spec.map σ)).obj
      (moduleExteriorPower (Spec (.of R))
        (relativeDifferentialSheaf (Spec.map α)) n)).IsQuasicoherent :=
    (SheafOfModules.isQuasicoherent (Spec (.of S)).ringCatSheaf).prop_of_iso
      (rawPullbackAffineSourceIso α σ n).symm inferInstance
  let : ((pullback (Spec.map σ)).obj L.val).IsQuasicoherent :=
    Invertible.lineBundle_isQuasicoherent (Invertible.pullbackLineBundle (Spec.map σ) L)
  apply hom_eq_of_globalSections_eq
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro p
  exact (saturatedPairScaledBidualMap_comp_apply Λ R K x y hx hy n L φ p).trans
    (affine_tensor_unit_scalar ((pullback (Spec.map σ)).obj L.val) (algebraMap R S x)
      (moduleSpecΓFunctor.map ((pullback (Spec.map σ)).map φ) p)).symm

end AlgebraicGeometry.Scheme.Blowup.RegularPair
