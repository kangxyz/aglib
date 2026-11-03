/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.Blowup.RegularPair.RawExterior

public import Aglib.AlgebraicGeometry.Modules.Differentials.Relative.AffineRawSections
public import Aglib.AlgebraicGeometry.Modules.Differentials.Relative.ExteriorCoefficient
public import Aglib.RingTheory.Kaehler.Exterior.BaseChange
public import Aglib.RingTheory.Kaehler.Exterior.Map


/-!
# The genuine regular-pair bound for the original sheaf pullback arrow

The actual saturated chart and original scheme maps are retained. The
regular-pair algebraic bound is transported along the proved original affine
arrow and section comparisons, rather than assumed for the sheaf map.
-/

@[expose] public noncomputable section

open CategoryTheory
open AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.Differentials

universe u


open AlgebraicGeometry.Scheme.Modules.Differentials
open KaehlerDifferential

namespace AlgebraicGeometry.Scheme.Blowup.RegularPair

/-- On the original saturated regular-pair chart, multiplication by the
exceptional coordinate lands in the image of the ORIGINAL raw sheaf pullback. -/
theorem saturatedPair_rawPullback_imageBound {Λ R : CommRingCat.{u}}
    (α : Λ ⟶ R) (x y : R) (hx : IsSMulRegular R x)
    (hy : IsSMulRegular (R ⧸ Ideal.span {x}) y) (n : ℕ) :
    let S := CommRingCat.of (Localization.Away.saturatedChart R (Ideal.span {x, y}) x)
    let σ : R ⟶ S := CommRingCat.ofHom
      (algebraMap R (Localization.Away.saturatedChart R (Ideal.span {x, y}) x))
    ∀ z : moduleSpecΓFunctor.obj (moduleExteriorPower (Spec S)
      (relativeDifferentialSheaf (Spec.map σ ≫ Spec.map α)) n),
      σ x • z ∈ LinearMap.range
        (moduleSpecΓFunctor.map (rawFormsPullback (Spec.map α) (Spec.map σ) n)).hom := by
  intro S σ z
  let := α.hom.toAlgebra
  let aRS : Algebra R S := inferInstance
  let presentationWith (a : Algebra R S) :=
    @IsAdjoinRoot R S _ _ a (Localization.Away.pairPolynomial x y)
  have hRS : σ.hom.toAlgebra = aRS := toAlgebra_algebraMap (R := R) (S := S)
  have hpres0 : presentationWith aRS :=
    Localization.Away.saturatedPairPresentation x y hx hy
  let := σ.hom.toAlgebra
  let := (α ≫ σ).hom.toAlgebra
  let : IsScalarTower Λ R S := IsScalarTower.of_algebraMap_eq' rfl
  have hpres : IsAdjoinRoot S (Localization.Away.pairPolynomial x y) :=
    Eq.mp (congrArg presentationWith hRS.symm) hpres0
  apply (rawPullbackSections_mem_range_iff α σ n (σ x • z)).mp
  rw [_root_.map_smul]
  let w : ⋀[S]^n (KaehlerDifferential Λ S) := rawPullbackTargetSectionsEquiv α σ n z
  have hb : σ x • w ∈ LinearMap.range (KaehlerDifferential.mapExteriorBaseChange Λ R S n) := by
    rw [KaehlerDifferential.mapExteriorBaseChange_range]
    exact IsAdjoinRoot.pair_exceptional_smul_exterior_mem_range hpres Λ n w
  exact hb

end AlgebraicGeometry.Scheme.Blowup.RegularPair
