/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Blowup.Differentials.RegularPair.ExceptionalSection
public import Aglib.AlgebraicGeometry.Blowup.Differentials.RegularPair.OnePoleChart
public import Aglib.AlgebraicGeometry.Blowup.Differentials.RegularPair.ScaledSquare
public import Aglib.AlgebraicGeometry.Modules.Differentials.Relative.ExteriorCoefficient
public import Aglib.AlgebraicGeometry.Modules.StructureSheaf.AffineMultiplication
public import Aglib.AlgebraicGeometry.Modules.Tensor.Monoidal.SectionFrame
public import Aglib.AlgebraicGeometry.Modules.Tensor.Section

/-!
# The original regular-pair one-pole unit square

The actual one-pole chart map, preceded by original raw pullback and bidual
evaluation, is the original pulled coefficient followed by the actual
exceptional positive section. The scalar and frame equations are proved
from the actual ideal inclusion, not supplied as one-pole premises.
-/

@[expose] public noncomputable section

open CategoryTheory
open AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.Differentials

open AlgebraicGeometry.Scheme.Blowup.RegularPoint
open AlgebraicGeometry.Scheme.Blowup.IdealFrames

universe u vK


open AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Modules.Differentials

namespace AlgebraicGeometry.Scheme.Blowup.RegularPair

private theorem postcomp_square {C : Type*} [Category C] {A B D E F : C}
    (r : A ⟶ B) (v : B ⟶ D) (k : D ⟶ E) (frame : E ⟶ F)
    (g : A ⟶ E) (scalar : E ⟶ E) (sectionMap : E ⟶ F)
    (h : r ≫ (v ≫ k) = g ≫ scalar) (hs : sectionMap = scalar ≫ frame) :
    r ≫ v ≫ (k ≫ frame) = g ≫ sectionMap := by
  calc
    _ = (r ≫ (v ≫ k)) ≫ frame := by simp only [Category.assoc]
    _ = (g ≫ scalar) ≫ frame := congrArg (fun q => q ≫ frame) h
    _ = g ≫ (scalar ≫ frame) := Category.assoc _ _ _
    _ = _ := congrArg (fun q => g ≫ q) hs.symm

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

local notation "I" => Ideal.span (Set.insert x (Set.singleton y))
local notation "B" => Blowup.blowupDatum (Blowup.affineCenter R I)
local notation "a" => firstGenerator I x y rfl
local notation "c" => chartMap B a

/-- The original raw coefficient and the original exceptional section form
the actual one-pole chart square, with the original structural unit. -/
theorem saturatedPairOnePoleChartMap_unit :
    let f : Spec (.of S) ⟶ canonicalBlowup I := c
    let s : SheafOfModules.unit (canonicalBlowup I).ringCatSheaf ⟶
        (Invertible.dualLineBundle (canonicalBlowup I) (centreIdealLine I)).val :=
      cartierDualIdealSection (centreι B)
    rawFormsPullback (Spec.map α) (Spec.map σ) n ≫
      Invertible.bidualMap (Spec (.of S))
        (moduleExteriorPower (Spec (.of S))
          (relativeDifferentialSheaf (Spec.map σ ≫ Spec.map α)) n) ≫
      saturatedPairOnePoleChartMap Λ R K x y hx hy n L φ =
    (pullback (Spec.map σ)).map φ ≫
      (positiveCartierTensorSection (Spec (.of S))
        (saturatedPairExceptionalPositiveLine R x y).val
        ((pullbackUnitIso f).inv ≫
          (pullback f).map s)).app
            ((pullback (Spec.map σ)).obj L.val) ≫
      (tensorSheafBraiding (Spec (.of S)) (saturatedPairExceptionalPositiveLine R x y).val
        ((pullback (Spec.map σ)).obj L.val)).hom := by
  intro f s
  have hs := positiveSection_tensorFrame ((pullback (Spec.map σ)).obj L.val)
    (saturatedPairExceptionalPositiveLine R x y).val
    (saturatedPairExceptionalPositiveFrame R x y)
    ((pullbackUnitIso f).inv ≫ (pullback f).map s)
    (affineMultiplication S (algebraMap R S x))
    (saturatedPair_exceptionalPositiveSection_frame R x y)
  exact postcomp_square _ _ _ _ _ _ _
    (saturatedPair_scaledBidualSquare Λ R K x y hx hy n L φ) hs

end AlgebraicGeometry.Scheme.Blowup.RegularPair
