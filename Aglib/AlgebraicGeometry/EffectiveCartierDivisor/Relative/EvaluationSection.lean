/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.BaseChange.LineBundleEvaluation
public import Aglib.AlgebraicGeometry.EffectiveCartierDivisor.Relative.Graph
public import Aglib.AlgebraicGeometry.Modules.ZeroLocus

/-!
Native migration from `R5Lab.Aglib.AlgebraicGeometry.Divisors.Relative.EvaluationSection` at R5
revision
`f8a3314ddecffcada2ec721d26d56a937bed9690`, SHA-256
`bd719c47da7f1fb05634527cfcacb9e84cc4dabe838710e536dd06f72e1e03e1`.
Original objects, maps, universes and explicit hypotheses are retained.
Native providers replace duplicate implementations.
-/

@[expose] public section

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open _root_.AlgebraicGeometry.Scheme.Cohomology (FibreCohomologyConcentrated)
open _root_.AlgebraicGeometry.Scheme.Modules.Invertible (LineBundle)
open AlgebraicGeometry.Scheme.Hom AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Modules.Hom
open AlgebraicGeometry.Scheme.Modules.Invertible
open _root_.AlgebraicGeometry.Scheme.Cohomology (evaluationContraction)
namespace AlgebraicGeometry.Scheme.Hom
universe u
open AlgebraicGeometry.Scheme.Modules.Invertible AlgebraicGeometry.Scheme.Hom
variable {Z S : Scheme.{u}} (f : Z ⟶ S)
variable [IsLocallyNoetherian S]
variable [IsProper f] [LocallyOfFinitePresentation f] [Flat f]
variable (L : LineBundle Z) (hL : FibreCohomologyConcentrated f L.val 1)
variable [IsIso (zeroInclusion (evaluationContraction f L hL) ≫ f)]
/-- The section of `f` obtained by inverting the projection from the actual
evaluation zero divisor. -/
def evaluationZeroSection : S ⟶ Z :=
  inv (zeroInclusion (evaluationContraction f L hL) ≫ f) ≫
    zeroInclusion (evaluationContraction f L hL)

@[reassoc (attr := simp)] theorem evaluationZeroSection_over :
    evaluationZeroSection f L hL ≫ f = 𝟙 S := by
  simp [evaluationZeroSection, Category.assoc]

@[reassoc (attr := simp)] theorem evaluationZeroSection_source :
    zeroInclusion (evaluationContraction f L hL) ≫ f ≫
      evaluationZeroSection f L hL = zeroInclusion (evaluationContraction f L hL) := by
  simp [evaluationZeroSection, ← Category.assoc]

/-- The canonical ideal comparison between the evaluation section and its
evaluation zero divisor. -/
def evaluationZeroSectionIdealIso :
    idealModule (evaluationZeroSection f L hL) ≅
      idealModule (zeroInclusion (evaluationContraction f L hL)) :=
  idealSourceIso (asIso (zeroInclusion (evaluationContraction f L hL) ≫ f))
    (evaluationZeroSection f L hL) ≪≫
      eqToIso (congrArg idealModule
        ((Category.assoc (zeroInclusion (evaluationContraction f L hL)) f
          (evaluationZeroSection f L hL)).trans (evaluationZeroSection_source f L hL)))
end AlgebraicGeometry.Scheme.Hom
