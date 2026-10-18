/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.Relative.AffineTrace
public import Aglib.AlgebraicGeometry.Cohomology.DirectImage.Affine.DerivedModel
public import Aglib.AlgebraicGeometry.Cohomology.Functoriality.Pushforward
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Affine.TildeExact
public import Aglib.AlgebraicGeometry.Modules.LocallyFree.Basic
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Tensor

/-!
# The actual affine derived model of differential coefficients

The original determinant/twist comparison, original affine coefficient trace,
and original tilde counit identify the actual derived pushforward of a
quasicoherent differential coefficient with its degree-n single. This supplies
both bounds; it does not identify a separately constructed trace arrow.
No Noetherianity or coefficient-flatness assumption is used.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.ProjectiveSpace AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Modules.Differentials

universe u
attribute [local instance] AlgebraicGeometry.Scheme.Modules.standardHasDerivedCategory
attribute [local instance] AlgebraicGeometry.Scheme.Cohomology.projectiveCoefficientTraceTarget

namespace AlgebraicGeometry.Scheme.Cohomology

variable (R : Type u) [CommRing R] (ι : Type u)

/-- The original affine coefficient comparison, including the actual tilde counit. -/
def projectiveDifferentialCoefficientResidueIso (n : ℕ) (e : ι ≃ Fin (n + 1))
    (N : (Spec (.of R)).Modules) [N.IsQuasicoherent] :
    letI : Fintype ι := Fintype.ofEquiv (Fin (n + 1)) e.symm
    (relativeTopDifferentialCoefficientsFunctor (toSpec R ι) n).obj N ≅
      projectiveResidueTwistTensorCoefficients R ι (moduleSpecΓFunctor.obj N) := by
  let : Fintype ι := Fintype.ofEquiv (Fin (n + 1)) e.symm
  exact (relativeTopDifferentialCoefficientsFunctor (toSpec R ι) n).mapIso
      (asIso N.fromTildeΓ).symm ≪≫
    projectiveDifferentialCoefficientsTwistingIso R ι n e (moduleSpecΓFunctor.obj N)

/-- The actual direct image of a differential coefficient is concentrated in the top
projective degree, via original affine direct-image and residue models. -/
def projectiveDifferentialCoefficientsAffineSingleIso
    (n : ℕ) (e : ι ≃ Fin (n + 1)) (N : (Spec (.of R)).Modules) [N.IsQuasicoherent] :
    (Scheme.Modules.derivedPushforwardPlus (toSpec R ι)).obj
        ((DerivedCategory.Plus.singleFunctor (ProjectiveSpace R ι).Modules 0).obj
          ((relativeTopDifferentialCoefficientsFunctor (toSpec R ι) n).obj N)) ≅
      (DerivedCategory.Plus.singleFunctor (Spec (.of R)).Modules (n : ℤ)).obj N := by
  let : Fintype ι := Fintype.ofEquiv (Fin (n + 1)) e.symm
  let P := ProjectiveSpace R ι
  let α := (toSpec R ι).appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom
  let G := moduleGlobalSectionsFunctorOfHom P α
  let Ω := (relativeTopDifferentialCoefficientsFunctor (toSpec R ι) n).obj N
  let J := moduleSpecΓFunctor.obj N
  let : IsFiniteLocallyFree P
      (moduleExteriorPower P (relativeDifferentialSheaf (toSpec R ι)) n) :=
    finiteLocallyFree_of_iso (differentialResidueTwistingIso R ι n e).symm
  let : Ω.IsQuasicoherent := isQuasicoherent_moduleTensorLeftFunctor
    (moduleExteriorPower P (relativeDifferentialSheaf (toSpec R ι)) n)
    ((Scheme.Modules.pullback (toSpec R ι)).obj N)
  let E := projectiveDifferentialCoefficientResidueIso R ι n e N
  let : IsIso (projectiveDerivedTraceCoefficients R ι n e J) :=
    projectiveDerivedTraceCoefficients_isIso R ι n e J
  let D := (G.rightDerivedFunctorPlus ⋙ DerivedCategory.Plus.ι).mapIso
      ((DerivedCategory.Plus.singleFunctor P.Modules 0).mapIso E) ≪≫
    asIso (projectiveDerivedTraceCoefficients R ι n e J)
  let Dplus : G.rightDerivedFunctorPlus.obj
        ((DerivedCategory.Plus.singleFunctor P.Modules 0).obj Ω) ≅
      (DerivedCategory.Plus.singleFunctor (ModuleCat.{u} R) (n : ℤ)).obj J :=
    (Functor.FullyFaithful.ofFullyFaithful
      (DerivedCategory.Plus.ι (C := ModuleCat.{u} R))).preimageIso D
  let C := (CochainComplex.singleFunctorPlus (ModuleCat.{u} R) (n : ℤ)).obj J
  let B := moduleSpecDerivedPushforwardModelIso (toSpec R ι) (injectiveResolution Ω) C Dplus.symm
  let A : CommRingCat.{u} := .of R
  let Tilde := tilde.functor A
  let : Tilde.Additive := {
    map_add {_P _Q} g h := tilde.map_add g h }
  let S : Tilde.mapCochainComplexPlus.obj C ≅
      (CochainComplex.singleFunctorPlus (Spec (.of R)).Modules (n : ℤ)).obj (tilde J) :=
    (CochainComplex.plus (Spec (.of R)).Modules).isoMk
      ((HomologicalComplex.singleMapHomologicalComplex Tilde (.up ℤ) (n : ℤ)).app J)
  exact B.symm ≪≫ DerivedCategory.Plus.Q.mapIso S ≪≫
    (DerivedCategory.Plus.singleFunctor (Spec (.of R)).Modules (n : ℤ)).mapIso
      (asIso N.fromTildeΓ)

/-- In particular, lower-degree cohomology vanishes for this actual affine coefficient image. -/
theorem projectiveDifferentialCoefficientsAffine_isGE
    (n : ℕ) (e : ι ≃ Fin (n + 1)) (N : (Spec (.of R)).Modules) [N.IsQuasicoherent] :
    ((Scheme.Modules.derivedPushforwardPlus (toSpec R ι)).obj
      ((DerivedCategory.Plus.singleFunctor (ProjectiveSpace R ι).Modules 0).obj
        ((relativeTopDifferentialCoefficientsFunctor (toSpec R ι) n).obj N))).IsGE (n : ℤ) :=
  DerivedCategory.Plus.TStructure.t.isGE_of_iso
    (projectiveDifferentialCoefficientsAffineSingleIso R ι n e N).symm (n : ℤ)

end AlgebraicGeometry.Scheme.Cohomology
