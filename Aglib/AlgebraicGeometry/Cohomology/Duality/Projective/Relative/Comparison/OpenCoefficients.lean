/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.Relative.Comparison.OpenAdjunction
public import Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.Relative.OpenPushforward
public import Aglib.AlgebraicGeometry.Cohomology.DirectImage.Restriction
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic

/-!
# Original Ext transport for affine-open differential coefficients

The original ordinary coefficient isomorphism and the supplied-resolution
restriction adjunction identify Ext into an affine-open direct image. This
records the source side of the relative Serre open square, including its
actual forward map; it does not assert compatibility with a trace.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Modules.Differentials

universe u
attribute [local instance] AlgebraicGeometry.Scheme.Modules.standardHasDerivedCategory

namespace AlgebraicGeometry.Scheme.Cohomology

private def openCoefficientHomIsoAddEquiv {C : Type*} [Category* C] [Preadditive C]
    {X X' Y Y' : C} (e : X ≅ X') (f : Y ≅ Y') : (X ⟶ Y) ≃+ (X' ⟶ Y') :=
  { Iso.homCongr e f with
    map_add' a b := by
      simp [Iso.homCongr_apply, Preadditive.comp_add, Preadditive.add_comp] }

@[simp] private theorem openCoefficientHomIsoAddEquiv_apply
    {C : Type*} [Category* C] [Preadditive C]
    {X X' Y Y' : C} (e : X ≅ X') (f : Y ≅ Y') (a : X ⟶ Y) :
    openCoefficientHomIsoAddEquiv e f a = e.inv ≫ a ≫ f.hom := rfl

variable {X Y U : Scheme.{u}} (p : X ⟶ Y) (j : U ⟶ Y)
  [IsOpenImmersion j] [IsAffineHom j] (n : ℕ)
  [IsFiniteLocallyFree X (moduleExteriorPower X (relativeDifferentialSheaf p) n)]
  (L : U.Modules) [L.IsQuasicoherent]
  [((relativeTopDifferentialCoefficientsFunctor (pullback.fst j p) n).obj L).IsQuasicoherent]

/-- The actual affine single comparison followed by the original coefficient isomorphism. -/
def relativeOpenCoefficientDerivedSingleIso :
    DerivedCategory.Plus.ι.obj
        ((Scheme.Modules.derivedPushforwardPlus (pullback.snd j p)).obj
          ((DerivedCategory.Plus.singleFunctor (pullback j p).Modules 0).obj
            ((relativeTopDifferentialCoefficientsFunctor (pullback.fst j p) n).obj L))) ≅
      (DerivedCategory.singleFunctor X.Modules 0).obj
        ((relativeTopDifferentialCoefficientsFunctor p n).obj
          ((Scheme.Modules.pushforward j).obj L)) := by
  let : IsAffineHom (pullback.snd j p) := MorphismProperty.pullback_snd j p inferInstance
  exact DerivedCategory.Plus.ι.mapIso
      (affineDerivedPushforwardSingleIso (pullback.snd j p)
        ((relativeTopDifferentialCoefficientsFunctor (pullback.fst j p) n).obj L)) ≪≫
    (DerivedCategory.singleFunctor X.Modules 0).mapIso
      (relativeTopDifferentialOpenPushforwardIso p j n L).symm

/-- Original affine-open Ext adjunction with its actual differential-coefficient maps. -/
@[no_expose] def relativeOpenCoefficientExtAddEquiv (M : X.Modules) (q : ℕ) :
    Ext.{u + 1} (M.restrict (pullback.snd j p))
        ((relativeTopDifferentialCoefficientsFunctor (pullback.fst j p) n).obj L) q ≃+
      Ext.{u + 1} M
        ((relativeTopDifferentialCoefficientsFunctor p n).obj
          ((Scheme.Modules.pushforward j).obj L)) q :=
  Ext.homAddEquiv.trans
    ((CategoryTheory.Adjunction.singleDerivedHomEquivOfInjectiveResolution
      (Scheme.Modules.restrictAdjunction (pullback.snd j p)) M (injectiveResolution
        ((relativeTopDifferentialCoefficientsFunctor (pullback.fst j p) n).obj L)) (q : ℤ)).trans
      ((openCoefficientHomIsoAddEquiv (Iso.refl _)
        ((shiftFunctor (DerivedCategory X.Modules) (q : ℤ)).mapIso
          (relativeOpenCoefficientDerivedSingleIso p j n L))).trans Ext.homAddEquiv.symm))

/-- The transported class has the original resolution adjoint and coefficient comparison
as its full-derived representative. -/
theorem relativeOpenCoefficientExtAddEquiv_hom (M : X.Modules) (q : ℕ)
    (x : Ext.{u + 1} (M.restrict (pullback.snd j p))
      ((relativeTopDifferentialCoefficientsFunctor (pullback.fst j p) n).obj L) q) :
    (relativeOpenCoefficientExtAddEquiv p j n L M q x).hom =
      CategoryTheory.Adjunction.singleDerivedHomEquivOfInjectiveResolution
        (Scheme.Modules.restrictAdjunction (pullback.snd j p)) M (injectiveResolution
          ((relativeTopDifferentialCoefficientsFunctor (pullback.fst j p) n).obj L)) (q : ℤ) x.hom ≫
        (shiftFunctor (DerivedCategory X.Modules) (q : ℤ)).map
          (relativeOpenCoefficientDerivedSingleIso p j n L).hom := by
  change Ext.homAddEquiv (relativeOpenCoefficientExtAddEquiv p j n L M q x) = _
  simp only [relativeOpenCoefficientExtAddEquiv, AddEquiv.trans_apply,
    AddEquiv.apply_symm_apply, Ext.homAddEquiv_apply]
  change 𝟙 ((DerivedCategory.singleFunctor X.Modules 0).obj M) ≫ _ ≫ _ = _
  rw [Category.id_comp, Functor.mapIso_hom]

end AlgebraicGeometry.Scheme.Cohomology

namespace AlgebraicGeometry.Scheme.Cohomology

/-- The installed single-degree shift comparison used by affine-open Hom transport. -/
def relativeOpenCoefficientShiftIso {C : Type*} [Category* C] [Abelian C]
    [HasDerivedCategory C] (N : C) (n q : ℤ) :
    ((DerivedCategory.singleFunctor C n).obj N)⟦q⟧ ≅
      ((DerivedCategory.singleFunctor C 0).obj N)⟦q - n⟧ :=
  ((DerivedCategory.singleFunctors C).shiftIso q (n - q) n (by omega)).app N ≪≫
    (((DerivedCategory.singleFunctors C).shiftIso (q - n) (n - q) 0 (by omega)).app N).symm

variable {W X U Y : Scheme.{u}} (i : W ⟶ X) (q : W ⟶ U) (p : X ⟶ Y) (j : U ⟶ Y)
  [IsOpenImmersion i] [IsOpenImmersion j] (H : IsPullback i q p j)

/-- Original open base change, expressed at the restriction of the actual pushed
source resolution. Exact restriction retains its original derived unit. -/
def relativeOpenPushforwardResolutionIso {M : X.Modules} (I : InjectiveResolution M) :
    DerivedCategory.Q.obj
        (((Scheme.Modules.restrictFunctor j).mapHomologicalComplex (.up ℤ)).obj
          (((Scheme.Modules.pushforward p).mapHomologicalComplex (.up ℤ)).obj I.cochainComplex)) ≅
      DerivedCategory.Plus.ι.obj ((Scheme.Modules.derivedPushforwardPlus q).obj
        ((DerivedCategory.Plus.singleFunctor W.Modules 0).obj (M.restrict i))) := by
  let J := Scheme.Modules.restrictFunctor j
  let A := Scheme.Modules.restrictFunctor i
  let P := Scheme.Modules.pushforward p
  let B := Scheme.Modules.pushforward q
  let K := P.mapCochainComplexPlus.obj I.cochainComplexPlus
  letI : IsIso J.rightDerivedFunctorPlusUnit :=
    J.isIso_rightDerivedFunctorPlusUnit_of_preservesHomology
  exact (DerivedCategory.Plus.QCompιIso U.Modules).symm.app (J.mapCochainComplexPlus.obj K) ≪≫
    DerivedCategory.Plus.ι.mapIso
      (asIso (J.rightDerivedFunctorPlusUnit.app K) ≪≫
        J.rightDerivedFunctorPlus.mapIso (I.rightDerivedFunctorPlusIso P) ≪≫
        (Scheme.Modules.derivedOpenBaseChangeIso i q p j H).app
          ((DerivedCategory.Plus.singleFunctor X.Modules 0).obj M) ≪≫
        B.rightDerivedFunctorPlus.mapIso ((A.rightDerivedFunctorPlusSingleIso 0).app M))

variable [IsAffineHom j]

/-- Actual Hom transport across an affine open, with arbitrary source module and
quasicoherent target coefficient. Both source models are the native derived images. -/
@[no_expose] def relativeOpenPushforwardHomAddEquiv (M : X.Modules)
    (L : U.Modules) [L.IsQuasicoherent] (n r : ℕ) :
    (DerivedCategory.Plus.ι.obj ((Scheme.Modules.derivedPushforwardPlus q).obj
        ((DerivedCategory.Plus.singleFunctor W.Modules 0).obj (M.restrict i))) ⟶
      ((DerivedCategory.singleFunctor U.Modules (n : ℤ)).obj L)⟦(r : ℤ)⟧) ≃+
    (DerivedCategory.Plus.ι.obj ((Scheme.Modules.derivedPushforwardPlus p).obj
        ((DerivedCategory.Plus.singleFunctor X.Modules 0).obj M)) ⟶
      ((DerivedCategory.singleFunctor Y.Modules (n : ℤ)).obj
        ((Scheme.Modules.pushforward j).obj L))⟦(r : ℤ)⟧) := by
  let I := injectiveResolution M
  let K := ((Scheme.Modules.pushforward p).mapHomologicalComplex (.up ℤ)).obj I.cochainComplex
  let E := relativeOpenPushforwardResolutionIso i q p j H I
  let D := CategoryTheory.Adjunction.rightDerivedResolutionIso
    (G := Scheme.Modules.pushforward p) I
  exact (openCoefficientHomIsoAddEquiv E.symm
      (relativeOpenCoefficientShiftIso L (n : ℤ) (r : ℤ))).trans
    ((affineOpenCochainDerivedHomAddEquiv j L (injectiveResolution L) ((r : ℤ) - n) K).trans
      (openCoefficientHomIsoAddEquiv D
        (relativeOpenCoefficientShiftIso ((Scheme.Modules.pushforward j).obj L)
          (n : ℤ) (r : ℤ)).symm))

/-- The target transport is the actual pointwise restriction adjunct with its original
source-resolution comparison and both installed coefficient-shift comparisons. -/
theorem relativeOpenPushforwardHomAddEquiv_apply (M : X.Modules)
    (L : U.Modules) [L.IsQuasicoherent] (n r : ℕ)
    (a : DerivedCategory.Plus.ι.obj ((Scheme.Modules.derivedPushforwardPlus q).obj
        ((DerivedCategory.Plus.singleFunctor W.Modules 0).obj (M.restrict i))) ⟶
      ((DerivedCategory.singleFunctor U.Modules (n : ℤ)).obj L)⟦(r : ℤ)⟧) :
    relativeOpenPushforwardHomAddEquiv i q p j H M L n r a =
      (CategoryTheory.Adjunction.rightDerivedResolutionIso
        (G := Scheme.Modules.pushforward p) (injectiveResolution M)).inv ≫
      affineOpenCochainDerivedHomAddEquiv j L (injectiveResolution L) ((r : ℤ) - n)
        (((Scheme.Modules.pushforward p).mapHomologicalComplex (.up ℤ)).obj
          (injectiveResolution M).cochainComplex)
        ((relativeOpenPushforwardResolutionIso i q p j H (injectiveResolution M)).hom ≫
          a ≫ (relativeOpenCoefficientShiftIso L (n : ℤ) (r : ℤ)).hom) ≫
      (relativeOpenCoefficientShiftIso ((Scheme.Modules.pushforward j).obj L)
        (n : ℤ) (r : ℤ)).inv := by
  simp only [relativeOpenPushforwardHomAddEquiv, AddEquiv.trans_apply,
    openCoefficientHomIsoAddEquiv_apply, Iso.symm_inv, Iso.symm_hom]

end AlgebraicGeometry.Scheme.Cohomology
