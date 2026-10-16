/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Complex.Basic
public import Aglib.AlgebraicGeometry.Modules.Flat.Generators
public import Aglib.Algebra.Homology.DerivedCategory.Minus.Localization
public import Aglib.AlgebraicGeometry.Modules.DerivedCategory.Minus.ResolvedPullback


/-!
# Actual arbitrary pullback on bounded-above derived categories

The genuine ambient bounded-complex localization theorem descends the
geometric flat-model functor to `DerivedCategory.Minus`. This file retains its
factorization, actual flat-model object formula, agreement on flat inputs, and
natural identity comparison. No flat-map, quasicoherence, replacement-existence,
or derived-equivalence hypothesis is assumed.
-/
/-!
Source: frozen dirty Quillen `6db56ddd3fdb898ef5de29d5fe51a0c61f9ba116`.
`Quillen/AlgebraicGeometry/Scheme/Sheaf/DerivedMinusPullback.lean`.
SHA-256: `e27e730708ae9cc095f87dcc8f9432593f884cb5ad417c53e3c6aab3487e014d`.
Selected source lines: 1–103.
Actual source objects, maps, hypotheses and independent universes are preserved.
-/

@[expose] public section

open CochainComplex


open AlgebraicGeometry.Scheme.Modules

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u w₁ w₂
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry HomologicalComplex
namespace AlgebraicGeometry.Scheme.Modules

variable {X Y : Scheme.{u}} (f : X ⟶ Y)
    [HasDerivedCategory.{w₁} Y.Modules] [HasDerivedCategory.{w₂} X.Modules]

omit [HasDerivedCategory.{w₁} Y.Modules] in
/-- The actual resolved functor into the ambient bounded-above derived category
inverts every original sheaf quasi-isomorphism. -/
theorem resolvedPullbackFunctorMinus_inverts :
    (boundedAboveQuasiIso Y.Modules).IsInvertedBy (resolvedPullbackFunctorMinus f) := by
  intro K L s hs
  let : QuasiIso s.hom := hs
  have : IsIso ((DerivedCategory.Minus.ι : DerivedCategory.Minus X.Modules ⥤ _).map
      ((resolvedPullbackFunctorMinus f).map s)) := resolvedPullbackFunctor_inverts f s
  exact isIso_of_reflects_iso _ (DerivedCategory.Minus.ι : DerivedCategory.Minus X.Modules ⥤ _)

/-- Actual arbitrary derived pullback on mathlib's bounded-above derived categories.
Its construction uses the proved ambient localization theorem and genuine flat replacements. -/
def derivedPullbackMinus : DerivedCategory.Minus Y.Modules ⥤ DerivedCategory.Minus X.Modules :=
  Localization.lift (resolvedPullbackFunctorMinus f) (resolvedPullbackFunctorMinus_inverts f)
    (boundedAboveQMinus Y.Modules)

/-- The derived functor retains the actual geometric flat-resolution formula. -/
def derivedPullbackMinusFactors :
    boundedAboveQMinus Y.Modules ⋙ derivedPullbackMinus f ≅ resolvedPullbackFunctorMinus f :=
  Localization.fac _ _ _

instance instLiftingDerivedPullbackMinus :
    Localization.Lifting (boundedAboveQMinus Y.Modules) (boundedAboveQuasiIso Y.Modules)
      (resolvedPullbackFunctorMinus f) (derivedPullbackMinus f) :=
  ⟨derivedPullbackMinusFactors f⟩

/-- Every actual bounded-above representative has the computed derived pullback object. -/
def derivedPullbackMinusObjectIso (K : BoundedAboveComplex Y.Modules) :
    ((derivedPullbackMinus f).obj ((boundedAboveQMinus Y.Modules).obj K)).obj ≅
      DerivedCategory.Q.obj ((AlgebraicGeometry.Scheme.Modules.Complex.pullback f).obj (flatModel Y
        K)) :=
  (DerivedCategory.Minus.ι).mapIso ((derivedPullbackMinusFactors f).app K) ≪≫
    resolvedPullbackObjectIso f K

/-- On genuinely flat bounded-above inputs the actual derived functor agrees with termwise pullback.
-/
def derivedPullbackMinusFlatObjectIso (K : BoundedAboveComplex Y.Modules)
    (hK : ∀ n, stalkwiseFlat Y (K.obj.X n)) :
    ((derivedPullbackMinus f).obj ((boundedAboveQMinus Y.Modules).obj K)).obj ≅
      DerivedCategory.Q.obj ((AlgebraicGeometry.Scheme.Modules.Complex.pullback f).obj K.obj) :=
  (DerivedCategory.Minus.ι).mapIso ((derivedPullbackMinusFactors f).app K) ≪≫
    resolvedPullbackFlatObjectIso f K hK

variable (X)

/-- The identity comparison is inherited from the actual augmentation, inside the ambient
  subcategory. -/
def resolvedPullbackMinusIdIso [HasDerivedCategory.{w₁} X.Modules] :
    resolvedPullbackFunctorMinus (𝟙 X) ≅ boundedAboveQMinus X.Modules :=
  NatIso.ofComponents (fun K => ObjectProperty.isoMk _ ((resolvedPullbackIdIso X).app K))
    (fun s => ObjectProperty.hom_ext _ ((resolvedPullbackIdIso X).hom.naturality s))

/-- Arbitrary derived pullback along the identity is naturally the actual identity functor. -/
def derivedPullbackMinusIdIso [HasDerivedCategory.{w₁} X.Modules] :
    derivedPullbackMinus (𝟙 X) ≅ 𝟭 (DerivedCategory.Minus X.Modules) :=
  Localization.liftNatIso (boundedAboveQMinus X.Modules) (boundedAboveQuasiIso X.Modules)
    (resolvedPullbackFunctorMinus (𝟙 X)) (boundedAboveQMinus X.Modules)
    (derivedPullbackMinus (𝟙 X)) (𝟭 _) (resolvedPullbackMinusIdIso X)

end AlgebraicGeometry.Scheme.Modules
