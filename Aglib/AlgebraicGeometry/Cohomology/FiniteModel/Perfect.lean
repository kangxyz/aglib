/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.FiniteModel.Derived
public import Aglib.AlgebraicGeometry.Cohomology.DirectImage.Affine.DerivedModel
public import Aglib.AlgebraicGeometry.Modules.Perfect.Affine
public import Aglib.Algebra.Category.ModuleCat.ChangeOfRings.Finiteness

/-!
# Strict perfect direct images from the same actual finite-cover model

Native tilde of the original finite-projective complex is strict perfect.
Exact-tilde derived transport identifies it with installed derived direct
image. After every ring map the same construction applies to the literal
scalar extension of that same complex, and the coefficient is the original
ordinary pullback. The new ring needs no Noetherianity or flatness.

The object comparisons use the original exact-tilde derived units and the
proved original counit. No additional chain representative is selected.
Equality with an independently chosen chain-normalized comparison, and any
same-map claim depending on that equality, remain separate obligations.
Relative base flatness does not identify ordinary and derived coefficient
pullback for a nonflat ambient morphism.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry HomologicalComplex

namespace AlgebraicGeometry.Scheme.Cohomology.FiniteCechCohomologyModel

variable {R : CommRingCat.{u}} {ι : Type u} {X : Scheme.{u}}
  {f : X ⟶ Spec R} {U : ι → X.Opens} {M : X.Modules} {n : ℕ}
  (D : FiniteCechCohomologyModel R ι X f U M n)

/-- Native tilde of the same actual finite-projective complex, with its original
bounded-below packing. -/
def sheafModelPlus : CochainComplex.Plus (Spec R).Modules :=
  (tilde.functor R).mapCochainComplexPlus.obj D.toPlus

/-- The underlying complex is the literal native tilde of the same original model. -/
theorem sheafModelPlus_obj : D.sheafModelPlus.obj =
    ((tilde.functor R).mapHomologicalComplex (.up ℤ)).obj D.complex := rfl

/-- Native tilde preserves the original lower term bound. -/
theorem sheafModelPlus_lowerBound : D.sheafModelPlus.obj.IsStrictlyGE 0 := by
  let := D.lowerBound
  change CochainComplex.IsStrictlyGE
    (((tilde.functor R).mapHomologicalComplex (.up ℤ)).obj D.complex) 0
  infer_instance

/-- Native tilde preserves the original upper term bound. -/
theorem sheafModelPlus_upperBound : D.sheafModelPlus.obj.IsStrictlyLE (n : ℤ) := by
  let := D.upperBound
  change CochainComplex.IsStrictlyLE
    (((tilde.functor R).mapHomologicalComplex (.up ℤ)).obj D.complex) (n : ℤ)
  infer_instance

/-- The original finite-projective terms give native strict perfectness with the same
term bounds. No cohomological finiteness inference over a new ring is needed. -/
theorem sheafModelPlus_strictPerfect :
    Scheme.Modules.Complex.strictPerfect (Spec R) D.sheafModelPlus.obj := by
  let := D.lowerBound
  let := D.upperBound
  let (j : ℤ) : Module.Finite R (D.complex.X j) := D.finite_X j
  let (j : ℤ) : Module.Projective R (D.complex.X j) := D.projective_X j
  exact Scheme.Modules.Complex.strictPerfect_tilde_of_finite_projective
    R D.complex 0 (n : ℤ)

variable {S : CommRingCat.{u}} (σ : R →+* S)

/-- Native tilde of the literal scalar extension of the same original model. -/
def baseChangeSheafModelPlus : CochainComplex.Plus (Spec S).Modules :=
  (tilde.functor S).mapCochainComplexPlus.obj (D.baseChangePlus σ)

local instance changedModelLower : (D.baseChangePlus σ).obj.IsStrictlyGE 0 := by
  let := D.lowerBound
  change CochainComplex.IsStrictlyGE
    (((ModuleCat.extendScalars σ).mapHomologicalComplex (.up ℤ)).obj D.complex) 0
  infer_instance

local instance changedModelUpper : (D.baseChangePlus σ).obj.IsStrictlyLE (n : ℤ) := by
  let := D.upperBound
  change CochainComplex.IsStrictlyLE
    (((ModuleCat.extendScalars σ).mapHomologicalComplex (.up ℤ)).obj D.complex) (n : ℤ)
  infer_instance

local instance changedModelFinite (j : ℤ) : Module.Finite S ((D.baseChangePlus σ).obj.X j) := by
  let : Module.Finite R (D.complex.X j) := D.finite_X j
  change Module.Finite S ((ModuleCat.extendScalars σ).obj (D.complex.X j))
  exact ModuleCat.finite_extendScalars σ (D.complex.X j)

local instance changedModelProjective (j : ℤ) :
    Module.Projective S ((D.baseChangePlus σ).obj.X j) := by
  let : Module.Projective R (D.complex.X j) := D.projective_X j
  change Module.Projective S ((ModuleCat.extendScalars σ).obj (D.complex.X j))
  exact ModuleCat.projective_extendScalars σ (D.complex.X j)

/-- The same scalar-extended model retains its original lower term bound after tilde. -/
theorem baseChangeSheafModelPlus_lowerBound :
    (D.baseChangeSheafModelPlus σ).obj.IsStrictlyGE 0 := by
  change CochainComplex.IsStrictlyGE
    (((tilde.functor S).mapHomologicalComplex (.up ℤ)).obj (D.baseChangePlus σ).obj) 0
  infer_instance

/-- The same scalar-extended model retains its original upper term bound after tilde. -/
theorem baseChangeSheafModelPlus_upperBound :
    (D.baseChangeSheafModelPlus σ).obj.IsStrictlyLE (n : ℤ) := by
  change CochainComplex.IsStrictlyLE
    (((tilde.functor S).mapHomologicalComplex (.up ℤ)).obj (D.baseChangePlus σ).obj) (n : ℤ)
  infer_instance

/-- The literal scalar extension of the original finite-projective model is strict perfect
over every new ring, including nonflat and non-Noetherian base changes. -/
theorem baseChangeSheafModelPlus_strictPerfect :
    Scheme.Modules.Complex.strictPerfect (Spec S) (D.baseChangeSheafModelPlus σ).obj :=
  Scheme.Modules.Complex.strictPerfect_tilde_of_finite_projective
    S (D.baseChangePlus σ).obj 0 (n : ℤ)

local instance perfectModelDerived (Z : Scheme.{u}) : HasDerivedCategory.{u + 1} Z.Modules :=
  HasDerivedCategory.standard _

local instance perfectModelDerivedModules (A : CommRingCat.{u}) :
    HasDerivedCategory.{u + 1} (ModuleCat.{u} A) := HasDerivedCategory.standard _

variable [X.IsSeparated] [M.IsQuasicoherent] [QuasiCompact f] [QuasiSeparated f]
  (hU : ∀ j, IsAffineOpen (U j)) (hcover : iSup U = ⊤)

/-- Exact-tilde derived transport of the original finite-cover comparison represents the
installed native direct image of the original coefficient. -/
def derivedPushforwardObjectIso (e : ι ≃ Fin (n + 1)) (I : InjectiveResolution M) :
    DerivedCategory.Plus.Q.obj D.sheafModelPlus ≅
      (Scheme.Modules.pushforward f).rightDerivedFunctorPlus.obj
        ((DerivedCategory.Plus.singleFunctor X.Modules 0).obj M) :=
  moduleSpecDerivedPushforwardModelIso f I D.toPlus
    (D.derivedGlobalSectionsIso hU hcover e I)

/-- The direct-image object comparison is the sole native exact-tilde transport of the
same original global-sections comparison. -/
theorem derivedPushforwardObjectIso_eq (e : ι ≃ Fin (n + 1)) (I : InjectiveResolution M) :
    D.derivedPushforwardObjectIso hU hcover e I =
      moduleSpecDerivedPushforwardModelIso f I D.toPlus
        (D.derivedGlobalSectionsIso hU hcover e I) := rfl

/-- The literal scalar extension of the same source model represents installed direct image
of the ordinary pulled coefficient after every ring map. -/
def baseChangeDerivedPushforwardObjectIso (e : ι ≃ Fin (n + 1))
    (hflat : Scheme.Modules.relativeFlat f M)
    (I : InjectiveResolution
      ((Scheme.Modules.pullback (pullback.fst f (Spec.map (CommRingCat.ofHom σ)))).obj M)) :
    let Y := pullback f (Spec.map (CommRingCat.ofHom σ))
    let p := pullback.fst f (Spec.map (CommRingCat.ofHom σ))
    let r := pullback.snd f (Spec.map (CommRingCat.ofHom σ))
    DerivedCategory.Plus.Q.obj (D.baseChangeSheafModelPlus σ) ≅
      (Scheme.Modules.pushforward r).rightDerivedFunctorPlus.obj
        ((DerivedCategory.Plus.singleFunctor Y.Modules 0).obj
          ((Scheme.Modules.pullback p).obj M)) := by
  let p := pullback.fst f (Spec.map (CommRingCat.ofHom σ))
  let N := (Scheme.Modules.pullback p).obj M
  let : N.IsQuasicoherent := Scheme.Modules.quasicoherent_pullback p M
  exact moduleSpecDerivedPushforwardModelIso
    (pullback.snd f (Spec.map (CommRingCat.ofHom σ))) I (D.baseChangePlus σ)
    (D.baseChangeDerivedGlobalSectionsIso hU hcover σ e hflat I)

end AlgebraicGeometry.Scheme.Cohomology.FiniteCechCohomologyModel
