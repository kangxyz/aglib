/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Projective.FiniteModel.Resolution
public import Aglib.AlgebraicGeometry.Cohomology.DirectImage.ResolutionSections.Pushforward.Spec
public import Aglib.AlgebraicGeometry.Modules.Perfect.Affine.Model

/-!
# The actual strict sheaf model map to original direct-image resolution

The native tilde of the original finite-projective model is strict perfect.
Its actual map to the original pushed injective resolution is the tilde of
the original resolution-section comparison, the inverse original spectrum
section comparison, and the original affine tilde/sections counit. Exactness
of tilde preserves the first quasi-isomorphism; the separate geometric
counit theorem is the remaining input to identify the actual direct image.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open HomologicalComplex

namespace AlgebraicGeometry.Scheme.Cohomology.ProjectiveCohomologyModel

variable {R : CommRingCat.{u}} {ι : Type u} {X : Scheme.{u}}
  {i : X ⟶ ProjectiveSpace R ι}
  {f : X ⟶ Spec R} {M : X.Modules} {n : ℕ}
  (D : ProjectiveCohomologyModel R ι i f M n)

/-- The actual native tilde complex of the same projective model, packed
in the existing strict-perfect full subcategory with the same term bounds. -/
def strictSheafModel : Scheme.Modules.Complex.StrictPerfect (Spec R) := by
  let := D.lowerBound
  let := D.upperBound
  let (j : ℤ) : Module.Finite R (D.complex.X j) := D.finite_X j
  let (j : ℤ) : Module.Projective R (D.complex.X j) := D.projective_X j
  exact ⟨((tilde.functor R).mapHomologicalComplex (.up ℤ)).obj D.complex,
    Scheme.Modules.Complex.strictPerfect_tilde_of_finite_projective
      R D.complex 0 (n : ℤ)⟩

/-- The same strict sheaf complex with its native bounded-below packing. -/
def strictSheafModelPlus : CochainComplex.Plus (Spec R).Modules :=
  (tilde.functor R).mapCochainComplexPlus.obj D.toPlus

/-- The native bounded-below packing and strict-perfect packing have the
literal same underlying original sheaf complex. -/
theorem strictSheafModelPlus_obj : D.strictSheafModelPlus.obj = D.strictSheafModel.obj := rfl

variable [IsClosedImmersion i] [M.IsQuasicoherent]

/-- The actual strict-model chain map to the original pushed injective
resolution: native tilde of the normalized original section comparison,
then the original affine adjunction counit. -/
def sheafComparison (e : ι ≃ Fin (n + 1)) (I : InjectiveResolution M) :
    D.strictSheafModel.obj ⟶
      (((Scheme.Modules.pushforward f).mapCochainComplexPlus.obj I.cochainComplexPlus).obj) :=
  Scheme.Modules.Complex.tildeModelMap R D.complex
    (((Scheme.Modules.pushforward f).mapCochainComplexPlus.obj I.cochainComplexPlus).obj)
    (D.resolutionSectionsComparison e I ≫
      (moduleSpecPushforwardGlobalSectionsComplexIso f (.up ℤ) I.cochainComplexPlus.obj).inv)

/-- Each original component is the same tilde map followed by the literal
original `fromTildeΓ` counit on the original direct-image term. -/
theorem sheafComparison_f (e : ι ≃ Fin (n + 1)) (I : InjectiveResolution M) (j : ℤ) :
    (D.sheafComparison e I).f j =
      tilde.map ((D.resolutionSectionsComparison e I ≫
        (moduleSpecPushforwardGlobalSectionsComplexIso f (.up ℤ)
          I.cochainComplexPlus.obj).inv).f j) ≫
      Scheme.Modules.fromTildeΓ
        ((((Scheme.Modules.pushforward f).mapCochainComplexPlus.obj
          I.cochainComplexPlus).obj).X j) := by
  exact Scheme.Modules.Complex.tildeModelMap_f R D.complex
    (((Scheme.Modules.pushforward f).mapCochainComplexPlus.obj I.cochainComplexPlus).obj) _ j

/-- The actual strict-model arrow is a quasi-isomorphism as soon as the
original affine counit on this original pushed resolution is one. This is a
composition criterion; the geometric supplier must prove that counit fact. -/
theorem sheafComparison_quasiIso_of_counit (e : ι ≃ Fin (n + 1)) (I : InjectiveResolution M)
    (hcounit : QuasiIso (Scheme.Modules.Complex.tildeGlobalSectionsCounit R (.up ℤ)
      (((Scheme.Modules.pushforward f).mapCochainComplexPlus.obj I.cochainComplexPlus).obj))) :
    QuasiIso (D.sheafComparison e I) := by
  let : QuasiIso (D.resolutionSectionsComparison e I) :=
    D.resolutionSectionsComparison_quasiIso e I
  let := hcounit
  exact Scheme.Modules.Complex.tildeModelMap_quasiIso R D.complex
    (((Scheme.Modules.pushforward f).mapCochainComplexPlus.obj I.cochainComplexPlus).obj)
    (D.resolutionSectionsComparison e I ≫
      (moduleSpecPushforwardGlobalSectionsComplexIso f (.up ℤ) I.cochainComplexPlus.obj).inv)

/-- The same actual sheaf comparison in the native bounded-below category. -/
def sheafComparisonPlus (e : ι ≃ Fin (n + 1)) (I : InjectiveResolution M) :
    D.strictSheafModelPlus ⟶
      (Scheme.Modules.pushforward f).mapCochainComplexPlus.obj I.cochainComplexPlus :=
  Scheme.Modules.Complex.tildeModelMapPlus R D.toPlus
    ((Scheme.Modules.pushforward f).mapCochainComplexPlus.obj I.cochainComplexPlus)
    (D.resolutionSectionsComparison e I ≫
      (moduleSpecPushforwardGlobalSectionsComplexIso f (.up ℤ) I.cochainComplexPlus.obj).inv)

local instance sheafModelDerivedSource : HasDerivedCategory.{u + 1} X.Modules :=
  HasDerivedCategory.standard _

local instance sheafModelDerivedTarget : HasDerivedCategory.{u + 1} (Spec R).Modules :=
  HasDerivedCategory.standard _

include D in
/-- The actual pushed resolution has a global strict model when its
original affine counit is a quasi-isomorphism. This retains an actual
native derived-object witness, rather than just homology isomorphisms. -/
theorem hasStrictSheafModel_of_counit (e : ι ≃ Fin (n + 1)) (I : InjectiveResolution M)
    (hcounit : QuasiIso (Scheme.Modules.Complex.tildeGlobalSectionsCounit R (.up ℤ)
      (((Scheme.Modules.pushforward f).mapCochainComplexPlus.obj I.cochainComplexPlus).obj))) :
    Scheme.Modules.Complex.HasStrictModel
      (((Scheme.Modules.pushforward f).mapCochainComplexPlus.obj I.cochainComplexPlus).obj) := by
  let := D.lowerBound
  let := D.upperBound
  let (j : ℤ) : Module.Finite R (D.complex.X j) := D.finite_X j
  let (j : ℤ) : Module.Projective R (D.complex.X j) := D.projective_X j
  let : QuasiIso (D.resolutionSectionsComparison e I) :=
    D.resolutionSectionsComparison_quasiIso e I
  let := hcounit
  exact Scheme.Modules.Complex.hasStrictModel_of_tildeModelMap R D.complex
    (((Scheme.Modules.pushforward f).mapCochainComplexPlus.obj I.cochainComplexPlus).obj)
    (D.resolutionSectionsComparison e I ≫
      (moduleSpecPushforwardGlobalSectionsComplexIso f (.up ℤ) I.cochainComplexPlus.obj).inv)
    0 (n : ℤ)

/-- Once the geometric counit has been proved a quasi-isomorphism, the
same strict sheaf complex represents the installed original derived
pushforward of the coefficient in degree zero. -/
def derivedPushforwardIso_of_counit (e : ι ≃ Fin (n + 1)) (I : InjectiveResolution M)
    (hcounit : QuasiIso (Scheme.Modules.Complex.tildeGlobalSectionsCounit R (.up ℤ)
      (((Scheme.Modules.pushforward f).mapCochainComplexPlus.obj I.cochainComplexPlus).obj))) :
    DerivedCategory.Plus.Q.obj D.strictSheafModelPlus ≅
      (Scheme.Modules.pushforward f).rightDerivedFunctorPlus.obj
        ((DerivedCategory.Plus.singleFunctor X.Modules 0).obj M) := by
  let : QuasiIso (D.resolutionSectionsComparison e I) :=
    D.resolutionSectionsComparison_quasiIso e I
  let := hcounit
  exact Scheme.Modules.Complex.tildeModelDerivedIsoPlus R D.toPlus
      ((Scheme.Modules.pushforward f).mapCochainComplexPlus.obj I.cochainComplexPlus)
      (D.resolutionSectionsComparison e I ≫
        (moduleSpecPushforwardGlobalSectionsComplexIso f (.up ℤ) I.cochainComplexPlus.obj).inv) ≪≫
    InjectiveResolution.rightDerivedFunctorPlusIso (Scheme.Modules.pushforward f) I

/-- The native derived-pushforward comparison keeps the literal original
strict-model arrow and the installed injective-resolution derived unit. -/
theorem derivedPushforwardIso_of_counit_hom (e : ι ≃ Fin (n + 1)) (I : InjectiveResolution M)
    (hcounit : QuasiIso (Scheme.Modules.Complex.tildeGlobalSectionsCounit R (.up ℤ)
      (((Scheme.Modules.pushforward f).mapCochainComplexPlus.obj I.cochainComplexPlus).obj))) :
    (D.derivedPushforwardIso_of_counit e I hcounit).hom =
      DerivedCategory.Plus.Q.map (D.sheafComparisonPlus e I) ≫
        (InjectiveResolution.rightDerivedFunctorPlusIso (Scheme.Modules.pushforward f) I).hom := rfl

end AlgebraicGeometry.Scheme.Cohomology.ProjectiveCohomologyModel
