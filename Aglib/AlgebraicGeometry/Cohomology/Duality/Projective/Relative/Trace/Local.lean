/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Mathlib.CategoryTheory.NatIso
public import Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.Relative.Trace.Pullback
public import Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.Relative.Trace.LocalCore
public import Aglib.AlgebraicGeometry.Cohomology.DirectImage.Affine.Cohomology
/-!
# Composition laws for the original local relative projective trace
The local comparison and trace compose over opaque coefficient and higher-image
functors. Their coefficient naturality and restriction refinement use the original
naturality, open-trace and restriction-composition equations.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules
universe u
attribute [local instance] AlgebraicGeometry.Scheme.Modules.standardHasDerivedCategory
namespace AlgebraicGeometry.Scheme.Cohomology.RelativeProjectiveTrace
/-- The affine trace sections equation using the canonical counit quasi-isomorphism. -/
def affineTraceSectionsEquation
    {R : Type u} [CommRing R] {X : Scheme.{u}}
    (p : X ⟶ Spec (.of R)) [QuasiCompact p] [QuasiSeparated p]
    (M : X.Modules) [M.IsQuasicoherent] (N : (Spec (.of R)).Modules) (n : ℕ)
    (t : ((Scheme.Modules.pushforward p).rightDerived n).obj M ⟶ N)
    (τ : Sheaf.H.{u + 1} (moduleAddSheaf X M) n → moduleSpecΓFunctor.obj N) : Prop := by
  letI := moduleResolutionPushforwardTildeCounit_quasiIso p (M)
    (injectiveResolution _)
  exact affineTraceSectionsEquationOfCounitQuasiIso p M N n t τ

/-- The model trace sections equation using the canonical counit quasi-isomorphism. -/
def traceModelSectionsEquation
    {A : Type u} [CommRing A] {P : Scheme.{u}}
    (r : P ⟶ Spec (.of A)) [QuasiCompact r] [QuasiSeparated r]
    (F : (Spec (.of A)).Modules ⥤ (Spec (.of A)).Modules)
    (U : (Spec (.of A)).Modules ⥤ P.Modules) (n : ℕ)
    (μ : F ≅ U ⋙ (Scheme.Modules.pushforward r).rightDerived n)
    (N : (Spec (.of A)).Modules) [(U.obj N).IsQuasicoherent]
    (τ : Sheaf.H.{u + 1} (moduleAddSheaf P (U.obj N)) n → moduleSpecΓFunctor.obj N)
    (z : F.obj N ⟶ N) : Prop := by
  letI := moduleResolutionPushforwardTildeCounit_quasiIso r (U.obj N)
    (injectiveResolution _)
  exact traceModelSectionsEquationOfCounitQuasiIso r F U n μ N τ z

theorem traceModelSections_of_standard
    {A : Type u} [CommRing A] {P : Scheme.{u}}
    (r : P ⟶ Spec (.of A)) [QuasiCompact r] [QuasiSeparated r]
    (F : (Spec (.of A)).Modules ⥤ (Spec (.of A)).Modules)
    (U : (Spec (.of A)).Modules ⥤ P.Modules) (n : ℕ)
    (μ : F ≅ U ⋙ (Scheme.Modules.pushforward r).rightDerived n)
    (N : (Spec (.of A)).Modules) [(U.obj N).IsQuasicoherent]
    (T : ((Scheme.Modules.pushforward r).rightDerived n).obj (U.obj N) ≅ N)
    (τ : Sheaf.H.{u + 1} (moduleAddSheaf P (U.obj N)) n → moduleSpecΓFunctor.obj N)
    (hT : affineTraceSectionsEquation r (U.obj N) N n T.hom τ) :
    traceModelSectionsEquation r F U n μ N τ
      (compositeTraceIso F U ((Scheme.Modules.pushforward r).rightDerived n) μ N T).hom := by
  let := moduleResolutionPushforwardTildeCounit_quasiIso r (U.obj N)
    (injectiveResolution _)
  exact traceModelSections_of_standard_of_counit_quasiIso r F U n μ N T τ hT

/-- The local trace sections equation using the canonical counit quasi-isomorphism. -/
def traceLocalSectionsEquation
    {A : Type u} [CommRing A] {P : Scheme.{u}}
    (r : P ⟶ Spec (.of A)) [QuasiCompact r] [QuasiSeparated r]
    {C E F : Type*} [Category* C] [Category* E] [Category* F]
    (F0 : C ⥤ E) (F1 : E ⥤ C) (J : C ⥤ (Spec (.of A)).Modules)
    (L : (Spec (.of A)).Modules ⥤ F) (V : F ⥤ (Spec (.of A)).Modules)
    (U : (Spec (.of A)).Modules ⥤ P.Modules)
    (η : (F0 ⋙ F1) ⋙ J ≅ J ⋙ (L ⋙ V)) (n : ℕ)
    (μ : L ⋙ V ≅ U ⋙ (Scheme.Modules.pushforward r).rightDerived n)
    (N : C) [((U.obj (J.obj N))).IsQuasicoherent]
    (τ : Sheaf.H.{u + 1} (moduleAddSheaf P (U.obj (J.obj N))) n →
      moduleSpecΓFunctor.obj (J.obj N))
    (z : J.obj (F1.obj (F0.obj N)) ⟶ J.obj N) : Prop := by
  letI := moduleResolutionPushforwardTildeCounit_quasiIso r (U.obj (J.obj N))
    (injectiveResolution _)
  exact traceLocalSectionsEquationOfCounitQuasiIso r F0 F1 J L V U η n μ N τ z

theorem traceLocalSections_of_model
    {A : Type u} [CommRing A] {P : Scheme.{u}}
    (r : P ⟶ Spec (.of A)) [QuasiCompact r] [QuasiSeparated r]
    {C E F : Type*} [Category* C] [Category* E] [Category* F]
    (F0 : C ⥤ E) (F1 : E ⥤ C) (J : C ⥤ (Spec (.of A)).Modules)
    (L : (Spec (.of A)).Modules ⥤ F) (V : F ⥤ (Spec (.of A)).Modules)
    (U : (Spec (.of A)).Modules ⥤ P.Modules)
    (η : (F0 ⋙ F1) ⋙ J ≅ J ⋙ (L ⋙ V)) (n : ℕ)
    (μ : L ⋙ V ≅ U ⋙ (Scheme.Modules.pushforward r).rightDerived n)
    (N : C) [((U.obj (J.obj N))).IsQuasicoherent]
    (t : V.obj (L.obj (J.obj N)) ⟶ J.obj N)
    (τ : Sheaf.H.{u + 1} (moduleAddSheaf P (U.obj (J.obj N))) n →
      moduleSpecΓFunctor.obj (J.obj N))
    (hT : traceModelSectionsEquation r (L ⋙ V) U n μ (J.obj N) τ t) :
    traceLocalSectionsEquation r F0 F1 J L V U η n μ N τ
      (traceLocalHomFactory F0 F1 J L V η N t) := by
  let := moduleResolutionPushforwardTildeCounit_quasiIso r (U.obj (J.obj N))
    (injectiveResolution _)
  exact traceLocalSections_of_model_of_counit_quasiIso r F0 F1 J L V U η n μ N t τ hT

end AlgebraicGeometry.Scheme.Cohomology.RelativeProjectiveTrace
