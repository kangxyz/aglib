/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Modules.Scalars
public import Aglib.AlgebraicGeometry.Cohomology.Functoriality.DegreeZero

/-!
# Geometric cohomology maps for arbitrary module coefficients

An actual coefficient arrow `M ⟶ f_* N` gives a map on the unchanged additive
`Sheaf.H`. It is constructed through exact additive inverse image and the
original coefficient adjunction. Structural ring maps make it linear, and its
degree-zero value is the actual adjoint map on global sections. The geometric
module-pullback map specializes the coefficient arrow to the original unit.

No flatness, quasicoherence, properness or finite-generation premise is needed
to construct these maps.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite

namespace AlgebraicGeometry.Scheme.Cohomology

universe u

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- Forgetting module scalars commutes with the actual geometric direct image. -/
def modulePushforwardAddSheafIso (N : X.Modules) :
    moduleAddSheaf Y ((Scheme.Modules.pushforward f).obj N) ≅
      (zariskiPushforward f).obj (moduleAddSheaf X N) := Iso.refl _

/-- The additive inverse-image coefficient map adjoint to an actual module coefficient arrow. -/
def moduleCoefficientPullback {M : Y.Modules} {N : X.Modules}
    (φ : M ⟶ (Scheme.Modules.pushforward f).obj N) :
    (zariskiPullback f).obj (moduleAddSheaf Y M) ⟶ moduleAddSheaf X N :=
  ((TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} f.base).homEquiv _ _).symm
    ((SheafOfModules.toSheaf Y.ringCatSheaf).map φ ≫
      (modulePushforwardAddSheafIso f N).hom)

/-- The actual geometric map on module-sheaf cohomology, with its displayed coefficient arrow. -/
def moduleCohomologyMapAlong {M : Y.Modules} {N : X.Modules}
    (φ : M ⟶ (Scheme.Modules.pushforward f).obj N) (n : ℕ) :
    Sheaf.H.{u + 1} (moduleAddSheaf Y M) n →+
      Sheaf.H.{u + 1} (moduleAddSheaf X N) n :=
  zariskiCohomologyMap f _ _ (moduleCoefficientPullback f φ) n

theorem app_globalRestriction (U : Y.Opens) (a : Γ(Y, ⊤)) :
    f.app U (globalRestriction Y U a) =
      globalRestriction X (f ⁻¹ᵁ U) (f.appTop a) := by
  have h := congrArg
    (fun q : Γ(Y, ⊤) ⟶ Γ(X, f ⁻¹ᵁ U) ↦ q.hom a)
    (f.naturality (homOfLE (show U ≤ ⊤ from le_top)).op)
  change f.app U (globalRestriction Y U a) =
    X.presheaf.map _ (f.appTop a) at h
  exact h

theorem moduleCoefficientPullback_scalar {M : Y.Modules} {N : X.Modules}
    (φ : M ⟶ (Scheme.Modules.pushforward f).obj N) (a : Γ(Y, ⊤)) :
    (zariskiPullback f).map (moduleScalarOfGlobal Y M a) ≫ moduleCoefficientPullback f φ =
      moduleCoefficientPullback f φ ≫ moduleScalarOfGlobal X N (f.appTop a) := by
  have h : moduleScalarOfGlobal Y M a ≫
        ((SheafOfModules.toSheaf Y.ringCatSheaf).map φ ≫
          (modulePushforwardAddSheafIso f N).hom) =
      ((SheafOfModules.toSheaf Y.ringCatSheaf).map φ ≫
          (modulePushforwardAddSheafIso f N).hom) ≫
        (zariskiPushforward f).map (moduleScalarOfGlobal X N (f.appTop a)) := by
    ext U x
    change M.val.obj U at x
    change (φ.val.app U).hom (globalRestriction Y U.unop a • x) =
      globalRestriction X (f ⁻¹ᵁ U.unop) (f.appTop a) •
        (show Γ(N, f ⁻¹ᵁ U.unop) from (φ.val.app U).hom x)
    rw [(φ.val.app U).hom.map_smul]
    change f.app U.unop (globalRestriction Y U.unop a) •
      (show Γ(N, f ⁻¹ᵁ U.unop) from (φ.val.app U).hom x) = _
    rw [app_globalRestriction]
  have h' := congrArg
    (((TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} f.base).homEquiv _ _).symm)
    h
  rw [Adjunction.homEquiv_naturality_right_symm,
    Adjunction.homEquiv_naturality_left_symm] at h'
  exact h'

/-- The geometric map is linear for any structural ring, with the induced target action. -/
def moduleCohomologyMapAlongLinear {R : Type u} [CommRing R]
    (α : R →+* Γ(Y, ⊤)) {M : Y.Modules} {N : X.Modules}
    (φ : M ⟶ (Scheme.Modules.pushforward f).obj N) (n : ℕ) :
    letI := moduleCohomologyModuleOfHom Y α M n
    letI := moduleCohomologyModuleOfHom X (f.appTop.hom.comp α) N n
    Sheaf.H.{u + 1} (moduleAddSheaf Y M) n →ₗ[R]
      Sheaf.H.{u + 1} (moduleAddSheaf X N) n := by
  letI := moduleCohomologyModuleOfHom Y α M n
  letI := moduleCohomologyModuleOfHom X (f.appTop.hom.comp α) N n
  exact {
    __ := moduleCohomologyMapAlong f φ n
    map_smul' := fun a x ↦
      zariskiCohomologyMap_naturality f _ _ (moduleCoefficientPullback f φ)
        (moduleScalarOfGlobal Y M (α a))
        (moduleScalarOfGlobal X N (f.appTop (α a)))
        (moduleCoefficientPullback_scalar f φ (α a)) n x }

/-- Degree zero is the original coefficient map followed by the direct-image section comparison. -/
theorem moduleCohomologyMapAlong_equiv₀ {M : Y.Modules} {N : X.Modules}
    (φ : M ⟶ (Scheme.Modules.pushforward f).obj N)
    (x : Sheaf.H.{u + 1} (moduleAddSheaf Y M) 0) :
    Sheaf.H.equiv₀ (moduleAddSheaf X N) isTerminalTop (moduleCohomologyMapAlong f φ 0 x) =
      (pushforwardSectionsIso f).hom.app (moduleAddSheaf X N)
        ((((SheafOfModules.toSheaf Y.ringCatSheaf).map φ ≫
          (modulePushforwardAddSheafIso f N).hom).hom.app (op ⊤))
          (Sheaf.H.equiv₀ (moduleAddSheaf Y M) isTerminalTop x)) := by
  rw [moduleCohomologyMapAlong, zariskiCohomologyMap_equiv₀]
  simp only [moduleCoefficientPullback, Equiv.apply_symm_apply]

/-- Geometric pullback on actual cohomology uses the original module adjunction unit. -/
def moduleCohomologyPullback (M : Y.Modules) (n : ℕ) :
    Sheaf.H.{u + 1} (moduleAddSheaf Y M) n →+
      Sheaf.H.{u + 1} (moduleAddSheaf X ((Scheme.Modules.pullback f).obj M)) n :=
  moduleCohomologyMapAlong f ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M) n

end AlgebraicGeometry.Scheme.Cohomology
