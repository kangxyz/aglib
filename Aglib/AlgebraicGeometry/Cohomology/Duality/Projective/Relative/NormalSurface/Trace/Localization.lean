/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.Relative.NormalSurface.Trace.Proper
public import Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.Relative.NormalSurface.CanonicalStalk
public import Aglib.AlgebraicGeometry.Cohomology.DirectImage.Stalk
public import Aglib.AlgebraicGeometry.Modules.Flat.Locality

/-!
# Localization of the actual ordinary canonical direct image

The degree-zero comparison uses the original right-derived-zero isomorphism,
flat local-spectrum base change and the original cohomology/sections map.
The local ring is not required to be finite over, or complete over, any base.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian AlgebraicGeometry
open AlgebraicGeometry.ProjectiveSpace AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Modules.QuasiCoherent Opposite

universe u

namespace AlgebraicGeometry.Scheme.Cohomology

attribute [local instance] ClosedImmersionAffineQuotientChart.isOpenImmersion

/-- Compose the original zero-degree, base-change and sections equivalences.
Keeping the constructor typed before specialization preserves all native actions. -/
def stalkSectionsLinearComposite
    {R : Type*} [CommRing R] {A B C D : Type*}
    [AddCommGroup A] [AddCommGroup B] [AddCommGroup C] [AddCommGroup D]
    [Module R A] [Module R B] [Module R C] [Module R D]
    (e₀ : A ≃ₗ[R] B) (e₁ : B ≃ₗ[R] C) (e₂ : C ≃ₗ[R] D) : A ≃ₗ[R] D :=
  e₀.trans (e₁.trans e₂)

/-- Evaluation of the same three original equivalences. -/
theorem stalkSectionsLinearComposite_apply
    {R : Type*} [CommRing R] {A B C D : Type*}
    [AddCommGroup A] [AddCommGroup B] [AddCommGroup C] [AddCommGroup D]
    [Module R A] [Module R B] [Module R C] [Module R D]
    (e₀ : A ≃ₗ[R] B) (e₁ : B ≃ₗ[R] C) (e₂ : C ≃ₗ[R] D) (x : A) :
    stalkSectionsLinearComposite e₀ e₁ e₂ x = e₂ (e₁ (e₀ x)) := rfl

/-- Evaluate the same composite using original endpoint normalization laws,
before specializing any carrier or scalar-action representation. -/
theorem stalkSectionsLinearComposite_apply_of_normalizations
    {R : Type*} [CommRing R] {A B C D : Type*}
    [AddCommGroup A] [AddCommGroup B] [AddCommGroup C] [AddCommGroup D]
    [Module R A] [Module R B] [Module R C] [Module R D]
    (e₀ : A ≃ₗ[R] B) (e₁ : B ≃ₗ[R] C) (e₂ : C ≃ₗ[R] D)
    (F : C → D) (x : A) (t : B) (h₀ : e₀ x = t)
    (h₂ : ∀ v, e₂ v = F v) :
    stalkSectionsLinearComposite e₀ e₁ e₂ x = F (e₁ t) := by
  rw [stalkSectionsLinearComposite_apply, h₀, h₂]

/-- The original degree-zero sections map with its native bundled target.
The scalar/carrier conversion is performed before any pullback specialization. -/
def moduleH0GlobalSectionsLinearEquivOfHom
    (Z : Scheme.{u}) {R : Type u} [CommRing R] (α : R →+* Γ(Z, ⊤)) (N : Z.Modules) :
    letI := moduleCohomologyModuleOfHom Z α N 0
    Sheaf.H.{u + 1} (moduleAddSheaf Z N) 0 ≃ₗ[R]
      (moduleGlobalSectionsFunctorOfHom Z α).obj N :=
  moduleH0EquivOfHom Z α N

/-- The bundled comparison has exactly the original degree-zero map. -/
theorem moduleH0GlobalSectionsLinearEquivOfHom_apply
    (Z : Scheme.{u}) {R : Type u} [CommRing R] (α : R →+* Γ(Z, ⊤)) (N : Z.Modules)
    (x : Sheaf.H.{u + 1} (moduleAddSheaf Z N) 0) :
    moduleH0GlobalSectionsLinearEquivOfHom Z α N x = moduleH0EquivOfHom Z α N x := rfl

/-- The actual ordinary direct-image stalk is the original sections over the
local-spectrum pullback, with its original local-ring action. -/
def ordinaryPushforwardStalkSectionsLinearEquiv
    {X Y : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f]
    (M : X.Modules) [M.IsQuasicoherent] (y : Y) :
    letI : HasPullback f (Y.fromSpecStalk y) :=
      AlgebraicGeometry.Scheme.Pullback.instHasPullback f (Y.fromSpecStalk y)
    let a := Limits.pullback.fst f (Y.fromSpecStalk y)
    let b := Limits.pullback.snd f (Y.fromSpecStalk y)
    let N := (Scheme.Modules.pullback a).obj M
    let α := b.appTop.hom.comp (Scheme.ΓSpecIso (Y.presheaf.stalk y)).inv.hom
    (moduleStalk Y y).obj ((pushforward f).obj M) ≃ₗ[Y.presheaf.stalk y]
      (moduleGlobalSectionsFunctorOfHom _ α).obj N := by
  let : HasPullback f (Y.fromSpecStalk y) :=
    AlgebraicGeometry.Scheme.Pullback.instHasPullback f (Y.fromSpecStalk y)
  let a := Limits.pullback.fst f (Y.fromSpecStalk y)
  let b := Limits.pullback.snd f (Y.fromSpecStalk y)
  let N := (Scheme.Modules.pullback a).obj M
  let α := b.appTop.hom.comp (Scheme.ΓSpecIso (Y.presheaf.stalk y)).inv.hom
  let := moduleCohomologyModuleOfHom _ α N 0
  let F := stalkSectionsLinearComposite
    ((moduleStalk Y y).mapIso
      ((pushforward f).rightDerivedZeroIsoSelf.app M).symm).toLinearEquiv
    (moduleHigherDirectImageStalkLinearEquiv f M y 0)
    (moduleH0GlobalSectionsLinearEquivOfHom _ α N)
  exact F



/-- The forward formula preserves the original degree-zero inclusion and the
actual higher-image flat base-change comparison, without substituting a finite
base model for the local ring. -/
theorem ordinaryPushforwardStalkSectionsLinearEquiv_apply
    {X Y : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f]
    (M : X.Modules) [M.IsQuasicoherent] (y : Y)
    (s : (moduleStalk Y y).obj ((pushforward f).obj M)) :
    letI : HasPullback f (Y.fromSpecStalk y) :=
      AlgebraicGeometry.Scheme.Pullback.instHasPullback f (Y.fromSpecStalk y)
    let a := Limits.pullback.fst f (Y.fromSpecStalk y)
    let b := Limits.pullback.snd f (Y.fromSpecStalk y)
    let N := (Scheme.Modules.pullback a).obj M
    let α := b.appTop.hom.comp (Scheme.ΓSpecIso (Y.presheaf.stalk y)).inv.hom
    let e₁ := moduleHigherDirectImageStalkLinearEquiv f M y 0
    let H₀ := moduleH0EquivOfHom _ α N
    let t := (moduleStalk Y y).map ((pushforward f).rightDerivedZeroIsoSelf.inv.app M) s
    ordinaryPushforwardStalkSectionsLinearEquiv f M y s = H₀ (e₁ t) := by
  intro a b N α e₁ H₀ t
  let := moduleCohomologyModuleOfHom _ α N 0
  let e₀ := ((moduleStalk Y y).mapIso
    ((pushforward f).rightDerivedZeroIsoSelf.app M).symm).toLinearEquiv
  let e₂ := moduleH0GlobalSectionsLinearEquivOfHom _ α N
  have h₀ : e₀ s = t := by
    simp only [e₀, t, CategoryTheory.Iso.toLinearEquiv_apply, Functor.mapIso_hom,
      Iso.symm_hom, Iso.app_inv]
  have h₂ : ∀ v, e₂ v = H₀ v :=
    fun v => moduleH0GlobalSectionsLinearEquivOfHom_apply _ α N v
  have hfull := stalkSectionsLinearComposite_apply_of_normalizations
    e₀ e₁ e₂ (fun v => H₀ v) s t h₀ h₂
  dsimp +instances only [ordinaryPushforwardStalkSectionsLinearEquiv, e₀, e₁, e₂, H₀, t, a, b, N, α]
    at hfull ⊢
  run_tac Lean.Elab.Tactic.withMainContext do
    let some decl := (← Lean.getLCtx).findFromUserName? `hfull
      | throwError "Missing existing original normalization proof"
    (← Lean.Elab.Tactic.getMainGoal).assign (Lean.mkFVar decl.fvarId)




/-- Transport an actual ordinary direct-image map to local sections. The input
is a sheaf map, not an assertion that its global sections are faithful. -/
def ordinaryPushforwardMapOnLocalSections
    {X Y : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f]
    (M : X.Modules) [M.IsQuasicoherent] (N : Y.Modules)
    (τ : (pushforward f).obj M ⟶ N) (y : Y) :
    let a := Limits.pullback.fst f (Y.fromSpecStalk y)
    let b := Limits.pullback.snd f (Y.fromSpecStalk y)
    let α := b.appTop.hom.comp (Scheme.ΓSpecIso (Y.presheaf.stalk y)).inv.hom
    (moduleGlobalSectionsFunctorOfHom _ α).obj ((Scheme.Modules.pullback a).obj M) →ₗ[
      Y.presheaf.stalk y] (moduleStalk Y y).obj N :=
  ((moduleStalk Y y).map τ).hom.comp
    (ordinaryPushforwardStalkSectionsLinearEquiv f M y).symm.toLinearMap

/-- The local-sections formula recovers exactly the original stalk map. -/
theorem ordinaryPushforwardMapOnLocalSections_normalization
    {X Y : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f]
    (M : X.Modules) [M.IsQuasicoherent] (N : Y.Modules)
    (τ : (pushforward f).obj M ⟶ N) (y : Y)
    (s : (moduleStalk Y y).obj ((pushforward f).obj M)) :
    ordinaryPushforwardMapOnLocalSections f M N τ y
        (ordinaryPushforwardStalkSectionsLinearEquiv f M y s) =
      (moduleStalk Y y).map τ s := by
  simp only [ordinaryPushforwardMapOnLocalSections, LinearMap.comp_apply,
    LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]

/-- If the actual trace is invertible, its localized form is invertible as well.
This does not assert that a proper canonical trace is always invertible. -/
def ordinaryPushforwardIsoOnLocalSections
    {X Y : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f]
    (M : X.Modules) [M.IsQuasicoherent] (N : Y.Modules)
    (τ : (pushforward f).obj M ⟶ N) [IsIso τ] (y : Y) :
    let a := Limits.pullback.fst f (Y.fromSpecStalk y)
    let b := Limits.pullback.snd f (Y.fromSpecStalk y)
    let α := b.appTop.hom.comp (Scheme.ΓSpecIso (Y.presheaf.stalk y)).inv.hom
    (moduleGlobalSectionsFunctorOfHom _ α).obj ((Scheme.Modules.pullback a).obj M) ≃ₗ[
      Y.presheaf.stalk y] (moduleStalk Y y).obj N :=
  (ordinaryPushforwardStalkSectionsLinearEquiv f M y).symm.trans
    ((moduleStalk Y y).mapIso (asIso τ)).toLinearEquiv

end AlgebraicGeometry.Scheme.Cohomology
