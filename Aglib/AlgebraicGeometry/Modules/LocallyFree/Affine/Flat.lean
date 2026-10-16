/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Affine.Chart
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Affine.Pullback
public import Aglib.AlgebraicGeometry.Modules.LocallyFree.FreeCover
public import Aglib.Algebra.Category.ModuleCat.BaseChange
public import Aglib.RingTheory.Flat.LocalBasis

/-!
# Affine flat finitely presented modules

Actual affine module sheaves with finitely presented flat section modules
have finite local bases. The localization and free-presentation comparisons
use the existing canonical tilde pullback and basis objects.

Source: `R5Lab/AlgebraicGeometry/Curves/Degree/FiniteFlatLocallyFree.lean`, frozen R5 integration
`79307ff88f07d34fd5c3edb859f799c55e38f290`, SHA-256
`d3dc4d7ca161eb1493165b50730ef4e573da5882fd475b4d4d520c066d42a7fb`. Selected original ranges: [[184,
244]].
-/

@[expose] public section
noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option linter.style.haveILetI false

open CategoryTheory Limits AlgebraicGeometry Opposite Module TopologicalSpace
namespace AlgebraicGeometry.Scheme.Modules
universe u
variable {R : CommRingCat.{u}} {X Y : Scheme.{u}} {I : Type u}

/-- Transfer the given affine-chart basis to the actual restricted module sheaf. -/
def affineOpenBasisIso (U : X.affineOpens) (M : X.Modules) [M.IsQuasicoherent]
    (b : Basis I Γ(X, U) Γ(M, U)) :
    SheafOfModules.free (R := U.val.toScheme.ringCatSheaf) I ≅ M.restrict U.val.ι := by
  let a := affineBasisIso (M.restrict U.property.fromSpec)
    (b.map (affineChartΓIso U M).symm.toLinearEquiv)
  refine freeIsoOfRestrictIso U.property.isoSpec.symm (M.restrict U.val.ι) ?_
  exact a ≪≫ ((Scheme.Modules.restrictFunctorComp
    U.property.isoSpec.inv U.val.ι).app M)

/-- The localization comparison for an actual quasi-coherent module on an affine spectrum. -/
def affineQuasicoherentLocalizationIso (M : (Spec R).Modules) [M.IsQuasicoherent]
    (r : R) :
    M.restrict (Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away r)))) ≅
      tilde (ModuleCat.of (Localization.Away r)
        (LocalizedModule.Away r ((moduleSpecΓFunctor (R := R)).obj M))) := by
  let φ : R ⟶ CommRingCat.of (Localization.Away r) :=
    CommRingCat.ofHom (algebraMap R (Localization.Away r))
  let e : (ModuleCat.extendScalars φ.hom).obj ((moduleSpecΓFunctor (R := R)).obj M) ≅
      ModuleCat.of (Localization.Away r)
        (LocalizedModule.Away r ((moduleSpecΓFunctor (R := R)).obj M)) :=
    ModuleCat.extendScalarsAlgebraIso R (Localization.Away r) _ ≪≫
      (LocalizedModule.equivTensorProduct (.powers r)
        ((moduleSpecΓFunctor (R := R)).obj M)).symm.toModuleIso
  exact ((Scheme.Modules.restrictFunctorIsoPullback (Spec.map φ)).app M) ≪≫
    ((Scheme.Modules.pullback (Spec.map φ)).mapIso (asIso M.fromTildeΓ).symm ≪≫
      (tildePullbackIso φ).app _) ≪≫
      (tilde.functor (CommRingCat.of (Localization.Away r))).mapIso e

/-- The free presentation induced by the localized module basis on a principal affine open. -/
def affineBasicOpenLocalizedBasisIso (M : (Spec R).Modules) [M.IsQuasicoherent]
    (r : R) (b : Basis I (Localization.Away r)
      (LocalizedModule.Away r ((moduleSpecΓFunctor (R := R)).obj M))) :
    SheafOfModules.free (R := (show (Spec R).Opens from PrimeSpectrum.basicOpen
      r).toScheme.ringCatSheaf) I ≅
      M.restrict (show (Spec R).Opens from PrimeSpectrum.basicOpen r).ι := by
  let e := basicOpenIsoSpecAway (R := R) r
  let a : SheafOfModules.free (R := (Spec (CommRingCat.of (Localization.Away r))).ringCatSheaf) I ≅
      M.restrict (Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away r)))) :=
    (tildeBasisIso _ b).symm ≪≫ (affineQuasicoherentLocalizationIso M r).symm
  refine freeIsoOfRestrictIso e.symm (M.restrict (show (Spec R).Opens from PrimeSpectrum.basicOpen
    r).ι) ?_
  refine a ≪≫ ((Scheme.Modules.restrictFunctorCongr ?_).app M) ≪≫
    ((Scheme.Modules.restrictFunctorComp e.inv (show (Spec R).Opens from PrimeSpectrum.basicOpen
      r).ι).app M)
  simp [e, basicOpenIsoSpecAway]

theorem affineFinitePresentationFlatSheaf_locallyFree
    (M : (Spec R).Modules) [M.IsQuasicoherent]
    [Module.FinitePresentation R ((moduleSpecΓFunctor (R := R)).obj M)]
    [Module.Flat R ((moduleSpecΓFunctor (R := R)).obj M)] :
    IsFiniteLocallyFree _ M := by
  let κ := {r : R // ∃ n : ℕ, Nonempty (Basis (Fin n) (Localization.Away r)
    (LocalizedModule.Away r ((moduleSpecΓFunctor (R := R)).obj M)))}
  let U : κ → (Spec R).Opens := fun r ↦ PrimeSpectrum.basicOpen r.val
  have hcov : IsOpenCover U := by
    apply top_le_iff.mp
    intro p _
    obtain ⟨r, hr, n, ⟨b⟩⟩ := Module.FinitePresentation.exists_basis_away_of_flat R
      ((moduleSpecΓFunctor (R := R)).obj M) p
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨r, n, ⟨b⟩⟩, hr⟩
  let n (r : κ) : ℕ := r.property.choose
  let b (r : κ) : Basis (ULift.{u} (Fin (n r))) (Localization.Away r.val)
      (LocalizedModule.Away r.val ((moduleSpecΓFunctor (R := R)).obj M)) :=
    r.property.choose_spec.some.reindex Equiv.ulift.symm
  exact sheafFiniteLocallyFree_of_coverFreeIso U hcov
    (fun r ↦ ULift.{u} (Fin (n r))) (fun r ↦ affineBasicOpenLocalizedBasisIso M r.val (b r))

end AlgebraicGeometry.Scheme.Modules
