/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.DirectImage.ResolutionSections.Pullback
public import Aglib.AlgebraicGeometry.Cohomology.BaseChange.Modules.Qcqs
public import Aglib.AlgebraicGeometry.Cohomology.BaseChange.Flat
public import Aglib.Algebra.Category.ModuleCat.ChangeOfRings.Flat

/-!
# Actual resolution-section homology after affine flat base change

The already proved original cohomology tensor map identifies the original
resolution-section homology mate. Its original unit formula proves equality
with that same map through the original resolution comparisons. Quasi-compact
quasi-separated geometry and scalar flatness supply invertibility; neither
Noetherianity nor cohomological finite generation is needed.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry HomologicalComplex
open scoped TensorProduct ChangeOfRings

namespace AlgebraicGeometry.Scheme.Cohomology

universe u

private theorem resolutionHomologyMap_isIso_of_cohomologyTensorMap
    {X Y : Scheme.{u}} {R S : Type u} [CommRing R] [CommRing S]
    (p : Y ⟶ X) [Flat p] (α : R →+* Γ(X, ⊤)) (β : S →+* Γ(Y, ⊤)) (σ : R →+* S)
    (hσ : p.appTop.hom.comp α = β.comp σ) {M : X.Modules}
    (I : InjectiveResolution M) (J : InjectiveResolution ((Scheme.Modules.pullback p).obj M))
    (n : ℕ)
    (hbc : letI := moduleCohomologyModuleOfHom X α M n
      letI := moduleCohomologyModuleOfHom Y β ((Scheme.Modules.pullback p).obj M) n
      IsIso (moduleCohomologyTensorMap (M := M) (N := (Scheme.Modules.pullback p).obj M)
        p σ α β hσ
        ((Scheme.Modules.pullbackPushforwardAdjunction p).unit.app M) n)) :
    IsIso (moduleResolutionPullbackSectionsHomologyMap p α β σ hσ I J n) := by
  let := σ.toAlgebra
  let := moduleCohomologyModuleOfHom X α M n
  let := moduleCohomologyModuleOfHom Y β ((Scheme.Modules.pullback p).obj M) n
  let := hbc
  let eR := moduleResolutionSectionsCohomologyLinearEquiv X α I n
  let eS := moduleResolutionSectionsCohomologyLinearEquiv Y β J n
  let eC := (asIso (moduleCohomologyTensorMap
    (M := M) (N := (Scheme.Modules.pullback p).obj M) p σ α β hσ
    ((Scheme.Modules.pullbackPushforwardAdjunction p).unit.app M) n)).toLinearEquiv
  let e := (eR.baseChange R S _ _).trans (eC.trans eS.symm)
  have he : moduleResolutionPullbackSectionsHomologyMap p α β σ hσ I J n =
      e.toModuleIso.hom := by
    apply ModuleCat.ExtendScalars.hom_ext
    intro x
    apply eS.injective
    rw [moduleResolutionPullbackSectionsHomologyMap_one_tmul p α β σ hσ I J n x]
    change moduleCohomologyMapAlong (M := M) (N := (Scheme.Modules.pullback p).obj M)
        p _ n (eR x) =
      eS (eS.symm (moduleCohomologyTensorMap
        (M := M) (N := (Scheme.Modules.pullback p).obj M) p σ α β hσ
        ((Scheme.Modules.pullbackPushforwardAdjunction p).unit.app M) n
        ((1 : S) ⊗ₜ[R,σ] eR x)))
    rw [LinearEquiv.apply_symm_apply, moduleCohomologyTensorMap_one_tmul]
  rw [he]
  infer_instance

private theorem resolutionTensorMap_quasiIso_of_homologyMap_isIso
    {X Y : Scheme.{u}} {R S : Type u} [CommRing R] [CommRing S]
    (p : Y ⟶ X) [Flat p] (α : R →+* Γ(X, ⊤)) (β : S →+* Γ(Y, ⊤)) (σ : R →+* S)
    (hσ : p.appTop.hom.comp α = β.comp σ) (hflat : σ.Flat) {M : X.Modules}
    (I : InjectiveResolution M) (J : InjectiveResolution ((Scheme.Modules.pullback p).obj M))
    (hH : ∀ n : ℕ,
      IsIso (moduleResolutionPullbackSectionsHomologyMap p α β σ hσ I J n)) :
    QuasiIso (moduleResolutionPullbackSectionsTensorMap p α β σ hσ I J) := by
  let : PreservesFiniteLimits (ModuleCat.extendScalars σ) :=
    ModuleCat.extendScalars_preservesFiniteLimits_of_flat σ hflat
  let : PreservesFiniteColimits (ModuleCat.extendScalars σ) :=
    ModuleCat.extendScalars_preservesFiniteColimits_of_flat σ hflat
  let C := moduleResolutionSectionComplex X α I
  let D := moduleResolutionSectionComplex Y β J
  let δ := moduleResolutionPullbackSectionsTensorMap p α β σ hσ I J
  let : C.IsStrictlyGE 0 := by dsimp only [C, moduleResolutionSectionComplex]; infer_instance
  let : D.IsStrictlyGE 0 := by dsimp only [D, moduleResolutionSectionComplex]; infer_instance
  let E : CochainComplex (ModuleCat.{u} S) ℤ :=
    ((ModuleCat.extendScalars σ).mapHomologicalComplex (.up ℤ)).obj C
  let : E.IsStrictlyGE 0 := by dsimp only [E]; infer_instance
  rw [quasiIso_iff]
  intro i
  rw [quasiIsoAt_iff_isIso_homologyMap]
  by_cases hi : 0 ≤ i
  · obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hi
    have he : moduleResolutionPullbackSectionsHomologyMap p α β σ hσ I J n =
        ((C.sc (n : ℤ)).mapHomologyIso (ModuleCat.extendScalars σ)).inv ≫
          homologyMap δ (n : ℤ) := by
      change ModuleCat.homologyBaseChangeMap σ (C.sc (n : ℤ)) ≫ homologyMap δ (n : ℤ) = _
      rw [ModuleCat.homologyBaseChangeMap_eq_mapHomologyIso_inv]
    let : IsIso (((C.sc (n : ℤ)).mapHomologyIso (ModuleCat.extendScalars σ)).inv ≫
        homologyMap δ (n : ℤ)) := he ▸ hH n
    exact IsIso.of_isIso_comp_left ((C.sc (n : ℤ)).mapHomologyIso
      (ModuleCat.extendScalars σ)).inv (homologyMap δ (n : ℤ))
  · exact (E.isZero_of_isGE 0 i (by omega)).isIso
      (D.isZero_of_isGE 0 i (by omega)) (homologyMap δ i)

/-- The actual native resolution-section tensor homology map is invertible after flat base
change over affine bases for a qcqs morphism and any quasicoherent coefficient. -/
theorem moduleResolutionPullbackSectionsHomologyMap_isIso_of_isPullback
    {X Y : Scheme.{u}} {R S : Type u} [CommRing R] [CommRing S]
    (a : Y ⟶ X) (b : Y ⟶ Spec (CommRingCat.of S))
    (f : X ⟶ Spec (CommRingCat.of R)) [QuasiCompact f] [QuasiSeparated f]
    (σ : R →+* S) (h : IsPullback a b f (Spec.map (CommRingCat.ofHom σ))) (hflat : σ.Flat)
    (M : X.Modules) [M.IsQuasicoherent] (I : InjectiveResolution M)
    (J : InjectiveResolution ((Scheme.Modules.pullback a).obj M)) (n : ℕ) :
    letI : Flat (Spec.map (CommRingCat.ofHom σ)) := Flat.SpecMap_iff.mpr hflat
    letI := Scheme.Modules.flat_cartesian_baseChange a b f (Spec.map (CommRingCat.ofHom σ)) h
    let α := f.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom
    let β := b.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of S)).inv.hom
    let hs := moduleSectionsBaseChangeScalars a b f σ h.w
    IsIso (moduleResolutionPullbackSectionsHomologyMap a α β σ hs I J n) := by
  let : Flat (Spec.map (CommRingCat.ofHom σ)) := Flat.SpecMap_iff.mpr hflat
  let := Scheme.Modules.flat_cartesian_baseChange a b f (Spec.map (CommRingCat.ofHom σ)) h
  exact resolutionHomologyMap_isIso_of_cohomologyTensorMap a _ _ σ _ I J n
    (moduleCohomologyTensorMap_isIso_of_quasiSeparated_of_isPullback a b f σ h hflat M n)

/-- The actual section-complex scalar mate is a quasi-isomorphism after affine flat base
change for any qcqs morphism and quasicoherent coefficient, on every supplied resolution. -/
theorem moduleResolutionPullbackSectionsTensorMap_quasiIso_of_isPullback
    {X Y : Scheme.{u}} {R S : Type u} [CommRing R] [CommRing S]
    (a : Y ⟶ X) (b : Y ⟶ Spec (CommRingCat.of S))
    (f : X ⟶ Spec (CommRingCat.of R)) [QuasiCompact f] [QuasiSeparated f]
    (σ : R →+* S) (h : IsPullback a b f (Spec.map (CommRingCat.ofHom σ))) (hflat : σ.Flat)
    (M : X.Modules) [M.IsQuasicoherent] (I : InjectiveResolution M)
    (J : InjectiveResolution ((Scheme.Modules.pullback a).obj M)) :
    letI : Flat (Spec.map (CommRingCat.ofHom σ)) := Flat.SpecMap_iff.mpr hflat
    letI := Scheme.Modules.flat_cartesian_baseChange a b f (Spec.map (CommRingCat.ofHom σ)) h
    let α := f.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom
    let β := b.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of S)).inv.hom
    let hs := moduleSectionsBaseChangeScalars a b f σ h.w
    QuasiIso (moduleResolutionPullbackSectionsTensorMap a α β σ hs I J) := by
  let : Flat (Spec.map (CommRingCat.ofHom σ)) := Flat.SpecMap_iff.mpr hflat
  let := Scheme.Modules.flat_cartesian_baseChange a b f (Spec.map (CommRingCat.ofHom σ)) h
  exact resolutionTensorMap_quasiIso_of_homologyMap_isIso a _ _ σ _ hflat I J
    (moduleResolutionPullbackSectionsHomologyMap_isIso_of_isPullback a b f σ h hflat M I J)

end AlgebraicGeometry.Scheme.Cohomology
