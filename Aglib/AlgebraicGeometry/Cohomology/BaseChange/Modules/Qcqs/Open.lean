/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.BaseChange.Modules.Qcqs.Gluing
public import Aglib.AlgebraicGeometry.Cohomology.BaseChange.Modules.Sections.OpenRestriction
public import Aglib.AlgebraicGeometry.Cohomology.BaseChange.Modules.Separated.Cartesian
public import Aglib.AlgebraicGeometry.Cohomology.Modules.Scalars.Iso
public import Aglib.AlgebraicGeometry.Cohomology.Restriction.Cartesian.Geometric

/-! # The original tensor comparison on a restricted open

The exact original geometric unit square gives an equality between the
native open tensor mate and the original cohomology tensor mate on the
actual restricted source. The target uses the original cartesian module
pullback/restriction comparison. This is the local separated input for
finite affine-union gluing.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open scoped TensorProduct ChangeOfRings

namespace AlgebraicGeometry.Scheme.Cohomology

variable {X Y : Scheme.{u}} {R S : Type u} [CommRing R] [CommRing S]

/-- The original open tensor mate is the original restricted cohomology tensor mate under
the actual open linear equivalences and the inverse cartesian coefficient comparison. -/
theorem moduleHPrimeTensorMap_restrict (p : Y ⟶ X) (σ : R →+* S)
    (α : R →+* Γ(X, ⊤)) (β : S →+* Γ(Y, ⊤))
    (hσ : p.appTop.hom.comp α = β.comp σ) (M : X.Modules) (U : X.Opens) (n : ℕ) :
    let V := p ⁻¹ᵁ U
    let a := V.ι
    let b := p ∣_ U
    let j := U.ι
    let h : IsPullback a b p j := (isPullback_morphismRestrict p U).flip
    let N : Y.Modules := (Scheme.Modules.pullback p).obj M
    let P : V.toScheme.Modules := (Scheme.Modules.pullback b).obj (M.restrict j)
    let αU := j.appTop.hom.comp α
    let βV := a.appTop.hom.comp β
    let hs := moduleSectionsOpenSquare_scalars a b p j α β σ hσ h.w
    let φp : M ⟶ (Scheme.Modules.pushforward p).obj N :=
      (Scheme.Modules.pullbackPushforwardAdjunction p).unit.app M
    let φb : M.restrict j ⟶ (Scheme.Modules.pushforward b).obj P :=
      (Scheme.Modules.pullbackPushforwardAdjunction b).unit.app (M.restrict j)
    let e : P ≅ N.restrict a :=
      asIso ((Scheme.Modules.cartesianPullbackBaseChangeMate a b p j h).app M)
    letI := moduleHPrimeModuleOfHom X α M n U
    letI := moduleHPrimeModuleOfHom Y β N n V
    letI := moduleCohomologyModuleOfHom U.toScheme αU (M.restrict j) n
    letI := moduleCohomologyModuleOfHom V.toScheme βV (N.restrict a) n
    letI := moduleCohomologyModuleOfHom V.toScheme βV P n
    (moduleHPrimeTensorMap p σ α β hσ φp n).app (op U) ≫
        (moduleHPrimeOpenLinearEquiv Y β N V n).toModuleIso.hom ≫
        (moduleCohomologyIsoOfHom V.toScheme βV e.symm n).hom =
      (ModuleCat.extendScalars.{u, u, u + 1} σ).map
          (moduleHPrimeOpenLinearEquiv X α M U n).toModuleIso.hom ≫
        moduleCohomologyTensorMap b σ αU βV hs φb n := by
  let V := p ⁻¹ᵁ U
  let a := V.ι
  let b := p ∣_ U
  let j := U.ι
  let h : IsPullback a b p j := (isPullback_morphismRestrict p U).flip
  let N : Y.Modules := (Scheme.Modules.pullback p).obj M
  let P : V.toScheme.Modules := (Scheme.Modules.pullback b).obj (M.restrict j)
  let αU := j.appTop.hom.comp α
  let βV := a.appTop.hom.comp β
  let hs := moduleSectionsOpenSquare_scalars a b p j α β σ hσ h.w
  let φp : M ⟶ (Scheme.Modules.pushforward p).obj N :=
    (Scheme.Modules.pullbackPushforwardAdjunction p).unit.app M
  let φb : M.restrict j ⟶ (Scheme.Modules.pushforward b).obj P :=
    (Scheme.Modules.pullbackPushforwardAdjunction b).unit.app (M.restrict j)
  let e : P ≅ N.restrict a :=
    asIso ((Scheme.Modules.cartesianPullbackBaseChangeMate a b p j h).app M)
  let := moduleHPrimeModuleOfHom X α M n U
  let := moduleHPrimeModuleOfHom Y β N n V
  let := moduleCohomologyModuleOfHom U.toScheme αU (M.restrict j) n
  let := moduleCohomologyModuleOfHom V.toScheme βV (N.restrict a) n
  let := moduleCohomologyModuleOfHom V.toScheme βV P n
  let eX : (moduleHPrimePresheaf X α M n).obj (op U) ≅
      ModuleCat.of R (Sheaf.H.{u + 1} (moduleAddSheaf U.toScheme (M.restrict j)) n) :=
    (moduleHPrimeOpenLinearEquiv X α M U n).toModuleIso
  let eY : (moduleHPrimePresheaf Y β N n).obj (op V) ≅
      ModuleCat.of S (Sheaf.H.{u + 1} (moduleAddSheaf V.toScheme (N.restrict a)) n) :=
    (moduleHPrimeOpenLinearEquiv Y β N V n).toModuleIso
  let eε := moduleCohomologyIsoOfHom V.toScheme βV e.symm n
  let q := moduleHPrimeTensorMap p σ α β hσ φp n
  let δ := moduleCohomologyTensorMap b σ αU βV hs φb n
  apply ModuleCat.ExtendScalars.hom_ext
  intro x
  change eε.hom (eY.hom (q.app (op U) ((1 : S) ⊗ₜ[R,σ] x))) =
    δ ((ModuleCat.extendScalars.{u, u, u + 1} σ).map eX.hom ((1 : S) ⊗ₜ[R,σ] x))
  calc
    _ = eε.hom (eY.hom
        ((zariskiCohomologyOpenMap p (moduleAddSheaf X M) (moduleAddSheaf Y N)
          (moduleCoefficientPullback p (M := M) (N := N) φp) n).app (op U) x)) :=
      congrArg (fun z => eε.hom (eY.hom z))
        (moduleHPrimeTensorMap_one_tmul p σ α β hσ φp n (op U) x)
    _ = moduleCohomologyMapAlong b φb n (eX.hom x) :=
      moduleHPrimeOpenRestrictionAddEquiv_pullback p M U n x
    _ = δ ((1 : S) ⊗ₜ[R,σ] eX.hom x) :=
      (moduleCohomologyTensorMap_one_tmul b σ αU βV hs φb n (eX.hom x)).symm
    _ = _ := congrArg δ (ModuleCat.ExtendScalars.map_tmul σ eX.hom 1 x).symm

/-- Flat base change is invertible on every compact separated source open, for the
original open tensor map in the actual supplied fibre square. -/
theorem moduleHPrimeTensorMap_isIso_app_of_isSeparated_open
    (p : Y ⟶ X) (q : Y ⟶ Spec (CommRingCat.of S))
    (f : X ⟶ Spec (CommRingCat.of R)) (σ : R →+* S)
    (h : IsPullback p q f (Spec.map (CommRingCat.ofHom σ))) (hflat : σ.Flat)
    (M : X.Modules) [M.IsQuasicoherent] (U : X.Opens) (hU : IsCompact (U : Set X))
    [U.toScheme.IsSeparated] (n : ℕ) :
    let α := f.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom
    let β := q.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of S)).inv.hom
    let hs := moduleSectionsBaseChangeScalars p q f σ h.w
    let N : Y.Modules := (Scheme.Modules.pullback p).obj M
    let φp : M ⟶ (Scheme.Modules.pushforward p).obj N :=
      (Scheme.Modules.pullbackPushforwardAdjunction p).unit.app M
    IsIso ((moduleHPrimeTensorMap p σ α β hs φp n).app (op U)) := by
  let V := p ⁻¹ᵁ U
  let a := V.ι
  let b := p ∣_ U
  let j := U.ι
  let hopen : IsPullback a b p j := (isPullback_morphismRestrict p U).flip
  let hlocal : IsPullback b (a ≫ q) (j ≫ f) (Spec.map (CommRingCat.ofHom σ)) :=
    (hopen.paste_horiz h.flip).flip
  let α := f.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom
  let β := q.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of S)).inv.hom
  let hs := moduleSectionsBaseChangeScalars p q f σ h.w
  let αU := j.appTop.hom.comp α
  let βV := a.appTop.hom.comp β
  let hsU := moduleSectionsOpenSquare_scalars a b p j α β σ hs hopen.w
  let N : Y.Modules := (Scheme.Modules.pullback p).obj M
  let P : V.toScheme.Modules := (Scheme.Modules.pullback b).obj (M.restrict j)
  let φp : M ⟶ (Scheme.Modules.pushforward p).obj N :=
    (Scheme.Modules.pullbackPushforwardAdjunction p).unit.app M
  let φb : M.restrict j ⟶ (Scheme.Modules.pushforward b).obj P :=
    (Scheme.Modules.pullbackPushforwardAdjunction b).unit.app (M.restrict j)
  let e : P ≅ N.restrict a :=
    asIso ((Scheme.Modules.cartesianPullbackBaseChangeMate a b p j hopen).app M)
  let := moduleHPrimeModuleOfHom X α M n U
  let := moduleHPrimeModuleOfHom Y β N n V
  let := moduleCohomologyModuleOfHom U.toScheme αU (M.restrict j) n
  let := moduleCohomologyModuleOfHom V.toScheme βV (N.restrict a) n
  let := moduleCohomologyModuleOfHom V.toScheme βV P n
  let eX : (moduleHPrimePresheaf X α M n).obj (op U) ≅
      ModuleCat.of R (Sheaf.H.{u + 1} (moduleAddSheaf U.toScheme (M.restrict j)) n) :=
    (moduleHPrimeOpenLinearEquiv X α M U n).toModuleIso
  let eY : (moduleHPrimePresheaf Y β N n).obj (op V) ≅
      ModuleCat.of S (Sheaf.H.{u + 1} (moduleAddSheaf V.toScheme (N.restrict a)) n) :=
    (moduleHPrimeOpenLinearEquiv Y β N V n).toModuleIso
  let eε := moduleCohomologyIsoOfHom V.toScheme βV e.symm n
  let δ := moduleCohomologyTensorMap b σ αU βV hsU φb n
  let t := moduleHPrimeTensorMap p σ α β hs φp n
  let : CompactSpace U.toScheme := isCompact_iff_compactSpace.mp hU
  let : QuasiCompact (j ≫ f) := inferInstance
  let : IsSeparated (j ≫ f) := inferInstance
  have : (M.restrict j).IsQuasicoherent := inferInstance
  let : IsIso δ := by
    have H := moduleCohomologyTensorMap_isIso_of_isPullback
      b (a ≫ q) (j ≫ f) σ hlocal hflat (M.restrict j) n
    simpa only [Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.comp_assoc] using H
  have Hsq : t.app (op U) ≫ eY.hom ≫ eε.hom =
      (ModuleCat.extendScalars.{u, u, u + 1} σ).map eX.hom ≫ δ :=
    moduleHPrimeTensorMap_restrict p σ α β hs M U n
  have Hiso : IsIso (t.app (op U) ≫ (eY.hom ≫ eε.hom)) := by
    rw [Hsq]
    infer_instance
  exact IsIso.of_isIso_comp_right (t.app (op U)) (eY.hom ≫ eε.hom)

end AlgebraicGeometry.Scheme.Cohomology
