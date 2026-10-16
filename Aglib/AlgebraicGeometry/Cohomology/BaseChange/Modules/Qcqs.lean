/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.BaseChange.Modules.Qcqs.Open

/-! # Canonical flat base change on quasi-compact quasi-separated schemes

The original cohomology tensor map is invertible in every degree for
arbitrary quasicoherent coefficients on a quasi-compact quasi-separated
scheme over an affine base. Native compact-open induction reduces to affine
unions. Their overlaps are compact and open in the added affine, hence
separated, and the original Mayer–Vietoris tensor ladder glues the actual
forward maps. No Noetherianity, properness or cohomological finiteness is used.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite

namespace AlgebraicGeometry.Scheme.Cohomology

variable {X Y : Scheme.{u}} {R S : Type u} [CommRing R] [CommRing S]

/-- Canonical flat cohomology base change for a quasi-compact quasi-separated morphism
over an affine base, retaining an arbitrary supplied cartesian square and original unit. -/
theorem moduleCohomologyTensorMap_isIso_of_quasiSeparated_of_isPullback
    (p : Y ⟶ X) (q : Y ⟶ Spec (CommRingCat.of S))
    (f : X ⟶ Spec (CommRingCat.of R)) [QuasiCompact f] [QuasiSeparated f]
    (σ : R →+* S) (h : IsPullback p q f (Spec.map (CommRingCat.ofHom σ))) (hflat : σ.Flat)
    (M : X.Modules) [M.IsQuasicoherent] (n : ℕ) :
    let α := f.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom
    let β := q.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of S)).inv.hom
    let hs := moduleSectionsBaseChangeScalars p q f σ h.w
    let N : Y.Modules := (Scheme.Modules.pullback p).obj M
    let φp : M ⟶ (Scheme.Modules.pushforward p).obj N :=
      (Scheme.Modules.pullbackPushforwardAdjunction p).unit.app M
    IsIso (moduleCohomologyTensorMap p σ α β hs φp n) := by
  let : CompactSpace X := (quasiCompact_iff_compactSpace f).mp inferInstance
  let : QuasiSeparatedSpace X := quasiSeparatedSpace_of_quasiSeparated f
  let α := f.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom
  let β := q.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of S)).inv.hom
  let hs := moduleSectionsBaseChangeScalars p q f σ h.w
  let N : Y.Modules := (Scheme.Modules.pullback p).obj M
  let φp : M ⟶ (Scheme.Modules.pushforward p).obj N :=
    (Scheme.Modules.pullbackPushforwardAdjunction p).unit.app M
  let C : X.Opens → Prop := fun U =>
    ∀ k, IsIso ((moduleHPrimeTensorMap p σ α β hs φp k).app (op U))
  have hbot : C ⊥ := by
    let : IsAffine (⊥ : X.Opens).toScheme := isAffineOpen_bot X
    intro k
    exact moduleHPrimeTensorMap_isIso_app_of_isSeparated_open p q f σ h hflat M ⊥
      (by simpa only [Opens.coe_bot] using (isCompact_empty : IsCompact (∅ : Set X))) k
  have hstep (T : X.Opens) (hT : IsCompact (T : Set X)) (U : X.affineOpens)
      (hCT : C T) : C (T ⊔ U.1) := by
    let : IsAffine U.1.toScheme := U.2
    have hCU : C U.1 := by
      intro k
      exact moduleHPrimeTensorMap_isIso_app_of_isSeparated_open
        p q f σ h hflat M U.1 U.2.isCompact k
    let i : (T ⊓ U.1).toScheme ⟶ U.1.toScheme := X.homOfLE inf_le_right
    let : (T ⊓ U.1).toScheme.IsSeparated := ⟨by
      rw [← terminal.comp_from i]
      infer_instance⟩
    have hTU : IsCompact ((T ⊓ U.1 : X.Opens) : Set X) :=
      hT.inter_of_isOpen U.2.isCompact T.isOpen U.1.isOpen
    have hCI : C (T ⊓ U.1) := by
      intro k
      exact moduleHPrimeTensorMap_isIso_app_of_isSeparated_open
        p q f σ h hflat M (T ⊓ U.1) hTU k
    intro k
    exact moduleHPrimeTensorMap_isIso_sup p σ α β hs φp hflat T U.1 hCT hCU hCI k
  have htop : C ⊤ := compact_open_induction_on (X := X) ⊤ isCompact_univ hbot hstep
  exact (moduleHPrimeTensorMap_top_isIso_iff p σ α β hs φp n).mp (htop n)

/-- The original actual-fibre-product module cohomology tensor map is invertible in every
degree after flat base change for arbitrary quasicoherent coefficients on a qcqs source. -/
theorem moduleCohomologyBaseChangeMap_isIso_of_quasiSeparated
    (f : X ⟶ Spec (CommRingCat.of R)) [QuasiCompact f] [QuasiSeparated f]
    (σ : R →+* S) (hflat : σ.Flat) (M : X.Modules) [M.IsQuasicoherent] (n : ℕ) :
    IsIso (moduleCohomologyBaseChangeMap f σ M n) :=
  moduleCohomologyTensorMap_isIso_of_quasiSeparated_of_isPullback
    (pullback.fst f (Spec.map (CommRingCat.ofHom σ)))
    (pullback.snd f (Spec.map (CommRingCat.ofHom σ))) f σ
    (IsPullback.of_hasPullback f (Spec.map (CommRingCat.ofHom σ))) hflat M n

end AlgebraicGeometry.Scheme.Cohomology
