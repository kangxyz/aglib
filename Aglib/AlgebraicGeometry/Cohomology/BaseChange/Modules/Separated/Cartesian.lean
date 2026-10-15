/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.BaseChange.Modules.Separated
public import Aglib.AlgebraicGeometry.Cohomology.Cech.ModuleBaseChange.Cartesian

/-! # Separated flat base change for a supplied cartesian square

The original cohomology tensor mate is invertible for the actual supplied
fibre square over spectra. The native finite Cech comparison and its original
geometric unit square prove the result directly, without replacing the
supplied square by a chosen pullback object.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open HomologicalComplex CategoryTheory.Cech

namespace AlgebraicGeometry.Scheme.Cohomology

variable {X Y : Scheme.{u}} {A B : Type u} [CommRing A] [CommRing B]

/-- A finite affine cover proves flat base change for the original cohomology tensor map
in every degree, retaining the actual supplied cartesian square. -/
theorem moduleCohomologyTensorMap_isIso_of_isPullback_of_finite_affine_cover [X.IsSeparated]
    (p : Y ⟶ X) (q : Y ⟶ Spec (CommRingCat.of B))
    (f : X ⟶ Spec (CommRingCat.of A)) (σ : A →+* B)
    (h : IsPullback p q f (Spec.map (CommRingCat.ofHom σ))) (hflat : σ.Flat)
    (M : X.Modules) [M.IsQuasicoherent] {ι : Type u} [Finite ι]
    (U : ι → X.Opens) (hcover : iSup U = ⊤) (hU : ∀ i, IsAffineOpen (U i)) (n : ℕ) :
    IsIso (moduleCohomologyTensorMap p σ
      (f.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom)
      (q.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom)
      (moduleSectionsBaseChangeScalars p q f σ h.w)
      ((Scheme.Modules.pullbackPushforwardAdjunction p).unit.app M) n) := by
  let α := f.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom
  let β := q.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom
  let hs := moduleSectionsBaseChangeScalars p q f σ h.w
  let N := (Scheme.Modules.pullback p).obj M
  let η := (Scheme.Modules.pullbackPushforwardAdjunction p).unit.app M
  let δ := moduleCechTensorMapAlong p σ α β hs η U
  let : PreservesFiniteLimits (ModuleCat.extendScalars.{u, u, u} σ) :=
    ModuleCat.extendScalars_preservesFiniteLimits_of_flat σ hflat
  let : PreservesFiniteColimits (ModuleCat.extendScalars.{u, u, u} σ) :=
    ModuleCat.extendScalars_preservesFiniteColimits_of_flat σ hflat
  let : IsIso δ := moduleCechTensorMapAlong_isIso_of_isPullback p q f σ h M U hU
  have hδ := moduleCechTensorMapAlong_forget_unit p σ α β hs η U
  cases n with
  | zero =>
    exact moduleCohomologyTensorMap_isIso_zero_of_cech p σ α β U hcover δ η hδ hs
  | succ n =>
    let : IsAffineHom p := MorphismProperty.of_isPullback h.flip inferInstance
    let : Y.IsSeparated := ⟨by
      rw [← terminal.comp_from p]
      infer_instance⟩
    have : N.IsQuasicoherent := Scheme.Modules.quasicoherent_pullback p M
    have haff (m : ℕ) (a : Fin (m + 1) → ι) :
        IsAffineOpen (∏ᶜ fun k => U (a k)) := by
      have he : (∏ᶜ fun k => U (a k)) = ⨅ k, U (a k) := by
        apply le_antisymm
        · exact le_iInf fun k => leOfHom (Pi.π _ k)
        · exact leOfHom (Pi.lift fun k => homOfLE (iInf_le _ k))
      rw [he]
      exact IsAffineOpen.iInf (fun k => hU (a k))
    have haff' (m : ℕ) (a : Fin (m + 1) → ι) :
        IsAffineOpen (∏ᶜ fun k => p ⁻¹ᵁ U (a k)) := by
      have he : (∏ᶜ fun k => p ⁻¹ᵁ U (a k)) = ⨅ k, p ⁻¹ᵁ U (a k) := by
        apply le_antisymm
        · exact le_iInf fun k => leOfHom (Pi.π _ k)
        · exact leOfHom (Pi.lift fun k => homOfLE (iInf_le _ k))
      rw [he]
      exact IsAffineOpen.iInf (fun k => (hU (a k)).preimage p)
    let I := injectiveResolution (moduleAddSheaf X M)
    let J := injectiveResolution (moduleAddSheaf Y N)
    exact moduleCohomologyTensorMap_isIso_succ_of_cech
      p σ α β U hcover haff haff' I J δ η hδ hs n

/-- Flat base change in every degree for a quasi-compact separated morphism to an affine
base, in the actual supplied cartesian square and with arbitrary quasicoherent coefficients. -/
theorem moduleCohomologyTensorMap_isIso_of_isPullback
    (p : Y ⟶ X) (q : Y ⟶ Spec (CommRingCat.of B))
    (f : X ⟶ Spec (CommRingCat.of A)) [QuasiCompact f] [IsSeparated f]
    (σ : A →+* B) (h : IsPullback p q f (Spec.map (CommRingCat.ofHom σ))) (hflat : σ.Flat)
    (M : X.Modules) [M.IsQuasicoherent] (n : ℕ) :
    IsIso (moduleCohomologyTensorMap p σ
      (f.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom)
      (q.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom)
      (moduleSectionsBaseChangeScalars p q f σ h.w)
      ((Scheme.Modules.pullbackPushforwardAdjunction p).unit.app M) n) := by
  let : CompactSpace X := (quasiCompact_iff_compactSpace f).mp inferInstance
  let : X.IsSeparated := ⟨by
    rw [← terminal.comp_from f]
    infer_instance⟩
  let 𝒰 := X.affineCover.finiteSubcover
  exact moduleCohomologyTensorMap_isIso_of_isPullback_of_finite_affine_cover p q f σ h hflat M
    (fun i => (𝒰.f i).opensRange) 𝒰.iSup_opensRange
    (fun i => isAffineOpen_opensRange (𝒰.f i)) n

end AlgebraicGeometry.Scheme.Cohomology
