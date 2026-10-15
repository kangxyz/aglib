/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Category.ModuleCat.ChangeOfRings.Flat
public import Aglib.AlgebraicGeometry.Cohomology.BaseChange.Modules.CechTransport
public import Aglib.AlgebraicGeometry.Cohomology.Cech.ModuleBaseChange
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Pullback
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.AlgebraicGeometry.Morphisms.Separated

/-! # Positive module cohomology under flat base change

The original scalar-adjunction tensor map is invertible in every positive
degree for a quasi-compact separated scheme over an affine base and arbitrary
quasicoherent coefficients. The proof uses a native finite affine subcover,
the actual Cech tensor isomorphism and its original geometric unit square.
No Noetherianity, finite generation or finiteness of cohomology is required.
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

variable {X : Scheme.{u}} {A B : Type u} [CommRing A] [CommRing B]

/-- A finite affine cover of a separated scheme proves flat base change for the original
positive cohomology tensor map with arbitrary quasicoherent coefficients. -/
theorem moduleCohomologyTensorMap_isIso_succ_of_finite_affine_cover [X.IsSeparated]
    (f : X ⟶ Spec (CommRingCat.of A)) (σ : A →+* B) (hflat : σ.Flat)
    (M : X.Modules) [M.IsQuasicoherent] {ι : Type u} [Finite ι]
    (U : ι → X.Opens) (hcover : iSup U = ⊤) (hU : ∀ i, IsAffineOpen (U i)) (n : ℕ) :
    let p := pullback.fst f (Spec.map (CommRingCat.ofHom σ))
    let q := pullback.snd f (Spec.map (CommRingCat.ofHom σ))
    let α := f.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom
    let β := q.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom
    IsIso (moduleCohomologyTensorMap p σ α β
      (moduleSectionsBaseChangeScalars p q f σ pullback.condition)
      ((Scheme.Modules.pullbackPushforwardAdjunction p).unit.app M) (n + 1)) := by
  let p := pullback.fst f (Spec.map (CommRingCat.ofHom σ))
  let q := pullback.snd f (Spec.map (CommRingCat.ofHom σ))
  let Y := pullback f (Spec.map (CommRingCat.ofHom σ))
  let α := f.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom
  let β := q.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom
  let h := moduleSectionsBaseChangeScalars p q f σ pullback.condition
  let N := (Scheme.Modules.pullback p).obj M
  let η := (Scheme.Modules.pullbackPushforwardAdjunction p).unit.app M
  let δ := moduleCechBaseChangeMap f σ M U
  let : PreservesFiniteLimits (ModuleCat.extendScalars.{u, u, u} σ) :=
    ModuleCat.extendScalars_preservesFiniteLimits_of_flat σ hflat
  let : PreservesFiniteColimits (ModuleCat.extendScalars.{u, u, u} σ) :=
    ModuleCat.extendScalars_preservesFiniteColimits_of_flat σ hflat
  let : IsAffineHom p := MorphismProperty.pullback_fst _ _ inferInstance
  let : Y.IsSeparated := ⟨by
    rw [← terminal.comp_from p]
    infer_instance⟩
  let : IsIso δ := moduleCechBaseChangeMap_isIso f σ M U hU
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
  have hδ := moduleCechTensorMapAlong_forget_unit p σ α β h η U
  exact moduleCohomologyTensorMap_isIso_succ_of_cech
    p σ α β U hcover haff haff' I J δ η hδ h n

/-- Flat base change for the original positive module cohomology tensor map of every
quasi-compact separated scheme over an affine base. -/
theorem moduleCohomologyTensorMap_isIso_succ_of_quasiCompact
    (f : X ⟶ Spec (CommRingCat.of A)) [QuasiCompact f] [IsSeparated f]
    (σ : A →+* B) (hflat : σ.Flat) (M : X.Modules) [M.IsQuasicoherent] (n : ℕ) :
    let p := pullback.fst f (Spec.map (CommRingCat.ofHom σ))
    let q := pullback.snd f (Spec.map (CommRingCat.ofHom σ))
    let α := f.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom
    let β := q.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom
    IsIso (moduleCohomologyTensorMap p σ α β
      (moduleSectionsBaseChangeScalars p q f σ pullback.condition)
      ((Scheme.Modules.pullbackPushforwardAdjunction p).unit.app M) (n + 1)) := by
  let : CompactSpace X := (quasiCompact_iff_compactSpace f).mp inferInstance
  let : X.IsSeparated := ⟨by
    rw [← terminal.comp_from f]
    infer_instance⟩
  let 𝒰 := X.affineCover.finiteSubcover
  exact moduleCohomologyTensorMap_isIso_succ_of_finite_affine_cover f σ hflat M
    (fun i => (𝒰.f i).opensRange) 𝒰.iSup_opensRange
    (fun i => isAffineOpen_opensRange (𝒰.f i)) n

end AlgebraicGeometry.Scheme.Cohomology
