/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.BaseChange.Modules.Map.Spec
public import Aglib.AlgebraicGeometry.Cohomology.BaseChange.Modules.CechTransport.DegreeZero
public import Aglib.AlgebraicGeometry.Cohomology.BaseChange.Modules.SeparatedPositive

/-!
# Flat base change for arbitrary quasicoherent coefficients on separated schemes

For a quasi-compact separated morphism to an affine base, the original module
cohomology tensor map is invertible in every nonnegative degree after a flat
ring map. The zero-degree proof uses the actual sheaf augmentation; positive
degrees use the native Cech/resolution computation. The comparison and its
unit formula concern the unchanged `Sheaf.H` and geometric module pullback.

There is no field, Noetherian, properness, finite-presentation or cohomological
finiteness premise.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite

namespace AlgebraicGeometry.Scheme.Cohomology

universe u

variable {X : Scheme.{u}} {A B : Type u} [CommRing A] [CommRing B]

/-- Flat base change in degree zero from an actual finite affine cover of a separated scheme. -/
theorem moduleCohomologyBaseChangeMap_isIso_zero_of_finite_affine_cover [X.IsSeparated]
    (f : X ⟶ Spec (CommRingCat.of A)) (σ : A →+* B) (hflat : σ.Flat)
    (M : X.Modules) [M.IsQuasicoherent] {ι : Type u} [Finite ι]
    (U : ι → X.Opens) (hcover : iSup U = ⊤) (hU : ∀ i, IsAffineOpen (U i)) :
    IsIso (moduleCohomologyBaseChangeMap f σ M 0) := by
  let p := pullback.fst f (Spec.map (CommRingCat.ofHom σ))
  let q := pullback.snd f (Spec.map (CommRingCat.ofHom σ))
  let α := f.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom
  let β := q.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom
  let h := moduleSectionsBaseChangeScalars p q f σ pullback.condition
  let η := (Scheme.Modules.pullbackPushforwardAdjunction p).unit.app M
  let δ := moduleCechBaseChangeMap f σ M U
  let : PreservesFiniteLimits (ModuleCat.extendScalars.{u, u, u} σ) :=
    ModuleCat.extendScalars_preservesFiniteLimits_of_flat σ hflat
  let : PreservesFiniteColimits (ModuleCat.extendScalars.{u, u, u} σ) :=
    ModuleCat.extendScalars_preservesFiniteColimits_of_flat σ hflat
  let : IsIso δ := moduleCechBaseChangeMap_isIso f σ M U hU
  have hδ := moduleCechTensorMapAlong_forget_unit p σ α β h η U
  exact moduleCohomologyTensorMap_isIso_zero_of_cech p σ α β U hcover δ η hδ h

/-- A finite affine cover proves canonical flat base change in every nonnegative degree. -/
theorem moduleCohomologyBaseChangeMap_isIso_of_finite_affine_cover [X.IsSeparated]
    (f : X ⟶ Spec (CommRingCat.of A)) (σ : A →+* B) (hflat : σ.Flat)
    (M : X.Modules) [M.IsQuasicoherent] {ι : Type u} [Finite ι]
    (U : ι → X.Opens) (hcover : iSup U = ⊤) (hU : ∀ i, IsAffineOpen (U i)) (n : ℕ) :
    IsIso (moduleCohomologyBaseChangeMap f σ M n) := by
  cases n with
  | zero =>
    exact moduleCohomologyBaseChangeMap_isIso_zero_of_finite_affine_cover f σ hflat M U hcover hU
  | succ n =>
    exact moduleCohomologyTensorMap_isIso_succ_of_finite_affine_cover f σ hflat M U hcover hU n

/-- Canonical flat base change in all degrees for a quasi-compact separated morphism
to the spectrum of an arbitrary commutative ring and any quasicoherent module coefficient. -/
theorem moduleCohomologyBaseChangeMap_isIso_of_isSeparated
    (f : X ⟶ Spec (CommRingCat.of A)) [QuasiCompact f] [IsSeparated f]
    (σ : A →+* B) (hflat : σ.Flat) (M : X.Modules) [M.IsQuasicoherent] (n : ℕ) :
    IsIso (moduleCohomologyBaseChangeMap f σ M n) := by
  let : CompactSpace X := (quasiCompact_iff_compactSpace f).mp inferInstance
  let : X.IsSeparated := ⟨by
    rw [← terminal.comp_from f]
    infer_instance⟩
  let 𝒰 := X.affineCover.finiteSubcover
  exact moduleCohomologyBaseChangeMap_isIso_of_finite_affine_cover f σ hflat M
    (fun i => (𝒰.f i).opensRange) 𝒰.iSup_opensRange
    (fun i => isAffineOpen_opensRange (𝒰.f i)) n

end AlgebraicGeometry.Scheme.Cohomology
