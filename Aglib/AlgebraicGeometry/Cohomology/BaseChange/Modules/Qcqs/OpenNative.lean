/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.BaseChange.Modules.Map.ExtScalarSquareIsIso
public import Aglib.AlgebraicGeometry.Cohomology.BaseChange.Modules.Qcqs.Gluing
public import Aglib.AlgebraicGeometry.Cohomology.BaseChange.Modules.Sections.OpenRestriction
public import Aglib.AlgebraicGeometry.Cohomology.BaseChange.Modules.Separated.Cartesian
public import Aglib.AlgebraicGeometry.Cohomology.Modules.Scalars.Iso
public import Aglib.AlgebraicGeometry.Cohomology.Restriction.Cartesian.Geometric
public import Aglib.AlgebraicGeometry.Cohomology.Restriction.LinearCoefficients.Iso

/-! # The original native tensor comparison on a restricted open

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

/-- The complete original open tensor restriction square and its law. -/
def moduleHPrimeTensorRestrictionSquare (p : Y ⟶ X) (σ : R →+* S)
    (α : R →+* Γ(X, ⊤)) (β : S →+* Γ(Y, ⊤))
    (hσ : p.appTop.hom.comp α = β.comp σ) (M : X.Modules) (U : X.Opens) (n : ℕ) :
    Square (ModuleCat.{u + 1} S) :=
  moduleOpenPullbackExtTensorSquare p σ α β hσ M U n

/-- The original restriction equation, exposed by its same four transparent edges. -/
theorem moduleHPrimeTensorMap_restrict_square (p : Y ⟶ X) (σ : R →+* S)
    (α : R →+* Γ(X, ⊤)) (β : S →+* Γ(Y, ⊤))
    (hσ : p.appTop.hom.comp α = β.comp σ) (M : X.Modules) (U : X.Opens) (n : ℕ) :
    let s := moduleHPrimeTensorRestrictionSquare p σ α β hσ M U n
    s.f₁₂ ≫ s.f₂₄ = s.f₁₃ ≫ s.f₃₄ :=
  (moduleHPrimeTensorRestrictionSquare p σ α β hσ M U n).fac

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
  let : CompactSpace U.toScheme := isCompact_iff_compactSpace.mp hU
  let : QuasiCompact (j ≫ f) := inferInstance
  let : IsSeparated (j ≫ f) := inferInstance
  have : (M.restrict j).IsQuasicoherent := inferInstance
  apply moduleHPrimeTensorMap_isIso_app_of_restricted_tensor_isIso p σ α β hs M U n
  have H := moduleCohomologyTensorMap_isIso_of_isPullback
    b (a ≫ q) (j ≫ f) σ hlocal hflat (M.restrict j) n
  simpa only [Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.comp_assoc] using H

end AlgebraicGeometry.Scheme.Cohomology
