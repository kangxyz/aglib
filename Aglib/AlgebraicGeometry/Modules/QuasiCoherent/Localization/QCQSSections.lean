/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.DirectImage.QuasiCoherent
public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated

/-!
# Principal-open sections of quasicoherent modules on qcqs schemes

The degree-zero direct-image comparison gives quasicoherence of the actual ordinary
pushforward under a quasi-compact quasi-separated morphism. On an affine target, its
original restriction maps are therefore module localizations. A section over the inverse
image of a principal open extends after multiplication by a power of the original base
function; a section restricting to zero is annihilated by such a power.

For a qcqs scheme, the canonical morphism to the spectrum of global functions gives the
global-function version. The scalar comparison and the exact inverse-image equality keep
the original module, section and global function in that statement.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite

universe u

namespace AlgebraicGeometry.Scheme.Modules.QuasiCoherent

/-- The actual ordinary direct image of a quasicoherent module under a qcqs morphism
is quasicoherent. No finiteness or Noetherianity of the coefficient is required. -/
theorem quasicoherent_pushforward_of_qcqs {X Y : Scheme.{u}} (q : X ⟶ Y)
    [QuasiCompact q] [QuasiSeparated q] (M : X.Modules) [M.IsQuasicoherent] :
    ((Scheme.Modules.pushforward q).obj M).IsQuasicoherent := by
  have h := Scheme.Cohomology.moduleHigherDirectImage_isQuasicoherent q M 0
  exact (SheafOfModules.isQuasicoherent Y.ringCatSheaf).prop_of_iso
    (((Scheme.Modules.pushforward q).rightDerivedZeroIsoSelf).app M) h

namespace QCQSSections

/-- The original restriction map of the actual pushforward to an affine base is
localization at each original base function. -/
theorem isLocalizing_pushforward {A : CommRingCat.{u}} {X : Scheme.{u}}
    (q : X ⟶ Spec A) [QuasiCompact q] [QuasiSeparated q]
    (M : X.Modules) [M.IsQuasicoherent] :
    IsLocalizing (modulesSpecToSheaf.obj ((Scheme.Modules.pushforward q).obj M)) := by
  let N := (Scheme.Modules.pushforward q).obj M
  let : N.IsQuasicoherent := quasicoherent_pushforward_of_qcqs q M
  exact (isIso_fromTildeΓ_iff_isLocalizing N).mp inferInstance

/-- Every section over the actual inverse image of `D(f)` extends after multiplication
by a power of `f`. Both section objects and their restriction map are those of the
original pushforward, hence of the original preimage opens. -/
theorem exists_pow_smul_extension {A : CommRingCat.{u}} {X : Scheme.{u}}
    (q : X ⟶ Spec A) [QuasiCompact q] [QuasiSeparated q]
    (M : X.Modules) [M.IsQuasicoherent] (f : A)
    (s : Γ((Scheme.Modules.pushforward q).obj M, PrimeSpectrum.basicOpen f)) :
    ∃ (n : ℕ) (t : Γ((Scheme.Modules.pushforward q).obj M, ⊤)),
      ((Scheme.Modules.pushforward q).obj M).presheaf.map
        (PrimeSpectrum.basicOpen f).leTop.op t = f ^ n • s := by
  have h : IsLocalizedModule.Away f
      ((modulesSpecToSheaf.obj ((Scheme.Modules.pushforward q).obj M)).obj.map
        (PrimeSpectrum.basicOpen f).leTop.op).hom :=
    isLocalizing_pushforward q M f
  obtain ⟨n, t, ht⟩ := h.surj _ _ s
  exact ⟨n, t, ht.symm⟩

/-- An original global section that restricts to zero over the inverse image of `D(f)`
is killed by a power of the original base function. -/
theorem exists_pow_smul_eq_zero {A : CommRingCat.{u}} {X : Scheme.{u}}
    (q : X ⟶ Spec A) [QuasiCompact q] [QuasiSeparated q]
    (M : X.Modules) [M.IsQuasicoherent] (f : A)
    (t : Γ((Scheme.Modules.pushforward q).obj M, ⊤))
    (ht : ((Scheme.Modules.pushforward q).obj M).presheaf.map
      (PrimeSpectrum.basicOpen f).leTop.op t = 0) :
    ∃ n : ℕ, f ^ n • t = 0 := by
  have h : IsLocalizedModule.Away f
      ((modulesSpecToSheaf.obj ((Scheme.Modules.pushforward q).obj M)).obj.map
        (PrimeSpectrum.basicOpen f).leTop.op).hom :=
    isLocalizing_pushforward q M f
  have ht' : ((modulesSpecToSheaf.obj ((Scheme.Modules.pushforward q).obj M)).obj.map
      (PrimeSpectrum.basicOpen f).leTop.op).hom t = 0 := ht
  obtain ⟨n, hn⟩ := h.exists_of_eq f (x := t) (y := 0)
    (by rw [map_zero]; exact ht')
  exact ⟨n, by simpa only [smul_zero] using hn⟩

/-- Under the canonical map to the spectrum of global functions, the base-ring scalar
action on actual pushforward sections is restriction of the original global function. -/
theorem toSpecΓ_smul {X : Scheme.{u}} (M : X.Modules)
    (U : (Spec Γ(X, ⊤)).Opens) (f : Γ(X, ⊤))
    (s : Γ((Scheme.Modules.pushforward X.toSpecΓ).obj M, U)) :
    f • s = X.presheaf.map (homOfLE (le_top : X.toSpecΓ ⁻¹ᵁ U ≤ ⊤)).op f •
      (show Γ(M, X.toSpecΓ ⁻¹ᵁ U) from s) := by
  change X.toSpecΓ.app U
      ((Spec Γ(X, ⊤)).presheaf.map U.leTop.op ((Scheme.ΓSpecIso Γ(X, ⊤)).inv f)) •
      (show Γ(M, X.toSpecΓ ⁻¹ᵁ U) from s) = _
  have h := ConcreteCategory.congr_hom (X.toSpecΓ.naturality U.leTop.op)
    ((Scheme.ΓSpecIso Γ(X, ⊤)).inv f)
  change X.toSpecΓ.app U
      ((Spec Γ(X, ⊤)).presheaf.map U.leTop.op ((Scheme.ΓSpecIso Γ(X, ⊤)).inv f)) =
    X.presheaf.map (homOfLE (le_top : X.toSpecΓ ⁻¹ᵁ U ≤ ⊤)).op
      (X.toSpecΓ.appTop ((Scheme.ΓSpecIso Γ(X, ⊤)).inv f)) at h
  rw [Scheme.toSpecΓ_appTop, Iso.inv_hom_id_apply] at h
  exact congrArg (fun r => r • (show Γ(M, X.toSpecΓ ⁻¹ᵁ U) from s)) h

/-- On a qcqs scheme, a section of the actual quasicoherent module on the nonvanishing
open of a global function extends after multiplication by a power of that function.
The displayed restriction and scalar action belong to the original scheme and module. -/
theorem exists_power_mul_eq_restriction {X : Scheme.{u}} [CompactSpace X]
    [QuasiSeparatedSpace X] (M : X.Modules) [M.IsQuasicoherent]
    (f : Γ(X, ⊤)) (s : Γ(M, X.basicOpen f)) :
    ∃ (n : ℕ) (t : Γ(M, ⊤)),
      M.presheaf.map (homOfLE (X.basicOpen_le f)).op t =
        (X.presheaf.map (homOfLE (X.basicOpen_le f)).op f) ^ n • s := by
  let h := X.toSpecΓ_preimage_basicOpen f
  let e : Γ(M, X.basicOpen f) ≅
      Γ((Scheme.Modules.pushforward X.toSpecΓ).obj M, PrimeSpectrum.basicOpen f) :=
    M.presheaf.mapIso (eqToIso h).op
  obtain ⟨n, t, ht⟩ := exists_pow_smul_extension X.toSpecΓ M f (e.hom s)
  refine ⟨n, t, ?_⟩
  have hres : e.inv
      (((Scheme.Modules.pushforward X.toSpecΓ).obj M).presheaf.map
        (PrimeSpectrum.basicOpen f).leTop.op t) =
      M.presheaf.map (homOfLE (X.basicOpen_le f)).op t := by
    change M.presheaf.map (eqToHom h.symm).op
      (M.presheaf.map ((Opens.map X.toSpecΓ.base).map
        (PrimeSpectrum.basicOpen f).leTop).op t) = _
    rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
    rfl
  have hsmul : e.inv (f ^ n • e.hom s) =
      (X.presheaf.map (homOfLE (X.basicOpen_le f)).op f) ^ n • s := by
    rw [toSpecΓ_smul]
    change M.presheaf.map (eqToHom h.symm).op
      (X.presheaf.map (homOfLE le_top).op (f ^ n) •
        (show Γ(M, X.toSpecΓ ⁻¹ᵁ PrimeSpectrum.basicOpen f) from e.hom s)) = _
    rw [Scheme.Modules.map_smul]
    have hscalar : X.presheaf.map (eqToHom h.symm).op
        (X.presheaf.map (homOfLE le_top).op (f ^ n)) =
        (X.presheaf.map (homOfLE (X.basicOpen_le f)).op f) ^ n := by
      rw [← CommRingCat.comp_apply, ← Functor.map_comp]
      change X.presheaf.map (homOfLE (X.basicOpen_le f)).op (f ^ n) = _
      exact map_pow _ _ _
    rw [hscalar]
    change _ • e.inv (e.hom s) = _
    rw [Iso.hom_inv_id_apply]
  exact hres.symm.trans ((congrArg (fun v => e.inv v) ht).trans hsmul)

end QCQSSections

end AlgebraicGeometry.Scheme.Modules.QuasiCoherent
