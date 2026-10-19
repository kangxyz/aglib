/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Invertible.Affine

/-!
# Invertible modules and their sheafifications

For a commutative ring `R` and an `R`-module `M`, the sheafification `tilde M` on `Spec R` is
locally rank one exactly when `M` is an invertible module (`tilde_isLocallyRankOne_iff`). The
direction `invertible_of_tilde_isLocallyRankOne` is the converse of `tilde_isLocallyRankOne`:
the global sections of the line bundle `tilde M` form an invertible module
(`invertible_globalSections`), and they are `M`. No Noetherian or finiteness hypothesis on `R`
or `M` is used.
-/

@[expose] public section

noncomputable section

open CategoryTheory AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.Modules.Invertible

universe u

-- The global-sections instance `invertible_globalSections` is stated for `moduleSpecΓFunctor`
-- applied to the underlying sheaf of a line bundle; matching it with `tilde M` needs relaxed
-- instance transparency, as in `tilde_isLocallyRankOne`.
set_option backward.isDefEq.respectTransparency false in
/-- A module whose sheafification is locally rank one is an invertible module. -/
theorem invertible_of_tilde_isLocallyRankOne {R : CommRingCat.{u}} (M : ModuleCat.{u} R)
    (h : IsLocallyRankOne (Spec R) (tilde M)) : Module.Invertible R M := by
  let L : LineBundle (Spec R) := ⟨tilde M, h⟩
  have : Module.Invertible R (moduleSpecΓFunctor.obj L.val) := invertible_globalSections L
  exact Module.Invertible.congr (M := moduleSpecΓFunctor.obj L.val)
    (tilde.isoTop M).symm.toLinearEquiv

/-- The sheafification of a module is locally rank one iff the module is invertible. -/
theorem tilde_isLocallyRankOne_iff {R : CommRingCat.{u}} (M : ModuleCat.{u} R) :
    IsLocallyRankOne (Spec R) (tilde M) ↔ Module.Invertible R M :=
  ⟨invertible_of_tilde_isLocallyRankOne M, fun _ ↦ tilde_isLocallyRankOne M⟩

end AlgebraicGeometry.Scheme.Modules.Invertible
