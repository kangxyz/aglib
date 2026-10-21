/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.BaseChange.Affine.GlobalSections
public import Aglib.AlgebraicGeometry.Modules.BaseChange.OpenImmersion
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Limits
public import Mathlib.AlgebraicGeometry.Morphisms.Affine

/-!
# Quasicoherent direct image along an affine morphism

The target need not be affine. Restriction to each actual affine chart is
identified with the original direct image through the pullback square.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u
open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme.Modules

/-- An affine morphism preserves quasicoherence under actual direct image. -/
theorem isQuasicoherent_pushforward_of_isAffineHom {X Y : Scheme.{u}}
    (f : X ⟶ Y) [IsAffineHom f] (M : X.Modules) [M.IsQuasicoherent] :
    ((pushforward f).obj M).IsQuasicoherent := by
  apply QuasiCoherent.quasicoherent_of_affineCharts
  intro R j _
  let : IsAffine (Limits.pullback f j) := isAffine_of_isAffineHom (pullback.snd f j)
  let : ((restrictFunctor (pullback.fst f j)).obj M).IsQuasicoherent :=
    isQuasicoherent_restrictFunctor _ M
  exact (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf).prop_of_iso
    ((openBaseChange f j).app M).symm
    (isQuasicoherent_pushforward_of_isAffine (pullback.snd f j) _)

end AlgebraicGeometry.Scheme.Modules
