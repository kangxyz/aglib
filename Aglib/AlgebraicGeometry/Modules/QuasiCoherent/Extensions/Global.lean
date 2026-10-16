/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Extensions.Affine
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Limits
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.FiniteType.Basic

/-!
# Actual global quasicoherent extension closure

Restriction to each actual affine chart is exact. The proved affine
extension theorem therefore gives quasicoherence of the original middle
module sheaf. The same argument proves extension closure of the actual
affine-locally finite-type quasicoherent predicate on every scheme.
No Noetherian hypothesis is used for these extension statements. Coherent
interpretation retains the existing locally Noetherian guard; no Serre
claim inside all module sheaves is made.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Modules

/-- Quasicoherence of the two end coefficients of an actual short exact
sequence implies quasicoherence of the original middle coefficient. -/
theorem isQuasicoherent_middle_of_shortExact {X : Scheme.{u}} {S : ShortComplex X.Modules}
    (hS : S.ShortExact) [S.X₁.IsQuasicoherent] [S.X₃.IsQuasicoherent] :
    S.X₂.IsQuasicoherent := by
  apply QuasiCoherent.quasicoherent_of_affineCharts S.X₂
  intro R j _
  let T := S.map (restrictFunctor j)
  let : T.X₁.IsQuasicoherent := isQuasicoherent_restrictFunctor j S.X₁
  let : T.X₃.IsQuasicoherent := isQuasicoherent_restrictFunctor j S.X₃
  exact QuasiCoherent.quasicoherent_middle_of_shortExact (hS.map_of_exact (restrictFunctor j))

instance quasicoherent_isClosedUnderExtensions (X : Scheme.{u}) :
    (SheafOfModules.isQuasicoherent X.ringCatSheaf).IsClosedUnderExtensions where
  prop_X₂_of_shortExact hS h₁ h₃ := by
    let := h₁
    let := h₃
    exact isQuasicoherent_middle_of_shortExact hS

namespace QuasiCoherent

/-- The actual affine-locally finite-type quasicoherent predicate is
extension-closed on every scheme, without local Noetherianity. -/
theorem affineLocallyFiniteType_middle_of_shortExact {X : Scheme.{u}}
    {S : ShortComplex X.Modules} (hS : S.ShortExact)
    (h₁ : affineLocallyFiniteType X S.X₁) (h₃ : affineLocallyFiniteType X S.X₃) :
    affineLocallyFiniteType X S.X₂ := by
  intro R j _
  exact affineFiniteSheaf_middle_of_shortExact (hS.map_of_exact (restrictFunctor j))
    (h₁ R j) (h₃ R j)

instance affineLocallyFiniteType_isClosedUnderExtensions (X : Scheme.{u}) :
    (affineLocallyFiniteType X).IsClosedUnderExtensions where
  prop_X₂_of_shortExact hS h₁ h₃ := affineLocallyFiniteType_middle_of_shortExact hS h₁ h₃

end QuasiCoherent

end AlgebraicGeometry.Scheme.Modules
