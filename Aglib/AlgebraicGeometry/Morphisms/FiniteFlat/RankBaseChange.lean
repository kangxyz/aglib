/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Morphisms.FiniteFlat.Fibres
public import Aglib.AlgebraicGeometry.Modules.BaseChange.Affine
public import Aglib.AlgebraicGeometry.Modules.BaseChange.CartesianInvertibility
public import Aglib.AlgebraicGeometry.Modules.FittingIdeal.ConstantRank

/-!
# Native locally free rank on an actual Cartesian square

The original affine base-change mate and the original pullback unit
isomorphism identify the pulled direct-image structure module with the
direct-image structure module of the actual base-changed map. Pullback
preserves the original constant-rank witness.

The input rank predicate already entails affineness. No etale, flat-base,
Noetherian or abstract base-change-family hypothesis is added.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- Constant native locally free rank is preserved on the given actual
Cartesian square, for arbitrary change of base. -/
theorem hasLocallyFreeRank_of_isPullback
    {W X T S : Scheme.{u}} (a : W ⟶ X) (b : W ⟶ T) (f : X ⟶ S) (g : T ⟶ S)
    (h : IsPullback a b f g) (r : ℕ) (hf : HasLocallyFreeRank f r) :
    HasLocallyFreeRank b r := by
  let : IsAffineHom f := hf.1
  let : IsAffineHom b := MorphismProperty.of_isPullback h inferInstance
  let O : X.Modules := SheafOfModules.unit X.ringCatSheaf
  let : O.IsLocallyFree := unit_isLocallyFree X
  let : O.IsQuasicoherent := inferInstance
  have hbc : IsIso ((cartesianBaseChangeMap a b f g h).app O) :=
    isIso_cartesianBaseChangeMap_of_isIso_moduleBaseChangeMap a b f g h O
      (moduleBaseChangeMap_isIso f g O)
  let e₀ := @asIso _ _ _ _ ((cartesianBaseChangeMap a b f g h).app O) hbc
  let e : (Scheme.Modules.pullback g).obj (pushforwardStructureSheaf f) ≅
      pushforwardStructureSheaf b :=
    e₀ ≪≫
      (Scheme.Modules.pushforward b).mapIso (pullbackUnitIso a)
  exact ⟨inferInstance, sheafHasRank_of_iso e (sheafHasRank_pullback g hf.2)⟩

end AlgebraicGeometry.Scheme.Hom
