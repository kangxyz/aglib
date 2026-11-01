/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Coherent.Hartogs.FiniteLocallyFreeRestriction
public import Aglib.AlgebraicGeometry.Modules.LocallyFree.FiniteFlat

/-! # Original section restriction of a finite flat cover on a Hartogs open

The cover is unchanged. Restriction is to the literal inverse-image open, and
the resulting ring map is the original open immersion's appTop. The actual
finite locally free module p_* O supplies the comparison; no extension of the
cover or of its algebra is assumed.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory

namespace AlgebraicGeometry.Scheme

universe u

/-- The original cover's ambient open-section restriction is an isomorphism. -/
theorem isIso_cover_restriction_of_structureUnit
    {W X : Scheme.{u}} (p : W ⟶ X) [IsFinite p] [Flat p]
    [LocallyOfFinitePresentation p] (O : X.Opens)
    [IsIso (SheafOfModules.unitToPushforwardObjUnit O.ι.toRingCatSheafHom)] :
    IsIso (W.presheaf.map (homOfLE (show p ⁻¹ᵁ O ≤ ⊤ from le_top)).op) := by
  let M : X.Modules := Modules.pushforwardStructureSheaf p
  let : Modules.IsFiniteLocallyFree X M :=
    Modules.finiteFlat_pushforwardStructureSheaf_isFiniteLocallyFree p
  let : IsIso ((Modules.restrictAdjunction O.ι).unit.app M) :=
    Modules.isIso_restrictUnit_of_structureUnit O.ι M
  have hb := (ConcreteCategory.isIso_iff_bijective
    (Modules.Hom.app ((Modules.restrictAdjunction O.ι).unit.app M) ⊤)).mp inferInstance
  rw [Modules.restrictAdjunction_unit_app_app] at hb
  let T : W.Opens := p ⁻¹ᵁ (O.ι ''ᵁ ⊤)
  have hT : T = p ⁻¹ᵁ O := by simp only [T, Opens.ι_image_top]
  have hi : IsIso (W.presheaf.map (homOfLE (show T ≤ ⊤ from le_top)).op) := by
    apply (ConcreteCategory.isIso_iff_bijective _).mpr
    exact hb
  have he : W.presheaf.map (homOfLE (show p ⁻¹ᵁ O ≤ ⊤ from le_top)).op =
      W.presheaf.map (homOfLE (show T ≤ ⊤ from le_top)).op ≫
        W.presheaf.map (eqToHom hT.symm).op := by
    rw [← Functor.map_comp]
    rfl
  rw [he]
  infer_instance

/-- Restriction of the actual cover to the literal inverse image preserves
its original global section ring via the original ring homomorphism. -/
theorem cover_restriction_appTop_bijective_of_structureUnit
    {W X : Scheme.{u}} (p : W ⟶ X) [IsFinite p] [Flat p]
    [LocallyOfFinitePresentation p] (O : X.Opens)
    [IsIso (SheafOfModules.unitToPushforwardObjUnit O.ι.toRingCatSheafHom)] :
    Function.Bijective (p ⁻¹ᵁ O).ι.appTop := by
  let Q := p ⁻¹ᵁ O
  let : IsIso (W.presheaf.map (homOfLE (show Q ≤ ⊤ from le_top)).op) :=
    isIso_cover_restriction_of_structureUnit p O
  have he : Q.ι.appTop ≫ Q.topIso.hom =
      W.presheaf.map (homOfLE (show Q ≤ ⊤ from le_top)).op := by
    simp only [Opens.ι_appTop, Opens.topIso_hom]
    rw [← Functor.map_comp]
    rfl
  have hi : IsIso (Q.ι.appTop ≫ Q.topIso.hom) := by rw [he]; infer_instance
  let : IsIso Q.ι.appTop := IsIso.of_isIso_comp_right _ Q.topIso.hom
  exact (ConcreteCategory.isIso_iff_bijective Q.ι.appTop).mp inferInstance

end AlgebraicGeometry.Scheme
