/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Localization
public import Mathlib.CategoryTheory.Sites.PreservesLocallyBijective

/-!
# Slice restriction and module-presheaf sheafification

Relocated from `Aglib/AlgebraicGeometry/Modules/Pullback/OpenRestriction.lean` at Aglib
`451aeda6b8bb5b44402b574dd6cf60f912360f8c`,
SHA-256 `59486f9a2887f0b9aef7266d8021cd0c26792525efd2b5b4335e04555cd281d3`.
The statements retain their original universes, hypotheses and actual maps.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Opposite
namespace PresheafOfModules.Restriction
universe u v
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable (R : Sheaf J RingCat.{u})
variable [HasWeakSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable (U : C)
variable [HasWeakSheafify (J.over U) AddCommGrpCat.{u}]
variable [(J.over U).WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- Restriction of module presheaves to the slice over U, with the identity scalar map. -/
def restrictPresheaf : _root_.PresheafOfModules.{u} R.obj ⥤
    _root_.PresheafOfModules.{u} (R.over U).obj :=
  _root_.PresheafOfModules.pushforward (F := Over.forget U) (𝟙 _)

/-- The actual module sheafification unit restricted to the slice over U. -/
def restrictedSheafificationUnit (P : _root_.PresheafOfModules.{u} R.obj) :
    (restrictPresheaf R U).obj P ⟶
      ((_root_.PresheafOfModules.sheafification (𝟙 R.obj)).obj P).over U |>.val :=
  (restrictPresheaf R U).map
    ((_root_.PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)).unit.app P)

omit [HasWeakSheafify (J.over U) AddCommGrpCat.{u}]
  [(J.over U).WEqualsLocallyBijective AddCommGrpCat.{u}] in
theorem restrictedSheafificationUnit_locallyInjective (P : _root_.PresheafOfModules.{u} R.obj) :
    _root_.PresheafOfModules.IsLocallyInjective (J.over U)
      (restrictedSheafificationUnit R U P) := by
  change Presheaf.IsLocallyInjective (J.over U)
    (Functor.whiskerLeft (Over.forget U).op (CategoryTheory.toSheafify J P.presheaf))
  exact Presheaf.isLocallyInjective_whisker (J.over U) J (Over.forget U) _

omit [HasWeakSheafify (J.over U) AddCommGrpCat.{u}]
  [(J.over U).WEqualsLocallyBijective AddCommGrpCat.{u}] in
theorem restrictedSheafificationUnit_locallySurjective (P : _root_.PresheafOfModules.{u} R.obj) :
    _root_.PresheafOfModules.IsLocallySurjective (J.over U)
      (restrictedSheafificationUnit R U P) := by
  change Presheaf.IsLocallySurjective (J.over U)
    (Functor.whiskerLeft (Over.forget U).op (CategoryTheory.toSheafify J P.presheaf))
  exact Presheaf.isLocallySurjective_whisker (J.over U) J (Over.forget U) _

theorem restrictedSheafificationUnit_sheafification_iso (P : _root_.PresheafOfModules.{u} R.obj) :
    IsIso ((_root_.PresheafOfModules.sheafification (𝟙 (R.over U).obj)).map
      (restrictedSheafificationUnit R U P)) := by
  apply Functor.IsLocalization.inverts
    (W := (J.over U).W.inverseImage (_root_.PresheafOfModules.toPresheaf (R.over U).obj))
  change (J.over U).W ((_root_.PresheafOfModules.toPresheaf (R.over U).obj).map
    (restrictedSheafificationUnit R U P))
  rw [(J.over U).W_iff_isLocallyBijective]
  exact ⟨restrictedSheafificationUnit_locallyInjective R U P,
    restrictedSheafificationUnit_locallySurjective R U P⟩

/-- Sheafification of slice restriction compared with slice restriction of sheafification. -/
def sheafificationOverIso (P : _root_.PresheafOfModules.{u} R.obj) :
    (_root_.PresheafOfModules.sheafification (𝟙 (R.over U).obj)).obj
      ((restrictPresheaf R U).obj P) ≅
      ((_root_.PresheafOfModules.sheafification (𝟙 R.obj)).obj P).over U := by
  let S : SheafOfModules.{u} (R.over U) :=
    ((_root_.PresheafOfModules.sheafification (𝟙 R.obj)).obj P).over U
  let f : (_root_.PresheafOfModules.sheafification (𝟙 (R.over U).obj)).obj
      ((restrictPresheaf R U).obj P) ⟶
      (_root_.PresheafOfModules.sheafification (𝟙 (R.over U).obj)).obj S.val :=
    (_root_.PresheafOfModules.sheafification (𝟙 (R.over U).obj)).map
      (restrictedSheafificationUnit R U P)
  have hf : IsIso f := restrictedSheafificationUnit_sheafification_iso R U P
  let c := (_root_.PresheafOfModules.sheafificationAdjunction (𝟙 (R.over U).obj)).counit.app S
  have hc : IsIso c := inferInstance
  exact asIso f ≪≫ asIso c

end PresheafOfModules.Restriction

namespace PresheafOfModules
universe u v
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable {R : Cᵒᵖ ⥤ RingCat.{u}}
variable [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
theorem isIso_of_locallyBijective {P Q : _root_.PresheafOfModules.{u} R} (f : P ⟶ Q)
    (hP : Presheaf.IsSheaf J P.presheaf) (hQ : Presheaf.IsSheaf J Q.presheaf)
    [_root_.PresheafOfModules.IsLocallyInjective J f]
    [_root_.PresheafOfModules.IsLocallySurjective J f] :
    IsIso f := by
  let eP := _root_.PresheafOfModules.homEquivOfIsLocallyBijective (J := J) f hP
  let eQ := _root_.PresheafOfModules.homEquivOfIsLocallyBijective (J := J) f hQ
  let g : Q ⟶ P := eP.symm (𝟙 P)
  have hfg : f ≫ g = 𝟙 P := eP.apply_symm_apply _
  have hgf : g ≫ f = 𝟙 Q := by
    apply eQ.injective
    change f ≫ (g ≫ f) = f ≫ 𝟙 Q
    rw [← Category.assoc, hfg, Category.id_comp, Category.comp_id]
  exact ⟨⟨g, hfg, hgf⟩⟩
end PresheafOfModules
