/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Invertible.Power.Pullback
public import Aglib.AlgebraicGeometry.Modules.Invertible.Power.TrivializedPower
public import Aglib.AlgebraicGeometry.Modules.Invertible.Power.UnitPower
public import Aglib.AlgebraicGeometry.Modules.Pullback.Tensor.Unit

/-!
Native migration from `R5Lab.Aglib.AlgebraicGeometry.Picard.PowerCoherence` at R5 revision
`f8a3314ddecffcada2ec721d26d56a937bed9690`, SHA-256
`bef5230750e8c9a12625ec167d856e834dcee058d8db207043f7a87a2e87a0c0`.
Original objects, maps, universes and explicit hypotheses are retained.
Native providers replace duplicate implementations.
-/

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
open _root_.AlgebraicGeometry.Scheme.Modules.Invertible
  (LineBundle pullbackLineBundle tensorPowerLineBundle trivialLineBundle)
open _root_.AlgebraicGeometry.Scheme.Modules
  (pullbackUnitIso pullbackTensorMap tensorSheafIso tensorSheafLeftUnit tensorSheafMap)
open AlgebraicGeometry.Scheme.Hom AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Modules.Invertible
namespace AlgebraicGeometry.Scheme.Modules.Invertible.Power
universe u

/-- The actual free-unit equation for pullback of the zeroth power. -/
theorem pullbackPowerIso_zero_hom {S T : Scheme.{u}} (f : S ⟶ T) (L : LineBundle T) :
    (AlgebraicGeometry.Scheme.Modules.Invertible.PowerPullback.pullbackPowerIso f L 0).hom =
      (Scheme.Modules.pullback f).map
          (AlgebraicGeometry.Scheme.Modules.Invertible.PowerPullback.freeUnitIso T).hom ≫
        (pullbackUnitIso f).hom ≫
            (AlgebraicGeometry.Scheme.Modules.Invertible.PowerPullback.freeUnitIso S).inv := rfl

theorem powerIso_zero_hom (S : Scheme.{u}) {L M : LineBundle S} (e : L.val ≅ M.val) :
    (AlgebraicGeometry.Scheme.Modules.Invertible.TrivializedPower.powerIso S e 0).hom = 𝟙 (show
        S.Modules from (trivialLineBundle S).val) := rfl

theorem unitPowerIso_zero_hom (S : Scheme.{u}) :
    (AlgebraicGeometry.Scheme.Modules.Invertible.UnitPower.unitPowerIso S 0).hom =
        (AlgebraicGeometry.Scheme.Modules.Invertible.PowerPullback.freeUnitIso S).hom := rfl

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
/-- The actual canonical tensor equation for a successor power pullback. -/
theorem pullbackPowerIso_succ_hom {S T : Scheme.{u}} (f : S ⟶ T) (L : LineBundle T) (n : ℕ) :
    (AlgebraicGeometry.Scheme.Modules.Invertible.PowerPullback.pullbackPowerIso f L (n + 1)).hom =
      pullbackTensorMap f L.val (tensorPowerLineBundle T L n).val ≫
        tensorSheafMap S (𝟙 ((Scheme.Modules.pullback f).obj L.val))
          (AlgebraicGeometry.Scheme.Modules.Invertible.PowerPullback.pullbackPowerIso f L
              n).hom := rfl

theorem powerIso_succ_hom (S : Scheme.{u}) {L M : LineBundle S} (e : L.val ≅ M.val) (n : ℕ) :
    (AlgebraicGeometry.Scheme.Modules.Invertible.TrivializedPower.powerIso S e (n + 1)).hom =
      tensorSheafMap S e.hom
          (AlgebraicGeometry.Scheme.Modules.Invertible.TrivializedPower.powerIso S e n).hom := rfl

theorem unitPowerIso_succ_hom (S : Scheme.{u}) (n : ℕ) :
    (AlgebraicGeometry.Scheme.Modules.Invertible.UnitPower.unitPowerIso S (n + 1)).hom =
      (tensorSheafLeftUnit S (tensorPowerLineBundle S
          (AlgebraicGeometry.Scheme.Modules.Invertible.UnitPower.unitLineBundle S) n).val).hom ≫
        (AlgebraicGeometry.Scheme.Modules.Invertible.UnitPower.unitPowerIso S n).hom := rfl

/-- The successor tensor calculation for arbitrary actual module objects and maps.
Only the specified previous-stage morphism equality is used; no curve or recursive
isomorphism is unfolded in this reusable categorical calculation. -/
theorem tensor_iso_successor_step {S T : Scheme.{u}} (f : S ⟶ T)
    (M P N : SheafOfModules.{u} T.ringCatSheaf)
    (Q R : SheafOfModules.{u} S.ringCatSheaf) (a : P ≅ N)
    (g : (Scheme.Modules.pullback f).obj M ⟶ SheafOfModules.unit S.ringCatSheaf)
    (h : (Scheme.Modules.pullback f).obj N ⟶ SheafOfModules.unit S.ringCatSheaf)
    (b : (Scheme.Modules.pullback f).obj P ⟶ Q) (c : Q ⟶ R)
    (d : R ⟶ SheafOfModules.unit S.ringCatSheaf)
    (ih : (Scheme.Modules.pullback f).map a.hom ≫ h = b ≫ c ≫ d) :
    (Scheme.Modules.pullback f).map (tensorSheafIso T (Iso.refl M) a).hom ≫
      pullbackTensorMap f M N ≫ tensorSheafMap S g h ≫
        (tensorSheafLeftUnit S (SheafOfModules.unit S.ringCatSheaf)).hom =
      pullbackTensorMap f M P ≫
        tensorSheafMap S (𝟙 ((Scheme.Modules.pullback f).obj M)) b ≫
          tensorSheafMap S g c ≫ (tensorSheafLeftUnit S R).hom ≫ d := by
  change (Scheme.Modules.pullback f).map (tensorSheafMap T (𝟙 M) a.hom) ≫
    pullbackTensorMap f M N ≫ tensorSheafMap S g h ≫
      (tensorSheafLeftUnit S (SheafOfModules.unit S.ringCatSheaf)).hom = _
  rw [Scheme.Modules.pullbackTensorMap_naturality_assoc,
      Scheme.Modules.tensorSheafMap_comp_assoc]
  simp only [CategoryTheory.Functor.map_id, Category.id_comp]
  rw [ih, Scheme.Modules.tensorSheafMap_comp_assoc, Category.id_comp]
  rw [← AlgebraicGeometry.Scheme.Modules.Invertible.UnitPower.tensorSheafLeftUnit_naturality S
      d, Scheme.Modules.tensorSheafMap_comp_assoc]
  simp only [Category.comp_id, Category.assoc]

/-- Functorial composition on arbitrary module objects, retaining their native iso category. -/
theorem pullback_three_isos_tail {S T : Scheme.{u}} (f : S ⟶ T)
    {A B C D : SheafOfModules.{u} T.ringCatSheaf}
    (a₀ : A ≅ D) (a : A ≅ B) (b : B ≅ C) (c : C ≅ D)
    (ha : a₀ = a ≪≫ b ≪≫ c)
    (d : (Scheme.Modules.pullback f).obj D ⟶ SheafOfModules.unit S.ringCatSheaf)
    (e : (Scheme.Modules.pullback f).obj C ⟶ SheafOfModules.unit S.ringCatSheaf)
    (g : (Scheme.Modules.pullback f).obj B ⟶ SheafOfModules.unit S.ringCatSheaf)
    (hc : (Scheme.Modules.pullback f).map c.hom ≫ d = e)
    (hb : (Scheme.Modules.pullback f).map b.hom ≫ e = g) :
    (Scheme.Modules.pullback f).map a₀.hom ≫ d =
      (Scheme.Modules.pullback f).map a.hom ≫ g := by
  rw [ha]
  simp only [Iso.trans_hom, CategoryTheory.Functor.map_comp, Category.assoc]
  rw [hc, hb]

end AlgebraicGeometry.Scheme.Modules.Invertible.Power
