/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Finite.ModuleComparison

/-! # The original finite module counit and canonical abelian trace -/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.EtaleCohomology

open Coefficients

attribute [local instance] hasSheafifyLarge hasSheafifyModules

private theorem counit_underlying_of_left_comparison
    {A : Type*} {B : Type*} {C : Type*} {D : Type*}
    [Category* A] [Category* B] [Category* C] [Category* D]
    {L₁ P₁ : A ⥤ B} {R₁ : B ⥤ A} {L₂ P₂ : C ⥤ D} {R₂ : D ⥤ C}
    {U : A ⥤ C} {V : B ⥤ D}
    (a : L₁ ⊣ R₁) (b : L₂ ⊣ R₂) (a' : P₁ ⊣ R₁) (b' : P₂ ⊣ R₂)
    (κ : L₁ ⟶ P₁) (α : L₂ ⟶ P₂)
    (e : L₁ ⋙ V ≅ U ⋙ L₂) (s : P₁ ⋙ V ≅ U ⋙ P₂)
    (r : R₁ ⋙ U ≅ V ⋙ R₂)
    (h : (mateEquiv a b (TwoSquare.mk _ _ _ _ e.inv)).natTrans = r.hom)
    (hk : Functor.whiskerRight κ V =
      e.hom ≫ Functor.whiskerLeft U α ≫ s.inv)
    (ha : a'.unit = a.unit ≫ Functor.whiskerRight κ R₁)
    (hb : b.unit ≫ Functor.whiskerRight α R₂ = b'.unit) (N : B) :
    V.map (a'.counit.app N) = s.hom.app (R₁.obj N) ≫
      P₂.map (r.hom.app N) ≫ b'.counit.app (V.obj N) := by
  have hm : (mateEquiv a' b' (TwoSquare.mk _ _ _ _ s.inv)).natTrans = r.hom := by
    apply mateEquiv_inv_natTrans_eq_of_unit a' b' s r.hom
    intro M
    have hunit := NatTrans.congr_app ha M
    have hα := NatTrans.congr_app hb (U.obj M)
    have hk' := NatTrans.congr_app hk M
    have hn := r.hom.naturality (κ.app M)
    have hu := Adjunction.underlying_unit_app a b e r h M
    simp only [NatTrans.comp_app, Functor.whiskerRight_app,
      Functor.whiskerLeft_app] at hunit hα hk'
    dsimp only [Functor.comp_obj, Functor.comp_map, Functor.id_obj] at hn
    have hc : V.map (κ.app M) ≫ s.hom.app M =
        e.hom.app M ≫ α.app (U.obj M) := by
      rw [hk']
      simp only [Category.assoc, Iso.inv_hom_id_app, Category.comp_id]
    calc
      U.map (a'.unit.app M) ≫ r.hom.app (P₁.obj M) ≫ R₂.map (s.hom.app M) =
          U.map (a.unit.app M) ≫ U.map (R₁.map (κ.app M)) ≫
            r.hom.app (P₁.obj M) ≫ R₂.map (s.hom.app M) := by
        rw [hunit, U.map_comp, Category.assoc]
      _ = U.map (a.unit.app M) ≫ r.hom.app (L₁.obj M) ≫
          R₂.map (V.map (κ.app M)) ≫ R₂.map (s.hom.app M) := by
        rw [reassoc_of% hn]
      _ = U.map (a.unit.app M) ≫ r.hom.app (L₁.obj M) ≫
          R₂.map (e.hom.app M) ≫ R₂.map (α.app (U.obj M)) := by
        rw [← R₂.map_comp, hc, R₂.map_comp]
      _ = b.unit.app (U.obj M) ≫ R₂.map (α.app (U.obj M)) := by
        rw [reassoc_of% hu]
      _ = b'.unit.app (U.obj M) := hα
  exact Adjunction.underlying_counit_app a' b' s r hm N

variable {Y X : Scheme.{u}} (f : Y ⟶ X) [Etale f] [IsSeparated f] (n : ℕ)
  [IsFinite f] (d : ℕ) (hd : ∀ x : X, f.finrank x = d)

include d hd

/-- The counit transported through the SAME module comparison is the original
canonical finite-etale SUM underneath. This is a whole map equation for every
actual module coefficient, before any cohomology or scalar evaluation. -/
theorem moduleFiniteEtaleDirectImageAdjunction_counit_underlying
    (M : ModuleSheaf X (ULift.{u + 1} (ZMod n))) :
    (SheafOfModules.toSheaf (constantRing X (ULift.{u + 1} (ZMod n)))).map
        ((moduleFiniteEtaleDirectImageAdjunction f n d hd).counit.app M) =
      (moduleDirectImageUnderlyingIso f (ULift.{u + 1} (ZMod n))).hom.app
          ((moduleInverseImage f (ULift.{u + 1} (ZMod n))).obj M) ≫
        (directImage f).map ((moduleInverseImageUnderlyingIso
          (ULift.{u + 1} (ZMod n)) f).hom.app M) ≫
        (finiteEtaleSheafTrace (Scheme.FiniteEtale.mk f) d hd).app
          ((SheafOfModules.toSheaf (constantRing X (ULift.{u + 1} (ZMod n)))).obj M) := by
  have hk := moduleEtaleLowerShriekToDirectImage_underlying f n
  have ha : (moduleFiniteEtaleDirectImageAdjunction f n d hd).unit =
      (moduleLowerShriekAdjunction f (ULift.{u + 1} (ZMod n))).unit ≫
        Functor.whiskerRight (moduleEtaleLowerShriekToDirectImage f n)
          (moduleInverseImage f (ULift.{u + 1} (ZMod n))) := rfl
  have hb := etaleLowerShriekToDirectImage_unit f
  exact counit_underlying_of_left_comparison
    (moduleLowerShriekAdjunction f (ULift.{u + 1} (ZMod n)))
    (etaleLowerShriekAdjunction f)
    (moduleFiniteEtaleDirectImageAdjunction f n d hd)
    (finiteEtaleDirectImageAdjunction (Scheme.FiniteEtale.mk f) d hd)
    (moduleEtaleLowerShriekToDirectImage f n) (etaleLowerShriekToDirectImage f)
    (moduleLowerShriekUnderlyingIso f (ULift.{u + 1} (ZMod n)))
    (moduleDirectImageUnderlyingIso f (ULift.{u + 1} (ZMod n)))
    (moduleInverseImageUnderlyingIso (ULift.{u + 1} (ZMod n)) f)
    (mate_moduleLowerShriekUnderlyingIso_inv f (ULift.{u + 1} (ZMod n))) hk ha hb M


end AlgebraicGeometry.Scheme.EtaleCohomology
