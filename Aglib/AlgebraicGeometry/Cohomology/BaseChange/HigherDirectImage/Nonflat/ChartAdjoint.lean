/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.BaseChange.HigherDirectImage.Nonflat.ChartCoefficient
public import Aglib.AlgebraicGeometry.Cohomology.BaseChange.HigherDirectImage.Nonflat.OpenSquareComposition

/-!
# The original adjoint of the restricted pullback unit

On a commuting pair of open charts, the coefficient obtained by restricting
the original geometric unit has its original adjoint equal to the inverse
native pullback/open-square comparison. In particular that adjoint is
invertible without a flatness or cartesian hypothesis on the square.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.Modules.Nonflat

/-- A double adjunction identifies the original adjoint from its unit equation,
without expanding the objects of any particular geometric functor. -/
private theorem doubleAdjoint_eq_of_unit
    {C₀ C₁ C₂ C₃ : Type*}
    [Category C₀] [Category C₁] [Category C₂] [Category C₃]
    {L₁ : C₀ ⥤ C₁} {R₁ : C₁ ⥤ C₀} {L₂ : C₁ ⥤ C₃} {R₂ : C₃ ⥤ C₁}
    {L₃ : C₀ ⥤ C₂} {R₃ : C₂ ⥤ C₀} {L₄ : C₂ ⥤ C₃} {R₄ : C₃ ⥤ C₂}
    (A₁ : L₁ ⊣ R₁) (A₂ : L₂ ⊣ R₂) (B₁ : L₃ ⊣ R₃) (B₂ : L₄ ⊣ R₄)
    (O : L₁ ⋙ L₂ ≅ L₃ ⋙ L₄) (C : R₂ ⋙ R₁ ≅ R₄ ⋙ R₃)
    (hC : conjugateEquiv (B₁.comp B₂) (A₁.comp A₂) O.hom = C.inv)
    (M : C₀) (φ : L₃.obj M ⟶ R₄.obj ((L₁ ⋙ L₂).obj M))
    (hφ : B₁.homEquiv M _ φ = (A₁.comp A₂).unit.app M ≫ C.hom.app _) :
    (B₂.homEquiv _ _).symm φ = O.inv.app M := by
  let A := A₁.comp A₂
  let B := B₁.comp B₂
  have hi : conjugateEquiv A B O.inv = C.hom := by
    apply (cancel_mono C.inv).mp
    rw [← hC, conjugateEquiv_comp, Iso.hom_inv_id, conjugateEquiv_id, hC,
      Iso.hom_inv_id]
  have ht : B.homEquiv _ _ (O.inv.app M) = A.unit.app M ≫ C.hom.app _ := by
    rw [Adjunction.homEquiv_unit]
    simpa only [hi] using (unit_conjugateEquiv A B O.inv M).symm
  have hB : B.homEquiv _ _ (O.inv.app M) =
      B₁.homEquiv _ _ (B₂.homEquiv _ _ (O.inv.app M)) := by
    simp only [B, Adjunction.comp_homEquiv]
    rfl
  apply (B₂.homEquiv _ _).injective
  rw [Equiv.apply_symm_apply]
  apply (B₁.homEquiv _ _).injective
  exact hφ.trans (ht.symm.trans hB)

/-- The genuine pullback adjoint of the original unit restricted to open
charts is exactly the inverse native pullback-square comparison. -/
theorem chartCoefficient_pullbackUnit_adjoint
    {X Y U V : Scheme.{u}}
    (p : Y ⟶ X) (a : U ⟶ X) (c : V ⟶ Y) (q : V ⟶ U)
    [IsOpenImmersion a] [IsOpenImmersion c] (w : q ≫ a = c ≫ p)
    (M : X.Modules) :
    ((pullbackPushforwardAdjunction q).homEquiv _ _).symm
        (chartCoefficient p a c q w ((pullbackPushforwardAdjunction p).unit.app M)) =
      (pullbackOpenSquare c q p a w.symm).inv.app M := by
  simp only [Functor.id_obj]
  let O := pullbackOpenSquare c q p a w.symm
  let C : pushforward c ⋙ pushforward p ≅ pushforward q ⋙ pushforward a :=
    pushforwardComp c p ≪≫ pushforwardCongr w.symm ≪≫ (pushforwardComp q a).symm
  have hC : conjugateEquiv
      ((restrictAdjunction a).comp (pullbackPushforwardAdjunction q))
      ((pullbackPushforwardAdjunction p).comp (restrictAdjunction c)) O.hom = C.inv := by
    simpa only [C, Iso.trans_inv, Iso.symm_inv, Category.assoc] using
      pullbackOpenSquare_conjugate_hom c q p a w.symm
  apply doubleAdjoint_eq_of_unit (pullbackPushforwardAdjunction p) (restrictAdjunction c)
    (restrictAdjunction a) (pullbackPushforwardAdjunction q) O C hC M
  rw [Adjunction.homEquiv_unit, chartCoefficient_unit]
  simp only [C, Adjunction.comp_unit_app, Iso.trans_hom, Iso.symm_hom,
    NatTrans.comp_app, Functor.comp_obj, Category.assoc]

/-- The original restricted-unit coefficient has an invertible original
pullback adjoint on every commuting pair of open charts. -/
theorem chartCoefficient_pullbackUnit_adjoint_isIso
    {X Y U V : Scheme.{u}}
    (p : Y ⟶ X) (a : U ⟶ X) (c : V ⟶ Y) (q : V ⟶ U)
    [IsOpenImmersion a] [IsOpenImmersion c] (w : q ≫ a = c ≫ p)
    (M : X.Modules) :
    IsIso (((pullbackPushforwardAdjunction q).homEquiv _ _).symm
      (chartCoefficient p a c q w ((pullbackPushforwardAdjunction p).unit.app M))) := by
  rw [chartCoefficient_pullbackUnit_adjoint]
  infer_instance

end AlgebraicGeometry.Scheme.Modules.Nonflat
