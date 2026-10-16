/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Adjunction.MateHomEquiv
public import Mathlib.CategoryTheory.Adjunction.Unique

/-!
# Adjunction comparisons and whiskered mates

Four actual adjunctions and a specified right-functor square identify the
original left-adjoint comparison on units. The remaining lemmas retain literal
conjugate/mate maps under isomorphism transport and whiskering.

Source: `R5Lab/AlgebraicGeometry/Curves/Degree/AffineModuleBaseChange.lean`, frozen R5 integration
`79307ff88f07d34fd5c3edb859f799c55e38f290`, SHA-256
`0739a4c1e7297a8f1dec99f8f53914339710e9240fa56c70a90ae2127581ed06`. Selected original ranges: [[581,
634], [986, 991], [1026, 1038], [1146, 1157], [1260, 1297]].
-/

@[expose] public section
noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option linter.style.haveILetI false

open CategoryTheory
namespace CategoryTheory
section
variable {C D A B : Type*} [Category* C] [Category* D] [Category* A] [Category* B]
  {Φ : D ⥤ C} {Γ : C ⥤ D} {Ψ : B ⥤ A} {Δ : A ⥤ B}
  {L : C ⥤ A} {R : A ⥤ C} {E : D ⥤ B} {G : B ⥤ D}
  (aY : Φ ⊣ Γ) (aX : Ψ ⊣ Δ) (af : L ⊣ R) (aE : E ⊣ G)
  (rIso : R ⋙ Γ ≅ Δ ⋙ G)

/-- The canonical left-adjoint uniqueness comparison for the displayed right-adjoint isomorphism. -/
def leftAdjointComparison : Φ ⋙ L ≅ E ⋙ Ψ :=
  Adjunction.leftAdjointUniq ((aY.comp af).ofNatIsoRight rIso) (aE.comp aX)

/-- The actual object comparison obtained from the two adjunction units and counits. -/
def adjunctionComparisonIso (N : C) [IsIso (aY.counit.app N)]
    [IsIso (aX.unit.app (E.obj (Γ.obj N)))] : Δ.obj (L.obj N) ≅ E.obj (Γ.obj N) :=
  Δ.mapIso (L.mapIso (asIso (aY.counit.app N)).symm ≪≫
    (leftAdjointComparison aY aX af aE rIso).app (Γ.obj N)) ≪≫
    (asIso (aX.unit.app (E.obj (Γ.obj N)))).symm

@[reassoc]
theorem adjunctionComparisonIso_unit (N : C) [IsIso (aY.counit.app N)]
    [IsIso (aX.unit.app (E.obj (Γ.obj N)))] :
    Γ.map (af.unit.app N) ≫ rIso.hom.app (L.obj N) ≫
      G.map (adjunctionComparisonIso aY aX af aE rIso N).hom = aE.unit.app (Γ.obj N) := by
  let ε := (asIso (aY.counit.app N)).inv
  let σ := leftAdjointComparison aY aX af aE rIso
  have hε : Γ.map ε = aY.unit.app (Γ.obj N) := by
    apply (cancel_mono (Γ.map (aY.counit.app N))).mp
    rw [← Γ.map_comp]
    change Γ.map ((asIso (aY.counit.app N)).inv ≫ (asIso (aY.counit.app N)).hom) = _
    rw [Iso.inv_hom_id, Γ.map_id, aY.right_triangle_components]
    rfl
  have hη := af.unit.naturality ε
  have hδ := rIso.hom.naturality (L.map ε)
  have hσ := Adjunction.unit_leftAdjointUniq_hom_app
    ((aY.comp af).ofNatIsoRight rIso) (aE.comp aX) (Γ.obj N)
  simp only [Adjunction.comp_unit_app, Adjunction.ofNatIsoRight, NatTrans.comp_app,
    Functor.whiskerLeft_app, Category.assoc] at hσ
  change aY.unit.app (Γ.obj N) ≫ Γ.map (af.unit.app (Φ.obj (Γ.obj N))) ≫
    rIso.hom.app (L.obj (Φ.obj (Γ.obj N))) ≫ G.map (Δ.map (σ.hom.app (Γ.obj N))) =
      aE.unit.app (Γ.obj N) ≫ G.map (aX.unit.app (E.obj (Γ.obj N))) at hσ
  change Γ.map (af.unit.app N) ≫ rIso.hom.app (L.obj N) ≫
    G.map (Δ.map (L.map ε ≫ σ.hom.app (Γ.obj N)) ≫
      (asIso (aX.unit.app (E.obj (Γ.obj N)))).inv) = _
  simp only [Functor.map_comp, Category.assoc]
  simp only [Functor.comp_map, Functor.id_obj] at hδ
  rw [← reassoc_of% hδ]
  simp only [Functor.comp_map, Functor.id_map, Functor.id_obj] at hη
  rw [← Γ.map_comp_assoc, ← hη, Γ.map_comp, hε]
  simp only [Category.assoc, Functor.comp_obj]
  rw [reassoc_of% hσ]
  rw [← G.map_comp]
  change aE.unit.app (Γ.obj N) ≫
    G.map ((asIso (aX.unit.app (E.obj (Γ.obj N)))).hom ≫
      (asIso (aX.unit.app (E.obj (Γ.obj N)))).inv) = _
  rw [Iso.hom_inv_id, G.map_id]
  exact Category.comp_id _

end

theorem isIso_of_iso_whiskers {C : Type*} [Category* C]
    {W X Y Z : C} (e : W ≅ X) (d : Y ≅ Z) (c : X ⟶ Y)
    (h : IsIso (e.hom ≫ c ≫ d.hom)) : IsIso c := by
  haveI : IsIso ((e.hom ≫ c) ≫ d.hom) := by simpa only [Category.assoc] using h
  haveI : IsIso (e.hom ≫ c) := (isIso_comp_right_iff (e.hom ≫ c) d.hom).mp inferInstance
  exact (isIso_comp_left_iff e.hom c).mp inferInstance

section AdjunctionTransport
variable {C D : Type*} [Category C] [Category D]
  {L₁ L₂ : C ⥤ D} {R₁ R₂ : D ⥤ C}

theorem conjugateEquiv_leftAdjointUniq_ofNatIsoRight_inv
    (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂) (e : R₁ ≅ R₂) :
    conjugateEquiv adj₁ adj₂
      (adj₁.leftAdjointUniq (adj₂.ofNatIsoRight e.symm)).inv = e.hom := by
  ext M
  apply (adj₂.homEquiv _ _).symm.injective
  rw [Adjunction.homEquiv_counit, conjugateEquiv_counit]
  rw [Adjunction.leftAdjointUniq_inv_app, Adjunction.leftAdjointUniq_hom_app_counit]
  rfl

end AdjunctionTransport

theorem conjugateEquiv_associator_inv
    {C₀ C₁ C₂ C₃ : Type*} [Category C₀] [Category C₁] [Category C₂] [Category C₃]
    {L₁ : C₀ ⥤ C₁} {R₁ : C₁ ⥤ C₀} {L₂ : C₁ ⥤ C₂} {R₂ : C₂ ⥤ C₁}
    {L₃ : C₂ ⥤ C₃} {R₃ : C₃ ⥤ C₂}
    (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂) (adj₃ : L₃ ⊣ R₃) :
    conjugateEquiv ((adj₁.comp adj₂).comp adj₃) (adj₁.comp (adj₂.comp adj₃))
      (Functor.associator _ _ _).inv = (Functor.associator _ _ _).inv := by
  apply (cancel_mono (Functor.associator _ _ _).hom).mp
  rw [← conjugateEquiv_associator_hom]
  rw [conjugateEquiv_comm _ _ (Iso.hom_inv_id (Functor.associator _ _ _)),
    conjugateEquiv_associator_hom]
  exact (Iso.inv_hom_id _).symm

section MateWhisker
variable {C₀ C₁ C₂ C₃ : Type*} [Category C₀] [Category C₁] [Category C₂] [Category C₃]
  {L₁ : C₀ ⥤ C₁} {R₁ : C₁ ⥤ C₀} {L₂ : C₂ ⥤ C₃} {R₂ : C₃ ⥤ C₂}
  {G G' : C₀ ⥤ C₂} {H H' : C₁ ⥤ C₃}
  (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂)

theorem mateEquiv_whiskerTop (α : TwoSquare G' L₁ L₂ H) (τ : G ⟶ G') :
    mateEquiv adj₁ adj₂ (α.whiskerTop τ) =
      (mateEquiv adj₁ adj₂ α).whiskerRight τ := by
  ext M
  simp only [mateEquiv_apply, TwoSquare.whiskerTop, TwoSquare.whiskerRight, TwoSquare.mk,
    TwoSquare.natTrans, NatTrans.comp_app, Functor.comp_obj,
    Functor.rightUnitor_inv_app, Functor.leftUnitor_hom_app,
    Functor.associator_hom_app, Functor.associator_inv_app,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, Functor.comp_map,
    Category.id_comp, Functor.map_comp, Category.assoc]
  rw [← adj₂.unit_naturality_assoc]

theorem mateEquiv_whiskerBottom (α : TwoSquare G L₁ L₂ H) (τ : H ⟶ H') :
    mateEquiv adj₁ adj₂ (α.whiskerBottom τ) =
      (mateEquiv adj₁ adj₂ α).whiskerLeft τ := by
  ext M
  simp only [mateEquiv_apply, TwoSquare.whiskerBottom, TwoSquare.whiskerLeft, TwoSquare.mk,
    TwoSquare.natTrans, NatTrans.comp_app, Functor.comp_obj,
    Functor.rightUnitor_inv_app, Functor.leftUnitor_hom_app,
    Functor.associator_hom_app, Functor.associator_inv_app,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, Functor.comp_map,
    Category.id_comp, Functor.map_comp, Category.assoc]
  erw [Category.comp_id, Category.id_comp]
  change adj₂.unit.app (G.obj (R₁.obj M)) ≫
    R₂.map (α.natTrans.app (R₁.obj M)) ≫ R₂.map (τ.app (L₁.obj (R₁.obj M))) ≫
      R₂.map (H'.map (adj₁.counit.app M)) =
    adj₂.unit.app (G.obj (R₁.obj M)) ≫ R₂.map (α.natTrans.app (R₁.obj M)) ≫
      R₂.map (H.map (adj₁.counit.app M)) ≫ R₂.map (τ.app M)
  rw [← R₂.map_comp, ← τ.naturality, R₂.map_comp]
  rfl
end MateWhisker


end CategoryTheory
