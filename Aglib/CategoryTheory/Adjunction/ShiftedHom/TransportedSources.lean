/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Adjunction.ShiftedHom.RightComposition

/-! Original source and target transports for the shifted mate. -/

open CategoryTheory

@[expose] public noncomputable section

namespace CategoryTheory.Adjunction

variable {C D : Type*} [Category* C] [Category* D]
  {M : Type*} [AddMonoid M] [HasShift C M] [HasShift D M]
  {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R) [R.CommShift M]

/-- The original shifted adjunct retains ordinary source precomposition. -/
theorem shiftedHomEquiv_precomp {I I' : C} {K : D} {q : M}
    (a : I' ⟶ I) (x : ShiftedHom (L.obj I) K q) :
    adj.shiftedHomEquiv q I' K (L.map a ≫ x) = a ≫ adj.shiftedHomEquiv q I K x := by
  simp only [Adjunction.shiftedHomEquiv_apply, Adjunction.homEquiv_naturality_left, Category.assoc]

/-- The original shifted adjunct retains ordinary target postcomposition. -/
theorem shiftedHomEquiv_postcomp_shift {I : C} {K K' : D} {q : M}
    (x : ShiftedHom (L.obj I) K q) (b : K ⟶ K') :
    adj.shiftedHomEquiv q I K' (x ≫ b⟦q⟧') =
      adj.shiftedHomEquiv q I K x ≫ (R.map b)⟦q⟧' := by
  have h := adj.shiftedHomEquiv_postcomp x (ShiftedHom.mk₀ 0 rfl b) (zero_add q)
  rw [ShiftedHom.comp_mk₀, ShiftedHom.map_mk₀, ShiftedHom.comp_mk₀] at h
  exact h

end CategoryTheory.Adjunction

namespace CategoryTheory

variable {A B C D M : Type*} [Category* A] [Category* B] [Category* C] [Category* D]
  [AddMonoid M] [HasShift A M] [HasShift B M] [HasShift C M] [HasShift D M]
  {L₁ : A ⥤ B} {R₁ : B ⥤ A} {L₂ : C ⥤ D} {R₂ : D ⥤ C}
  {U : A ⥤ C} {V : B ⥤ D}
  [R₁.CommShift M] [R₂.CommShift M] [U.CommShift M] [V.CommShift M]

/-- The actual mate on shifted classes retains its given source and target maps. -/
theorem shiftedHomEquiv_of_mate_of_transported_sources
    (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂)
    (s : TwoSquare U L₁ L₂ V) (d : R₁ ⋙ U ⟶ V ⋙ R₂)
    [NatTrans.CommShift d M] (hd : (mateEquiv adj₁ adj₂ s).natTrans = d)
    {I : A} {I' : C} {J K : B} {J' K' : D}
    (e : L₁.obj I ⟶ J) (e' : L₂.obj I' ⟶ J')
    (u : I' ⟶ U.obj I) (v : J' ⟶ V.obj J) (t : V.obj K ⟶ K')
    {q : M} (x : ShiftedHom J K q) (y : ShiftedHom J' K' q)
    (hs : L₂.map u ≫ s.app I ≫ V.map e = e' ≫ v)
    (hy : y = v ≫ x.map V ≫ t⟦q⟧') :
    adj₂.shiftedHomEquiv q I' K' (e' ≫ y) =
      u ≫ (adj₁.shiftedHomEquiv q I K (e ≫ x)).map U ≫
        (d.app K ≫ R₂.map t)⟦q⟧' := by
  let z := adj₁.shiftedHomEquiv q I K (e ≫ x)
  have hmate := shiftedHomEquiv_of_mate adj₁ adj₂ s d hd I K q (e ≫ x)
  have hmap : ShiftedHom.map (e ≫ x : ShiftedHom (L₁.obj I) K q) V =
      V.map e ≫ x.map V := by
    simp only [ShiftedHom.map, Functor.map_comp, Category.assoc]
  have he : e' ≫ y = (L₂.map u ≫ (s.app I ≫
      ShiftedHom.map (e ≫ x : ShiftedHom (L₁.obj I) K q) V)) ≫ t⟦q⟧' := by
    rw [hy, hmap]
    simpa only [Category.assoc] using congrArg (fun z' => z' ≫ x.map V ≫ t⟦q⟧') hs.symm
  rw [he, adj₂.shiftedHomEquiv_postcomp_shift, adj₂.shiftedHomEquiv_precomp, ← hmate]
  change (u ≫ z.map U ≫ (d.app K)⟦q⟧') ≫ (R₂.map t)⟦q⟧' =
    u ≫ z.map U ≫ (d.app K ≫ R₂.map t)⟦q⟧'
  simp only [Functor.map_comp, Category.assoc]

end CategoryTheory
