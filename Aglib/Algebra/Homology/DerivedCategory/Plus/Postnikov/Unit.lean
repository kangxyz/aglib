/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.DerivedCategory.Plus.Postnikov.Layers
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact

/-!
# Postnikov triangles retaining a specified unit

An actual map from a degree-zero single to a nonnegative object, inducing
an isomorphism on original H0, identifies that single with the native
degree-zero truncation. Transporting the native truncation triangle retains
the specified map as its literal first arrow. For a two-layer object the
last term is the single of its original H1, with the original connecting
morphism retained. The degree-one homology sequence also supplies the raw
short exact sequence used by low-degree Leray.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

universe u v w

namespace DerivedCategory.Plus

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]

/-- The native lift of a specified H0-isomorphism to the degree-zero
truncation is invertible. -/
theorem isIso_liftTruncLT_of_isIso_homology_zero {M : C} {K : Plus C} [K.IsGE 0]
    (u : (singleFunctor C 0).obj M ⟶ K)
    [IsIso ((homologyFunctor C 0).map u)] :
    IsIso (TStructure.t.liftTruncLT u 0 1 rfl) := by
  let a := TStructure.t.liftTruncLT u 0 1 rfl
  let L := (TStructure.t.truncLT 1).obj K
  let : L.IsGE 0 := by dsimp [L]; infer_instance
  let : L.IsLE 0 := TStructure.t.isLE_truncLT_obj K 1 0 (by omega)
  apply (isIso_iff a).mpr
  intro n
  by_cases hn : n = 0
  · subst n
    let H := homologyFunctor C 0
    let i := (TStructure.t.truncLTι 1).app K
    let : IsIso (H.map i) := isIso_homology_truncLTι K 1 0 (by omega)
    have he : H.map a ≫ H.map i = H.map u := by
      rw [← H.map_comp]
      exact congrArg H.map (TStructure.t.liftTruncLT_ι u 0 1 rfl)
    have : IsIso (H.map a ≫ H.map i) := by rw [he]; infer_instance
    exact IsIso.of_isIso_comp_right (H.map a) (H.map i)
  · rcases lt_or_gt_of_ne hn with hn | hn
    · exact (isZero_homology_of_isGE ((singleFunctor C 0).obj M) 0 n hn).isIso
        (isZero_homology_of_isGE L 0 n hn) _
    · exact (isZero_homology_of_isLE ((singleFunctor C 0).obj M) 0 n hn).isIso
        (isZero_homology_of_isLE L 0 n hn) _

/-- The actual lift of the specified unit, with its native truncation target. -/
def unitTruncationIso {M : C} {K : Plus C} [K.IsGE 0]
    (u : (singleFunctor C 0).obj M ⟶ K)
    [IsIso ((homologyFunctor C 0).map u)] :
    (singleFunctor C 0).obj M ≅ (TStructure.t.truncLT 1).obj K := by
  let := isIso_liftTruncLT_of_isIso_homology_zero u
  exact asIso (TStructure.t.liftTruncLT u 0 1 rfl)

/-- The native truncation inclusion recovers the specified original unit. -/
@[reassoc]
theorem unitTruncationIso_hom_ι {M : C} {K : Plus C} [K.IsGE 0]
    (u : (singleFunctor C 0).obj M ⟶ K)
    [IsIso ((homologyFunctor C 0).map u)] :
    (unitTruncationIso u).hom ≫ (TStructure.t.truncLTι 1).app K = u :=
  TStructure.t.liftTruncLT_ι u 0 1 rfl

/-- The specified unit is the literal first arrow; the third object is
the original positive truncation, with no positive upper bound assumed. -/
def unitTruncationTriangle {M : C} {K : Plus C} [K.IsGE 0]
    (u : (singleFunctor C 0).obj M ⟶ K)
    [IsIso ((homologyFunctor C 0).map u)] : Triangle (Plus C) :=
  Triangle.mk u ((TStructure.t.truncGEπ 1).app K)
    ((TStructure.t.truncGEδLT 1).app K ≫ (unitTruncationIso u).inv⟦(1 : ℤ)⟧')

/-- Cancellation of the original shifted inverse, at a typed arrow boundary. -/
theorem shifted_inv_hom_cancel {L M N : Plus C} (e : L ≅ M)
    (δ : N ⟶ M⟦(1 : ℤ)⟧) :
    (δ ≫ e.inv⟦(1 : ℤ)⟧') ≫ e.hom⟦(1 : ℤ)⟧' = δ := by
  rw [Category.assoc, ← Functor.map_comp, Iso.inv_hom_id,
    (shiftFunctor (Plus C) (1 : ℤ)).map_id, Category.comp_id]

/-- This comparison transports only the first object along the proved
native lift of the same specified unit. -/
def unitTruncationTriangleIso {M : C} {K : Plus C} [K.IsGE 0]
    (u : (singleFunctor C 0).obj M ⟶ K)
    [IsIso ((homologyFunctor C 0).map u)] :
    unitTruncationTriangle u ≅ (TStructure.t.triangleLTGE 1).obj K := by
  refine Triangle.isoMk _ _ (unitTruncationIso u) (Iso.refl _) (Iso.refl _) ?_ ?_ ?_
  · change u ≫ 𝟙 K = (unitTruncationIso u).hom ≫ (TStructure.t.truncLTι 1).app K
    rw [Category.comp_id, unitTruncationIso_hom_ι]
  · change (TStructure.t.truncGEπ 1).app K ≫ 𝟙 _ =
      𝟙 K ≫ (TStructure.t.truncGEπ 1).app K
    rw [Category.comp_id, Category.id_comp]
  · change ((TStructure.t.truncGEδLT 1).app K ≫
      (unitTruncationIso u).inv⟦(1 : ℤ)⟧') ≫ (unitTruncationIso u).hom⟦(1 : ℤ)⟧' =
        𝟙 _ ≫ (TStructure.t.truncGEδLT 1).app K
    exact (shifted_inv_hom_cancel (unitTruncationIso u) ((TStructure.t.truncGEδLT 1).app K)).trans
      (Category.id_comp _).symm

/-- The triangle retains the native distinguishedness witness. -/
theorem unitTruncationTriangle_distinguished {M : C} {K : Plus C} [K.IsGE 0]
    (u : (singleFunctor C 0).obj M ⟶ K)
    [IsIso ((homologyFunctor C 0).map u)] :
    unitTruncationTriangle u ∈ distTriang _ :=
  (distinguished_iff_of_iso (unitTruncationTriangleIso u)).mpr
    (TStructure.t.triangleLTGE_distinguished 1 K)

/-- The positive truncation of a two-layer object is its original H1
single, normalized by the original projection on H1. -/
def positiveLayerIso (K : Plus C) [K.IsLE 1] :
    (TStructure.t.truncGE 1).obj K ≅ (singleFunctor C 1).obj
      ((homologyFunctor C 1).obj K) :=
  isoSingleHomology ((TStructure.t.truncGE 1).obj K) 1 ≪≫
    (singleFunctor C 1).mapIso (homologyTruncGEIso K 1 1 le_rfl).symm

/-- The two-layer triangle retains the specified unit and the original
connecting morphism. No splitting is asserted. -/
def unitPostnikovTriangle {M : C} {K : Plus C} [K.IsGE 0] [K.IsLE 1]
    (u : (singleFunctor C 0).obj M ⟶ K)
    [IsIso ((homologyFunctor C 0).map u)] : Triangle (Plus C) :=
  Triangle.mk u
    ((TStructure.t.truncGEπ 1).app K ≫ (positiveLayerIso K).hom)
    ((positiveLayerIso K).inv ≫ (unitTruncationTriangle u).mor₃)

/-- The last-object comparison preserves the same unit and boundary map. -/
def unitPostnikovTriangleIso {M : C} {K : Plus C} [K.IsGE 0] [K.IsLE 1]
    (u : (singleFunctor C 0).obj M ⟶ K)
    [IsIso ((homologyFunctor C 0).map u)] :
    unitPostnikovTriangle u ≅ unitTruncationTriangle u := by
  refine Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) (positiveLayerIso K).symm ?_ ?_ ?_
  · change u ≫ 𝟙 K = 𝟙 _ ≫ u
    rw [Category.comp_id, Category.id_comp]
  · change ((TStructure.t.truncGEπ 1).app K ≫ (positiveLayerIso K).hom) ≫
      (positiveLayerIso K).inv = 𝟙 K ≫ (TStructure.t.truncGEπ 1).app K
    rw [Category.assoc, Iso.hom_inv_id, Category.comp_id, Category.id_comp]
  · let δ : (TStructure.t.truncGE 1).obj K ⟶ ((singleFunctor C 0).obj M)⟦(1 : ℤ)⟧ :=
      (TStructure.t.truncGEδLT 1).app K ≫ (unitTruncationIso u).inv⟦(1 : ℤ)⟧'
    change ((positiveLayerIso K).inv ≫ δ) ≫
      (shiftFunctor (Plus C) (1 : ℤ)).map (𝟙 ((singleFunctor C 0).obj M)) =
        (positiveLayerIso K).inv ≫ δ
    rw [(shiftFunctor (Plus C) (1 : ℤ)).map_id, Category.comp_id]

/-- The two-layer triangle is the original distinguished triangle transported
through its normalized homology layer. -/
theorem unitPostnikovTriangle_distinguished {M : C} {K : Plus C}
    [K.IsGE 0] [K.IsLE 1] (u : (singleFunctor C 0).obj M ⟶ K)
    [IsIso ((homologyFunctor C 0).map u)] :
    unitPostnikovTriangle u ∈ distTriang _ :=
  (distinguished_iff_of_iso (unitPostnikovTriangleIso u)).mpr
    (unitTruncationTriangle_distinguished u)

/-- The actual first homology maps of a distinguished triangle form a short complex. -/
def homologyOneShortComplex (T : Triangle (Plus C)) (hT : T ∈ distTriang _) :
    ShortComplex C :=
  ShortComplex.mk ((homologyFunctor C 1).map T.mor₁)
    ((homologyFunctor C 1).map T.mor₂)
    ((homologyFunctor C 0).homologySequence_comp T hT 1)

/-- Exactly the two adjacent vanishings used by low-degree Leray make
the original degree-one homology complex short exact. -/
theorem homologyOneShortComplex_shortExact (T : Triangle (Plus C)) (hT : T ∈ distTriang _)
    (h₀ : IsZero ((homologyFunctor C 0).obj T.obj₃))
    (h₂ : IsZero ((homologyFunctor C 2).obj T.obj₁)) :
    (homologyOneShortComplex T hT).ShortExact := by
  let H := homologyFunctor C 0
  refine { exact := H.homologySequence_exact₂ T hT 1, mono_f := ?_, epi_g := ?_ }
  · change Mono ((homologyFunctor C 1).map T.mor₁)
    exact (H.homologySequence_mono_shift_map_mor₁_iff T hT 0 1 (by omega)).mpr
      (h₀.eq_of_src _ _)
  · change Epi ((homologyFunctor C 1).map T.mor₂)
    exact (H.homologySequence_epi_shift_map_mor₂_iff T hT 1 2 (by omega)).mpr
      (h₂.eq_of_tgt _ _)

end DerivedCategory.Plus
