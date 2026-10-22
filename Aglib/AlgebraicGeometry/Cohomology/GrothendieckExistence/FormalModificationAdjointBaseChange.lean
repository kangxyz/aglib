/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.GrothendieckExistence.FormalPushforwardBaseChange
public import Aglib.AlgebraicGeometry.Modules.BaseChange.Adjoint

/-! # Base change retains the specified formal adjunction family

The right-hand family is built from the original upstairs formal isomorphism.
The equation includes the original quotient comparison and the original mate,
so it can be combined with whole-family uniqueness on affine overlaps.
-/

@[expose] public noncomputable section
open CategoryTheory Opposite
namespace AlgebraicGeometry.Scheme.Modules.Coherent
universe u
variable {R : Type u} [CommRing R]
  {X Y X' Y' : Scheme.{u}}
  [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
  [IsLocallyNoetherian X'] [IsLocallyNoetherian Y']
  (a : Y' ⟶ Y) (b : Y' ⟶ X') (p : Y ⟶ X) (g : X' ⟶ X)
  [IsProper p] [IsProper b]
  (h : IsPullback a b p g) (f : X ⟶ Spec (CommRingCat.of R)) (I : Ideal R)
  (F : AdicSystem X (idealThickeningIdealSheaf f I)) (G : Y.CoherentSheaf)
  (β : (baseIdealPullbackFunctor p f I).obj F ≅
    (completionFunctor Y (idealThickeningIdealSheaf (p ≫ f) I)).obj G)

local instance : G.obj.IsQuasicoherent :=
  QuasiCoherent.quasicoherent_of_affineCharts _ (fun B j _ => (G.property B j).1)

/-- Consume the whole formal comparison certificate inside the native adjunction.
No concrete scalar stage equality is separately restated. -/
private theorem adjointEquation_of_formalData
    {C D : Type*} [Category C] [Category D]
    {P : ObjectProperty (ℕᵒᵖ ⥤ D)} (S T : P.FullSubcategory)
    (N₀ N : ℕ → D)
    (a : ∀ n, S.obj.obj (op n) ⟶ N₀ n) (b : ∀ n, N₀ n ⟶ N n)
    (z : ∀ n, N n ⟶ T.obj.obj (op n))
    (c : {e : S ≅ T // ∀ n, e.hom.hom.app (op n) = a n ≫ b n ≫ z n})
    (R : D ⥤ C) (n : ℕ) {U V : C}
    (x : U ⟶ V) (y : V ⟶ R.obj (N n))
    (E₀ : (S.obj.obj (op n) ⟶ N n) ≃ (U ⟶ R.obj (N n)))
    (E₁ : (S.obj.obj (op n) ⟶ T.obj.obj (op n)) ≃
      (U ⟶ R.obj (T.obj.obj (op n))))
    (hm : x ≫ y = E₀ (a n ≫ b n))
    (hn : E₁ ((a n ≫ b n) ≫ z n) = E₀ (a n ≫ b n) ≫ R.map (z n)) :
    x ≫ y ≫ R.map (z n) = E₁ (c.val.hom.hom.app (op n)) := by
  rw [← Category.assoc, hm, ← hn, Category.assoc, ← c.property n]

omit [IsProper p] [IsProper b] in
/-- The original formal adjunction commutes with the native base-change mate.
The right side is the native adjoint of the actual transported formal iso. -/
theorem formalModificationAdjoint_baseChange (n : ℕ) :
    (pullback g).map ((formalModificationAdjoint p f I F _ β.hom).app (op n)) ≫
      (cartesianBaseChangeMap a b p g h).app
        ((idealSheafQuotientFunctor Y (idealThickeningIdealSheaf (p ≫ f) I ^ n)).obj G.obj) ≫
      (pushforward b).map
        (squarePullbackQuotientComparisonOfComm a b p g h.w f I G n).val.hom =
    (pullbackPushforwardAdjunction b).homEquiv
      ((pullback g).obj (F.obj.obj (op n)))
      (((completionFunctor Y' (idealThickeningIdealSheaf (b ≫ (g ≫ f)) I)).obj
        ((coherentPullback a).obj G)).obj.obj (op n))
      ((formalModificationBaseChangeFormalData a b p g h.w f I F G β).val.hom.hom.app
        (op n)) := by
  exact adjointEquation_of_formalData
    ((baseIdealPullbackFunctor b (g ≫ f) I).obj ((baseIdealPullbackFunctor g f I).obj F))
    ((completionFunctor Y' (idealThickeningIdealSheaf (b ≫ (g ≫ f)) I)).obj
      ((coherentPullback a).obj G))
    (fun k => (pullback a).obj ((pullback p).obj (F.obj.obj (op k))))
    (fun k => (pullback a).obj
      ((idealSheafQuotientFunctor Y (idealThickeningIdealSheaf (p ≫ f) I ^ k)).obj G.obj))
    (fun k => (pullbackSquareIso a b p g h.w).hom.app (F.obj.obj (op k)))
    (fun k => (pullback a).map (β.hom.hom.app (op k)))
    (fun k => (squarePullbackQuotientComparisonOfComm a b p g h.w f I G k).val.hom)
    (formalModificationBaseChangeFormalData a b p g h.w f I F G β)
    (pushforward b) n
    ((pullback g).map ((formalModificationAdjoint p f I F _ β.hom).app (op n)))
    ((cartesianBaseChangeMap a b p g h).app
      ((idealSheafQuotientFunctor Y (idealThickeningIdealSheaf (p ≫ f) I ^ n)).obj G.obj))
    ((pullbackPushforwardAdjunction b).homEquiv _ _)
    ((pullbackPushforwardAdjunction b).homEquiv _ _)
    (cartesianBaseChangeMap_adjoint a b p g h _ _ (β.hom.hom.app (op n)))
    ((pullbackPushforwardAdjunction b).homEquiv_naturality_right _ _)

end AlgebraicGeometry.Scheme.Modules.Coherent
