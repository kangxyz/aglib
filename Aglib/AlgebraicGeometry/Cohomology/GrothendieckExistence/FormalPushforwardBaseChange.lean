/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.GrothendieckExistence.FormalPushforwardComparison
public import Aglib.AlgebraicGeometry.Cohomology.GrothendieckExistence.FormalModificationBaseChange

/-! # The original formal pushforward comparison commutes with base change

The finite-stage square is proved on the original quotient unit, which is epi.
Neither finite-stage injectivity nor invertibility of the pushforward comparison
is used. The structural-ideal transport keeps its original unit equation.
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
  (G : Y.CoherentSheaf)

local instance : G.obj.IsQuasicoherent :=
  QuasiCoherent.quasicoherent_of_affineCharts _ (fun B j _ => (G.property B j).1)
local instance : ((pushforward p).obj G.obj).IsQuasicoherent :=
  QuasiCoherent.quasicoherent_of_affineCharts _
    (fun B j _ => ((properPushforwardCoefficient p G).property B j).1)

/-- The quotient pullback across the square, including its original unit law. -/
def squarePullbackQuotientComparison (n : ℕ) :=
  squarePullbackQuotientComparisonOfComm a b p g h.w f I G n

/-- Original-unit detection of the native mate square, before specialization. -/
theorem comparisonSquare_of_units
    {C D C' D' : Type*} [Category C] [Category D] [Category C'] [Category D']
    (P : D ⥤ C) (T : C ⥤ C') (H : D ⥤ D') (S : D' ⥤ C')
    (bc : P ⋙ T ⟶ H ⋙ S) {N Q : D} {A : C} {A' B' : C'} {Q' : D'}
    (u : P.obj N ⟶ A) (v : N ⟶ Q)
    (u₁ : T.obj (P.obj N) ⟶ A') (u₂ : S.obj (H.obj N) ⟶ B')
    (v' : H.obj N ⟶ Q') (ψ : A ⟶ P.obj Q) (ψ' : B' ⟶ S.obj Q')
    (c : T.obj A ⟶ A') (d : H.obj Q ⟶ Q') (k : A' ⟶ B')
    [Epi (T.map u)]
    (hψ : u ≫ ψ = P.map v) (hψ' : u₂ ≫ ψ' = S.map v')
    (hc : T.map u ≫ c = u₁) (hd : H.map v ≫ d = v')
    (hk : u₁ ≫ k = bc.app N ≫ u₂) :
    T.map ψ ≫ bc.app Q ≫ S.map d = c ≫ k ≫ ψ' := by
  apply (cancel_epi (T.map u)).mp
  calc
    T.map u ≫ T.map ψ ≫ bc.app Q ≫ S.map d =
        T.map (P.map v) ≫ bc.app Q ≫ S.map d := by
      rw [← Functor.map_comp_assoc, hψ]
    _ = bc.app N ≫ S.map (H.map v) ≫ S.map d := by
      have hn := bc.naturality v
      change T.map (P.map v) ≫ bc.app Q = bc.app N ≫ S.map (H.map v) at hn
      rw [← Category.assoc, hn, Category.assoc]
    _ = bc.app N ≫ S.map v' := by rw [← Functor.map_comp, hd]
    _ = T.map u ≫ c ≫ k ≫ ψ' := by
      rw [← Category.assoc, ← Category.assoc, hc, hk, Category.assoc, hψ']

/-- The actual pushforward comparison and the native base-change mate commute. -/
theorem formalPushforwardComparison_baseChange (n : ℕ) :
    (pullback g).map ((formalPushforwardComparison p f I G).app (op n)) ≫
      (cartesianBaseChangeMap a b p g h).app
        ((idealSheafQuotientFunctor Y (idealThickeningIdealSheaf (p ≫ f) I ^ n)).obj G.obj) ≫
      (pushforward b).map (squarePullbackQuotientComparison a b p g h f I G n).val.hom =
    (baseIdealPullbackQuotientIso g f I ((pushforward p).obj G.obj) n).hom ≫
      (idealSheafQuotientFunctor X' (idealThickeningIdealSheaf (g ≫ f) I ^ n)).map
        ((cartesianBaseChangeMap a b p g h).app G.obj) ≫
      (formalPushforwardComparison b (g ≫ f) I ((coherentPullback a).obj G)).app (op n) := by
  exact comparisonSquare_of_units (pushforward p) (pullback g) (pullback a)
    (pushforward b) (cartesianBaseChangeMap a b p g h)
    ((idealSheafQuotientUnit X (idealThickeningIdealSheaf f I ^ n)).app
      ((pushforward p).obj G.obj))
    ((idealSheafQuotientUnit Y (idealThickeningIdealSheaf (p ≫ f) I ^ n)).app G.obj)
    ((idealSheafQuotientUnit X' (idealThickeningIdealSheaf (g ≫ f) I ^ n)).app
      ((pullback g).obj ((pushforward p).obj G.obj)))
    ((idealSheafQuotientUnit X' (idealThickeningIdealSheaf (g ≫ f) I ^ n)).app
      ((pushforward b).obj ((pullback a).obj G.obj)))
    ((idealSheafQuotientUnit Y' (idealThickeningIdealSheaf (b ≫ (g ≫ f)) I ^ n)).app
      ((pullback a).obj G.obj))
    ((formalPushforwardComparison p f I G).app (op n))
    ((formalPushforwardComparison b (g ≫ f) I ((coherentPullback a).obj G)).app (op n))
    (baseIdealPullbackQuotientIso g f I ((pushforward p).obj G.obj) n).hom
    (squarePullbackQuotientComparison a b p g h f I G n).val.hom
    ((idealSheafQuotientFunctor X' (idealThickeningIdealSheaf (g ≫ f) I ^ n)).map
      ((cartesianBaseChangeMap a b p g h).app G.obj))
    (formalPushforwardComparison_unit p f I G n)
    (formalPushforwardComparison_unit b (g ≫ f) I ((coherentPullback a).obj G) n)
    (baseIdealPullbackQuotientIso_unit g f I ((pushforward p).obj G.obj) n)
    (squarePullbackQuotientComparison a b p g h f I G n).property
    ((idealSheafQuotientUnit X' (idealThickeningIdealSheaf (g ≫ f) I ^ n)).naturality
      ((cartesianBaseChangeMap a b p g h).app G.obj)).symm

end AlgebraicGeometry.Scheme.Modules.Coherent
