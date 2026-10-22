/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.GrothendieckExistence.FormalPushforwardBaseChange

/-! # Original pushforward diagram base change from whole unit certificates -/

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

local instance originalDiagramBaseChangeCoefficientQuasicoherent : G.obj.IsQuasicoherent :=
  QuasiCoherent.quasicoherent_of_affineCharts _ (fun B j _ => (G.property B j).1)
local instance originalDiagramBaseChangePushforwardQuasicoherent :
    ((pushforward p).obj G.obj).IsQuasicoherent :=
  QuasiCoherent.quasicoherent_of_affineCharts _
    (fun B j _ => ((properPushforwardCoefficient p G).property B j).1)

/-- Detect the whole native mate square from original diagram/unit packets,
projecting certificates only while all quotient objects remain abstract. -/
theorem diagramSquare_of_unitPackets
    {C D C' D' : Type*} [Category C] [Category D] [Category C'] [Category D']
    (P : D ⥤ C) (T : C ⥤ C') (H : D ⥤ D') (S : D' ⥤ C')
    (bc : P ⋙ T ⟶ H ⋙ S) (N : D)
    (A : ℕᵒᵖ ⥤ C) (Q : ℕᵒᵖ ⥤ D) (A' B' : ℕᵒᵖ ⥤ C') (Q' : ℕᵒᵖ ⥤ D')
    (u : ∀ n, P.obj N ⟶ A.obj (op n)) (v : ∀ n, N ⟶ Q.obj (op n))
    (u₁ : ∀ n, T.obj (P.obj N) ⟶ A'.obj (op n))
    (u₂ : ∀ n, S.obj (H.obj N) ⟶ B'.obj (op n))
    (v' : ∀ n, H.obj N ⟶ Q'.obj (op n))
    (cψ : {ψ : A ⟶ Q ⋙ P // ∀ n, u n ≫ ψ.app (op n) = P.map (v n)})
    (cψ' : {ψ : B' ⟶ Q' ⋙ S // ∀ n, u₂ n ≫ ψ.app (op n) = S.map (v' n)})
    (cc : {e : A ⋙ T ≅ A' // ∀ n, T.map (u n) ≫ e.hom.app (op n) = u₁ n})
    (ck : {k : A' ⟶ B' // ∀ n, u₁ n ≫ k.app (op n) = bc.app N ≫ u₂ n})
    (d : ∀ n, {e : H.obj (Q.obj (op n)) ≅ Q'.obj (op n) //
      H.map (v n) ≫ e.hom = v' n})
    (hu : ∀ n, Epi (T.map (u n))) (n : ℕ) :
    T.map (cψ.val.app (op n)) ≫ bc.app (Q.obj (op n)) ≫ S.map (d n).val.hom =
      cc.val.hom.app (op n) ≫ ck.val.app (op n) ≫ cψ'.val.app (op n) := by
  let := hu n
  exact comparisonSquare_of_units P T H S bc (u n) (v n) (u₁ n) (u₂ n) (v' n)
    (cψ.val.app (op n)) (cψ'.val.app (op n)) (cc.val.hom.app (op n)) (d n).val.hom
    (ck.val.app (op n)) (cψ.property n) (cψ'.property n) (cc.property n)
    (d n).property (ck.property n)

/-- Original raw completion diagram square for the native proper-pushforward mate. -/
theorem pullbackCompletionComparison_square (n : ℕ) :
    (pullback g).map ((formalPushforwardComparisonData p f I G).val.app (op n)) ≫
      (cartesianBaseChangeMap a b p g h).app
        ((idealSheafQuotientFunctor Y (idealThickeningIdealSheaf (p ≫ f) I ^ n)).obj
          G.obj) ≫ (pushforward b).map
            (squarePullbackQuotientComparison a b p g h f I G n).val.hom =
    (pullbackCompletionDiagramComparison g f I
      (properPushforwardCoefficient p G)).val.hom.app (op n) ≫
      (idealSheafQuotientTowerHom X' (idealThickeningIdealSheaf (g ≫ f) I)
        ((cartesianBaseChangeMap a b p g h).app G.obj)).app (op n) ≫
      (formalPushforwardComparisonData b (g ≫ f) I
        ((coherentPullback a).obj G)).val.app (op n) := by
  exact diagramSquare_of_unitPackets (pushforward p) (pullback g) (pullback a)
    (pushforward b) (cartesianBaseChangeMap a b p g h) G.obj
    (idealSheafQuotientTower X (idealThickeningIdealSheaf f I) ((pushforward p).obj G.obj))
    (idealSheafQuotientTower Y (idealThickeningIdealSheaf (p ≫ f) I) G.obj)
    (idealSheafQuotientTower X' (idealThickeningIdealSheaf (g ≫ f) I)
      ((pullback g).obj ((pushforward p).obj G.obj)))
    (idealSheafQuotientTower X' (idealThickeningIdealSheaf (g ≫ f) I)
      ((pushforward b).obj ((pullback a).obj G.obj)))
    (idealSheafQuotientTower Y' (idealThickeningIdealSheaf (b ≫ (g ≫ f)) I)
      ((pullback a).obj G.obj))
    (fun k => (idealSheafQuotientUnit X (idealThickeningIdealSheaf f I ^ k)).app
      ((pushforward p).obj G.obj))
    (fun k => (idealSheafQuotientUnit Y (idealThickeningIdealSheaf (p ≫ f) I ^ k)).app
      G.obj)
    (fun k => (idealSheafQuotientUnit X' (idealThickeningIdealSheaf (g ≫ f) I ^ k)).app
      ((pullback g).obj ((pushforward p).obj G.obj)))
    (fun k => (idealSheafQuotientUnit X' (idealThickeningIdealSheaf (g ≫ f) I ^ k)).app
      ((pushforward b).obj ((pullback a).obj G.obj)))
    (fun k => (idealSheafQuotientUnit Y'
      (idealThickeningIdealSheaf (b ≫ (g ≫ f)) I ^ k)).app ((pullback a).obj G.obj))
    (formalPushforwardComparisonData p f I G)
    (formalPushforwardComparisonData b (g ≫ f) I ((coherentPullback a).obj G))
    (pullbackCompletionDiagramComparison g f I (properPushforwardCoefficient p G))
    (quotientTowerMapComparison (idealThickeningIdealSheaf (g ≫ f) I)
      ((cartesianBaseChangeMap a b p g h).app G.obj))
    (fun k => squarePullbackQuotientComparison a b p g h f I G k)
    (fun k => by
      let : Epi ((idealSheafQuotientUnit X
          (idealThickeningIdealSheaf f I ^ k)).app ((pushforward p).obj G.obj)) :=
        pullbackPushforwardUnit_epi
          (idealThickeningIdealSheaf f I ^ k).subschemeι ((pushforward p).obj G.obj)
      exact (pullback g).map_epi
        ((idealSheafQuotientUnit X (idealThickeningIdealSheaf f I ^ k)).app
          ((pushforward p).obj G.obj))) n

end AlgebraicGeometry.Scheme.Modules.Coherent
