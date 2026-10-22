/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.GrothendieckExistence.AffineModificationUniformBound
public import Aglib.AlgebraicGeometry.Cohomology.GrothendieckExistence.AffinePushforwardFactorization

/-! # Affine bounds independent of the base-ideal presentation

The whole original diagram, its quotient units and its specified upstairs
isomorphism are retained while normalizing the two structural ideals.
-/

@[expose] public noncomputable section
open CategoryTheory Opposite
namespace AlgebraicGeometry.Scheme.Modules.Coherent
universe u
variable {B : CommRingCat.{u}} [IsNoetherianRing B]
  {Y : Scheme.{u}} [IsLocallyNoetherian Y]
  (p : Y ⟶ Spec B) [IsProper p] (G : Y.CoherentSheaf)

/-- The unique original adjunction factorization has a uniform exceptional
bound over an arbitrary Noetherian affine base, independently of the ideal presentation. -/
theorem affineFactorization_hasBoundedDefects
    (J : Ideal B)
    {K : (Spec B).IdealSheafData} {L : Y.IdealSheafData}
    (hK : K = idealThickeningIdealSheaf (𝟙 (Spec B)) J)
    (hL : L = idealThickeningIdealSheaf (p ≫ 𝟙 (Spec B)) J)
    (F : AdicSystem (Spec B) K)
    (β : F.obj ⋙ pullback p ≅ ((completionFunctor Y L).obj G).obj)
    (ψ : ((completionFunctor (Spec B) K).obj (properPushforwardCoefficient p G)).obj ⟶
      ((completionFunctor Y L).obj G).obj ⋙ pushforward p)
    (hψ : ∀ n : ℕ, (idealSheafQuotientUnit (Spec B) (K ^ n)).app
        ((pushforward p).obj G.obj) ≫ ψ.app (op n) =
      (pushforward p).map ((idealSheafQuotientUnit Y (L ^ n)).app G.obj))
    (α : F ⟶ (completionFunctor (Spec B) K).obj (properPushforwardCoefficient p G))
    (hα : α.hom ≫ ψ =
      ((pullbackPushforwardAdjunction p).whiskerRight ℕᵒᵖ).homEquiv
        F.obj ((completionFunctor Y L).obj G).obj β.hom)
    (E : (Spec B).IdealSheafData) (U : (Spec B).Opens) [IsIso (p ∣_ U)]
    (hU : (U : Set (Spec B))ᶜ ⊆ E.support) :
    AdicSystem.HasBoundedDefects E α := by
  subst K
  subst L
  have hψeq : ψ = formalPushforwardComparison p (𝟙 (Spec B)) J G :=
    originalUnitDiagram_eq
      (idealSheafQuotientTower (Spec B) (idealThickeningIdealSheaf (𝟙 (Spec B)) J)
        ((pushforward p).obj G.obj))
      (idealSheafQuotientTower Y (idealThickeningIdealSheaf (p ≫ 𝟙 (Spec B)) J) G.obj ⋙
        pushforward p) ((pushforward p).obj G.obj)
      (fun n => (idealSheafQuotientUnit (Spec B)
        (idealThickeningIdealSheaf (𝟙 (Spec B)) J ^ n)).app ((pushforward p).obj G.obj))
      (fun n => (pushforward p).map ((idealSheafQuotientUnit Y
        (idealThickeningIdealSheaf (p ≫ 𝟙 (Spec B)) J ^ n)).app G.obj))
      (fun n => pullbackPushforwardUnit_epi
        (idealThickeningIdealSheaf (𝟙 (Spec B)) J ^ n).subschemeι
        ((pushforward p).obj G.obj)) ψ hψ
      (formalPushforwardComparisonData p (𝟙 (Spec B)) J G)
  subst ψ
  let β' : (baseIdealPullbackFunctor p (𝟙 (Spec B)) J).obj F ≅
      (completionFunctor Y (idealThickeningIdealSheaf (p ≫ 𝟙 (Spec B)) J)).obj G :=
    ObjectProperty.isoMk _ β
  have hαeq := affineModificationComparison_original_unique p J F G β'.hom α hα
  rw [hαeq]
  exact affineModificationComparison_hasBoundedDefects J p F G β' E U hU

/-- The same bound applies directly to an original comparison over a different
affine base, without completeness or faithful flatness of its defining-ideal completion. -/
theorem affineModificationComparison_overArbitraryBase_hasBoundedDefects
    {A : Type u} [CommRing A] (f : Spec B ⟶ Spec (CommRingCat.of A)) (I : Ideal A)
    (F : AdicSystem (Spec B) (idealThickeningIdealSheaf f I))
    (β : (baseIdealPullbackFunctor p f I).obj F ≅
      (completionFunctor Y (idealThickeningIdealSheaf (p ≫ f) I)).obj G)
    (α : F ⟶ (completionFunctor (Spec B) (idealThickeningIdealSheaf f I)).obj
      (properPushforwardCoefficient p G))
    (hα : α.hom ≫ formalPushforwardComparison p f I G =
      formalModificationAdjoint p f I F _ β.hom)
    (E : (Spec B).IdealSheafData) (U : (Spec B).Opens) [IsIso (p ∣_ U)]
    (hU : (U : Set (Spec B))ᶜ ⊆ E.support) :
    AdicSystem.HasBoundedDefects E α := by
  let K := idealThickeningIdealSheaf f I
  let J := affineIdeal B K
  have hK : K = idealThickeningIdealSheaf (𝟙 (Spec B)) J :=
    (idealThickeningIdealSheaf_affineIdeal B K).symm
  have hL : idealThickeningIdealSheaf (p ≫ f) I =
      idealThickeningIdealSheaf (p ≫ 𝟙 (Spec B)) J := by
    exact (baseIdeal_comap p f I).symm.trans
      ((congrArg (fun K : (Spec B).IdealSheafData => K.comap p) hK).trans
        (baseIdeal_comap p (𝟙 (Spec B)) J))
  exact affineFactorization_hasBoundedDefects p G J hK hL F
    ((adicSystemToDiagram Y (idealThickeningIdealSheaf (p ≫ f) I)).mapIso β)
    (formalPushforwardComparison p f I G) (formalPushforwardComparison_unit p f I G)
    α hα E U hU

end AlgebraicGeometry.Scheme.Modules.Coherent
