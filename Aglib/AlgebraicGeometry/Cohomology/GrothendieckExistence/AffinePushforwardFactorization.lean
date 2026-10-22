/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.GrothendieckExistence.AffineModificationComparison

/-! # Original affine factorization independent of the presentation of the ideal

The ideal may be given by any affine base. Its chart ideal normalizes the
original quotient objects. The quotient-unit equation identifies the actual
pushforward comparison; the entire specified adjunction family is retained.
-/

@[expose] public noncomputable section
open CategoryTheory Opposite
namespace AlgebraicGeometry.Scheme.Modules.Coherent
universe u
variable {B : CommRingCat.{u}} [IsNoetherianRing B]
  {Y : Scheme.{u}} [IsLocallyNoetherian Y]
  (p : Y ⟶ Spec B) [IsProper p] (G : Y.CoherentSheaf)

/-- Original quotient-unit detection on a whole diagram, before geometric specialization. -/
theorem originalUnitDiagram_eq {C : Type*} [Category C]
    (S T : ℕᵒᵖ ⥤ C) (U : C) (u : ∀ n, U ⟶ S.obj (op n))
    (v : ∀ n, U ⟶ T.obj (op n)) (hu : ∀ n, Epi (u n))
    (ψ : S ⟶ T) (hψ : ∀ n, u n ≫ ψ.app (op n) = v n)
    (c : {η : S ⟶ T // ∀ n, u n ≫ η.app (op n) = v n}) : ψ = c.val := by
  apply NatTrans.ext
  funext j
  let := hu j.unop
  exact (cancel_epi (u j.unop)).mp ((hψ j.unop).trans (c.property j.unop).symm)

/-- The original affine comparison is characterized by its actual quotient
units and acts on arbitrary compatible adjunction families. -/
theorem existsUnique_affinePushforwardFactorization
    (J : Ideal B) {K : (Spec B).IdealSheafData} {L : Y.IdealSheafData}
    (hK : K = idealThickeningIdealSheaf (𝟙 (Spec B)) J)
    (hL : L = idealThickeningIdealSheaf (p ≫ 𝟙 (Spec B)) J)
    (F : AdicSystem (Spec B) K)
    (ψ : ((completionFunctor (Spec B) K).obj (properPushforwardCoefficient p G)).obj ⟶
      ((completionFunctor Y L).obj G).obj ⋙ pushforward p)
    (hψ : ∀ n : ℕ, (idealSheafQuotientUnit (Spec B) (K ^ n)).app
        ((pushforward p).obj G.obj) ≫ ψ.app (op n) =
      (pushforward p).map ((idealSheafQuotientUnit Y (L ^ n)).app G.obj))
    (γ : F.obj ⟶ ((completionFunctor Y L).obj G).obj ⋙ pushforward p) :
    ∃! α : F ⟶ (completionFunctor (Spec B) K).obj (properPushforwardCoefficient p G),
      α.hom ≫ ψ = γ := by
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
  let H := (completionFunctor Y (idealThickeningIdealSheaf (p ≫ 𝟙 (Spec B)) J)).obj G
  let β : (baseIdealPullbackFunctor p (𝟙 (Spec B)) J).obj F ⟶ H :=
    ObjectProperty.homMk
      ((((pullbackPushforwardAdjunction p).whiskerRight ℕᵒᵖ).homEquiv F.obj H.obj).symm γ)
  have hβ : formalModificationAdjoint p (𝟙 (Spec B)) J F H β = γ :=
    (((pullbackPushforwardAdjunction p).whiskerRight ℕᵒᵖ).homEquiv F.obj H.obj).apply_symm_apply γ
  refine ⟨affineModificationComparison p J F G β, ?_, ?_⟩
  · exact (affineModificationComparison_original_diagram p J F G β).trans hβ
  · intro α hα
    exact affineModificationComparison_original_unique p J F G β α (hα.trans hβ.symm)

/-- Every compatible family into the original ambient tower factors uniquely
on an affine base, independently of the original base-ring presentation. -/
theorem existsUnique_affinePushforwardFactorization_overBase
    {A : Type u} [CommRing A] (f : Spec B ⟶ Spec (CommRingCat.of A)) (I : Ideal A)
    (F : AdicSystem (Spec B) (idealThickeningIdealSheaf f I))
    (γ : F.obj ⟶
      ((completionFunctor Y (idealThickeningIdealSheaf (p ≫ f) I)).obj G).obj ⋙
        pushforward p) :
    ∃! α : F ⟶ (completionFunctor (Spec B) (idealThickeningIdealSheaf f I)).obj
      (properPushforwardCoefficient p G),
      α.hom ≫ formalPushforwardComparison p f I G = γ := by
  let K := idealThickeningIdealSheaf f I
  let J := affineIdeal B K
  have hK : K = idealThickeningIdealSheaf (𝟙 (Spec B)) J :=
    (idealThickeningIdealSheaf_affineIdeal B K).symm
  have hL : idealThickeningIdealSheaf (p ≫ f) I =
      idealThickeningIdealSheaf (p ≫ 𝟙 (Spec B)) J := by
    exact (baseIdeal_comap p f I).symm.trans
      ((congrArg (fun K : (Spec B).IdealSheafData => K.comap p) hK).trans
        (baseIdeal_comap p (𝟙 (Spec B)) J))
  exact existsUnique_affinePushforwardFactorization p G J hK hL F
    (formalPushforwardComparison p f I G) (formalPushforwardComparison_unit p f I G) γ

/-- In particular, retain the specified original upstairs formal map. -/
theorem existsUnique_affineModificationComparison_overBase
    {A : Type u} [CommRing A] (f : Spec B ⟶ Spec (CommRingCat.of A)) (I : Ideal A)
    (F : AdicSystem (Spec B) (idealThickeningIdealSheaf f I))
    (β : (baseIdealPullbackFunctor p f I).obj F ⟶
      (completionFunctor Y (idealThickeningIdealSheaf (p ≫ f) I)).obj G) :
    ∃! α : F ⟶ (completionFunctor (Spec B) (idealThickeningIdealSheaf f I)).obj
      (properPushforwardCoefficient p G),
      α.hom ≫ formalPushforwardComparison p f I G =
        formalModificationAdjoint p f I F _ β :=
  existsUnique_affinePushforwardFactorization_overBase p G f I F
    (formalModificationAdjoint p f I F _ β)

end AlgebraicGeometry.Scheme.Modules.Coherent
