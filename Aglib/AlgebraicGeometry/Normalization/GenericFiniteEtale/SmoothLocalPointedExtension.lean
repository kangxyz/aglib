/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Normalization.GenericFiniteEtale.SmoothLocalSectionPurity
public import Aglib.AlgebraicGeometry.Stalk.GenericSection

/-! # The original generic-pointed cover extends near the whole local section

The supplied original generic cover point extends uniquely by finite integral
descent over the normal base. Pointed relative purity makes the unchanged
normalization finite etale over an actual target open containing the whole
original section. Its original generic triangle is retained literally.
-/

@[expose] public noncomputable section

open CategoryTheory

namespace AlgebraicGeometry.Scheme.FiniteEtale.GenericNormalization.OpenRecovery

universe u

/-- Original generic-pointed local extension, without a supplied global
normalization section or any codimension-one/formal-completion hypothesis. -/
theorem exists_smoothLocal_genericPointedExtension
    (A : Type u) [CommRing A] [IsDomain A] [IsLocalRing A]
    [IsNoetherianRing A] [IsIntegrallyClosed A]
    {X U : Scheme.{u}} (p : X ⟶ Spec (.of A)) [Smooth p] [GeometricallyConnected p]
    (s : Spec (.of A) ⟶ X) (hs : s ≫ p = 𝟙 _)
    (W : (Spec (.of A)).Opens) [Nonempty W]
    (j : U ⟶ X) [IsOpenImmersion j]
    (hj : Set.range j = p ⁻¹' (W : Set (Spec (.of A))))
    (N : ℕ) (hN : 0 < N) (hunit : IsUnit (N : A)) :
    letI : GeometricallyIntegral p := geometricallyIntegral_of_smooth_of_geometricallyConnected p
    letI : IsIntegral X := GeometricallyIntegral.isIntegral_of_isLocallyNoetherian p
    letI : Nonempty U := section_baseOpen_nonempty p s hs W j hj
    letI : IsIntegral U := isIntegral_of_isOpenImmersion j
    letI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian p
    letI : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x) :=
      fun x => (normalStalks_of_smooth_normalBase A p x).2
    ∀ (Y : FiniteEtale U) [IsIntegral Y.obj.left]
      [CategoryTheory.PreGaloisCategory.IsGalois Y], Nat.card (Aut Y) ∣ N →
      ∀ (a : Spec (Spec (.of A)).functionField ⟶ Y.obj.left),
        a ≫ Y.obj.hom ≫ j =
          (Spec (.of A)).fromSpecStalk (genericPoint (Spec (.of A))) ≫ s →
        ∃ Z : X.Opens, Set.range s ⊆ Z ∧
          IsFinite ((genericMap j Y.obj.hom).fromNormalization ∣_ Z) ∧
          Etale ((genericMap j Y.obj.hom).fromNormalization ∣_ Z) ∧
          ∃! l : Spec (.of A) ⟶ (genericMap j Y.obj.hom).normalization,
            l ≫ (genericMap j Y.obj.hom).fromNormalization = s ∧
            (Spec (.of A)).fromSpecStalk (genericPoint (Spec (.of A))) ≫ l =
              a ≫ inclusion j Y.obj.hom := by
  let : GeometricallyIntegral p := geometricallyIntegral_of_smooth_of_geometricallyConnected p
  let : IsIntegral X := GeometricallyIntegral.isIntegral_of_isLocallyNoetherian p
  let : Nonempty U := section_baseOpen_nonempty p s hs W j hj
  let : IsIntegral U := isIntegral_of_isOpenImmersion j
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian p
  let (x : X) : IsIntegrallyClosed (X.presheaf.stalk x) :=
    (normalStalks_of_smooth_normalBase A p x).2
  dsimp only
  intro Y _ _ hcard a ha
  let f := (genericMap j Y.obj.hom).fromNormalization
  let : IsFinite f := fromNormalization_isFinite j Y.obj.hom
  have hnormal : NormalStalks (Spec (.of A)) := fun x =>
    ⟨(isIntegrallyClosed_and_isDomain_stalk_Spec A x).2,
      (isIntegrallyClosed_and_isDomain_stalk_Spec A x).1⟩
  have hi : inclusion j Y.obj.hom ≫ f = Y.obj.hom ≫ j := inclusion_over j Y.obj.hom
  have hgeneric : (a ≫ inclusion j Y.obj.hom) ≫ f =
      (Spec (.of A)).fromSpecStalk (genericPoint (Spec (.of A))) ≫ s := by
    rw [Category.assoc, hi]
    exact ha
  obtain ⟨l, hl, huniq⟩ := existsUnique_integralGenericLift
    (Spec (.of A)) hnormal s f (a ≫ inclusion j Y.obj.hom) hgeneric
  obtain ⟨Z, hZ, hEt⟩ :=
    exists_smoothLocal_baseOpen_etaleNeighborhood A p s hs W j hj N hN hunit Y hcard l hl.1
  exact ⟨Z, hZ, inferInstance, hEt, l, hl, huniq⟩

end AlgebraicGeometry.Scheme.FiniteEtale.GenericNormalization.OpenRecovery
