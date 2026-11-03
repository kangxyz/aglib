/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Normalization.GenericFiniteEtale.SmoothLocalPointedExtension
public import Aglib.AlgebraicGeometry.Normalization.GenericFiniteEtale.GaloisRestrictedExtension

/-! # The literal Galois pointed-cover neighborhood of the original section

The unchanged normalization is restricted to the produced target neighborhood.
Native open lifts retain the original section and generic-point triangles.
-/

@[expose] public noncomputable section

open CategoryTheory

namespace AlgebraicGeometry.Scheme.FiniteEtale.GenericNormalization.OpenRecovery

universe u

/-- The original generic-pointed cover gives a literal Galois cover near the
whole section, with unchanged deck order and original generic triangle. -/
theorem exists_smoothLocal_galoisPointedExtension
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
        ∃ (Z : X.Opens) (hZ : Set.range s ⊆ Z)
          (hEt : Etale ((genericMap j Y.obj.hom).fromNormalization ∣_ Z)),
          letI : Nonempty Z := ⟨⟨s (IsLocalRing.closedPoint A), hZ ⟨_, rfl⟩⟩⟩
          letI : IsIntegral Z := isIntegral_of_isOpenImmersion Z.ι
          letI : Etale ((genericMap j Y.obj.hom).fromNormalization ∣_ Z) := hEt
          CategoryTheory.PreGaloisCategory.IsGalois (restrictedNormalizationCover j Y Z) ∧
            Nat.card (Aut (restrictedNormalizationCover j Y Z)) = Nat.card (Aut Y) ∧
            ∃ (sZ : Spec (.of A) ⟶ Z)
              (lZ : Spec (.of A) ⟶ (genericMap j Y.obj.hom).fromNormalization ⁻¹ᵁ Z),
              sZ ≫ Z.ι = s ∧
              lZ ≫ (restrictedNormalizationCover j Y Z).obj.hom = sZ ∧
              (Spec (.of A)).fromSpecStalk (genericPoint (Spec (.of A))) ≫ lZ ≫
                ((genericMap j Y.obj.hom).fromNormalization ⁻¹ᵁ Z).ι =
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
  obtain ⟨Z, hZ, _, hEt, l, hl, _⟩ :=
    exists_smoothLocal_genericPointedExtension A p s hs W j hj N hN hunit Y hcard a ha
  let : Nonempty Z := ⟨⟨s (IsLocalRing.closedPoint A), hZ ⟨_, rfl⟩⟩⟩
  let : IsIntegral Z := isIntegral_of_isOpenImmersion Z.ι
  let f := (genericMap j Y.obj.hom).fromNormalization
  let : Etale (f ∣_ Z) := hEt
  have hsZ : Set.range s ⊆ Set.range Z.ι := by
    simpa only [Scheme.Opens.range_ι] using hZ
  let sZ := IsOpenImmersion.lift Z.ι s hsZ
  have hsZeq : sZ ≫ Z.ι = s := IsOpenImmersion.lift_fac ..
  have hlZ : Set.range l ⊆ Set.range (f ⁻¹ᵁ Z).ι := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨x, rfl⟩
    change f (l x) ∈ Z
    rw [← Scheme.Hom.comp_apply, hl.1]
    exact hZ ⟨x, rfl⟩
  let lZ := IsOpenImmersion.lift (f ⁻¹ᵁ Z).ι l hlZ
  have hlZeq : lZ ≫ (f ⁻¹ᵁ Z).ι = l := IsOpenImmersion.lift_fac ..
  obtain ⟨hG, horder⟩ := restrictedNormalization_isGalois_card j Y Z
  refine ⟨Z, hZ, hEt, hG, horder, sZ, lZ, hsZeq, ?_, ?_⟩
  · apply (cancel_mono Z.ι).mp
    change (lZ ≫ f ∣_ Z) ≫ Z.ι = sZ ≫ Z.ι
    rw [Category.assoc, morphismRestrict_ι, ← Category.assoc, hlZeq, hl.1, hsZeq]
  · change (Spec (.of A)).fromSpecStalk (genericPoint (Spec (.of A))) ≫
      lZ ≫ (f ⁻¹ᵁ Z).ι = a ≫ inclusion j Y.obj.hom
    rw [hlZeq]
    exact hl.2

end AlgebraicGeometry.Scheme.FiniteEtale.GenericNormalization.OpenRecovery
