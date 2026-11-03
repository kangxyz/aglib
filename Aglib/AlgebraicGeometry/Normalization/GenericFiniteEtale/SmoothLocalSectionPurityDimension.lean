/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Normalization.GenericFiniteEtale.SmoothDimensionOneBaseOpen

/-! # The exact dimension-induction statement for the original pointed normalization

This proposition quantifies over the original rings, schemes, cover and section.
It introduces no geometric model or extra completion hypothesis. The dimension
at most one case is the original field/DVR argument.
-/

@[expose] public noncomputable section

open CategoryTheory

namespace AlgebraicGeometry.Scheme.FiniteEtale.GenericNormalization.OpenRecovery

universe u

/-- The original selected section point is etale in the specified base dimension. -/
def SmoothLocalSectionPurityAtDimension (d : ℕ) : Prop :=
  ∀ (A : Type u) [CommRing A] [IsDomain A] [IsLocalRing A]
    [IsNoetherianRing A] [IsIntegrallyClosed A], ringKrullDim A = (d : ℕ) →
    ∀ {X U : Scheme.{u}} (p : X ⟶ Spec (.of A)) [Smooth p] [GeometricallyConnected p]
      (s : Spec (.of A) ⟶ X) (hs : s ≫ p = 𝟙 _),
      ∀ (W : (Spec (.of A)).Opens) [Nonempty W]
        (j : U ⟶ X) [IsOpenImmersion j]
        (hj : Set.range j = p ⁻¹' (W : Set (Spec (.of A)))),
        ∀ (N : ℕ), 0 < N → IsUnit (N : A) →
          letI : GeometricallyIntegral p :=
            geometricallyIntegral_of_smooth_of_geometricallyConnected p
          letI : IsIntegral X := GeometricallyIntegral.isIntegral_of_isLocallyNoetherian p
          letI : Nonempty U := section_baseOpen_nonempty p s hs W j hj
          letI : IsIntegral U := isIntegral_of_isOpenImmersion j
          ∀ (Y : FiniteEtale U) [IsIntegral Y.obj.left]
            [CategoryTheory.PreGaloisCategory.IsGalois Y], Nat.card (Aut Y) ∣ N →
            ∀ (a : Spec (.of A) ⟶ (genericMap j Y.obj.hom).normalization),
              a ≫ (genericMap j Y.obj.hom).fromNormalization = s →
              (genericMap j Y.obj.hom).fromNormalization.etaleAt
                (a (IsLocalRing.closedPoint A))

/-- The exact original induction statement holds in dimensions zero and one. -/
theorem smoothLocalSectionPurityAtDimension_of_le_one
    (d : ℕ) (hd : d ≤ 1) : SmoothLocalSectionPurityAtDimension.{u} d := by
  intro A _ _ _ _ _ hdim X U p _ _ s hs W _ j _ hj N hN hunit
  let : GeometricallyIntegral p := geometricallyIntegral_of_smooth_of_geometricallyConnected p
  let : IsIntegral X := GeometricallyIntegral.isIntegral_of_isLocallyNoetherian p
  let : Nonempty U := section_baseOpen_nonempty p s hs W j hj
  let : IsIntegral U := isIntegral_of_isOpenImmersion j
  dsimp only
  intro Y _ _ hcard a ha
  have hdim' : ringKrullDim A ≤ 1 := by
    rw [hdim]
    exact_mod_cast hd
  let : Etale (genericMap j Y.obj.hom).fromNormalization :=
    etale_normalization_of_smooth_dimLE_one_baseOpen_section A hdim' p s hs W j hj
      N hN hunit Y hcard a ha
  exact ⟨⊤, trivial, inferInstance⟩

end AlgebraicGeometry.Scheme.FiniteEtale.GenericNormalization.OpenRecovery
