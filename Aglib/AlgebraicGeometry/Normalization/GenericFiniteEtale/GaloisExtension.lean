/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Normalization.GenericFiniteEtale.EtaleExtension
public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.OpenGaloisReflection
public import Aglib.CategoryTheory.Galois.Iso

/-! # Galoisness and original deck groups of the normalization extension

The original restriction isomorphism and full faithfulness of actual open
restriction reflect Galoisness. Deck groups are compared by the native map on
automorphisms followed by the same original restriction isomorphism.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.PreGaloisCategory

namespace AlgebraicGeometry.Scheme.FiniteEtale.GenericNormalization.OpenRecovery

universe u

variable {X U : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
  [∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x)] [Nonempty U]
  (j : U ⟶ X) [IsOpenImmersion j] (Y : FiniteEtale U)
  [Etale (genericMap j Y.obj.hom).fromNormalization]

/-- The original open restriction and recovery induce the actual deck-group equivalence. -/
def normalizationFiniteEtale_autEquiv :
    Aut (normalizationFiniteEtale j Y) ≃* Aut Y := by
  let : IsIntegral U := isIntegral_of_isOpenImmersion j
  let : (baseChange j).Full := (baseChange_open_full_faithful j).1
  let : (baseChange j).Faithful := (baseChange_open_full_faithful j).2
  exact ((Functor.FullyFaithful.ofFullyFaithful (baseChange j)).autMulEquivOfFullyFaithful
    (normalizationFiniteEtale j Y)).trans
      (Aut.autMulEquivOfIso (normalizationFiniteEtale_restrictionIso j Y).symm)

/-- The same normalization extension has the unchanged original deck-group order. -/
theorem normalizationFiniteEtale_card_aut :
    Nat.card (Aut (normalizationFiniteEtale j Y)) = Nat.card (Aut Y) :=
  Nat.card_congr (normalizationFiniteEtale_autEquiv j Y).toEquiv

/-- Original Galoisness reflects through the original open-recovery isomorphism. -/
theorem normalizationFiniteEtale_isGalois [IsIntegral Y.obj.left] :
    letI : IsIntegral U := isIntegral_of_isOpenImmersion j
    ∀ [IsGalois Y], IsGalois (normalizationFiniteEtale j Y) := by
  let : IsIntegral U := isIntegral_of_isOpenImmersion j
  intro hG
  let : IsIntegral (normalizationFiniteEtale j Y).obj.left :=
    normalizationFiniteEtale_isIntegral j Y
  let x := algebraicClosureResiduePoint U (Classical.choice (inferInstance : Nonempty U))
  let : IsGalois ((baseChange j).obj (normalizationFiniteEtale j Y)) :=
    isGalois_of_iso (fiberToFinite x) (normalizationFiniteEtale_restrictionIso j Y)
  exact isGalois_of_open_baseChange j (normalizationFiniteEtale j Y)

end AlgebraicGeometry.Scheme.FiniteEtale.GenericNormalization.OpenRecovery
