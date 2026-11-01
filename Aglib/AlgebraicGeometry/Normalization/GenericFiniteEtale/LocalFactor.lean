/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.IntegralClosure.FiniteEtale.LocalFactorGeneric
public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.FieldGaloisObject
public import Aglib.CategoryTheory.Galois.RegularActionComponent
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-! # The actual generic component selected by a normalization point

The specified maximal localization determines its literal tensor generic field.
Its spectrum is a connected subobject of the original finite etale generic
algebra. The inclusion is the original generic algebra map, not a chosen
unrelated field factor. A regular original action makes this actual component
Galois and embeds its deck group in the original acting group.
-/

@[expose] public noncomputable section

open CategoryTheory Opposite
open CategoryTheory.PreGaloisCategory
open scoped TensorProduct

namespace AlgebraicGeometry.Scheme.FiniteEtale.LocalFactor

universe u v

variable (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [HenselianLocalRing R]
  (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
  (A : Type u) [CommRing A] [Algebra K A] [Algebra R A] [IsScalarTower R K A]
  [Algebra.Etale K A]
  (q : Ideal (integralClosure R A)) [q.IsMaximal]

local notation "S₀" => Localization.AtPrime q
local notation "L₀" => K ⊗[R] S₀

local instance : Module.Finite K A := Algebra.FormallyUnramified.finite_of_free K A
local instance : Field L₀ := integralClosure.LocalFactor.genericField R K A q
local instance : Module.Finite K L₀ := integralClosure.LocalFactor.generic_finite R K A q
local instance : Algebra.Etale K L₀ := integralClosure.LocalFactor.generic_etale R K A q

/-- The spectrum of the literal generic field of the specified local factor. -/
def genericCover : FiniteEtale (Spec (.of K)) :=
  (finiteEtaleSpecFunctor K).obj (op (CommAlgCat.FiniteEtale.of K L₀))

/-- The actual inclusion is obtained from the original surjective generic map. -/
def genericInclusion : genericCover R K A q ⟶
    (finiteEtaleSpecFunctor K).obj (op (CommAlgCat.FiniteEtale.of K A)) :=
  (finiteEtaleSpecFunctor K).map
    (CommAlgCat.FiniteEtale.ofHom (integralClosure.LocalFactor.genericMap R K A q)).op

/-- The unchanged underlying scheme map is the original generic ring map. -/
theorem genericInclusion_left :
    (genericInclusion R K A q).hom.left =
      Spec.map (CommRingCat.ofHom
        (integralClosure.LocalFactor.genericMap R K A q).toRingHom) := rfl

/-- Surjectivity of the original generic map gives actual categorical monicity. -/
theorem genericInclusion_mono : Mono (genericInclusion R K A q) := by
  let : IsClosedImmersion (Spec.map (CommRingCat.ofHom
      (integralClosure.LocalFactor.genericMap R K A q).toRingHom)) :=
    IsClosedImmersion.spec_of_surjective _
      (integralClosure.LocalFactor.genericMap_surjective R K A q)
  apply (forgetToScheme (Spec (.of K))).mono_of_mono_map
  change Mono (Spec.map (CommRingCat.ofHom
    (integralClosure.LocalFactor.genericMap R K A q).toRingHom))
  infer_instance

/-- The selected generic component is connected because its literal ring is a field. -/
theorem genericCover_connected : IsConnected (genericCover R K A q) := by
  let : ConnectedSpace (genericCover R K A q).obj.left := by
    change ConnectedSpace (Spec (.of L₀))
    infer_instance
  exact Connectedness.categoricalConnected_of_connectedSpace (genericCover R K A q)

variable (Ω : Type u) [Field Ω] [Algebra K Ω] [IsSepClosed Ω]
  {G : Type v} [Group G]
  (ρ : G →* Aut ((finiteEtaleSpecFunctor K).obj (op (CommAlgCat.FiniteEtale.of K A))))
  (z : Fiber (Spec.algebraMap K Ω) (genericCover R K A q))
  (hρ : Function.Bijective (fun a =>
    (fiberToFinite (Spec.algebraMap K Ω)).map (ρ a).hom
      ((fiberToFinite (Spec.algebraMap K Ω)).map (genericInclusion R K A q) z)))

include hρ in
/-- The specified generic component is Galois under the original regular action. -/
theorem genericCover_isGalois : IsGalois (genericCover R K A q) := by
  let := genericInclusion_mono R K A q
  let := genericCover_connected R K A q
  exact isGalois_of_regularAction_component (fiberToFinite (Spec.algebraMap K Ω))
    ρ _ hρ (genericInclusion R K A q) z rfl

include hρ in
/-- The actual component deck group embeds in the original acting group,
with the literal translation equation and resulting order divisibility. -/
theorem genericCover_deck_embedding :
    ∃ δ : Aut (genericCover R K A q) →* G, Function.Injective δ ∧
      (∀ σ, σ.hom ≫ genericInclusion R K A q =
        genericInclusion R K A q ≫ (ρ (δ σ)).hom) ∧
      Nat.card (Aut (genericCover R K A q)) ∣ Nat.card G := by
  let := genericInclusion_mono R K A q
  let := genericCover_connected R K A q
  let F := fiberToFinite (Spec.algebraMap K Ω)
  exact ⟨componentTranslationHom F ρ _ hρ (genericInclusion R K A q) z rfl,
    componentTranslationHom_injective F ρ _ hρ (genericInclusion R K A q) z rfl,
    componentTranslation_over F ρ _ hρ (genericInclusion R K A q) z rfl,
    component_aut_card_dvd F ρ _ hρ (genericInclusion R K A q) z rfl⟩

include hρ in
/-- The literal generic field is Galois, and its original field automorphism
order divides the original acting-group order. -/
theorem genericField_isGalois_and_card_dvd :
    _root_.IsGalois K L₀ ∧ Nat.card (L₀ ≃ₐ[K] L₀) ∣ Nat.card G := by
  let := genericCover_isGalois R K A q Ω ρ z hρ
  refine ⟨isGalois_of_iso_fieldSpectrum K L₀ (genericCover R K A q) (Iso.refl _), ?_⟩
  rw [← fieldSpectrum_card_aut K L₀]
  exact (genericCover_deck_embedding R K A q Ω ρ z hρ).choose_spec.2.2

end AlgebraicGeometry.Scheme.FiniteEtale.LocalFactor
