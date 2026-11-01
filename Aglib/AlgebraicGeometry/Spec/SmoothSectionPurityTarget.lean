/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Spec.SmoothSectionPurityOpen
public import Aglib.AlgebraicGeometry.Morphisms.Etale.FiniteStalkNeighborhood

/-! # The original finite branch open in the section-purity induction step

The original canonical target etale open is constructed internally. Fibrewise
etaleness in codimension one and along the punctured section gives etaleness
at the prescribed closed lifted section point. These are the explicit inputs
of the local induction step, not a claim of full relative purity.
-/

@[expose] public noncomputable section

open CategoryTheory

namespace AlgebraicGeometry.Scheme

universe u

/-- The closed lifted section point is etale once the original finite map is
etale on every codimension-one target fibre and every punctured section fibre. -/
theorem smoothSection_etaleAt_of_codimensionOne_of_puncturedSection
    (A B C : Type u) [CommRing A] [IsDomain A] [IsLocalRing A]
    [IsNoetherianRing A] [IsIntegrallyClosed A]
    [CommRing B] [IsDomain B] [Algebra A B] [Algebra.Smooth A B]
    [CommRing C] [IsDomain C] [IsIntegrallyClosed C]
    [Algebra B C] [FaithfulSMul B C] [Module.Finite B C]
    (ε : B →ₐ[A] A) (δ : C →+* A)
    (hδ : δ.comp (algebraMap B C) = ε.toRingHom)
    (hdim : 2 ≤ ringKrullDim A)
    (hheight : ∀ q : PrimeSpectrum B, q.asIdeal.height = 1 →
      ∀ y : Spec (.of C), Spec.algebraMap B C y = q →
        (Spec.algebraMap B C).etaleAt y)
    (hpuncture : ∀ x : Spec (.of A), x ∈ puncturedSpecOpen A →
      ∀ y : Spec (.of C), Spec.algebraMap B C y =
        Spec.map (CommRingCat.ofHom ε.toRingHom) x →
        (Spec.algebraMap B C).etaleAt y) :
    (Spec.algebraMap B C).etaleAt
      (Spec.map (CommRingCat.ofHom δ) (IsLocalRing.closedPoint A)) := by
  let f := Spec.algebraMap B C
  let s := Spec.map (CommRingCat.ofHom ε.toRingHom)
  let a := Spec.map (CommRingCat.ofHom δ)
  let : IsFinite f := by
    change IsFinite (Spec.map (CommRingCat.ofHom (algebraMap B C)))
    rw [IsFinite.SpecMap_iff]
    exact RingHom.finite_algebraMap.mpr inferInstance
  let U := f.etaleTargetOpen f.isClosedMap
  have hmap : a ≫ f = s := by
    change Spec.map _ ≫ Spec.map _ = Spec.map _
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, hδ]
  have hUheight : ∀ q : PrimeSpectrum B, q.asIdeal.height = 1 → q ∈ U := by
    intro q hq
    rintro ⟨y, hy, he⟩
    exact hy (hheight q hq y he)
  have hUpuncture : puncturedSpecOpen A ≤ s ⁻¹ᵁ U := by
    intro x hx
    rintro ⟨y, hy, he⟩
    exact hy (hpuncture x hx y he)
  by_cases hc : s (IsLocalRing.closedPoint A) ∈ U
  · have hmem : a (IsLocalRing.closedPoint A) ∈ f ⁻¹ᵁ U := by
      change f (a (IsLocalRing.closedPoint A)) ∈ U
      have he := congrArg (fun g : Spec (.of A) ⟶ Spec (.of B) =>
        g (IsLocalRing.closedPoint A)) hmap
      exact he.symm ▸ hc
    exact f.preimage_etaleTargetOpen_le f.isClosedMap hmem
  · have hzero : s ⁻¹ᵁ U = puncturedSpecOpen A := by
      apply le_antisymm
      · intro x hx he
        exact hc (he ▸ hx)
      · exact hUpuncture
    let : Etale (f ∣_ U) := f.etale_restrict_etaleTargetOpen f.isClosedMap
    exact smoothSection_etaleAt_of_hartogsOpen A B C ε δ hδ U hUheight hzero hdim
      (IsLocalRing.closedPoint A)

end AlgebraicGeometry.Scheme
