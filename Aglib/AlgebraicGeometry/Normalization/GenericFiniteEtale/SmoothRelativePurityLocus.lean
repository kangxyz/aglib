/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Normalization.GenericFiniteEtale.SmoothLowHeightBaseFiber
public import Aglib.AlgebraicGeometry.Normalization.GenericFiniteEtale.SmoothLocalSectionPurity

/-! # The original etale locus satisfies the relative-purity fibre conditions

The actual normalization's target etale open is dense in every fibre and
contains whole fibres over base primes of height at most one. This does not
prove relative purity or identify that open with the entire target.
-/

@[expose] public noncomputable section

open CategoryTheory

namespace AlgebraicGeometry.Scheme

universe u

/-- A target open containing an actual section is dense on each original
geometrically irreducible fibre. -/
theorem dense_fiber_preimage_of_section_range_subset
    {X S : Scheme.{u}} (p : X ⟶ S) [GeometricallyIrreducible p]
    (s : S ⟶ X) (hs : s ≫ p = 𝟙 S)
    (E : X.Opens) (hE : Set.range s ⊆ E) (q : S) :
    Dense ((p.fiberι q) ⁻¹' (E : Set X)) := by
  have hsq : p (s q) = q := by
    exact congrArg (fun f : S ⟶ S => f q) hs
  have hr : s q ∈ Set.range (p.fiberι q) := by
    rw [p.range_fiberι]
    exact hsq
  obtain ⟨z, hz⟩ := hr
  apply (E.isOpen.preimage (p.fiberι q).continuous).dense
  refine ⟨z, ?_⟩
  change (p.fiberι q) z ∈ E
  rw [hz]
  exact hE ⟨q, rfl⟩

namespace FiniteEtale.GenericNormalization.OpenRecovery

/-- Both fibre conditions concern the same original canonical etale open.
The low-height conclusion concerns all points of a base fibre, not just
codimension-one points of the smooth target. The supplied closed-map proof
is only the proof argument of the canonical target open; finiteness of this
normalization already follows from the original finite-etale cover. -/
theorem etaleTargetOpen_fiber_dense_and_baseHeight_le_one_full
    (A : Type u) [CommRing A] [IsDomain A] [IsLocalRing A]
    [IsNoetherianRing A] [IsIntegrallyClosed A]
    {X U : Scheme.{u}} [IsIntegral X] [IsIntegral U]
    (p : X ⟶ Spec (.of A)) [Smooth p] [GeometricallyConnected p]
    (s : Spec (.of A) ⟶ X) (hs : s ≫ p = 𝟙 _)
    (W : (Spec (.of A)).Opens) [Nonempty W]
    (j : U ⟶ X) [IsOpenImmersion j]
    (hj : Set.range j = p ⁻¹' (W : Set (Spec (.of A))))
    (N : ℕ) (hN : 0 < N) (hunit : IsUnit (N : A))
    (Y : FiniteEtale U) [IsIntegral Y.obj.left]
    [CategoryTheory.PreGaloisCategory.IsGalois Y] (hcard : Nat.card (Aut Y) ∣ N)
    (a : Spec (.of A) ⟶ (genericMap j Y.obj.hom).normalization)
    (ha : a ≫ (genericMap j Y.obj.hom).fromNormalization = s)
    (hf : IsClosedMap (genericMap j Y.obj.hom).fromNormalization) :
    let E := (genericMap j Y.obj.hom).fromNormalization.etaleTargetOpen hf
    (∀ q : Spec (.of A), Dense ((p.fiberι q) ⁻¹' (E : Set X))) ∧
      ∀ x : X, (p x).asIdeal.height ≤ 1 → x ∈ E := by
  let : GeometricallyIntegral p :=
    geometricallyIntegral_of_smooth_of_geometricallyConnected p
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian p
  let (x : X) : IsIntegrallyClosed (X.presheaf.stalk x) :=
    (normalStalks_of_smooth_normalBase A p x).2
  let f := (genericMap j Y.obj.hom).fromNormalization
  let : IsFinite f := fromNormalization_isFinite j Y.obj.hom
  have het := etaleAt_smoothLocal_baseOpen_section A p s hs W j hj
    N hN hunit Y hcard a ha
  have hsection : Set.range s ⊆ f.etaleTargetOpen hf :=
    range_subset_etaleTargetOpen_of_section_etaleAt j Y s a ha het
  refine ⟨fun q => dense_fiber_preimage_of_section_range_subset p s hs
    (f.etaleTargetOpen hf) hsection q, ?_⟩
  intro x hx
  rintro ⟨y, hy, he⟩
  exact hy (etaleAt_of_smooth_baseOpen_baseHeight_le_one A p s hs W j hj
    N hN hunit Y hcard a ha x hx y he)

end FiniteEtale.GenericNormalization.OpenRecovery
end AlgebraicGeometry.Scheme
