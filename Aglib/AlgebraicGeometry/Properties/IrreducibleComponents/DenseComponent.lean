/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.IsIso
public import Mathlib.Topology.Irreducible
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.AlgebraicGeometry.Morphisms.OpenImmersion

/-!
# Unique dense component selected by an isomorphism open

Source: `R5Lab.Aglib.AlgebraicGeometry.IrreducibleComponents.DenseComponent`.
R5 packet revision: `f8a3314ddecffcada2ec721d26d56a937bed9690`.
Source SHA-256: `c400ef19903e817e9275b82d9229e7d30acedda13a7fa1936e279900ee5ac01a`.
Actual objects, maps, universes and hypotheses are retained.
Native declaration ownership replaces the source application namespaces.
-/

@[expose] public section

noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Limits AlgebraicGeometry
universe u

namespace AlgebraicGeometry.Scheme

/-- The closure of a nonempty irreducible open is an actual maximal
irreducible component; this does not assume a component inventory. -/
theorem irreducible_open_closure_component
    {X : Type*} [TopologicalSpace X] {O : Set X}
    (hO : IsOpen O) (hI : IsIrreducible O) : closure O ∈ irreducibleComponents X := by
  refine ⟨hI.closure, ?_⟩
  intro Z hZ hOZ
  have hmeet : (Z ∩ O).Nonempty := by
    obtain ⟨x, hx⟩ := hI.nonempty
    exact ⟨x, hOZ (subset_closure hx), hx⟩
  exact (subset_closure_inter_of_isPreirreducible_of_isOpen hZ.2 hO hmeet).trans
    (closure_mono Set.inter_subset_right)

/-- Any actual component meeting that open must be its closure. -/
theorem component_eq_closure_of_meets_irreducible_open
    {X : Type*} [TopologicalSpace X] {O Z : Set X}
    (hO : IsOpen O) (hI : IsIrreducible O)
    (hZ : Z ∈ irreducibleComponents X) (hmeet : (Z ∩ O).Nonempty) : Z = closure O := by
  have hsub : Z ⊆ closure O :=
    (subset_closure_inter_of_isPreirreducible_of_isOpen hZ.1.2 hO hmeet).trans
      (closure_mono Set.inter_subset_right)
  exact Set.Subset.antisymm hsub (hZ.2 hI.closure hsub)

/-- An isomorphism over a nonempty target open selects exactly one actual
source component with dense image. The topological statement needs no
Noetherianity: maximality is proved from the irreducible source open. -/
theorem unique_dense_component_of_open_preimage
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] [IrreducibleSpace Y]
    (f : X → Y) (hf : Continuous f) {V : Set Y} (hV : IsOpen V)
    (hVne : V.Nonempty) (hI : IsIrreducible (f ⁻¹' V))
    (hsurj : f '' (f ⁻¹' V) = V) :
    ∃! D : irreducibleComponents X, Dense (f '' D.val) := by
  let O : Set X := f ⁻¹' V
  have hO : IsOpen O := hV.preimage hf
  let D : irreducibleComponents X := ⟨closure O, irreducible_open_closure_component hO hI⟩
  have hdense : Dense (f '' D.val) := by
    apply (hV.dense hVne).mono
    rw [← hsurj]
    exact Set.image_mono subset_closure
  refine ⟨D, hdense, ?_⟩
  intro Z hZ
  obtain ⟨y, hyV, x, hxZ, rfl⟩ := hZ.inter_open_nonempty V hV hVne
  apply Subtype.ext
  exact component_eq_closure_of_meets_irreducible_open hO hI Z.property ⟨x, hxZ, hyV⟩

/-- Scheme-level version retaining the actual restricted morphism. -/
theorem unique_dense_component_of_isIso_restrict
    {X Y : Scheme.{u}} [IsIntegral Y] (f : X ⟶ Y)
    (V : Y.Opens) (hV : (V : Set Y).Nonempty) [IsIso (f ∣_ V)] :
    ∃! D : irreducibleComponents X, Dense (f '' D.val) := by
  let : Nonempty V := ⟨⟨hV.choose, hV.choose_spec⟩⟩
  let : IsIntegral V := isIntegral_of_isOpenImmersion V.ι
  let : IsIntegral (f ⁻¹ᵁ V).toScheme := IsIntegral.of_isIso (inv (f ∣_ V))
  apply unique_dense_component_of_open_preimage f f.continuous V.isOpen hV
  · simpa only [Set.image_univ, Scheme.Opens.range_ι, Scheme.Hom.coe_preimage] using
      (IrreducibleSpace.isIrreducible_univ (f ⁻¹ᵁ V).toScheme).image
        (f ⁻¹ᵁ V).ι (f ⁻¹ᵁ V).ι.continuous.continuousOn
  · apply Set.Subset.antisymm (Set.image_preimage_subset _ _)
    intro y hy
    obtain ⟨x, hx⟩ := (f ∣_ V).surjective ⟨y, hy⟩
    refine ⟨x.val, x.property, ?_⟩
    exact (morphismRestrict_base_coe f V x).symm.trans (congrArg Subtype.val hx)

/-- The dense-image component is exactly the closure of the actual inverse open. -/
theorem dense_component_eq_closure_of_isIso_restrict
    {X Y : Scheme.{u}} [IsIntegral Y] (f : X ⟶ Y)
    (V : Y.Opens) (hV : (V : Set Y).Nonempty) [IsIso (f ∣_ V)]
    (D : irreducibleComponents X) (hD : Dense (f '' D.val)) :
    D.val = closure (f ⁻¹' (V : Set Y)) := by
  let : Nonempty V := ⟨⟨hV.choose, hV.choose_spec⟩⟩
  let : IsIntegral V := isIntegral_of_isOpenImmersion V.ι
  let : IsIntegral (f ⁻¹ᵁ V).toScheme := IsIntegral.of_isIso (inv (f ∣_ V))
  have hI : IsIrreducible (f ⁻¹' (V : Set Y)) := by
    simpa only [Set.image_univ, Scheme.Opens.range_ι, Scheme.Hom.coe_preimage] using
      (IrreducibleSpace.isIrreducible_univ (f ⁻¹ᵁ V).toScheme).image
        (f ⁻¹ᵁ V).ι (f ⁻¹ᵁ V).ι.continuous.continuousOn
  obtain ⟨y, hyV, x, hxD, rfl⟩ := hD.inter_open_nonempty V V.isOpen hV
  exact component_eq_closure_of_meets_irreducible_open
    (V.isOpen.preimage f.continuous) hI D.property ⟨x, hxD, hyV⟩

end AlgebraicGeometry.Scheme
