/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.AlgebraicGeometry.IdealSheaf.IrreducibleComponent
public import Aglib.AlgebraicGeometry.IdealSheaf.Closed.RadicalSubscheme
public import Aglib.AlgebraicGeometry.IdealSheaf.Closed.ReducedClosedUnion
public import Aglib.AlgebraicGeometry.Limits.Range
public import Aglib.AlgebraicGeometry.Limits.FiniteCoproductPullback

/-!
# The original component cover is an isomorphism on a dense open

The native closed component subschemes of a reduced Noetherian scheme are
integral. Their literal coproduct map is surjective and becomes an isomorphism
on the union of the native opens which avoid all other components. That union
contains every generic point and is dense. The construction allows the empty
scheme and uses no field or dimension hypothesis. Its consumer is reduction
of curve cohomological dimension to proper integral components.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme.IrreducibleComponentCover

variable (X : Scheme.{u}) [IsNoetherian X]

local instance : Finite (irreducibleComponents X) :=
  NoetherianSpace.finite_irreducibleComponents.to_subtype

/-- The family consists of the original native closed component subschemes. -/
abbrev component (c : irreducibleComponents X) : Scheme.{u} :=
  X.irreducibleComponent c.val c.property

/-- The original closed inclusion of a component. -/
abbrev inclusion (c : irreducibleComponents X) : component X c ⟶ X :=
  X.irreducibleComponentι c.val c.property

/-- The native component inclusion has its original component as range. -/
theorem inclusion_range (c : irreducibleComponents X) :
    Set.range (inclusion X c) = c.val := by
  change Set.range (X.irreducibleComponentIdeal c.val c.property).subschemeι = _
  rw [IdealSheafData.range_subschemeι]
  rfl

/-- Reducedness of the original scheme makes its native component subschemes integral. -/
instance component_isIntegral [IsReduced X] (c : irreducibleComponents X) :
    IsIntegral (component X c) := by
  have hr : IsReduced (component X c) := by
    apply IdealSheafData.subscheme_reduced_of_radical
    rw [irreducibleComponentIdeal_def]
    exact IdealSheafData.kernel_radical _
  exact isIntegral_of_irreducibleSpace_of_isReduced _

/-- The native open part of a component avoiding every other component. -/
abbrev piece (c : irreducibleComponents X) : X.Opens :=
  X.irreducibleComponentOpen c.val

/-- Each isolated component open has the original component as closure. -/
theorem closure_piece (c : irreducibleComponents X) :
    closure (piece X c : Set X) = c.val :=
  closure_sUnion_irreducibleComponents_sdiff_singleton
    NoetherianSpace.finite_irreducibleComponents c.val c.property

/-- The isolated open is contained in its component. -/
theorem piece_subset (c : irreducibleComponents X) : (piece X c : Set X) ⊆ c.val := by
  rw [← closure_piece X c]
  exact subset_closure

/-- Every isolated component open contains its actual generic point. -/
theorem genericPoint_mem_piece (c : irreducibleComponents X) :
    (genericPoints.ofComponent c).val ∈ piece X c := by
  obtain ⟨z, hz⟩ : (piece X c : Set X).Nonempty := by
    rw [← closure_nonempty_iff, closure_piece]
    exact c.property.1.nonempty
  exact ((genericPoints.isGenericPoint_ofComponent c).mem_open_set_iff
    (piece X c).isOpen).mpr ⟨z, piece_subset X c hz, hz⟩

/-- The isolated component opens are pairwise disjoint. -/
theorem piece_disjoint : Pairwise (fun c d => Disjoint (piece X c) (piece X d)) := by
  intro c d hcd
  rw [← Opens.coe_disjoint]
  apply Set.disjoint_left.mpr
  intro x hxc hxd
  change x ∉ ⋃₀ (irreducibleComponents X \ {c.val}) at hxc
  apply hxc
  refine Set.mem_sUnion.mpr ⟨d.val, ⟨d.property, ?_⟩, piece_subset X d hxd⟩
  simpa only [Set.mem_singleton_iff] using
    (show d.val ≠ c.val from fun h => hcd (Subtype.ext h.symm))

/-- The common open over which the original components separate. -/
def separatingOpen : X.Opens := ⨆ c, piece X c

/-- The separating open contains every original component generic point. -/
theorem genericPoints_subset_separatingOpen : genericPoints X ⊆ separatingOpen X := by
  intro x hx
  let c := genericPoints.component (⟨x, hx⟩ : genericPoints X)
  have he : (genericPoints.ofComponent c).val = x :=
    congrArg Subtype.val (genericPoints.ofComponent_component ⟨x, hx⟩)
  have hm := genericPoint_mem_piece X c
  rw [he] at hm
  exact (le_iSup (piece X) c) hm

/-- The original separating open is dense, including for the empty scheme. -/
theorem separatingOpen_dense : Dense (separatingOpen X : Set X) := by
  apply Dense.mono (genericPoints_subset_separatingOpen X)
  exact dense_iff_closure_eq.mpr genericPoints.closure

instance separatingOpen_dominant : IsDominant (separatingOpen X).ι :=
  Opens.isDominant_ι (separatingOpen_dense X)

/-- A point of a component in the separating open lies in that component's own piece. -/
theorem mem_piece_of_mem_component (c : irreducibleComponents X) {x : X}
    (hxc : x ∈ c.val) (hx : x ∈ separatingOpen X) : x ∈ piece X c := by
  obtain ⟨d, hd⟩ := Opens.mem_iSup.mp hx
  by_cases hdc : d = c
  · simpa only [hdc] using hd
  · change x ∉ ⋃₀ (irreducibleComponents X \ {d.val}) at hd
    exact (hd (Set.mem_sUnion.mpr
      ⟨c.val, ⟨c.property, fun h => hdc (Subtype.ext h.symm)⟩, hxc⟩)).elim

/-- The literal coproduct of the original component inclusions. -/
def map : (∐ component X) ⟶ X := Sigma.desc (inclusion X)

/-- The original component coproduct covers the entire scheme. -/
instance map_surjective : Surjective (map X) := by
  apply Surjective.sigmaDesc_of_union_range_eq_univ
  apply Set.eq_univ_of_forall
  intro x
  let c : irreducibleComponents X :=
    ⟨_root_.irreducibleComponent x, irreducibleComponent_mem_irreducibleComponents x⟩
  exact Set.mem_iUnion.mpr ⟨c, (inclusion_range X c).symm ▸ mem_irreducibleComponent⟩

variable [IsReduced X]

/-- The original component restriction to its isolated open is an isomorphism. -/
instance pieceRestriction_isIso (c : irreducibleComponents X) :
    IsIso (inclusion X c ∣_ piece X c) := by
  have hs : Surjective (inclusion X c ∣_ piece X c) := by
    constructor
    intro x
    obtain ⟨y, hy⟩ := (inclusion_range X c).symm ▸ piece_subset X c x.property
    refine ⟨⟨y, ?_⟩, ?_⟩
    · change inclusion X c y ∈ piece X c
      simpa only [hy] using x.property
    · apply Subtype.ext
      exact (morphismRestrict_base_coe (inclusion X c) (piece X c) _).trans hy
  exact isIso_of_isClosedImmersion_of_surjective _

omit [IsReduced X] in
/-- Restriction to the separating open agrees with restriction to the component's own piece. -/
theorem component_preimage_separatingOpen (c : irreducibleComponents X) :
    inclusion X c ⁻¹ᵁ separatingOpen X = inclusion X c ⁻¹ᵁ piece X c := by
  ext y
  constructor
  · exact mem_piece_of_mem_component X c
      ((inclusion_range X c) ▸ Set.mem_range_self y)
  · exact fun hy => (le_iSup (piece X) c) hy

/-- Each original component restricts to an open component of the separating open. -/
instance restriction_isOpenImmersion (c : irreducibleComponents X) :
    IsOpenImmersion (inclusion X c ∣_ separatingOpen X) := by
  let e := (component X c).isoOfEq (component_preimage_separatingOpen X c)
  let hle : piece X c ≤ separatingOpen X := le_iSup (piece X) c
  let k := X.homOfLE hle
  have : IsOpenImmersion k := inferInstanceAs (IsOpenImmersion (X.homOfLE hle))
  have he : inclusion X c ∣_ separatingOpen X =
      e.hom ≫ (inclusion X c ∣_ piece X c) ≫ k := by
    apply (cancel_mono (separatingOpen X).ι).mp
    dsimp only [e, k]
    rw [morphismRestrict_ι, Category.assoc, Category.assoc, homOfLE_ι,
      morphismRestrict_ι, ← Category.assoc, isoOfEq_hom_ι]
  rw [he]
  infer_instance

omit [IsReduced X] in
/-- The original range of each restriction is its isolated piece inside the common open. -/
theorem restriction_range (c : irreducibleComponents X) :
    Set.range (inclusion X c ∣_ separatingOpen X) =
      (separatingOpen X).ι ⁻¹' (piece X c : Set X) := by
  rw [Scheme.Pullback.Fibre.pullback_range_fst
    (isPullback_morphismRestrict (inclusion X c) (separatingOpen X)), inclusion_range]
  ext x
  exact ⟨fun hx => mem_piece_of_mem_component X c hx x.property,
    fun hx => piece_subset X c hx⟩

/-- The original coproduct map becomes an isomorphism after the literal separating-open pullback. -/
theorem pullback_map_isIso : IsIso (pullback.snd (map X) (separatingOpen X).ι) := by
  let P (c : irreducibleComponents X) :=
    (inclusion X c ⁻¹ᵁ separatingOpen X).toScheme
  let q (c : irreducibleComponents X) : P c ⟶ separatingOpen X :=
    inclusion X c ∣_ separatingOpen X
  have hd : Pairwise (fun c d => Disjoint (Set.range (q c)) (Set.range (q d))) := by
    intro c d hcd
    rw [restriction_range, restriction_range]
    exact (Opens.coe_disjoint.mpr (piece_disjoint X hcd)).preimage _
  have : IsOpenImmersion (Sigma.desc q) := isOpenImmersion_sigmaDesc P q hd
  have : Surjective (Sigma.desc q) := by
    apply Surjective.sigmaDesc_of_union_range_eq_univ
    apply Set.eq_univ_of_forall
    intro x
    obtain ⟨c, hc⟩ := Opens.mem_iSup.mp x.property
    exact Set.mem_iUnion.mpr ⟨c, (restriction_range X c).symm ▸ hc⟩
  have : IsIso (Sigma.desc q) :=
    (isIso_iff_isOpenImmersion_and_surjective _).mpr ⟨inferInstance, inferInstance⟩
  have H := (FinitaryPreExtensive.isUniversal_finiteCoproducts
    (coproductIsCoproduct (component X))).isPullback_of_isColimit_right
      (inclusion X) (map X) (separatingOpen X).ι
      (fun c => (inclusion X c ⁻¹ᵁ separatingOpen X).ι) q
      (fun c => (isPullback_morphismRestrict (inclusion X c) (separatingOpen X)).flip)
      (coproductIsCoproduct P) (fun c => by simp [map])
  have H' : IsPullback
      (Limits.Sigma.map (fun c => (inclusion X c ⁻¹ᵁ separatingOpen X).ι))
      (Sigma.desc q) (map X) (separatingOpen X).ι := by
    convert! H using 1
  have : IsIso (H'.isoPullback.hom ≫ pullback.snd (map X) (separatingOpen X).ι) := by
    rw [H'.isoPullback_hom_snd]
    infer_instance
  exact IsIso.of_isIso_comp_left H'.isoPullback.hom _

/-- The same statement for the literal original morphism restriction. -/
instance map_restrict_isIso : IsIso (map X ∣_ separatingOpen X) := by
  have := pullback_map_isIso X
  have : IsIso ((pullbackRestrictIsoRestrict (map X) (separatingOpen X)).hom ≫
      map X ∣_ separatingOpen X) := by
    rw [pullbackRestrictIsoRestrict_hom_morphismRestrict]
    infer_instance
  exact IsIso.of_isIso_comp_left
    (pullbackRestrictIsoRestrict (map X) (separatingOpen X)).hom _

end AlgebraicGeometry.Scheme.IrreducibleComponentCover
