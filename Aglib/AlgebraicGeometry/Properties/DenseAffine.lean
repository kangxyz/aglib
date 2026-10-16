/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Noetherian

/-!
# Dense affine neighborhoods with finitely many irreducible components

An affine open can be enlarged to contain every generic point when the scheme
has finitely many irreducible components. The enlargement adds finitely many
disjoint affine opens, using the native finite disjoint-union theorem.
No reducedness, irreducibility or separation hypothesis is needed.
-/

@[expose] public section

noncomputable section

open TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme

variable {X : Scheme.{u}}

/-- An affine open of a scheme with finitely many irreducible components is contained
in an affine open containing all generic points. -/
theorem exists_isAffineOpen_superset_genericPoints
    (hX : (irreducibleComponents X).Finite) {V : X.Opens} (hV : IsAffineOpen V) :
    ∃ U : X.Opens, IsAffineOpen U ∧ V ≤ U ∧ genericPoints X ⊆ U := by
  classical
  let : Finite (irreducibleComponents X) := hX.to_subtype
  let E (Z : irreducibleComponents X) : X.Opens :=
    ⟨(⋃₀ (irreducibleComponents X \ {Z.val}))ᶜ, by
      rw [isOpen_compl_iff, Set.sUnion_eq_biUnion]
      exact hX.sdiff.isClosed_biUnion fun W hW =>
        isClosed_of_mem_irreducibleComponents W hW.1⟩
  have hEclosure (Z : irreducibleComponents X) : closure (E Z : Set X) = Z.val :=
    closure_sUnion_irreducibleComponents_sdiff_singleton hX Z.val Z.property
  have hEsub (Z : irreducibleComponents X) : (E Z : Set X) ⊆ Z.val := by
    rw [← hEclosure Z]
    exact subset_closure
  have hEmem (Z : irreducibleComponents X) : (genericPoints.ofComponent Z).val ∈ E Z := by
    obtain ⟨z, hz⟩ : (E Z : Set X).Nonempty := by
      rw [← closure_nonempty_iff, hEclosure]
      exact Z.property.1.1
    exact ((genericPoints.isGenericPoint_ofComponent Z).mem_open_set_iff (E Z).isOpen).mpr
      ⟨z, hEsub Z hz, hz⟩
  let A := {Z : irreducibleComponents X // (genericPoints.ofComponent Z).val ∉ V}
  have hW (a : A) : ∃ W : X.Opens,
      IsAffineOpen W ∧ (genericPoints.ofComponent a.val).val ∈ W ∧ W ≤ E a.val :=
    exists_isAffineOpen_mem_and_subset (hEmem a.val)
  choose W hWaff hWmem hWle using hW
  have hWdisj : Pairwise (fun a b : A => Disjoint (W a) (W b)) := by
    intro a b hab
    rw [← Opens.coe_disjoint]
    apply Set.disjoint_left.mpr
    intro z hza hzb
    have hba : b.val.val ≠ a.val.val := by
      intro h
      exact hab (Subtype.ext (Subtype.ext h.symm))
    have hzE := hWle a hza
    change z ∉ ⋃₀ (irreducibleComponents X \ {a.val.val}) at hzE
    apply hzE
    exact Set.mem_sUnion.mpr ⟨b.val.val,
      ⟨b.val.property, by simpa only [Set.mem_singleton_iff] using hba⟩,
      hEsub b.val (hWle b hzb)⟩
  have hVdisj : Disjoint V (⨆ a, W a) := by
    rw [disjoint_iSup_iff]
    intro a
    rw [← Opens.coe_disjoint]
    apply Set.disjoint_left.mpr
    intro z hzV hzW
    have hd := ((genericPoints.isGenericPoint_ofComponent a.val).disjoint_iff V.isOpen).mpr
      a.property
    exact Set.disjoint_left.mp hd (hEsub a.val (hWle a hzW)) hzV
  refine ⟨V ⊔ ⨆ a, W a,
    hV.sup_of_disjoint (IsAffineOpen.iSup_of_disjoint hWaff hWdisj) hVdisj,
    le_sup_left, ?_⟩
  intro x hx
  by_cases hxV : x ∈ V
  · exact (show V ≤ V ⊔ ⨆ a, W a from le_sup_left) hxV
  · let Z := genericPoints.component (⟨x, hx⟩ : genericPoints X)
    have hxZ : (genericPoints.ofComponent Z).val = x :=
      congrArg Subtype.val (genericPoints.ofComponent_component ⟨x, hx⟩)
    let a : A := ⟨Z, by simpa only [hxZ] using hxV⟩
    have hxW : x ∈ W a := by
      have hm : (genericPoints.ofComponent Z).val ∈ W a := hWmem a
      rwa [hxZ] at hm
    exact (show (⨆ a, W a) ≤ V ⊔ ⨆ a, W a from le_sup_right) ((le_iSup W a) hxW)

/-- Every point has a dense affine neighborhood when there are finitely many
irreducible components. -/
theorem exists_dense_isAffineOpen_mem_of_finite_irreducibleComponents
    (hX : (irreducibleComponents X).Finite) (x : X) :
    ∃ U : X.Opens, IsAffineOpen U ∧ x ∈ U ∧ genericPoints X ⊆ U ∧ Dense (U : Set X) := by
  obtain ⟨V, hV, hxV, -⟩ := exists_isAffineOpen_mem_and_subset
    (show x ∈ (⊤ : X.Opens) from trivial)
  obtain ⟨U, hU, hVU, hgen⟩ := exists_isAffineOpen_superset_genericPoints hX hV
  refine ⟨U, hU, hVU hxV, hgen, ?_⟩
  rw [dense_iff_closure_eq]
  apply Set.eq_univ_of_forall
  intro y
  exact closure_mono hgen (by rw [genericPoints.closure]; trivial)

/-- A quasi-compact scheme with finitely many irreducible components has a finite affine
cover whose members and common intersection are dense. Every member contains all generic
points. The empty scheme is allowed. -/
theorem exists_finite_dense_affine_cover_of_finite_irreducibleComponents
    [CompactSpace X] (hX : (irreducibleComponents X).Finite) :
    ∃ (ι : Type u) (_ : Fintype ι) (U : ι → X.Opens),
      (∀ i, IsAffineOpen (U i) ∧ Dense (U i : Set X) ∧ genericPoints X ⊆ U i) ∧
      (⨆ i, U i) = ⊤ ∧ Dense ((⨅ i, U i : X.Opens) : Set X) := by
  classical
  choose U hUaff hUmem hUgen hUdense using
    exists_dense_isAffineOpen_mem_of_finite_irreducibleComponents hX
  have hcover : (Set.univ : Set X) ⊆ ⋃ x, (U x : Set X) := by
    intro x _
    exact Set.mem_iUnion.mpr ⟨x, hUmem x⟩
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover
    (fun x => (U x : Set X)) (fun x => (U x).isOpen) hcover
  refine ⟨s, inferInstance, fun x => U x.val,
    fun x => ⟨hUaff x.val, hUdense x.val, hUgen x.val⟩, ?_, ?_⟩
  · apply top_unique
    intro x _
    obtain ⟨y, hy, hxy⟩ := Set.mem_iUnion₂.mp (hs (Set.mem_univ x))
    exact Opens.mem_iSup.mpr ⟨⟨y, hy⟩, hxy⟩
  · apply Dense.mono ?_ (dense_iff_closure_eq.mpr (genericPoints.closure (α := X)))
    intro x hx
    change x ∈ (((⨅ a : s, U a.val) : X.Opens) : Set X)
    rw [Opens.coe_iInf]
    exact Set.mem_iInter.mpr fun a => hUgen a.val hx

/-- A Noetherian scheme has a finite cover by dense affine opens with dense common
intersection, without irreducibility or reducedness assumptions. -/
theorem exists_finite_dense_affine_cover [IsNoetherian X] :
    ∃ (ι : Type u) (_ : Fintype ι) (U : ι → X.Opens),
      (∀ i, IsAffineOpen (U i) ∧ Dense (U i : Set X) ∧ genericPoints X ⊆ U i) ∧
      (⨆ i, U i) = ⊤ ∧ Dense ((⨅ i, U i : X.Opens) : Set X) :=
  exists_finite_dense_affine_cover_of_finite_irreducibleComponents
    NoetherianSpace.finite_irreducibleComponents

end AlgebraicGeometry.Scheme
