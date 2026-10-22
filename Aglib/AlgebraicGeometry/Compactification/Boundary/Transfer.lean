/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Compactification.Boundary.ProjectedCentres
public import Aglib.AlgebraicGeometry.Blowup.SchematicDensity
public import Aglib.AlgebraicGeometry.Blowup.BaseChange

/-!
# Transferring boundary control to the modified original image

The additional blowup uses the literal pullback of the original sum centre.
Its comparison map is the native universal blowup map, never a nonflat
base-change isomorphism. Schematic density is preserved along this actual
blowup, and properness plus the original unit locus supplies surjectivity.
-/

@[expose] public noncomputable section
set_option autoImplicit false
open CategoryTheory Limits TopologicalSpace
universe u v

namespace AlgebraicGeometry.Scheme.Compactification

/-- Transfer the projected closure bounds to the modified common image.
All input closure bounds refer to the literal original fibre products. The
unit hypothesis is on the original source, and is supplied by its actual
inclusion in the common protected open. -/
theorem boundary_empty_of_projected_control
    {M M' U : Scheme.{u}} [IsLocallyNoetherian M'] {ι : Type v}
    {Y Y' : ι → Scheme.{u}} (π : ∀ i, M ⟶ Y i) (π' : ∀ i, M' ⟶ Y' i)
    (β : ∀ i, Y' i ⟶ Y i) (r : M' ⟶ M)
    (hπ : ∀ i, π' i ≫ β i = r ≫ π i)
    (j : U ⟶ M) (j' : U ⟶ M') [QuasiCompact j'] [IsSchemeTheoreticallyDominant j']
    (hj : j' ≫ r = j) (V : ∀ i, (Y i).Opens)
    (hV : ∀ i, Set.range (j ≫ π i) ⊆ V i)
    (I : M.IdealSheafData) (hI : I.comap j = ⊤) (B : Blowup.BlowupDatum I)
    (F : ∀ i, Set (Y i)) (T : ι → Closeds B.Y)
    (hT : (⋂ i, (T i : Set B.Y)) = ∅)
    (hcontrol : ∀ i (D : Set B.Y), D ⊆ (B.map ≫ π i) ⁻¹' (V i : Set (Y i)) →
      (pullback.snd (B.map ≫ π i) (β i) ⁻¹' closure (β i ⁻¹' F i)) ∩
        closure (pullback.fst (B.map ≫ π i) (β i) ⁻¹' D) ⊆
          pullback.fst (B.map ≫ π i) (β i) ⁻¹' (T i : Set B.Y)) :
    (⋂ i, π' i ⁻¹' closure (β i ⁻¹' F i)) = ∅ := by
  let C := Blowup.blowupDatum (I.comap r)
  let b : C.Y ⟶ B.Y := Blowup.BaseChange.map r rfl B C
  have hb : b ≫ B.map = C.map ≫ r := Blowup.BaseChange.map_triangle r rfl B C
  have hIj : (I.comap r).comap j' = ⊤ := by
    rw [← IdealSheafData.comap_comp, hj, hI]
  let t : U ⟶ C.Y := C.lift j' (Blowup.cartier_of_comap_eq_top (I.comap r) j' hIj)
  have ht : t ≫ C.map = j' := C.lift_map _ _
  let : IsProper C.map := C.isProper_of_isLocallyNoetherian
  let : IsDominant C.map := ⟨j'.denseRange.mono (by
    rintro _ ⟨x, rfl⟩
    exact ⟨t x, congrArg (fun f : U ⟶ M' => f x) ht⟩)⟩
  let Q := pullback C.map j'
  let a : Q ⟶ C.Y := pullback.fst C.map j'
  let u : Q ⟶ U := pullback.snd C.map j'
  let : IsSchemeTheoreticallyDominant a := C.pullback_fst_isSchemeTheoreticallyDominant j'
  have hab : a ≫ b ≫ B.map = u ≫ j := by
    rw [hb, ← Category.assoc, pullback.condition, Category.assoc, hj]
  let D : Set B.Y := B.map ⁻¹' Set.range j
  have hD : ∀ i, D ⊆ (B.map ≫ π i) ⁻¹' (V i : Set (Y i)) := by
    intro i x hx
    obtain ⟨z, hz⟩ := hx
    have hh := hV i ⟨z, rfl⟩
    change π i (B.map x) ∈ V i
    rw [← hz]
    exact hh
  have hbounds : ∀ i, (C.map ≫ π' i) ⁻¹' closure (β i ⁻¹' F i) ⊆
      b ⁻¹' (T i : Set B.Y) := by
    intro i
    have hw : b ≫ (B.map ≫ π i) = (C.map ≫ π' i) ≫ β i := by
      rw [← Category.assoc, hb, Category.assoc, ← hπ i, Category.assoc]
    let k : C.Y ⟶ pullback (B.map ≫ π i) (β i) :=
      pullback.lift b (C.map ≫ π' i) hw
    have hk₁ : k ≫ pullback.fst (B.map ≫ π i) (β i) = b := pullback.lift_fst _ _ _
    have hk₂ : k ≫ pullback.snd (B.map ≫ π i) (β i) = C.map ≫ π' i :=
      pullback.lift_snd _ _ _
    have hrange : Set.range a ⊆ k ⁻¹'
        closure (pullback.fst (B.map ≫ π i) (β i) ⁻¹' D) := by
      rintro _ ⟨z, rfl⟩
      apply subset_closure
      change B.map (pullback.fst (B.map ≫ π i) (β i) (k (a z))) ∈ Set.range j
      have hkval := congrArg (fun f : C.Y ⟶ B.Y => f (a z)) hk₁
      change pullback.fst (B.map ≫ π i) (β i) (k (a z)) = b (a z) at hkval
      rw [hkval]
      refine ⟨u z, ?_⟩
      exact (congrArg (fun f : Q ⟶ M => f z) hab).symm
    have hclosure : ∀ z : C.Y,
        k z ∈ closure (pullback.fst (B.map ≫ π i) (β i) ⁻¹' D) := by
      have hh := closure_minimal hrange (isClosed_closure.preimage k.continuous)
      rw [a.denseRange.closure_range] at hh
      exact fun z => hh (Set.mem_univ z)
    intro z hz
    have hkval := congrArg (fun f : C.Y ⟶ Y' i => f z) hk₂
    change pullback.snd (B.map ≫ π i) (β i) (k z) = (C.map ≫ π' i) z at hkval
    have hz' : k z ∈ pullback.snd (B.map ≫ π i) (β i) ⁻¹'
        closure (β i ⁻¹' F i) := by
      change pullback.snd (B.map ≫ π i) (β i) (k z) ∈ closure (β i ⁻¹' F i)
      rw [hkval]
      exact hz
    have hh := hcontrol i D (hD i) ⟨hz', hclosure z⟩
    have hfval := congrArg (fun f : C.Y ⟶ B.Y => f z) hk₁
    change pullback.fst (B.map ≫ π i) (β i) (k z) = b z at hfval
    change pullback.fst (B.map ≫ π i) (β i) (k z) ∈ T i at hh
    rwa [hfval] at hh
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro x hx
  obtain ⟨z, rfl⟩ := C.map.surjective x
  have hz : b z ∈ ⋂ i, (T i : Set B.Y) := by
    apply Set.mem_iInter.mpr
    intro i
    exact hbounds i (Set.mem_iInter.mp hx i)
  rw [hT] at hz
  exact hz

end AlgebraicGeometry.Scheme.Compactification
