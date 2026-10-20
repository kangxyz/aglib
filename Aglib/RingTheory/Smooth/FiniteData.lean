/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.RingTheory.Smooth.FiniteModel
public import Mathlib.RingTheory.Smooth.NoetherianDescent
public import Mathlib.RingTheory.Smooth.Flat
public import Mathlib.LinearAlgebra.TensorProduct.Finiteness

/-!
B12 affine smooth descent supplier, on the pinned Lean/Mathlib basis.
No proper spreading, bundle or semicontinuity conclusion is asserted here.
-/

/-!
## Migration source

Native extraction from `lean/R5Lab/Aglib/RingTheory/Smooth/FiniteData.lean` at R5 revision
`f8a3314ddecffcada2ec721d26d56a937bed9690`, SHA-256
`8ebb8f61cd3daaf8705767829fc40fe0f251f44454b755ff23bd68f1efe2142f`.
-/

@[expose] public section

noncomputable section

open _root_.TensorProduct

namespace Algebra.Smooth.FiniteData

universe u

/-- An actual smooth algebra has a smooth finite constant-base model that
contains any prescribed finite chart data and finite constant data. The map
to the original algebra is injective and is the map of the displayed base
change equivalence on `1 ⊗ z`. -/
theorem exists_smooth_model_with_finite_data
    (K B : Type u) [Field K] [CommRing B] [Algebra K B] [Algebra.Smooth K B]
    (data : Finset B) (baseExtra : Finset K) :
    ∃ (A : Type u) (C : Type u) (_ : CommRing A) (_ : CommRing C)
      (_ : Algebra ℤ A) (_ : Algebra A K) (_ : Algebra A C),
      Function.Injective (algebraMap A K) ∧ Algebra.FiniteType ℤ A ∧
      Algebra.Smooth A C ∧
      (∀ x ∈ baseExtra, x ∈ Set.range (algebraMap A K)) ∧
      ∃ e : K ⊗[A] C ≃ₐ[K] B,
        Function.Injective (fun z : C => e (1 ⊗ₜ[A] z)) ∧
        ∀ t ∈ data, ∃ z : C, e (1 ⊗ₜ[A] z) = t := by
  classical
  obtain ⟨A, C, iC, iAC, hA, hC, hbase, e, hinj, hdata⟩ :=
    Algebra.Smooth.FiniteModel.exists_smooth_model_with_finite_data
      (C := K) (B := B) data baseExtra
  let := iC
  let := iAC
  let := hC
  refine ⟨A, C, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    Subtype.val_injective, A.fg_iff_finiteType.mp hA, hC, ?_, e, hinj, hdata⟩
  intro x hx
  exact ⟨⟨x, hbase x hx⟩, rfl⟩

/-- Factor the unchanged finite relation ring through an injective model map.
The finite generator inclusion suffices for the entire original ring map. -/
theorem exists_lift_of_generators_in_range
    {L C : Type u} [Field L] [CommRing C]
    (data : Finset L) (f : C →+* L) (hf : Function.Injective f)
    (hdata : ∀ x ∈ data, x ∈ f.range) :
    ∃ lift : Subring.closure (data : Set L) →+* C,
      f.comp lift = (Subring.closure (data : Set L)).subtype := by
  have hle : Subring.closure (data : Set L) ≤ f.range :=
    Subring.closure_le.mpr hdata
  let inc := Subring.inclusion hle
  have hfi : Function.Injective f.rangeRestrict := by
    intro x y hxy
    exact hf (congrArg Subtype.val hxy)
  let e : C ≃+* f.range :=
    RingEquiv.ofBijective f.rangeRestrict ⟨hfi, f.rangeRestrict_surjective⟩
  refine ⟨e.symm.toRingHom.comp inc, ?_⟩
  ext x
  change f (e.symm (inc x)) = (x : L)
  change (e (e.symm (inc x)) : L) = (x : L)
  rw [e.apply_symm_apply]
  rfl

/-- A smooth affine algebra containing the original relation ring admits a
smooth finite constant-base model through which that exact map factors.
Neither the source function field nor its K2 is mapped to a finite fibre. -/
theorem exists_smooth_model_carrying_subring
    (K B L : Type u) [Field K] [CommRing B] [Algebra K B] [Algebra.Smooth K B]
    [Field L] (j : B →+* L) (hj : Function.Injective j)
    (data : Finset L)
    (originalLift : Subring.closure (data : Set L) →+* B)
    (hOriginal : j.comp originalLift =
      (Subring.closure (data : Set L)).subtype)
    (extra : Finset B) (baseExtra : Finset K) :
    ∃ (A : Type u) (C : Type u) (_ : CommRing A) (_ : CommRing C)
      (_ : Algebra ℤ A) (_ : Algebra A K) (_ : Algebra A C),
      Function.Injective (algebraMap A K) ∧ Algebra.FiniteType ℤ A ∧
      Algebra.Smooth A C ∧
      (∀ x ∈ baseExtra, x ∈ Set.range (algebraMap A K)) ∧
      ∃ e : K ⊗[A] C ≃ₐ[K] B,
        let f : C →+* B := e.toRingHom.comp
          (Algebra.TensorProduct.includeRight : C →ₐ[A] K ⊗[A] C).toRingHom
        Function.Injective f ∧ (∀ t ∈ extra, t ∈ Set.range f) ∧
        ∃ lift : Subring.closure (data : Set L) →+* C,
          f.comp lift = originalLift ∧
          (j.comp f).comp lift =
            (Subring.closure (data : Set L)).subtype := by
  classical
  let generators : Finset B := data.attach.image (fun x =>
    originalLift ⟨x.val, Subring.subset_closure x.property⟩)
  obtain ⟨A, C, instA, instC, instZA, instAK, instAC, hAinj, hAft, hCsmooth,
    hbase, e, hfinj, hdata⟩ :=
    exists_smooth_model_with_finite_data K B (extra ∪ generators) baseExtra
  let : CommRing A := instA
  let : CommRing C := instC
  let : Algebra ℤ A := instZA
  let : Algebra A K := instAK
  let : Algebra A C := instAC
  let f : C →+* B := e.toRingHom.comp
    (Algebra.TensorProduct.includeRight : C →ₐ[A] K ⊗[A] C).toRingHom
  have hf : Function.Injective f := hfinj
  have hgen : ∀ x ∈ data, x ∈ (j.comp f).range := by
    intro x hx
    obtain ⟨z, hz⟩ := hdata
      (originalLift ⟨x, Subring.subset_closure hx⟩)
      (Finset.mem_union_right _ (Finset.mem_image.mpr
        ⟨⟨x, hx⟩, Finset.mem_attach _ _, rfl⟩))
    refine ⟨z, ?_⟩
    change j (e (1 ⊗ₜ[A] z)) = x
    rw [hz]
    exact RingHom.congr_fun hOriginal ⟨x, Subring.subset_closure hx⟩
  obtain ⟨lift, hlift⟩ := exists_lift_of_generators_in_range data
    (j.comp f) (hj.comp hf) hgen
  refine ⟨A, C, instA, instC, instZA, instAK, instAC, hAinj, hAft, hCsmooth,
    hbase, e, hf, ?_, lift, ?_, hlift⟩
  · intro t ht
    exact hdata t (Finset.mem_union_left _ ht)
  · ext x
    apply hj
    exact (RingHom.congr_fun hlift x).trans (RingHom.congr_fun hOriginal x).symm

end Algebra.Smooth.FiniteData
