/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.Koszul.Ext.Quotient
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-!
# Top Koszul Ext with arbitrary coefficients

The original top Koszul cocycle identifies native top Ext with the actual
coefficient quotient by the list ideal. The equivalence is linear over the
original quotient ring, and its literal representative and coefficient maps
retain the original cocycle and native Yoneda postcomposition.

The proof descends from the ring coefficient through the original coordinate
projections on free modules and the native Ext sequence of an actual free
presentation. The coefficient needs no regularity, flatness, finiteness or
Noetherian hypothesis. Empty lists, unit equations and zero rings are included.
The ring and coefficient carrier universe is common, as in the finite Koszul
construction; the supported Ext size is independent. Lower-degree vanishing
uses additional coefficient regularity. Localization and determinant changes
are downstream consumers of these same original classes.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
open scoped Pointwise
noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u w

namespace ChainComplex.Koszul
variable {R : Type u} [CommRing R] [HasExt.{w} (ModuleCat.{u} R)]

private theorem topExtClass_ideal_smul_le_ker (s : List R)
    (hs : RingTheory.Sequence.IsWeaklyRegular R s)
    (N : ModuleCat.{u} R) :
    (Ideal.ofList s) • (⊤ : Submodule R N) ≤ LinearMap.ker (topExtClass s hs N) := by
  apply Submodule.smul_le.mpr
  intro r hr x _
  change topExtClass s hs N (r • x) = 0
  rw [(topExtClass s hs N).map_smul]
  exact Ext.quotientSourceIsTorsionBySet (Ideal.ofList s) N s.length (a := ⟨r, hr⟩)

private theorem topExtClass_finsupp_eq_zero_mem (s : List R)
    (hs : RingTheory.Sequence.IsWeaklyRegular R s)
    {ι : Type u} (x : ι →₀ R)
    (hx : topExtClass s hs (ModuleCat.of R (ι →₀ R)) x = 0) :
    x ∈ (Ideal.ofList s) • (⊤ : Submodule R (ι →₀ R)) := by
  classical
  have hcoord (i : ι) : x i ∈ Ideal.ofList s := by
    let g : ModuleCat.of R (ι →₀ R) ⟶ ModuleCat.of R R :=
      ModuleCat.ofHom (Finsupp.lapply i)
    have h := topExtClass_comp_mk₀ s hs g x
    have hg : g x = x i := rfl
    have hz : topExtClass s hs (ModuleCat.of R R) (x i) = 0 := by
      simpa only [hx, Ext.zero_comp, hg] using h.symm
    have hmem : x i ∈ LinearMap.ker (topExtClass.{u,w} s hs (ModuleCat.of R R)) := hz
    exact (topExtClass_ring_ker.{u,w} s hs) ▸ hmem
  rw [← Finsupp.sum_single x]
  change (∑ i ∈ x.support, Finsupp.single i (x i)) ∈
    (Ideal.ofList s) • (⊤ : Submodule R (ι →₀ R))
  apply Submodule.sum_mem
  intro i _
  simpa only [Finsupp.smul_single, smul_eq_mul, mul_one] using
    (Submodule.smul_mem_smul (hcoord i)
      (show (Finsupp.single i (1 : R) : ι →₀ R) ∈ (⊤ : Submodule R (ι →₀ R)) from trivial))

/-- The original top class has exactly the list-ideal multiples as its kernel,
for every coefficient. -/
theorem topExtClass_ker (s : List R) (hs : RingTheory.Sequence.IsWeaklyRegular R s)
    (N : ModuleCat.{u} R) :
    LinearMap.ker (topExtClass s hs N) = (Ideal.ofList s) • (⊤ : Submodule R N) := by
  apply le_antisymm
  · intro x hx
    let F : ModuleCat.{u} R := ModuleCat.of R (N →₀ R)
    let π : F ⟶ N := ModuleCat.ofHom (Finsupp.linearCombination R (id : N → N))
    let : Epi π := (ModuleCat.epi_iff_surjective π).mpr
      (Finsupp.linearCombination_id_surjective R N)
    let S := ShortComplex.kernelSequence π
    have hS : S.ShortExact := {
      exact := ShortComplex.kernelSequence_exact π
      mono_f := by change Mono (kernel.ι π); infer_instance
      epi_g := by change Epi π; infer_instance }
    obtain ⟨y, hy⟩ := Finsupp.linearCombination_id_surjective R N x
    have hπy : π y = x := hy
    have hc : (topExtClass s hs F y).comp (Ext.mk₀ S.g) (add_zero s.length) = 0 := by
      rw [topExtClass_comp_mk₀]
      change topExtClass s hs N (π y) = 0
      rw [hπy]
      exact hx
    obtain ⟨z, hz⟩ := Ext.covariant_sequence_exact₂
      (X := ModuleCat.of R (R ⧸ Ideal.ofList s)) hS (topExtClass s hs F y) hc
    obtain ⟨k, hk⟩ := topExtClass_surjective s hs (kernel π) z
    have hrep : topExtClass s hs F ((kernel.ι π) k) = topExtClass s hs F y := by
      calc
        _ = (topExtClass s hs (kernel π) k).comp (Ext.mk₀ (kernel.ι π))
            (add_zero s.length) := (topExtClass_comp_mk₀ s hs (kernel.ι π) k).symm
        _ = _ := by rw [hk]; exact hz
    have hd : topExtClass s hs F (y - (kernel.ι π) k) = 0 := by
      rw [map_sub, hrep, sub_self]
    have hm := topExtClass_finsupp_eq_zero_mem s hs (y - (kernel.ι π) k) hd
    have hzero : π ((kernel.ι π) k) = 0 :=
      ConcreteCategory.congr_hom (kernel.condition π) k
    have hprod : π (y - (kernel.ι π) k) = x := by
      rw [π.hom.map_sub, hzero, sub_zero]
      exact hy
    have hmap := (Submodule.smul_top_le_comap_smul_top (Ideal.ofList s) π.hom) hm
    change π (y - (kernel.ι π) k) ∈ (Ideal.ofList s) • (⊤ : Submodule R N) at hmap
    rwa [hprod] at hmap
  · exact topExtClass_ideal_smul_le_ker s hs N

/-- The actual coefficient quotient computes native top Ext through the original Koszul class. -/
def topExtLinearEquiv (s : List R) (hs : RingTheory.Sequence.IsWeaklyRegular R s)
    (N : ModuleCat.{u} R) :
    (N ⧸ ((Ideal.ofList s) • (⊤ : Submodule R N))) ≃ₗ[R]
      Ext.{w} (ModuleCat.of R (R ⧸ Ideal.ofList s)) N s.length :=
  (Submodule.quotEquivOfEq _ _ (topExtClass_ker s hs N).symm).trans
    ((topExtClass s hs N).quotKerEquivOfSurjective (topExtClass_surjective s hs N))

/-- A quotient representative gives the same original finite-resolution cocycle class. -/
@[simp]
theorem topExtLinearEquiv_apply_mk (s : List R) (hs : RingTheory.Sequence.IsWeaklyRegular R s)
    (N : ModuleCat.{u} R) (x : N) :
    topExtLinearEquiv.{u,w} s hs N (Submodule.Quotient.mk x) = topExtClass s hs N x := by
  simp only [topExtLinearEquiv, LinearEquiv.trans_apply, Submodule.quotEquivOfEq_mk,
    LinearMap.quotKerEquivOfSurjective_apply_mk]

/-- The unchanged top Ext equivalence is linear for the native quotient-ring actions. -/
def topExtQuotientLinearEquiv (s : List R) (hs : RingTheory.Sequence.IsWeaklyRegular R s)
    (N : ModuleCat.{u} R) :
    letI := Ext.quotientSourceModule.{u,w} (Ideal.ofList s) N s.length
    (N ⧸ ((Ideal.ofList s) • (⊤ : Submodule R N))) ≃ₗ[R ⧸ Ideal.ofList s]
      Ext.{w} (ModuleCat.of R (R ⧸ Ideal.ofList s)) N s.length := by
  letI := Ext.quotientSourceModule.{u,w} (Ideal.ofList s) N s.length
  refine {
    __ := (topExtLinearEquiv.{u,w} s hs N).toAddEquiv
    map_smul' := ?_ }
  intro b x
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective b
  obtain ⟨m, rfl⟩ := Submodule.mkQ_surjective
    ((Ideal.ofList s) • (⊤ : Submodule R N)) x
  change topExtLinearEquiv.{u,w} s hs N
      (Ideal.Quotient.mk (Ideal.ofList s) r • Submodule.Quotient.mk m) =
    Ideal.Quotient.mk (Ideal.ofList s) r •
      topExtLinearEquiv.{u,w} s hs N (Submodule.Quotient.mk m)
  rw [Module.Quotient.mk_smul_mk, topExtLinearEquiv_apply_mk, topExtLinearEquiv_apply_mk,
    Ext.quotientSourceModule_mk_smul]
  exact (topExtClass s hs N).map_smul r m

/-- Quotient-linearity retains the original cocycle on every coefficient representative. -/
@[simp]
theorem topExtQuotientLinearEquiv_apply_mk (s : List R)
    (hs : RingTheory.Sequence.IsWeaklyRegular R s) (N : ModuleCat.{u} R) (x : N) :
    topExtQuotientLinearEquiv.{u,w} s hs N (Submodule.Quotient.mk x) = topExtClass s hs N x :=
  topExtLinearEquiv_apply_mk s hs N x

/-- The quotient-ring refinement keeps exactly the original additive equivalence. -/
@[simp]
theorem topExtQuotientLinearEquiv_toAddEquiv (s : List R)
    (hs : RingTheory.Sequence.IsWeaklyRegular R s) (N : ModuleCat.{u} R) :
    letI := Ext.quotientSourceModule.{u,w} (Ideal.ofList s) N s.length
    (topExtQuotientLinearEquiv.{u,w} s hs N).toAddEquiv =
      (topExtLinearEquiv.{u,w} s hs N).toAddEquiv := rfl

/-- Original coefficient quotient maps give exactly native Yoneda postcomposition. -/
theorem topExtQuotientLinearEquiv_naturality (s : List R)
    (hs : RingTheory.Sequence.IsWeaklyRegular R s) {N N' : ModuleCat.{u} R}
    (g : N ⟶ N') (x : N ⧸ ((Ideal.ofList s) • (⊤ : Submodule R N))) :
    (topExtQuotientLinearEquiv.{u,w} s hs N x).comp (Ext.mk₀ g) (add_zero s.length) =
      topExtQuotientLinearEquiv.{u,w} s hs N'
        ((((Ideal.ofList s) • (⊤ : Submodule R N)).mapQ
          ((Ideal.ofList s) • (⊤ : Submodule R N')) g.hom
          (Submodule.smul_top_le_comap_smul_top (Ideal.ofList s) g.hom)) x) := by
  obtain ⟨m, rfl⟩ := Submodule.mkQ_surjective
    ((Ideal.ofList s) • (⊤ : Submodule R N)) x
  change (topExtQuotientLinearEquiv.{u,w} s hs N (Submodule.Quotient.mk m)).comp
      (Ext.mk₀ g) (add_zero s.length) =
    topExtQuotientLinearEquiv.{u,w} s hs N' (Submodule.Quotient.mk (g m))
  rw [topExtQuotientLinearEquiv_apply_mk, topExtQuotientLinearEquiv_apply_mk]
  exact topExtClass_comp_mk₀ s hs g m

end ChainComplex.Koszul
