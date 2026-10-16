/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Motivic Cohomology contributors
-/
module

public import Aglib.Algebra.Homology.Koszul.Augmentation
public import Aglib.Algebra.Homology.Koszul.Differential
public import Mathlib.RingTheory.Regular.RegularSequence

/-!
# The boundary ideal of a finite Koszul complex

The degree-one differential is transported along the canonical identification
of degree zero with the ring. Its image is proved equal to the ideal generated
by the input list. This identifies the categorical degree-zero homology with
the genuine ideal quotient and constructs the corresponding augmentation.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped TensorProduct

namespace ChainComplex.Koszul

variable {R : Type u} [CommRing R]

/-- The actual differential with degree-zero target identified as the ring. -/
noncomputable def boundaryMap (s : List R) : (chainComplex s).X 1 ⟶ ModuleCat.of R R :=
  (chainComplex s).d 1 0 ≫ (zeroComponentIso s).hom

/-- The ideal given by the actual degree-one boundary image. -/
noncomputable def boundaryIdeal (s : List R) : Ideal R := LinearMap.range (boundaryMap s).hom

@[reassoc]
theorem ιCons_zero_zero_zeroComponentIso (a : R) (s : List R) :
    ιCons a s 0 0 0 rfl ≫ (zeroComponentIso (a :: s)).hom =
      (λ_ ((chainComplex s).X 0)).hom ≫ (zeroComponentIso s).hom := by
  change HomologicalComplex.ιTensorObj (singleComplex R a) (chainComplex s) 0 0 0 rfl ≫
    (tensorZeroDesc (singleComplex R a) (chainComplex s) ≫
      ((𝟙 (ModuleCat.of R R)) ⊗ₘ (zeroComponentIso s).hom) ≫
        (λ_ (ModuleCat.of R R)).hom) = _
  rw [← Category.assoc, tensorZeroDesc, HomologicalComplex.ι_mapBifunctorDesc]
  simp only [eqToHom_refl]
  exact leftUnitor_naturality (zeroComponentIso s).hom

@[reassoc]
theorem ιCons_zero_boundaryMap (a : R) (s : List R) :
    ιCons a s 0 1 1 rfl ≫ boundaryMap (a :: s) =
      (λ_ ((chainComplex s).X 1)).hom ≫ boundaryMap s := by
  unfold boundaryMap
  erw [← Category.assoc, ιCons_zero_d, Category.assoc,
    ιCons_zero_zero_zeroComponentIso, ← Category.assoc, leftUnitor_naturality]
  rfl

@[reassoc]
theorem ιCons_one_boundaryMap (a : R) (s : List R) :
    ιCons a s 1 0 1 rfl ≫ boundaryMap (a :: s) =
      (λ_ ((chainComplex s).X 0)).hom ≫ (zeroComponentIso s).hom ≫
        ModuleCat.ofHom (LinearMap.lsmul R R a) := by
  unfold boundaryMap
  erw [← Category.assoc, ιCons_one_zero_d, Category.assoc,
    ιCons_zero_zero_zeroComponentIso]
  apply ModuleCat.hom_ext
  refine TensorProduct.ext (LinearMap.ext fun r => LinearMap.ext fun x => ?_)
  change R at r
  change (zeroComponentIso s).hom ((a * r) • x) =
    a * (zeroComponentIso s).hom (r • x)
  simp only [mul_smul, map_smul, smul_eq_mul]

/-- An actual boundary ideal lies in an ideal precisely when its quotient kills the differential. -/
theorem boundaryIdeal_le_iff (s : List R) (I : Ideal R) :
    boundaryIdeal s ≤ I ↔ boundaryMap s ≫ ModuleCat.ofHom I.mkQ = 0 := by
  constructor
  · intro h
    apply ModuleCat.hom_ext
    apply LinearMap.range_le_ker_iff.mp
    change LinearMap.range (boundaryMap s).hom ≤ LinearMap.ker I.mkQ
    rw [Submodule.ker_mkQ]
    exact h
  · intro h
    have hh := LinearMap.range_le_ker_iff.mpr (ModuleCat.hom_ext_iff.mp h)
    change LinearMap.range (boundaryMap s).hom ≤ LinearMap.ker I.mkQ at hh
    rw [Submodule.ker_mkQ] at hh
    exact hh

set_option backward.isDefEq.respectTransparency false in
/-- The new scalar and old boundaries generate all the boundaries in the tensor recursion. -/
theorem boundaryIdeal_cons_le_iff (a : R) (s : List R) (I : Ideal R) :
    boundaryIdeal (a :: s) ≤ I ↔ a ∈ I ∧ boundaryIdeal s ≤ I := by
  rw [boundaryIdeal_le_iff]
  constructor
  · intro h
    have hm : ModuleCat.ofHom (LinearMap.lsmul R R a) ≫ ModuleCat.ofHom I.mkQ = 0 := by
      apply (cancel_epi ((λ_ ((chainComplex s).X 0)).hom ≫ (zeroComponentIso s).hom)).mp
      have hnew := congrArg (fun f => ιCons a s 1 0 1 rfl ≫ f) h
      erw [← Category.assoc, ιCons_one_boundaryMap] at hnew
      simpa only [Category.assoc, comp_zero] using hnew
    constructor
    · have hx := congrArg (fun f : ModuleCat.of R R ⟶ ModuleCat.of R (R ⧸ I) => f 1) hm
      change (Submodule.Quotient.mk (a * 1) : R ⧸ I) = 0 at hx
      rw [mul_one] at hx
      exact (Submodule.Quotient.mk_eq_zero I).mp hx
    · rw [boundaryIdeal_le_iff]
      apply (cancel_epi (λ_ ((chainComplex s).X 1)).hom).mp
      have hnew := congrArg (fun f => ιCons a s 0 1 1 rfl ≫ f) h
      erw [← Category.assoc, ιCons_zero_boundaryMap] at hnew
      simpa only [Category.assoc, comp_zero] using hnew
  · rintro ⟨ha, hs⟩
    have hm : ModuleCat.ofHom (LinearMap.lsmul R R a) ≫ ModuleCat.ofHom I.mkQ = 0 := by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro r
      change (Submodule.Quotient.mk (a * r) : R ⧸ I) = 0
      exact (Submodule.Quotient.mk_eq_zero I).mpr (I.mul_mem_right r ha)
    have ht := (boundaryIdeal_le_iff s I).mp hs
    apply HomologicalComplex.mapBifunctor.hom_ext
    intro i j hij
    change i + j = 1 at hij
    have hi : i = 0 ∨ i = 1 := by omega
    rcases hi with rfl | rfl
    · have hj : j = 1 := by omega
      subst j
      change ιCons a s 0 1 1 rfl ≫ (boundaryMap (a :: s) ≫ ModuleCat.ofHom I.mkQ) = _
      erw [← Category.assoc, ιCons_zero_boundaryMap, Category.assoc, ht]
      simp only [comp_zero]
    · have hj : j = 0 := by omega
      subst j
      change ιCons a s 1 0 1 rfl ≫ (boundaryMap (a :: s) ≫ ModuleCat.ofHom I.mkQ) = _
      erw [← Category.assoc, ιCons_one_boundaryMap, Category.assoc, Category.assoc, hm]
      simp only [comp_zero]

@[simp]
theorem boundaryIdeal_nil : boundaryIdeal ([] : List R) = ⊥ := by
  have h : boundaryMap ([] : List R) = 0 := (isZero_X [] 1 (by simp)).eq_of_src _ _
  rw [boundaryIdeal, h]
  exact LinearMap.range_zero

/-- The boundary ideal satisfies the genuine ideal-generation recursion. -/
theorem boundaryIdeal_cons (a : R) (s : List R) :
    boundaryIdeal (a :: s) = Ideal.span {a} ⊔ boundaryIdeal s := by
  apply le_antisymm
  · exact (boundaryIdeal_cons_le_iff a s _).mpr
      ⟨Submodule.mem_sup_left (Ideal.subset_span (Set.mem_singleton a)), le_sup_right⟩
  · have h := (boundaryIdeal_cons_le_iff a s (boundaryIdeal (a :: s))).mp le_rfl
    refine sup_le (Ideal.span_le.mpr ?_) h.2
    intro r hr
    obtain rfl := Set.mem_singleton_iff.mp hr
    exact h.1

/-- The actual differential image is exactly the ideal generated by the input list. -/
theorem boundaryIdeal_eq_ofList (s : List R) : boundaryIdeal s = Ideal.ofList s := by
  induction s with
  | nil => rw [boundaryIdeal_nil, Ideal.ofList_nil]
  | cons a s ih => rw [boundaryIdeal_cons, Ideal.ofList_cons, ih]

/-- The literal finite Koszul homology quotient is the actual generated ideal quotient. -/
noncomputable def idealQuotientEquiv (s : List R) :
    HomologyZeroQuotient s ≃ₗ[R] R ⧸ Ideal.ofList s :=
  Submodule.Quotient.equiv _ _ (zeroComponentIso s).toLinearEquiv (by
    rw [← LinearMap.range_comp]
    exact boundaryIdeal_eq_ofList s)

/-- Degree-zero homology of the constructed finite complex is R modulo the list ideal. -/
noncomputable def homologyZeroIdealIso (s : List R) :
    (chainComplex s).homology 0 ≅ ModuleCat.of R (R ⧸ Ideal.ofList s) :=
  homologyZeroIso s ≪≫ (idealQuotientEquiv s).toModuleIso

/-- The actual augmentation to the genuine ideal quotient. -/
noncomputable def idealAugmentation (s : List R) :
    chainComplex s ⟶ (ChainComplex.single₀ (ModuleCat R)).obj
      (ModuleCat.of R (R ⧸ Ideal.ofList s)) :=
  augmentation s ≫
    (ChainComplex.single₀ (ModuleCat R)).map (idealQuotientEquiv s).toModuleIso.hom

/-- The ideal augmentation computes degree zero for every finite list. -/
theorem idealAugmentation_quasiIsoAt_zero (s : List R) : QuasiIsoAt (idealAugmentation s) 0 := by
  have := augmentation_quasiIsoAt_zero s
  unfold idealAugmentation
  infer_instance

end ChainComplex.Koszul
