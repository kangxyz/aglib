/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.Koszul.Ideal
public import Aglib.Algebra.Homology.Koszul.Coefficient.Finite
public import Mathlib.LinearAlgebra.Basis.Prod
public import Mathlib.LinearAlgebra.LinearIndependent.Basic
public import Mathlib.RingTheory.Ideal.Cotangent

/-!
# The linear part of the native Koszul differential

The actual two-column splitting gives free terms and degree-one coefficients.
Cotangent independence detects these coefficients modulo the maximal ideal;
the signed two-column differential then gives the result in every degree.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped BigOperators

namespace ChainComplex.Koszul

variable {R : Type u} [CommRing R]

/-- The two actual columns identify a positive term with their product. -/
def singleTensorComponentEquiv (a : R) (K : ChainComplex (ModuleCat R) ℕ) (n : ℕ) :
    (HomologicalComplex.tensorObj (singleComplex R a) K).X (n + 1) ≃ₗ[R]
      K.X (n + 1) × K.X n where
  toLinearMap := (singleTensorπZero a K (n + 1)).hom.prod (singleTensorπOne a K n).hom
  invFun x := singleTensorιZero a K (n + 1) x.1 + singleTensorιOne a K n x.2
  left_inv := singleTensor_decomposition_apply a K n
  right_inv x := by
    ext <;> simp

/-- Every term of the native tensor Koszul complex is free. -/
instance chainComplex_free_X (s : List R) (n : ℕ) :
    Module.Free R ((chainComplex s).X n) := by
  induction s generalizing n with
  | nil =>
    cases n with
    | zero => exact Module.Free.of_equiv (zeroComponentIso []).toLinearEquiv.symm
    | succ n =>
      have : Subsingleton ((chainComplex ([] : List R)).X (n + 1)) :=
        ModuleCat.subsingleton_of_isZero (isZero_X [] (n + 1) (by simp))
      infer_instance
  | cons a s ih =>
    cases n with
    | zero => exact Module.Free.of_equiv (zeroComponentIso (a :: s)).toLinearEquiv.symm
    | succ n =>
      have := ih (n + 1)
      have := ih n
      exact Module.Free.of_equiv (singleTensorComponentEquiv a (chainComplex s) n).symm

private theorem map_mem_ideal_smul_top {M N : Type u} [AddCommGroup M] [AddCommGroup N]
    [Module R M] [Module R N] (I : Ideal R) (g : M →ₗ[R] N) {x : M}
    (hx : x ∈ I • (⊤ : Submodule R M)) : g x ∈ I • (⊤ : Submodule R N) :=
  Submodule.smul_top_le_comap_smul_top I g hx

/-- Coefficients in degree one, formed from the original column projections. -/
def degreeOneCoefficients {I : Ideal R} : (s : List I) →
    (chainComplex (s.map fun x : I => (x : R))).X 1 →ₗ[R] (Fin s.length → R)
  | [] => 0
  | a :: s => LinearMap.pi (Fin.cons
      (((zeroComponentIso (s.map fun x : I => (x : R))).hom.hom).comp
        (singleTensorπOne (a : R) (chainComplex (s.map fun x : I => (x : R))) 0).hom)
      (fun j => (LinearMap.proj j).comp ((degreeOneCoefficients s).comp
        (singleTensorπZero (a : R) (chainComplex (s.map fun x : I => (x : R))) 1).hom)))

theorem degreeOneCoefficients_cons_zero {I : Ideal R} (a : I) (s : List I)
    (z : (chainComplex ((a : R) :: s.map fun x : I => (x : R))).X 1) :
    degreeOneCoefficients (a :: s) z 0 =
      (zeroComponentIso (s.map fun x : I => (x : R))).hom
        (singleTensorπOne (a : R) (chainComplex (s.map fun x : I => (x : R))) 0 z) := rfl

theorem degreeOneCoefficients_cons_succ {I : Ideal R} (a : I) (s : List I)
    (z : (chainComplex ((a : R) :: s.map fun x : I => (x : R))).X 1) (j : Fin s.length) :
    degreeOneCoefficients (a :: s) z j.succ =
      degreeOneCoefficients s
        (singleTensorπZero (a : R) (chainComplex (s.map fun x : I => (x : R))) 1 z) j := rfl

/-- Ideal-valued degree-one coefficients give an element in the ideal times the term. -/
theorem mem_smul_top_of_degreeOneCoefficients_mem (I : Ideal R) (s : List I) :
    ∀ z : (chainComplex (s.map fun x : I => (x : R))).X 1,
      (∀ j, degreeOneCoefficients s z j ∈ I) →
        z ∈ I • (⊤ : Submodule R ((chainComplex (s.map fun x : I => (x : R))).X 1)) := by
  induction s with
  | nil =>
    intro z _
    have : Subsingleton ((chainComplex (([] : List I).map fun x : I => (x : R))).X 1) :=
      ModuleCat.subsingleton_of_isZero
        (isZero_X (([] : List I).map fun x : I => (x : R)) 1 (by simp))
    have hz0 : z = 0 := Subsingleton.elim _ _
    rw [hz0]
    exact Submodule.zero_mem _
  | cons a s ih =>
    intro z hz
    let t := s.map fun x : I => (x : R)
    let K := chainComplex t
    have hu : singleTensorπZero (a : R) K 1 z ∈ I • (⊤ : Submodule R (K.X 1)) :=
      ih _ (fun j => by simpa only [degreeOneCoefficients_cons_succ] using hz j.succ)
    have hc : (zeroComponentIso t).hom (singleTensorπOne (a : R) K 0 z) ∈ I := by
      simpa only [degreeOneCoefficients_cons_zero] using hz 0
    have hv : singleTensorπOne (a : R) K 0 z ∈ I • (⊤ : Submodule R (K.X 0)) := by
      have hh := Submodule.map_le_smul_top I (zeroComponentIso t).inv.hom
        (show (zeroComponentIso t).inv
            ((zeroComponentIso t).hom (singleTensorπOne (a : R) K 0 z)) ∈
            Submodule.map (zeroComponentIso t).inv.hom I from ⟨_, hc, rfl⟩)
      simpa using hh
    rw [← singleTensor_decomposition_apply (a : R) K 0 z]
    exact add_mem (map_mem_ideal_smul_top I (singleTensorιZero (a : R) K 1).hom hu)
      (map_mem_ideal_smul_top I (singleTensorιOne (a : R) K 0).hom hv)

private theorem singleTensorιZero_boundary (a : R) (s : List R) :
    singleTensorιZero a (chainComplex s) 1 ≫ boundaryMap (a :: s) = boundaryMap s := by
  change (λ_ ((chainComplex s).X 1)).inv ≫
    (ιCons a s 0 1 1 rfl ≫ boundaryMap (a :: s)) = _
  erw [ιCons_zero_boundaryMap]
  simp

private theorem singleTensorιOne_boundary (a : R) (s : List R) :
    singleTensorιOne a (chainComplex s) 0 ≫ boundaryMap (a :: s) =
      (zeroComponentIso s).hom ≫ ModuleCat.ofHom (LinearMap.lsmul R R a) := by
  change (λ_ ((chainComplex s).X 0)).inv ≫
    (ιCons a s 1 0 1 rfl ≫ boundaryMap (a :: s)) = _
  erw [ιCons_one_boundaryMap]
  simp

/-- The actual degree-one differential is its coordinate linear combination. -/
theorem boundaryMap_eq_sum_degreeOneCoefficients {I : Ideal R} (s : List I) :
    ∀ z : (chainComplex (s.map fun x : I => (x : R))).X 1,
      boundaryMap (s.map fun x : I => (x : R)) z =
        ∑ j : Fin s.length, degreeOneCoefficients s z j * (s.get j : R) := by
  induction s with
  | nil =>
    intro z
    have : Subsingleton ((chainComplex (([] : List I).map fun x : I => (x : R))).X 1) :=
      ModuleCat.subsingleton_of_isZero
        (isZero_X (([] : List I).map fun x : I => (x : R)) 1 (by simp))
    have hz0 : z = 0 := Subsingleton.elim _ _
    simp [hz0]
  | cons a s ih =>
    intro z
    let t := s.map fun x : I => (x : R)
    let K := chainComplex t
    have h₀ (x : K.X 1) :
        boundaryMap ((a : R) :: t) (singleTensorιZero (a : R) K 1 x) =
          boundaryMap t x :=
      ConcreteCategory.congr_hom (singleTensorιZero_boundary (a : R) t) x
    have h₁ (x : K.X 0) :
        boundaryMap ((a : R) :: t) (singleTensorιOne (a : R) K 0 x) =
          (a : R) * (zeroComponentIso t).hom x :=
      ConcreteCategory.congr_hom (singleTensorιOne_boundary (a : R) t) x
    change (boundaryMap ((a : R) :: t)).hom z = _
    conv_lhs => rw [← singleTensor_decomposition_apply (a : R) K 0 z]
    rw [map_add, h₀, h₁, ih]
    erw [Fin.sum_univ_succ]
    simp only [degreeOneCoefficients_cons_zero, degreeOneCoefficients_cons_succ,
      List.get_eq_getElem, Fin.val_succ, List.getElem_cons_succ]
    exact add_comm _ _ |>.trans (congrArg (fun x => x + _) (mul_comm _ _))

open IsLocalRing

private theorem degreeOne_mem_maximalIdeal_smul_top [IsLocalRing R]
    (s : List (maximalIdeal R))
    (hlin : LinearIndependent (ResidueField R)
      (fun j : Fin s.length => (maximalIdeal R).toCotangent (s.get j)))
    (z : (chainComplex (s.map fun x : maximalIdeal R => (x : R))).X 1)
    (hz : (chainComplex (s.map fun x : maximalIdeal R => (x : R))).d 1 0 z ∈
      maximalIdeal R ^ 2 •
        (⊤ : Submodule R ((chainComplex (s.map fun x : maximalIdeal R => (x : R))).X 0))) :
    z ∈ maximalIdeal R •
      (⊤ : Submodule R ((chainComplex (s.map fun x : maximalIdeal R => (x : R))).X 1)) := by
  classical
  let c := degreeOneCoefficients s z
  have hb : boundaryMap (s.map fun x : maximalIdeal R => (x : R)) z ∈ maximalIdeal R ^ 2 := by
    let t := s.map fun x : maximalIdeal R => (x : R)
    have hh := map_mem_ideal_smul_top (maximalIdeal R ^ 2)
      (zeroComponentIso t).hom.hom hz
    have heq : boundaryMap t z = (zeroComponentIso t).hom ((chainComplex t).d 1 0 z) :=
      ModuleCat.comp_apply _ _ z
    rw [heq]
    simpa only [Ideal.smul_eq_mul, Ideal.mul_top] using hh
  have hs : (maximalIdeal R).toCotangent (∑ j, c j • s.get j) = 0 := by
    apply ((maximalIdeal R).toCotangent_eq_zero _).mpr
    rw [boundaryMap_eq_sum_degreeOneCoefficients] at hb
    simpa only [Submodule.coe_sum, Submodule.coe_smul, smul_eq_mul] using hb
  have hrel : ∑ j, residue R (c j) • (maximalIdeal R).toCotangent (s.get j) = 0 := by
    calc
      _ = ∑ j, (maximalIdeal R).toCotangent (c j • s.get j) := by
        apply Finset.sum_congr rfl
        intro j _
        rw [← ResidueField.algebraMap_eq, algebraMap_smul, map_smul]
      _ = (maximalIdeal R).toCotangent (∑ j, c j • s.get j) := by rw [map_sum]
      _ = 0 := hs
  apply mem_smul_top_of_degreeOneCoefficients_mem (maximalIdeal R) s z
  intro j
  exact (residue_eq_zero_iff (R := R) _).mp ((Fintype.linearIndependent_iff.mp hlin) _ hrel j)

/-- Cotangent-independent ideal entries give an injective native differential linear part. -/
theorem mem_maximalIdeal_smul_top_of_d_mem_sq_list [IsLocalRing R]
    (s : List (maximalIdeal R))
    (hlin : LinearIndependent (ResidueField R)
      (fun j : Fin s.length => (maximalIdeal R).toCotangent (s.get j)))
    (i : ℕ) :
    ∀ z : (chainComplex (s.map fun x : maximalIdeal R => (x : R))).X (i + 1),
      (chainComplex (s.map fun x : maximalIdeal R => (x : R))).d (i + 1) i z ∈
          maximalIdeal R ^ 2 •
            (⊤ : Submodule R ((chainComplex (s.map fun x : maximalIdeal R => (x : R))).X i)) →
        z ∈ maximalIdeal R •
          (⊤ : Submodule R
            ((chainComplex (s.map fun x : maximalIdeal R => (x : R))).X (i + 1))) := by
  induction s generalizing i with
  | nil =>
    intro z _
    have : Subsingleton
        ((chainComplex (([] : List (maximalIdeal R)).map
          fun x : maximalIdeal R => (x : R))).X (i + 1)) :=
      ModuleCat.subsingleton_of_isZero
        (isZero_X (([] : List (maximalIdeal R)).map
          fun x : maximalIdeal R => (x : R)) (i + 1) (by simp))
    have hz0 : z = 0 := Subsingleton.elim _ _
    rw [hz0]
    exact Submodule.zero_mem _
  | cons a s ih =>
    have htail : LinearIndependent (ResidueField R)
        (fun j : Fin s.length => (maximalIdeal R).toCotangent (s.get j)) := by
      simpa only [Function.comp_def, List.get_eq_getElem, Fin.val_succ,
        List.getElem_cons_succ] using
        hlin.comp (fun j : Fin s.length => j.succ) (Fin.succ_injective _)
    cases i with
    | zero => exact degreeOne_mem_maximalIdeal_smul_top (a :: s) hlin
    | succ i =>
      intro z hz
      let t := s.map fun x : maximalIdeal R => (x : R)
      let K := chainComplex t
      have hv : singleTensorπOne (a : R) K (i + 1) z ∈
          maximalIdeal R • (⊤ : Submodule R (K.X (i + 1))) := by
        apply ih htail i
        have hh : singleTensorπOne (a : R) K i
            ((HomologicalComplex.tensorObj (singleComplex R (a : R)) K).d
              (i + 2) (i + 1) z) ∈
              maximalIdeal R ^ 2 • (⊤ : Submodule R (K.X i)) :=
          map_mem_ideal_smul_top (maximalIdeal R ^ 2)
            (singleTensorπOne (a : R) K i).hom hz
        rw [singleTensorπOne_d_apply] at hh
        exact (Submodule.neg_mem_iff _).mp hh
      have hu : singleTensorπZero (a : R) K (i + 2) z ∈
          maximalIdeal R • (⊤ : Submodule R (K.X (i + 2))) := by
        apply ih htail (i + 1)
        have hh : singleTensorπZero (a : R) K (i + 1)
            ((HomologicalComplex.tensorObj (singleComplex R (a : R)) K).d
              (i + 2) (i + 1) z) ∈
              maximalIdeal R ^ 2 • (⊤ : Submodule R (K.X (i + 1))) :=
          map_mem_ideal_smul_top (maximalIdeal R ^ 2)
            (singleTensorπZero (a : R) K (i + 1)).hom hz
        rw [singleTensorπZero_d_apply] at hh
        have ha : (a : R) • singleTensorπOne (a : R) K (i + 1) z ∈
            maximalIdeal R ^ 2 • (⊤ : Submodule R (K.X (i + 1))) := by
          rw [pow_two, Submodule.mul_smul]
          exact Submodule.smul_mem_smul a.property hv
        simpa only [add_sub_cancel_right] using sub_mem hh ha
      rw [← singleTensor_decomposition_apply (a : R) K (i + 1) z]
      exact add_mem
        (map_mem_ideal_smul_top (maximalIdeal R) (singleTensorιZero (a : R) K (i + 2)).hom hu)
        (map_mem_ideal_smul_top (maximalIdeal R) (singleTensorιOne (a : R) K (i + 1)).hom hv)

/-- For cotangent-independent entries, a boundary in the square forces its input into `m`. -/
theorem mem_maximalIdeal_smul_top_of_d_mem_sq [IsLocalRing R] {e : ℕ}
    (f : Fin e → maximalIdeal R)
    (hlin : LinearIndependent (ResidueField R)
      (fun j => (maximalIdeal R).toCotangent (f j))) (i : ℕ) :
    ∀ z : (chainComplex (List.ofFn fun j => (f j : R))).X (i + 1),
      (chainComplex (List.ofFn fun j => (f j : R))).d (i + 1) i z ∈
          maximalIdeal R ^ 2 •
            (⊤ : Submodule R ((chainComplex (List.ofFn fun j => (f j : R))).X i)) →
        z ∈ maximalIdeal R •
          (⊤ : Submodule R ((chainComplex (List.ofFn fun j => (f j : R))).X (i + 1))) := by
  have hlist : LinearIndependent (ResidueField R)
      (fun j : Fin (List.ofFn f).length =>
        (maximalIdeal R).toCotangent ((List.ofFn f).get j)) := by
    simpa only [Function.comp_def, List.get_ofFn] using
      hlin.comp (Fin.cast (List.length_ofFn (f := f))) (Fin.cast_injective _)
  have hmap : (List.ofFn f).map (fun x : maximalIdeal R => (x : R)) =
      List.ofFn (fun j => (f j : R)) := List.map_ofFn
  rw [← hmap]
  exact mem_maximalIdeal_smul_top_of_d_mem_sq_list (List.ofFn f) hlist i

end ChainComplex.Koszul
