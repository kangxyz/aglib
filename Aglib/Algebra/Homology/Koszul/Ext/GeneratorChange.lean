/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.Koszul.Ext.Top
public import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic
public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.Tactic.Module

/-!
# Determinant covariance of the original ordered Koszul Ext class

The comparison is built on the original recursive tensor complexes. Insertion
by each row of the change-of-generators matrix gives its actual chain map.
Its degree-zero component preserves the original quotient augmentation and
its top component is the determinant in the original ordered top frames.
The matrix need not be invertible over the ring. The public overlap theorem
uses the same ideal and the original quotient map, with only the necessary
transport between the two equal list lengths.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open CategoryTheory.MonoidalCategory
open HomologicalComplex
universe u w

namespace ChainComplex.Koszul
namespace GeneratorChange
variable {R : Type u} [CommRing R]

private def value : (s : List R) → (Fin s.length → R) → R
  | [], _ => 0
  | a :: s, v => v 0 * a + value s (v ∘ Fin.succ)

private theorem value_eq_sum (s : List R) (v : Fin s.length → R) :
    value s v = ∑ i, v i * s.get i := by
  induction s with
  | nil => simp [value]
  | cons a s ih => simp [value, Fin.sum_univ_succ, ih]

private def insert : (s : List R) → (Fin s.length → R) →
    (n : ℕ) → (chainComplex s).X n →ₗ[R] (chainComplex s).X (n + 1)
  | [], _, _ => 0
  | a :: s, v, 0 =>
      (singleTensorιZero a (chainComplex s) 1).hom.comp
          ((insert s (v ∘ Fin.succ) 0).comp (singleTensorπZero a (chainComplex s) 0).hom) +
        (singleTensorιOne a (chainComplex s) 0).hom.comp
          ((LinearMap.lsmul R ((chainComplex s).X 0) (v 0)).comp
            (singleTensorπZero a (chainComplex s) 0).hom)
  | a :: s, v, n + 1 =>
      (singleTensorιZero a (chainComplex s) (n + 2)).hom.comp
          ((insert s (v ∘ Fin.succ) (n + 1)).comp
            (singleTensorπZero a (chainComplex s) (n + 1)).hom) +
        (singleTensorιOne a (chainComplex s) (n + 1)).hom.comp
          ((LinearMap.lsmul R ((chainComplex s).X (n + 1)) (v 0)).comp
            (singleTensorπZero a (chainComplex s) (n + 1)).hom) -
        (singleTensorιOne a (chainComplex s) (n + 1)).hom.comp
          ((insert s (v ∘ Fin.succ) n).comp (singleTensorπOne a (chainComplex s) n).hom)

private theorem insert_ιZero (a : R) (s : List R)
    (v : Fin (a :: s).length → R) (n : ℕ) (x : (chainComplex s).X n) :
    insert (a :: s) v n (singleTensorιZero a (chainComplex s) n x) =
      singleTensorιZero a (chainComplex s) (n + 1) (insert s (v ∘ Fin.succ) n x) +
        singleTensorιOne a (chainComplex s) n (v 0 • x) := by
  cases n <;> simp [insert, LinearMap.comp_apply]

private theorem insert_ιOne (a : R) (s : List R)
    (v : Fin (a :: s).length → R) (n : ℕ) (x : (chainComplex s).X n) :
    insert (a :: s) v (n + 1) (singleTensorιOne a (chainComplex s) n x) =
      -singleTensorιOne a (chainComplex s) (n + 1) (insert s (v ∘ Fin.succ) n x) := by
  simp [insert, LinearMap.comp_apply]

private theorem tensor_linear_ext (a : R) (s : List R)
    (Z : ModuleCat.{u} R) (n : ℕ)
    {f g : (chainComplex (a :: s)).X n →ₗ[R] Z}
    (h₀ : ∀ x, f (singleTensorιZero a (chainComplex s) n x) =
      g (singleTensorιZero a (chainComplex s) n x))
    (h₁ : ∀ m (hm : n = m + 1), ∀ x,
      f (((chainComplex (a :: s)).XIsoOfEq hm.symm).hom
        (singleTensorιOne a (chainComplex s) m x)) =
      g (((chainComplex (a :: s)).XIsoOfEq hm.symm).hom
        (singleTensorιOne a (chainComplex s) m x))) : f = g := by
  ext x
  cases n with
  | zero =>
    rw [← singleTensor_decomposition_zero_apply a (chainComplex s) x]
    exact h₀ _
  | succ n =>
    have h₁' (y : (chainComplex s).X n) :
        f (singleTensorιOne a (chainComplex s) n y) =
          g (singleTensorιOne a (chainComplex s) n y) := h₁ n rfl y
    rw [← singleTensor_decomposition_apply a (chainComplex s) n x,
      map_add, map_add, h₀, h₁']

private theorem insert_add (s : List R) (v z : Fin s.length → R) (n : ℕ) :
    insert s (v + z) n = insert s v n + insert s z n := by
  induction s generalizing n with
  | nil => simp [insert]
  | cons a s ih =>
    apply tensor_linear_ext a s _ n
    · intro x
      simp only [insert_ιZero, LinearMap.add_apply, Pi.add_apply, add_smul]
      have h := LinearMap.congr_fun (ih (v ∘ Fin.succ) (z ∘ Fin.succ) n) x
      change insert s ((v + z) ∘ Fin.succ) n x = _ at h
      rw [h]
      simp only [LinearMap.add_apply, map_add]
      module
    · intro m hm x
      subst n
      simp only [HomologicalComplex.XIsoOfEq_rfl, Iso.refl_hom, ModuleCat.id_apply]
      simp only [insert_ιOne, LinearMap.add_apply]
      have h := LinearMap.congr_fun (ih (v ∘ Fin.succ) (z ∘ Fin.succ) m) x
      change insert s ((v + z) ∘ Fin.succ) m x = _ at h
      rw [h]
      simp only [LinearMap.add_apply, map_add]
      module

private theorem insert_smul (s : List R) (r : R) (v : Fin s.length → R) (n : ℕ) :
    insert s (r • v) n = r • insert s v n := by
  induction s generalizing n with
  | nil => simp [insert]
  | cons a s ih =>
    apply tensor_linear_ext a s _ n
    · intro x
      simp only [insert_ιZero, LinearMap.smul_apply, Pi.smul_apply, smul_eq_mul]
      have h := LinearMap.congr_fun (ih (v ∘ Fin.succ) n) x
      change insert s ((r • v) ∘ Fin.succ) n x = _ at h
      rw [h]
      simp only [LinearMap.smul_apply, map_smul, mul_smul, smul_add]
    · intro m hm x
      subst n
      simp only [HomologicalComplex.XIsoOfEq_rfl, Iso.refl_hom, ModuleCat.id_apply]
      simp only [insert_ιOne, LinearMap.smul_apply]
      have h := LinearMap.congr_fun (ih (v ∘ Fin.succ) m) x
      change insert s ((r • v) ∘ Fin.succ) m x = _ at h
      rw [h]
      simp only [LinearMap.smul_apply, map_smul, smul_neg]

@[simp] private theorem insert_zero (s : List R) (n : ℕ) : insert s 0 n = 0 := by
  simpa using insert_smul s 0 (0 : Fin s.length → R) n

private theorem insert_sq (s : List R) (v : Fin s.length → R) (n : ℕ)
    (x : (chainComplex s).X n) : insert s v (n + 1) (insert s v n x) = 0 := by
  induction s generalizing n with
  | nil => simp only [insert, LinearMap.zero_apply]
  | cons a s ih =>
    have hz : (insert (a :: s) v (n + 1)).comp (insert (a :: s) v n) = 0 := by
      apply tensor_linear_ext a s _ n
      · intro y
        simp only [LinearMap.comp_apply, insert_ιZero, map_add, insert_ιOne,
          map_smul, ih, map_zero, zero_add, LinearMap.zero_apply]
        module
      · intro m hm y
        subst n
        simp only [HomologicalComplex.XIsoOfEq_rfl, Iso.refl_hom, ModuleCat.id_apply]
        simp only [LinearMap.comp_apply, insert_ιOne, map_neg, ih, map_zero,
          neg_zero, LinearMap.zero_apply]
    exact LinearMap.congr_fun hz x

private theorem cons_d_ιZero (a : R) (s : List R) (n : ℕ)
    (x : (chainComplex s).X (n + 1)) :
    (chainComplex (a :: s)).d (n + 1) n (singleTensorιZero a (chainComplex s) (n + 1) x) =
      singleTensorιZero a (chainComplex s) n ((chainComplex s).d (n + 1) n x) :=
  singleTensor_d_ιZero_apply a (chainComplex s) n x

private theorem cons_d_ιOne (a : R) (s : List R) (n : ℕ)
    (x : (chainComplex s).X (n + 1)) :
    (chainComplex (a :: s)).d (n + 2) (n + 1)
        (singleTensorιOne a (chainComplex s) (n + 1) x) =
      singleTensorιZero a (chainComplex s) (n + 1) (a • x) -
        singleTensorιOne a (chainComplex s) n ((chainComplex s).d (n + 1) n x) :=
  singleTensor_d_ιOne_apply a (chainComplex s) n x

private theorem cons_d_ιOne_zero (a : R) (s : List R)
    (x : (chainComplex s).X 0) :
    (chainComplex (a :: s)).d 1 0 (singleTensorιOne a (chainComplex s) 0 x) =
      singleTensorιZero a (chainComplex s) 0 (a • x) :=
  singleTensor_d_ιOne_zero_apply a (chainComplex s) x

private theorem insert_homotopy (s : List R) (v : Fin s.length → R) :
    (∀ x : (chainComplex s).X 0,
      (chainComplex s).d 1 0 (insert s v 0 x) = value s v • x) ∧
    (∀ n (x : (chainComplex s).X (n + 1)),
      (chainComplex s).d (n + 2) (n + 1) (insert s v (n + 1) x) +
        insert s v n ((chainComplex s).d (n + 1) n x) = value s v • x) := by
  induction s with
  | nil =>
    simp only [insert, value, LinearMap.zero_apply, map_zero, zero_add, zero_smul,
      forall_const, and_self]
  | cons a s ih =>
    obtain ⟨h₀, h₁⟩ := ih (v ∘ Fin.succ)
    constructor
    · intro x
      rw [← singleTensor_decomposition_zero_apply a (chainComplex s) x]
      simp only [insert_ιZero, map_add, cons_d_ιZero,
        cons_d_ιOne_zero, h₀, value, map_smul, add_smul]
      module
    · intro n x
      have hlin : ((chainComplex (a :: s)).d (n + 2) (n + 1)).hom.comp
          (insert (a :: s) v (n + 1)) +
          (insert (a :: s) v n).comp ((chainComplex (a :: s)).d (n + 1) n).hom =
          LinearMap.lsmul R ((chainComplex (a :: s)).X (n + 1)) (value (a :: s) v) := by
        apply tensor_linear_ext a s _ (n + 1)
        · intro y
          simp only [LinearMap.add_apply, LinearMap.comp_apply, insert_ιZero,
            map_add, cons_d_ιZero, cons_d_ιOne,
            map_smul, LinearMap.lsmul_apply, value]
          have h := congrArg (fun z => singleTensorιZero a (chainComplex s) (n + 1) z)
            (h₁ n y)
          simp only [map_add, map_smul] at h
          have he := (eq_sub_iff_add_eq).mpr (h₁ n y)
          rw [he]
          simp only [map_sub, map_smul]
          module
        · intro m hm y
          have he : m = n := by omega
          subst m
          simp only [HomologicalComplex.XIsoOfEq_rfl, Iso.refl_hom, ModuleCat.id_apply]
          cases n with
          | zero =>
            change (chainComplex (a :: s)).d 2 1
                (insert (a :: s) v 1 (singleTensorιOne a (chainComplex s) 0 y)) +
              insert (a :: s) v 0 ((chainComplex (a :: s)).d 1 0
                (singleTensorιOne a (chainComplex s) 0 y)) =
              value (a :: s) v • singleTensorιOne a (chainComplex s) 0 y
            rw [insert_ιOne, map_neg, cons_d_ιOne, cons_d_ιOne_zero, insert_ιZero, h₀]
            simp only [map_smul, value, add_smul]
            module
          | succ n =>
            simp only [LinearMap.add_apply, LinearMap.comp_apply, insert_ιOne,
              map_neg, cons_d_ιOne, insert_ιZero, map_sub, map_add,
              map_smul, LinearMap.lsmul_apply, value]
            have h := congrArg (fun z => singleTensorιOne a (chainComplex s) (n + 1) z)
              (h₁ n y)
            have he := (eq_sub_iff_add_eq).mpr (h₁ n y)
            rw [he]
            simp only [map_sub, map_smul]
            module
      exact LinearMap.congr_fun hlin x

private abbrev Total (s : List R) := ∀ n : ℕ, (chainComplex s).X n

private def totalInsert (s : List R) (v : Fin s.length → R) : Total s →ₗ[R] Total s where
  toFun x | 0 => 0 | n + 1 => insert s v n (x n)
  map_add' x y := by ext n; cases n <;> simp
  map_smul' r x := by ext n; cases n <;> simp

private def insertLinear (s : List R) :
    (Fin s.length → R) →ₗ[R] Module.End R (Total s) where
  toFun := totalInsert s
  map_add' v z := by ext x n; cases n <;> simp [totalInsert, insert_add]
  map_smul' r v := by ext x n; cases n <;> simp [totalInsert, insert_smul]

private def representation (s : List R) :
    ExteriorAlgebra R (Fin s.length → R) →ₐ[R] Module.End R (Total s) :=
  ExteriorAlgebra.lift R ⟨insertLinear s, fun v => by
    ext x n
    cases n with
    | zero => rfl
    | succ n =>
      cases n with
      | zero => simp [insertLinear, totalInsert, Module.End.mul_apply]
      | succ n => exact insert_sq s v n (x n)⟩

private def seed (s : List R) : Total s
  | 0 => (zeroComponentIso s).inv 1
  | _ + 1 => 0

private def ordered (s : List R) : List (Fin s.length → R) → Total s
  | [] => seed s
  | v :: vs => totalInsert s v (ordered s vs)

private theorem ordered_ofFn (s : List R) (n : ℕ) (v : Fin n → (Fin s.length → R)) :
    ordered s (List.ofFn v) = representation s (ExteriorAlgebra.ιMulti R n v) (seed s) := by
  induction n with
  | zero => simp [ordered, ExteriorAlgebra.ιMulti_zero_apply]
  | succ n ih =>
    simp only [List.ofFn_succ, ordered, ExteriorAlgebra.ιMulti_succ_apply,
      map_mul, representation, ExteriorAlgebra.lift_ι_apply]
    exact congrArg (totalInsert s (v 0)) (ih (v ∘ Fin.succ))

private theorem zeroFrame_cons (a : R) (s : List R) :
    singleTensorιZero a (chainComplex s) 0 ≫ (zeroComponentIso (a :: s)).hom =
      (zeroComponentIso s).hom := by
  dsimp only [singleTensorιZero]
  rw [Category.assoc, ιCons_zero_zero_zeroComponentIso]
  rw [← Category.assoc, Iso.inv_hom_id, Category.id_comp]

private def embed (a : R) (s : List R) : Total s →ₗ[R] Total (a :: s) where
  toFun x n := singleTensorιZero a (chainComplex s) n (x n)
  map_add' x y := by ext n; simp
  map_smul' r x := by ext n; simp

private theorem seed_cons (a : R) (s : List R) : seed (a :: s) = embed a s (seed s) := by
  ext n
  cases n with
  | zero =>
    apply (ConcreteCategory.bijective_of_isIso (zeroComponentIso (a :: s)).hom).injective
    have h := ConcreteCategory.congr_hom (zeroFrame_cons a s) ((zeroComponentIso s).inv 1)
    simpa [seed, embed] using h.symm
  | succ n => simp [seed, embed]

private theorem insert_embed (a : R) (s : List R) (v : Fin s.length → R) (x : Total s) :
    totalInsert (a :: s) (Fin.cons 0 v) (embed a s x) =
      embed a s (totalInsert s v x) := by
  ext n
  cases n with
  | zero => simp [totalInsert, embed]
  | succ n =>
    have h := insert_ιZero a s (Fin.cons 0 v) n (x n)
    simpa only [totalInsert, embed, LinearMap.coe_mk, AddHom.coe_mk,
      Fin.cons_zero, Fin.cons_succ, Function.comp_def, zero_smul, map_zero, add_zero] using h

private theorem ordered_embed (a : R) (s : List R) (vs : List (Fin s.length → R)) :
    ordered (a :: s) (vs.map (Fin.cons 0)) = embed a s (ordered s vs) := by
  induction vs with
  | nil => exact seed_cons a s
  | cons v vs ih => simp only [List.map_cons, ordered, ih, insert_embed]

private theorem basis_rows_cons (n : ℕ) :
    List.ofFn (Pi.basisFun R (Fin (n + 1))) =
      Fin.cons 1 (0 : Fin n → R) ::
        (List.ofFn (Pi.basisFun R (Fin n))).map (Fin.cons 0) := by
  rw [List.ofFn_succ, List.map_ofFn]
  congr 1
  · ext j
    cases j using Fin.cases <;> simp [Pi.basisFun_apply]
  · apply congrArg List.ofFn
    funext i j
    cases j using Fin.cases <;> simp [Pi.basisFun_apply, Pi.single_apply, Fin.succ_inj]

private theorem ordered_basis (s : List R) :
    (topComponentIso s).hom
      (ordered s (List.ofFn (Pi.basisFun R (Fin s.length))) s.length) = 1 := by
  induction s with
  | nil => rfl
  | cons a s ih =>
    change (topComponentIso (a :: s)).hom
      (ordered (a :: s) (List.ofFn (Pi.basisFun R (Fin (s.length + 1))))
        (s.length + 1)) = 1
    rw [basis_rows_cons, ordered, ordered_embed]
    change (topComponentIso (a :: s)).hom
      (insert (a :: s) (Fin.cons 1 0) s.length
        (singleTensorιZero a (chainComplex s) s.length
          (ordered s (List.ofFn (Pi.basisFun R (Fin s.length))) s.length))) = 1
    rw [insert_ιZero]
    simp only [Fin.cons_zero, Fin.cons_succ, Function.comp_def, insert_zero,
      LinearMap.zero_apply, map_zero, zero_add, one_smul]
    have h := ConcreteCategory.congr_hom (topComponentIso_cons a s)
      (ordered s (List.ofFn (Pi.basisFun R (Fin s.length))) s.length)
    exact h.trans ih

private def topEvaluation (s : List R) : Module.End R (Total s) →ₗ[R] R where
  toFun F := (topComponentIso s).hom (F (seed s) s.length)
  map_add' F G := by simp
  map_smul' r F := by simp

private def topAlternating (s : List R) :
    (Fin s.length → R) [⋀^Fin s.length]→ₗ[R] R :=
  ((topEvaluation s).comp (representation s).toLinearMap).compAlternatingMap
    (ExteriorAlgebra.ιMulti R s.length)

private theorem ordered_det (s : List R) (M : Matrix (Fin s.length) (Fin s.length) R) :
    (topComponentIso s).hom (ordered s (List.ofFn M) s.length) = M.det := by
  have h := (topAlternating s).eq_smul_basis_det (Pi.basisFun R (Fin s.length))
  have hb : topAlternating s (Pi.basisFun R (Fin s.length)) = 1 := by
    simpa only [topAlternating, LinearMap.compAlternatingMap_apply, LinearMap.comp_apply,
      AlgHom.toLinearMap_apply, topEvaluation, LinearMap.coe_mk, AddHom.coe_mk,
      ← ordered_ofFn] using ordered_basis s
  have hM := congrArg (fun f => f M) h
  rw [hb, one_smul, Pi.basisFun_det] at hM
  simpa only [topAlternating, LinearMap.compAlternatingMap_apply, LinearMap.comp_apply,
    AlgHom.toLinearMap_apply, topEvaluation, LinearMap.coe_mk, AddHom.coe_mk,
    ← ordered_ofFn, Matrix.det] using hM

private def initialComparison (s : List R) : chainComplex ([] : List R) ⟶ chainComplex s where
  f | 0 => (zeroComponentIso []).hom ≫ (zeroComponentIso s).inv | _ + 1 => 0
  comm' i j hij := by
    obtain rfl : j + 1 = i := hij
    exact (isZero_X [] (j + 1) (by simp)).eq_of_src _ _

private def extendComparison (s : List R) (v : Fin s.length → R)
    (K : ChainComplex (ModuleCat.{u} R) ℕ) (F : K ⟶ chainComplex s) :
    HomologicalComplex.tensorObj (singleComplex R (value s v)) K ⟶ chainComplex s where
  f
    | 0 => singleTensorπZero (value s v) K 0 ≫ F.f 0
    | n + 1 =>
        singleTensorπZero (value s v) K (n + 1) ≫ F.f (n + 1) +
          singleTensorπOne (value s v) K n ≫ F.f n ≫ ModuleCat.ofHom (insert s v n)
  comm' i j hij := by
    obtain rfl : j + 1 = i := hij
    apply singleTensor_hom_ext (value s v) K j
    · apply ModuleCat.hom_ext
      ext x
      cases j with
      | zero =>
        change ((chainComplex s).d 1 0)
            (((singleTensorπZero (value s v) K 1 ≫ F.f 1 +
              singleTensorπOne (value s v) K 0 ≫ F.f 0 ≫
                ModuleCat.ofHom (insert s v 0))).hom
                  (singleTensorιZero (value s v) K 1 x)) = _
        simpa only [ModuleCat.hom_add, LinearMap.add_apply, ModuleCat.comp_apply,
          singleTensorπZero_ιZero_apply, singleTensorπOne_ιZero_apply,
          map_zero, add_zero, singleTensor_d_ιZero_apply] using
            ConcreteCategory.congr_hom (F.comm 1 0) x
      | succ j =>
        have hc := ConcreteCategory.congr_hom (F.comm (j + 2) (j + 1)) x
        simpa only [ModuleCat.hom_add, LinearMap.add_apply, ModuleCat.comp_apply,
          singleTensorπZero_ιZero_apply, singleTensorπOne_ιZero_apply,
          map_zero, add_zero, singleTensor_d_ιZero_apply] using hc
    · apply ModuleCat.hom_ext
      ext x
      cases j with
      | zero =>
        change (chainComplex s).d 1 0
            (F.f 1 (singleTensorπZero (value s v) K 1
                (singleTensorιOne (value s v) K 0 x)) +
              insert s v 0 (F.f 0 (singleTensorπOne (value s v) K 0
                (singleTensorιOne (value s v) K 0 x)))) =
          F.f 0 (singleTensorπZero (value s v) K 0
            ((HomologicalComplex.tensorObj (singleComplex R (value s v)) K).d 1 0
              (singleTensorιOne (value s v) K 0 x)))
        rw [singleTensorπZero_ιOne_apply, singleTensorπOne_ιOne_apply,
          map_zero, zero_add, singleTensor_d_ιOne_zero_apply, singleTensorπZero_ιZero_apply]
        simpa only [map_smul] using (insert_homotopy s v).1 (F.f 0 x)
      | succ j =>
        change (chainComplex s).d (j + 2) (j + 1)
            (F.f (j + 2) (singleTensorπZero (value s v) K (j + 2)
                (singleTensorιOne (value s v) K (j + 1) x)) +
              insert s v (j + 1) (F.f (j + 1)
                (singleTensorπOne (value s v) K (j + 1)
                  (singleTensorιOne (value s v) K (j + 1) x)))) =
          F.f (j + 1) (singleTensorπZero (value s v) K (j + 1)
            ((HomologicalComplex.tensorObj (singleComplex R (value s v)) K).d
              (j + 2) (j + 1) (singleTensorιOne (value s v) K (j + 1) x))) +
          insert s v j (F.f j (singleTensorπOne (value s v) K j
            ((HomologicalComplex.tensorObj (singleComplex R (value s v)) K).d
              (j + 2) (j + 1) (singleTensorιOne (value s v) K (j + 1) x))))
        rw [singleTensorπZero_ιOne_apply, singleTensorπOne_ιOne_apply,
          map_zero, zero_add]
        have hZ : singleTensorπZero (value s v) K (j + 1)
            ((HomologicalComplex.tensorObj (singleComplex R (value s v)) K).d
              (j + 2) (j + 1) (singleTensorιOne (value s v) K (j + 1) x)) =
            value s v • x := by
          rw [singleTensor_d_ιOne_apply]
          simp only [map_sub, singleTensorπZero_ιZero_apply,
            singleTensorπZero_ιOne_apply, sub_zero]
        have hO : singleTensorπOne (value s v) K j
            ((HomologicalComplex.tensorObj (singleComplex R (value s v)) K).d
              (j + 2) (j + 1) (singleTensorιOne (value s v) K (j + 1) x)) =
            -K.d (j + 1) j x := by
          rw [singleTensor_d_ιOne_apply]
          simp only [map_sub, singleTensorπOne_ιZero_apply,
            singleTensorπOne_ιOne_apply, zero_sub]
        rw [hZ, hO]
        simp only [map_smul, map_neg]
        have hc := ConcreteCategory.congr_hom (F.comm (j + 1) j) x
        change (chainComplex s).d (j + 1) j (F.f (j + 1) x) = F.f j (K.d (j + 1) j x) at hc
        have h := (eq_sub_iff_add_eq).mpr ((insert_homotopy s v).2 j (F.f (j + 1) x))
        rw [hc] at h
        simpa only [sub_eq_add_neg] using h

private def source (s : List R) (vs : List (Fin s.length → R)) : List R := vs.map (value s)

private def comparison (s : List R) :
    (vs : List (Fin s.length → R)) → chainComplex (source s vs) ⟶ chainComplex s
  | [] => initialComparison s
  | v :: vs => extendComparison s v (chainComplex (source s vs)) (comparison s vs)

private theorem comparison_zero (s : List R) (vs : List (Fin s.length → R)) :
    (comparison s vs).f 0 ≫ (zeroComponentIso s).hom = (zeroComponentIso (source s vs)).hom := by
  induction vs with
  | nil =>
    change ((zeroComponentIso []).hom ≫ (zeroComponentIso s).inv) ≫
      (zeroComponentIso s).hom = (zeroComponentIso []).hom
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  | cons v vs ih =>
    change (singleTensorπZero (value s v) (chainComplex (source s vs)) 0 ≫
      (comparison s vs).f 0) ≫ (zeroComponentIso s).hom =
        (zeroComponentIso (value s v :: source s vs)).hom
    rw [Category.assoc, ih]
    apply singleTensor_hom_ext_zero (value s v) (chainComplex (source s vs))
    rw [singleTensorιZero_πZero_assoc, zeroFrame_cons]

private theorem comparison_top (s : List R) (vs : List (Fin s.length → R)) :
    (comparison s vs).f (source s vs).length
        ((topComponentIso (source s vs)).inv 1) =
      ordered s vs (source s vs).length := by
  induction vs with
  | nil =>
    change (zeroComponentIso s).inv
      ((zeroComponentIso []).hom ((topComponentIso []).inv 1)) = (zeroComponentIso s).inv 1
    rfl
  | cons v vs ih =>
    change ((extendComparison s v (chainComplex (source s vs)) (comparison s vs)).f
      ((source s vs).length + 1))
        (singleTensorιOne (value s v) (chainComplex (source s vs)) (source s vs).length
          ((topComponentIso (source s vs)).inv 1)) = _
    simp only [extendComparison, ModuleCat.hom_add, LinearMap.add_apply, ModuleCat.comp_apply,
      singleTensorπZero_ιOne_apply, singleTensorπOne_ιOne_apply, map_zero, zero_add]
    change insert s v (source s vs).length
      ((comparison s vs).f (source s vs).length ((topComponentIso (source s vs)).inv 1)) =
      insert s v (source s vs).length (ordered s vs (source s vs).length)
    exact congrArg (insert s v (source s vs).length) ih

private theorem evaluation_XIso (s : List R) (x : Total s) {n m : ℕ} (h : n = m) :
    ((chainComplex s).XIsoOfEq h).hom (x n) = x m := by
  subst m
  rfl

private def frame (s : List R) (n : ℕ) (h : n = s.length) :
    (chainComplex s).X n ≅ ModuleCat.of R R :=
  (chainComplex s).XIsoOfEq h ≪≫ topComponentIso s

private theorem comparison_determinant (s : List R)
    (M : Matrix (Fin s.length) (Fin s.length) R) :
    let t := source s (List.ofFn M)
    let h : t.length = s.length := by simp [t, source]
    (comparison s (List.ofFn M)).f t.length ≫ (frame s t.length h).hom =
      (topComponentIso t).hom ≫ ModuleCat.ofHom (LinearMap.lsmul R R M.det) := by
  intro t h
  apply (cancel_epi (topComponentIso t).inv).mp
  apply ModuleCat.hom_ext
  apply LinearMap.ext_ring
  change (frame s t.length h).hom
      ((comparison s (List.ofFn M)).f t.length ((topComponentIso t).inv 1)) = _
  rw [comparison_top]
  change (topComponentIso s).hom
      (((chainComplex s).XIsoOfEq h).hom (ordered s (List.ofFn M) t.length)) = _
  rw [evaluation_XIso, ordered_det]
  simp

private theorem augmentation_zero (s : List R) (x : (chainComplex s).X 0) :
    (idealAugmentation s).f 0 x =
      Ideal.Quotient.mk (Ideal.ofList s) ((zeroComponentIso s).hom x) := by
  simp only [idealAugmentation, HomologicalComplex.comp_f, augmentation_f_zero,
    ChainComplex.single₀_map_f_zero, ModuleCat.comp_apply]
  rfl

private theorem extClass_cast [HasExt.{w} (ModuleCat.{u} R)]
    (s : List R) (hs : RingTheory.Sequence.IsWeaklyRegular R s)
    (n : ℕ) (h : s.length = n) (r : R) :
    cast (congrArg (fun k => Ext.{w} (ModuleCat.of R (R ⧸ Ideal.ofList s))
      (ModuleCat.of R R) k) h) (topExtClass s hs (ModuleCat.of R R) r) =
    (finiteProjectiveResolution s hs).extMk
      ((frame s n h.symm).hom ≫ ModuleCat.ofHom (LinearMap.toSpanSingleton R R r))
      (n + 1) rfl ((isZero_X s (n + 1) (by omega)).eq_of_src _ _) := by
  subst n
  rfl

private theorem ext_covariance [HasExt.{w} (ModuleCat.{u} R)]
    (s t : List R) (hs : RingTheory.Sequence.IsWeaklyRegular R s)
    (ht : RingTheory.Sequence.IsWeaklyRegular R t) (hlen : s.length = t.length)
    (hI : Ideal.ofList t ≤ Ideal.ofList s) (F : chainComplex t ⟶ chainComplex s)
    (h₀ : F.f 0 ≫ (zeroComponentIso s).hom = (zeroComponentIso t).hom)
    (d : R) (hTop : F.f t.length ≫ (frame s t.length hlen.symm).hom =
      (topComponentIso t).hom ≫ ModuleCat.ofHom (LinearMap.lsmul R R d)) (r : R) :
    let q : ModuleCat.of R (R ⧸ Ideal.ofList t) ⟶ ModuleCat.of R (R ⧸ Ideal.ofList s) :=
      ModuleCat.ofHom ((Ideal.ofList t).mapQ (Ideal.ofList s) LinearMap.id hI)
    (Ext.mk₀ q).comp
      (cast (congrArg (fun k => Ext.{w} (ModuleCat.of R (R ⧸ Ideal.ofList s))
        (ModuleCat.of R R) k) hlen) (topExtClass s hs (ModuleCat.of R R) r))
      (zero_add t.length) = topExtClass t ht (ModuleCat.of R R) (d * r) := by
  intro q
  let Φ : ProjectiveResolution.Hom (finiteProjectiveResolution t ht)
      (finiteProjectiveResolution s hs) q :=
    { hom := F
      hom_f_zero_comp_π_f_zero := by
        apply ModuleCat.hom_ext
        ext x
        change (idealAugmentation s).f 0 (F.f 0 x) = q ((idealAugmentation t).f 0 x)
        rw [augmentation_zero, augmentation_zero]
        change Ideal.Quotient.mk (Ideal.ofList s) ((zeroComponentIso s).hom (F.f 0 x)) =
          Ideal.Quotient.mk (Ideal.ofList s) ((zeroComponentIso t).hom x)
        have h := ConcreteCategory.congr_hom h₀ x
        exact congrArg (Ideal.Quotient.mk (Ideal.ofList s)) h }
  rw [extClass_cast s hs t.length hlen r,
    ProjectiveResolution.mk₀_comp_extMk (φ := Φ)]
  rw [topExtClass_apply]
  congr 1
  rw [← Category.assoc, hTop, Category.assoc]
  congr 1
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change (d * x) * r = x * (d * r)
  ring

end GeneratorChange

/-- Ordered change of weakly regular generators acts on the original top Koszul
Ext class by the determinant. The quotient map is the original map induced by
the common ideal. The matrix need not be invertible over the ring. -/
theorem topExtClass_generatorChange
    {R : Type u} [CommRing R] [HasExt.{w} (ModuleCat.{u} R)]
    (s t : List R) (hs : RingTheory.Sequence.IsWeaklyRegular R s)
    (ht : RingTheory.Sequence.IsWeaklyRegular R t)
    (M : Matrix (Fin s.length) (Fin s.length) R)
    (hM : t = List.ofFn (fun i => ∑ j, M i j * s.get j))
    (hI : Ideal.ofList t = Ideal.ofList s) (r : R) :
    let hlen : s.length = t.length := by rw [hM, List.length_ofFn]
    let q : ModuleCat.of R (R ⧸ Ideal.ofList t) ⟶ ModuleCat.of R (R ⧸ Ideal.ofList s) :=
      ModuleCat.ofHom ((Ideal.ofList t).mapQ (Ideal.ofList s) LinearMap.id hI.le)
    (Ext.mk₀ q).comp
      (cast (congrArg (fun k => Ext.{w} (ModuleCat.of R (R ⧸ Ideal.ofList s))
        (ModuleCat.of R R) k) hlen) (topExtClass s hs (ModuleCat.of R R) r))
      (zero_add t.length) = topExtClass t ht (ModuleCat.of R R) (M.det * r) := by
  have he : t = GeneratorChange.source s (List.ofFn M) := by
    rw [hM]
    simp only [GeneratorChange.source, List.map_ofFn]
    congr 1
    funext i
    exact (GeneratorChange.value_eq_sum s (M i)).symm
  cases he
  exact GeneratorChange.ext_covariance s (GeneratorChange.source s (List.ofFn M)) hs ht
    (by simp [GeneratorChange.source]) hI.le (GeneratorChange.comparison s (List.ofFn M))
    (GeneratorChange.comparison_zero s (List.ofFn M)) M.det
    (GeneratorChange.comparison_determinant s M) r

end ChainComplex.Koszul
