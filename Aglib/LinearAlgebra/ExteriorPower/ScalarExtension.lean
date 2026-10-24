/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.LinearAlgebra.ExteriorPower.Semilinear
public import Mathlib.LinearAlgebra.ExteriorAlgebra.Grading
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.Localization.BaseChange

/-!
# Exterior powers under actual scalar extension

The exterior tensor map is constructed directly from square-zero generators
and cancellation of mixed terms. The native homogeneous pieces give the tensor
equivalence and actual localization maps without inverting two.
-/

@[expose] public noncomputable section

open scoped TensorProduct

namespace ExteriorAlgebra

variable {R S M : Type*} [CommRing R] [CommRing S] [Algebra R S]
  [AddCommGroup M] [Module R M]

/-- Tensor the original exterior generator map. -/
def tensorGenerator : S ⊗[R] M →ₗ[S] S ⊗[R] ExteriorAlgebra R M :=
  TensorProduct.AlgebraTensorModule.map (LinearMap.id (R := S) (M := S)) (ι R)

@[simp]
theorem tensorGenerator_tmul (s : S) (m : M) :
    tensorGenerator (R := R) (S := S) (s ⊗ₜ[R] m) = s ⊗ₜ[R] ι R m := by
  rw [tensorGenerator, TensorProduct.AlgebraTensorModule.map_tmul, LinearMap.id_apply]

/-- Mixed terms cancel before any use of a square-zero identity; characteristic two is allowed. -/
theorem tensorGenerator_add_mul_swap (v w : S ⊗[R] M) :
    tensorGenerator v * tensorGenerator w + tensorGenerator w * tensorGenerator v = 0 := by
  induction v using TensorProduct.inductionOn with
  | tmul s m =>
    induction w using TensorProduct.inductionOn with
    | tmul t m' =>
      rw [tensorGenerator_tmul, tensorGenerator_tmul,
        Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul,
        mul_comm t s, ← TensorProduct.tmul_add, ι_add_mul_swap, TensorProduct.tmul_zero]
    | add w w' hw hw' =>
      calc
        _ = (tensorGenerator (s ⊗ₜ[R] m) * tensorGenerator w +
              tensorGenerator w * tensorGenerator (s ⊗ₜ[R] m)) +
            (tensorGenerator (s ⊗ₜ[R] m) * tensorGenerator w' +
              tensorGenerator w' * tensorGenerator (s ⊗ₜ[R] m)) := by
          rw [map_add, mul_add, add_mul]
          abel
        _ = 0 := by rw [hw, hw', add_zero]
  | add v v' hv hv' =>
    calc
      _ = (tensorGenerator v * tensorGenerator w + tensorGenerator w * tensorGenerator v) +
          (tensorGenerator v' * tensorGenerator w + tensorGenerator w * tensorGenerator v') := by
        rw [map_add, add_mul, mul_add]
        abel
      _ = 0 := by rw [hv, hv', add_zero]

/-- The tensored generator squares to zero without an invertibility hypothesis on two. -/
theorem tensorGenerator_sq_zero (v : S ⊗[R] M) : tensorGenerator v * tensorGenerator v = 0 := by
  induction v using TensorProduct.inductionOn with
  | tmul s m =>
    rw [tensorGenerator_tmul, Algebra.TensorProduct.tmul_mul_tmul, ι_sq_zero,
      TensorProduct.tmul_zero]
  | add v w hv hw =>
    calc
      _ = (tensorGenerator v * tensorGenerator v + tensorGenerator w * tensorGenerator w) +
          (tensorGenerator v * tensorGenerator w + tensorGenerator w * tensorGenerator v) := by
        rw [map_add, mul_add, add_mul, add_mul]
        abel
      _ = 0 := by rw [hv, hw, tensorGenerator_add_mul_swap, add_zero, zero_add]

/-- The actual exterior-algebra tensor map, constructed directly so that characteristic two
is retained. No Clifford base-change theorem with invertible two is imported. -/
def tensorMap : ExteriorAlgebra S (S ⊗[R] M) →ₐ[S] S ⊗[R] ExteriorAlgebra R M :=
  ExteriorAlgebra.lift S ⟨tensorGenerator, tensorGenerator_sq_zero⟩

@[simp]
theorem tensorMap_ι (v : S ⊗[R] M) :
    tensorMap (ι S v) = tensorGenerator v :=
  ExteriorAlgebra.lift_ι_apply _ _ _ _

theorem tensorMap_ι_tmul (s : S) (m : M) :
    tensorMap (ι S (s ⊗ₜ[R] m)) = s ⊗ₜ[R] ι R m := by
  rw [tensorMap_ι, tensorGenerator_tmul]

/-- Original pure-vector wedges keep their tensor and order. -/
theorem tensorMap_ιMulti_one (n : ℕ) (v : Fin n → M) :
    tensorMap (ιMulti S n (fun i => 1 ⊗ₜ[R] v i)) = 1 ⊗ₜ[R] ιMulti R n v := by
  induction n with
  | zero => rw [ιMulti_zero_apply, map_one, ιMulti_zero_apply, Algebra.TensorProduct.one_def]
  | succ n ih =>
    rw [ιMulti_succ_apply, map_mul, tensorMap_ι_tmul]
    change (1 ⊗ₜ[R] ι R (v 0)) *
      tensorMap (ιMulti S n (fun i => 1 ⊗ₜ[R] Matrix.vecTail v i)) = _
    rw [ih, Algebra.TensorProduct.tmul_mul_tmul, one_mul, ← ιMulti_succ_apply]

/-- The native homogeneous component obtained from the actual grading map. -/
def degreeComponent (n : ℕ) : ExteriorAlgebra R M →ₗ[R] (⋀[R]^n M) :=
  (DirectSum.component R ℕ (fun i => ⋀[R]^i M) n).comp
    (ExteriorAlgebra.GradedAlgebra.liftι R M).toLinearMap

@[simp]
theorem degreeComponent_coe (n : ℕ) (v : ⋀[R]^n M) :
    degreeComponent n (v : ExteriorAlgebra R M) = v := by
  change DirectSum.component R ℕ (fun i => ⋀[R]^i M) n
    (ExteriorAlgebra.GradedAlgebra.liftι R M (v : ExteriorAlgebra R M)) = v
  rw [ExteriorAlgebra.GradedAlgebra.liftι_eq]
  simpa only [DirectSum.lof_eq_of] using
    DirectSum.component.lof_self (M := fun i : ℕ => ↥(⋀[R]^i M)) R n v

@[simp]
theorem degreeComponent_ιMulti (n : ℕ) (v : Fin n → M) :
    degreeComponent n (ιMulti R n v) = exteriorPower.ιMulti R n v := by
  change degreeComponent n ((exteriorPower.ιMulti R n v : ⋀[R]^n M) :
    ExteriorAlgebra R M) = _
  exact degreeComponent_coe n _

end ExteriorAlgebra

namespace LinearMap

variable {R S M N : Type*} [CommRing R] [CommRing S] [Algebra R S]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] [Module S N]
  [IsScalarTower R S N]

/-- Restrict an algebra-map-semilinear map using the original scalar tower.
The underlying function is unchanged. -/
def ofAlgebraSemilinear (f : M →ₛₗ[algebraMap R S] N) : M →ₗ[R] N where
  toFun := f
  map_add' := f.map_add
  map_smul' r x := (f.map_smulₛₗ r x).trans (IsScalarTower.algebraMap_smul S r (f x))

@[simp]
theorem ofAlgebraSemilinear_apply (f : M →ₛₗ[algebraMap R S] N) (x : M) :
    ofAlgebraSemilinear f x = f x := rfl

end LinearMap

namespace exteriorPower

variable {R S M N : Type*} [CommRing R] [CommRing S] [Algebra R S]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] [Module S N]
  [IsScalarTower R S N]

/-- Regard the original R-linear map into an S-module as the corresponding semilinear map. -/
def algebraSemilinear (f : M →ₗ[R] N) : M →ₛₗ[algebraMap R S] N where
  toFun := f
  map_add' := f.map_add
  map_smul' r x := (f.map_smul r x).trans (IsScalarTower.algebraMap_smul S r (f x)).symm

@[simp]
theorem algebraSemilinear_apply (f : M →ₗ[R] N) (x : M) :
    algebraSemilinear (S := S) f x = f x := rfl

/-- The existing semilinear exterior construction, with its actual restricted R-scalars. -/
def mapAlgebra (n : ℕ) (f : M →ₗ[R] N) : (⋀[R]^n M) →ₗ[R] (⋀[S]^n N) :=
  LinearMap.ofAlgebraSemilinear
    (mapSemilinear n (algebraSemilinear (S := S) f))

/-- The actual exterior map retains the native semilinear map on every element. -/
theorem mapAlgebra_apply (n : ℕ) (f : M →ₗ[R] N) (x : ⋀[R]^n M) :
    mapAlgebra (S := S) n f x = mapSemilinear n (algebraSemilinear (S := S) f) x :=
  LinearMap.ofAlgebraSemilinear_apply (mapSemilinear n (algebraSemilinear (S := S) f)) x

@[simp]
theorem mapAlgebra_ιMulti (n : ℕ) (f : M →ₗ[R] N) (v : Fin n → M) :
    mapAlgebra (S := S) n f (ιMulti R n v) = ιMulti S n (f ∘ v) := by
  calc
    mapAlgebra (S := S) n f (ιMulti R n v) =
        mapSemilinear n (algebraSemilinear (S := S) f) (ιMulti R n v) :=
      mapAlgebra_apply n f (ιMulti R n v)
    _ = ιMulti S n (algebraSemilinear (S := S) f ∘ v) :=
      mapSemilinear_apply_ιMulti n (algebraSemilinear (S := S) f) v
    _ = ιMulti S n (f ∘ v) := by
      apply congrArg (ιMulti S n)
      funext i
      exact algebraSemilinear_apply (S := S) f (v i)

section BaseChange

variable (S M)

/-- The actual degree-n part of the directly constructed exterior tensor map. -/
def tensorBaseChangeForward (n : ℕ) :
    (⋀[S]^n (S ⊗[R] M)) →ₗ[S] S ⊗[R] (⋀[R]^n M) :=
  (TensorProduct.AlgebraTensorModule.map (LinearMap.id (R := S) (M := S))
    (ExteriorAlgebra.degreeComponent n)).comp
      (ExteriorAlgebra.tensorMap.toLinearMap.comp (⋀[S]^n (S ⊗[R] M)).subtype)

/-- The inverse is induced by the original vector map `m ↦ 1 ⊗ m`. -/
def tensorBaseChangeBackward (n : ℕ) :
    S ⊗[R] (⋀[R]^n M) →ₗ[S] (⋀[S]^n (S ⊗[R] M)) :=
  (mapAlgebra (S := S) n (TensorProduct.mk R S M 1)).liftBaseChange S

theorem tensorBaseChangeForward_ιMulti (n : ℕ) (v : Fin n → M) :
    tensorBaseChangeForward (R := R) S M n
      (ιMulti S n (fun i => 1 ⊗ₜ[R] v i)) = 1 ⊗ₜ[R] ιMulti R n v := by
  change TensorProduct.AlgebraTensorModule.map (LinearMap.id (R := S) (M := S))
    (ExteriorAlgebra.degreeComponent n)
      (ExteriorAlgebra.tensorMap
        (ExteriorAlgebra.ιMulti S n (fun i => 1 ⊗ₜ[R] v i))) = _
  rw [ExteriorAlgebra.tensorMap_ιMulti_one, TensorProduct.AlgebraTensorModule.map_tmul,
    LinearMap.id_apply, ExteriorAlgebra.degreeComponent_ιMulti]

@[simp]
theorem tensorBaseChangeBackward_tmul (n : ℕ) (s : S) (v : ⋀[R]^n M) :
    tensorBaseChangeBackward (R := R) S M n (s ⊗ₜ[R] v) =
      s • mapAlgebra (S := S) n (TensorProduct.mk R S M 1) v :=
  LinearMap.liftBaseChange_tmul _ _ _ _

theorem tensorBaseChangeForward_mapAlgebra (n : ℕ) (v : ⋀[R]^n M) :
    tensorBaseChangeForward (R := R) S M n
      (mapAlgebra (S := S) n (TensorProduct.mk R S M 1) v) = 1 ⊗ₜ[R] v := by
  have he : ((tensorBaseChangeForward (R := R) S M n).restrictScalars R).comp
      (mapAlgebra (S := S) n (TensorProduct.mk R S M 1)) =
        TensorProduct.mk R S (⋀[R]^n M) 1 := by
    apply exteriorPower.linearMap_ext
    apply AlternatingMap.ext
    intro v
    change tensorBaseChangeForward (R := R) S M n
      (mapAlgebra (S := S) n (TensorProduct.mk R S M 1) (ιMulti R n v)) =
        1 ⊗ₜ[R] ιMulti R n v
    rw [mapAlgebra_ιMulti]
    exact tensorBaseChangeForward_ιMulti S M n v
  exact LinearMap.congr_fun he v

theorem tensorBaseChangeForward_backward (n : ℕ) (v : S ⊗[R] (⋀[R]^n M)) :
    tensorBaseChangeForward (R := R) S M n
      (tensorBaseChangeBackward (R := R) S M n v) = v := by
  induction v using TensorProduct.inductionOn with
  | tmul s v =>
    rw [tensorBaseChangeBackward_tmul, map_smul, tensorBaseChangeForward_mapAlgebra,
      TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  | add v w hv hw => simp only [map_add, hv, hw]

theorem span_one_tmul_eq_top :
    Submodule.span S (Set.range (fun m : M => (1 : S) ⊗ₜ[R] m)) = ⊤ := by
  apply Submodule.eq_top_iff'.mpr
  intro v
  induction v using TensorProduct.inductionOn with
  | tmul s m =>
    have hm : (1 : S) ⊗ₜ[R] m ∈
        Submodule.span S (Set.range (fun m : M => (1 : S) ⊗ₜ[R] m)) :=
      Submodule.subset_span ⟨m, rfl⟩
    simpa only [TensorProduct.smul_tmul', smul_eq_mul, mul_one] using
      Submodule.smul_mem _ s hm
  | add v w hv hw => exact Submodule.add_mem _ hv hw

theorem tensorBaseChangeBackward_forward (n : ℕ) (v : ⋀[S]^n (S ⊗[R] M)) :
    tensorBaseChangeBackward (R := R) S M n
      (tensorBaseChangeForward (R := R) S M n v) = v := by
  classical
  have hspan := exteriorPower.ιMulti_span_of_span S n (S ⊗[R] M)
    (span_one_tmul_eq_top (R := R) S M)
  have hv : v ∈ Submodule.span S
      (ιMulti S n '' {w : Fin n → S ⊗[R] M |
        Set.range w ⊆ Set.range (fun m : M => (1 : S) ⊗ₜ[R] m)}) := by
    rw [hspan]
    trivial
  induction hv using Submodule.span_induction with
  | mem v hv =>
    obtain ⟨w, hw, rfl⟩ := hv
    choose m hm using fun i => hw (Set.mem_range_self i)
    have he : w = fun i => 1 ⊗ₜ[R] m i := funext fun i => (hm i).symm
    rw [he, tensorBaseChangeForward_ιMulti, tensorBaseChangeBackward_tmul,
      one_smul, mapAlgebra_ιMulti]
    rfl
  | zero => simp
  | add v w _ _ hv hw => simp only [map_add, hv, hw]
  | smul s v _ hv => simp only [map_smul, hv]

/-- Native exterior powers commute with arbitrary scalar extension, including characteristic two. -/
def tensorBaseChangeEquiv (n : ℕ) :
    (⋀[S]^n (S ⊗[R] M)) ≃ₗ[S] S ⊗[R] (⋀[R]^n M) where
  __ := tensorBaseChangeForward (R := R) S M n
  invFun := tensorBaseChangeBackward (R := R) S M n
  left_inv v := by
    change tensorBaseChangeBackward (R := R) S M n
      (tensorBaseChangeForward (R := R) S M n v) = v
    exact tensorBaseChangeBackward_forward S M n v
  right_inv v := by
    change tensorBaseChangeForward (R := R) S M n
      (tensorBaseChangeBackward (R := R) S M n v) = v
    exact tensorBaseChangeForward_backward S M n v

end BaseChange

section Congr

variable {A X Y : Type*} [CommRing A] [AddCommGroup X] [Module A X]
  [AddCommGroup Y] [Module A Y]

/-- The native exterior maps of a linear equivalence and its inverse are inverse. -/
def congrLinearEquiv (n : ℕ) (e : X ≃ₗ[A] Y) : (⋀[A]^n X) ≃ₗ[A] (⋀[A]^n Y) where
  toLinearMap := exteriorPower.map n e.toLinearMap
  invFun := exteriorPower.map n e.symm.toLinearMap
  left_inv x := by
    have he : (exteriorPower.map n e.symm.toLinearMap).comp
        (exteriorPower.map n e.toLinearMap) = LinearMap.id := by
      apply exteriorPower.linearMap_ext
      apply AlternatingMap.ext
      intro v
      change exteriorPower.map n e.symm.toLinearMap
        (exteriorPower.map n e.toLinearMap (ιMulti A n v)) = ιMulti A n v
      rw [exteriorPower.map_apply_ιMulti, exteriorPower.map_apply_ιMulti]
      congr 1
      funext i
      exact e.symm_apply_apply (v i)
    exact LinearMap.congr_fun he x
  right_inv y := by
    have he : (exteriorPower.map n e.toLinearMap).comp
        (exteriorPower.map n e.symm.toLinearMap) = LinearMap.id := by
      apply exteriorPower.linearMap_ext
      apply AlternatingMap.ext
      intro v
      change exteriorPower.map n e.toLinearMap
        (exteriorPower.map n e.symm.toLinearMap (ιMulti A n v)) = ιMulti A n v
      rw [exteriorPower.map_apply_ιMulti, exteriorPower.map_apply_ιMulti]
      congr 1
      funext i
      exact e.apply_symm_apply (v i)
    exact LinearMap.congr_fun he y

@[simp]
theorem congrLinearEquiv_ιMulti (n : ℕ) (e : X ≃ₗ[A] Y) (v : Fin n → X) :
    congrLinearEquiv n e (ιMulti A n v) = ιMulti A n (e ∘ v) := by
  change exteriorPower.map n e.toLinearMap (ιMulti A n v) = _
  exact exteriorPower.map_apply_ιMulti e.toLinearMap v

end Congr

/-- Exterior scalar change is proved from the actual tensor equivalence and pure-wedge formula. -/
theorem isBaseChange_mapAlgebra (n : ℕ) (f : M →ₗ[R] N) (hf : IsBaseChange S f) :
    IsBaseChange S (mapAlgebra (S := S) n f) := by
  let e : S ⊗[R] (⋀[R]^n M) ≃ₗ[S] (⋀[S]^n N) :=
    (tensorBaseChangeEquiv (R := R) S M n).symm.trans (congrLinearEquiv n hf.equiv)
  apply IsBaseChange.of_equiv e
  intro x
  have he : (e.toLinearMap.restrictScalars R).comp
      (TensorProduct.mk R S (⋀[R]^n M) 1) = mapAlgebra (S := S) n f := by
    apply exteriorPower.linearMap_ext
    apply AlternatingMap.ext
    intro v
    change congrLinearEquiv n hf.equiv
      (tensorBaseChangeBackward (R := R) S M n (1 ⊗ₜ[R] ιMulti R n v)) =
        mapAlgebra (S := S) n f (ιMulti R n v)
    rw [tensorBaseChangeBackward_tmul, one_smul, mapAlgebra_ιMulti,
      congrLinearEquiv_ιMulti, mapAlgebra_ιMulti]
    congr 1
    funext i
    exact (hf.equiv_tmul 1 (v i)).trans (one_smul _ _)
  exact LinearMap.congr_fun he x

/-- The actual exterior map of a module localization is again that module's localization. -/
theorem isLocalizedModule_mapAlgebra (U : Submonoid R) [IsLocalization U S]
    (n : ℕ) (f : M →ₗ[R] N) [IsLocalizedModule U f] :
    IsLocalizedModule U (mapAlgebra (S := S) n f) :=
  (isLocalizedModule_iff_isBaseChange U S _).mpr
    (isBaseChange_mapAlgebra n f (IsLocalizedModule.isBaseChange U S f))

end exteriorPower

namespace exteriorPower

variable {R S M N : Type*} [CommRing R] [CommRing S] [Algebra R S]
  [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M]
  [AddCommGroup N] [Module R N]

/-- Restricted-linear maps on an S-exterior power are determined on S-multiples
of wedges from a spanning set. No S-action on the target is assumed. -/
theorem restrictLinearMap_ext_of_span (n : ℕ) (s : Set M)
    (hs : Submodule.span S s = ⊤)
    (f g : (⋀[S]^n M) →ₗ[R] N)
    (h : ∀ (v : Fin n → M), Set.range v ⊆ s →
      ∀ c : S, f (c • ιMulti S n v) = g (c • ιMulti S n v)) : f = g := by
  have hspan := exteriorPower.ιMulti_span_of_span S n M hs
  apply LinearMap.ext
  intro x
  have hx : x ∈ Submodule.span S (ιMulti S n '' {v : Fin n → M | Set.range v ⊆ s}) := by
    rw [hspan]
    trivial
  have he : ∀ c : S, f (c • x) = g (c • x) := by
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨v, hv, rfl⟩ := hx
      exact h v hv
    | zero => intro c; rw [smul_zero, map_zero, map_zero]
    | add x y _ _ hx hy =>
      intro c
      rw [smul_add, map_add, map_add, hx c, hy c]
    | smul t x _ hx =>
      intro c
      simpa only [smul_smul] using hx (c * t)
  simpa only [one_smul] using he 1

end exteriorPower
