/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.AdicCompletion.BoundedTorsion
public import Aglib.RingTheory.Descent.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Pi
public import Mathlib.RingTheory.Flat.Equalizer
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
public import Mathlib.RingTheory.Ideal.Quotient.Defs
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.RingTheory.Noetherian.Basic

/-!
# Bounded torsion and regular-conductor algebra effectivity

Let `R → S` be an algebra map and `J` an ideal of the source `R`. Assume that
`R → S / JS` is surjective. An `S`-module annihilated by `JS` is unchanged by
the actual scalar-extension counit `S ⊗[R] M → M`; its inverse is `m ↦ 1 ⊗ m`.
Finite generation descends using the same module and generating elements.
For an algebra the comparison retains the original unit and multiplication.

An `S`-submodule of `S ⊗[R] M` containing `JS` times that ambient module is
the scalar-extension image of its inverse image under the original unit.
Flatness makes the canonical comparison an equivalence. A finite ambient
module over a Noetherian source ring makes the constructed submodule finite.

The finite cross-relation matrix supplies a concrete conductor ambient.
Its coordinate square and flat tensor comparison retain the original
coefficients. Actual conductor multiplication gives a map into this kernel.
The actual fraction map identifies its original-unit preimage with the
localization-intersection subalgebra. This proves finiteness over a
Noetherian source and bijectivity of the original tensor algebra map in
the regular-conductor case.
Its original punctured-localization comparisons are constructed from the
same conductor products. The actual torsion quotient and compatible
quotient-pair algebra belong to the separate `FiniteModification.Torsion`
module. General torsion algebra effectivity remains separate.

These are ingredients of Stacks 05E5, Lemmas 15.91.2, 15.91.3 and 15.91.17
(0ALK). General finite-modification algebra effectivity is not asserted.
The torsion comparison and submodule image equality need no flatness,
Noetherianity or finite-generation condition on `J`.
-/

@[expose] public noncomputable section

open TensorProduct

namespace Algebra.Descent.FormalGluing

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]

/-- Surjectivity onto the extended-ideal quotient gives an original scalar
with an error in that extended ideal. The ideal belongs to the source ring. -/
theorem exists_sub_mem_extendedIdeal (J : Ideal R)
    (hcoeff : Function.Surjective
      ((Ideal.Quotient.mk (J.map (algebraMap R S))).comp (algebraMap R S))) (s : S) :
    ∃ r : R, s - algebraMap R S r ∈ J.map (algebraMap R S) := by
  obtain ⟨r, hr⟩ := hcoeff (Ideal.Quotient.mk (J.map (algebraMap R S)) s)
  refine ⟨r, Ideal.Quotient.eq.mp ?_⟩
  exact hr.symm

/-- An actual quotient comparison supplies the coefficient-surjectivity
hypothesis through its stated equation on original elements. -/
theorem quotient_coefficients_surjective (J : Ideal R)
    (e : R ⧸ J ≃+* S ⧸ J.map (algebraMap R S))
    (he : ∀ r : R, e (Ideal.Quotient.mk J r) =
      Ideal.Quotient.mk (J.map (algebraMap R S)) (algebraMap R S r)) :
    Function.Surjective
      ((Ideal.Quotient.mk (J.map (algebraMap R S))).comp (algebraMap R S)) := by
  intro x
  obtain ⟨y, rfl⟩ := e.surjective x
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective y
  exact ⟨r, (he r).symm⟩

section Modules

variable {M : Type*} [AddCommGroup M] [Module R M] [Module S M]
  [IsScalarTower R S M]

/-- The original scalar-action counit on the tensor product of modules. -/
def scalarTensorMap : S ⊗[R] M →ₗ[S] M :=
  AlgebraTensorModule.lift
    { toFun := fun s =>
        { toFun := fun m => s • m
          map_add' := smul_add s
          map_smul' := fun r m => smul_comm s r m }
      map_add' := fun s t => by
        ext m
        exact add_smul s t m
      map_smul' := fun s t => by
        ext m
        exact mul_smul s t m }

@[simp]
theorem scalarTensorMap_tmul (s : S) (m : M) :
    scalarTensorMap (R := R) (s ⊗ₜ[R] m) = s • m := rfl

/-- A scalar error in `JS` acts trivially on a module annihilated by `JS`. -/
theorem smul_eq_of_sub_mem_extendedIdeal (J : Ideal R)
    (hM : J.map (algebraMap R S) • (⊤ : Submodule S M) = ⊥)
    {s : S} {r : R} (h : s - algebraMap R S r ∈ J.map (algebraMap R S))
    (m : M) : s • m = r • m := by
  have hz := Submodule.smul_mem_smul h (Submodule.mem_top : m ∈ (⊤ : Submodule S M))
  rw [hM] at hz
  have hzero : (s - algebraMap R S r) • m = 0 := hz
  rw [sub_smul, sub_eq_zero] at hzero
  simpa only [algebraMap_smul] using hzero

/-- Every extended scalar acts as one original scalar on the entire
annihilated module. The representing scalar is independent of its element. -/
theorem scalar_action_lifts (J : Ideal R)
    (hcoeff : Function.Surjective
      ((Ideal.Quotient.mk (J.map (algebraMap R S))).comp (algebraMap R S)))
    (hM : J.map (algebraMap R S) • (⊤ : Submodule S M) = ⊥) (s : S) :
    ∃ r : R, ∀ m : M, s • m = r • m := by
  obtain ⟨r, hr⟩ := exists_sub_mem_extendedIdeal J hcoeff s
  exact ⟨r, smul_eq_of_sub_mem_extendedIdeal J hM hr⟩

/-- Finite generation descends on the original module through its actual
scalar actions; no replacement module or chosen descent datum is assumed. -/
theorem finite_restrictScalars (J : Ideal R)
    (hcoeff : Function.Surjective
      ((Ideal.Quotient.mk (J.map (algebraMap R S))).comp (algebraMap R S)))
    (hM : J.map (algebraMap R S) • (⊤ : Submodule S M) = ⊥)
    [Module.Finite S M] : Module.Finite R M :=
  Module.Finite.of_scalar_actions_lift (scalar_action_lifts J hcoeff hM)

/-- An element of `JS` tensors to zero because its source-ideal factor can
move across the tensor product and annihilate the original module element. -/
theorem tmul_eq_zero_of_mem_extendedIdeal (J : Ideal R)
    (hM : J.map (algebraMap R S) • (⊤ : Submodule S M) = ⊥)
    {s : S} (hs : s ∈ J.map (algebraMap R S)) (m : M) : s ⊗ₜ[R] m = 0 := by
  have hs' : s ∈ J • (⊤ : Submodule R S) := by
    rw [Ideal.smul_top_eq_map]
    exact hs
  refine Submodule.smul_induction_on hs' (fun r hr t _ => ?_)
    (fun x y hx hy => by rw [TensorProduct.add_tmul, hx, hy, add_zero])
  have hz := Submodule.smul_mem_smul (Ideal.mem_map_of_mem (algebraMap R S) hr)
    (Submodule.mem_top : m ∈ (⊤ : Submodule S M))
  rw [hM] at hz
  have hrm : r • m = 0 := by
    simpa only [algebraMap_smul] using
      (show algebraMap R S r • m = 0 from hz)
  rw [TensorProduct.smul_tmul, hrm, TensorProduct.tmul_zero]

/-- The inverse counit identity on a pure tensor, retaining its original
scalar and module element. -/
theorem tmul_eq_one_tmul_smul (J : Ideal R)
    (hcoeff : Function.Surjective
      ((Ideal.Quotient.mk (J.map (algebraMap R S))).comp (algebraMap R S)))
    (hM : J.map (algebraMap R S) • (⊤ : Submodule S M) = ⊥) (s : S) (m : M) :
    s ⊗ₜ[R] m = (1 : S) ⊗ₜ[R] (s • m) := by
  obtain ⟨r, hr⟩ := exists_sub_mem_extendedIdeal J hcoeff s
  have hz := tmul_eq_zero_of_mem_extendedIdeal J hM hr m
  rw [TensorProduct.sub_tmul, sub_eq_zero] at hz
  rw [hz, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul,
    smul_eq_of_sub_mem_extendedIdeal J hM hr m]

/-- The canonical scalar-action map is bijective on an annihilated module. -/
theorem scalarTensorMap_bijective (J : Ideal R)
    (hcoeff : Function.Surjective
      ((Ideal.Quotient.mk (J.map (algebraMap R S))).comp (algebraMap R S)))
    (hM : J.map (algebraMap R S) • (⊤ : Submodule S M) = ⊥) :
    Function.Bijective (scalarTensorMap (R := R) (S := S) (M := M)) := by
  have hinv : ∀ z : S ⊗[R] M,
      (1 : S) ⊗ₜ[R] scalarTensorMap (R := R) z = z := by
    intro z
    induction z using TensorProduct.inductionOn with
    | tmul s m => exact (tmul_eq_one_tmul_smul J hcoeff hM s m).symm
    | add x y hx hy => rw [map_add, TensorProduct.tmul_add, hx, hy]
  refine ⟨?_, fun m => ⟨(1 : S) ⊗ₜ[R] m, one_smul S m⟩⟩
  intro x y h
  rw [← hinv x, h, hinv y]

/-- Actual scalar extension and restriction cancel on a module killed by
the extended source ideal. -/
def torsionTensorEquiv (J : Ideal R)
    (hcoeff : Function.Surjective
      ((Ideal.Quotient.mk (J.map (algebraMap R S))).comp (algebraMap R S)))
    (hM : J.map (algebraMap R S) • (⊤ : Submodule S M) = ⊥) :
    S ⊗[R] M ≃ₗ[S] M :=
  LinearEquiv.ofBijective scalarTensorMap (scalarTensorMap_bijective J hcoeff hM)

@[simp]
theorem torsionTensorEquiv_tmul (J : Ideal R)
    (hcoeff : Function.Surjective
      ((Ideal.Quotient.mk (J.map (algebraMap R S))).comp (algebraMap R S)))
    (hM : J.map (algebraMap R S) • (⊤ : Submodule S M) = ⊥) (s : S) (m : M) :
    torsionTensorEquiv J hcoeff hM (s ⊗ₜ[R] m) = s • m := rfl

@[simp]
theorem torsionTensorEquiv_symm_apply (J : Ideal R)
    (hcoeff : Function.Surjective
      ((Ideal.Quotient.mk (J.map (algebraMap R S))).comp (algebraMap R S)))
    (hM : J.map (algebraMap R S) • (⊤ : Submodule S M) = ⊥) (m : M) :
    (torsionTensorEquiv J hcoeff hM).symm m = (1 : S) ⊗ₜ[R] m := by
  apply (torsionTensorEquiv J hcoeff hM).injective
  rw [LinearEquiv.apply_symm_apply, torsionTensorEquiv_tmul, one_smul]

variable {N : Type*} [AddCommGroup N] [Module R N] [Module S N]
  [IsScalarTower R S N]

/-- Original base-ring-linear maps between annihilated modules are already
linear for the extended scalars. -/
def linearMapOfTorsion (J : Ideal R)
    (hcoeff : Function.Surjective
      ((Ideal.Quotient.mk (J.map (algebraMap R S))).comp (algebraMap R S)))
    (hM : J.map (algebraMap R S) • (⊤ : Submodule S M) = ⊥)
    (hN : J.map (algebraMap R S) • (⊤ : Submodule S N) = ⊥)
    (f : M →ₗ[R] N) : M →ₗ[S] N where
  toFun := f
  map_add' := f.map_add
  map_smul' s m := by
    change f (s • m) = s • f m
    obtain ⟨r, hr⟩ := exists_sub_mem_extendedIdeal J hcoeff s
    calc
      f (s • m) = f (r • m) :=
        congrArg f (smul_eq_of_sub_mem_extendedIdeal J hM hr m)
      _ = r • f m := f.map_smul r m
      _ = s • f m := (smul_eq_of_sub_mem_extendedIdeal J hN hr (f m)).symm

@[simp]
theorem linearMapOfTorsion_restrictScalars (J : Ideal R)
    (hcoeff : Function.Surjective
      ((Ideal.Quotient.mk (J.map (algebraMap R S))).comp (algebraMap R S)))
    (hM : J.map (algebraMap R S) • (⊤ : Submodule S M) = ⊥)
    (hN : J.map (algebraMap R S) • (⊤ : Submodule S N) = ⊥)
    (f : M →ₗ[R] N) :
    (linearMapOfTorsion J hcoeff hM hN f).restrictScalars R = f := rfl

end Modules

section Algebras

variable {D : Type*} [CommRing D] [Algebra R D] [Algebra S D]
  [IsScalarTower R S D]

/-- The module comparison has the same forward map as the original
multiplicative algebra counit. -/
theorem counit_toLinearMap :
    (counit R S D).toLinearMap = scalarTensorMap (R := R) (S := S) (M := D) := by
  apply AlgebraTensorModule.ext
  intro s d
  rfl

/-- For an annihilated algebra, the comparison is an actual algebra
isomorphism, so its unit and multiplication are retained. -/
def torsionTensorAlgEquiv (J : Ideal R)
    (hcoeff : Function.Surjective
      ((Ideal.Quotient.mk (J.map (algebraMap R S))).comp (algebraMap R S)))
    (hD : J.map (algebraMap R S) • (⊤ : Submodule S D) = ⊥) :
    S ⊗[R] D ≃ₐ[S] D := by
  apply AlgEquiv.ofBijective (counit R S D)
  change Function.Bijective (counit R S D).toLinearMap
  rw [counit_toLinearMap]
  exact scalarTensorMap_bijective J hcoeff hD

@[simp]
theorem torsionTensorAlgEquiv_tmul (J : Ideal R)
    (hcoeff : Function.Surjective
      ((Ideal.Quotient.mk (J.map (algebraMap R S))).comp (algebraMap R S)))
    (hD : J.map (algebraMap R S) • (⊤ : Submodule S D) = ⊥) (s : S) (d : D) :
    torsionTensorAlgEquiv J hcoeff hD (s ⊗ₜ[R] d) = algebraMap S D s * d := by
  change counit R S D (s ⊗ₜ[R] d) = algebraMap S D s * d
  rw [counit_tmul, Algebra.smul_def]

@[simp]
theorem torsionTensorAlgEquiv_symm_apply (J : Ideal R)
    (hcoeff : Function.Surjective
      ((Ideal.Quotient.mk (J.map (algebraMap R S))).comp (algebraMap R S)))
    (hD : J.map (algebraMap R S) • (⊤ : Submodule S D) = ⊥) (d : D) :
    (torsionTensorAlgEquiv J hcoeff hD).symm d = (1 : S) ⊗ₜ[R] d := by
  apply (torsionTensorAlgEquiv J hcoeff hD).injective
  rw [AlgEquiv.apply_symm_apply, torsionTensorAlgEquiv_tmul, map_one, one_mul]

end Algebras

section Submodules

variable {M : Type*} [AddCommGroup M] [Module R M]

/-- The original-unit inverse image of an extended-scalar submodule. -/
def unitPreimage (P : Submodule S (S ⊗[R] M)) : Submodule R M :=
  (P.restrictScalars R).comap (TensorProduct.mk R S M 1)

@[simp]
theorem mem_unitPreimage (P : Submodule S (S ⊗[R] M)) (m : M) :
    m ∈ unitPreimage P ↔ (1 : S) ⊗ₜ[R] m ∈ P := Iff.rfl

/-- The actual scalar-extension image of the original-unit preimage always
lies in the given submodule. -/
theorem unitPreimage_baseChange_le (P : Submodule S (S ⊗[R] M)) :
    (unitPreimage P).baseChange S ≤ P := by
  rw [Submodule.baseChange_eq_span]
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨m, hm, rfl⟩
  exact hm

/-- Containment of the extended-ideal multiple puts the original ideal
multiple inside the original-unit preimage. -/
theorem smul_top_le_unitPreimage (J : Ideal R)
    (P : Submodule S (S ⊗[R] M))
    (hP : J.map (algebraMap R S) • (⊤ : Submodule S (S ⊗[R] M)) ≤ P) :
    J • (⊤ : Submodule R M) ≤ unitPreimage P := by
  apply Submodule.smul_le.mpr
  intro r hr m _
  change (1 : S) ⊗ₜ[R] (r • m) ∈ P
  have h := hP (Submodule.smul_mem_smul (Ideal.mem_map_of_mem (algebraMap R S) hr)
    (Submodule.mem_top : (1 : S) ⊗ₜ[R] m ∈ (⊤ : Submodule S (S ⊗[R] M))))
  simpa only [algebraMap_smul, TensorProduct.tmul_smul] using h

/-- A coefficient error in the extended source ideal lies in the actual
tensor image of the original-unit preimage. -/
theorem tmul_mem_baseChange_unitPreimage (J : Ideal R)
    (P : Submodule S (S ⊗[R] M))
    (hP : J.map (algebraMap R S) • (⊤ : Submodule S (S ⊗[R] M)) ≤ P)
    {s : S} (hs : s ∈ J.map (algebraMap R S)) (m : M) :
    s ⊗ₜ[R] m ∈ (unitPreimage P).baseChange S := by
  have hs' : s ∈ J • (⊤ : Submodule R S) := by
    rw [Ideal.smul_top_eq_map]
    exact hs
  refine Submodule.smul_induction_on hs' (fun r hr t _ => ?_)
    (fun x y hx hy => by
      rw [TensorProduct.add_tmul]
      exact Submodule.add_mem _ hx hy)
  rw [TensorProduct.smul_tmul]
  exact Submodule.tmul_mem_baseChange_of_mem t
    (smul_top_le_unitPreimage J P hP
      (Submodule.smul_mem_smul hr (Submodule.mem_top : m ∈ (⊤ : Submodule R M))))

/-- Each tensor differs from an original-unit tensor by an element of the
constructed tensor image. Only finitely many coefficient corrections occur. -/
theorem exists_sub_one_tmul_mem_baseChange_unitPreimage (J : Ideal R)
    (hcoeff : Function.Surjective
      ((Ideal.Quotient.mk (J.map (algebraMap R S))).comp (algebraMap R S)))
    (P : Submodule S (S ⊗[R] M))
    (hP : J.map (algebraMap R S) • (⊤ : Submodule S (S ⊗[R] M)) ≤ P)
    (z : S ⊗[R] M) :
    ∃ m : M, z - (1 : S) ⊗ₜ[R] m ∈ (unitPreimage P).baseChange S := by
  induction z using TensorProduct.inductionOn with
  | tmul s m =>
      obtain ⟨r, hr⟩ := exists_sub_mem_extendedIdeal J hcoeff s
      refine ⟨r • m, ?_⟩
      have he : (1 : S) ⊗ₜ[R] (r • m) = algebraMap R S r ⊗ₜ[R] m := by
        rw [Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]
      rw [he, ← TensorProduct.sub_tmul]
      exact tmul_mem_baseChange_unitPreimage J P hP hr m
  | add x y hx hy =>
      obtain ⟨m, hm⟩ := hx
      obtain ⟨n, hn⟩ := hy
      refine ⟨m + n, ?_⟩
      rw [TensorProduct.tmul_add, add_sub_add_comm]
      exact Submodule.add_mem _ hm hn

/-- Effectivity for a submodule with bounded cokernel: its inverse image
under the original unit has exactly the specified scalar-extension image.
`Submodule.baseChange` is the range of the base-changed original inclusion. -/
theorem unitPreimage_baseChange (J : Ideal R)
    (hcoeff : Function.Surjective
      ((Ideal.Quotient.mk (J.map (algebraMap R S))).comp (algebraMap R S)))
    (P : Submodule S (S ⊗[R] M))
    (hP : J.map (algebraMap R S) • (⊤ : Submodule S (S ⊗[R] M)) ≤ P) :
    (unitPreimage P).baseChange S = P := by
  apply le_antisymm (unitPreimage_baseChange_le P)
  intro z hz
  obtain ⟨m, hm⟩ := exists_sub_one_tmul_mem_baseChange_unitPreimage J hcoeff P hP z
  have hPm : (1 : S) ⊗ₜ[R] m ∈ P := by
    have h := P.sub_mem hz (unitPreimage_baseChange_le P hm)
    simpa only [sub_sub_cancel] using h
  have hone : (1 : S) ⊗ₜ[R] m ∈ (unitPreimage P).baseChange S :=
    Submodule.tmul_mem_baseChange_of_mem 1 hPm
  simpa only [sub_add_cancel] using ((unitPreimage P).baseChange S).add_mem hm hone

/-- The canonical flat-base-change isomorphism onto the original submodule. -/
def unitPreimageTensorEquiv [Module.Flat R S] (J : Ideal R)
    (hcoeff : Function.Surjective
      ((Ideal.Quotient.mk (J.map (algebraMap R S))).comp (algebraMap R S)))
    (P : Submodule S (S ⊗[R] M))
    (hP : J.map (algebraMap R S) • (⊤ : Submodule S (S ⊗[R] M)) ≤ P) :
    S ⊗[R] unitPreimage P ≃ₗ[S] P :=
  (Submodule.toBaseChange.toLinearEquiv S (unitPreimage P)).trans
    (LinearEquiv.ofEq _ _ (unitPreimage_baseChange J hcoeff P hP))

/-- The reconstructed comparison is the base change of the original
submodule inclusion, with only its codomain restricted. -/
theorem unitPreimageTensorEquiv_apply [Module.Flat R S] (J : Ideal R)
    (hcoeff : Function.Surjective
      ((Ideal.Quotient.mk (J.map (algebraMap R S))).comp (algebraMap R S)))
    (P : Submodule S (S ⊗[R] M))
    (hP : J.map (algebraMap R S) • (⊤ : Submodule S (S ⊗[R] M)) ≤ P)
    (z : S ⊗[R] unitPreimage P) :
    (unitPreimageTensorEquiv J hcoeff P hP z : S ⊗[R] M) =
      (unitPreimage P).subtype.baseChange S z := rfl

@[simp]
theorem unitPreimageTensorEquiv_tmul [Module.Flat R S] (J : Ideal R)
    (hcoeff : Function.Surjective
      ((Ideal.Quotient.mk (J.map (algebraMap R S))).comp (algebraMap R S)))
    (P : Submodule S (S ⊗[R] M))
    (hP : J.map (algebraMap R S) • (⊤ : Submodule S (S ⊗[R] M)) ≤ P)
    (s : S) (m : unitPreimage P) :
    (unitPreimageTensorEquiv J hcoeff P hP (s ⊗ₜ[R] m) : S ⊗[R] M) =
      s ⊗ₜ[R] (m : M) := rfl

/-- The constructed original-unit preimage is finite in a finite ambient
module over a Noetherian ring. This finiteness needs no flatness hypothesis. -/
theorem finite_unitPreimage [IsNoetherianRing R] [Module.Finite R M]
    (P : Submodule S (S ⊗[R] M)) : Module.Finite R (unitPreimage P) := by
  infer_instance

end Submodules

section CrossRelations

variable {ι : Type*}

/-- The finite-coordinate cross-relation map for a family of source
coefficients. Its kernel is the ambient module for conductor multiplication. -/
def crossRelationMap (d : ι → R) : (ι → R) →ₗ[R] ((ι × ι) → R) :=
  LinearMap.pi fun ij =>
    d ij.1 • LinearMap.proj ij.2 - d ij.2 • LinearMap.proj ij.1

@[simp]
theorem crossRelationMap_apply (d : ι → R) (x : ι → R) (ij : ι × ι) :
    crossRelationMap d x ij = d ij.1 * x ij.2 - d ij.2 * x ij.1 := rfl

/-- The original cross-relation kernel, with no domain or regularity premise. -/
abbrev crossRelations (d : ι → R) : Submodule R (ι → R) :=
  (crossRelationMap d).ker

theorem mem_crossRelations (d : ι → R) (x : ι → R) :
    x ∈ crossRelations d ↔ ∀ i j, d i * x j = d j * x i := by
  constructor
  · intro hx i j
    exact sub_eq_zero.mp (congrFun (show crossRelationMap d x = 0 from hx) (i, j))
  · intro hx
    change crossRelationMap d x = 0
    funext ij
    exact sub_eq_zero.mpr (hx ij.1 ij.2)

/-- Original scalars give the distinguished scalar vectors in the kernel. -/
def crossRelationScalars (d : ι → R) : R →ₗ[R] crossRelations d :=
  (LinearMap.toSpanSingleton R (ι → R) d).codRestrict _ (by
    intro b
    apply (mem_crossRelations d _).mpr
    intro i j
    change d i * (b * d j) = d j * (b * d i)
    rw [mul_left_comm (d i) b (d j), mul_left_comm (d j) b (d i),
      mul_comm (d i) (d j)])

@[simp]
theorem crossRelationScalars_apply (d : ι → R) (b : R) (i : ι) :
    (crossRelationScalars d b : ι → R) i = b * d i := rfl

/-- One regular coordinate makes the original scalar-vector map injective. -/
theorem crossRelationScalars_injective (d : ι → R) (i : ι)
    (hreg : IsSMulRegular R (d i)) : Function.Injective (crossRelationScalars d) := by
  intro b c h
  apply hreg
  have hc := congrArg (fun x : crossRelations d => (x : ι → R) i) h
  change d i * b = d i * c
  change b * d i = c * d i at hc
  exact (mul_comm (d i) b).trans (hc.trans (mul_comm c (d i)))

/-- A generator times a cross-relation vector is the original scalar vector
given by that vector's matching coordinate. -/
theorem generator_smul_crossRelation (d : ι → R) (i : ι) (x : crossRelations d) :
    d i • x = crossRelationScalars d ((x : ι → R) i) := by
  apply Subtype.ext
  funext j
  change d i * (x : ι → R) j = (x : ι → R) i * d j
  exact ((mem_crossRelations d x).mp x.property i j).trans (mul_comm _ _)

/-- The generated ideal times the whole ambient kernel lies in its scalar
copy of the original ring. -/
theorem span_smul_top_le_crossRelationScalars_range (d : ι → R) :
    Ideal.span (Set.range d) • (⊤ : Submodule R (crossRelations d)) ≤
      (crossRelationScalars d).range := by
  apply Submodule.smul_le.mpr
  intro r hr x _
  induction hr using Submodule.span_induction with
  | mem a ha =>
      obtain ⟨i, rfl⟩ := ha
      exact ⟨(x : ι → R) i, (generator_smul_crossRelation d i x).symm⟩
  | zero => simpa only [zero_smul] using (crossRelationScalars d).range.zero_mem
  | add a b _ _ ha hb =>
      simpa only [add_smul] using (crossRelationScalars d).range.add_mem ha hb
  | smul a b _ hb =>
      simpa only [smul_smul, smul_eq_mul] using (crossRelationScalars d).range.smul_mem a hb

/-- The cross-relation ambient is finite over a Noetherian source ring. -/
theorem finite_crossRelations [Finite ι] [IsNoetherianRing R] (d : ι → R) :
    Module.Finite R (crossRelations d) := by
  infer_instance

section FiniteCoordinates

variable [Fintype ι] [DecidableEq ι]

/-- The actual finite-coordinate tensor maps commute with the cross-relation
maps formed from the original coefficients and their images. -/
theorem crossRelationMap_baseChange (d : ι → R) :
    (crossRelationMap (fun i => algebraMap R S (d i))).comp
        (TensorProduct.piScalarRight R S S ι).toLinearMap =
      (TensorProduct.piScalarRight R S S (ι × ι)).toLinearMap.comp
        (AlgebraTensorModule.lTensor S S (crossRelationMap d)) := by
  apply AlgebraTensorModule.ext
  intro s x
  funext ij
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe,
    AlgebraTensorModule.lTensor_tmul, TensorProduct.piScalarRight_apply,
    TensorProduct.piScalarRightHom_tmul, crossRelationMap_apply,
    Algebra.smul_def, map_sub, map_mul, sub_mul, mul_assoc]

/-- Coordinate transport identifies the kernel of the base-changed matrix
with the actual cross-relation kernel over the extended ring. -/
def crossRelationKernelEquiv (d : ι → R) :
    (AlgebraTensorModule.lTensor S S (crossRelationMap d)).ker ≃ₗ[S]
      crossRelations (fun i => algebraMap R S (d i)) :=
  (TensorProduct.piScalarRight R S S ι).ofSubmodules _ _ (by
    apply le_antisymm
    · rintro y ⟨x, hx, rfl⟩
      change crossRelationMap (fun i => algebraMap R S (d i))
        (TensorProduct.piScalarRight R S S ι x) = 0
      have h : crossRelationMap (fun i => algebraMap R S (d i))
          (TensorProduct.piScalarRight R S S ι x) =
          TensorProduct.piScalarRight R S S (ι × ι)
            (AlgebraTensorModule.lTensor S S (crossRelationMap d) x) :=
        LinearMap.congr_fun (crossRelationMap_baseChange (S := S) d) x
      have hx0 : AlgebraTensorModule.lTensor S S (crossRelationMap d) x = 0 := hx
      exact h.trans (by rw [hx0, map_zero])
    · intro y hy
      refine ⟨(TensorProduct.piScalarRight R S S ι).symm y, ?_,
        (TensorProduct.piScalarRight R S S ι).apply_symm_apply y⟩
      change AlgebraTensorModule.lTensor S S (crossRelationMap d)
        ((TensorProduct.piScalarRight R S S ι).symm y) = 0
      have h : crossRelationMap (fun i => algebraMap R S (d i))
          (TensorProduct.piScalarRight R S S ι
            ((TensorProduct.piScalarRight R S S ι).symm y)) =
          TensorProduct.piScalarRight R S S (ι × ι)
            (AlgebraTensorModule.lTensor S S (crossRelationMap d)
              ((TensorProduct.piScalarRight R S S ι).symm y)) :=
        LinearMap.congr_fun (crossRelationMap_baseChange (S := S) d)
          ((TensorProduct.piScalarRight R S S ι).symm y)
      apply (TensorProduct.piScalarRight R S S (ι × ι)).injective
      rw [map_zero, ← h, LinearEquiv.apply_symm_apply]
      exact hy)

/-- Flat base change of the finite cross-relation ambient through the
original coordinate maps. -/
def crossRelationsTensorEquiv [Module.Flat R S] (d : ι → R) :
    S ⊗[R] crossRelations d ≃ₗ[S] crossRelations (fun i => algebraMap R S (d i)) :=
  (LinearMap.tensorKerEquiv S S (crossRelationMap d)).trans
    (crossRelationKernelEquiv (S := S) d)

@[simp]
theorem crossRelationsTensorEquiv_tmul [Module.Flat R S] (d : ι → R)
    (s : S) (x : crossRelations d) (i : ι) :
    (crossRelationsTensorEquiv (S := S) d (s ⊗ₜ[R] x) : ι → S) i =
      algebraMap R S ((x : ι → R) i) * s := by
  change (TensorProduct.piScalarRight R S S ι (s ⊗ₜ[R] (x : ι → R))) i = _
  rw [TensorProduct.piScalarRight_apply, TensorProduct.piScalarRightHom_tmul]
  exact Algebra.smul_def _ _

end FiniteCoordinates

section Conductor

variable {D : Type*} [CommRing D] [Algebra R D]

/-- The unique original-ring coefficient of multiplication by one conductor
generator, extracted through the original injective structural map. -/
def conductorCoordinate (d : ι → R)
    (hinj : Function.Injective (algebraMap R D))
    (hcond : ∀ i : ι, ∀ z : D, ∃ r : R, algebraMap R D r = d i • z)
    (i : ι) : D →ₗ[R] R :=
  (LinearEquiv.ofInjective (Algebra.linearMap R D) hinj).symm.toLinearMap.comp
    ((LinearMap.lsmul R D (d i)).codRestrict (Algebra.linearMap R D).range
      (fun z => hcond i z))

/-- The coordinate extraction preserves the literal conductor product. -/
theorem algebraMap_conductorCoordinate (d : ι → R)
    (hinj : Function.Injective (algebraMap R D))
    (hcond : ∀ i : ι, ∀ z : D, ∃ r : R, algebraMap R D r = d i • z)
    (i : ι) (z : D) :
    algebraMap R D (conductorCoordinate d hinj hcond i z) = d i • z := by
  exact LinearEquiv.ofInjective_symm_apply (Algebra.linearMap R D)
    (h := hinj) ⟨d i • z, hcond i z⟩

/-- Multiplication by all actual conductor generators gives a map into the
cross-relation ambient. -/
def conductorMap (d : ι → R)
    (hinj : Function.Injective (algebraMap R D))
    (hcond : ∀ i : ι, ∀ z : D, ∃ r : R, algebraMap R D r = d i • z) :
    D →ₗ[R] crossRelations d :=
  (LinearMap.pi (conductorCoordinate d hinj hcond)).codRestrict _ (by
    intro z
    apply (mem_crossRelations d _).mpr
    intro i j
    apply hinj
    change algebraMap R D (d i * conductorCoordinate d hinj hcond j z) =
      algebraMap R D (d j * conductorCoordinate d hinj hcond i z)
    rw [map_mul, map_mul, algebraMap_conductorCoordinate,
      algebraMap_conductorCoordinate, Algebra.smul_def, Algebra.smul_def]
    exact mul_left_comm _ _ _)

@[simp]
theorem conductorMap_apply (d : ι → R)
    (hinj : Function.Injective (algebraMap R D))
    (hcond : ∀ i : ι, ∀ z : D, ∃ r : R, algebraMap R D r = d i • z)
    (z : D) (i : ι) :
    (conductorMap d hinj hcond z : ι → R) i =
      conductorCoordinate d hinj hcond i z := rfl

/-- A generator regular on the original algebra makes the conductor map
injective. Regularity is an explicit pointwise premise, not inferred from
normality of an unspecified finite algebra. -/
theorem conductorMap_injective (d : ι → R)
    (hinj : Function.Injective (algebraMap R D))
    (hcond : ∀ i : ι, ∀ z : D, ∃ r : R, algebraMap R D r = d i • z)
    (i : ι) (hreg : IsSMulRegular D (d i)) :
    Function.Injective (conductorMap d hinj hcond) := by
  intro x y h
  apply hreg
  have hc := congrArg (fun z : crossRelations d =>
    algebraMap R D ((z : ι → R) i)) h
  change algebraMap R D (conductorCoordinate d hinj hcond i x) =
    algebraMap R D (conductorCoordinate d hinj hcond i y) at hc
  simpa only [algebraMap_conductorCoordinate] using hc

/-- The conductor map extends the original scalar-vector map. -/
theorem conductorMap_algebraMap (d : ι → R)
    (hinj : Function.Injective (algebraMap R D))
    (hcond : ∀ i : ι, ∀ z : D, ∃ r : R, algebraMap R D r = d i • z) (r : R) :
    conductorMap d hinj hcond (algebraMap R D r) = crossRelationScalars d r := by
  apply Subtype.ext
  funext i
  apply hinj
  change algebraMap R D (conductorCoordinate d hinj hcond i (algebraMap R D r)) =
    algebraMap R D (r * d i)
  rw [algebraMap_conductorCoordinate, Algebra.smul_def, map_mul]
  exact mul_comm _ _

/-- The actual conductor image contains the generated-ideal multiple of
the ambient kernel, which is the bounded-cokernel input for submodule descent. -/
theorem span_smul_top_le_conductorMap_range (d : ι → R)
    (hinj : Function.Injective (algebraMap R D))
    (hcond : ∀ i : ι, ∀ z : D, ∃ r : R, algebraMap R D r = d i • z) :
    Ideal.span (Set.range d) • (⊤ : Submodule R (crossRelations d)) ≤
      (conductorMap d hinj hcond).range := by
  apply (span_smul_top_le_crossRelationScalars_range d).trans
  rintro x ⟨r, rfl⟩
  exact ⟨algebraMap R D r, conductorMap_algebraMap d hinj hcond r⟩

end Conductor

end CrossRelations

section Localization

private theorem away_algebraMap_injective (t : R) (hreg : IsSMulRegular R t) :
    Function.Injective (algebraMap R (Localization.Away t)) := by
  intro x y h
  obtain ⟨n, hn⟩ := IsLocalization.Away.exists_of_eq (x := t) h
  exact IsSMulRegular.pow n hreg hn

private theorem localizationBaseMap_ringHom_comp (t : R) :
    (Localization.awayMap (algebraMap R S) t).comp
        (algebraMap R (Localization.Away t)) =
      (algebraMap S (Localization.Away (algebraMap R S t))).comp (algebraMap R S) := by
  unfold Localization.awayMap IsLocalization.Away.map
  apply IsLocalization.map_comp

/-- The original map between the two principal localizations, retaining
the original base ring as algebra scalars. -/
def localizationBaseMap (t : R) :
    Localization.Away t →ₐ[R] Localization.Away (algebraMap R S t) where
  toRingHom := Localization.awayMap (algebraMap R S) t
  commutes' r := by
    have h : Localization.awayMap (algebraMap R S) t
        (algebraMap R (Localization.Away t) r) =
        algebraMap S (Localization.Away (algebraMap R S t)) (algebraMap R S r) :=
      congrArg (fun f : R →+* Localization.Away (algebraMap R S t) => f r)
        (localizationBaseMap_ringHom_comp (S := S) t)
    exact h.trans (IsScalarTower.algebraMap_apply R S
      (Localization.Away (algebraMap R S t)) r).symm

theorem localizationBaseMap_algebraMap (t r : R) :
    localizationBaseMap (S := S) t (algebraMap R (Localization.Away t) r) =
      algebraMap S (Localization.Away (algebraMap R S t)) (algebraMap R S r) := by
  exact congrArg (fun f : R →+* Localization.Away (algebraMap R S t) => f r)
    (localizationBaseMap_ringHom_comp (S := S) t)

/-- Faithfully flat principal-ideal contraction detects an original scalar
inside the principal localization. The coefficient map is the actual
localized original map. -/
theorem exists_scalar_of_localizationBaseMap [Module.FaithfullyFlat R S]
    (t : R) (hreg : IsSMulRegular R t) (x : Localization.Away t) (s : S)
    (h : localizationBaseMap (S := S) t x =
      algebraMap S (Localization.Away (algebraMap R S t)) s) :
    ∃ r : R, x = algebraMap R (Localization.Away t) r := by
  let L := Localization.Away t
  let U := Localization.Away (algebraMap R S t)
  let F : L →ₐ[R] U := localizationBaseMap t
  have hF (r : R) : F (algebraMap R L r) = algebraMap S U (algebraMap R S r) :=
    localizationBaseMap_algebraMap t r
  have hregS : IsSMulRegular S (algebraMap R S t) := hreg.of_flat
  have hinj : Function.Injective (algebraMap S U) :=
    away_algebraMap_injective (algebraMap R S t) hregS
  obtain ⟨n, b, hb⟩ := IsLocalization.Away.surj t x
  have hs : algebraMap R S b = algebraMap R S (t ^ n) * s := by
    apply hinj
    calc
      algebraMap S U (algebraMap R S b) = F (algebraMap R L b) := (hF b).symm
      _ = F (x * algebraMap R L t ^ n) := congrArg F hb.symm
      _ = algebraMap S U s * algebraMap S U (algebraMap R S t) ^ n := by
        rw [map_mul, map_pow, h, hF]
      _ = algebraMap S U (algebraMap R S (t ^ n) * s) := by
        rw [map_mul, map_pow, map_pow, mul_comm]
  have hmem : b ∈ Ideal.span {t ^ n} := by
    rw [← Ideal.comap_map_eq_self_of_faithfullyFlat (B := S) (Ideal.span {t ^ n})]
    change algebraMap R S b ∈ (Ideal.span {t ^ n}).map (algebraMap R S)
    rw [Ideal.map_span, Set.image_singleton, Ideal.mem_span_singleton]
    exact ⟨s, hs⟩
  obtain ⟨r, hr⟩ := Ideal.mem_span_singleton.mp hmem
  refine ⟨r, (IsLocalization.Away.algebraMap_pow_isUnit (S := L) t n).mul_right_cancel ?_⟩
  calc
    x * algebraMap R L t ^ n = algebraMap R L b := hb
    _ = algebraMap R L r * algebraMap R L t ^ n := by
      rw [hr, map_mul, map_pow, mul_comm]

section ConductorLocalization

variable {D : Type*} [CommRing D] [Algebra R D]

/-- Inverting a conductor element identifies the two actual localizations.
This construction uses the original structural map and the original
conductor products. Regularity on the larger algebra is not needed here. -/
def conductorAwayEquiv (t : R) (hinj : Function.Injective (algebraMap R D))
    (hcond : ∀ z : D, ∃ r : R, algebraMap R D r = t • z) :
    Localization.Away t ≃ₐ[R] Localization.Away (algebraMap R D t) := by
  apply AlgEquiv.ofBijective (localizationBaseMap (S := D) t)
  constructor
  · change Function.Injective (Localization.awayMap (algebraMap R D) t)
    apply Localization.awayMap_injective_iff.mpr
    intro x hx
    have hx0 : x = 0 := hinj (by simpa only [map_zero] using hx)
    exact ⟨0, by simpa only [pow_zero, one_mul] using hx0⟩
  · change Function.Surjective (Localization.awayMap (algebraMap R D) t)
    apply Localization.awayMap_surjective_iff.mpr
    intro z
    obtain ⟨r, hr⟩ := hcond z
    exact ⟨r, 1, by simpa only [pow_one, Algebra.smul_def] using hr⟩

/-- The actual conductor localization map into the original ring's
principal localization. Its kernel is not discarded by definition. -/
def conductorLocalizationMap (t : R)
    (hinj : Function.Injective (algebraMap R D))
    (hcond : ∀ z : D, ∃ r : R, algebraMap R D r = t • z) :
    D →ₐ[R] Localization.Away t :=
  (conductorAwayEquiv t hinj hcond).symm.toAlgHom.comp
    (IsScalarTower.toAlgHom R D (Localization.Away (algebraMap R D t)))

/-- A regular conductor acts injectively on the original algebra, so its
actual map into the localization of the scalar ring is injective. -/
theorem conductorLocalizationMap_injective (t : R)
    (hinj : Function.Injective (algebraMap R D))
    (hcond : ∀ z : D, ∃ r : R, algebraMap R D r = t • z)
    (hreg : IsSMulRegular D t) :
    Function.Injective (conductorLocalizationMap t hinj hcond) := by
  have hregD : IsSMulRegular D (algebraMap R D t) := by
    intro x y hxy
    apply hreg
    change algebraMap R D t * x = algebraMap R D t * y at hxy
    simpa only [Algebra.smul_def] using hxy
  exact (conductorAwayEquiv t hinj hcond).symm.injective.comp
    (away_algebraMap_injective (algebraMap R D t) hregD)

end ConductorLocalization

section RegularConductorModel

variable {D : Type*} [CommRing D] [Algebra R D] [Algebra S D]
  [IsScalarTower R S D]

/-- The actual localization-intersection subalgebra, constructed as the
preimage of the actual conductor localization image. -/
def regularConductorSubalgebra (t : R)
    (hinj : Function.Injective (algebraMap S D))
    (hcond : ∀ z : D, ∃ s : S, algebraMap S D s = algebraMap R S t • z) :
    Subalgebra R (Localization.Away t) :=
  ((conductorLocalizationMap (algebraMap R S t) hinj hcond).restrictScalars R).range.comap
    (localizationBaseMap (S := S) t)

/-- The original algebra map from the localization-intersection subalgebra
to the given completed algebra, obtained by inverting its actual image. -/
def regularConductorMap (t : R)
    (hinj : Function.Injective (algebraMap S D))
    (hcond : ∀ z : D, ∃ s : S, algebraMap S D s = algebraMap R S t • z)
    (hreg : IsSMulRegular D (algebraMap R S t)) :
    regularConductorSubalgebra t hinj hcond →ₐ[R] D := by
  let j : D →ₐ[R] Localization.Away (algebraMap R S t) :=
    (conductorLocalizationMap (algebraMap R S t) hinj hcond).restrictScalars R
  let e : D ≃ₐ[R] j.range := AlgEquiv.ofInjective j
    (conductorLocalizationMap_injective (algebraMap R S t) hinj hcond hreg)
  let p : regularConductorSubalgebra t hinj hcond →ₐ[R] j.range :=
    ((localizationBaseMap (S := S) t).comp
      (regularConductorSubalgebra t hinj hcond).val).codRestrict _ (fun z => z.property)
  exact e.symm.toAlgHom.comp p

/-- The original localization triangle for every element of the constructed
subalgebra. -/
theorem regularConductorMap_localization (t : R)
    (hinj : Function.Injective (algebraMap S D))
    (hcond : ∀ z : D, ∃ s : S, algebraMap S D s = algebraMap R S t • z)
    (hreg : IsSMulRegular D (algebraMap R S t))
    (z : regularConductorSubalgebra t hinj hcond) :
    conductorLocalizationMap (algebraMap R S t) hinj hcond
        (regularConductorMap t hinj hcond hreg z) =
      localizationBaseMap (S := S) t z := by
  let j : D →ₐ[R] Localization.Away (algebraMap R S t) :=
    (conductorLocalizationMap (algebraMap R S t) hinj hcond).restrictScalars R
  let e : D ≃ₐ[R] j.range := AlgEquiv.ofInjective j
    (conductorLocalizationMap_injective (algebraMap R S t) hinj hcond hreg)
  change j (e.symm ⟨localizationBaseMap (S := S) t z, z.property⟩) =
    localizationBaseMap (S := S) t z
  exact congrArg Subtype.val (e.apply_symm_apply _)

/-- The canonical algebra comparison to be proved bijective in regular
conductor effectivity. Its formula retains the original scalar and algebra maps. -/
def regularConductorBaseChange (t : R)
    (hinj : Function.Injective (algebraMap S D))
    (hcond : ∀ z : D, ∃ s : S, algebraMap S D s = algebraMap R S t • z)
    (hreg : IsSMulRegular D (algebraMap R S t)) :
    S ⊗[R] regularConductorSubalgebra t hinj hcond →ₐ[S] D :=
  AlgHom.liftEquiv R S _ D (regularConductorMap t hinj hcond hreg)

@[simp]
theorem regularConductorBaseChange_tmul (t : R)
    (hinj : Function.Injective (algebraMap S D))
    (hcond : ∀ z : D, ∃ s : S, algebraMap S D s = algebraMap R S t • z)
    (hreg : IsSMulRegular D (algebraMap R S t))
    (s : S) (z : regularConductorSubalgebra t hinj hcond) :
    regularConductorBaseChange t hinj hcond hreg (s ⊗ₜ[R] z) =
      s • regularConductorMap t hinj hcond hreg z := rfl

end RegularConductorModel

end Localization

section FractionalKernel

variable {ι : Type*}

/-- The actual fraction represented by a cross-relation vector, using its
specified denominator coordinate. -/
def crossRelationFraction (d : ι → R) (i₀ : ι) :
    crossRelations d →ₗ[R] Localization.Away (d i₀) where
  toFun x := algebraMap R (Localization.Away (d i₀)) ((x : ι → R) i₀) *
    IsLocalization.Away.invSelf (d i₀)
  map_add' x y := by
    change algebraMap R (Localization.Away (d i₀))
        ((x : ι → R) i₀ + (y : ι → R) i₀) * _ = _
    rw [map_add, add_mul]
  map_smul' r x := by
    change algebraMap R (Localization.Away (d i₀)) (r * (x : ι → R) i₀) * _ =
      r • (algebraMap R (Localization.Away (d i₀)) ((x : ι → R) i₀) * _)
    rw [map_mul, Algebra.smul_def, mul_assoc]

@[simp]
theorem crossRelationFraction_apply (d : ι → R) (i₀ : ι) (x : crossRelations d) :
    crossRelationFraction d i₀ x =
      algebraMap R (Localization.Away (d i₀)) ((x : ι → R) i₀) *
        IsLocalization.Away.invSelf (d i₀) := rfl

/-- Every coordinate is the original product of its generator and the
represented fraction. -/
theorem generator_mul_crossRelationFraction (d : ι → R) (i₀ i : ι)
    (x : crossRelations d) :
    algebraMap R (Localization.Away (d i₀)) (d i) * crossRelationFraction d i₀ x =
      algebraMap R (Localization.Away (d i₀)) ((x : ι → R) i) := by
  rw [crossRelationFraction_apply, ← mul_assoc, ← map_mul,
    (mem_crossRelations d x).mp x.property i i₀, map_mul, mul_assoc,
    mul_left_comm, IsLocalization.Away.mul_invSelf, mul_one]

/-- The fraction map retains the original scalar vectors. -/
theorem crossRelationFraction_scalars (d : ι → R) (i₀ : ι) (r : R) :
    crossRelationFraction d i₀ (crossRelationScalars d r) =
      algebraMap R (Localization.Away (d i₀)) r := by
  rw [crossRelationFraction_apply, crossRelationScalars_apply, map_mul,
    mul_assoc, IsLocalization.Away.mul_invSelf, mul_one]

/-- A regular denominator coordinate makes the represented fraction
determine every original coordinate. -/
theorem crossRelationFraction_injective (d : ι → R) (i₀ : ι)
    (hreg : IsSMulRegular R (d i₀)) : Function.Injective (crossRelationFraction d i₀) := by
  intro x y h
  apply Subtype.ext
  funext i
  have he : algebraMap R (Localization.Away (d i₀)) ((x : ι → R) i) =
      algebraMap R (Localization.Away (d i₀)) ((y : ι → R) i) := by
    rw [← generator_mul_crossRelationFraction d i₀ i x,
      ← generator_mul_crossRelationFraction d i₀ i y, h]
  obtain ⟨n, hn⟩ := IsLocalization.Away.exists_of_eq (x := d i₀) he
  exact IsSMulRegular.pow n hreg hn

/-- The actual image consists exactly of fractions whose products by all
specified generators are original scalars. -/
theorem mem_crossRelationFraction_range_iff (d : ι → R) (i₀ : ι)
    (hreg : IsSMulRegular R (d i₀)) (z : Localization.Away (d i₀)) :
    z ∈ (crossRelationFraction d i₀).range ↔
      ∀ i : ι, ∃ r : R, algebraMap R (Localization.Away (d i₀)) r =
        algebraMap R (Localization.Away (d i₀)) (d i) * z := by
  constructor
  · rintro ⟨x, rfl⟩ i
    exact ⟨(x : ι → R) i, (generator_mul_crossRelationFraction d i₀ i x).symm⟩
  · intro h
    choose x hx using h
    have hcross : x ∈ crossRelations d := by
      apply (mem_crossRelations d x).mpr
      intro i j
      have he : algebraMap R (Localization.Away (d i₀)) (d i * x j) =
          algebraMap R (Localization.Away (d i₀)) (d j * x i) := by
        rw [map_mul, map_mul, hx, hx]
        exact mul_left_comm _ _ _
      obtain ⟨n, hn⟩ := IsLocalization.Away.exists_of_eq (x := d i₀) he
      exact IsSMulRegular.pow n hreg hn
    refine ⟨⟨x, hcross⟩, ?_⟩
    change algebraMap R (Localization.Away (d i₀)) (x i₀) *
      IsLocalization.Away.invSelf (d i₀) = z
    rw [hx, mul_assoc, mul_left_comm, IsLocalization.Away.mul_invSelf, mul_one]

section BaseChange

variable [Fintype ι] [DecidableEq ι] [Module.Flat R S]

/-- Fraction representation commutes with the actual coordinate base-change
map on the original unit tensors. -/
theorem crossRelationFraction_baseChange (d : ι → R) (i₀ : ι)
    (x : crossRelations d) :
    crossRelationFraction (fun i => algebraMap R S (d i)) i₀
        (crossRelationsTensorEquiv (S := S) d ((1 : S) ⊗ₜ[R] x)) =
      localizationBaseMap (S := S) (d i₀) (crossRelationFraction d i₀ x) := by
  apply (IsLocalization.Away.algebraMap_isUnit
    (S := Localization.Away (algebraMap R S (d i₀))) (algebraMap R S (d i₀))).mul_left_cancel
  rw [generator_mul_crossRelationFraction (fun i => algebraMap R S (d i)) i₀ i₀
    (crossRelationsTensorEquiv (S := S) d ((1 : S) ⊗ₜ[R] x))]
  calc
    algebraMap S (Localization.Away (algebraMap R S (d i₀)))
        ((crossRelationsTensorEquiv (S := S) d ((1 : S) ⊗ₜ[R] x) : ι → S) i₀) =
        algebraMap S (Localization.Away (algebraMap R S (d i₀)))
          (algebraMap R S ((x : ι → R) i₀)) := by
      rw [crossRelationsTensorEquiv_tmul, mul_one]
    _ = localizationBaseMap (S := S) (d i₀)
        (algebraMap R (Localization.Away (d i₀)) ((x : ι → R) i₀)) :=
      (localizationBaseMap_algebraMap (d i₀) ((x : ι → R) i₀)).symm
    _ = localizationBaseMap (S := S) (d i₀)
        (algebraMap R (Localization.Away (d i₀)) (d i₀) *
          crossRelationFraction d i₀ x) :=
      congrArg (localizationBaseMap (S := S) (d i₀))
        (generator_mul_crossRelationFraction d i₀ i₀ x).symm
    _ = algebraMap S (Localization.Away (algebraMap R S (d i₀)))
          (algebraMap R S (d i₀)) *
        localizationBaseMap (S := S) (d i₀) (crossRelationFraction d i₀ x) := by
      rw [map_mul, localizationBaseMap_algebraMap]

end BaseChange

section Conductor

variable {D : Type*} [CommRing D] [Algebra R D]

/-- The cross-relation coordinates and the actual conductor localization
map represent the same fraction. -/
theorem crossRelationFraction_conductorMap (d : ι → R) (i₀ : ι)
    (hinj : Function.Injective (algebraMap R D))
    (hcond : ∀ i : ι, ∀ z : D, ∃ r : R, algebraMap R D r = d i • z) (z : D) :
    crossRelationFraction d i₀ (conductorMap d hinj hcond z) =
      conductorLocalizationMap (d i₀) hinj (hcond i₀) z := by
  let j := conductorLocalizationMap (d i₀) hinj (hcond i₀)
  apply (IsLocalization.Away.algebraMap_isUnit
    (S := Localization.Away (d i₀)) (d i₀)).mul_left_cancel
  rw [generator_mul_crossRelationFraction, conductorMap_apply]
  calc
    algebraMap R (Localization.Away (d i₀)) (conductorCoordinate d hinj hcond i₀ z) =
        j (algebraMap R D (conductorCoordinate d hinj hcond i₀ z)) :=
      (j.commutes _).symm
    _ = j (d i₀ • z) := congrArg j (algebraMap_conductorCoordinate d hinj hcond i₀ z)
    _ = d i₀ • j z := j.toLinearMap.map_smul (d i₀) z
    _ = algebraMap R (Localization.Away (d i₀)) (d i₀) * j z := Algebra.smul_def _ _

end Conductor

end FractionalKernel

section RegularConductorEffectivity

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  {D : Type*} [CommRing D] [Algebra R D] [Algebra S D] [IsScalarTower R S D]

section Flat

variable [Module.Flat R S]

omit [Algebra R D] [IsScalarTower R S D] in
/-- The actual conductor image inside the original tensor ambient, using
the coordinate base-change equivalence rather than an abstract model. -/
def conductorTensorSubmodule (d : ι → R)
    (hinj : Function.Injective (algebraMap S D))
    (hcond : ∀ i : ι, ∀ z : D, ∃ s : S, algebraMap S D s = algebraMap R S (d i) • z) :
    Submodule S (S ⊗[R] crossRelations d) :=
  (conductorMap (fun i => algebraMap R S (d i)) hinj hcond).range.comap
    (crossRelationsTensorEquiv (S := S) d).toLinearMap

omit [Algebra R D] [IsScalarTower R S D] in
/-- The source ideal generated by the conductor coefficients gives the
actual bounded-cokernel hypothesis for the constructed tensor submodule. -/
theorem span_smul_top_le_conductorTensorSubmodule (d : ι → R)
    (hinj : Function.Injective (algebraMap S D))
    (hcond : ∀ i : ι, ∀ z : D, ∃ s : S, algebraMap S D s = algebraMap R S (d i) • z) :
    (Ideal.span (Set.range d)).map (algebraMap R S) •
      (⊤ : Submodule S (S ⊗[R] crossRelations d)) ≤ conductorTensorSubmodule d hinj hcond := by
  have hspan : (Ideal.span (Set.range d)).map (algebraMap R S) =
      Ideal.span (Set.range (fun i => algebraMap R S (d i))) := by
    rw [Ideal.map_span, ← Set.range_comp]
    rfl
  apply Submodule.smul_le.mpr
  intro s hs x _
  change crossRelationsTensorEquiv (S := S) d (s • x) ∈
    (conductorMap (fun i => algebraMap R S (d i)) hinj hcond).range
  rw [map_smul]
  apply span_smul_top_le_conductorMap_range (fun i => algebraMap R S (d i)) hinj hcond
  exact Submodule.smul_mem_smul (hspan ▸ hs)
    (Submodule.mem_top : crossRelationsTensorEquiv (S := S) d x ∈
      (⊤ : Submodule S (crossRelations (fun i => algebraMap R S (d i)))))

omit [Algebra R D] [IsScalarTower R S D] in
/-- The original-unit inverse image in the finite cross-relation kernel. -/
abbrev regularConductorKernel (d : ι → R)
    (hinj : Function.Injective (algebraMap S D))
    (hcond : ∀ i : ι, ∀ z : D, ∃ s : S, algebraMap S D s = algebraMap R S (d i) • z) :
    Submodule R (crossRelations d) :=
  unitPreimage (conductorTensorSubmodule d hinj hcond)

/-- A vector in the original-unit preimage represents an element of the
actual localization-intersection algebra. -/
theorem crossRelationFraction_mem_regularConductorSubalgebra
    (d : ι → R) (i₀ : ι) (hinj : Function.Injective (algebraMap S D))
    (hcond : ∀ i : ι, ∀ z : D, ∃ s : S, algebraMap S D s = algebraMap R S (d i) • z)
    (x : regularConductorKernel d hinj hcond) :
    crossRelationFraction d i₀ x ∈ regularConductorSubalgebra (d i₀) hinj (hcond i₀) := by
  obtain ⟨z, hz⟩ := x.property
  change ∃ z : D, conductorLocalizationMap (algebraMap R S (d i₀)) hinj (hcond i₀) z =
    localizationBaseMap (S := S) (d i₀) (crossRelationFraction d i₀ x)
  refine ⟨z, ?_⟩
  change conductorMap (fun i => algebraMap R S (d i)) hinj hcond z =
    crossRelationsTensorEquiv (S := S) d ((1 : S) ⊗ₜ[R] (x : crossRelations d)) at hz
  calc
    conductorLocalizationMap (algebraMap R S (d i₀)) hinj (hcond i₀) z =
        crossRelationFraction (fun i => algebraMap R S (d i)) i₀
          (conductorMap (fun i => algebraMap R S (d i)) hinj hcond z) :=
      (crossRelationFraction_conductorMap (fun i => algebraMap R S (d i)) i₀
        hinj hcond z).symm
    _ = crossRelationFraction (fun i => algebraMap R S (d i)) i₀
        (crossRelationsTensorEquiv (S := S) d ((1 : S) ⊗ₜ[R] (x : crossRelations d))) :=
      congrArg (crossRelationFraction (fun i => algebraMap R S (d i)) i₀) hz
    _ = _ := crossRelationFraction_baseChange d i₀ (x : crossRelations d)

/-- The original fraction map sends the constructed kernel into the actual
localization-intersection algebra. No ring operations are transported. -/
def regularConductorKernelMap (d : ι → R) (i₀ : ι)
    (hinj : Function.Injective (algebraMap S D))
    (hcond : ∀ i : ι, ∀ z : D, ∃ s : S, algebraMap S D s = algebraMap R S (d i) • z) :
    regularConductorKernel d hinj hcond →ₗ[R]
      regularConductorSubalgebra (d i₀) hinj (hcond i₀) where
  toFun x := ⟨crossRelationFraction d i₀ x,
    crossRelationFraction_mem_regularConductorSubalgebra d i₀ hinj hcond x⟩
  map_add' x y := Subtype.ext ((crossRelationFraction d i₀).map_add x y)
  map_smul' r x := Subtype.ext ((crossRelationFraction d i₀).map_smul r x)

@[simp]
theorem regularConductorKernelMap_coe (d : ι → R) (i₀ : ι)
    (hinj : Function.Injective (algebraMap S D))
    (hcond : ∀ i : ι, ∀ z : D, ∃ s : S, algebraMap S D s = algebraMap R S (d i) • z)
    (x : regularConductorKernel d hinj hcond) :
    (regularConductorKernelMap d i₀ hinj hcond x : Localization.Away (d i₀)) =
      crossRelationFraction d i₀ x := rfl

end Flat

variable [Module.FaithfullyFlat R S]

omit [Fintype ι] [DecidableEq ι] in
/-- Each actual conductor product of an element of the intersection
algebra is an original scalar, by faithful-flat principal membership. -/
theorem regularConductorSubalgebra_generator_mul (d : ι → R) (i₀ : ι)
    (hinj : Function.Injective (algebraMap S D))
    (hcond : ∀ i : ι, ∀ z : D, ∃ s : S, algebraMap S D s = algebraMap R S (d i) • z)
    (hreg : IsSMulRegular R (d i₀))
    (hregD : IsSMulRegular D (algebraMap R S (d i₀)))
    (z : regularConductorSubalgebra (d i₀) hinj (hcond i₀)) (i : ι) :
    ∃ r : R, algebraMap R (Localization.Away (d i₀)) r =
      algebraMap R (Localization.Away (d i₀)) (d i) * (z : Localization.Away (d i₀)) := by
  let ψ := regularConductorMap (d i₀) hinj (hcond i₀) hregD
  let j := conductorLocalizationMap (algebraMap R S (d i₀)) hinj (hcond i₀)
  obtain ⟨s, hs⟩ := hcond i (ψ z)
  have he : localizationBaseMap (S := S) (d i₀)
      (algebraMap R (Localization.Away (d i₀)) (d i) * (z : Localization.Away (d i₀))) =
      algebraMap S (Localization.Away (algebraMap R S (d i₀))) s := by
    rw [map_mul, localizationBaseMap_algebraMap,
      ← regularConductorMap_localization (d i₀) hinj (hcond i₀) hregD z]
    change algebraMap S (Localization.Away (algebraMap R S (d i₀)))
      (algebraMap R S (d i)) * j (ψ z) = _
    calc
      _ = algebraMap R S (d i) • j (ψ z) :=
        (Algebra.smul_def (algebraMap R S (d i)) (j (ψ z))).symm
      _ = j (algebraMap R S (d i) • ψ z) := (j.toLinearMap.map_smul _ _).symm
      _ = j (algebraMap S D s) := congrArg j hs.symm
      _ = _ := j.commutes s
  obtain ⟨r, hr⟩ := exists_scalar_of_localizationBaseMap (d i₀) hreg _ s he
  exact ⟨r, hr.symm⟩

/-- Every element of the actual intersection subalgebra is the fraction
of a vector in the original-unit preimage; no algebra-model premise occurs. -/
theorem regularConductorKernelMap_bijective (d : ι → R) (i₀ : ι)
    (hinj : Function.Injective (algebraMap S D))
    (hcond : ∀ i : ι, ∀ z : D, ∃ s : S, algebraMap S D s = algebraMap R S (d i) • z)
    (hreg : IsSMulRegular R (d i₀))
    (hregD : IsSMulRegular D (algebraMap R S (d i₀))) :
    Function.Bijective (regularConductorKernelMap d i₀ hinj hcond) := by
  constructor
  · intro x y h
    apply Subtype.ext
    apply crossRelationFraction_injective d i₀ hreg
    exact congrArg Subtype.val h
  · intro z
    obtain ⟨x, hx⟩ := (mem_crossRelationFraction_range_iff d i₀ hreg z).mpr
      (regularConductorSubalgebra_generator_mul d i₀ hinj hcond hreg hregD z)
    have hcross : crossRelationsTensorEquiv (S := S) d ((1 : S) ⊗ₜ[R] x) =
        conductorMap (fun i => algebraMap R S (d i)) hinj hcond
          (regularConductorMap (d i₀) hinj (hcond i₀) hregD z) := by
      apply crossRelationFraction_injective (fun i => algebraMap R S (d i)) i₀ hreg.of_flat
      rw [crossRelationFraction_baseChange, hx, crossRelationFraction_conductorMap,
        regularConductorMap_localization]
    have hxQ : x ∈ regularConductorKernel d hinj hcond :=
      ⟨regularConductorMap (d i₀) hinj (hcond i₀) hregD z, hcross.symm⟩
    exact ⟨⟨x, hxQ⟩, Subtype.ext hx⟩

/-- The actual underlying module of the intersection algebra is precisely
the finite original-unit preimage in the cross-relation kernel. -/
def regularConductorKernelEquiv (d : ι → R) (i₀ : ι)
    (hinj : Function.Injective (algebraMap S D))
    (hcond : ∀ i : ι, ∀ z : D, ∃ s : S, algebraMap S D s = algebraMap R S (d i) • z)
    (hreg : IsSMulRegular R (d i₀))
    (hregD : IsSMulRegular D (algebraMap R S (d i₀))) :
    regularConductorKernel d hinj hcond ≃ₗ[R]
      regularConductorSubalgebra (d i₀) hinj (hcond i₀) :=
  LinearEquiv.ofBijective (regularConductorKernelMap d i₀ hinj hcond)
    (regularConductorKernelMap_bijective d i₀ hinj hcond hreg hregD)

@[simp]
theorem regularConductorKernelEquiv_coe (d : ι → R) (i₀ : ι)
    (hinj : Function.Injective (algebraMap S D))
    (hcond : ∀ i : ι, ∀ z : D, ∃ s : S, algebraMap S D s = algebraMap R S (d i) • z)
    (hreg : IsSMulRegular R (d i₀))
    (hregD : IsSMulRegular D (algebraMap R S (d i₀)))
    (x : regularConductorKernel d hinj hcond) :
    (regularConductorKernelEquiv d i₀ hinj hcond hreg hregD x : Localization.Away (d i₀)) =
      crossRelationFraction d i₀ x := by
  change (regularConductorKernelMap d i₀ hinj hcond x : Localization.Away (d i₀)) = _
  rfl

omit [Fintype ι] [DecidableEq ι] in
/-- The actual intersection subalgebra is finite over the Noetherian
source, through its original fraction module, without a finite-model premise. -/
theorem finite_regularConductorSubalgebra [Finite ι] [IsNoetherianRing R]
    (d : ι → R) (i₀ : ι) (hinj : Function.Injective (algebraMap S D))
    (hcond : ∀ i : ι, ∀ z : D, ∃ s : S, algebraMap S D s = algebraMap R S (d i) • z)
    (hreg : IsSMulRegular R (d i₀))
    (hregD : IsSMulRegular D (algebraMap R S (d i₀))) :
    Module.Finite R (regularConductorSubalgebra (d i₀) hinj (hcond i₀)) := by
  classical
  let : Fintype ι := Fintype.ofFinite ι
  let : Module.Finite R (crossRelations d) := finite_crossRelations d
  let : Module.Finite R (regularConductorKernel d hinj hcond) :=
    finite_unitPreimage (conductorTensorSubmodule d hinj hcond)
  exact Module.Finite.equiv (regularConductorKernelEquiv d i₀ hinj hcond hreg hregD)

omit [Algebra R D] [IsScalarTower R S D] in
/-- The given algebra, as a module, is the actual conductor range pulled
back through the coordinate base-change equivalence. -/
def conductorTensorRangeEquiv (d : ι → R) (i₀ : ι)
    (hinj : Function.Injective (algebraMap S D))
    (hcond : ∀ i : ι, ∀ z : D, ∃ s : S, algebraMap S D s = algebraMap R S (d i) • z)
    (hregD : IsSMulRegular D (algebraMap R S (d i₀))) :
    conductorTensorSubmodule d hinj hcond ≃ₗ[S] D :=
  ((crossRelationsTensorEquiv (S := S) d).ofSubmodule'
    (conductorMap (fun i => algebraMap R S (d i)) hinj hcond).range).trans
      (LinearEquiv.ofInjective (conductorMap (fun i => algebraMap R S (d i)) hinj hcond)
        (conductorMap_injective _ hinj hcond i₀ hregD)).symm

omit [Algebra R D] [IsScalarTower R S D] in
private theorem conductorTensorRangeEquiv_apply (d : ι → R) (i₀ : ι)
    (hinj : Function.Injective (algebraMap S D))
    (hcond : ∀ i : ι, ∀ z : D, ∃ s : S, algebraMap S D s = algebraMap R S (d i) • z)
    (hregD : IsSMulRegular D (algebraMap R S (d i₀)))
    (x : conductorTensorSubmodule d hinj hcond) :
    conductorMap (fun i => algebraMap R S (d i)) hinj hcond
        (conductorTensorRangeEquiv d i₀ hinj hcond hregD x) =
      crossRelationsTensorEquiv (S := S) d x := by
  exact LinearEquiv.ofInjective_symm_apply _
    (h := conductorMap_injective (fun i => algebraMap R S (d i)) hinj hcond i₀ hregD)
    ((crossRelationsTensorEquiv (S := S) d).ofSubmodule'
      (conductorMap (fun i => algebraMap R S (d i)) hinj hcond).range x)

omit [Algebra R D] [IsScalarTower R S D] in
/-- The constructed kernel recovers the original algebra as an actual
scalar-extended module, using only source-ideal coefficient approximation. -/
def regularConductorKernelTensorEquiv (d : ι → R) (i₀ : ι)
    (hinj : Function.Injective (algebraMap S D))
    (hcond : ∀ i : ι, ∀ z : D, ∃ s : S, algebraMap S D s = algebraMap R S (d i) • z)
    (hregD : IsSMulRegular D (algebraMap R S (d i₀)))
    (hcoeff : Function.Surjective ((Ideal.Quotient.mk
      ((Ideal.span (Set.range d)).map (algebraMap R S))).comp (algebraMap R S))) :
    S ⊗[R] regularConductorKernel d hinj hcond ≃ₗ[S] D :=
  (unitPreimageTensorEquiv (Ideal.span (Set.range d)) hcoeff
    (conductorTensorSubmodule d hinj hcond)
    (span_smul_top_le_conductorTensorSubmodule d hinj hcond)).trans
      (conductorTensorRangeEquiv d i₀ hinj hcond hregD)

omit [Algebra R D] [IsScalarTower R S D] in
private theorem regularConductorKernelTensorEquiv_conductor (d : ι → R) (i₀ : ι)
    (hinj : Function.Injective (algebraMap S D))
    (hcond : ∀ i : ι, ∀ z : D, ∃ s : S, algebraMap S D s = algebraMap R S (d i) • z)
    (hregD : IsSMulRegular D (algebraMap R S (d i₀)))
    (hcoeff : Function.Surjective ((Ideal.Quotient.mk
      ((Ideal.span (Set.range d)).map (algebraMap R S))).comp (algebraMap R S)))
    (s : S) (x : regularConductorKernel d hinj hcond) :
    conductorMap (fun i => algebraMap R S (d i)) hinj hcond
        (regularConductorKernelTensorEquiv d i₀ hinj hcond hregD hcoeff (s ⊗ₜ[R] x)) =
      crossRelationsTensorEquiv (S := S) d (s ⊗ₜ[R] (x : crossRelations d)) := by
  have h := conductorTensorRangeEquiv_apply d i₀ hinj hcond hregD
    (unitPreimageTensorEquiv (Ideal.span (Set.range d)) hcoeff
      (conductorTensorSubmodule d hinj hcond)
      (span_smul_top_le_conductorTensorSubmodule d hinj hcond) (s ⊗ₜ[R] x))
  rw [unitPreimageTensorEquiv_tmul] at h
  exact h

/-- On every original pure tensor, the constructed module equivalence
agrees with the original algebra map on the represented fraction. -/
theorem regularConductorKernelTensorEquiv_tmul (d : ι → R) (i₀ : ι)
    (hinj : Function.Injective (algebraMap S D))
    (hcond : ∀ i : ι, ∀ z : D, ∃ s : S, algebraMap S D s = algebraMap R S (d i) • z)
    (hreg : IsSMulRegular R (d i₀))
    (hregD : IsSMulRegular D (algebraMap R S (d i₀)))
    (hcoeff : Function.Surjective ((Ideal.Quotient.mk
      ((Ideal.span (Set.range d)).map (algebraMap R S))).comp (algebraMap R S)))
    (s : S) (x : regularConductorKernel d hinj hcond) :
    regularConductorKernelTensorEquiv d i₀ hinj hcond hregD hcoeff (s ⊗ₜ[R] x) =
      s • regularConductorMap (d i₀) hinj (hcond i₀) hregD
        (regularConductorKernelEquiv d i₀ hinj hcond hreg hregD x) := by
  have hone : regularConductorKernelTensorEquiv d i₀ hinj hcond hregD hcoeff
        ((1 : S) ⊗ₜ[R] x) =
      regularConductorMap (d i₀) hinj (hcond i₀) hregD
        (regularConductorKernelEquiv d i₀ hinj hcond hreg hregD x) := by
    apply conductorLocalizationMap_injective (algebraMap R S (d i₀)) hinj (hcond i₀) hregD
    rw [← crossRelationFraction_conductorMap (fun i => algebraMap R S (d i)) i₀ hinj hcond,
      regularConductorKernelTensorEquiv_conductor, crossRelationFraction_baseChange,
      regularConductorMap_localization, regularConductorKernelEquiv_coe]
  calc
    regularConductorKernelTensorEquiv d i₀ hinj hcond hregD hcoeff (s ⊗ₜ[R] x) =
        s • regularConductorKernelTensorEquiv d i₀ hinj hcond hregD hcoeff
          ((1 : S) ⊗ₜ[R] x) := by
      rw [← map_smul]
      congr 1
      simp only [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    _ = _ := congrArg (fun z : D => s • z) hone

omit [Fintype ι] [DecidableEq ι] in
/-- The original tensor algebra map is bijective: its underlying linear
map is the constructed kernel equivalence, with the exact pure-tensor formula. -/
theorem regularConductorBaseChange_bijective [Finite ι] (d : ι → R) (i₀ : ι)
    (hinj : Function.Injective (algebraMap S D))
    (hcond : ∀ i : ι, ∀ z : D, ∃ s : S, algebraMap S D s = algebraMap R S (d i) • z)
    (hreg : IsSMulRegular R (d i₀))
    (hregD : IsSMulRegular D (algebraMap R S (d i₀)))
    (hcoeff : Function.Surjective ((Ideal.Quotient.mk
      ((Ideal.span (Set.range d)).map (algebraMap R S))).comp (algebraMap R S))) :
    Function.Bijective (regularConductorBaseChange (d i₀) hinj (hcond i₀) hregD) := by
  classical
  let : Fintype ι := Fintype.ofFinite ι
  let e := regularConductorKernelEquiv d i₀ hinj hcond hreg hregD
  let eS := AlgebraTensorModule.congr (LinearEquiv.refl S S) e.symm
  let θ := eS.trans (regularConductorKernelTensorEquiv d i₀ hinj hcond hregD hcoeff)
  have heq : (regularConductorBaseChange (d i₀) hinj (hcond i₀) hregD).toLinearMap =
      θ.toLinearMap := by
    apply AlgebraTensorModule.ext
    intro s z
    change regularConductorBaseChange (d i₀) hinj (hcond i₀) hregD (s ⊗ₜ[R] z) =
      regularConductorKernelTensorEquiv d i₀ hinj hcond hregD hcoeff
        (s ⊗ₜ[R] e.symm z)
    rw [regularConductorBaseChange_tmul,
      regularConductorKernelTensorEquiv_tmul d i₀ hinj hcond hreg hregD hcoeff]
    exact congrArg (fun x => s • regularConductorMap (d i₀) hinj (hcond i₀) hregD x)
      (e.apply_symm_apply z).symm
  change Function.Bijective (regularConductorBaseChange (d i₀) hinj (hcond i₀) hregD).toLinearMap
  rw [heq]
  exact θ.bijective

/-- Regular-conductor algebra effectivity for the actual localization
intersection. The equivalence is the original tensor algebra map, so it
retains multiplication, unit and the original structural homomorphism. -/
def regularConductorAlgEquiv (d : ι → R) (i₀ : ι)
    (hinj : Function.Injective (algebraMap S D))
    (hcond : ∀ i : ι, ∀ z : D, ∃ s : S, algebraMap S D s = algebraMap R S (d i) • z)
    (hreg : IsSMulRegular R (d i₀))
    (hregD : IsSMulRegular D (algebraMap R S (d i₀)))
    (hcoeff : Function.Surjective ((Ideal.Quotient.mk
      ((Ideal.span (Set.range d)).map (algebraMap R S))).comp (algebraMap R S))) :
    S ⊗[R] regularConductorSubalgebra (d i₀) hinj (hcond i₀) ≃ₐ[S] D :=
  AlgEquiv.ofBijective (regularConductorBaseChange (d i₀) hinj (hcond i₀) hregD)
    (regularConductorBaseChange_bijective d i₀ hinj hcond hreg hregD hcoeff)

omit [DecidableEq ι] in
@[simp]
theorem regularConductorAlgEquiv_tmul (d : ι → R) (i₀ : ι)
    (hinj : Function.Injective (algebraMap S D))
    (hcond : ∀ i : ι, ∀ z : D, ∃ s : S, algebraMap S D s = algebraMap R S (d i) • z)
    (hreg : IsSMulRegular R (d i₀))
    (hregD : IsSMulRegular D (algebraMap R S (d i₀)))
    (hcoeff : Function.Surjective ((Ideal.Quotient.mk
      ((Ideal.span (Set.range d)).map (algebraMap R S))).comp (algebraMap R S)))
    (s : S) (z : regularConductorSubalgebra (d i₀) hinj (hcond i₀)) :
    regularConductorAlgEquiv d i₀ hinj hcond hreg hregD hcoeff (s ⊗ₜ[R] z) =
      algebraMap S D s * regularConductorMap (d i₀) hinj (hcond i₀) hregD z := by
  change regularConductorBaseChange (d i₀) hinj (hcond i₀) hregD (s ⊗ₜ[R] z) = _
  rw [regularConductorBaseChange_tmul, Algebra.smul_def]

end RegularConductorEffectivity

section PuncturedLocalization

variable {D : Type*} [CommRing D]
  [Algebra R D] [Algebra S D] [IsScalarTower R S D]
  [Module.FaithfullyFlat R S] {ι : Type*}

/-- The original generated conductor ideal multiplies the actual model into
its original scalar image. This is stronger than support agreement. -/
theorem regularConductorSubalgebra_conductor (d : ι → R) (i₀ : ι)
    (hinj : Function.Injective (algebraMap S D))
    (hcond : ∀ i : ι, ∀ z : D, ∃ s : S, algebraMap S D s = algebraMap R S (d i) • z)
    (hreg : IsSMulRegular R (d i₀))
    (hregD : IsSMulRegular D (algebraMap R S (d i₀)))
    (r : R) (hr : r ∈ Ideal.span (Set.range d))
    (z : regularConductorSubalgebra (d i₀) hinj (hcond i₀)) :
    ∃ b : R, algebraMap R (regularConductorSubalgebra (d i₀) hinj (hcond i₀)) b = r • z := by
  let E := regularConductorSubalgebra (d i₀) hinj (hcond i₀)
  have hm : r • z ∈ (Algebra.linearMap R E).range := by
    induction hr using Submodule.span_induction with
    | mem a ha =>
        obtain ⟨i, rfl⟩ := ha
        obtain ⟨b, hb⟩ :=
          regularConductorSubalgebra_generator_mul d i₀ hinj hcond hreg hregD z i
        refine ⟨b, ?_⟩
        apply Subtype.ext
        calc
          ((Algebra.linearMap R E) b : Localization.Away (d i₀)) =
              algebraMap R (Localization.Away (d i₀)) b := E.val.commutes b
          _ = algebraMap R (Localization.Away (d i₀)) (d i) * z := hb
          _ = d i • (z : Localization.Away (d i₀)) := (Algebra.smul_def _ _).symm
          _ = (d i • z : E) := (E.val.toLinearMap.map_smul (d i) z).symm
    | zero => simpa only [zero_smul] using (Algebra.linearMap R E).range.zero_mem
    | add a b _ _ ha hb =>
        simpa only [add_smul] using (Algebra.linearMap R E).range.add_mem ha hb
    | smul a b _ hb =>
        simpa only [smul_smul, smul_eq_mul] using (Algebra.linearMap R E).range.smul_mem a hb
  exact hm

omit [Module.FaithfullyFlat R S] in
/-- The actual structural map to the subalgebra inside R[1/t] is injective
when t is regular on R. No field or domain structure on the target is used. -/
theorem regularConductorSubalgebra_algebraMap_injective (d : ι → R) (i₀ : ι)
    (hinj : Function.Injective (algebraMap S D))
    (hcond : ∀ i : ι, ∀ z : D, ∃ s : S, algebraMap S D s = algebraMap R S (d i) • z)
    (hreg : IsSMulRegular R (d i₀)) :
    Function.Injective (algebraMap R (regularConductorSubalgebra (d i₀) hinj (hcond i₀))) := by
  intro a b hab
  have he : algebraMap R (Localization.Away (d i₀)) a =
      algebraMap R (Localization.Away (d i₀)) b := congrArg Subtype.val hab
  obtain ⟨n, hn⟩ := IsLocalization.Away.exists_of_eq (x := d i₀) he
  exact IsSMulRegular.pow n hreg hn

/-- Inverting an element whose power belongs to the original conductor
makes the original scalar map an isomorphism on the two actual localizations. -/
def regularConductorAwayEquiv (d : ι → R) (i₀ : ι)
    (hinj : Function.Injective (algebraMap S D))
    (hcond : ∀ i : ι, ∀ z : D, ∃ s : S, algebraMap S D s = algebraMap R S (d i) • z)
    (hreg : IsSMulRegular R (d i₀))
    (hregD : IsSMulRegular D (algebraMap R S (d i₀)))
    (f : R) (n : ℕ) (hfn : f ^ n ∈ Ideal.span (Set.range d)) :
    Localization.Away f ≃ₐ[R]
      Localization.Away (algebraMap R (regularConductorSubalgebra (d i₀) hinj (hcond i₀)) f) := by
  let E := regularConductorSubalgebra (d i₀) hinj (hcond i₀)
  apply AlgEquiv.ofBijective (localizationBaseMap (S := E) f)
  constructor
  · change Function.Injective (Localization.awayMap (algebraMap R E) f)
    apply Localization.awayMap_injective_iff.mpr
    intro x hx
    have hx0 : x = 0 :=
      regularConductorSubalgebra_algebraMap_injective d i₀ hinj hcond hreg
        (by simpa only [map_zero] using hx)
    exact ⟨0, by simpa only [pow_zero, one_mul] using hx0⟩
  · change Function.Surjective (Localization.awayMap (algebraMap R E) f)
    apply Localization.awayMap_surjective_iff.mpr
    intro z
    obtain ⟨b, hb⟩ :=
      regularConductorSubalgebra_conductor d i₀ hinj hcond hreg hregD (f ^ n) hfn z
    exact ⟨b, n, by simpa only [Algebra.smul_def, map_pow] using hb⟩

theorem regularConductorAwayEquiv_algebraMap (d : ι → R) (i₀ : ι)
    (hinj : Function.Injective (algebraMap S D))
    (hcond : ∀ i : ι, ∀ z : D, ∃ s : S, algebraMap S D s = algebraMap R S (d i) • z)
    (hreg : IsSMulRegular R (d i₀))
    (hregD : IsSMulRegular D (algebraMap R S (d i₀)))
    (f : R) (n : ℕ) (hfn : f ^ n ∈ Ideal.span (Set.range d)) (r : R) :
    regularConductorAwayEquiv d i₀ hinj hcond hreg hregD f n hfn
        (algebraMap R (Localization.Away f) r) =
      algebraMap R
        (Localization.Away
          (algebraMap R (regularConductorSubalgebra (d i₀) hinj (hcond i₀)) f)) r :=
  (regularConductorAwayEquiv d i₀ hinj hcond hreg hregD f n hfn).commutes r

end PuncturedLocalization



/-- A finite generating family for the actual source conductor ideal can
retain a specified original conductor element as its zeroth coordinate. -/
theorem exists_conductorFamily (J : Ideal R) (hJ : J.FG) (t : R) (ht : t ∈ J) :
    ∃ (n : ℕ) (d : Option (Fin n) → R),
      d none = t ∧ Ideal.span (Set.range d) = J := by
  obtain ⟨n, g, hg⟩ := Submodule.fg_iff_exists_fin_generating_family.mp hJ
  change Ideal.span (Set.range g) = J at hg
  let d : Option (Fin n) → R := Option.elim' t g
  refine ⟨n, d, rfl, le_antisymm ?_ ?_⟩
  · apply Ideal.span_le.mpr
    rintro _ ⟨i, rfl⟩
    cases i with
    | none => exact ht
    | some i =>
        have hi : g i ∈ Ideal.span (Set.range g) := Ideal.subset_span ⟨i, rfl⟩
        rw [hg] at hi
        exact hi
  · rw [← hg]
    apply Ideal.span_mono
    rintro _ ⟨i, rfl⟩
    exact ⟨some i, rfl⟩

end Algebra.Descent.FormalGluing
