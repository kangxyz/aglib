/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.RingTheory.TensorProduct.Maps
public import Mathlib.RingTheory.Flat.CategoryTheory
public import Mathlib.RingTheory.RingHom.Flat

/-!
# External tensor modules and their base change

The carrier is the original tensor product over the common base ring.
The tensor-algebra action is the native `TensorProduct.Algebra.module`
applied to the original left action and the original right tensor map.
No ambiguous tensor-algebra action is installed as a global instance.
-/

@[expose] public noncomputable section

open scoped TensorProduct

namespace TensorProduct.External

variable (R B M N : Type*) [CommRing R] [CommRing B] [Algebra R B]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] [Module B N]
  [IsScalarTower R B N]

/-- The original action on the second tensor factor, using the native
endomorphism tensor map and the original scalar representation. -/
@[instance_reducible]
def rightModule : Module B (M ⊗[R] N) :=
  Module.compHom (M ⊗[R] N)
    (((Module.End.lTensorAlgHom R N M).comp (Algebra.lsmul R R N :
      B →ₐ[R] Module.End R N)).toRingHom)

/-- The right action is exactly the original action on the second factor. -/
theorem rightModule_smul_tmul (b : B) (m : M) (n : N) :
    letI := rightModule R B M N
    b • (m ⊗ₜ[R] n) = m ⊗ₜ[R] (b • n) := rfl

/-- The right tensor action retains the original base-ring action. -/
theorem rightModule_isScalarTower :
    letI := rightModule R B M N
    IsScalarTower R B (M ⊗[R] N) := by
  let := rightModule R B M N
  refine ⟨fun r b t => ?_⟩
  induction t using TensorProduct.inductionOn with
  | tmul m n =>
    change m ⊗ₜ[R] ((r • b) • n) = r • (m ⊗ₜ[R] (b • n))
    rw [smul_assoc, TensorProduct.tmul_smul]
  | add x y hx hy => simp only [smul_add, hx, hy]

variable (A : Type*) [CommRing A] [Algebra R A] [Module A M] [IsScalarTower R A M]

/-- The original actions on separate tensor factors commute. -/
theorem left_right_smulCommClass :
    letI := rightModule R B M N
    SMulCommClass A B (M ⊗[R] N) := by
  let := rightModule R B M N
  refine ⟨fun a b t => ?_⟩
  induction t using TensorProduct.inductionOn with
  | tmul m n => rfl
  | add x y hx hy => simp only [smul_add, hx, hy]

/-- The canonical native tensor-algebra action on the original external
tensor module. It is intentionally not a global instance. -/
@[instance_reducible]
def module : Module (A ⊗[R] B) (M ⊗[R] N) := by
  letI := rightModule R B M N
  letI := rightModule_isScalarTower R B M N
  letI := left_right_smulCommClass R B M N A
  exact TensorProduct.Algebra.module

/-- The canonical tensor-algebra action has its original pure-tensor formula. -/
theorem module_smul_tmul (a : A) (b : B) (m : M) (n : N) :
    letI := module R B M N A
    (a ⊗ₜ[R] b) • (m ⊗ₜ[R] n) = (a • m) ⊗ₜ[R] (b • n) := rfl

/-- The native tensor-algebra action has the original base-ring scalar tower. -/
theorem module_isScalarTower :
    letI := module R B M N A
    IsScalarTower R (A ⊗[R] B) (M ⊗[R] N) := by
  let := module R B M N A
  refine ⟨fun r d t => ?_⟩
  induction d using TensorProduct.inductionOn with
  | tmul a b =>
    induction t using TensorProduct.inductionOn with
    | tmul m n =>
      change ((r • a) • m) ⊗ₜ[R] (b • n) = r • ((a • m) ⊗ₜ[R] (b • n))
      rw [smul_assoc, TensorProduct.smul_tmul']
    | add x y hx hy => simp only [smul_add, hx, hy]
  | add d e hd he => simp only [smul_add, add_smul, hd, he]

variable {R B M N A}
variable {M' N' : Type*} [AddCommGroup M'] [Module R M'] [Module A M']
  [IsScalarTower R A M'] [AddCommGroup N'] [Module R N'] [Module B N']
  [IsScalarTower R B N']

/-- The original tensor map of coefficient morphisms is linear for the
canonical native tensor-algebra action. -/
def map (f : M →ₗ[A] M') (g : N →ₗ[B] N') :
    letI := module R B M N A
    letI := module R B M' N' A
    M ⊗[R] N →ₗ[A ⊗[R] B] M' ⊗[R] N' := by
  letI := module R B M N A
  letI := module R B M' N' A
  let h := TensorProduct.map (f.restrictScalars R) (g.restrictScalars R)
  refine { toAddHom := h.toAddHom, map_smul' := ?_ }
  intro d t
  change h (d • t) = d • h t
  induction d using TensorProduct.inductionOn with
  | tmul a b =>
    induction t using TensorProduct.inductionOn with
    | tmul m n =>
      change f (a • m) ⊗ₜ[R] g (b • n) = (a • f m) ⊗ₜ[R] (b • g n)
      rw [f.map_smul, g.map_smul]
    | add x y hx hy => simp only [smul_add, map_add, hx, hy]
  | add d e hd he => simp only [add_smul, map_add, hd, he]

/-- The external coefficient map keeps the literal original tensor formula. -/
@[simp]
theorem map_tmul (f : M →ₗ[A] M') (g : N →ₗ[B] N') (m : M) (n : N) :
    map f g (m ⊗ₜ[R] n) = f m ⊗ₜ[R] g n := rfl

/-- Its underlying additive map is exactly the original tensor map. -/
theorem map_toAddHom (f : M →ₗ[A] M') (g : N →ₗ[B] N') :
    letI := module R B M N A
    letI := module R B M' N' A
    (map (R := R) f g).toAddHom =
      (TensorProduct.map (f.restrictScalars R) (g.restrictScalars R)).toAddHom := rfl

section BaseChange

variable (R A B M N)
variable (C : Type*) [CommRing C] [Algebra R C] [Algebra A C] [Algebra B C]
  [IsScalarTower R A C] [IsScalarTower R B C]

/-- The canonical tensor of the two original compatible algebra maps to C. -/
def scalarMap : A ⊗[R] B →ₐ[R] C :=
  Algebra.TensorProduct.lift (IsScalarTower.toAlgHom R A C)
    (IsScalarTower.toAlgHom R B C) (fun _ _ => Commute.all _ _)

/-- The original pair of scalar-extension units, followed by the original tensor map. -/
def unitPairing : M →ₗ[R] N →ₗ[R] (C ⊗[A] M) ⊗[C] (C ⊗[B] N) where
  toFun m :=
    { toFun n := ((1 : C) ⊗ₜ[A] m) ⊗ₜ[C] ((1 : C) ⊗ₜ[B] n)
      map_add' n n' := by simp only [TensorProduct.tmul_add]
      map_smul' r n := by
        simp only [RingHom.id_apply]
        rw [TensorProduct.tmul_smul, TensorProduct.tmul_smul] }
  map_add' m m' := by
    apply LinearMap.ext
    intro n
    change ((1 : C) ⊗ₜ[A] (m + m')) ⊗ₜ[C] ((1 : C) ⊗ₜ[B] n) =
      ((1 : C) ⊗ₜ[A] m) ⊗ₜ[C] ((1 : C) ⊗ₜ[B] n) + ((1 : C) ⊗ₜ[A] m') ⊗ₜ[C] ((1 : C) ⊗ₜ[B] n)
    simp only [TensorProduct.tmul_add, TensorProduct.add_tmul]
  map_smul' r m := by
    apply LinearMap.ext
    intro n
    change ((1 : C) ⊗ₜ[A] (r • m)) ⊗ₜ[C] ((1 : C) ⊗ₜ[B] n) =
      r • (((1 : C) ⊗ₜ[A] m) ⊗ₜ[C] ((1 : C) ⊗ₜ[B] n))
    rw [TensorProduct.tmul_smul]
    rfl

@[simp]
theorem unitPairing_apply (m : M) (n : N) :
    unitPairing R B M N A C m n = ((1 : C) ⊗ₜ[A] m) ⊗ₜ[C] ((1 : C) ⊗ₜ[B] n) := rfl

/-- The first scalar-extension unit retains the original A action through A -> C. -/
theorem unitPairing_smul_left (a : A) (m : M) (n : N) :
    unitPairing R B M N A C (a • m) n =
      algebraMap A C a • unitPairing R B M N A C m n := by
  change ((1 : C) ⊗ₜ[A] (a • m)) ⊗ₜ[C] ((1 : C) ⊗ₜ[B] n) =
    algebraMap A C a • (((1 : C) ⊗ₜ[A] m) ⊗ₜ[C] ((1 : C) ⊗ₜ[B] n))
  rw [TensorProduct.tmul_smul, TensorProduct.smul_tmul']
  exact congrArg (fun t => t ⊗ₜ[C] ((1 : C) ⊗ₜ[B] n))
    (IsScalarTower.algebraMap_smul C a ((1 : C) ⊗ₜ[A] m)).symm

/-- The second scalar-extension unit retains the original B action through B -> C. -/
theorem unitPairing_smul_right (b : B) (m : M) (n : N) :
    unitPairing R B M N A C m (b • n) =
      algebraMap B C b • unitPairing R B M N A C m n := by
  change ((1 : C) ⊗ₜ[A] m) ⊗ₜ[C] ((1 : C) ⊗ₜ[B] (b • n)) =
    algebraMap B C b • (((1 : C) ⊗ₜ[A] m) ⊗ₜ[C] ((1 : C) ⊗ₜ[B] n))
  rw [TensorProduct.tmul_smul,
    ← IsScalarTower.algebraMap_smul C b ((1 : C) ⊗ₜ[B] n), TensorProduct.tmul_smul]

/-- The tensor of the original scalar-extension units is linear for the
canonical tensor-algebra map, on the original tensor carrier. -/
def unitMap :
    letI := module R B M N A
    letI := (scalarMap (R := R) (A := A) (B := B) C).toRingHom.toAlgebra
    M ⊗[R] N →ₗ[A ⊗[R] B] (C ⊗[A] M) ⊗[C] (C ⊗[B] N) := by
  letI := module R B M N A
  letI := (scalarMap (R := R) (A := A) (B := B) C).toRingHom.toAlgebra
  let h := TensorProduct.lift (unitPairing R B M N A C)
  refine { toAddHom := h.toAddHom, map_smul' := ?_ }
  intro d t
  change h (d • t) = d • h t
  induction d using TensorProduct.inductionOn with
  | tmul a b =>
    induction t using TensorProduct.inductionOn with
    | tmul m n =>
      change unitPairing R B M N A C (a • m) (b • n) =
        (a ⊗ₜ[R] b) • unitPairing R B M N A C m n
      rw [unitPairing_smul_left, unitPairing_smul_right, smul_smul,
        ← IsScalarTower.algebraMap_smul C (a ⊗ₜ[R] b)]
      rfl
    | add x y hx hy => simp only [smul_add, map_add, hx, hy]
  | add d e hd he => simp only [add_smul, map_add, hd, he]

/-- The original tensor-algebra linear unit map has its literal pure-tensor formula. -/
@[simp]
theorem unitMap_tmul (m : M) (n : N) :
    unitMap R B M N A C (m ⊗ₜ[R] n) =
      ((1 : C) ⊗ₜ[A] m) ⊗ₜ[C] ((1 : C) ⊗ₜ[B] n) := rfl

/-- The canonical forward base-change map uses the original scalar-extension
adjunction map, with the original balanced tensor unit. -/
def baseChangeMap :
    letI := module R B M N A
    letI := (scalarMap (R := R) (A := A) (B := B) C).toRingHom.toAlgebra
    C ⊗[A ⊗[R] B] (M ⊗[R] N) →ₗ[C] (C ⊗[A] M) ⊗[C] (C ⊗[B] N) := by
  letI := module R B M N A
  letI := (scalarMap (R := R) (A := A) (B := B) C).toRingHom.toAlgebra
  exact (unitMap R B M N A C).liftBaseChange C

/-- The forward map keeps the original scalar-extension tensor formula. -/
theorem baseChangeMap_tmul (c : C) (m : M) (n : N) :
    letI := module R B M N A
    letI := (scalarMap (R := R) (A := A) (B := B) C).toRingHom.toAlgebra
    baseChangeMap R B M N A C (c ⊗ₜ[A ⊗[R] B] (m ⊗ₜ[R] n)) =
      (c ⊗ₜ[A] m) ⊗ₜ[C] ((1 : C) ⊗ₜ[B] n) := by
  let := module R B M N A
  let := (scalarMap (R := R) (A := A) (B := B) C).toRingHom.toAlgebra
  change c • (((1 : C) ⊗ₜ[A] m) ⊗ₜ[C] ((1 : C) ⊗ₜ[B] n)) = _
  rw [TensorProduct.smul_tmul', TensorProduct.smul_tmul', smul_eq_mul, mul_one]

/-- The original unit into scalar extension is linear in the two original
coefficient rings separately. This is the balanced map used for the inverse. -/
def toBaseChangePairing :
    letI := module R B M N A
    letI := (scalarMap (R := R) (A := A) (B := B) C).toRingHom.toAlgebra
    M →ₗ[A] N →ₗ[B] C ⊗[A ⊗[R] B] (M ⊗[R] N) := by
  letI := module R B M N A
  letI := (scalarMap (R := R) (A := A) (B := B) C).toRingHom.toAlgebra
  refine {
    toFun := fun m =>
      { toFun := fun n => (1 : C) ⊗ₜ[A ⊗[R] B] (m ⊗ₜ[R] n)
        map_add' := fun n n' => by simp only [TensorProduct.tmul_add]
        map_smul' := ?_ }
    map_add' := ?_
    map_smul' := ?_ }
  · intro b n
    change (1 : C) ⊗ₜ[A ⊗[R] B] (m ⊗ₜ[R] (b • n)) =
      b • ((1 : C) ⊗ₜ[A ⊗[R] B] (m ⊗ₜ[R] n))
    have hp : m ⊗ₜ[R] (b • n) = (1 ⊗ₜ[R] b : A ⊗[R] B) • (m ⊗ₜ[R] n) := by
      rw [module_smul_tmul, one_smul]
    rw [hp, TensorProduct.tmul_smul,
      ← IsScalarTower.algebraMap_smul C (1 ⊗ₜ[R] b), ← IsScalarTower.algebraMap_smul C b]
    have hs : algebraMap (A ⊗[R] B) C (1 ⊗ₜ[R] b) = algebraMap B C b := by
      change algebraMap A C 1 * algebraMap B C b = _
      rw [map_one, one_mul]
    rw [hs]
  · intro m m'
    apply LinearMap.ext
    intro n
    change (1 : C) ⊗ₜ[A ⊗[R] B] ((m + m') ⊗ₜ[R] n) =
      (1 : C) ⊗ₜ[A ⊗[R] B] (m ⊗ₜ[R] n) + (1 : C) ⊗ₜ[A ⊗[R] B] (m' ⊗ₜ[R] n)
    simp only [TensorProduct.add_tmul, TensorProduct.tmul_add]
  · intro a m
    apply LinearMap.ext
    intro n
    change (1 : C) ⊗ₜ[A ⊗[R] B] ((a • m) ⊗ₜ[R] n) =
      a • ((1 : C) ⊗ₜ[A ⊗[R] B] (m ⊗ₜ[R] n))
    have hp : (a • m) ⊗ₜ[R] n = (a ⊗ₜ[R] 1 : A ⊗[R] B) • (m ⊗ₜ[R] n) := by
      rw [module_smul_tmul, one_smul]
    rw [hp, TensorProduct.tmul_smul,
      ← IsScalarTower.algebraMap_smul C (a ⊗ₜ[R] 1), ← IsScalarTower.algebraMap_smul C a]
    have hs : algebraMap (A ⊗[R] B) C (a ⊗ₜ[R] 1) = algebraMap A C a := by
      change algebraMap A C a * algebraMap B C 1 = _
      rw [map_one, mul_one]
    rw [hs]

@[simp]
theorem toBaseChangePairing_apply (m : M) (n : N) :
    letI := module R B M N A
    letI := (scalarMap (R := R) (A := A) (B := B) C).toRingHom.toAlgebra
    toBaseChangePairing R B M N A C m n = (1 : C) ⊗ₜ[A ⊗[R] B] (m ⊗ₜ[R] n) := rfl

/-- The inverse base-change map extends the original balanced pairing in
both coefficient variables, using the native scalar-extension maps. -/
def baseChangeInv :
    letI := module R B M N A
    letI := (scalarMap (R := R) (A := A) (B := B) C).toRingHom.toAlgebra
    (C ⊗[A] M) ⊗[C] (C ⊗[B] N) →ₗ[C] C ⊗[A ⊗[R] B] (M ⊗[R] N) := by
  letI := module R B M N A
  letI := (scalarMap (R := R) (A := A) (B := B) C).toRingHom.toAlgebra
  let Z := C ⊗[A ⊗[R] B] (M ⊗[R] N)
  let h : M →ₗ[A] (C ⊗[B] N →ₗ[C] Z) :=
    ((LinearMap.liftBaseChangeEquiv (R := B) (M := N) (N := Z) C).toLinearMap.restrictScalars A) ∘ₗ
      toBaseChangePairing R B M N A C
  exact TensorProduct.lift (h.liftBaseChange C)

/-- The inverse has exactly the original product-of-scalars tensor formula. -/
theorem baseChangeInv_tmul (c d : C) (m : M) (n : N) :
    letI := module R B M N A
    letI := (scalarMap (R := R) (A := A) (B := B) C).toRingHom.toAlgebra
    baseChangeInv R B M N A C ((c ⊗ₜ[A] m) ⊗ₜ[C] (d ⊗ₜ[B] n)) =
      (c * d) ⊗ₜ[A ⊗[R] B] (m ⊗ₜ[R] n) := by
  let := module R B M N A
  let := (scalarMap (R := R) (A := A) (B := B) C).toRingHom.toAlgebra
  change c • (d • ((1 : C) ⊗ₜ[A ⊗[R] B] (m ⊗ₜ[R] n))) = _
  rw [smul_smul, TensorProduct.smul_tmul', smul_eq_mul, mul_one]

/-- Applying the original forward map and then its inverse fixes scalar
extension of the original external tensor. -/
theorem baseChangeInv_comp_baseChangeMap :
    letI := module R B M N A
    letI := (scalarMap (R := R) (A := A) (B := B) C).toRingHom.toAlgebra
    (baseChangeInv R B M N A C) ∘ₗ baseChangeMap R B M N A C = LinearMap.id := by
  let := module R B M N A
  let := (scalarMap (R := R) (A := A) (B := B) C).toRingHom.toAlgebra
  apply TensorProduct.AlgebraTensorModule.ext
  intro c t
  change baseChangeInv R B M N A C (baseChangeMap R B M N A C (c ⊗ₜ[A ⊗[R] B] t)) =
    c ⊗ₜ[A ⊗[R] B] t
  induction t using TensorProduct.inductionOn with
  | tmul m n => rw [baseChangeMap_tmul, baseChangeInv_tmul, mul_one]
  | add x y hx hy => simp only [TensorProduct.tmul_add, map_add, hx, hy]

/-- Applying the inverse and then the original forward map fixes the
tensor of the two original scalar extensions. -/
theorem baseChangeMap_comp_baseChangeInv :
    letI := module R B M N A
    letI := (scalarMap (R := R) (A := A) (B := B) C).toRingHom.toAlgebra
    (baseChangeMap R B M N A C) ∘ₗ baseChangeInv R B M N A C = LinearMap.id := by
  let := module R B M N A
  let := (scalarMap (R := R) (A := A) (B := B) C).toRingHom.toAlgebra
  apply TensorProduct.ext'
  intro s t
  change baseChangeMap R B M N A C (baseChangeInv R B M N A C (s ⊗ₜ[C] t)) = s ⊗ₜ[C] t
  induction s using TensorProduct.inductionOn with
  | tmul c m =>
    induction t using TensorProduct.inductionOn with
    | tmul d n =>
      rw [baseChangeInv_tmul, baseChangeMap_tmul]
      calc
        _ = (d • (c ⊗ₜ[A] m)) ⊗ₜ[C] ((1 : C) ⊗ₜ[B] n) := by
          rw [TensorProduct.smul_tmul', smul_eq_mul, mul_comm d c]
        _ = (c ⊗ₜ[A] m) ⊗ₜ[C] (d • ((1 : C) ⊗ₜ[B] n)) :=
          TensorProduct.smul_tmul d _ _
        _ = _ := by rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    | add x y hx hy => simp only [TensorProduct.tmul_add, map_add, hx, hy]
  | add x y hx hy => simp only [TensorProduct.add_tmul, map_add, hx, hy]

/-- The canonical heterobasic tensor/base-change equivalence, on the
original tensor carriers and original compatible scalar maps. No flatness
hypothesis or chosen module basis is needed. -/
def baseChangeEquiv :
    letI := module R B M N A
    letI := (scalarMap (R := R) (A := A) (B := B) C).toRingHom.toAlgebra
    C ⊗[A ⊗[R] B] (M ⊗[R] N) ≃ₗ[C] (C ⊗[A] M) ⊗[C] (C ⊗[B] N) := by
  letI := module R B M N A
  letI := (scalarMap (R := R) (A := A) (B := B) C).toRingHom.toAlgebra
  exact LinearEquiv.ofLinearMap (baseChangeMap R B M N A C) (baseChangeInv R B M N A C)
    (baseChangeMap_comp_baseChangeInv R B M N A C)
    (baseChangeInv_comp_baseChangeMap R B M N A C)

/-- The equivalence has exactly the original forward tensor map. -/
theorem baseChangeEquiv_toLinearMap :
    letI := module R B M N A
    letI := (scalarMap (R := R) (A := A) (B := B) C).toRingHom.toAlgebra
    (baseChangeEquiv R B M N A C).toLinearMap = baseChangeMap R B M N A C := rfl

/-- Its inverse has exactly the original product-of-scalars tensor map. -/
theorem baseChangeEquiv_symm_toLinearMap :
    letI := module R B M N A
    letI := (scalarMap (R := R) (A := A) (B := B) C).toRingHom.toAlgebra
    (baseChangeEquiv R B M N A C).symm.toLinearMap = baseChangeInv R B M N A C := rfl

/-- Whole naturality in both original coefficient modules, including the
original tensor-algebra scalar-extension map on the source. -/
theorem baseChangeMap_naturality (f : M →ₗ[A] M') (g : N →ₗ[B] N') :
    letI := module R B M N A
    letI := module R B M' N' A
    letI := (scalarMap (R := R) (A := A) (B := B) C).toRingHom.toAlgebra
    (TensorProduct.map (f.baseChange C) (g.baseChange C)) ∘ₗ baseChangeMap R B M N A C =
      baseChangeMap R B M' N' A C ∘ₗ (map (R := R) f g).baseChange C := by
  let := module R B M N A
  let := module R B M' N' A
  let := (scalarMap (R := R) (A := A) (B := B) C).toRingHom.toAlgebra
  apply TensorProduct.AlgebraTensorModule.ext
  intro c t
  change TensorProduct.map (f.baseChange C) (g.baseChange C)
      (baseChangeMap R B M N A C (c ⊗ₜ[A ⊗[R] B] t)) =
    baseChangeMap R B M' N' A C ((map (R := R) f g).baseChange C (c ⊗ₜ[A ⊗[R] B] t))
  induction t using TensorProduct.inductionOn with
  | tmul m n =>
    simp only [baseChangeMap_tmul, TensorProduct.map_tmul, LinearMap.baseChange_tmul, map_tmul]
  | add x y hx hy => simp only [TensorProduct.tmul_add, map_add, hx, hy]

section Exactness

variable {M'' N'' : Type*} [AddCommGroup M''] [Module R M''] [Module A M'']
  [IsScalarTower R A M''] [AddCommGroup N''] [Module R N''] [Module B N'']
  [IsScalarTower R B N'']

/-- The original tensor of the two scalar extensions preserves an exact
first-variable pair when the other coefficient is base-flat and the
actual tensor-algebra scalar map is flat. -/
theorem baseChange_exact_left [Module.Flat R N]
    (hC : (scalarMap (R := R) (A := A) (B := B) C).toRingHom.Flat)
    (f : M →ₗ[A] M') (g : M' →ₗ[A] M'') (hfg : Function.Exact f g) :
    Function.Exact
      (TensorProduct.map (f.baseChange C) (LinearMap.id : C ⊗[B] N →ₗ[C] C ⊗[B] N))
      (TensorProduct.map (g.baseChange C) (LinearMap.id : C ⊗[B] N →ₗ[C] C ⊗[B] N)) := by
  let := module R B M N A
  let := module R B M' N A
  let := module R B M'' N A
  let := (scalarMap (R := R) (A := A) (B := B) C).toRingHom.toAlgebra
  have : Module.Flat (A ⊗[R] B) C := hC
  have hD : Function.Exact
      (map (R := R) f (LinearMap.id : N →ₗ[B] N))
      (map (R := R) g (LinearMap.id : N →ₗ[B] N)) := by
    change Function.Exact ((f.restrictScalars R).rTensor N) ((g.restrictScalars R).rTensor N)
    exact Module.Flat.rTensor_exact N hfg
  have hE : Function.Exact
      ((map (R := R) f (LinearMap.id : N →ₗ[B] N)).baseChange C)
      ((map (R := R) g (LinearMap.id : N →ₗ[B] N)).baseChange C) :=
    Module.Flat.lTensor_exact C hD
  refine Function.Exact.of_ladder_linearEquiv_of_exact
    (e₁ := baseChangeEquiv R B M N A C) (e₂ := baseChangeEquiv R B M' N A C)
    (e₃ := baseChangeEquiv R B M'' N A C) ?_ ?_ hE
  · simpa only [baseChangeEquiv_toLinearMap, LinearMap.baseChange_id] using
      baseChangeMap_naturality R B M N A C f (LinearMap.id : N →ₗ[B] N)
  · simpa only [baseChangeEquiv_toLinearMap, LinearMap.baseChange_id] using
      baseChangeMap_naturality R B M' N A C g (LinearMap.id : N →ₗ[B] N)

/-- The original tensor of the two scalar extensions preserves an exact
second-variable pair under the corresponding original base-flat and
actual tensor-algebra flatness hypotheses. -/
theorem baseChange_exact_right [Module.Flat R M]
    (hC : (scalarMap (R := R) (A := A) (B := B) C).toRingHom.Flat)
    (f : N →ₗ[B] N') (g : N' →ₗ[B] N'') (hfg : Function.Exact f g) :
    Function.Exact
      (TensorProduct.map (LinearMap.id : C ⊗[A] M →ₗ[C] C ⊗[A] M) (f.baseChange C))
      (TensorProduct.map (LinearMap.id : C ⊗[A] M →ₗ[C] C ⊗[A] M) (g.baseChange C)) := by
  let := module R B M N A
  let := module R B M N' A
  let := module R B M N'' A
  let := (scalarMap (R := R) (A := A) (B := B) C).toRingHom.toAlgebra
  have : Module.Flat (A ⊗[R] B) C := hC
  have hD : Function.Exact
      (map (R := R) (LinearMap.id : M →ₗ[A] M) f)
      (map (R := R) (LinearMap.id : M →ₗ[A] M) g) := by
    change Function.Exact ((f.restrictScalars R).lTensor M) ((g.restrictScalars R).lTensor M)
    exact Module.Flat.lTensor_exact M hfg
  have hE : Function.Exact
      ((map (R := R) (LinearMap.id : M →ₗ[A] M) f).baseChange C)
      ((map (R := R) (LinearMap.id : M →ₗ[A] M) g).baseChange C) :=
    Module.Flat.lTensor_exact C hD
  refine Function.Exact.of_ladder_linearEquiv_of_exact
    (e₁ := baseChangeEquiv R B M N A C) (e₂ := baseChangeEquiv R B M N' A C)
    (e₃ := baseChangeEquiv R B M N'' A C) ?_ ?_ hE
  · simpa only [baseChangeEquiv_toLinearMap, LinearMap.baseChange_id] using
      baseChangeMap_naturality R B M N A C (LinearMap.id : M →ₗ[A] M) f
  · simpa only [baseChangeEquiv_toLinearMap, LinearMap.baseChange_id] using
      baseChangeMap_naturality R B M N' A C (LinearMap.id : M →ₗ[A] M) g

end Exactness

end BaseChange

end TensorProduct.External
