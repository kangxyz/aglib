/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.Group.RootsFiniteEtale
public import Aglib.RingTheory.TensorProduct.CoalgebraBaseChange
public import Aglib.RingTheory.RootsOfUnity.Galois
public import Aglib.RingTheory.RootsOfUnity.BaseField
public import Aglib.RingTheory.RootsOfUnity.PrimitiveCoordinates
public import Mathlib.RingTheory.HopfAlgebra.Basic

/-!
# The intrinsic roots Hopf algebra and its actual geometric points

The algebra is the original R[T]/(T^n - 1), with its multiplicative comultiplication,
identity, inversion, Hopf laws, and cocommutativity. Finiteness holds at nonzero
levels; etaleness additionally requires that n is a unit in R. Algebra points and
generic Hopf multiplication are compared with the actual roots-of-unity group.
The supplied primitive root is used only by the final root-fixedness theorem.
Source: K2-018, revision e73d98b1b5c1e5abcdebf7d058e436d792b87982;
the original integration provenance was raw SHA-256
a8b4ec48bd1b43ecbdc0b33ae7bf38c438daa53f7f0c3d462242a821ad2d4da0.
Rooted Tate tensor-square coordinates remain with the application.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false
open scoped TensorProduct

namespace AlgebraicGeometry.Scheme.Group.RootsHopfAlgebra

open AlgebraicGeometry.Scheme.Group.RootsFiniteEtale
open Field.absoluteGaloisGroup.RootsOfUnity

universe u
variable (R : Type u) [CommRing R] (n : ℕ) [NeZero n]

abbrev H := RootAlgebra R n
abbrev t : H R n := AdjoinRoot.root (rootPolynomial R n)

/-- Actual multiplicative comultiplication on the root quotient. -/
def delta : H R n →ₐ[R] H R n ⊗[R] H R n :=
  AdjoinRoot.liftAlgHom (rootPolynomial R n)
    (Algebra.ofId R _) (t R n ⊗ₜ[R] t R n) (by
      simp [rootPolynomial, Algebra.TensorProduct.tmul_pow, root_pow,
        Algebra.TensorProduct.one_def])

/-- Actual identity section, evaluated at the root 1. -/
def epsilon : H R n →ₐ[R] R :=
  AdjoinRoot.liftAlgHom (rootPolynomial R n) (AlgHom.id R R) 1 (by
    simp [rootPolynomial])

/-- Actual inversion on the root quotient. -/
def inverse : H R n →ₐ[R] H R n :=
  AdjoinRoot.liftAlgHom (rootPolynomial R n) (Algebra.ofId R _) (t R n ^ (n - 1)) (by
    have hp : (t R n ^ (n - 1)) ^ n = 1 := by
      rw [← pow_mul, Nat.mul_comm, pow_mul, root_pow]
      simp
    simp only [rootPolynomial, Polynomial.eval₂_sub, Polynomial.eval₂_pow,
      Polynomial.eval₂_X, Polynomial.eval₂_one]
    exact sub_eq_zero.mpr hp)

omit [NeZero n] in
@[simp] theorem delta_t : delta R n (t R n) = t R n ⊗ₜ[R] t R n :=
  AdjoinRoot.liftAlgHom_root _ _ _ _

omit [NeZero n] in
@[simp] theorem epsilon_t : epsilon R n (t R n) = 1 :=
  AdjoinRoot.liftAlgHom_root _ _ _ _

omit [NeZero n] in
@[simp] theorem inverse_t : inverse R n (t R n) = t R n ^ (n - 1) :=
  AdjoinRoot.liftAlgHom_root _ _ _ _

omit [NeZero n] in
theorem delta_coassoc :
    (Algebra.TensorProduct.assoc R R R (H R n) (H R n) (H R n)).toAlgHom.comp
      ((Algebra.TensorProduct.map (delta R n) (AlgHom.id R (H R n))).comp (delta R n)) =
    (Algebra.TensorProduct.map (AlgHom.id R (H R n)) (delta R n)).comp (delta R n) := by
  apply AdjoinRoot.algHom_ext
  simp

omit [NeZero n] in
theorem delta_counit_left :
    (Algebra.TensorProduct.map (epsilon R n) (AlgHom.id R (H R n))).comp (delta R n) =
      (Algebra.TensorProduct.lid R (H R n)).symm := by
  apply AdjoinRoot.algHom_ext
  simp

omit [NeZero n] in
theorem delta_counit_right :
    (Algebra.TensorProduct.map (AlgHom.id R (H R n)) (epsilon R n)).comp (delta R n) =
      (Algebra.TensorProduct.rid R R (H R n)).symm := by
  apply AdjoinRoot.algHom_ext
  simp

instance rootsBialgebra : Bialgebra R (H R n) :=
  Bialgebra.ofAlgHom (delta R n) (epsilon R n) (delta_coassoc R n)
    (delta_counit_left R n) (delta_counit_right R n)

omit [NeZero n] in
@[simp] theorem comulAlgHom_eq : Bialgebra.comulAlgHom R (H R n) = delta R n := rfl
omit [NeZero n] in
@[simp] theorem counitAlgHom_eq : Bialgebra.counitAlgHom R (H R n) = epsilon R n := rfl

theorem inverse_mul_t : inverse R n (t R n) * t R n = 1 := by
  rw [inverse_t, ← pow_succ]
  simpa [Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr (NeZero.ne n))] using root_pow R n

theorem antipode_left :
    (Algebra.TensorProduct.lift (inverse R n) (AlgHom.id R (H R n))
      (fun _ _ => Commute.all _ _)).comp (Bialgebra.comulAlgHom R (H R n)) =
    (Algebra.ofId R (H R n)).comp (Bialgebra.counitAlgHom R (H R n)) := by
  apply AdjoinRoot.algHom_ext
  simpa using inverse_mul_t R n

theorem antipode_right :
    (Algebra.TensorProduct.lift (AlgHom.id R (H R n)) (inverse R n)
      (fun _ _ => Commute.all _ _)).comp (Bialgebra.comulAlgHom R (H R n)) =
    (Algebra.ofId R (H R n)).comp (Bialgebra.counitAlgHom R (H R n)) := by
  apply AdjoinRoot.algHom_ext
  simpa [mul_comm] using inverse_mul_t R n

instance rootsHopfAlgebra : HopfAlgebra R (H R n) :=
  HopfAlgebra.ofAlgHom (inverse R n) (antipode_left R n) (antipode_right R n)

omit [NeZero n] in
theorem delta_comm :
    (Algebra.TensorProduct.comm R (H R n) (H R n)).toAlgHom.comp (delta R n) = delta R n := by
  apply AdjoinRoot.algHom_ext
  simp

instance rootsCocomm : Coalgebra.IsCocomm R (H R n) where
  comm_comp_comul := congrArg AlgHom.toLinearMap (delta_comm R n)

theorem finite : Module.Finite R (H R n) := inferInstance

theorem etale (hunit : IsUnit (n : R)) : Algebra.Etale R (H R n) :=
  rootAlgebra_etale R n (Nat.pos_of_ne_zero (NeZero.ne n)) hunit

section GeometricPoints

variable (K : Type u) [Field K] [Algebra R K]

open Field.absoluteGaloisGroup.RootsOfUnity.PrimitiveCoordinates
open Algebra.TensorProduct.BaseChange

-- This local view uses the same action on the definitional automorphism carrier.
local instance :
    DistribMulAction (AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) (Mu K n) :=
  muDistribMulAction K n

/-- Evaluation at the actual universal root identifies quotient-algebra maps
with actual roots, with the prescribed base-algebra structure. -/
def algebraPointEquiv : (H R n →ₐ[R] AlgebraicClosure K) ≃ Mu K n where
  toFun f := Additive.ofMul (rootsOfUnity.mkOfPowEq (f (t R n))
    (by rw [← map_pow, root_pow, map_one]))
  invFun a := AdjoinRoot.liftAlgHom (rootPolynomial R n)
    (Algebra.ofId R (AlgebraicClosure K)) ((a.toMul : (AlgebraicClosure K)ˣ) : AlgebraicClosure K)
    (by
      simp only [rootPolynomial, Polynomial.eval₂_sub, Polynomial.eval₂_pow,
        Polynomial.eval₂_X, Polynomial.eval₂_one]
      exact sub_eq_zero.mpr ((mem_rootsOfUnity' n a.toMul.val).mp a.toMul.property))
  left_inv f := by
    apply AdjoinRoot.algHom_ext
    simp
  right_inv a := by
    apply Additive.toMul.injective
    apply rootsOfUnity.coe_injective
    simp

/-- This point identification is exactly the existing polynomial-root
universal property, now at maps preserving the prescribed R-algebra structure. -/
theorem algebraPointEquiv_rootRingHomEquiv (f : H R n →ₐ[R] AlgebraicClosure K) :
    (algebraPointEquiv R n K f).toMul =
      rootRingHomEquiv (AlgebraicClosure K) (algebraMap R (AlgebraicClosure K)) n
        ⟨f.toRingHom, by ext r; exact f.commutes r⟩ := rfl

/-- Actual geometric points of K tensor H, without a cyclic replacement. -/
def pointEquiv : Mu K n ≃ ((K ⊗[R] H R n) →ₐ[K] AlgebraicClosure K) :=
  (algebraPointEquiv R n K).symm.trans
    (Algebra.TensorProduct.liftEquivRight R K (H R n) (AlgebraicClosure K))

/-- The point belonging to this actual root. -/
def point (a : Mu K n) : (K ⊗[R] H R n) →ₐ[K] AlgebraicClosure K :=
  pointEquiv R n K a

@[simp] theorem point_root (a : Mu K n) :
    point R n K a ((1 : K) ⊗ₜ[R] t R n) =
      ((a.toMul : (AlgebraicClosure K)ˣ) : AlgebraicClosure K) := by
  simp [point, pointEquiv, algebraPointEquiv, Algebra.TensorProduct.liftEquivRight]

omit [NeZero n] in
/-- A generic algebra point is determined by its actual root value. -/
theorem point_ext {f g : (K ⊗[R] H R n) →ₐ[K] AlgebraicClosure K}
    (h : f ((1 : K) ⊗ₜ[R] t R n) = g ((1 : K) ⊗ₜ[R] t R n)) : f = g := by
  apply (Algebra.TensorProduct.liftEquivRight R K (H R n) (AlgebraicClosure K)).symm.injective
  apply AdjoinRoot.algHom_ext
  exact h

omit [NeZero n] in
@[simp] theorem genericDelta_root :
    Algebra.TensorProduct.BaseChange.comul R K (delta R n) ((1 : K) ⊗ₜ[R] t R n) =
      ((1 : K) ⊗ₜ[R] t R n) ⊗ₜ[K] ((1 : K) ⊗ₜ[R] t R n) := by
  simp [Algebra.TensorProduct.BaseChange.comul, Algebra.TensorProduct.BaseChange.map]

omit [NeZero n] in
@[simp] theorem genericEpsilon_root :
    Algebra.TensorProduct.BaseChange.counit R K (epsilon R n) ((1 : K) ⊗ₜ[R] t R n) = 1 := by
  simp [Algebra.TensorProduct.BaseChange.counit, Algebra.TensorProduct.BaseChange.map]

/-- Addition of actual roots is precisely the actual Hopf multiplication. -/
theorem point_add (a b : Mu K n) : point R n K (a + b) =
    (Algebra.TensorProduct.lift (point R n K a) (point R n K b)
      (fun _ _ => Commute.all _ _)).comp (Algebra.TensorProduct.BaseChange.comul R K (delta R n)) :=
        by
  apply point_ext R n K
  simp

/-- The actual zero root is precisely the Hopf identity. -/
theorem point_zero : point R n K 0 =
    (Algebra.ofId K (AlgebraicClosure K)).comp (Algebra.TensorProduct.BaseChange.counit R K (epsilon
      R n)) := by
  apply point_ext R n K
  simp

/-- The genuine Galois action on roots is the Galois action on their maps. -/
theorem point_galois (sigma : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) (a : Mu K n) :
    sigma.toAlgHom.comp (point R n K a) = point R n K (sigma • a) := by
  apply point_ext R n K
  simp
  rfl

/-- With a primitive root in K, every actual root is fixed. This is a theorem
about the genuine root action, deduced from the primitive generator. -/
theorem mu_fixed (zeta : rootsOfUnity n K)
    (hzeta : IsPrimitiveRoot ((zeta : Kˣ) : K) n)
    (g : Field.absoluteGaloisGroup K) (x : Mu K n) : g • x = x := by
  obtain ⟨k, rfl⟩ := exists_zsmul_root K n (Field.absoluteGaloisGroup.RootsOfUnity.baseRoot K n
    zeta)
    (baseRoot_primitive K n zeta hzeta) x
  change rootAction K n g (k • Field.absoluteGaloisGroup.RootsOfUnity.baseRoot K n zeta) = _
  rw [map_zsmul]
  change k • (g • Field.absoluteGaloisGroup.RootsOfUnity.baseRoot K n zeta) = _
  rw [Field.absoluteGaloisGroup.RootsOfUnity.baseRoot_fixed]


end GeometricPoints

end AlgebraicGeometry.Scheme.Group.RootsHopfAlgebra
