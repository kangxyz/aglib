/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.Amitsur.Conerve
public import Aglib.Algebra.Homology.Amitsur.Augmented
public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Associator

/-!
# The original Amitsur complex of an arbitrary module

The native Čech conerve acts on the original coefficient module by tensoring.
The augmented complex is the native augmented alternating coface complex.
Its augmentation is the original map `m ↦ 1 ⊗ m`; its later differentials
are the original alternating unit insertions, without a flatness premise on `M`.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory
open scoped Simplicial TensorProduct

namespace ModuleCat.Amitsur

universe u v

variable (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
variable (M : ModuleCat.{max u v} R)

/-- The original underlying algebra module tensored with the original coefficient module. -/
def tensorModule : CommAlgCat.{u} R ⥤ ModuleCat.{max u v} R where
  obj A := ModuleCat.of R (A ⊗[R] M)
  map f := ModuleCat.ofHom (f.hom.toLinearMap.rTensor M)
  map_id A := by ext a m; rfl
  map_comp f g := by ext a m; rfl

/-- The original native module-valued Amitsur cosimplicial object. -/
def cosimplicial : CosimplicialObject (ModuleCat.{max u v} R) :=
  Algebra.Amitsur.conerve R S ⋙ tensorModule R M

/-- The original module and its original unit augmentation of the native conerve. -/
def augmentedObject : CosimplicialObject.Augmented (ModuleCat.{max u v} R) where
  left := M
  right := cosimplicial R S M
  hom := {
    app n := ModuleCat.ofHom (TensorProduct.mk R (Algebra.Amitsur.term R S n.len) M 1)
    naturality := by
      intro i j f
      ext m
      change (1 : Algebra.Amitsur.term R S j.len) ⊗ₜ[R] m =
        (((Algebra.Amitsur.conerve R S).map f).hom 1) ⊗ₜ[R] m
      rw [map_one] }

/-- The original native alternating coface complex. -/
def complex : CochainComplex (ModuleCat.{max u v} R) ℕ :=
  AlgebraicTopology.AlternatingCofaceMapComplex.obj (cosimplicial R S M)

/-- The actual original augmented Amitsur complex, with `M` in degree zero. -/
def augmentedComplex : CochainComplex (ModuleCat.{max u v} R) ℕ :=
  AlgebraicTopology.Amitsur.augmentedObj (augmentedObject R S M)

@[simp]
theorem augmentedComplex_X_zero : (augmentedComplex R S M).X 0 = M := rfl

@[simp]
theorem augmentedComplex_X_succ (n : ℕ) :
    (augmentedComplex R S M).X (n + 1) =
      ModuleCat.of R (Algebra.Amitsur.term R S n ⊗[R] M) := rfl

/-- The augmentation is the original unit-tensor map, on original module elements. -/
theorem augmentedComplex_d_zero_one_apply (m : M) :
    (augmentedComplex R S M).d 0 1 m =
      (1 : Algebra.Amitsur.term R S 0) ⊗ₜ[R] m := rfl

/-- Every original coface acts through its original algebra map on pure tensors. -/
@[simp]
theorem cosimplicial_δ_apply (n : ℕ) (i : Fin (n + 2))
    (a : Algebra.Amitsur.term R S n) (m : M) :
    (cosimplicial R S M).δ i (a ⊗ₜ[R] m) =
      ((Algebra.Amitsur.conerve R S).δ i).hom a ⊗ₜ[R] m := rfl

/-- The actual first unaugmented term is the original `S ⊗ M`. -/
def degreeZeroIso : (complex R S M).X 0 ≅ ModuleCat.of R (S ⊗[R] M) :=
  (tensorModule R M).mapIso (Algebra.Amitsur.zeroIso R S)

/-- Under the actual degree-zero comparison, the original augmentation stays `1 ⊗ m`. -/
theorem augmentation_degreeZeroIso_apply (m : M) :
    ((augmentedComplex R S M).d 0 1 ≫ (degreeZeroIso R S M).hom) m =
      (1 : S) ⊗ₜ[R] m := by
  change ((Algebra.Amitsur.zeroTo R S).hom 1) ⊗ₜ[R] m = (1 : S) ⊗ₜ[R] m
  rw [map_one]

/-- The actual successor comparison is the canonical first-factor tensor comparison. -/
def successorIso (n : ℕ) : (complex R S M).X (n + 1) ≅
    ModuleCat.of R (S ⊗[R] ((complex R S M).X n)) :=
  (tensorModule R M).mapIso (Algebra.Amitsur.successorTensorIso R S n) ≪≫
    (TensorProduct.assoc R S (Algebra.Amitsur.term R S n) M).toModuleIso

end ModuleCat.Amitsur
