/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: R5Lab contributors
-/
module

public import Mathlib.RingTheory.TensorProduct.Maps
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.Algebra.Algebra.Subalgebra.Basic

/-! Flat base change commutes with explicit equalizer algebras.

## Extraction basis

Transferred from `R5Lab.RingTheory.Descent.FlatEqualizerBaseChange` at source revision
`95a3772b895fbc19a81684be4ffd519d0fdcd6b3`, SHA-256
`f4d31b6a34353ae5986f29d3b06d6a807afca6b3bda63adf8d973af3412a5590`.
The source interface retains its objects, maps and assumptions under native
mathematical declaration namespaces.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false

open _root_.TensorProduct

namespace AlgHom.Equalizer

universe u v w z
variable {R : Type u} (T : Type v) {B : Type w} {C : Type z}
variable [CommRing R] [CommRing T] [CommRing B] [CommRing C]
variable [Algebra R T] [Algebra R B] [Algebra R C]
variable (f g : B →ₐ[R] C)

/-- Extension of scalars of the algebra homomorphism `f` from `R` to `T`. -/
abbrev baseMap (f : B →ₐ[R] C) : T ⊗[R] B →ₐ[T] T ⊗[R] C :=
  Algebra.TensorProduct.map (AlgHom.id T T) f

lemma tensorInclusion_mem (x : T ⊗[R] AlgHom.equalizer f g) :
    Algebra.TensorProduct.map (AlgHom.id T T) (AlgHom.equalizer f g).val x ∈
      AlgHom.equalizer (baseMap T f) (baseMap T g) := by
  change baseMap T f _ = baseMap T g _
  induction x using _root_.TensorProduct.inductionOn with
  | tmul t b =>
    change t ⊗ₜ[R] f b = t ⊗ₜ[R] g b
    rw [b.property]
  | add x y hx hy => simp only [map_add, hx, hy]

/-- The natural map includes the equalizer and then extends scalars. -/
def map : T ⊗[R] AlgHom.equalizer f g →ₐ[T]
    AlgHom.equalizer (baseMap T f) (baseMap T g) :=
  (Algebra.TensorProduct.map (AlgHom.id T T) (AlgHom.equalizer f g).val).codRestrict _
    (tensorInclusion_mem T f g)

@[simp] lemma map_tmul (t : T) (b : AlgHom.equalizer f g) :
    (map T f g (t ⊗ₜ[R] b) : T ⊗[R] B) = t ⊗ₜ[R] (b : B) := rfl

lemma equalizer_exact : Function.Exact (AlgHom.equalizer f g).val.toLinearMap
    (f.toLinearMap - g.toLinearMap) := by
  intro b
  constructor
  · intro hb
    exact ⟨⟨b, sub_eq_zero.mp hb⟩, rfl⟩
  · rintro ⟨a, rfl⟩
    exact sub_eq_zero.mpr a.property

lemma map_injective [Module.Flat R T] : Function.Injective (map T f g) := by
  intro x y h
  apply Module.Flat.lTensor_preserves_injective_linearMap
    (AlgHom.equalizer f g).val.toLinearMap Subtype.val_injective
  exact congrArg Subtype.val h

lemma map_surjective [Module.Flat R T] : Function.Surjective (map T f g) := by
  intro x
  have hx : (f.toLinearMap - g.toLinearMap).lTensor T (x : T ⊗[R] B) = 0 := by
    rw [LinearMap.lTensor_sub, LinearMap.sub_apply, sub_eq_zero]
    exact x.property
  obtain ⟨y, hy⟩ := (Module.Flat.lTensor_exact T (equalizer_exact f g) x.val).1 hx
  exact ⟨y, Subtype.ext hy⟩

/-- Flat base change preserves this equalizer, as an actual algebra isomorphism. -/
def equiv [Module.Flat R T] : T ⊗[R] AlgHom.equalizer f g ≃ₐ[T]
    AlgHom.equalizer (baseMap T f) (baseMap T g) :=
  AlgEquiv.ofBijective (map T f g) ⟨map_injective T f g, map_surjective T f g⟩

@[simp] lemma equiv_tmul [Module.Flat R T] (t : T) (b : AlgHom.equalizer f g) :
    (equiv T f g (t ⊗ₜ[R] b) : T ⊗[R] B) = t ⊗ₜ[R] (b : B) := rfl

end AlgHom.Equalizer
