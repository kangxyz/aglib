/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.RingTheory.Coalgebra.FiniteDualCharacters

/-! The character correspondence uses arbitrary coefficient algebras and the original tensor. -/

@[expose] public section

noncomputable section

open Module
open scoped TensorProduct Module.Dual.FiniteDual

variable (k V R : Type*) [Field k] [AddCommGroup V] [Module k V]
  [Coalgebra k V] [FiniteDimensional k V] [CommRing R] [Algebra k R]

example : (Dual k V →ₐ[k] R) ≃ GroupLike R (R ⊗[k] V) :=
  Module.Dual.algHomGroupLikeEquiv k V R

example (f : Dual k V →ₐ[k] R) :
    (Module.Dual.algHomGroupLikeEquiv k V R f).val =
      TensorProduct.comm k V R (f.toLinearMap.lTensor V (coevaluation k V 1)) :=
  Module.Dual.algHomGroupLikeEquiv_val k V R f

example {S : Type*} [CommRing S] [Algebra k S]
    (f : Dual k V →ₐ[k] R) (g : R →ₐ[k] S) :
    (Module.Dual.algHomGroupLikeEquiv k V S (g.comp f)).val =
      TensorProduct.map g.toLinearMap LinearMap.id
        (Module.Dual.algHomGroupLikeEquiv k V R f).val :=
  Module.Dual.algHomGroupLikeEquiv_naturality k V R f g
