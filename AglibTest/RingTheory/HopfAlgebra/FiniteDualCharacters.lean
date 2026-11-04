/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.RingTheory.HopfAlgebra.FiniteDualCharacters

/-! Character units retain native coevaluation and arbitrary coefficient-algebra naturality. -/

@[expose] public section

noncomputable section

open Module
open scoped TensorProduct Module.Dual.FiniteDual

variable (k A R : Type*) [Field k] [Ring A] [HopfAlgebra k A]
  [FiniteDimensional k A] [CommRing R] [Algebra k R]

example : (Dual k A →ₐ[k] R) ≃
    {u : (R ⊗[k] A)ˣ // IsGroupLikeElem R (u : R ⊗[k] A)} :=
  Module.Dual.algHomGroupLikeUnitsEquiv k A R

example (f : Dual k A →ₐ[k] R) :
    ((Module.Dual.algHomGroupLikeUnitsEquiv k A R f).val : R ⊗[k] A) =
      TensorProduct.comm k A R (f.toLinearMap.lTensor A (coevaluation k A 1)) :=
  Module.Dual.algHomGroupLikeUnitsEquiv_val k A R f

example (f : Dual k A →ₐ[k] R) :
    (Module.Dual.algHomGroupLikeUnitsEquiv k A R f).val =
      Units.map (Module.Dual.characterTensorHom k A R f).toMonoidHom
        (HopfAlgebra.coevaluationUnit k A) :=
  Module.Dual.algHomGroupLikeUnitsEquiv_eq_map_coevaluationUnit k A R f

example {S : Type*} [CommRing S] [Algebra k S]
    (f : Dual k A →ₐ[k] R) (g : R →ₐ[k] S) :
    (Module.Dual.algHomGroupLikeUnitsEquiv k A S (g.comp f)).val =
      Units.map (Algebra.TensorProduct.map g (AlgHom.id k A)).toMonoidHom
        (Module.Dual.algHomGroupLikeUnitsEquiv k A R f).val :=
  Module.Dual.algHomGroupLikeUnitsEquiv_naturality k A R f g
