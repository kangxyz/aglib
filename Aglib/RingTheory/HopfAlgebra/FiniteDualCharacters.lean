/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.RingTheory.Coalgebra.FiniteDualCharacters
public import Aglib.RingTheory.HopfAlgebra.FiniteDualEvaluation
public import Mathlib.RingTheory.HopfAlgebra.GroupLike
public import Mathlib.RingTheory.HopfAlgebra.TensorProduct

/-!
# Finite-dual characters as the original group-like units

The native Hopf antipode makes every group-like element a unit. Composing this
canonical unit construction with the finite-coalgebra character equivalence
identifies algebra maps from the dual with the original group-like units over
an arbitrary coefficient algebra. Both the value and coefficient naturality
remain the original coevaluation and tensor maps.
-/

@[expose] public section

noncomputable section

open Module
open scoped TensorProduct Module.Dual.FiniteDual

namespace GroupLike

variable (R A : Type*) [CommRing R] [Ring A] [HopfAlgebra R A]

/-- Group-like elements are exactly the original units whose values are group-like. -/
def unitsEquiv : GroupLike R A ≃ {u : Aˣ // IsGroupLikeElem R (u : A)} where
  toFun a := ⟨GroupLike.toUnits R a, a.2⟩
  invFun u := ⟨u.val, u.2⟩
  left_inv a := by apply GroupLike.val_injective; rfl
  right_inv u := by apply Subtype.ext; apply Units.ext; rfl

@[simp]
theorem unitsEquiv_val (a : GroupLike R A) : ((unitsEquiv R A a).val : A) = a.val := rfl

end GroupLike

namespace Module.Dual

section TensorMap

variable (k A R : Type*) [Field k] [Ring A] [Algebra k A] [Coalgebra k A]
  [CommRing R] [Algebra k R]

/-- The actual tensor-algebra map contracting the dual factor with a character. -/
def characterTensorHom (f : Dual k A →ₐ[k] R) : A ⊗[k] Dual k A →ₐ[k] R ⊗[k] A :=
  (Algebra.TensorProduct.map f (AlgHom.id k A)).comp
    (Algebra.TensorProduct.comm k A (Dual k A)).toAlgHom

/-- The character tensor map is exactly native linear contraction followed by the swap. -/
theorem characterTensorHom_apply (f : Dual k A →ₐ[k] R) (z : A ⊗[k] Dual k A) :
    characterTensorHom k A R f z =
      TensorProduct.comm k A R (f.toLinearMap.lTensor A z) := by
  induction z using TensorProduct.inductionOn with
  | tmul a g => rfl
  | add x y hx hy => simp only [map_add, hx, hy]

end TensorMap

variable (k A R : Type*) [Field k] [Ring A] [HopfAlgebra k A]
  [FiniteDimensional k A] [CommRing R] [Algebra k R]

/-- The actual finite-dual character correspondence, valued in native group-like units. -/
def algHomGroupLikeUnitsEquiv :
    (Dual k A →ₐ[k] R) ≃ {u : (R ⊗[k] A)ˣ // IsGroupLikeElem R (u : R ⊗[k] A)} :=
  (algHomGroupLikeEquiv k A R).trans (GroupLike.unitsEquiv R (R ⊗[k] A))

/-- The character unit has exactly the original contracted coevaluation as its value. -/
theorem algHomGroupLikeUnitsEquiv_val (f : Dual k A →ₐ[k] R) :
    ((algHomGroupLikeUnitsEquiv k A R f).val : R ⊗[k] A) =
      TensorProduct.comm k A R (f.toLinearMap.lTensor A (coevaluation k A 1)) :=
  algHomGroupLikeEquiv_val k A R f

/-- The whole character unit is the image of the literal universal coevaluation unit. -/
theorem algHomGroupLikeUnitsEquiv_eq_map_coevaluationUnit (f : Dual k A →ₐ[k] R) :
    (algHomGroupLikeUnitsEquiv k A R f).val =
      Units.map (characterTensorHom k A R f).toMonoidHom
        (HopfAlgebra.coevaluationUnit k A) := by
  apply Units.ext
  change ((algHomGroupLikeUnitsEquiv k A R f).val : R ⊗[k] A) =
    characterTensorHom k A R f (coevaluation k A 1)
  rw [algHomGroupLikeUnitsEquiv_val, characterTensorHom_apply]

/-- The character unit commutes with the actual scalar map on the tensor algebra. -/
theorem algHomGroupLikeUnitsEquiv_naturality {S : Type*} [CommRing S] [Algebra k S]
    (f : Dual k A →ₐ[k] R) (g : R →ₐ[k] S) :
    (algHomGroupLikeUnitsEquiv k A S (g.comp f)).val =
      Units.map (Algebra.TensorProduct.map g (AlgHom.id k A)).toMonoidHom
        (algHomGroupLikeUnitsEquiv k A R f).val := by
  apply Units.ext
  exact algHomGroupLikeEquiv_naturality k A R f g

end Module.Dual
