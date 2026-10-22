/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Tensor.Monoidal.Sections
public import Mathlib.CategoryTheory.Monoidal.CommMon_

/-!
# Native algebra-object laws detected on original section tensors

This packet is independent of geometric direct-image implementation details.
Given actual sheaf maps with the prescribed section unit and multiplication,
ordinary section monoid laws prove all native internal commutative-monoid laws.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u

open CategoryTheory MonoidalCategory Opposite

namespace AlgebraicGeometry.Scheme.Modules.Algebra

variable {X : Scheme.{u}} (M : X.Modules) [∀ U : X.Opens, CommMonoid Γ(M, U)]
  (one : 𝟙_ X.Modules ⟶ M) (mul : M ⊗ M ⟶ M)
  (hone : ∀ U : X.Opens, one.app U (1 : Γ(X, U)) = (1 : Γ(M, U)))
  (hmul : ∀ (U : X.Opens) (m n : Γ(M, U)),
    mul.app U (moduleTensorSection X M M U m n) = m * n)

/-- Section monoid formulas on the original unit and multiplication imply the native monoid laws. -/
@[instance_reducible]
def monObjOfSectionMonoids : MonObj M where
  one := one
  mul := mul
  one_mul := by
    apply (cancel_epi (λ_ M).inv).mp
    rw [Iso.inv_hom_id]
    apply Scheme.Modules.hom_ext
    intro U
    ext m
    change mul.app U ((one ▷ M).val.app (op U) ((λ_ M).inv.val.app (op U) m)) = m
    exact (congrArg (fun x => mul.app U ((one ▷ M).val.app (op U) x))
      (leftUnitor_inv_moduleTensorSection M U m)).trans
      ((congrArg (mul.app U) (whiskerRight_moduleTensorSection one M U (1 : Γ(X, U)) m)).trans
        ((congrArg (fun a => mul.app U (moduleTensorSection X M M U a m)) (hone U)).trans
          ((hmul U 1 m).trans (_root_.one_mul m))))
  mul_one := by
    apply (cancel_epi (ρ_ M).inv).mp
    rw [Iso.inv_hom_id]
    apply Scheme.Modules.hom_ext
    intro U
    ext m
    change mul.app U ((M ◁ one).val.app (op U) ((ρ_ M).inv.val.app (op U) m)) = m
    exact (congrArg (fun x => mul.app U ((M ◁ one).val.app (op U) x))
      (rightUnitor_inv_moduleTensorSection M U m)).trans
      ((congrArg (mul.app U) (whiskerLeft_moduleTensorSection M one U m (1 : Γ(X, U)))).trans
        ((congrArg (fun a => mul.app U (moduleTensorSection X M M U m a)) (hone U)).trans
          ((hmul U m 1).trans (_root_.mul_one m))))
  mul_assoc := by
    apply moduleTensor_nested_hom_ext_left
    intro U m n p
    have hl : ((mul ▷ M) ≫ mul).app U
        (moduleTensorSection X (M ⊗ M) M U (moduleTensorSection X M M U m n) p) =
        (m * n) * p :=
      (congrArg (mul.app U) (whiskerRight_moduleTensorSection mul M U
        (moduleTensorSection X M M U m n) p)).trans
        ((congrArg (fun a => mul.app U (moduleTensorSection X M M U a p))
          (hmul U m n)).trans (hmul U (m * n) p))
    have hr : ((α_ M M M).hom ≫ (M ◁ mul) ≫ mul).app U
        (moduleTensorSection X (M ⊗ M) M U (moduleTensorSection X M M U m n) p) =
        m * (n * p) :=
      (congrArg (fun x => mul.app U ((M ◁ mul).val.app (op U) x))
        (associator_hom_moduleTensorSection M M M U m n p)).trans
        ((congrArg (mul.app U) (whiskerLeft_moduleTensorSection M mul U m
          (moduleTensorSection X M M U n p))).trans
          ((congrArg (fun a => mul.app U (moduleTensorSection X M M U m a))
            (hmul U n p)).trans (hmul U m (n * p))))
    exact hl.trans ((_root_.mul_assoc m n p).trans hr.symm)

/-- The same section multiplication formula gives native commutativity. -/
theorem isCommMonObjOfSectionMonoids :
    @IsCommMonObj _ _ _ _ M (monObjOfSectionMonoids M one mul hone hmul) := by
  let hMon : MonObj M := monObjOfSectionMonoids M one mul hone hmul
  refine { mul_comm := ?_ }
  apply moduleTensor_hom_ext
  intro U m n
  exact (congrArg (mul.app U) (braiding_hom_moduleTensorSection M M U m n)).trans
    ((hmul U n m).trans ((_root_.mul_comm n m).trans (hmul U m n).symm))

end AlgebraicGeometry.Scheme.Modules.Algebra
