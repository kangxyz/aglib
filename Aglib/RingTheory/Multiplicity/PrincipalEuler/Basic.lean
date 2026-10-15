/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.Length.ExactSequence
public import Aglib.RingTheory.ScalarHomology.Basic
public import Mathlib.LinearAlgebra.Isomorphisms
public import Mathlib.LinearAlgebra.TensorProduct.RightExactness

/-!
# Principal Euler expressions and finite-length cancellation

Supporting original Grayson principal-face/local-length prerequisites for
`K2-018#prop:k2018-arithmetic-characters`
(`research/exposes/K2/018/expose.tex`), source snapshot
`e73d98b1b5c1e5abcdebf7d058e436d792b87982`.

Encoded generic subset: A is a commutative ring and N an arbitrary A-module,
in separate Lean universes. If Module.length A N is not infinity, every
endomorphism has equal kernel and cokernel ENat lengths, and the principal
Euler expression vanishes. The expression itself is defined for arbitrary N
as the difference of the two integer casts of ENat.toNat. Scalar regularity
IsSMulRegular N t makes it the integer cast of the quotient length's toNat;
it supplies no finite-cokernel-length conclusion. A genuine finite-length
interpretation retains the relevant finite-length hypotheses. No Noetherian,
domain or flatness assumption is imposed by these generic declarations.

This is a supporting cancellation/regularity prerequisite, not the weighted
prime-filtration formula, an original-object face-cycle equality, or a full
motivic/arithmetic-character comparison.

## Extraction basis

Transferred from `R5Lab.RingTheory.LocalLength.PrincipalEuler` at source revision
`95a3772b895fbc19a81684be4ffd519d0fdcd6b3`, SHA-256
`d15099f8ac6ef7764769d54446a0995386aec85b1b6770c405de472eb9fde981`.
The source interface retains its objects, maps and assumptions under native
mathematical declaration namespaces.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
namespace Module
universe u v
variable {A : Type u} [CommRing A] {N : Type v} [AddCommGroup N] [Module A N]

/-- Integer scalar Euler expression formed from ENat.toNat casts of the cokernel and kernel
lengths. It is defined without finite-length hypotheses.

Source mapping: supporting generalized local construction for
`K2-018#prop:k2018-arithmetic-characters`, source snapshot
`e73d98b1b5c1e5abcdebf7d058e436d792b87982`.
Encoded prerequisite subset: the integer expression obtained from the two ENat.toNat
casts for scalar cokernel and kernel lengths on arbitrary N; no finite-length condition
is assumed by the definition. -/
def principalEuler (t : A) : ℤ :=
  ((Module.length A (N ⧸ LinearMap.range (LinearMap.lsmul A N t))).toNat : ℤ) -
    ((Module.length A (LinearMap.ker (LinearMap.lsmul A N t))).toNat : ℤ)

theorem principalEuler_zero_of_finite_length (t : A) (hN : Module.length A N ≠ ⊤) :
    principalEuler (N := N) t = 0 := by
  unfold principalEuler
  rw [length_kernel_eq_cokernel (LinearMap.lsmul A N t) hN, sub_self]

/-- On a module where the principal element is scalar-regular, the Euler expression reduces
to the integer cast of the quotient ENat length's toNat. Finite quotient length is a
separate obligation.

Source mapping: supporting generalized local construction for
`K2-018#prop:k2018-arithmetic-characters`, source snapshot
`e73d98b1b5c1e5abcdebf7d058e436d792b87982`.
Encoded prerequisite subset: IsSMulRegular N t removes the scalar kernel contribution
and gives the quotient ENat length's toNat integer cast; finite quotient length remains
a separate condition. -/
theorem principalEuler_of_regular (t : A) (ht : IsSMulRegular N t) :
    principalEuler (N := N) t =
      ((Module.length A (N ⧸ LinearMap.range (LinearMap.lsmul A N t))).toNat : ℤ) := by
  have hs : Subsingleton (LinearMap.ker (LinearMap.lsmul A N t)) := by
    refine ⟨fun x y => Subtype.ext ?_⟩
    exact ht (x.property.trans y.property.symm)
  have hz : Module.length A (LinearMap.ker (LinearMap.lsmul A N t)) = 0 :=
    Module.length_eq_zero_iff.mpr hs
  simp only [principalEuler, hz, ENat.toNat_zero, Nat.cast_zero, sub_zero]

/-- The two homology terms defining the principal Euler integer have finite
length. This property does not assert regularity of the principal scalar. -/
def FinitePrincipal (N : Type*) [AddCommGroup N] [Module A N] (t : A) : Prop :=
  Module.length A (ScalarKernel N t) ≠ ⊤ ∧
    Module.length A (ScalarCokernel N t) ≠ ⊤

theorem finitePrincipal_of_regular (N : Type*) [AddCommGroup N] [Module A N]
    (t : A) (hr : IsSMulRegular N t)
    (hc : Module.length A (ScalarCokernel N t) ≠ ⊤) : FinitePrincipal N t := by
  let : Subsingleton (ScalarKernel N t) := ⟨fun x y => Subtype.ext
    (hr (x.property.trans y.property.symm))⟩
  refine ⟨?_, hc⟩
  simp only [Module.length_eq_zero, ne_eq, ENat.zero_ne_top, not_false_eq_true]

end Module
