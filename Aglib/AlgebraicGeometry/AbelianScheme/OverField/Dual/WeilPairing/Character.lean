/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.AbelianScheme.OverField.Dual.WeilPairing.KernelIso

/-! The Weil character is the same positive Poincare character on every test. -/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry MonoidalCategory
open Scheme.OverField Scheme.Group
open scoped CategoryTheory.MonObj

universe u

namespace AlgebraicGeometry.Scheme.RelativePicard

attribute [local instance] Over.cartesianMonoidalCategory

variable {k : Type u} [Field k] (A : Grp (FScheme k))
  (P : LocallyNoetherianOver (Spec (.of k))) [LocallyOfFiniteType P.obj.hom]
  (R : ((locallyNoetherianOverInclusion (Spec (.of k))).op ⋙ (fppfPicardSheaf A.X.hom).obj ⋙
    CategoryTheory.forget AddCommGrpCat.{u + 1}).RepresentableBy P)
  [IsHProjective A.X.hom] [GeometricallyIntegral A.X.hom] [Smooth A.X.hom]
  [IsSeparated P.obj.hom] [IsCommMonObj A.X]

/-- On every original test, the adjoint of the Weil pairing gives the character
of the same normalized Poincare trivialization. -/
theorem characterEquiv_comp_multiplicationKernelCartierHom
    (n : ℕ) (hn : 0 < n) {T : FScheme k} (t : T ⟶ (dualMultiplicationKernel A P R n).X) :
    let q := MultiplicationKernel.multiplicationHom A n
    letI : IsFinite q.hom.hom.left :=
      (Multiplication.multiplicationHom_finite_flat_surjective A n hn).1
    letI : IsCommMonObj (Kernel.group q).X := Kernel.isCommMonObj_group q
    let j := dualMultiplicationKernelInclusion A P R n
    CartierDuality.characterEquiv (Kernel.group q) T
        (t ≫ (multiplicationKernelCartierHom A P R n hn).hom.hom) =
      poincareKernelCharacter A A P R P R q (t ≫ j.hom.hom)
        (by rw [Category.assoc, dualMultiplicationKernelInclusion_comp_pullback A P R n,
          MonObj.comp_one]) := by
  let q := MultiplicationKernel.multiplicationHom A n
  let : IsFinite q.hom.hom.left :=
    (Multiplication.multiplicationHom_finite_flat_surjective A n hn).1
  let : IsCommMonObj (Kernel.group q).X := Kernel.isCommMonObj_group q
  let E := dualMultiplicationKernel A P R n
  let : IsFinite E.X.hom := isFinite_dualMultiplicationKernel A P R n hn
  let j := dualMultiplicationKernelInclusion A P R n
  exact characterEquiv_comp_poincareKernelCartierMap A A P R P R q E j
    (dualMultiplicationKernelInclusion_comp_pullback A P R n) t

end AlgebraicGeometry.Scheme.RelativePicard
