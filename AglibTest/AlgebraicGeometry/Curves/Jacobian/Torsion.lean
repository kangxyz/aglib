/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Curves.Jacobian.Torsion

/-! The same P/R consumer keeps the original Jacobian, level one and genus zero. -/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry MonoidalCategory MonObj
open scoped CategoryTheory.MonObj
open AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.OverField AlgebraicGeometry.Scheme.OverField.Curve
open AlgebraicGeometry.Scheme.RelativePicard AlgebraicGeometry.Scheme.Group

universe u

attribute [local instance] Over.cartesianMonoidalCategory

variable {k : Type u} [Field k] {X : FScheme k} (hX : Properties X)
  (P : LocallyNoetherianOver (Spec (.of k))) [LocallyOfFiniteType P.obj.hom]
  [IsSeparated P.obj.hom]
  (R : ((locallyNoetherianOverInclusion (Spec (.of k))).op ⋙
    (fppfPicardSheaf X.hom).obj ⋙
      CategoryTheory.forget AddCommGrpCat.{u + 1}).RepresentableBy P)

include hX in
example (n : ℕ) (hn : 0 < n) :
    letI := picardCommGrpObj X.hom P R
    Scheme.Hom.HasLocallyFreeRank ((𝟙 (identityComponentOver P.obj)) ^ n).left
      (n ^ (2 * coherentGenus k X)) :=
  hasLocallyFreeRank_multiplication_identityComponentOver_of_pos hX P R n hn

include hX in
example :
    letI := picardCommGrpObj X.hom P R
    Nonempty (AddSubgroup.torsionBy
      (MultiplicationKernel.geometricPoints (Grp.mk (identityComponentOver P.obj))) (1 : ℤ) ≃+
      (Fin (2 * coherentGenus k X) → ZMod 1)) :=
  nonempty_torsionEquiv_identityComponentOver_of_isUnit hX P R 1 (by simp)

include hX in
example (hg : coherentGenus k X = 0) (n : ℕ) (hn : IsUnit (n : k)) :
    letI := picardCommGrpObj X.hom P R
    Nonempty (AddSubgroup.torsionBy
      (MultiplicationKernel.geometricPoints (Grp.mk (identityComponentOver P.obj))) (n : ℤ) ≃+
      (Fin 0 → ZMod n)) := by
  let := picardCommGrpObj X.hom P R
  have h := nonempty_torsionEquiv_identityComponentOver_of_isUnit hX P R n hn
  rw [hg, Nat.mul_zero] at h
  exact h

include hX in
example (n : ℕ) (hn : IsUnit (n : k)) :
    letI := picardCommGrpObj X.hom P R
    let T := AddSubgroup.torsionBy
      (MultiplicationKernel.geometricPoints (Grp.mk (identityComponentOver P.obj))) (n : ℤ)
    letI : Module (ZMod n) T := AddCommGroup.zmodModule
      (fun x : T => Subtype.ext (AddSubgroup.torsionBy.nsmul_iff.mp x.property))
    Nonempty (Module.Basis (Fin (2 * coherentGenus k X)) (ZMod n) T) :=
  nonempty_torsionBasis_identityComponentOver_of_isUnit hX P R n hn

end
