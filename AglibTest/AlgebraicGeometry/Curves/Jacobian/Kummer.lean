/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Curves.Jacobian.Kummer

/-! The original proper Kummer map and the same supplied P/R are retained. -/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry MonoidalCategory MonObj
open scoped CategoryTheory.MonObj
open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.OverField
open AlgebraicGeometry.Scheme.OverField.Curve AlgebraicGeometry.Scheme.RelativePicard
open AlgebraicGeometry.Scheme.Group AlgebraicGeometry.Scheme.EtaleCohomology
open GroupCohomology.Kummer.Coefficients

universe u w

attribute [local instance] Over.cartesianMonoidalCategory hasSheafifyLarge

variable {k : Type u} [Field k] [IsAlgClosed k] {X : FScheme k} (hX : Properties X)
  (P : LocallyNoetherianOver (Spec (.of k))) [LocallyOfFiniteType P.obj.hom]
  [IsSeparated P.obj.hom]
  (R : ((locallyNoetherianOverInclusion (Spec (.of k))).op ⋙
    (fppfPicardSheaf X.hom).obj ⋙
      CategoryTheory.forget AddCommGrpCat.{u + 1}).RepresentableBy P)
  [HasExt.{w} (AbelianSheaf.{u, u + 1} X.left)]

example (n : ℕ) (hn : 0 < n) (hunit : IsUnit (n : k)) :
    letI := picardCommGrpObj X.hom P R
    Nonempty (Sheaf.H.{w} (mu X.left n) 1 ≃+ AddSubgroup.torsionBy
      (Additive (𝟙_ (Over (Spec (.of k))) ⟶ identityComponentOver P.obj)) (n : ℤ)) :=
  ⟨rootsOneJacobianTorsionAddEquiv hX P R n hn hunit⟩

example :
    letI := picardCommGrpObj X.hom P R
    Nat.card (AddSubgroup.torsionBy
      (Additive (𝟙_ (Over (Spec (.of k))) ⟶ identityComponentOver P.obj)) (1 : ℤ)) = 1 := by
  let := picardCommGrpObj X.hom P R
  exact (card_rationalTorsion_identityComponentOver_of_isUnit hX P R 1
    (by simpa only [Nat.cast_one] using (isUnit_one : IsUnit (1 : k)))).trans (one_pow _)

example (n : ℕ) (hn : 0 < n) (hunit : IsUnit (n : k))
    (x : Sheaf.H.{w} (mu X.left n) 1) :
    letI := picardCommGrpObj X.hom P R
    (rootsOneJacobianTorsionAddEquiv hX P R n hn hunit x).val.toMul ≫
      identityComponentι P.obj = picardPoint P R (Kummer.rootsPicardMap X.left n x) :=
  congrFun (rootsOneJacobianTorsionAddEquiv_comp_inclusion hX P R n hn hunit) x

end
