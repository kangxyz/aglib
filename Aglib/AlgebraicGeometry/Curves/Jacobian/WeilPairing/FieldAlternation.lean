/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.AbelianScheme.OverField.Dual.WeilPairing.FieldAlternation
public import Aglib.AlgebraicGeometry.Curves.Jacobian.WeilPairing.Alternation

/-! Alternation of the original canonical pairing over its ground field. -/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry MonoidalCategory
open Scheme.RelativePicard Scheme.Group Scheme.Modules.Invertible
open CartesianMonoidalCategory

universe u

namespace AlgebraicGeometry.Scheme.OverField.Curve

attribute [local instance] Over.cartesianMonoidalCategory

variable {k : Type u} [Field k] {X : FScheme k} (hX : Properties X)
  (P : LocallyNoetherianOver (Spec (.of k))) [LocallyOfFiniteType P.obj.hom]
  [IsSeparated P.obj.hom]
  (R : ((locallyNoetherianOverInclusion (Spec (.of k))).op ⋙ (fppfPicardSheaf X.hom).obj ⋙
    CategoryTheory.forget AddCommGrpCat.{u + 1}).RepresentableBy P)
  (Q : LocallyNoetherianOver (Spec (.of k))) [LocallyOfFiniteType Q.obj.hom]
  [IsSeparated Q.obj.hom]
  (RQ : ((locallyNoetherianOverInclusion (Spec (.of k))).op ⋙
    (fppfPicardSheaf (picardIdentityComponent X.hom P R).hom).obj ⋙
      CategoryTheory.forget AddCommGrpCat.{u + 1}).RepresentableBy Q)

/-- The original canonical Jacobian Weil pairing is alternating on the
whole original positive multiplication kernel, over every field. -/
theorem jacobianWeilPairingMorphism_diagonal (n : ℕ) (hn : 0 < n) :
    letI := picardCommGrpObj X.hom P R
    let J := picardIdentityComponent X.hom P R
    letI : IsCommMonObj J := inferInstanceAs (IsCommMonObj (Group.identityComponentOver P.obj))
    let T := (MultiplicationKernel.kernelGroup (Grp.mk J) n).X
    MultiplicativeGroup.rootsHomEquiv (Base k) n T
      (lift (𝟙 T) (𝟙 T) ≫ jacobianWeilPairingMorphism hX P R Q RQ n hn) = 1 := by
  by_cases hg : coherentGenus k X = 0
  · exact jacobianWeilPairingMorphism_diagonal_of_genus_zero hX P R Q RQ hg n hn
  let := picardCommGrpObj X.hom P R
  let J := picardIdentityComponent X.hom P R
  let : IsCommMonObj J := inferInstanceAs (IsCommMonObj (Group.identityComponentOver P.obj))
  let : IsHProjective J.hom := isHProjective_identityComponentOver hX P R
  let : GeometricallyIntegral J.hom := geometricallyIntegral_identityComponentOver hX P R
  let : Smooth J.hom := smooth_identityComponentOver hX P R
  let : IsProper J.hom := isProper_identityComponentOver hX P R
  let K := AlgebraicClosure k
  let A := Grp.mk J
  let e := canonicalJacobianPrincipalGroupIso hX P R Q RQ
  obtain ⟨L, _, hL⟩ := canonicalJacobianPrincipalIso_geometricPositive hX P R Q RQ K
    (Nat.pos_of_ne_zero hg)
  exact weilPairingMorphismOfPrincipalIso_diagonal_of_fieldLineBundle A Q RQ e K L hL n hn

end AlgebraicGeometry.Scheme.OverField.Curve
