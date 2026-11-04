/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.AbelianScheme.OverField.Dual.WeilPairing.Polarization
public import Aglib.AlgebraicGeometry.Curves.Jacobian.Theta.CanonicalPrincipal

/-! The canonical Weil pairing on the original Jacobian, over the ground field. -/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry MonoidalCategory
open Scheme.RelativePicard Scheme.Group

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

/-- The original positive-level Weil pairing transported by the canonical
principal isomorphism of the original Jacobian. No curve origin is needed. -/
def jacobianWeilPairingMorphism (n : ℕ) (hn : 0 < n) :
    letI := picardCommGrpObj X.hom P R
    let J := picardIdentityComponent X.hom P R
    letI : IsCommMonObj J := inferInstanceAs (IsCommMonObj (Group.identityComponentOver P.obj))
    let G := MultiplicationKernel.kernelGroup (Grp.mk J) n
    G.X ⊗ G.X ⟶ MultiplicativeGroup.rootsScheme (Base k) n := by
  let := picardCommGrpObj X.hom P R
  let J := picardIdentityComponent X.hom P R
  let : IsCommMonObj J := inferInstanceAs (IsCommMonObj (Group.identityComponentOver P.obj))
  let : IsHProjective J.hom := isHProjective_identityComponentOver hX P R
  let : GeometricallyIntegral J.hom := geometricallyIntegral_identityComponentOver hX P R
  let : Smooth J.hom := smooth_identityComponentOver hX P R
  exact weilPairingMorphismOfPrincipalIso (Grp.mk J) Q RQ
    (canonicalJacobianPrincipalGroupIso hX P R Q RQ) n hn

end AlgebraicGeometry.Scheme.OverField.Curve
