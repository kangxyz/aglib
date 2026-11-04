/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.AbelianScheme.OverField.Dual.WeilPairing.Alternation
public import Aglib.AlgebraicGeometry.Curves.Jacobian.Theta.Descent.GroundPolarization
public import Aglib.AlgebraicGeometry.Curves.Jacobian.WeilPairing

/-! Alternation of the original canonical pairing via the actual based theta class. -/

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

/-- With a given ground-field origin in positive genus, the canonical
Jacobian pairing is alternating on the whole original positive kernel.
This applies in every characteristic and at every positive level. -/
theorem jacobianWeilPairingMorphism_diagonal_of_origin
    (o : Spec (.of k) ⟶ X.left) (ho : o ≫ X.hom = 𝟙 _)
    (hg : 0 < coherentGenus k X) (n : ℕ) (hn : 0 < n) :
    letI := picardCommGrpObj X.hom P R
    let J := picardIdentityComponent X.hom P R
    letI : IsCommMonObj J := inferInstanceAs (IsCommMonObj (Group.identityComponentOver P.obj))
    let T := (MultiplicationKernel.kernelGroup (Grp.mk J) n).X
    MultiplicativeGroup.rootsHomEquiv (Base k) n T
      (lift (𝟙 T) (𝟙 T) ≫ jacobianWeilPairingMorphism hX P R Q RQ n hn) = 1 := by
  let := picardCommGrpObj X.hom P R
  let J := picardIdentityComponent X.hom P R
  let : IsCommMonObj J := inferInstanceAs (IsCommMonObj (Group.identityComponentOver P.obj))
  let : IsHProjective J.hom := isHProjective_identityComponentOver hX P R
  let : GeometricallyIntegral J.hom := geometricallyIntegral_identityComponentOver hX P R
  let : Smooth J.hom := smooth_identityComponentOver hX P R
  let : IsProper J.hom := isProper_identityComponentOver hX P R
  let A := Grp.mk J
  let L := thetaLineBundleGroundField hX o ho P R hg
  let f := lineBundleClassIdentityComponentGroupHom J Q RQ (classOf J.left L)
  let e := canonicalJacobianPrincipalGroupIso hX P R Q RQ
  have hf : f = e.hom := by
    apply Grp.hom_ext
    exact lineBundleClassMorphismIdentityComponent_thetaLineBundleGroundField
      hX o ho P R Q RQ hg
  exact weilPairingMorphismOfPrincipalIso_diagonal_of_lineBundleClass
    A Q RQ L e hf.symm n hn

/-- In genus zero the canonical pairing is alternating without a choice of origin.
The original Jacobian is terminal over the field, so its canonical principal map
is also the map of its original trivial line bundle. -/
theorem jacobianWeilPairingMorphism_diagonal_of_genus_zero
    (hg : coherentGenus k X = 0) (n : ℕ) (hn : 0 < n) :
    letI := picardCommGrpObj X.hom P R
    let J := picardIdentityComponent X.hom P R
    letI : IsCommMonObj J := inferInstanceAs (IsCommMonObj (Group.identityComponentOver P.obj))
    let T := (MultiplicationKernel.kernelGroup (Grp.mk J) n).X
    MultiplicativeGroup.rootsHomEquiv (Base k) n T
      (lift (𝟙 T) (𝟙 T) ≫ jacobianWeilPairingMorphism hX P R Q RQ n hn) = 1 := by
  let := picardCommGrpObj X.hom P R
  let J := picardIdentityComponent X.hom P R
  let : IsCommMonObj J := inferInstanceAs (IsCommMonObj (Group.identityComponentOver P.obj))
  let : IsHProjective J.hom := isHProjective_identityComponentOver hX P R
  let : GeometricallyIntegral J.hom := geometricallyIntegral_identityComponentOver hX P R
  let : Smooth J.hom := smooth_identityComponentOver hX P R
  let : IsProper J.hom := isProper_identityComponentOver hX P R
  let : IsIso J.hom := isIso_identityComponentOver_hom_of_genus_zero hX P R hg
  let A := Grp.mk J
  let L : LineBundle J.left := trivialLineBundle J.left
  let e := canonicalJacobianPrincipalGroupIso hX P R Q RQ
  have he : e.hom = lineBundleClassIdentityComponentGroupHom J Q RQ (classOf J.left L) := by
    apply (cancel_mono e.inv).mp
    apply Grp.hom_ext
    apply Over.OverMorphism.ext
    apply (cancel_mono J.hom).mp
    exact (Over.w _).trans (Over.w _).symm
  exact weilPairingMorphismOfPrincipalIso_diagonal_of_lineBundleClass A Q RQ L e he n hn

end AlgebraicGeometry.Scheme.OverField.Curve
