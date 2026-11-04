/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.AbelianScheme.OverField.Dual.Geometry
public import Aglib.AlgebraicGeometry.AbelianScheme.OverField.Multiplication.Rank
public import Aglib.AlgebraicGeometry.Group.IdentityComponent.Commutative
public import Aglib.AlgebraicGeometry.Morphisms.FiniteFlat.FieldRank

/-!
# Structural degree of the original dual multiplication kernels

The original dual geometry and smooth-group dimension theorem identify the
identity cotangent dimensions. The native positive multiplication rank
therefore gives equal degree for the same original kernels in every
characteristic.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry MonoidalCategory
open Scheme.OverField
open scoped CategoryTheory.MonObj

universe u

namespace AlgebraicGeometry.Scheme.RelativePicard

attribute [local instance] Over.cartesianMonoidalCategory

variable {k : Type u} [Field k] (A : FScheme k) [GrpObj A]
  [IsHProjective A.hom] [Smooth A.hom] [GeometricallyIntegral A.hom]
  (P : LocallyNoetherianOver (Spec (.of k))) [LocallyOfFiniteType P.obj.hom]
  [IsSeparated P.obj.hom]
  (R : ((locallyNoetherianOverInclusion (Spec (.of k))).op ⋙ (fppfPicardSheaf A.hom).obj ⋙
    CategoryTheory.forget AddCommGrpCat.{u + 1}).RepresentableBy P)

/-- The same supplied dual has the original source identity cotangent dimension. -/
theorem finrank_identityCotangent_picardIdentityComponent_eq :
    Module.finrank k (Cotangent.Space η[picardIdentityComponent A.hom P R]) =
      Module.finrank k (Cotangent.Space η[A]) := by
  let := picardCommGrpObj A.hom P R
  let D := picardIdentityComponent A.hom P R
  obtain ⟨_, hsm, hint, hdim⟩ :=
    isHProjective_smooth_geometricallyIntegral_picardIdentityComponent A P R
  have : Smooth D.hom := hsm
  have : GeometricallyIntegral D.hom := hint
  have : IsIntegral D.left := GeometricallyIntegral.isIntegral_of_subsingleton D.hom
  have : IsIntegral A.left := GeometricallyIntegral.isIntegral_of_subsingleton A.hom
  have hD := Group.topologicalKrullDim_eq_finrank_identityCotangent_of_preconnected D
  have hA := Group.topologicalKrullDim_eq_finrank_identityCotangent_of_preconnected A
  have heq : (Module.finrank k (Cotangent.Space η[D]) : WithBot ℕ∞) =
      (Module.finrank k (Cotangent.Space η[A]) : WithBot ℕ∞) :=
    hD.symm.trans (hdim.trans hA)
  exact_mod_cast heq

variable [IsCommMonObj A]

/-- The actual positive multiplication kernels of the source and its supplied
original dual have the same structural finite-scheme degree. -/
theorem finiteSchemeDegree_multiplicationKernel_picardIdentityComponent_eq
    (n : ℕ) (hn : 0 < n) :
    letI := picardCommGrpObj A.hom P R
    letI : IsCommMonObj (picardIdentityComponent A.hom P R) :=
      inferInstanceAs (IsCommMonObj (Group.identityComponentOver P.obj))
    Hom.finiteSchemeDegree k
        (Group.MultiplicationKernel.kernelGroup (Grp.mk (picardIdentityComponent A.hom P R))
          n).X.hom =
      Hom.finiteSchemeDegree k (Group.MultiplicationKernel.kernelGroup (Grp.mk A) n).X.hom := by
  let := picardCommGrpObj A.hom P R
  let D := picardIdentityComponent A.hom P R
  let G := Grp.mk A
  let H := Grp.mk D
  have : IsCommMonObj H.X :=
    inferInstanceAs (IsCommMonObj (Group.identityComponentOver P.obj))
  obtain ⟨hproj, hsm, hint, _⟩ :=
    isHProjective_smooth_geometricallyIntegral_picardIdentityComponent A P R
  have : IsHProjective D.hom := hproj
  have : Smooth D.hom := hsm
  have : GeometricallyIntegral D.hom := hint
  have : IsFinite (Group.MultiplicationKernel.kernelGroup G n).X.hom :=
    Group.Multiplication.kernelGroup_isFinite_of_pos G n hn
  have : IsFinite (Group.MultiplicationKernel.kernelGroup H n).X.hom :=
    Group.Multiplication.kernelGroup_isFinite_of_pos H n hn
  have hG := (Hom.hasLocallyFreeRank_iff_finiteSchemeDegree_eq
    (Group.MultiplicationKernel.kernelGroup G n).X _).mp
      (Group.Multiplication.kernelGroup_hasLocallyFreeRank G n hn)
  have hH := (Hom.hasLocallyFreeRank_iff_finiteSchemeDegree_eq
    (Group.MultiplicationKernel.kernelGroup H n).X _).mp
      (Group.Multiplication.kernelGroup_hasLocallyFreeRank H n hn)
  change Hom.finiteSchemeDegree k (Group.MultiplicationKernel.kernelGroup H n).X.hom =
    Hom.finiteSchemeDegree k (Group.MultiplicationKernel.kernelGroup G n).X.hom
  exact hH.trans ((congrArg (fun d : ℕ => n ^ (2 * d))
    (finrank_identityCotangent_picardIdentityComponent_eq A P R)).trans hG.symm)

end AlgebraicGeometry.Scheme.RelativePicard
