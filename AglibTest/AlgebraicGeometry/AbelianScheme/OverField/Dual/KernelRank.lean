/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.AbelianScheme.OverField.Dual.KernelRank

/-! Equal degree on the original positive kernels, with no invertibility premise. -/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry MonoidalCategory
open Scheme Scheme.OverField Scheme.RelativePicard

universe u

attribute [local instance] Over.cartesianMonoidalCategory

example {k : Type u} [Field k] (A : FScheme k) [GrpObj A] [IsCommMonObj A]
    [IsHProjective A.hom] [Smooth A.hom] [GeometricallyIntegral A.hom]
    (P : LocallyNoetherianOver (Spec (.of k))) [LocallyOfFiniteType P.obj.hom]
    [IsSeparated P.obj.hom]
    (R : ((locallyNoetherianOverInclusion (Spec (.of k))).op ⋙ (fppfPicardSheaf A.hom).obj ⋙
      CategoryTheory.forget AddCommGrpCat.{u + 1}).RepresentableBy P) (n : ℕ) (hn : 0 < n) :
    letI := picardCommGrpObj A.hom P R
    letI : IsCommMonObj (picardIdentityComponent A.hom P R) :=
      inferInstanceAs (IsCommMonObj (Scheme.Group.identityComponentOver P.obj))
    Scheme.Hom.finiteSchemeDegree k
        (Scheme.Group.MultiplicationKernel.kernelGroup
          (Grp.mk (picardIdentityComponent A.hom P R)) n).X.hom =
      Scheme.Hom.finiteSchemeDegree k
        (Scheme.Group.MultiplicationKernel.kernelGroup (Grp.mk A) n).X.hom :=
  finiteSchemeDegree_multiplicationKernel_picardIdentityComponent_eq A P R n hn
