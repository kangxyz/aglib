/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.AbelianScheme.OverField.Dual.WeilPairing.KernelIso
public import Aglib.AlgebraicGeometry.Picard.Scheme.IdentityComponentBaseChangeGroup
public import Aglib.AlgebraicGeometry.Group.MultiplicationKernel.BaseChange
public import Aglib.AlgebraicGeometry.Group.MultiplicationKernel.Functoriality

/-! The original dual multiplication kernel under field extension. -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
open Scheme.OverField Scheme.Group
open scoped CategoryTheory.MonObj

universe u

namespace AlgebraicGeometry.Scheme.RelativePicard

attribute [local instance] Over.cartesianMonoidalCategory

variable {k : Type u} [Field k] (A : Grp (FScheme k))
  (P : LocallyNoetherianOver (Spec (.of k))) [LocallyOfFiniteType P.obj.hom]
  (R : ((locallyNoetherianOverInclusion (Spec (.of k))).op ⋙ (fppfPicardSheaf A.X.hom).obj ⋙
    CategoryTheory.forget AddCommGrpCat.{u + 1}).RepresentableBy P)
  (K : Type u) [Field K] [Algebra k K]

local notation "scalar" => Spec.algebraMap k K
local notation "F" => Over.pullback scalar
local notation "AK" => Functor.obj (Functor.mapGrp F) A
local notation "PK" => LocallyNoetherianOver.baseChange scalar P
local notation "RK" => baseChangeRepresentableBy A.X.hom scalar P R

local instance : LocallyOfFiniteType (PK).obj.hom :=
  inferInstanceAs (LocallyOfFiniteType (pullback.snd P.obj.hom scalar))

/-- Base change of the original dual multiplication kernel uses the original
Picard component comparison and the original multiplication-kernel comparison. -/
def dualMultiplicationKernelBaseChangeIso (n : ℕ) :
    (F).mapGrp.obj (dualMultiplicationKernel A P R n) ≅ dualMultiplicationKernel AK PK RK n := by
  let := picardCommGrpObj A.X.hom P R
  let := picardCommGrpObj (AK).X.hom PK RK
  let D := picardIdentityComponent A.X.hom P R
  let D' := picardIdentityComponent (AK).X.hom PK RK
  let : IsCommMonObj D := inferInstanceAs (IsCommMonObj (Group.identityComponentOver P.obj))
  let : IsCommMonObj D' := inferInstanceAs (IsCommMonObj (Group.identityComponentOver (PK).obj))
  let H := Grp.mk D
  let H' := Grp.mk D'
  let : IsCommMonObj ((F).mapGrp.obj H).X :=
    MultiplicationKernel.baseChange_isCommMonObj scalar H
  let e : (F).mapGrp.obj H ≅ H' := picardIdentityComponentBaseChangeGroupIso P R K
  exact MultiplicationKernel.baseChangeIso scalar H n ≪≫ MultiplicationKernel.mapIso e n

/-- The dual kernel comparison preserves the original inclusion and the same
Picard component base-change map. -/
theorem dualMultiplicationKernelBaseChangeIso_hom_inclusion (n : ℕ) :
    (dualMultiplicationKernelBaseChangeIso A P R K n).hom.hom.hom ≫
        (dualMultiplicationKernelInclusion AK PK RK n).hom.hom =
      (F).map (dualMultiplicationKernelInclusion A P R n).hom.hom ≫
        (picardIdentityComponentBaseChangeOverIso P R K).hom := by
  let := picardCommGrpObj A.X.hom P R
  let := picardCommGrpObj (AK).X.hom PK RK
  let D := picardIdentityComponent A.X.hom P R
  let D' := picardIdentityComponent (AK).X.hom PK RK
  let : IsCommMonObj D := inferInstanceAs (IsCommMonObj (Group.identityComponentOver P.obj))
  let : IsCommMonObj D' := inferInstanceAs (IsCommMonObj (Group.identityComponentOver (PK).obj))
  let H := Grp.mk D
  let H' := Grp.mk D'
  let : IsCommMonObj ((F).mapGrp.obj H).X :=
    MultiplicationKernel.baseChange_isCommMonObj scalar H
  let e : (F).mapGrp.obj H ≅ H' := picardIdentityComponentBaseChangeGroupIso P R K
  let b := MultiplicationKernel.baseChangeIso scalar H n
  have h :
      (b ≪≫ MultiplicationKernel.mapIso e n).hom ≫ Kernel.inclusion
          (MultiplicationKernel.multiplicationHom H' n) =
        (F).mapGrp.map (Kernel.inclusion (MultiplicationKernel.multiplicationHom H n)) ≫ e.hom := by
    rw [Iso.trans_hom, Category.assoc, MultiplicationKernel.mapIso_hom,
      MultiplicationKernel.map_inclusion, ← Category.assoc,
      MultiplicationKernel.baseChangeIso_hom_inclusion]
  have hraw := congrArg (fun f => f.hom.hom) h
  simp only [Grp.comp_hom_hom] at hraw
  exact hraw

end AlgebraicGeometry.Scheme.RelativePicard
