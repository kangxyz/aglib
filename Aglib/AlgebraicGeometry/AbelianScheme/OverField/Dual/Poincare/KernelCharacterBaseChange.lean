/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.AbelianScheme.OverField.Dual.Poincare.KernelMultiplierBaseChange
public import Aglib.AlgebraicGeometry.Picard.Kernel.TorsorCharacter.FieldCharacter

/-! Scalar extension of the original Poincare kernel character. -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
open Scheme.OverField Scheme.Cohomology Scheme.Group Scheme.Modules.Invertible
open scoped CategoryTheory.MonObj

universe u

namespace AlgebraicGeometry.Scheme.RelativePicard

attribute [local instance] Over.cartesianMonoidalCategory

variable {k : Type u} [Field k] (A B : Grp (FScheme k))
  [IsProper A.X.hom] [GeometricallyIntegral A.X.hom]
  [IsProper B.X.hom] [GeometricallyIntegral B.X.hom]
  (PA : LocallyNoetherianOver (Spec (.of k))) [LocallyOfFiniteType PA.obj.hom]
  (RA : ((locallyNoetherianOverInclusion (Spec (.of k))).op ⋙ (fppfPicardSheaf A.X.hom).obj ⋙
    CategoryTheory.forget AddCommGrpCat.{u + 1}).RepresentableBy PA)
  (PB : LocallyNoetherianOver (Spec (.of k))) [LocallyOfFiniteType PB.obj.hom]
  (RB : ((locallyNoetherianOverInclusion (Spec (.of k))).op ⋙ (fppfPicardSheaf B.X.hom).obj ⋙
    CategoryTheory.forget AddCommGrpCat.{u + 1}).RepresentableBy PB)
  (q : A ⟶ B) (K : Type u) [Field K] [Algebra k K]
  (T : LocallyNoetherianOver (Spec (.of K)))
  (t : T.obj ⟶ fieldBaseChange K (picardIdentityComponent B.X.hom PB RB))

local notation "scalar" => Spec.algebraMap k K
local notation "F" => Over.pullback scalar
local notation "AK" => Functor.obj (Functor.mapGrp F) A
local notation "BK" => Functor.obj (Functor.mapGrp F) B
local notation "qK" => CategoryTheory.Functor.map (Functor.mapGrp F) q
local notation "PAK" => LocallyNoetherianOver.baseChange scalar PA
local notation "PBK" => LocallyNoetherianOver.baseChange scalar PB
local notation "RAK" => baseChangeRepresentableBy A.X.hom scalar PA RA
local notation "RBK" => baseChangeRepresentableBy B.X.hom scalar PB RB
local notation "Told" => Functor.obj (LocallyNoetherianOver.map scalar) T
local notation "tOld" => Equiv.symm
  (Adjunction.homEquiv (Over.mapPullbackAdj scalar) T.obj (picardIdentityComponent B.X.hom PB RB)) t
local notation "tNew" =>
  t ≫ CategoryTheory.Iso.hom (picardIdentityComponentBaseChangeOverIso PB RB K)

local instance : IsProper (AK).X.hom := inferInstanceAs (IsProper (pullback.snd A.X.hom scalar))
local instance : GeometricallyIntegral (AK).X.hom :=
  inferInstanceAs (GeometricallyIntegral (pullback.snd A.X.hom scalar))
local instance : IsProper (BK).X.hom := inferInstanceAs (IsProper (pullback.snd B.X.hom scalar))
local instance : GeometricallyIntegral (BK).X.hom :=
  inferInstanceAs (GeometricallyIntegral (pullback.snd B.X.hom scalar))
local instance : LocallyOfFiniteType (PAK).obj.hom :=
  inferInstanceAs (LocallyOfFiniteType (pullback.snd PA.obj.hom scalar))
local instance : LocallyOfFiniteType (PBK).obj.hom :=
  inferInstanceAs (LocallyOfFiniteType (pullback.snd PB.obj.hom scalar))

/-- The original kernel character commutes with scalar extension through the
kernel comparison for the supplied equality of group homomorphisms. -/
theorem poincareKernelCharacter_fieldBaseChange_of_map_eq
    (q' : AK ⟶ BK) (h : qK = q')
    (ht : tOld ≫ picardIdentityComponentPullback PA RA PB RB q.hom.hom = 1)
    (htK' : tNew ≫ picardIdentityComponentPullback (X := (AK).X) (Y := (BK).X)
      PAK RAK PBK RBK q'.hom.hom = 1)
    (u : ((F).mapGrp.obj (Kernel.group q)) ⟶ Kernel.group q')
    (hu : u = (Kernel.baseChangeIso scalar q).hom ≫
      (eqToIso (congrArg (fun f => Kernel.group f) h)).hom) :
    (Over.pullback T.obj.hom).mapGrp.map u ≫
        poincareKernelCharacter AK BK PAK RAK PBK RBK q' tNew htK' =
      (Group.BaseChange.groupSchemeBaseChangeComp T.obj.hom scalar).inv.app (Kernel.group q) ≫
        poincareKernelCharacter A B PA RA PB RB q tOld ht := by
  subst q'
  have hu' : u = (Kernel.baseChangeIso scalar q).hom :=
    hu.trans (Category.comp_id _)
  clear hu
  subst u
  unfold poincareKernelCharacter
  with_reducible
    refine kernelTrivializationCharacter_fieldBaseChange_of_multiplier
      (k := k) (K := K) (A := A) (B := B) q T.obj _ _ _ _ ?_
  have hm := poincareKernelMultiplier_fieldBaseChange A B PA RA PB RB q K T t ht htK'
  dsimp only at hm
  exact hm

/-- Use the literal canonical comparison and its equality transport on
the two original kernels. -/
theorem poincareKernelCharacter_fieldBaseChange_for_comparison
    (q' : AK ⟶ BK) (h : qK = q')
    (ht : tOld ≫ picardIdentityComponentPullback PA RA PB RB q.hom.hom = 1)
    (htK' : tNew ≫ picardIdentityComponentPullback (X := (AK).X) (Y := (BK).X)
      PAK RAK PBK RBK q'.hom.hom = 1) :
    (Over.pullback T.obj.hom).mapGrp.map
        ((Kernel.baseChangeIso scalar q).hom ≫
          (eqToIso (congrArg (fun f => Kernel.group f) h)).hom) ≫
        poincareKernelCharacter AK BK PAK RAK PBK RBK q' tNew htK' =
      (Group.BaseChange.groupSchemeBaseChangeComp T.obj.hom scalar).inv.app (Kernel.group q) ≫
        poincareKernelCharacter A B PA RA PB RB q tOld ht :=
  poincareKernelCharacter_fieldBaseChange_of_map_eq A B PA RA PB RB q K T t q' h ht htK' _ rfl

end AlgebraicGeometry.Scheme.RelativePicard
