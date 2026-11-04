/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.AbelianScheme.OverField.Dual.KernelPairing
public import Aglib.AlgebraicGeometry.AbelianScheme.OverField.Dual.Poincare.RigidifiedBaseChange
public import Aglib.AlgebraicGeometry.Picard.Kernel.TorsorCharacter.FieldMultiplier

/-! Field extension of the original normalized Poincare character's multiplier. -/

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

/-- The original normalized Poincare character on the new kernel has the
original multiplier transported along the original Cartesian comparisons. -/
theorem poincareKernelMultiplier_fieldBaseChange
    (ht : tOld ≫ picardIdentityComponentPullback PA RA PB RB q.hom.hom = 1)
    (htK : tNew ≫ picardIdentityComponentPullback (X := (AK).X) (Y := (BK).X)
      PAK RAK PBK RBK (Mon.Hom.hom (InducedCategory.Hom.hom qK)) = 1) :
    let M := (poincarePullback B.X PB RB tOld).bundle
    let a := poincareKernelFrame A B PA RA PB RB q tOld ht
    let N := (poincarePullback (BK).X PBK RBK tNew).bundle
    let c := poincareKernelFrame AK BK PAK RAK PBK RBK qK tNew htK
    let h := familyMapOfHom (Kernel.baseChangeIso scalar q).inv.hom.hom T.obj ≫
      (familyBaseChangeIso (Kernel.group q).X.hom scalar T.obj).hom
    kernelMultiplier qK (Kernel.marking qK) T.obj N c =
      Units.map h.appTop.hom.toMonoidHom
      (kernelMultiplier q (Kernel.marking q) (Told).obj M a) := by
  intro M a N c h
  let M' := pullbackLineBundle (familyBaseChangeIso B.X.hom scalar T.obj).hom M
  let a' := fieldBaseChangeFamilyFrame q T.obj M a
  let M₀ := poincarePullback B.X PB RB tOld
  let M₁ := poincarePullbackOnFieldBaseChange B PB RB K T t
  let eB : pullback (BK).X.hom T.obj.hom ≅ pullback B.X.hom (Told).obj.hom :=
    familyBaseChangeIso B.X.hom scalar T.obj
  have hM : M₁.bundle = pullbackLineBundle eB.hom M₀.bundle := by
    unfold M₁ M₀ poincarePullbackOnFieldBaseChange RigidifiedPair.mapFamily
    rfl
  have hRaw : M₁.bundle.val = M'.val :=
    congrArg (fun L : LineBundle (pullback (BK).X.hom T.obj.hom) => L.val) hM
  let e := (poincarePullbackFieldBaseChangeIso B PB RB K T t).iso
  let he : N.val ≅ M'.val := e ≪≫ eqToIso hRaw
  have h₁ := kernelMultiplier_eq_of_iso qK (Kernel.marking qK) T.obj N c M' he a'
  have h₂ := kernelMultiplier_fieldBaseChange q T.obj M a
  exact h₁.trans h₂

end AlgebraicGeometry.Scheme.RelativePicard
