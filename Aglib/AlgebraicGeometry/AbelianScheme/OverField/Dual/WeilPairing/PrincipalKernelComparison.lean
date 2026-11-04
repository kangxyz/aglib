/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.AbelianScheme.OverField.Dual.WeilPairing.DualKernelBaseChange
public import Aglib.AlgebraicGeometry.AbelianScheme.OverField.Dual.WeilPairing.Polarization

/-! Restriction of the transported original principal isomorphism to the original kernels. -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
open Scheme.OverField Scheme.Group
open scoped CategoryTheory.MonObj

universe u

namespace AlgebraicGeometry.Scheme.RelativePicard

attribute [local instance] Over.cartesianMonoidalCategory

variable {k : Type u} [Field k] (A : Grp (FScheme k)) [IsCommMonObj A.X]
  (P : LocallyNoetherianOver (Spec (.of k))) [LocallyOfFiniteType P.obj.hom]
  (R : ((locallyNoetherianOverInclusion (Spec (.of k))).op ⋙ (fppfPicardSheaf A.X.hom).obj ⋙
    CategoryTheory.forget AddCommGrpCat.{u + 1}).RepresentableBy P)
  (e : A ≅ Grp.mk (picardIdentityComponent A.X.hom P R))
  (K : Type u) [Field K] [Algebra k K]

local notation "scalar" => Spec.algebraMap k K
local notation "F" => Over.pullback scalar
local notation "AK" => Functor.obj (Functor.mapGrp F) A
local notation "PK" => LocallyNoetherianOver.baseChange scalar P
local notation "RK" => baseChangeRepresentableBy A.X.hom scalar P R
local instance : LocallyOfFiniteType (PK).obj.hom :=
  inferInstanceAs (LocallyOfFiniteType (pullback.snd P.obj.hom scalar))
local instance : IsCommMonObj (AK).X := MultiplicationKernel.baseChange_isCommMonObj scalar A

/-- The original principal restriction commutes with the original multiplication
kernel and Picard-component comparisons. -/
theorem principalIsoOnMultiplicationKernel_fieldBaseChange (n : ℕ) :
    let eD := picardIdentityComponentBaseChangeGroupIso P R K
    let eK := (F).mapGrp.mapIso e ≪≫ eD
    (MultiplicationKernel.baseChangeIso scalar A n).hom ≫
        (principalIsoOnMultiplicationKernel AK PK RK eK n).hom =
      (F).mapGrp.map (principalIsoOnMultiplicationKernel A P R e n).hom ≫
        (dualMultiplicationKernelBaseChangeIso A P R K n).hom := by
  intro eD eK
  let := picardCommGrpObj A.X.hom P R
  let := picardCommGrpObj (AK).X.hom PK RK
  let DK := picardIdentityComponent (AK).X.hom PK RK
  let : IsCommMonObj DK := inferInstanceAs (IsCommMonObj (Group.identityComponentOver (PK).obj))
  let u := MultiplicationKernel.baseChangeIso scalar A n
  let v := dualMultiplicationKernelBaseChangeIso A P R K n
  let s := principalIsoOnMultiplicationKernel A P R e n
  let sK := principalIsoOnMultiplicationKernel AK PK RK eK n
  let i := Kernel.inclusion (MultiplicationKernel.multiplicationHom A n)
  let iK := Kernel.inclusion (MultiplicationKernel.multiplicationHom AK n)
  let j := dualMultiplicationKernelInclusion A P R n
  let jK := dualMultiplicationKernelInclusion AK PK RK n
  have hu : u.hom ≫ iK = (F).mapGrp.map i :=
    MultiplicationKernel.baseChangeIso_hom_inclusion scalar A n
  have hv : v.hom ≫ jK = (F).mapGrp.map j ≫ eD.hom := by
    apply Grp.hom_ext
    exact dualMultiplicationKernelBaseChangeIso_hom_inclusion A P R K n
  have hs : s.hom ≫ j = i ≫ e.hom :=
    principalIsoOnMultiplicationKernel_hom_inclusion A P R e n
  have hsK : sK.hom ≫ jK = iK ≫ eK.hom :=
    principalIsoOnMultiplicationKernel_hom_inclusion AK PK RK eK n
  apply Kernel.hom_ext_of_inclusion (MultiplicationKernel.multiplicationHom (Grp.mk DK) n)
  change (u.hom ≫ sK.hom) ≫ jK = ((F).mapGrp.map s.hom ≫ v.hom) ≫ jK
  calc
    _ = (u.hom ≫ iK) ≫ eK.hom := (Category.assoc _ _ _).trans
      ((congrArg (fun g => u.hom ≫ g) hsK).trans (Category.assoc _ _ _).symm)
    _ = (F).mapGrp.map (i ≫ e.hom) ≫ eD.hom := by
      unfold eK
      simp only [hu, (F).mapGrp.map_comp, Iso.trans_hom, Functor.mapIso_hom, Category.assoc]
    _ = (F).mapGrp.map s.hom ≫ ((F).mapGrp.map j ≫ eD.hom) := by
      rw [← hs, (F).mapGrp.map_comp, Category.assoc]
    _ = _ := (congrArg (fun g => (F).mapGrp.map s.hom ≫ g) hv.symm).trans
      (Category.assoc _ _ _).symm

end AlgebraicGeometry.Scheme.RelativePicard
