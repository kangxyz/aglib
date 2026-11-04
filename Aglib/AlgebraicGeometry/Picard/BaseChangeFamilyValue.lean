/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Picard.BaseChangeRepresentableBy

/-! The original family value of a base-changed Picard representer. -/

open CategoryTheory CategoryTheory.Limits Opposite

@[expose] public noncomputable section

namespace AlgebraicGeometry.Scheme.RelativePicard

open Scheme.Modules.Invertible

universe u

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {X S S' : Scheme.{u}} (p : X ⟶ S) (g : S' ⟶ S)
  (P : LocallyNoetherianOver S) [LocallyOfFiniteType P.obj.hom]
  (R : ((locallyNoetherianOverInclusion S).op ⋙ (fppfPicardSheaf p).obj ⋙
    CategoryTheory.forget AddCommGrpCat.{u + 1}).RepresentableBy P)

/-- The original base-changed representing map retains the original family class. -/
theorem baseChangeRepresentableBy_homEquiv_of_family [IsLocallyNoetherian S']
    {T : LocallyNoetherianOver S'}
    (f : T ⟶ LocallyNoetherianOver.baseChange g P)
    (x : PicardGroup (pullback p (T.obj.hom ≫ g)))
    (h : R.homEquiv
      (ObjectProperty.homMk (((Over.mapPullbackAdj g).homEquiv T.obj P.obj).symm f.hom) :
        (LocallyNoetherianOver.map g).obj T ⟶ P) =
      ((quotientProjection p ≫ toFppfPicardSheaf p).app (op ((Over.map g).obj T.obj))).hom x) :
    (baseChangeRepresentableBy p g P R).homEquiv f =
      ((quotientProjection (pullback.snd p g) ≫
        toFppfPicardSheaf (pullback.snd p g)).app (op T.obj)).hom
          (pullbackClass (familyBaseChangeIso p g T.obj).hom x) := by
  rw [baseChangeRepresentableBy_homEquiv, h]
  let E := fppfPicardSheafBaseChangeIso p g
  let F := familyPicardFunctorBaseChangeIso p g
  let U := op T.obj
  let A := (quotientProjection p ≫ toFppfPicardSheaf p).app (op ((Over.map g).obj T.obj))
  let B := (quotientProjection (pullback.snd p g) ≫ toFppfPicardSheaf (pullback.snd p g)).app U
  let y := pullbackClass (familyBaseChangeIso p g T.obj).hom x
  change (E.inv.app U).hom (A.hom x) = B.hom y
  apply (ConcreteCategory.bijective_of_isIso (E.hom.app U)).injective
  have hE : (E.hom.app U).hom ((E.inv.app U).hom (A.hom x)) = A.hom x :=
    congrArg (fun a => a.hom (A.hom x)) (E.inv_hom_id_app U)
  have hF : (F.hom.app U).hom y = x :=
    congrArg (fun a => a.hom x) (F.inv_hom_id_app U)
  have hB : (E.hom.app U).hom (B.hom y) = A.hom ((F.hom.app U).hom y) :=
    congrArg (fun N => (N.app U).hom y)
      (quotientProjection_comp_toFppfPicardSheaf_comp_fppfPicardSheafBaseChangeIso_hom p g)
  exact hE.trans ((congrArg A.hom hF.symm).trans hB.symm)

/-- The original terminal family comparison is the first projection on the actual fibre. -/
theorem familyBaseChangeIso_hom_comp_terminal :
    let T := Over.mk (𝟙 S')
    let q : (Over.map g).obj T ⟶ Over.mk g := Over.homMk (𝟙 S') rfl
    (familyBaseChangeIso p g T).hom ≫ (familyScheme p).map q =
      pullback.fst (pullback.snd p g) (𝟙 S') := by
  intro T q
  apply pullback.hom_ext
  · rw [Category.assoc, familyScheme_map_fst]
    exact familyBaseChangeIso_hom_fst p g T
  · rw [Category.assoc, familyScheme_map_snd, ← Category.assoc]
    have h := familyBaseChangeIso_hom_snd p g T
    exact (congrArg (fun a => a ≫ 𝟙 S') h).trans
      (pullback.condition (f := pullback.snd p g) (g := 𝟙 S')).symm

omit [LocallyOfFiniteType P.obj.hom] in
/-- The original representing bijection respects restriction of a specified family class. -/
theorem homEquiv_comp_of_familyClass
    {T T' : LocallyNoetherianOver S} (d : T' ⟶ T) (a : T ⟶ P)
    (c : PicardGroup (pullback p T.obj.hom))
    (h : R.homEquiv a = ((quotientProjection p ≫ toFppfPicardSheaf p).app (op T.obj)).hom c) :
    R.homEquiv (d ≫ a) =
      ((quotientProjection p ≫ toFppfPicardSheaf p).app (op T'.obj)).hom
        (pullbackClass ((familyScheme p).map d.hom) c) := by
  let N := quotientProjection p ≫ toFppfPicardSheaf p
  have h₁ := R.homEquiv_comp d a
  change R.homEquiv (d ≫ a) = ((fppfPicardSheaf p).obj.map d.hom.op).hom (R.homEquiv a) at h₁
  have h₂ := congrArg (((fppfPicardSheaf p).obj.map d.hom.op).hom) h
  have h₃ := congrArg (fun f => f.hom c) (N.naturality d.hom.op)
  exact h₁.trans (h₂.trans h₃.symm)

end AlgebraicGeometry.Scheme.RelativePicard
