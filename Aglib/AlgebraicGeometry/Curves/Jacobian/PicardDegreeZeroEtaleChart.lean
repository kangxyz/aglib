/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Curves.Jacobian.PicardDegreeZeroEtale
public import Aglib.AlgebraicGeometry.EtaleCohomology.Kummer.RelativePicardSheaf.NormalizedBaseChangeChart

/-! The original normalized family values on Jacobian étale charts. -/

open CategoryTheory CategoryTheory.Limits Opposite
open MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.MonObj

@[expose] public noncomputable section

namespace CategoryTheory.Adjunction

variable {C D : Type*} [Category* C] [Category* D] {F : C ⥤ D} {G : D ⥤ C}

/-- The original transpose retains the given original right-functor morphism. -/
theorem homEquiv_symm_comp_of_map_eq (adj : F ⊣ G)
    {T : C} {X Y : D} (a : F.obj T ⟶ X) (b : X ⟶ Y)
    (m : G.obj X ⟶ G.obj Y) (h : m = G.map b) :
    (adj.homEquiv T Y).symm ((adj.homEquiv T X) a ≫ m) = a ≫ b := by
  subst m
  rw [adj.homEquiv_naturality_right_symm, Equiv.symm_apply_apply]

end CategoryTheory.Adjunction

namespace AlgebraicGeometry.Scheme.OverField.Curve

open Scheme.RelativePicard Scheme.Group Scheme.EtaleCohomology Scheme.Group.BaseChange
open Scheme.Modules.Invertible

universe u

attribute [local instance] Over.cartesianMonoidalCategory hasSheafifyLarge
  groupSchemeBaseChange_isCommMonObj

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {k : Type u} [Field k] {X : FScheme k}
  (P : LocallyNoetherianOver (Base k)) [LocallyOfFiniteType P.obj.hom]
  (R : ((locallyNoetherianOverInclusion (Base k)).op ⋙ (fppfPicardSheaf X.hom).obj ⋙
    CategoryTheory.forget AddCommGrpCat.{u + 1}).RepresentableBy P)
  {S : Scheme.{u}} [IsLocallyNoetherian S] (f : S ⟶ Base k)
  (U : S.Etale)

set_option hygiene false in
local notation "T" => Kummer.locallyNoetherianEtaleTest U
set_option hygiene false in
local notation "T'" => (LocallyNoetherianOver.map f).obj (T)
set_option hygiene false in
local notation "Q" => LocallyNoetherianOver.baseChange f P

/-- The original point of the base-changed Jacobian is the original transpose. -/
abbrev jacobianEtaleChartPoint
    (t : letI := picardCommGrpObj X.hom P R
      (T').obj ⟶ picardIdentityComponent X.hom P R) :=
  letI := picardCommGrpObj X.hom P R
  ((Over.mapPullbackAdj f).homEquiv (T).obj (picardIdentityComponent X.hom P R)) t

/-- The original chart point followed by the group inclusion transposes to
the original included point. -/
abbrev jacobianEtaleChartPointAdjunctInclusion
    (t : letI := picardCommGrpObj X.hom P R
      (T').obj ⟶ picardIdentityComponent X.hom P R) :=
  letI := picardCommGrpObj X.hom P R
  let i := picardIdentityComponentGroupInclusion P R
  let m := picardDegreeZeroEtaleGroupInclusion P R f
  let A := Over.mapPullbackAdj f
  Adjunction.homEquiv_symm_comp_of_map_eq A t i.hom.hom m.hom.hom
    (picardDegreeZeroEtaleGroupInclusion_hom P R f)

variable (o : S ⟶ pullback X.hom f) (ho : o ≫ pullback.snd X.hom f = 𝟙 S)
  [IsProper (pullback.snd X.hom f)] [Flat (pullback.snd X.hom f)]
  [GeometricallyIntegral (pullback.snd X.hom f)]

set_option maxHeartbeats 400000 in
-- The original normalized chart equality compares two nested étale sheaf
-- adjunctions. Kernel conversion at these concrete types exceeds the default budget.
/-- The original normalized chart map evaluates any supplied original
degree-zero family on the same chart. -/
abbrev jacobianEtaleChartPointNormalizedValue
    (t : letI := picardCommGrpObj X.hom P R
      (T').obj ⟶ picardIdentityComponent X.hom P R)
    (c : PicardGroup (pullback X.hom (U.hom ≫ f)))
    (hc : letI := picardCommGrpObj X.hom P R
      R.homEquiv (ObjectProperty.homMk (t ≫ identityComponentι P.obj) : T' ⟶ P) =
        ((quotientProjection X.hom ≫ toFppfPicardSheaf X.hom).app (op (T').obj)).hom c) :=
  letI := picardCommGrpObj X.hom P R
  let J := picardIdentityComponent X.hom P R
  letI : IsCommMonObj J := inferInstanceAs (IsCommMonObj (identityComponentOver P.obj))
  let m := picardDegreeZeroEtaleGroupInclusion P R f
  let x := jacobianEtaleChartPoint P R f U t
  let ht := jacobianEtaleChartPointAdjunctInclusion P R f U t
  Kummer.picardNormalizedChartBaseChangeOfAdjointValue X.hom f o ho P R U m x c
    (t ≫ identityComponentι P.obj) ht hc

end AlgebraicGeometry.Scheme.OverField.Curve
