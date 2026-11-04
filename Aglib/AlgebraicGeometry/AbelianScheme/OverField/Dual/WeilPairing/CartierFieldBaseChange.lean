/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.AbelianScheme.OverField.Dual.Poincare.KernelCharacterBaseChange
public import Aglib.AlgebraicGeometry.AbelianScheme.OverField.Dual.WeilPairing.Character
public import Aglib.AlgebraicGeometry.AbelianScheme.OverField.Dual.WeilPairing.DualKernelBaseChange
public import Aglib.AlgebraicGeometry.Group.CartierDuality.BaseChange.FromCharacter
public import Aglib.AlgebraicGeometry.ProjectiveSpace.BaseChange.Projective

public meta import Lean.Elab.Tactic

/-! Scalar extension of the original Cartier comparison for multiplication kernels. -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
open Scheme.OverField Scheme.Group
open scoped CategoryTheory.MonObj

universe u

namespace AlgebraicGeometry.Scheme.RelativePicard

attribute [local instance] Over.cartesianMonoidalCategory

private theorem precompose_zero_of_original_inclusion
    {C : Type*} [Category C] [CartesianMonoidalCategory C] {X Y D : C} [MonObj D]
    (t : X ⟶ D) (j : Y ⟶ D) (v : X ⟶ Y) (q : D ⟶ D)
    (h : t = v ≫ j) (hz : j ≫ q = 1) : t ≫ q = 1 := by
  rw [h, Category.assoc, hz, MonObj.comp_one]

variable {k : Type u} [Field k] (A : Grp (FScheme k))
  (P : LocallyNoetherianOver (Spec (.of k))) [LocallyOfFiniteType P.obj.hom]
  (R : ((locallyNoetherianOverInclusion (Spec (.of k))).op ⋙ (fppfPicardSheaf A.X.hom).obj ⋙
    CategoryTheory.forget AddCommGrpCat.{u + 1}).RepresentableBy P)
  [IsCommMonObj A.X] [IsHProjective A.X.hom] [GeometricallyIntegral A.X.hom]
  [Smooth A.X.hom] [IsSeparated P.obj.hom]

/-- The original character formula at an identified original Picard point. -/
private theorem characterEquiv_comp_multiplicationKernelCartierHom_of_inclusion
    (n : ℕ) (hn : 0 < n) {T : FScheme k} (t : T ⟶ (dualMultiplicationKernel A P R n).X)
    (p : T ⟶ picardIdentityComponent A.X.hom P R)
    (h : t ≫ (dualMultiplicationKernelInclusion A P R n).hom.hom = p)
    (hp : p ≫ picardIdentityComponentPullback P R P R
      (MultiplicationKernel.multiplicationHom A n).hom.hom = 1) :
    let q := MultiplicationKernel.multiplicationHom A n
    letI : IsFinite q.hom.hom.left :=
      (Multiplication.multiplicationHom_finite_flat_surjective A n hn).1
    letI : IsCommMonObj (Kernel.group q).X := Kernel.isCommMonObj_group q
    CartierDuality.characterEquiv (Kernel.group q) T
        (t ≫ (multiplicationKernelCartierHom A P R n hn).hom.hom) =
      poincareKernelCharacter A A P R P R q p hp := by
  subst p
  exact characterEquiv_comp_multiplicationKernelCartierHom A P R n hn t

variable (K : Type u) [Field K] [Algebra k K]

local notation "scalar" => Spec.algebraMap k K
local notation "F" => Over.pullback scalar
local notation "AK" => Functor.obj (Functor.mapGrp F) A
local notation "PK" => LocallyNoetherianOver.baseChange scalar P
local notation "RK" => baseChangeRepresentableBy A.X.hom scalar P R
local instance : LocallyOfFiniteType (PK).obj.hom :=
  inferInstanceAs (LocallyOfFiniteType (pullback.snd P.obj.hom scalar))
local instance : IsSeparated (PK).obj.hom :=
  inferInstanceAs (IsSeparated (pullback.snd P.obj.hom scalar))
local instance : IsCommMonObj (AK).X := MultiplicationKernel.baseChange_isCommMonObj scalar A
local instance : IsHProjective (AK).X.hom :=
  inferInstanceAs (IsHProjective (pullback.snd A.X.hom scalar))
local instance : GeometricallyIntegral (AK).X.hom :=
  inferInstanceAs (GeometricallyIntegral (pullback.snd A.X.hom scalar))
local instance : Smooth (AK).X.hom := inferInstanceAs (Smooth (pullback.snd A.X.hom scalar))

private theorem scalarCharacterEquiv_of_inclusion
    (n : ℕ) (hn : 0 < n) {T : FScheme K}
    (t : T ⟶ (dualMultiplicationKernel AK PK RK n).X)
    (p : T ⟶ picardIdentityComponent (AK).X.hom PK RK)
    (h : t ≫ (dualMultiplicationKernelInclusion AK PK RK n).hom.hom = p)
    (hp : p ≫ picardIdentityComponentPullback (X := (AK).X) (Y := (AK).X)
      PK RK PK RK (MultiplicationKernel.multiplicationHom AK n).hom.hom = 1) :
    let q := MultiplicationKernel.multiplicationHom AK n
    letI : IsFinite q.hom.hom.left :=
      (Multiplication.multiplicationHom_finite_flat_surjective AK n hn).1
    letI : IsCommMonObj (Kernel.group q).X := Kernel.isCommMonObj_group q
    CartierDuality.characterEquiv (Kernel.group q) T
        (t ≫ (multiplicationKernelCartierHom AK PK RK n hn).hom.hom) =
      poincareKernelCharacter AK AK PK RK PK RK q p hp := by
  let ftK : LocallyOfFiniteType (PK).obj.hom :=
    inferInstanceAs (LocallyOfFiniteType (pullback.snd P.obj.hom scalar))
  let prK : IsHProjective (AK).X.hom :=
    inferInstanceAs (IsHProjective (pullback.snd A.X.hom scalar))
  let giK : GeometricallyIntegral (AK).X.hom :=
    inferInstanceAs (GeometricallyIntegral (pullback.snd A.X.hom scalar))
  let smK : Smooth (AK).X.hom := inferInstanceAs (Smooth (pullback.snd A.X.hom scalar))
  let seK : IsSeparated (PK).obj.hom :=
    inferInstanceAs (IsSeparated (pullback.snd P.obj.hom scalar))
  let coK : IsCommMonObj (AK).X := MultiplicationKernel.baseChange_isCommMonObj scalar A
  exact @characterEquiv_comp_multiplicationKernelCartierHom_of_inclusion K _
    AK PK ftK RK coK prK giK smK seK n hn T t p h hp

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option maxHeartbeats 750000 in
-- Forming the two native characters and applying the universal detector exceeds the default
-- budget. The original character comparison itself is supplied by the preceding theorem.
/-- The original multiplication Cartier map commutes with the original two
kernel comparisons and the original comparison of finite Cartier duals. -/
theorem multiplicationKernelCartierHom_fieldBaseChange (n : ℕ) (hn : 0 < n) :
    let G := MultiplicationKernel.kernelGroup A n
    let GK := MultiplicationKernel.kernelGroup AK n
    let G₀ := (F).mapGrp.obj G
    let fin : IsFinite G.X.hom := Multiplication.kernelGroup_isFinite_of_pos A n hn
    let comm : IsCommMonObj G.X :=
      Kernel.isCommMonObj_group (MultiplicationKernel.multiplicationHom A n)
    let finK : IsFinite GK.X.hom := Multiplication.kernelGroup_isFinite_of_pos AK n hn
    let commK : IsCommMonObj GK.X :=
      Kernel.isCommMonObj_group (MultiplicationKernel.multiplicationHom AK n)
    let fin₀ : IsFinite G₀.X.hom := inferInstanceAs (IsFinite (pullback.snd G.X.hom scalar))
    letI : IsCommMonObj G.X := comm
    let comm₀ : IsCommMonObj G₀.X := MultiplicationKernel.baseChange_isCommMonObj scalar G
    let E := dualMultiplicationKernel A P R n
    let EK := dualMultiplicationKernel AK PK RK n
    let E₀ := (F).mapGrp.obj E
    let L := @CartierDuality.dualGroup k _ G fin comm
    let LK := @CartierDuality.dualGroup K _ GK finK commK
    let L₀ := @CartierDuality.dualGroup K _ G₀ fin₀ comm₀
    let u : G₀ ⟶ GK := (MultiplicationKernel.baseChangeIso scalar A n).hom
    let v : E₀ ⟶ EK := (dualMultiplicationKernelBaseChangeIso A P R K n).hom
    let c : E ⟶ L := multiplicationKernelCartierHom A P R n hn
    let cK : EK ⟶ LK := multiplicationKernelCartierHom AK PK RK n hn
    let d : LK ⟶ L₀ := @CartierDuality.dualMap K _ G₀ GK fin₀ finK comm₀ commK u
    let b : (F).mapGrp.obj L ⟶ L₀ :=
      (@CartierDuality.dualGroupBaseChangeIso k _ K _ G fin comm scalar).hom
    v ≫ cK ≫ d = (F).mapGrp.map c ≫ b := by
  intro G GK G₀ fin comm finK commK fin₀ comm₀ E EK E₀ L LK L₀ u v c cK d b
  let : IsFinite G.X.hom := fin
  let : IsCommMonObj G.X := comm
  let : IsFinite GK.X.hom := finK
  let : IsCommMonObj GK.X := commK
  let : IsFinite G₀.X.hom := fin₀
  let : IsCommMonObj G₀.X := comm₀
  let q := MultiplicationKernel.multiplicationHom A n
  let q' := MultiplicationKernel.multiplicationHom AK n
  let qK := (F).mapGrp.map q
  let hq : qK = q' := MultiplicationKernel.map_multiplicationHom scalar A n
  let : IsFinite E.X.hom := isFinite_dualMultiplicationKernel A P R n hn
  let T : LocallyNoetherianOver (Spec (.of K)) :=
    ⟨(F).obj E.X, inferInstanceAs (IsLocallyNoetherian (pullback E.X.hom scalar))⟩
  let j := (dualMultiplicationKernelInclusion A P R n).hom.hom
  let jK := (dualMultiplicationKernelInclusion AK PK RK n).hom.hom
  let t : T.obj ⟶ (F).obj (picardIdentityComponent A.X.hom P R) := (F).map j
  let tK : T.obj ⟶ picardIdentityComponent (AK).X.hom PK RK :=
    t ≫ (picardIdentityComponentBaseChangeOverIso P R K).hom
  let adj := Over.mapPullbackAdj scalar
  let s : (Over.map scalar).obj T.obj ⟶ E.X := adj.counit.app E.X
  let t₀ := (adj.homEquiv T.obj _).symm t
  let z := v.hom.hom ≫ cK.hom.hom
  let := picardCommGrpObj (AK).X.hom PK RK
  let : GrpObj (Group.identityComponentOver (PK).obj) :=
    Group.grpObjIdentityComponentOver (PK).obj
  have htK : tK = v.hom.hom ≫ jK :=
    (dualMultiplicationKernelBaseChangeIso_hom_inclusion A P R K n).symm
  have hs : (adj.homEquiv T.obj E.X).symm (𝟙 T.obj) = s := by
    apply Over.OverMorphism.ext
    simp only [MultiplicativeBaseChange.pullbackAdj_symm_left, Over.id_left, Category.id_comp,
      s, adj, Over.mapPullbackAdj_counit_app, Over.homMk_left]
  have ht₀ : t₀ = s ≫ j :=
    (adj.homEquiv_naturality_right_symm (𝟙 T.obj) j).trans
      (congrArg (fun x => x ≫ j) hs)
  have h₀ : t₀ ≫ picardIdentityComponentPullback P R P R q.hom.hom = 1 := by
    rw [ht₀, Category.assoc, dualMultiplicationKernelInclusion_comp_pullback, MonObj.comp_one]
  let DK := Group.identityComponentOver (PK).obj
  let monDK : MonObj DK := (Group.grpObjIdentityComponentOver (PK).obj).toMonObj
  let qD : DK ⟶ DK := picardIdentityComponentPullback (X := (AK).X) (Y := (AK).X)
    PK RK PK RK q'.hom.hom
  have zeroK := dualMultiplicationKernelInclusion_comp_pullback AK PK RK n
  have h₁ := @precompose_zero_of_original_inclusion (FScheme K) _ _
    T.obj EK.X DK monDK tK jK v.hom.hom qD htK zeroK
  let FT := Over.pullback T.obj.hom
  have huDef := MultiplicationKernel.baseChangeIso_hom_factor scalar A n
  let pr : IsProper A.X.hom := inferInstance
  let gi : GeometricallyIntegral A.X.hom := inferInstance
  let ft : LocallyOfFiniteType P.obj.hom := inferInstance
  have hGeneric := @poincareKernelCharacter_fieldBaseChange_for_comparison k _ A A pr gi pr gi
    P ft R P ft R q K _ _ T t
  have hGenericMap := hGeneric q' hq
  have hGenericZeros := hGenericMap h₀ h₁
  let u' : G₀ ⟶ GK := (Kernel.baseChangeIso scalar
    (MultiplicationKernel.multiplicationHom A n)).hom ≫
      (eqToIso (congrArg (fun f : AK ⟶ AK => Kernel.group f)
        (MultiplicationKernel.map_multiplicationHom scalar A n))).hom
  have hu := hGenericZeros
  have hc := @characterEquiv_comp_multiplicationKernelCartierHom_of_inclusion k _
    A P ft R _ _ gi _ _ n hn ((Over.map scalar).obj T.obj) s t₀ ht₀.symm h₀
  have hcK := scalarCharacterEquiv_of_inclusion A P R K n hn (T := T.obj)
    v.hom.hom tK htK.symm h₁
  have hFinish := @CartierDuality.dualGroupBaseChangeIso_hom_eq_of_universal_character k K
    _ _ scalar G fin comm GK finK commK E EK u' v c cK
  have hC := hFinish (by
    change FT.mapGrp.map u' ≫ CartierDuality.characterEquiv GK T.obj z =
      (Group.BaseChange.groupSchemeBaseChangeComp T.obj.hom scalar).inv.app G ≫
        CartierDuality.characterEquiv G ((Over.map scalar).obj T.obj) (s ≫ c.hom.hom)
    rw [hc, hcK]
    -- The original comparison already has this type. Use its inferred proof term directly
    -- so the elaborator does not repeat the expensive conversion before kernel checking.
    run_tac Lean.Elab.Tactic.withMainContext do
      let some h := (← Lean.getLCtx).findFromUserName? `hu
        | throwError "Missing the original Poincare character comparison"
      (← Lean.Elab.Tactic.getMainGoal).assign h.toExpr)
  have huNative : u = u' := by
    unfold u u'
    with_reducible exact huDef
  exact (congrArg (fun (f : G₀ ⟶ GK) =>
    v ≫ cK ≫ @CartierDuality.dualMap K _ G₀ GK fin₀ finK comm₀ commK f) huNative).trans hC

end AlgebraicGeometry.Scheme.RelativePicard
