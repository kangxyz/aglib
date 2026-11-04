/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.H1.RepresentedKernel.CoverTerminalPullback
public import Aglib.AlgebraicGeometry.Curves.Jacobian.WeilPairing.AbelKummer
public import Aglib.AlgebraicGeometry.EtaleCohomology.Kummer.TerminalCoverRootBoundary
public import Aglib.AlgebraicGeometry.Picard.Kernel.TorsorCharacter.FramePushout

/-! The original Abel boundary pushed along the positive original Weil character. -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open MonoidalCategory CartesianMonoidalCategory
open Scheme.OverField Scheme.Group Scheme.Group.BaseChange Scheme.EtaleCohomology
open Scheme.EtaleCohomology.RepresentedKernel Scheme.Group.MultiplicativeGroup
open scoped CategoryTheory.MonObj

namespace AlgebraicGeometry.Scheme.RelativePicard.KernelFramePushout

attribute [local instance] Over.cartesianMonoidalCategory hasSheafifyLarge
  Kernel.isCommMonObj_group groupSchemeBaseChange_isCommMonObj familyCoefficient_isCommMonObj

universe u wX wZ

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {k : Type u} [Field k] {A B : Grp (FScheme k)} (q : A ⟶ B)
  [IsCommMonObj A.X] [IsCommMonObj B.X]
  [IsFinite q.hom.hom.left] [Etale q.hom.hom.left] [Surjective q.hom.hom.left]
  {X : FScheme k} (a : X ⟶ B.X)

set_option hygiene false in
local notation "T₀" => (𝟙_ (FScheme k))
set_option hygiene false in
local notation "B₀" => Group.BaseChange.baseChangedGroup (T₀).hom B

variable [hBExt : HasExt.{wX} (AbelianSheaf.{u, u + 1} (B₀).X.left)]
  [HasExt.{wZ} (AbelianSheaf.{u, u + 1} X.left)]

/-- The original direct graph boundary with the original terminal roots character. -/
abbrev originalTerminalFamilyCoverRootBoundary
    (n : ℕ) (hn : 0 < n) (hinv : IsUnit (n : Γ((B₀).X.left, ⊤)))
    (χ₀ : Group.BaseChange.baseChangedGroup (𝟙 (Base k)) (Kernel.group q) ⟶
      rootsGroupScheme (Base k) n) :=
  let g := (B₀).X.hom
  let iB : B.X.left ⟶ (B₀).X.left :=
    pullback.lift (𝟙 B.X.left) B.X.hom (by simp)
  let f : X.left ⟶ (B₀).X.left := a.left ≫ iB
  let hb : f ≫ g = X.hom := by
    change (a.left ≫ iB) ≫ pullback.snd B.X.hom (T₀).hom = X.hom
    rw [Category.assoc, pullback.lift_snd]
    exact a.w
  let hf : f ≫ pullback.fst B.X.hom (T₀).hom = a.left := by
    change (a.left ≫ iB) ≫ pullback.fst B.X.hom (T₀).hom = _
    rw [Category.assoc, pullback.lift_fst, Category.comp_id]
  letI : HasExt.{wX} (AbelianSheaf.{u, u + 1}
      (Group.BaseChange.baseChangedGroup (𝟙 (Base k)) B).X.left) := hBExt
  Kummer.terminalCoverRootBoundary_of_eq (Kernel.marking q) f a.left X.hom hb a.w hf
    (familyCoverTorsor q (T₀)) (familyCoverTorsor_eq q (T₀)) n hn hinv χ₀

end AlgebraicGeometry.Scheme.RelativePicard.KernelFramePushout

namespace AlgebraicGeometry.Scheme.OverField.Curve

open Scheme.RelativePicard Scheme.RelativePicard.KernelFramePushout

universe u w w'

attribute [local instance] Over.cartesianMonoidalCategory hasSheafifyLarge
  Kernel.isCommMonObj_group groupSchemeBaseChange_isCommMonObj

section RootsSource

open GroupCohomology.Kummer.Coefficients

variable {Y Y' Z : Scheme.{u}}
  [HasExt.{w'} (AbelianSheaf.{u, u + 1} Y)] [HasExt.{w'} (AbelianSheaf.{u, u + 1} Y')]
  [HasExt.{w} (AbelianSheaf.{u, u + 1} Z)]

/-- The original roots pullback equality transports along the same source, arrow, and class. -/
theorem rootsPullback_result_of_source_eq
    {f : Z ⟶ Y} {f' : Z ⟶ Y'} {n : ℕ} {hn : 0 < n}
    {hi : IsUnit (n : Γ(Y, ⊤))} {hi' : IsUnit (n : Γ(Y', ⊤))}
    {c : H1Etale Y (mu Y n)} {c' : H1Etale Y' (mu Y' n)}
    {s t : H1Etale Z (mu Z n)}
    (h : s = Kummer.rootsCohomologyPullback.{u, w', w} f n hn hi 1 c)
    (h' : Kummer.rootsCohomologyPullback.{u, w', w} f' n hn hi' 1 c' = t)
    (hY : Y = Y') (hf : HEq f f') (hc : HEq c c') : s = t := by
  subst Y'
  cases hf
  cases hc
  exact h.trans h'

end RootsSource

variable {k : Type u} [Field k] [IsAlgClosed k] {X : FScheme k} (hX : Properties X)
  (P : LocallyNoetherianOver (Spec (.of k))) [LocallyOfFiniteType P.obj.hom]
  [IsSeparated P.obj.hom]
  (R : ((locallyNoetherianOverInclusion (Spec (.of k))).op ⋙ (fppfPicardSheaf X.hom).obj ⋙
    CategoryTheory.forget AddCommGrpCat.{u + 1}).RepresentableBy P)
  (Q : LocallyNoetherianOver (Spec (.of k))) [LocallyOfFiniteType Q.obj.hom]
  [IsSeparated Q.obj.hom]
  (RQ : ((locallyNoetherianOverInclusion (Spec (.of k))).op ⋙
    (fppfPicardSheaf (picardIdentityComponent X.hom P R).hom).obj ⋙
      CategoryTheory.forget AddCommGrpCat.{u + 1}).RepresentableBy Q)

set_option hygiene false in
local notation "J" => picardIdentityComponent X.hom P R
set_option hygiene false in
local notation "T₀" => (𝟙_ (FScheme k))

variable [hXExt : HasExt.{w} (AbelianSheaf.{u, u + 1} X.left)]
  [hJExt : HasExt.{w'} (AbelianSheaf.{u, u + 1} (pullback (J).hom (T₀).hom))]

/-- Applying the positive original Weil character to the unsigned original Abel boundary gives
the negative original inverse Kummer class of the same torsion point. -/
abbrev jacobianAbelRootBoundaryEqNeg
    (o : Spec (.of k) ⟶ X.left) (ho : o ≫ X.hom = 𝟙 _)
    (n : ℕ) (hn : 0 < n) (hu : IsUnit (n : k))
    (y : letI := picardCommGrpObj X.hom P R
      letI : GrpObj (J) := grpObjPicardIdentityComponent X.hom P R
      letI : IsCommMonObj (J) := inferInstanceAs (IsCommMonObj (identityComponentOver P.obj))
      (T₀) ⟶ (MultiplicationKernel.kernelGroup (Grp.mk (J)) n).X) :=
  letI := picardCommGrpObj X.hom P R
  let Jc := (J)
  letI : GrpObj Jc := grpObjPicardIdentityComponent X.hom P R
  let A : Grp (FScheme k) := Grp.mk Jc
  let RQA : ((locallyNoetherianOverInclusion (Spec (.of k))).op ⋙
      (fppfPicardSheaf A.X.hom).obj ⋙
      CategoryTheory.forget AddCommGrpCat.{u + 1}).RepresentableBy Q := RQ
  letI : IsCommMonObj A.X := inferInstanceAs (IsCommMonObj (identityComponentOver P.obj))
  letI : IsHProjective A.X.hom := isHProjective_identityComponentOver hX P R
  letI : GeometricallyIntegral A.X.hom := geometricallyIntegral_identityComponentOver hX P R
  letI : Smooth A.X.hom := smooth_identityComponentOver hX P R
  let t : (T₀) ⟶ (dualMultiplicationKernel A Q RQA n).X :=
    y ≫ (principalIsoOnMultiplicationKernel A Q RQA
      (canonicalJacobianPrincipalGroupIso hX P R Q RQ) n).hom.hom.hom
  let a : X ⟶ A.X := jacobianCurveMorphism hX o ho P R
  letI : HasExt.{w'} (AbelianSheaf.{u, u + 1} (pullback A.X.hom (T₀).hom)) := hJExt
  let q := MultiplicationKernel.multiplicationHom A n
  let hq := Multiplication.multiplicationHom_finite_flat_surjective A n hn
  letI : IsFinite q.hom.hom.left := hq.1
  letI : Surjective q.hom.hom.left := hq.2.2
  letI : Etale q.hom.hom.left := by
    simpa only [q, MultiplicationKernel.multiplicationHom_hom, MultiplicationKernel.multiplication]
      using Multiplication.multiplication_etale_of_smooth_of_isUnit A n hu
  let K := Kernel.group q
  letI : IsFinite K.X.hom := Multiplication.kernelGroup_isFinite_of_pos A n hn
  let χ₀ := _root_.AlgebraicGeometry.Scheme.Group.CartierDuality.characterRoots K (T₀)
    (t ≫ (multiplicationKernelCartierHom A Q RQA n hn).hom.hom) n
    (Kernel.multiplication_kernel_pow_eq_one A n)
  let A₀ := (groupSchemeBaseChange (T₀).hom).functor.obj A
  let Y := A₀.X.left
  letI : HasExt.{w'} (AbelianSheaf.{u, u + 1} Y) := hJExt
  letI : HasExt.{w'} (AbelianSheaf.{u, u + 1}
      ((Over.pullback (T₀).hom).mapGrp.obj A).X.left) := hJExt
  let hinv : IsUnit (n : Γ(Y, ⊤)) := by
    simpa only [map_natCast] using hu.map (Scheme.constants A₀.X)
  let hDirect := originalTerminalFamilyCoverRootBoundary.{u, w', w} q a n hn hinv χ₀
  let iA : A.X.left ⟶ Y :=
    pullback.lift (f := A.X.hom) (g := (T₀).hom) (𝟙 A.X.left) A.X.hom (by simp)
  let f : X.left ⟶ Y := a.left ≫ iA
  let F := Kummer.rootsCohomologyPullback.{u, w', w} f n hn hinv 1
  let hξ := jacobianTerminalFamilyKummerClass_eq_coverPush hX P R Q RQ n hn hu y
  let hNeg :=
    rootsCohomologyPullback_multiplicationFamilyKummerClass_jacobianCurveMorphism
      hX P R Q RQ o ho n hn hu y
  let hSigned := (congrArg F hξ.symm).trans hNeg
  let Yid := (Group.BaseChange.baseChangedGroup (𝟙 (Base k)) A).X.left
  let jIdExt : HasExt.{w'} (AbelianSheaf.{u, u + 1} Yid) := hJExt
  let jExt : HasExt.{w'} (AbelianSheaf.{u, u + 1} Y) := hJExt
  @rootsPullback_result_of_source_eq Yid Y X.left jIdExt jExt hXExt
    _ _ n hn _ _ _ _ _ _ hDirect hSigned
    (by rfl) (by rfl)
    (by
      simp only [multiplicationFamilyRootCharacter, Group.BaseChange.baseChangedGroup,
        groupSchemeBaseChange_functor, Over.tensorUnit_left, Over.tensorUnit_hom]
      rfl)

end AlgebraicGeometry.Scheme.OverField.Curve
