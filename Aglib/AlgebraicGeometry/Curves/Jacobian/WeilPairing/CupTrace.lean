/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Curves.Jacobian.WeilPairing
public import Aglib.Algebra.Homology.DerivedCategory.Ext.SignedCharacterDetection
public import Aglib.AlgebraicGeometry.Curves.Jacobian.WeilPairing.CupData
public import Aglib.AlgebraicGeometry.Curves.Jacobian.WeilPairing.AbelTraceCover
public import Aglib.AlgebraicGeometry.Curves.Jacobian.WeilPairing.AbelRootBoundary
public import Aglib.AlgebraicGeometry.Curves.Jacobian.WeilPairing.FirstKummerScalarValue
public import Aglib.AlgebraicGeometry.AbelianScheme.OverField.Dual.WeilPairing.TerminalCharacterDescent
public import Aglib.AlgebraicGeometry.AbelianScheme.OverField.Dual.WeilPairing.TerminalEvaluation
public import Aglib.AlgebraicGeometry.EtaleCohomology.Duality.RelativeTraceScalar
public import Aglib.AlgebraicGeometry.EtaleCohomology.Duality.RootsTraceContractionScalar
public import Aglib.AlgebraicGeometry.EtaleCohomology.Kummer.RepresentedRootValuePullback
public import Aglib.AlgebraicGeometry.EtaleCohomology.Kummer.RootsScalarFieldTransport

/-! # Original Jacobian Weil values and signed cup trace -/

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
open MonoidalCategory CartesianMonoidalCategory MonObj
open GroupCohomology.Kummer.Coefficients GroupCohomology.Kummer.CoefficientBaseChange

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace AlgebraicGeometry.Scheme.OverField.Curve

open Scheme.Group Scheme.Group.BaseChange Scheme.RelativePicard
open Scheme.EtaleCohomology Scheme.EtaleCohomology.Coefficients
open Scheme.EtaleCohomology.RepresentedKernel Scheme.OverField.Curve.PointDivisor

universe u

attribute [local instance] Over.cartesianMonoidalCategory hasSheafifyLarge hasSheafifyModules
  groupSchemeBaseChange_isCommMonObj moduleSheafExtZModModule
  CategoryTheory.TorsionZMod.Ringed.abWEqualsLocallyBijectiveStandard

variable {k : Type u} [Field k] [IsAlgClosed k] {X : FScheme k} (hX : Properties X)
  (P : LocallyNoetherianOver (Base k)) [LocallyOfFiniteType P.obj.hom] [IsSeparated P.obj.hom]
  (R : ((locallyNoetherianOverInclusion (Base k)).op ⋙ (fppfPicardSheaf X.hom).obj ⋙
    CategoryTheory.forget AddCommGrpCat.{u + 1}).RepresentableBy P)
  (Q : LocallyNoetherianOver (Base k)) [LocallyOfFiniteType Q.obj.hom] [IsSeparated Q.obj.hom]
  (RQ : ((locallyNoetherianOverInclusion (Base k)).op ⋙
    (fppfPicardSheaf (picardIdentityComponent X.hom P R).hom).obj ⋙
      CategoryTheory.forget AddCommGrpCat.{u + 1}).RepresentableBy Q)
  (n : ℕ) (hn : 0 < n) (hu : IsUnit (n : k))

set_option hygiene false in
local notation "Λ" => ULift.{u + 1} (ZMod n)
set_option hygiene false in
local notation "J" => picardIdentityComponent X.hom P R
set_option hygiene false in
local notation "T₀" => 𝟙_ (FScheme k)
set_option hygiene false in
local notation "Z" => pullback X.hom X.hom
set_option hygiene false in
local notation "π" => pullback.snd X.hom X.hom
set_option hygiene false in
local notation "f" => pullback.fst X.hom X.hom

/-- The standard Ext realization for the original abelian sheaves. -/
local instance weilCupAbelianExt (Y : Scheme.{u}) : HasExt.{u + 2} (AbelianSheaf.{u, u + 1} Y) :=
  hasExtStandard Y
/-- The standard Ext realization for the original finite coefficient modules. -/
local instance weilCupModuleExt (Y : Scheme.{u}) : HasExt.{u + 2} (ModuleSheaf Y Λ) :=
  SheafOfModules.hasExt (constantRing Y Λ)

set_option maxHeartbeats 600000 in
-- Specializing the original relative trace and point-value comparisons exceeds the default budget.
/-- The original Weil value in the original roots coefficient is the signed
trace of the original ordered Kummer cup product. -/
theorem jacobianWeilPairingMorphism_cupTrace
    (x y : letI := picardCommGrpObj X.hom P R
      letI : GrpObj (J) := grpObjPicardIdentityComponent X.hom P R
      letI : IsCommMonObj (J) := inferInstanceAs (IsCommMonObj (identityComponentOver P.obj))
      (T₀) ⟶ (MultiplicationKernel.kernelGroup (Grp.mk (J)) n).X) :
    let := picardCommGrpObj X.hom P R
    let : GrpObj (J) := grpObjPicardIdentityComponent X.hom P R
    let : IsCommMonObj (J) := inferInstanceAs (IsCommMonObj (identityComponentOver P.obj))
    let g := lift x y ≫ jacobianWeilPairingMorphism hX P R Q RQ n hn
    let β := moduleUnitRootsIso k n hn hu (𝟙 (Base k))
    let s := jacobianSignedCupTrace hX P R n hn hu x y
    (Ext.mk₀ (representedIntegerSection (MultiplicativeGroup.rootsGroupScheme (Base k) n) g) :
      Sheaf.H.{u + 2} (mu (Base k) n) 0) =
      moduleRootsUnitExtCohomologyAddEquiv (Base k) n 0 (Ext.mk₀ (s.val • β.hom)) := by
  intro laws hgrp hcomm g β₀ s
  obtain ⟨o, ho⟩ := hX.exists_rationalPoint_of_isAlgClosed
  let p := X.hom
  let := hX.smooth
  let := hX.proper
  let : IsNoetherian X.left := curveProperties_isNoetherian hX
  let : ConnectedSpace X.left := curveProperties_connectedSpace hX
  let : GeometricallyIntegral p := curveProperties_geometricallyIntegral
    smoothFieldNormality normalComponentsOpen hX
  let := laws
  let := hgrp
  let := hcomm
  let : NeZero n := ⟨Nat.ne_of_gt hn⟩
  let A : Grp (FScheme k) := Grp.mk (J)
  let : IsHProjective A.X.hom := isHProjective_identityComponentOver hX P R
  let : GeometricallyIntegral A.X.hom := geometricallyIntegral_identityComponentOver hX P R
  let : Smooth A.X.hom := smooth_identityComponentOver hX P R
  let e := canonicalJacobianPrincipalGroupIso hX P R Q RQ
  let q := MultiplicationKernel.multiplicationHom A n
  let K := Kernel.group q
  let : IsCommMonObj K.X := Kernel.isCommMonObj_group q
  let hq := Multiplication.multiplicationHom_finite_flat_surjective A n hn
  let : IsFinite q.hom.hom.left := hq.1
  let : Surjective q.hom.hom.left := hq.2.2
  let hEtale : Etale q.hom.hom.left := by
    simpa only [q, MultiplicationKernel.multiplicationHom_hom, MultiplicationKernel.multiplication]
      using Multiplication.multiplication_etale_of_smooth_of_isUnit A n hu
  let := hEtale
  let d := p ≫ o
  let o' : X.left ⟶ Z := pullback.lift d (𝟙 X.left)
    (by simp only [d, p, Category.assoc, ho, Category.comp_id, Category.id_comp])
  have ho' : o' ≫ π = 𝟙 X.left := pullback.lift_snd _ _ _
  let W : (Z).Opens := ⟨(Set.range (pullback.diagonal p))ᶜ,
    (pullback.diagonal p).isClosedEmbedding.isClosed_range.isOpen_compl⟩
  let j := W.ι
  have hj : Set.range j = (Set.range (pullback.diagonal p))ᶜ := Scheme.Opens.range_ι W
  let := HasDerivedCategory.standard (AbelianSheaf.{u, u + 1} X.left)
  let := HasDerivedCategory.standard (AbelianSheaf.{u, u + 1} Z)
  let := HasDerivedCategory.standard (ModuleSheaf (Base k) Λ)
  let := HasDerivedCategory.standard (ModuleSheaf X.left Λ)
  let := HasDerivedCategory.standard (ModuleSheaf Z Λ)
  let := HasDerivedCategory.standard (ModuleSheaf W.toScheme Λ)
  let : ∀ V : X.left.Etale, HasExt.{u + 2} (Sheaf ((Scheme.smallEtaleTopology Z).over
    ((siteBaseChange π).obj V)) AddCommGrpCat.{u + 1}) := fun _ => HasExt.standard _
  let : ∀ V : X.left.Etale, HasExt.{u + 2} (AbelianSheaf.{u, u + 1} (pullback V.hom π)) :=
    fun V => hasExtStandard (pullback V.hom π)
  let hi₀ := modulePoint_globalLevelInvertible (C := (T₀)) n hu
  let hi := levelInvertible p n hi₀
  let β := jacobianCupRootsIso (X := X) n hn hu
  let α := jacobianKernelPointRootsOne hX P R n hn hu
  let vx := jacobianKernelPointModuleRootsOne hX P R n hn hu x
  let vy := jacobianKernelPointModuleRootsOne hX P R n hn hu y
  let u := vy.comp (Ext.mk₀ β.inv) (add_zero 1)
  let w₀ := -(u.comp vx (rfl : 1 + 1 = 2))
  obtain ⟨τ, a, ha, hτdef, hnorm⟩ :=
    properCurveDiagonalTraceExistsNormalized hX n hn hu o ho
  let G := (groupSchemeBaseChange p).functor.obj A
  let KX := Group.BaseChange.baseChangedGroup p K
  let m := kernelMarking p (Kernel.marking q)
  let hpow := (congrArg representedSheafMap (groupSchemeBaseChange_map_identity_pow p A n)).trans
    (RepresentedKernel.Native.representedSheafMap_multiplication G n)
  let : Epi (n • 𝟙 (representedSheaf G)) :=
    epi_nsmul_representedSheaf_groupBaseChange p A n hEtale hq.2.2
  let jP := picardDegreeZeroEtaleInclusion P R p o' ho'
  let a₀ := representedIntegerSection G (jacobianAbelTerminalGraph hX o ho P R)
  let hS := Kummer.markedPowerKernelSequence_shortExact m n hpow
  let C : Sheaf.H.{u + 2} (representedSheaf KX) 1 := (Ext.mk₀ a₀).comp hS.extClass (zero_add 1)
  let r : Ext.{u + 2} (moduleRootsOfUnity Z n) (moduleRootsOfUnity Z n) 1 :=
    Kummer.moduleRootsExtOneTensor n hn hu (f ≫ p) (constantModuleExtPullback n f 1 u)
  let B := ModuleSheaf X.left Λ
  let BZ := ModuleSheaf Z Λ
  let I := (DerivedCategory.Plus.singleFunctor B 0).obj (moduleUnit X.left Λ)
  let M := (DerivedCategory.Plus.singleFunctor BZ 0).obj (moduleRootsOfUnity Z n)
  let t : ShiftedHom ((moduleDerivedDirectImage Λ π).obj M) I (-1 : ℤ) :=
    (r.homPlus.map (moduleDerivedDirectImage Λ π)).comp τ
      (by omega : (-2 : ℤ) + 1 = -1)
  let θ₀ := Kummer.markedKummerTraceFunctional π o' ho' n hn hi m hpow jP
    (Kummer.moduleRootsShiftedMapUnderlying π n t)
  let b := (SheafOfModules.toSheaf (constantRing X.left Λ)).map β.hom ≫
    (moduleRootsOfUnityUnderlyingIso X.left n).hom
  let θ := θ₀ ≫ b
  let χ := multiplicationTerminalRootCharacterSheafEquiv A Q RQ e n hn p hi₀
  have hα : Function.Injective α := by
    intro z z' h
    let i := (Kernel.inclusion q).hom.hom
    let : Mono i := (Kernel.square q).mono_fst_of_mono
    apply (cancel_mono i).mp
    have ht := (rootsOneJacobianTorsionAddEquiv hX P R n hn hu).symm.injective h
    exact congrArg (fun k' => k'.val.toMul) ht
  have hχ (z : (T₀) ⟶ K.X) : C.comp (Ext.mk₀ (χ z)) (add_zero 1) = -α z := by
    have hPos := multiplicationTerminalRootCharacterSheafEquiv_apply A Q RQ e n hn p hi₀ z
    let hCover := jacobianAbelRootBoundaryEqNeg.{u, u + 2, u + 2}
      hX P R Q RQ o ho n hn hu z
    exact (congrArg (fun g => C.comp (Ext.mk₀ g) (add_zero 1)) hPos).trans hCover
  have hβ : u.comp (Ext.mk₀ β.hom) (add_zero 1) = vy := by
    change (vy.comp (Ext.mk₀ β.inv) (add_zero 1)).comp (Ext.mk₀ β.hom) (add_zero 1) = vy
    rw [Ext.comp_assoc_of_third_deg_zero, Ext.mk₀_comp_mk₀, β.inv_hom_id, Ext.comp_mk₀_id]
  let E := moduleRootsUnitExtCohomologyAddEquiv X.left n 1
  have hy : E (u.comp (Ext.mk₀ β.hom) (add_zero 1)) = α y :=
    (congrArg E hβ).trans (E.apply_symm_apply (α y))
  let hCoverTrace := jacobianAbelTraceCover.{u, u + 2, u + 2, u + 2, u + 2, u + 2, u + 2}
    hX o ho P R n hn hu hi o' ho' j hj u β.hom τ hnorm
  let hTrace := hCoverTrace.trans (congrArg Neg.neg hy)
  have hθ := Ext.eq_character_of_signed_postcomp C χ α hα hχ y _ hTrace
  let i := diagonalSectionFibreMap p o ho
  have hi₁ : i ≫ f = 𝟙 X.left := pullback.lift_fst _ _ _
  let w := moduleRootsUnitExtPullback f n hn hi 2 w₀
  have hOrd := properCurveProductOrdinaryTraceNsmul hX n hn hu o ho a w (ha.2 w)
  have hSection := Kummer.moduleRootsUnitExtPullback_section f i hi₁ n hn hi 2 w₀
  let scalar := fun z : Ext.{u + 2} (moduleUnit X.left Λ) (moduleRootsOfUnity X.left n) 2 =>
    (Curves.traceAddEquiv hX n hn hu hi
      (moduleRootsUnitExtCohomologyAddEquiv X.left n 2 z)).val • 𝟙 I
  have hOrd' := hOrd.trans (congrArg scalar hSection)
  have hScalar :=
    rootsFirstPullback_traceContraction_scalar n hn hu p f π hi u vx τ a hτdef s hOrd'
  let U := etaleTerminal X.left
  let T := Kummer.locallyNoetherianEtaleTest U
  let T' := (LocallyNoetherianOver.map p).obj T
  let dX : T' ⟶ locallyNoetherianRationalPoint k := ObjectProperty.homMk
    (Over.homMk T'.obj.hom (Category.comp_id T'.obj.hom))
  let xK := (Over.mapPullbackAdj p).homEquiv (Over.mk (𝟙 X.left)) K.X (dX.hom ≫ x)
  let aX := representedIntegerSection KX xK
  let aY := representedIntegerSection KX (Kummer.terminalPointPullback p x)
  have hVal := jacobianFirstKummerTraceFunctional_value.{u, u + 2, u + 2, u + 2,
    _, _, u + 2, u + 2, u + 2, u + 2, _, _}
    hX P R n hn hu o' ho' hi x t β.hom s hScalar
  let χ₀ := multiplicationKernelRootCharacterOfPrincipalIso A Q RQ e n hn (T₀) y
  let χF : K ⟶ MultiplicativeGroup.rootsGroupScheme (Base k) n :=
    groupSchemeBaseChangeId.inv.app K ≫ χ₀
  let fieldPoint := g
  let hPoint := originalTerminalPrincipalCharacterSection A Q RQ e n hn x y
  let fieldClass := fun z : (T₀) ⟶ (MultiplicativeGroup.rootsGroupScheme (Base k) n).X =>
    (Ext.mk₀ (representedIntegerSection (MultiplicativeGroup.rootsGroupScheme (Base k) n) z) :
      Sheaf.H.{u + 2} (mu (Base k) n) 0)
  let pb₀ := Kummer.rootsCohomologyPullback p n hn hi₀ 0
  let c₀ := fun g : representedSheaf KX ⟶ mu X.left n =>
    (Ext.mk₀ (aX ≫ g) : Sheaf.H.{u + 2} (mu X.left n) 0)
  have hPB := Kummer.rootsCohomologyPullback_characterValue p n hn hi₀ (G := K) χF x
  have hChr := multiplicationTerminalRootCharacterSheafEquiv_apply A Q RQ e n hn p hi₀ y
  let cY := fun g : representedSheaf KX ⟶ mu X.left n =>
    (Ext.mk₀ (aY ≫ g) : Sheaf.H.{u + 2} (mu X.left n) 0)
  have hWeilY :=
    (congrArg (fun z => pb₀ (fieldClass z)) hPoint).symm.trans
      (hPB.trans (congrArg cY hChr.symm))
  let T₁ := Over.mk (𝟙 X.left)
  let T₂ := (Over.map p).obj T₁
  let dY : T₂ ⟶ Over.mk (𝟙 (Base k)) := Over.homMk T₂.hom (Category.comp_id T₂.hom)
  have hd : dX.hom = dY := Over.mkIdTerminal.hom_ext _ _
  have haX : aX = aY :=
    congrArg (representedIntegerSection KX)
      (congrArg ((Over.mapPullbackAdj p).homEquiv T₁ K.X)
        (congrArg (fun z : T₂ ⟶ Over.mk (𝟙 (Base k)) => z ≫ x) hd))
  have hWeil :=
    hWeilY.trans (congrArg (fun a => Ext.mk₀ (a ≫ χ y)) haX.symm)
  have hValue := (hWeil.trans (congrArg c₀ hθ.symm)).trans hVal
  exact Kummer.rootsScalarValue_of_pullback p o ho n hn hi₀ (fieldClass fieldPoint)
    β₀.hom s.val hValue

end AlgebraicGeometry.Scheme.OverField.Curve
