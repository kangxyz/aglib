/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import
  Aglib.AlgebraicGeometry.Modules.Differentials.Relative.Conormal.Determinant.Localization
public import Aglib.AlgebraicGeometry.Modules.ExteriorPower.LocallyFree
public import Aglib.AlgebraicGeometry.Modules.Invertible.Dual
public import Aglib.AlgebraicGeometry.Cohomology.ClosedImmersion.RightAdjoint.RegularList.Sheaf
public import
  Aglib.AlgebraicGeometry.Cohomology.ClosedImmersion.RightAdjoint.RegularList.Sheaf.Localization
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Affine.Pullback
/-!
# The actual regular-list purity line and its normal determinant

The top homology of the installed closed right adjoint is identified with the
dual normal determinant tensored with the actual pulled-back coefficient line.
The original ordered Koszul class, inverse affine counit and tilde comparisons
fix its normalization. The dual normal generator evaluates the original
normal-first wedge to one through the native dual evaluation.
-/
@[expose] public section
noncomputable section
open CategoryTheory CategoryTheory.Abelian AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme.Hom
open AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.Invertible
open AlgebraicGeometry.Scheme.Modules.Differentials
open scoped TensorProduct
universe u
namespace AlgebraicGeometry.Scheme.Modules
variable (X : Scheme.{u})
private theorem isoSectionsHom_injective {Y : Scheme.{u}} {M N : Y.Modules}
    (e : M ≅ N) (U : Y.Opens) : Function.Injective (e.hom.val.app (op U)) := by
  intro x y h
  have hx := congrArg (fun k => k.val.app (op U) x) e.hom_inv_id
  have hy := congrArg (fun k => k.val.app (op U) y) e.hom_inv_id
  exact hx.symm.trans ((congrArg (e.inv.val.app (op U)) h).trans hy)

private theorem reassocFive {C : Type*} [Category C] {V W X Y Z T : C}
    (f : V ⟶ W) (g : W ⟶ X) (h : X ⟶ Y) (i : Y ⟶ Z) (j : Z ⟶ T) :
    (f ≫ g ≫ h ≫ i) ≫ j = f ≫ g ≫ h ≫ i ≫ j := by
  simp only [Category.assoc]

private def dualTransportIso {L M : X.Modules} (e : L ≅ M) :
    dualSheaf X L ≅ dualSheaf X M := by
  let a : dualSheaf X L ⟶ dualSheaf X M := {
    val.app U := (InternalHom.overHomMap X ⊤
      ((SheafOfModules.overFunctor X.ringCatSheaf ⊤).map e.inv)
      (𝟙 ((SheafOfModules.unit X.ringCatSheaf).over ⊤))).val.app
        (op (Over.mk (homOfLE le_top : U.unop ⟶ ⊤)))
    val.naturality := by intros; rfl }
  let b : dualSheaf X M ⟶ dualSheaf X L := {
    val.app U := (InternalHom.overHomMap X ⊤
      ((SheafOfModules.overFunctor X.ringCatSheaf ⊤).map e.hom)
      (𝟙 ((SheafOfModules.unit X.ringCatSheaf).over ⊤))).val.app
        (op (Over.mk (homOfLE le_top : U.unop ⟶ ⊤)))
    val.naturality := by intros; rfl }
  refine ⟨a, b, ?_, ?_⟩
  · apply SheafOfModules.hom_ext
    ext U : 1
    exact congrArg (fun f => f.val.app (op (Over.mk (homOfLE le_top : U.unop ⟶ ⊤))))
      (InternalHom.overHomIso X ⊤ ((SheafOfModules.overFunctor X.ringCatSheaf ⊤).mapIso e)
        (Iso.refl ((SheafOfModules.unit X.ringCatSheaf).over ⊤))).hom_inv_id
  · apply SheafOfModules.hom_ext
    ext U : 1
    exact congrArg (fun f => f.val.app (op (Over.mk (homOfLE le_top : U.unop ⟶ ⊤))))
      (InternalHom.overHomIso X ⊤ ((SheafOfModules.overFunctor X.ringCatSheaf ⊤).mapIso e)
        (Iso.refl ((SheafOfModules.unit X.ringCatSheaf).over ⊤))).inv_hom_id

private def dualFrameIso {L : X.Modules} (e : L ≅ SheafOfModules.unit X.ringCatSheaf) :
    dualSheaf X L ≅ SheafOfModules.unit X.ringCatSheaf :=
  dualTransportIso X e ≪≫ InternalHom.unitSourceIso X (SheafOfModules.unit X.ringCatSheaf)

private theorem dualFrameIso_hom_evaluation {L : X.Modules}
    (e : L ≅ SheafOfModules.unit X.ringCatSheaf) (U : X.Opens)
    (ell : (dualSheaf X L).val.obj (op U)) :
    (dualFrameIso X e).hom.val.app (op U) ell =
      ell.val.app (op (Over.mk (𝟙 U))) (e.inv.val.app (op U) (1 : Γ(X, U))) := rfl

private theorem dualFrameIso_inv_evaluation {L : X.Modules}
    (e : L ≅ SheafOfModules.unit X.ringCatSheaf) (U : X.Opens)
    (v : L.val.obj (op U)) :
    ((dualFrameIso X e).inv.val.app (op U) (1 : Γ(X, U))).val.app
      (op (Over.mk (𝟙 U))) v = e.hom.val.app (op U) v := by
  let : Module Γ(X, U) (L.val.obj (op U)) := by
    change Module (X.ringCatSheaf.obj.obj (op U)) (L.val.obj (op U))
    infer_instance
  let d := dualFrameIso X e
  let ell := d.inv.val.app (op U) (1 : Γ(X, U))
  let w := e.inv.val.app (op U) (1 : Γ(X, U))
  let r : Γ(X, U) := e.hom.val.app (op U) v
  have hn : ell.val.app (op (Over.mk (𝟙 U))) w = (1 : Γ(X, U)) :=
    (dualFrameIso_hom_evaluation X e U ell).symm.trans
      (congrArg (fun f => f.val.app (op U) (1 : Γ(X, U))) d.inv_hom_id)
  have hw : r • w = v := by
    have h := (e.inv.val.app (op U)).hom.map_smul r (1 : Γ(X, U))
    change e.inv.val.app (op U) (show Γ(X, U) from r * 1) = r • w at h
    exact h.symm.trans ((congrArg (e.inv.val.app (op U)) (mul_one r)).trans
      (congrArg (fun f => f.val.app (op U) v) e.hom_inv_id))
  have hl := ell.property (op (Over.mk (𝟙 U))) r w
  change ell.val.app (op (Over.mk (𝟙 U))) (r • w) =
    (show Γ(X, U) from r *
      (show Γ(X, U) from ell.val.app (op (Over.mk (𝟙 U))) w)) at hl
  exact (congrArg (ell.val.app (op (Over.mk (𝟙 U)))) hw).symm.trans
    (hl.trans ((congrArg (fun a : Γ(X, U) => r * a) hn).trans (mul_one r)))

private theorem evaluationSheaf_section (M N : X.Modules) (U : X.Opens)
    (ell : (InternalHom.sheaf X M N).val.obj (op U)) (v : M.val.obj (op U)) :
    (evaluationSheaf X M N).val.app (op U)
      (moduleTensorSection X (InternalHom.sheaf X M N) M U ell v) =
        ell.val.app (op (Over.mk (𝟙 U))) v := by
  let φ := evaluationPresheaf X M N
  have h := (_root_.PresheafOfModules.sheafificationHomEquiv
    (𝟙 X.ringCatSheaf.obj)).apply_symm_apply φ
  have hp := congrArg (fun f => f.app (op U) (ell ⊗ₜ[Γ(X, U)] v)) h
  exact hp

private theorem dualEvaluationIso_section (L : LineBundle X) (U : X.Opens)
    (ell : (dualLineBundle X L).val.val.obj (op U)) (v : L.val.val.obj (op U)) :
    (dualEvaluationIso X L).hom.val.app (op U)
      (moduleTensorSection X (dualLineBundle X L).val L.val U ell v) =
        ell.val.app (op (Over.mk (𝟙 U))) v :=
  (congrArg (fun f => f.val.app (op U)
    (moduleTensorSection X (dualLineBundle X L).val L.val U ell v))
      (dualEvaluationIso_hom X L)).trans (evaluationSheaf_section X L.val _ U ell v)

/-- A supplied actual unit frame equips its original sheaf with the native line property. -/
def lineBundleOfUnitFrame {L : X.Modules}
    (e : L ≅ SheafOfModules.unit X.ringCatSheaf) : LineBundle X := by
  refine ⟨L, (isLocallyRankOne_iff_local_unit X L).mpr ?_⟩
  intro x
  exact ⟨⊤, trivial, ⟨(SheafOfModules.overFunctor X.ringCatSheaf ⊤).mapIso e⟩⟩

private abbrev nativeFreeModule (Y : Scheme.{u}) (U : Y.Opens) (d : ℕ) :
    Module (Y.sheaf.obj.obj (op U))
      ((SheafOfModules.free (R := Y.ringCatSheaf) (ULift.{u} (Fin d))).val.obj (op U)) := by
  change Module (Y.ringCatSheaf.obj.obj (op U))
    ((SheafOfModules.free (R := Y.ringCatSheaf) (ULift.{u} (Fin d))).val.obj (op U))
  infer_instance

private theorem freeSectionDet (Y : Scheme.{u}) (U : Y.Opens) (d : ℕ) :
    letI := nativeFreeModule Y U d
    (SheafOfModulesOfCommRing.freeFinSectionsBasis Y.sheaf d (op U)).det.toFun
      (fun i => (SheafOfModules.freeSection (R := Y.ringCatSheaf) (ULift.up i)).val
        (op U)) = (1 : Γ(Y, U)) := by
  let := nativeFreeModule Y U d
  let b := SheafOfModulesOfCommRing.freeFinSectionsBasis Y.sheaf d (op U)
  exact (congrArg b.det.toFun (funext fun i =>
    SheafOfModulesOfCommRing.freeFinSectionsBasis_apply Y.sheaf d (op U) i)).symm.trans
      (Module.Basis.det_self b)

variable {R A B : CommRingCat.{u}} (α : R ⟶ A) (σ : A ⟶ B) (hσ : Function.Surjective σ)
  (s : List A) (hs : RingTheory.Sequence.IsWeaklyRegular A s)
  (hk : Ideal.ofList s = RingHom.ker σ.hom)

private def normalTopFrame :
    moduleExteriorPower (Spec B)
      ((pullback (Spec.map σ)).obj (idealModule (Spec.map σ))) s.length ≅
        SheafOfModules.unit (Spec B).ringCatSheaf :=
  (moduleExteriorPowerFunctor (Spec B) s.length).mapIso
    (relativeConormalAffineGeometricFreeIso α σ hσ s hs hk) ≪≫
      SheafOfModulesOfCommRing.exteriorTopFreeIso (Spec B).sheaf s.length

private def normalOrderedSections (U : (Spec B).Opens) (i : Fin s.length) :
    ((pullback (Spec.map σ)).obj (idealModule (Spec.map σ))).val.obj (op U) :=
  (relativeConormalAffineIdealPullbackIso α σ hσ).inv.val.app (op U)
    (tilde.toOpen (relativeConormalAffineModule α σ hσ) U
      (relativeConormalAffineClass α σ hσ
        ⟨s.get i, hk.le (Ideal.subset_span (s.get_mem i))⟩))

private theorem normalTopFrame_wedge (U : (Spec B).Opens) :
    (normalTopFrame α σ hσ s hs hk).hom.val.app (op U)
      ((SheafOfModulesOfCommRing.exteriorPowerMk (Spec B).sheaf
        ((pullback (Spec.map σ)).obj (idealModule (Spec.map σ))) s.length).app (op U)
        (normalOrderedSections α σ hσ s hk U)) = (1 : Γ(Spec B, U)) := by
  let := nativeFreeModule (Spec B) U s.length
  let e := relativeConormalAffineGeometricFreeIso α σ hσ s hs hk
  let v := normalOrderedSections α σ hσ s hk U
  have h1 := congrArg
    ((SheafOfModulesOfCommRing.exteriorTopFreeHom (Spec B).sheaf s.length).val.app (op U))
      (SheafOfModulesOfCommRing.exteriorPowerFunctor_map_mk (Spec B).sheaf e.hom
        s.length (op U) v)
  have h2 := SheafOfModulesOfCommRing.exteriorTopFreeHom_mk (Spec B).sheaf s.length (op U)
    (fun i => e.hom.val.app (op U) (v i))
  have hv : (fun i => e.hom.val.app (op U) (v i)) =
      fun i => (SheafOfModules.freeSection (R := (Spec B).ringCatSheaf) (ULift.up i)).val
        (op U) := funext fun i =>
    relativeConormalAffineGeometricFreeIso_class α σ hσ s hs hk i U
  exact h1.trans (h2.trans ((congrArg
    (SheafOfModulesOfCommRing.freeFinSectionsBasis (Spec B).sheaf s.length (op U)).det.toFun
      hv).trans (freeSectionDet (Spec B) U s.length)))

private theorem originalNormalDualEvaluation (U : (Spec B).Opens) :
    let L := lineBundleOfUnitFrame (Spec B) (normalTopFrame α σ hσ s hs hk)
    let ell := (dualFrameIso (Spec B) (normalTopFrame α σ hσ s hs hk)).inv.val.app (op U)
      (1 : Γ(Spec B, U))
    let v := (SheafOfModulesOfCommRing.exteriorPowerMk (Spec B).sheaf
      ((pullback (Spec.map σ)).obj (idealModule (Spec.map σ))) s.length).app (op U)
        (normalOrderedSections α σ hσ s hk U)
    (dualEvaluationIso (Spec B) L).hom.val.app (op U)
      (moduleTensorSection (Spec B) (dualLineBundle (Spec B) L).val L.val U ell v) =
        (1 : Γ(Spec B, U)) := by
  intro L ell v
  exact (dualEvaluationIso_section (Spec B) L U ell v).trans
    ((dualFrameIso_inv_evaluation (Spec B) (normalTopFrame α σ hσ s hs hk) U v).trans
      (normalTopFrame_wedge α σ hσ s hs hk U))

end AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme.Modules
section Quotient
universe w a b
variable {R A : CommRingCat.{u}} (α : R ⟶ A) (s : List A)
  (hs : RingTheory.Sequence.IsWeaklyRegular A s)

private def quotientNormalFrame : (moduleExteriorPower (Spec (CommRingCat.of (A ⧸ Ideal.ofList
  s))) ((pullback (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.ofList s)) : A ⟶
  (CommRingCat.of (A ⧸ Ideal.ofList s))))).obj (idealModule (Spec.map (CommRingCat.ofHom
  (Ideal.Quotient.mk (Ideal.ofList s)) : A ⟶ (CommRingCat.of (A ⧸ Ideal.ofList s)))))) s.length) ≅
  SheafOfModules.unit (Spec (CommRingCat.of (A ⧸ Ideal.ofList s))).ringCatSheaf :=
  normalTopFrame α (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.ofList s)) : A ⟶ (CommRingCat.of
    (A ⧸ Ideal.ofList s))) (Ideal.Quotient.mk_surjective) s hs (Ideal.mk_ker.symm)

/-- The frame of the actual normal determinant given by the original ordered list. -/
def closedImmersionRegularListNormalFrameIso :
    moduleExteriorPower (Spec (CommRingCat.of (A ⧸ Ideal.ofList s)))
      ((pullback (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.ofList s)) :
        A ⟶ CommRingCat.of (A ⧸ Ideal.ofList s)))).obj
          (idealModule (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.ofList s)) :
            A ⟶ CommRingCat.of (A ⧸ Ideal.ofList s))))) s.length ≅
      SheafOfModules.unit (Spec (CommRingCat.of (A ⧸ Ideal.ofList s))).ringCatSheaf :=
  (moduleExteriorPowerFunctor (Spec (CommRingCat.of (A ⧸ Ideal.ofList s))) s.length).mapIso
    (relativeConormalAffineGeometricFreeIso α
      (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.ofList s)) :
        A ⟶ CommRingCat.of (A ⧸ Ideal.ofList s)) Ideal.Quotient.mk_surjective s hs
      Ideal.mk_ker.symm) ≪≫
    SheafOfModulesOfCommRing.exteriorTopFreeIso
      (Spec (CommRingCat.of (A ⧸ Ideal.ofList s))).sheaf s.length

/-- The normal frame uses precisely the original conormal free map and native top-free frame. -/
theorem closedImmersionRegularListNormalFrameIso_eq :
    closedImmersionRegularListNormalFrameIso α s hs =
      (moduleExteriorPowerFunctor (Spec (CommRingCat.of (A ⧸ Ideal.ofList s))) s.length).mapIso
        (relativeConormalAffineGeometricFreeIso α
          (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.ofList s)) :
            A ⟶ CommRingCat.of (A ⧸ Ideal.ofList s)) Ideal.Quotient.mk_surjective s hs
          Ideal.mk_ker.symm) ≪≫
        SheafOfModulesOfCommRing.exteriorTopFreeIso
          (Spec (CommRingCat.of (A ⧸ Ideal.ofList s))).sheaf s.length := by
  rfl

/-- The actual normal determinant line of the original quotient immersion. -/
def closedImmersionRegularListNormalLineBundle :
    LineBundle (Spec (CommRingCat.of (A ⧸ Ideal.ofList s))) :=
  lineBundleOfUnitFrame _ (closedImmersionRegularListNormalFrameIso α s hs)

/-- The native dual frame of the original ordered normal determinant. -/
@[no_expose] def closedImmersionRegularListNormalDualFrameIso :
    (dualLineBundle _ (closedImmersionRegularListNormalLineBundle α s hs)).val ≅
      SheafOfModules.unit (Spec (CommRingCat.of (A ⧸ Ideal.ofList s))).ringCatSheaf :=
  dualFrameIso _ (quotientNormalFrame α s hs)

variable {L : (Spec A).Modules} [L.IsQuasicoherent]
  (e : moduleSpecΓFunctor.obj L ≅ ModuleCat.of A A)

/-- The coefficient frame uses the original affine counit, scalar extension and tilde. -/
def closedImmersionRegularListCoefficientFrameIso :
    (pullback (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.ofList s)) : A ⟶
      (CommRingCat.of (A ⧸ Ideal.ofList s))))).obj L ≅ SheafOfModules.unit (Spec (CommRingCat.of
      (A ⧸ Ideal.ofList s))).ringCatSheaf := by
  exact (pullback (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.ofList s)) : A ⟶
    (CommRingCat.of (A ⧸ Ideal.ofList s))))).mapIso (asIso L.fromTildeΓ).symm ≪≫
    (tildePullbackIso (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.ofList s)) : A ⟶
      (CommRingCat.of (A ⧸ Ideal.ofList s)))).app (moduleSpecΓFunctor.obj L) ≪≫
    (tilde.functor (CommRingCat.of (A ⧸ Ideal.ofList s))).mapIso
      ((ModuleCat.extendScalars ((CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.ofList s)) : A ⟶
        (CommRingCat.of (A ⧸ Ideal.ofList s)))).hom).mapIso e ≪≫
        ModuleCat.extendScalarsAlgebraObjIso A (CommRingCat.of (A ⧸ Ideal.ofList s)) (ModuleCat.of
          A A) ≪≫
          (TensorProduct.AlgebraTensorModule.rid A (CommRingCat.of (A ⧸ Ideal.ofList s))
            (CommRingCat.of (A ⧸ Ideal.ofList s))).toModuleIso) ≪≫
    tildeSelf

private def quotientInverseNormalFrame :
    tensorSheaf (Spec (CommRingCat.of (A ⧸ Ideal.ofList s))) (dualSheaf (Spec (CommRingCat.of (A ⧸
      Ideal.ofList s))) (moduleExteriorPower (Spec (CommRingCat.of (A ⧸ Ideal.ofList s)))
      ((pullback (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.ofList s)) : A ⟶
      (CommRingCat.of (A ⧸ Ideal.ofList s))))).obj (idealModule (Spec.map (CommRingCat.ofHom
      (Ideal.Quotient.mk (Ideal.ofList s)) : A ⟶ (CommRingCat.of (A ⧸ Ideal.ofList s))))))
      s.length)) ((pullback (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.ofList s)) : A
      ⟶ (CommRingCat.of (A ⧸ Ideal.ofList s))))).obj L) ≅
      SheafOfModules.unit (Spec (CommRingCat.of (A ⧸ Ideal.ofList s))).ringCatSheaf :=
  ((SheafOfModulesOfCommRing.tensorFunctor (Spec (CommRingCat.of (A ⧸ Ideal.ofList
    s))).sheaf).mapIso
    (dualFrameIso (Spec (CommRingCat.of (A ⧸ Ideal.ofList s))) (quotientNormalFrame α s hs))).app
      ((pullback (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.ofList s)) : A ⟶
      (CommRingCat.of (A ⧸ Ideal.ofList s))))).obj L) ≪≫
      (SheafOfModulesOfCommRing.tensorLeftUnitIso (Spec (CommRingCat.of (A ⧸ Ideal.ofList
        s))).sheaf).app
        ((pullback (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.ofList s)) : A ⟶
          (CommRingCat.of (A ⧸ Ideal.ofList s))))).obj L) ≪≫
        closedImmersionRegularListCoefficientFrameIso s e

/-- The original ordered normal class determines the inverse normal/coefficient line frame. -/
@[no_expose] def closedImmersionRegularListInverseNormalLineIso :
    SheafOfModules.unit (Spec (CommRingCat.of (A ⧸ Ideal.ofList s))).ringCatSheaf ≅
      tensorSheaf (Spec (CommRingCat.of (A ⧸ Ideal.ofList s))) (dualSheaf (Spec (CommRingCat.of (A
        ⧸ Ideal.ofList s))) (moduleExteriorPower (Spec (CommRingCat.of (A ⧸ Ideal.ofList s)))
        ((pullback (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.ofList s)) : A ⟶
        (CommRingCat.of (A ⧸ Ideal.ofList s))))).obj (idealModule (Spec.map (CommRingCat.ofHom
        (Ideal.Quotient.mk (Ideal.ofList s)) : A ⟶ (CommRingCat.of (A ⧸ Ideal.ofList s))))))
        s.length)) ((pullback (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.ofList s)) :
        A ⟶ (CommRingCat.of (A ⧸ Ideal.ofList s))))).obj L) :=
  (quotientInverseNormalFrame α s hs e).symm

/-- The normal dual section is normalized by the original ordered regular generators. -/
@[no_expose] def closedImmersionRegularListNormalDualSection (U : (Spec (CommRingCat.of (A ⧸
  Ideal.ofList s))).Opens) :
    (dualSheaf (Spec (CommRingCat.of (A ⧸ Ideal.ofList s))) (moduleExteriorPower (Spec
      (CommRingCat.of (A ⧸ Ideal.ofList s))) ((pullback (Spec.map (CommRingCat.ofHom
      (Ideal.Quotient.mk (Ideal.ofList s)) : A ⟶ (CommRingCat.of (A ⧸ Ideal.ofList s))))).obj
      (idealModule (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.ofList s)) : A ⟶
      (CommRingCat.of (A ⧸ Ideal.ofList s)))))) s.length)).val.obj (op U) :=
  (dualFrameIso (Spec (CommRingCat.of (A ⧸ Ideal.ofList s))) (quotientNormalFrame α s
    hs)).inv.val.app (op U)
    (1 : Γ(Spec (CommRingCat.of (A ⧸ Ideal.ofList s)), U))

/-- The original normal dual is the section of one in the actual native dual frame. -/
theorem closedImmersionRegularListNormalDualSection_eq
    (U : (Spec (CommRingCat.of (A ⧸ Ideal.ofList s))).Opens) :
    closedImmersionRegularListNormalDualSection α s hs U =
      (closedImmersionRegularListNormalDualFrameIso α s hs).inv.val.app (op U)
        (1 : Γ(Spec (CommRingCat.of (A ⧸ Ideal.ofList s)), U)) := by
  rfl

/-- The native dual frame is evaluation on the inverse-one section of the same normal frame. -/
theorem closedImmersionRegularListNormalDualFrameIso_hom_evaluation
    (U : (Spec (CommRingCat.of (A ⧸ Ideal.ofList s))).Opens)
    (ell : (dualLineBundle _ (closedImmersionRegularListNormalLineBundle α s hs)).val.val.obj
      (op U)) :
    (closedImmersionRegularListNormalDualFrameIso α s hs).hom.val.app (op U) ell =
      ell.val.app (op (Over.mk (𝟙 U)))
        ((closedImmersionRegularListNormalFrameIso α s hs).inv.val.app (op U)
          (1 : Γ(Spec (CommRingCat.of (A ⧸ Ideal.ofList s)), U))) :=
  dualFrameIso_hom_evaluation _ (quotientNormalFrame α s hs) U ell

/-- The original ordered regular generators wedged in their original order. -/
@[no_expose] def closedImmersionRegularListNormalSection
    (U : (Spec (CommRingCat.of (A ⧸ Ideal.ofList s))).Opens) :
    (closedImmersionRegularListNormalLineBundle α s hs).val.val.obj (op U) :=
  (SheafOfModulesOfCommRing.exteriorPowerMk
    (Spec (CommRingCat.of (A ⧸ Ideal.ofList s))).sheaf
    ((pullback (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.ofList s)) :
      A ⟶ CommRingCat.of (A ⧸ Ideal.ofList s)))).obj
        (idealModule (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.ofList s)) :
          A ⟶ CommRingCat.of (A ⧸ Ideal.ofList s))))) s.length).app (op U)
    (normalOrderedSections α (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.ofList s)) :
      A ⟶ CommRingCat.of (A ⧸ Ideal.ofList s)) Ideal.Quotient.mk_surjective s
        Ideal.mk_ker.symm U)

/-- The normal section is the literal wedge of the original ordered kernel classes. -/
theorem closedImmersionRegularListNormalSection_eq
    (U : (Spec (CommRingCat.of (A ⧸ Ideal.ofList s))).Opens) :
    closedImmersionRegularListNormalSection α s hs U =
      (SheafOfModulesOfCommRing.exteriorPowerMk
        (Spec (CommRingCat.of (A ⧸ Ideal.ofList s))).sheaf
        ((pullback (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.ofList s)) :
          A ⟶ CommRingCat.of (A ⧸ Ideal.ofList s)))).obj
            (idealModule (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.ofList s)) :
              A ⟶ CommRingCat.of (A ⧸ Ideal.ofList s))))) s.length).app (op U)
        (fun j => (relativeConormalAffineIdealPullbackIso α
          (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.ofList s)) :
            A ⟶ CommRingCat.of (A ⧸ Ideal.ofList s)) Ideal.Quotient.mk_surjective).inv.val.app
              (op U)
          (tilde.toOpen (relativeConormalAffineModule α
            (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.ofList s)) :
              A ⟶ CommRingCat.of (A ⧸ Ideal.ofList s)) Ideal.Quotient.mk_surjective) U
            (relativeConormalAffineClass α
              (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.ofList s)) :
                A ⟶ CommRingCat.of (A ⧸ Ideal.ofList s)) Ideal.Quotient.mk_surjective
              ⟨s.get j, Ideal.mk_ker.symm.le (Ideal.subset_span (s.get_mem j))⟩))) := by
  rfl

/-- The same original normal frame sends the same original ordered wedge to one. -/
theorem closedImmersionRegularListNormalFrameIso_normalSection
    (U : (Spec (CommRingCat.of (A ⧸ Ideal.ofList s))).Opens) :
    (closedImmersionRegularListNormalFrameIso α s hs).hom.val.app (op U)
      (closedImmersionRegularListNormalSection α s hs U) =
        (1 : Γ(Spec (CommRingCat.of (A ⧸ Ideal.ofList s)), U)) :=
  normalTopFrame_wedge α
    (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.ofList s)) :
      A ⟶ CommRingCat.of (A ⧸ Ideal.ofList s)) Ideal.Quotient.mk_surjective s hs
    Ideal.mk_ker.symm U

/-- Native dual evaluation of the same ordered normal wedge is exactly one. -/
theorem closedImmersionRegularListNormalDualSection_dualEvaluation
    (U : (Spec (CommRingCat.of (A ⧸ Ideal.ofList s))).Opens) :
    (dualEvaluationIso _ (closedImmersionRegularListNormalLineBundle α s hs)).hom.val.app
      (op U)
      (moduleTensorSection _
        (dualLineBundle _ (closedImmersionRegularListNormalLineBundle α s hs)).val
        (closedImmersionRegularListNormalLineBundle α s hs).val U
        (closedImmersionRegularListNormalDualSection α s hs U)
        (closedImmersionRegularListNormalSection α s hs U)) =
      (1 : Γ(Spec (CommRingCat.of (A ⧸ Ideal.ofList s)), U)) :=
  originalNormalDualEvaluation α
    (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.ofList s)) :
      A ⟶ CommRingCat.of (A ⧸ Ideal.ofList s))
    Ideal.Quotient.mk_surjective s hs Ideal.mk_ker.symm U

/-- The coefficient section retains the original affine pullback and tilde comparisons. -/
@[no_expose] def closedImmersionRegularListCoefficientSection (r : (CommRingCat.of (A ⧸
  Ideal.ofList s))) (U : (Spec (CommRingCat.of (A ⧸ Ideal.ofList s))).Opens) :
    ((pullback (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.ofList s)) : A ⟶
      (CommRingCat.of (A ⧸ Ideal.ofList s))))).obj L).val.obj (op U) :=
  (closedImmersionRegularListCoefficientFrameIso s e).inv.val.app (op U)
    (tilde.toOpen (ModuleCat.of (CommRingCat.of (A ⧸ Ideal.ofList s)) (CommRingCat.of (A ⧸
      Ideal.ofList s))) U r)

/-- The coefficient section is the original inverse affine coefficient frame on that section. -/
theorem closedImmersionRegularListCoefficientSection_eq
    (r : CommRingCat.of (A ⧸ Ideal.ofList s))
    (U : (Spec (CommRingCat.of (A ⧸ Ideal.ofList s))).Opens) :
    closedImmersionRegularListCoefficientSection s e r U =
      (closedImmersionRegularListCoefficientFrameIso s e).inv.val.app (op U)
        (tilde.toOpen (ModuleCat.of (CommRingCat.of (A ⧸ Ideal.ofList s))
          (CommRingCat.of (A ⧸ Ideal.ofList s))) U r) := by
  rfl

/-- The inverse normal frame preserves the original dual and coefficient sections. -/
theorem closedImmersionRegularListInverseNormalLineIso_section (r : (CommRingCat.of (A ⧸
    Ideal.ofList s))) (U :
  (Spec (CommRingCat.of (A ⧸ Ideal.ofList s))).Opens) :
    (closedImmersionRegularListInverseNormalLineIso α s hs e).hom.val.app (op U)
      (tilde.toOpen (ModuleCat.of (CommRingCat.of (A ⧸ Ideal.ofList s)) (CommRingCat.of (A ⧸
        Ideal.ofList s))) U r) =
    moduleTensorSection (Spec (CommRingCat.of (A ⧸ Ideal.ofList s))) (dualSheaf (Spec
      (CommRingCat.of (A ⧸ Ideal.ofList s))) (moduleExteriorPower (Spec (CommRingCat.of (A ⧸
      Ideal.ofList s))) ((pullback (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.ofList
      s)) : A ⟶ (CommRingCat.of (A ⧸ Ideal.ofList s))))).obj (idealModule (Spec.map
      (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.ofList s)) : A ⟶ (CommRingCat.of (A ⧸
      Ideal.ofList s)))))) s.length)) ((pullback (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk
      (Ideal.ofList s)) : A ⟶ (CommRingCat.of (A ⧸ Ideal.ofList s))))).obj L) U
      (closedImmersionRegularListNormalDualSection α s hs U)
      (closedImmersionRegularListCoefficientSection s e r U) := by
  let d := dualFrameIso (Spec (CommRingCat.of (A ⧸ Ideal.ofList s))) (quotientNormalFrame α s hs)
  let f := closedImmersionRegularListCoefficientFrameIso s e
  let t := quotientInverseNormalFrame α s hs e
  apply isoSectionsHom_injective t U
  have hleft := congrArg (fun k => k.val.app (op U)
    (tilde.toOpen (ModuleCat.of (CommRingCat.of (A ⧸ Ideal.ofList s)) (CommRingCat.of (A ⧸
      Ideal.ofList s))) U r)) t.inv_hom_id
  have hdual : d.hom.val.app (op U)
      (closedImmersionRegularListNormalDualSection α s hs U) = (1 : Γ(Spec (CommRingCat.of (A ⧸
        Ideal.ofList s)), U)) :=
    congrArg (fun k => k.val.app (op U) (1 : Γ(Spec (CommRingCat.of (A ⧸ Ideal.ofList s)), U)))
      d.inv_hom_id
  have hcoeff : f.hom.val.app (op U)
      (closedImmersionRegularListCoefficientSection s e r U) =
        tilde.toOpen (ModuleCat.of (CommRingCat.of (A ⧸ Ideal.ofList s)) (CommRingCat.of (A ⧸
          Ideal.ofList s))) U r :=
    congrArg (fun k => k.val.app (op U)
      (tilde.toOpen (ModuleCat.of (CommRingCat.of (A ⧸ Ideal.ofList s)) (CommRingCat.of (A ⧸
        Ideal.ofList s))) U r)) f.inv_hom_id
  have hunit := tensorToUnit_section d.hom ((pullback (Spec.map (CommRingCat.ofHom
    (Ideal.Quotient.mk (Ideal.ofList s)) : A ⟶ (CommRingCat.of (A ⧸ Ideal.ofList s))))).obj L) U
    (closedImmersionRegularListNormalDualSection α s hs U)
    (closedImmersionRegularListCoefficientSection s e r U)
  let : Module Γ(Spec (CommRingCat.of (A ⧸ Ideal.ofList s)), U) (((pullback (Spec.map
    (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.ofList s)) : A ⟶ (CommRingCat.of (A ⧸
    Ideal.ofList s))))).obj L).val.obj (op U)) := by
    change Module ((Spec (CommRingCat.of (A ⧸ Ideal.ofList s))).ringCatSheaf.obj.obj (op U)) _
    infer_instance
  have hunit' := hunit.trans
    ((congrArg (fun a : Γ(Spec (CommRingCat.of (A ⧸ Ideal.ofList s)), U) =>
      a • closedImmersionRegularListCoefficientSection s e r U) hdual).trans
        (one_smul Γ(Spec (CommRingCat.of (A ⧸ Ideal.ofList s)), U)
          (closedImmersionRegularListCoefficientSection s e r U)))
  have hright := (congrArg (f.hom.val.app (op U)) hunit').trans hcoeff
  exact hleft.trans hright.symm

/-- The coefficient-one normal dual evaluates the original normal-first wedge to one. -/
theorem closedImmersionRegularListNormalDualSection_evaluation (U : (Spec (CommRingCat.of (A ⧸
  Ideal.ofList s))).Opens) :
    let v := (SheafOfModulesOfCommRing.exteriorPowerMk (Spec (CommRingCat.of (A ⧸ Ideal.ofList
      s))).sheaf
      ((pullback (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.ofList s)) : A ⟶
        (CommRingCat.of (A ⧸ Ideal.ofList s))))).obj (idealModule (Spec.map (CommRingCat.ofHom
        (Ideal.Quotient.mk (Ideal.ofList s)) : A ⟶ (CommRingCat.of (A ⧸ Ideal.ofList s))))))
        s.length).app (op U)
      (fun j => (relativeConormalAffineIdealPullbackIso α (CommRingCat.ofHom (Ideal.Quotient.mk
        (Ideal.ofList s)) : A ⟶ (CommRingCat.of (A ⧸ Ideal.ofList s)))
        Ideal.Quotient.mk_surjective).inv.val.app (op U)
        (tilde.toOpen (relativeConormalAffineModule α (CommRingCat.ofHom (Ideal.Quotient.mk
          (Ideal.ofList s)) : A ⟶ (CommRingCat.of (A ⧸ Ideal.ofList s)))
          Ideal.Quotient.mk_surjective) U
          (relativeConormalAffineClass α (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.ofList s)) :
            A ⟶ (CommRingCat.of (A ⧸ Ideal.ofList s))) Ideal.Quotient.mk_surjective
            ⟨s.get j, Ideal.mk_ker.symm.le (Ideal.subset_span (s.get_mem j))⟩)))
    (evaluationSheaf (Spec (CommRingCat.of (A ⧸ Ideal.ofList s))) (moduleExteriorPower (Spec
      (CommRingCat.of (A ⧸ Ideal.ofList s))) ((pullback (Spec.map (CommRingCat.ofHom
      (Ideal.Quotient.mk (Ideal.ofList s)) : A ⟶ (CommRingCat.of (A ⧸ Ideal.ofList s))))).obj
      (idealModule (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.ofList s)) : A ⟶
      (CommRingCat.of (A ⧸ Ideal.ofList s)))))) s.length) (SheafOfModules.unit (Spec
      (CommRingCat.of (A ⧸ Ideal.ofList s))).ringCatSheaf)).val.app (op U)
      (moduleTensorSection (Spec (CommRingCat.of (A ⧸ Ideal.ofList s))) (dualSheaf (Spec
        (CommRingCat.of (A ⧸ Ideal.ofList s))) (moduleExteriorPower (Spec (CommRingCat.of (A ⧸
        Ideal.ofList s))) ((pullback (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.ofList
        s)) : A ⟶ (CommRingCat.of (A ⧸ Ideal.ofList s))))).obj (idealModule (Spec.map
        (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.ofList s)) : A ⟶ (CommRingCat.of (A ⧸
        Ideal.ofList s)))))) s.length)) (moduleExteriorPower (Spec (CommRingCat.of (A ⧸
        Ideal.ofList s))) ((pullback (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.ofList
        s)) : A ⟶ (CommRingCat.of (A ⧸ Ideal.ofList s))))).obj (idealModule (Spec.map
        (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.ofList s)) : A ⟶ (CommRingCat.of (A ⧸
        Ideal.ofList s)))))) s.length) U
        (closedImmersionRegularListNormalDualSection α s hs U) v) = (1 : Γ(Spec (CommRingCat.of (A
          ⧸ Ideal.ofList s)), U)) := by
  intro v
  exact (congrArg (fun k => k.val.app (op U)
    (moduleTensorSection (Spec (CommRingCat.of (A ⧸ Ideal.ofList s))) (dualSheaf (Spec
      (CommRingCat.of (A ⧸ Ideal.ofList s))) (moduleExteriorPower (Spec (CommRingCat.of (A ⧸
      Ideal.ofList s))) ((pullback (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.ofList
      s)) : A ⟶ (CommRingCat.of (A ⧸ Ideal.ofList s))))).obj (idealModule (Spec.map
      (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.ofList s)) : A ⟶ (CommRingCat.of (A ⧸
      Ideal.ofList s)))))) s.length)) (moduleExteriorPower (Spec (CommRingCat.of (A ⧸ Ideal.ofList
      s))) ((pullback (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.ofList s)) : A ⟶
      (CommRingCat.of (A ⧸ Ideal.ofList s))))).obj (idealModule (Spec.map (CommRingCat.ofHom
      (Ideal.Quotient.mk (Ideal.ofList s)) : A ⟶ (CommRingCat.of (A ⧸ Ideal.ofList s))))))
      s.length) U
      (closedImmersionRegularListNormalDualSection α s hs U) v))
      (dualEvaluationIso_hom (Spec (CommRingCat.of (A ⧸ Ideal.ofList s)))
        (lineBundleOfUnitFrame (Spec (CommRingCat.of (A ⧸ Ideal.ofList s))) (quotientNormalFrame α s
          hs)))).symm.trans
    (originalNormalDualEvaluation α (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.ofList s)) : A ⟶
      (CommRingCat.of (A ⧸ Ideal.ofList s))) Ideal.Quotient.mk_surjective s hs
      Ideal.mk_ker.symm U)

local instance : (moduleSpecΓFunctor (R := (CommRingCat.of (A ⧸ Ideal.ofList s)))).Additive :=
  moduleSpecΓFunctor_additive _

variable [HasExt.{w} (ModuleCat.{u} A)]
  [HasDerivedCategory.{a} (Spec A).Modules] [HasDerivedCategory.{b} (Spec (CommRingCat.of (A ⧸
    Ideal.ofList s))).Modules]

/-- The actual top homology of the installed Ri! is the inverse normal/coefficient line. -/
@[no_expose] def derivedClosedImmersionRightAdjointRegularListConormalTopHomologyIso :
    ((DerivedCategory.Plus.homologyFunctor (Spec (CommRingCat.of (A ⧸ Ideal.ofList s))).Modules
      (s.length : ℤ)).obj ((closedImmersionRightAdjoint (Spec.map (CommRingCat.ofHom
      (Ideal.Quotient.mk (Ideal.ofList s)) : A ⟶ (CommRingCat.of (A ⧸ Ideal.ofList
      s))))).rightDerivedFunctorPlus.obj ((DerivedCategory.Plus.singleFunctor (Spec A).Modules
      0).obj L))) ≅ tensorSheaf (Spec (CommRingCat.of (A ⧸ Ideal.ofList s))) (dualSheaf (Spec
      (CommRingCat.of (A ⧸ Ideal.ofList s))) (moduleExteriorPower (Spec (CommRingCat.of (A ⧸
      Ideal.ofList s))) ((pullback (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.ofList
      s)) : A ⟶ (CommRingCat.of (A ⧸ Ideal.ofList s))))).obj (idealModule (Spec.map
      (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.ofList s)) : A ⟶ (CommRingCat.of (A ⧸
      Ideal.ofList s)))))) s.length)) ((pullback (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk
      (Ideal.ofList s)) : A ⟶ (CommRingCat.of (A ⧸ Ideal.ofList s))))).obj L) :=
  derivedClosedImmersionRightAdjointRegularListTopHomologyIso s hs (injectiveResolution L) e ≪≫
    closedImmersionRegularListInverseNormalLineIso α s hs e

/-- The conormal map is the original native unit frame followed by the inverse normal line. -/
theorem derivedClosedImmersionRightAdjointRegularListConormalTopHomologyIso_hom :
    (derivedClosedImmersionRightAdjointRegularListConormalTopHomologyIso α s hs e).hom =
      (derivedClosedImmersionRightAdjointRegularListTopHomologyIso s hs
        (injectiveResolution L) e).hom ≫
      (closedImmersionRegularListInverseNormalLineIso α s hs e).hom := by
  rfl

/-- Actual regular-list purity with the inverse normal determinant and original coefficient. -/
@[no_expose] def derivedClosedImmersionRightAdjointRegularListConormalIso :
    ((closedImmersionRightAdjoint (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.ofList
      s)) : A ⟶ (CommRingCat.of (A ⧸ Ideal.ofList s))))).rightDerivedFunctorPlus.obj
      ((DerivedCategory.Plus.singleFunctor (Spec A).Modules 0).obj L)) ≅
      (DerivedCategory.Plus.singleFunctor (Spec (CommRingCat.of (A ⧸ Ideal.ofList s))).Modules
      (s.length : ℤ)).obj
      (tensorSheaf (Spec (CommRingCat.of (A ⧸ Ideal.ofList s))) (dualSheaf (Spec (CommRingCat.of
        (A ⧸ Ideal.ofList s))) (moduleExteriorPower (Spec (CommRingCat.of (A ⧸ Ideal.ofList s)))
        ((pullback (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.ofList s)) : A ⟶
        (CommRingCat.of (A ⧸ Ideal.ofList s))))).obj (idealModule (Spec.map (CommRingCat.ofHom
        (Ideal.Quotient.mk (Ideal.ofList s)) : A ⟶ (CommRingCat.of (A ⧸ Ideal.ofList s))))))
        s.length)) ((pullback (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.ofList s)) :
        A ⟶ (CommRingCat.of (A ⧸ Ideal.ofList s))))).obj L)) :=
  derivedClosedImmersionRightAdjointRegularListIso s hs (injectiveResolution L) e ≪≫
    (DerivedCategory.Plus.singleFunctor (Spec (CommRingCat.of (A ⧸ Ideal.ofList s))).Modules
      (s.length : ℤ)).mapIso
      (closedImmersionRegularListInverseNormalLineIso α s hs e)

/-- The inverse-normal map retains the original model unit, affine counit and exact tilde. -/
theorem derivedClosedImmersionRightAdjointRegularListConormalTopHomologyIso_counit :
    let J := injectiveResolution L
    let : QuasiIso (Complex.tildeGlobalSectionsCounit (CommRingCat.of (A ⧸ Ideal.ofList s)) (.up ℤ)
      (closedImmersionRightAdjointRegularListResolutionComplex s J)) :=
        closedImmersionRightAdjointRegularListResolutionTildeCounit_quasiIso s hs J e
    (derivedClosedImmersionRightAdjointRegularListConormalTopHomologyIso α s hs e).hom =
      (derivedClosedImmersionRightAdjointRegularListModelHomologyIso s J
        (s.length : ℤ)).hom ≫
      (Complex.tildeGlobalSectionsHomologyIso (CommRingCat.of (A ⧸ Ideal.ofList s)) (.up ℤ)
        (closedImmersionRightAdjointRegularListResolutionComplex s J) (s.length : ℤ)).inv ≫
      (tilde.functor (CommRingCat.of (A ⧸ Ideal.ofList s))).map
        (closedImmersionRightAdjointRegularListResolutionTopSectionsLinearEquiv s hs J
          e).toModuleIso.hom ≫ (tildeSelf (R := (CommRingCat.of (A ⧸ Ideal.ofList s)))).hom ≫
      (closedImmersionRegularListInverseNormalLineIso α s hs e).hom := by
  intro J hJ
  change (derivedClosedImmersionRightAdjointRegularListTopHomologyIso s hs J e).hom ≫ _ = _
  rw [derivedClosedImmersionRightAdjointRegularListTopHomologyIso_hom,
    closedImmersionRightAdjointRegularListResolutionTopHomologyIso_hom]
  exact reassocFive _ _ _ _ _

/-- The original Koszul class maps to the normalized dual normal and coefficient sections. -/
theorem derivedClosedImmersionRightAdjointRegularListConormalTopHomologyIso_class
    (r : A) (U : (Spec (CommRingCat.of (A ⧸ Ideal.ofList s))).Opens) :
    let J := injectiveResolution L
    let : QuasiIso (Complex.tildeGlobalSectionsCounit (CommRingCat.of (A ⧸ Ideal.ofList s)) (.up ℤ)
      (closedImmersionRightAdjointRegularListResolutionComplex s J)) :=
        closedImmersionRightAdjointRegularListResolutionTildeCounit_quasiIso s hs J e
    let C := closedImmersionRightAdjointRegularListResolutionComplex s J
    let G := ((moduleSpecΓFunctor (R := (CommRingCat.of (A ⧸ Ideal.ofList
      s)))).mapHomologicalComplex (.up ℤ)).obj C
    let ξ := (closedImmersionRightAdjointRegularListResolutionSectionsExtAddEquiv s J
      s.length).symm
      ((ChainComplex.Koszul.topExtClass s hs (ModuleCat.of A A) r).comp
        (Ext.mk₀ e.inv) (Nat.add_zero s.length))
    (derivedClosedImmersionRightAdjointRegularListConormalTopHomologyIso α s hs e).hom.val.app
      (op U) ((derivedClosedImmersionRightAdjointRegularListModelHomologyIso s J
        (s.length : ℤ)).inv.val.app (op U)
        ((Complex.tildeGlobalSectionsHomologyIso (CommRingCat.of (A ⧸ Ideal.ofList s)) (.up ℤ) C
          (s.length : ℤ)).hom.val.app
          (op U) (tilde.toOpen (G.homology (s.length : ℤ)) U ξ))) =
      moduleTensorSection (Spec (CommRingCat.of (A ⧸ Ideal.ofList s))) (dualSheaf (Spec
        (CommRingCat.of (A ⧸ Ideal.ofList s))) (moduleExteriorPower (Spec (CommRingCat.of (A ⧸
        Ideal.ofList s))) ((pullback (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.ofList
        s)) : A ⟶ (CommRingCat.of (A ⧸ Ideal.ofList s))))).obj (idealModule (Spec.map
        (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.ofList s)) : A ⟶ (CommRingCat.of (A ⧸
        Ideal.ofList s)))))) s.length)) ((pullback (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk
        (Ideal.ofList s)) : A ⟶ (CommRingCat.of (A ⧸ Ideal.ofList s))))).obj L) U
        (closedImmersionRegularListNormalDualSection α s hs U)
        (closedImmersionRegularListCoefficientSection s e (Ideal.Quotient.mk _ r) U) := by
  intro J hJ C G ξ
  let P := closedImmersionRightAdjointRegularListResolutionTopSectionsLinearEquiv s hs J e
  let E := closedImmersionRightAdjointRegularListResolutionSectionsExtAddEquiv s J s.length
  have hξ : ξ = P.symm (Ideal.Quotient.mk (Ideal.ofList s) r) := by
    apply E.injective
    exact (E.apply_symm_apply _).trans
      (closedImmersionRightAdjointRegularListResolutionTopSectionsLinearEquiv_class
        s hs J e r).symm
  let em := derivedClosedImmersionRightAdjointRegularListModelHomologyIso s J (s.length : ℤ)
  let ec := Complex.tildeGlobalSectionsHomologyIso (CommRingCat.of (A ⧸ Ideal.ofList s)) (.up ℤ) C
    (s.length : ℤ)
  let en := closedImmersionRegularListInverseNormalLineIso α s hs e
  let es := tildeSelf (R := CommRingCat.of (A ⧸ Ideal.ofList s))
  let pval := (tilde.map P.toModuleIso.hom).val.app (op U)
  let sval := es.hom.val.app (op U)
  let nval := en.hom.val.app (op U)
  have htop := derivedClosedImmersionRightAdjointRegularListConormalTopHomologyIso_counit
    α s hs e
  change _ = em.hom ≫ ec.inv ≫
    (tilde.functor (CommRingCat.of (A ⧸ Ideal.ofList s))).map P.toModuleIso.hom ≫
      es.hom ≫ en.hom at htop
  let z := tilde.toOpen (G.homology (s.length : ℤ)) U ξ
  have hval := congrArg (fun k => k.val.app (op U)
    (em.inv.val.app (op U) (ec.hom.val.app (op U) z))) htop
  change _ = nval (sval (pval (ec.inv.val.app (op U) (em.hom.val.app (op U) (em.inv.val.app (op U)
    (ec.hom.val.app (op U) (z))))))) at hval
  have hm := congrArg (fun k => k.val.app (op U) (ec.hom.val.app (op U) z)) em.inv_hom_id
  change em.hom.val.app (op U) (em.inv.val.app (op U) (ec.hom.val.app (op U) z)) =
    ec.hom.val.app (op U) z at hm
  have hc := congrArg (fun k => k.val.app (op U) z) ec.hom_inv_id
  change ec.inv.val.app (op U) (ec.hom.val.app (op U) z) = z at hc
  have hcancel := (congrArg (ec.inv.val.app (op U)) hm).trans hc
  have hp := ConcreteCategory.congr_hom (tilde.toOpen_map_app P.toModuleIso.hom U) ξ
  change pval z = tilde.toOpen
    (ModuleCat.of (CommRingCat.of (A ⧸ Ideal.ofList s))
      (CommRingCat.of (A ⧸ Ideal.ofList s))) U (P ξ) at hp
  have hP := (congrArg P hξ).trans (P.apply_symm_apply (Ideal.Quotient.mk _ r))
  have hp' := hp.trans (congrArg
    (tilde.toOpen (ModuleCat.of (CommRingCat.of (A ⧸ Ideal.ofList s))
      (CommRingCat.of (A ⧸ Ideal.ofList s))) U) hP)
  exact hval.trans ((congrArg (fun x => nval (sval (pval x))) hcancel).trans
    ((congrArg (fun x => nval (sval x)) hp').trans
      (closedImmersionRegularListInverseNormalLineIso_section α s hs e (Ideal.Quotient.mk _ r) U)))

end Quotient
end AlgebraicGeometry.Scheme.Modules
