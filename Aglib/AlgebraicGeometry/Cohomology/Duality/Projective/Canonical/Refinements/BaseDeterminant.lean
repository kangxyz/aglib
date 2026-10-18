/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import
  Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.Canonical.Refinements.BaseDifferentials
public import Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.Canonical.AffineDeterminant
public import Aglib.AlgebraicGeometry.Modules.StructureSheaf.Hom
public import
  Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.Canonical.Refinements.NormalBase

/-!
# Original normal-first determinants under affine base change

The original affine wedge sections commute with the actual native module
maps. Original differential bases give section-one generators in the
actual exterior frames. These computations supply the original source
generator for the canonical determinant comparison.
-/

@[expose] public section
noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme.Modules.Differentials

universe u
namespace AlgebraicGeometry.Scheme.Modules

private def affineWedge {B : CommRingCat.{u}} (N : (Spec B).Modules) (E : ModuleCat.{u} B)
    (n : ℕ) (e : N ≅ tilde E) (U : (Spec B).Opens) (v : Fin n → E) :
    (moduleExteriorPower (Spec B) N n).val.obj (op U) :=
  (SheafOfModulesOfCommRing.exteriorPowerMk (Spec B).sheaf N n).app (op U)
    (fun i => e.inv.val.app (op U) (tilde.toOpen E U (v i)))

private theorem affineWedge_map {B : CommRingCat.{u}} {N N' : (Spec B).Modules}
    {E E' : ModuleCat.{u} B} (e : N ≅ tilde E) (e' : N' ≅ tilde E')
    (f : E ⟶ E') (n : ℕ) (U : (Spec B).Opens) (v : Fin n → E) :
    ((moduleExteriorPowerFunctor (Spec B) n).map
      (e.hom ≫ (tilde.functor B).map f ≫ e'.inv)).val.app (op U)
        (affineWedge N E n e U v) = affineWedge N' E' n e' U (fun i => f (v i)) := by
  let g := e.hom ≫ (tilde.functor B).map f ≫ e'.inv
  let v₀ := fun i => e.inv.val.app (op U) (tilde.toOpen E U (v i))
  have hg (i : Fin n) : g.val.app (op U) (v₀ i) =
      e'.inv.val.app (op U) (tilde.toOpen E' U (f (v i))) := by
    have hc := congrArg (fun z => z.val.app (op U) (tilde.toOpen E U (v i))) e.inv_hom_id
    have hf := ConcreteCategory.congr_hom (tilde.toOpen_map_app f U) (v i)
    change g.val.app (op U) (v₀ i) = _
    exact congrArg (e'.inv.val.app (op U))
      ((congrArg (((tilde.functor B).map f).val.app (op U)) hc).trans hf)
  have hw := SheafOfModulesOfCommRing.exteriorPowerFunctor_map_mk
    (Spec B).sheaf g n (op U) v₀
  exact hw.trans (congrArg
    ((SheafOfModulesOfCommRing.exteriorPowerMk (Spec B).sheaf N' n).app (op U)) (funext hg))

private abbrev nativeFreeSections (Z : Scheme.{u}) (U : Z.Opens) (n : ℕ) :
    Module (Z.sheaf.obj.obj (op U))
      ((SheafOfModules.free (R := Z.ringCatSheaf) (ULift.{u} (Fin n))).val.obj (op U)) := by
  change Module (Z.ringCatSheaf.obj.obj (op U)) _
  infer_instance

private theorem freeSectionDet (Z : Scheme.{u}) (U : Z.Opens) (n : ℕ) :
    letI := nativeFreeSections Z U n
    (SheafOfModulesOfCommRing.freeFinSectionsBasis Z.sheaf n (op U)).det.toFun
      (fun i => (SheafOfModules.freeSection (R := Z.ringCatSheaf) (ULift.up i)).val (op U)) =
        (1 : Γ(Z, U)) := by
  let := nativeFreeSections Z U n
  let b := SheafOfModulesOfCommRing.freeFinSectionsBasis Z.sheaf n (op U)
  exact (congrArg b.det.toFun (funext fun i =>
    SheafOfModulesOfCommRing.freeFinSectionsBasis_apply Z.sheaf n (op U) i)).symm.trans
      (Module.Basis.det_self b)

/-- The original ordered differential basis wedge has value one in its original affine frame. -/
theorem canonicalAffineTopFrame_basis {R A : CommRingCat.{u}} (α : R ⟶ A) (n : ℕ)
    (b : Module.Basis (Fin n) A (CommRingCat.KaehlerDifferential α)) (U : (Spec A).Opens) :
    (affineRelativeTopFrame α n b).hom.val.app (op U)
      ((SheafOfModulesOfCommRing.exteriorPowerMk (Spec A).sheaf
        (relativeDifferentialSheaf (Spec.map α)) n).app (op U)
        (fun i => (relativeDifferentialAffineIso α).inv.val.app (op U)
          (tilde.toOpen (CommRingCat.KaehlerDifferential α) U (b i)))) =
        (1 : Γ(Spec A, U)) := by
  let := nativeFreeSections (Spec A) U n
  let Ω := relativeDifferentialSheaf (Spec.map α)
  let E := CommRingCat.KaehlerDifferential α
  let eA := relativeDifferentialAffineIso α
  let b' : Module.Basis (ULift.{u} (Fin n)) A E := b.reindex Equiv.ulift.symm
  let eF := tildeBasisIso E b'
  let g := eA.hom ≫ eF.hom
  let v := fun i => eA.inv.val.app (op U) (tilde.toOpen E U (b i))
  let F := SheafOfModules.free (R := (Spec A).ringCatSheaf) (ULift.{u} (Fin n))
  have hg (i : Fin n) : g.val.app (op U) (v i) =
      (SheafOfModules.freeSection (R := (Spec A).ringCatSheaf) (ULift.up i)).val (op U) := by
    have hc := congrArg (fun z => z.val.app (op U) (tilde.toOpen E U (b i))) eA.inv_hom_id
    have hb : eF.hom.val.app (op U) (tilde.toOpen E U (b i)) =
        (SheafOfModules.freeSection (R := (Spec A).ringCatSheaf) (ULift.up i)).val (op U) := by
      have hi : b' (ULift.up i) = b i := by
        exact Module.Basis.reindex_apply b Equiv.ulift.symm (ULift.up i)
      have h := tildeBasisIso_hom_toOpen E b' (ULift.up i) U
      exact (congrArg (fun x => eF.hom.val.app (op U) (tilde.toOpen E U x)) hi).symm.trans h
    exact (congrArg (eF.hom.val.app (op U)) hc).trans hb
  let top := SheafOfModulesOfCommRing.exteriorTopFreeHom (Spec A).sheaf n
  have hw := SheafOfModulesOfCommRing.exteriorPowerFunctor_map_mk
    (Spec A).sheaf g n (op U) v
  have hfree := SheafOfModulesOfCommRing.exteriorTopFreeHom_mk (Spec A).sheaf n (op U)
    (fun i => (SheafOfModules.freeSection (R := (Spec A).ringCatSheaf) (ULift.up i)).val (op U))
  change top.val.app (op U)
      (((moduleExteriorPowerFunctor (Spec A) n).map g).val.app (op U)
        ((SheafOfModulesOfCommRing.exteriorPowerMk (Spec A).sheaf Ω n).app (op U) v)) = _
  exact (congrArg (top.val.app (op U)) hw).trans
    ((congrArg (fun w => top.val.app (op U)
      ((SheafOfModulesOfCommRing.exteriorPowerMk (Spec A).sheaf F n).app (op U) w))
        (funext hg)).trans (hfree.trans (freeSectionDet (Spec A) U n)))

private theorem hom_ext_global_unitFrame {Z : Scheme.{u}} {M N : Z.Modules}
    (e : M ≅ SheafOfModules.unit Z.ringCatSheaf) (z : M.val.obj (op ⊤))
    (hz : e.hom.val.app (op ⊤) z = (1 : Γ(Z, ⊤))) {f g : M ⟶ N}
    (hfg : f.val.app (op ⊤) z = g.val.app (op ⊤) z) : f = g := by
  have hi : e.inv.val.app (op ⊤) (1 : Γ(Z, ⊤)) = z :=
    (congrArg (e.inv.val.app (op ⊤)) hz.symm).trans
      (congrArg (fun k => k.val.app (op ⊤) z) e.hom_inv_id)
  apply (cancel_epi e.inv).mp
  apply (unitHomGlobalSectionsEquiv Z N).injective
  change f.val.app (op ⊤) (e.inv.val.app (op ⊤) (1 : Γ(Z, ⊤))) =
    g.val.app (op ⊤) (e.inv.val.app (op ⊤) (1 : Γ(Z, ⊤)))
  exact (congrArg (f.val.app (op ⊤)) hi).trans
    (hfg.trans (congrArg (g.val.app (op ⊤)) hi).symm)

private theorem conormalBasisWedge {R A : CommRingCat.{u}} (α : R ⟶ A) (s : List A)
    (hs : RingTheory.Sequence.IsWeaklyRegular A s)
    (U : (Spec (regularListQuotientRing s)).Opens) :
    affineWedge
      ((pullback (Spec.map (regularListQuotientMap s))).obj
        (Scheme.Hom.idealModule (Spec.map (regularListQuotientMap s))))
      (relativeConormalAffineModule α (regularListQuotientMap s) Ideal.Quotient.mk_surjective)
      s.length (relativeConormalAffineIdealPullbackIso α (regularListQuotientMap s)
        Ideal.Quotient.mk_surjective) U
      (relativeConormalAffineBasis α (regularListQuotientMap s) Ideal.Quotient.mk_surjective
        s hs Ideal.mk_ker.symm) = closedImmersionRegularListNormalSection α s hs U := by
  let q := regularListQuotientMap s
  let E := relativeConormalAffineModule α q Ideal.Quotient.mk_surjective
  let C := (pullback (Spec.map q)).obj (Scheme.Hom.idealModule (Spec.map q))
  let e := relativeConormalAffineIdealPullbackIso α q Ideal.Quotient.mk_surjective
  have h := congrArg
    ((SheafOfModulesOfCommRing.exteriorPowerMk (Spec (regularListQuotientRing s)).sheaf
      C s.length).app (op U))
    (funext fun j => congrArg (fun v => e.inv.val.app (op U) (tilde.toOpen E U v))
      (relativeConormalAffineBasis_apply α q Ideal.Quotient.mk_surjective
        s hs Ideal.mk_ker.symm j))
  exact h.trans (closedImmersionRegularListNormalSection_eq α s hs U).symm

/-- The original normal-first determinant commutes with the actual native base differential
maps. The normal ideal section is the same original section on both sides. -/
theorem canonicalBaseConormalDeterminant
    {R S A : CommRingCat.{u}} (ρ : R ⟶ S) (β : S ⟶ A) (s : List A)
    (hs : RingTheory.Sequence.IsWeaklyRegular A s)
    (hA : (ρ ≫ β).hom.FormallySmooth)
    (hB : ((ρ ≫ β) ≫ regularListQuotientMap s).hom.FormallySmooth)
    (hA' : β.hom.FormallySmooth) (hB' : (β ≫ regularListQuotientMap s).hom.FormallySmooth)
    {d : ℕ}
    (bQ : Module.Basis (Fin d) (regularListQuotientRing s)
      (CommRingCat.KaehlerDifferential ((ρ ≫ β) ≫ regularListQuotientMap s)))
    (bQ' : Module.Basis (Fin d) (regularListQuotientRing s)
      (CommRingCat.KaehlerDifferential (β ≫ regularListQuotientMap s))) :
    let B := regularListQuotientRing s
    let q := regularListQuotientMap s
    let α := ρ ≫ β
    let γM := (ModuleCat.extendScalars q.hom).map (canonicalBaseDifferentialMap ρ β)
    let γQ := canonicalBaseDifferentialMap ρ (β ≫ q)
    let τM := (relativeConormalAffineMiddleIso α q).hom ≫ (tilde.functor B).map γM ≫
      (relativeConormalAffineMiddleIso β q).inv
    let τQ := (relativeDifferentialAffineIso (α ≫ q)).hom ≫ (tilde.functor B).map γQ ≫
      (relativeDifferentialAffineIso (β ≫ q)).inv
    (relativeConormalAffineDeterminantIso α q Ideal.Quotient.mk_surjective
      s hs Ideal.mk_ker.symm hA hB bQ).hom ≫
        (moduleExteriorPowerFunctor (Spec B) (s.length + d)).map τM =
      (moduleTensorLeftFunctor (Spec B)
        (closedImmersionRegularListNormalLineBundle α s hs).val).map
          ((moduleExteriorPowerFunctor (Spec B) d).map τQ) ≫
        (relativeConormalAffineDeterminantIso β q Ideal.Quotient.mk_surjective
          s hs Ideal.mk_ker.symm hA' hB' bQ').hom := by
  intro B q α γM γQ τM τQ
  let Z := Spec B
  let U : Z.Opens := ⊤
  let C := (pullback (Spec.map q)).obj (Scheme.Hom.idealModule (Spec.map q))
  let Ctop := moduleExteriorPower Z C s.length
  let Q := relativeDifferentialSheaf (Spec.map (α ≫ q))
  let Q' := relativeDifferentialSheaf (Spec.map (β ≫ q))
  let Qtop := moduleExteriorPower Z Q d
  let Qtop' := moduleExteriorPower Z Q' d
  let bC := relativeConormalAffineBasis α q Ideal.Quotient.mk_surjective s hs Ideal.mk_ker.symm
  let bC' := relativeConormalAffineBasis β q Ideal.Quotient.mk_surjective s hs Ideal.mk_ker.symm
  let eC := closedImmersionRegularListNormalFrameIso α s hs
  let eQ := affineRelativeTopFrame (α ≫ q) d bQ
  let eS := ((SheafOfModulesOfCommRing.tensorFunctor Z.sheaf).mapIso eC).app Qtop ≪≫
    (SheafOfModulesOfCommRing.tensorLeftUnitIso Z.sheaf).app Qtop ≪≫ eQ
  let normal := closedImmersionRegularListNormalSection α s hs U
  let tangent := affineWedge Q (CommRingCat.KaehlerDifferential (α ≫ q)) d
    (relativeDifferentialAffineIso (α ≫ q)) U bQ
  let z := moduleTensorSection Z Ctop Qtop U normal tangent
  have hz : eS.hom.val.app (op U) z = (1 : Γ(Z, U)) := by
    let : Module Γ(Z, U) (Qtop.val.obj (op U)) := by
      change Module (Z.ringCatSheaf.obj.obj (op U)) _
      infer_instance
    have ht := tensorToUnit_section eC.hom Qtop U normal tangent
    have hn := closedImmersionRegularListNormalFrameIso_normalSection α s hs U
    have hq := canonicalAffineTopFrame_basis (α ≫ q) d bQ U
    change eQ.hom.val.app (op U)
      (((tensorToUnit eC.hom).app Qtop).val.app (op U) z) = _
    exact (congrArg (eQ.hom.val.app (op U))
      (ht.trans ((congrArg (fun r : Γ(Z, U) => r • tangent) hn).trans
        (one_smul Γ(Z, U) tangent)))).trans hq
  apply hom_ext_global_unitFrame eS z hz
  have hsurj : Function.Surjective (relativeConormalAffineLinearG α q
      Ideal.Quotient.mk_surjective) :=
    (ModuleCat.epi_iff_surjective _).mp
      (relativeConormalAffineLinearComplex_epi α q Ideal.Quotient.mk_surjective)
  choose w hw using fun j => hsurj (bQ j)
  let G := relativeConormalAffineLinearG α q Ideal.Quotient.mk_surjective
  let G' := relativeConormalAffineLinearG β q Ideal.Quotient.mk_surjective
  let F := relativeConormalAffineLinearF α q Ideal.Quotient.mk_surjective
  let F' := relativeConormalAffineLinearF β q Ideal.Quotient.mk_surjective
  let γC := canonicalBaseConormalIso ρ β q Ideal.Quotient.mk_surjective
  let eN := relativeConormalAffineIdealPullbackIso α q Ideal.Quotient.mk_surjective
  let eN' := relativeConormalAffineIdealPullbackIso β q Ideal.Quotient.mk_surjective
  let eT := relativeDifferentialAffineIso (α ≫ q)
  let eT' := relativeDifferentialAffineIso (β ≫ q)
  let eM := relativeConormalAffineMiddleIso α q
  let eM' := relativeConormalAffineMiddleIso β q
  let Δ := relativeConormalAffineDeterminantIso α q Ideal.Quotient.mk_surjective
    s hs Ideal.mk_ker.symm hA hB bQ
  let Δ' := relativeConormalAffineDeterminantIso β q Ideal.Quotient.mk_surjective
    s hs Ideal.mk_ker.symm hA' hB' bQ'
  have hw' : (fun j => G (w j)) = bQ := funext hw
  have hin : moduleTensorSection Z Ctop Qtop U
      (affineWedge C _ s.length eN U bC) (affineWedge Q _ d eT U (fun j => G (w j))) = z :=
    congrArg₂ (moduleTensorSection Z Ctop Qtop U)
      (conormalBasisWedge α s hs U) (congrArg (affineWedge Q _ d eT U) hw')
  have hΔ := relativeConormalAffineDeterminantIso_wedge α q Ideal.Quotient.mk_surjective
    s hs Ideal.mk_ker.symm hA hB bQ U bC w
  have hL := (congrArg
    (((moduleExteriorPowerFunctor Z (s.length + d)).map τM).val.app (op U))
    ((congrArg (Δ.hom.val.app (op U)) hin).symm.trans hΔ)).trans
      (affineWedge_map eM eM' γM (s.length + d) U (Fin.append (fun i => F (bC i)) w))
  have hbc : (fun j => γC.hom (bC j)) = bC' := by
    funext j
    rw [relativeConormalAffineBasis_apply, canonicalBaseConormalIso_class,
      relativeConormalAffineBasis_apply]
  have hnormal : affineWedge C _ s.length eN' U (fun j => γC.hom (bC j)) = normal :=
    (congrArg (affineWedge C _ s.length eN' U) hbc).trans
      ((conormalBasisWedge β s hs U).trans (regularListNormalSection_base β α s hs U))
  have hgw : (fun j => G' (γM (w j))) = fun j => γQ (bQ j) := by
    funext j
    have h := congrArg (fun f => f (w j))
      (canonicalBaseConormal_g ρ β q Ideal.Quotient.mk_surjective)
    exact h.symm.trans (congrArg γQ (hw j))
  have hin' : moduleTensorSection Z Ctop Qtop' U
      (affineWedge C _ s.length eN' U (fun j => γC.hom (bC j)))
      (affineWedge Q' _ d eT' U (fun j => G' (γM (w j)))) =
    moduleTensorSection Z Ctop Qtop' U normal
      (affineWedge Q' _ d eT' U (fun j => γQ (bQ j))) :=
    congrArg₂ (moduleTensorSection Z Ctop Qtop' U) hnormal
      (congrArg (affineWedge Q' _ d eT' U) hgw)
  have hmap := moduleTensorLeftFunctor_map_section Ctop
    ((moduleExteriorPowerFunctor Z d).map τQ) U normal tangent
  have hmap' := hmap.trans (congrArg (moduleTensorSection Z Ctop Qtop' U normal)
    (affineWedge_map eT eT' γQ d U bQ))
  have hΔ' := relativeConormalAffineDeterminantIso_wedge β q Ideal.Quotient.mk_surjective
    s hs Ideal.mk_ker.symm hA' hB' bQ' U (fun j => γC.hom (bC j)) (fun j => γM (w j))
  have hR := (congrArg (Δ'.hom.val.app (op U)) hmap').trans
    ((congrArg (Δ'.hom.val.app (op U)) hin'.symm).trans hΔ')
  have hfamily :
      (fun k => γM (Fin.append (fun j => F (bC j)) w k)) =
    Fin.append (fun j => F' (γC.hom (bC j))) (fun j => γM (w j)) := by
    funext k
    refine Fin.addCases (fun j => ?_) (fun j => ?_) k
    · simpa only [Fin.append_left, ModuleCat.comp_apply] using congrArg (fun f => f (bC j))
        (canonicalBaseConormal_f ρ β q Ideal.Quotient.mk_surjective)
    · simp only [Fin.append_right]
  exact hL.trans ((congrArg (affineWedge _ _ (s.length + d) eM' U) hfamily).trans hR.symm)

end AlgebraicGeometry.Scheme.Modules
