/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.Canonical.AffineDeterminant
public import Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.Canonical.Refinements.BaseDifferentials.Geometry
public import Aglib.AlgebraicGeometry.Modules.StructureSheaf.Hom

/-!
# The actual ambient coefficient bridge under change of base

The original differential basis frames the ambient top exterior power and
its scalar-extended middle term. For an arbitrary native differential map,
these two frame conjugates are the same determinant before and after the
original quotient map. The native pullback unit therefore identifies the
actual coefficient bridges, including the geometric base-open map.
-/

@[expose] public section
noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme.Modules.Differentials
open scoped TensorProduct ChangeOfRings

universe u
namespace AlgebraicGeometry.Scheme.Modules

private abbrev coefficientFreeModule (X : Scheme.{u}) (U : X.Opens) (m : ℕ) :
    Module (X.sheaf.obj.obj (op U))
      ((SheafOfModules.free (R := X.ringCatSheaf) (ULift.{u} (Fin m))).val.obj (op U)) := by
  change Module (X.ringCatSheaf.obj.obj (op U))
    ((SheafOfModules.free (R := X.ringCatSheaf) (ULift.{u} (Fin m))).val.obj (op U))
  infer_instance

private def coefficientScalar {B : CommRingCat.{u}} (U : (Spec B).Opens) :
    B →+* Γ(Spec B, U) :=
  ((Scheme.ΓSpecIso B).inv ≫ (Spec B).presheaf.map U.leTop.op).hom

private def coefficientFrameSemilinear {B : CommRingCat.{u}} (E : ModuleCat.{u} B)
    (m : ℕ) (bE : Module.Basis (Fin m) B E) (U : (Spec B).Opens) :
    letI := coefficientFreeModule (Spec B) U m
    E →ₛₗ[coefficientScalar U]
      ((SheafOfModules.free (R := (Spec B).ringCatSheaf) (ULift.{u} (Fin m))).val.obj
        (op U)) := by
  letI := coefficientFreeModule (Spec B) U m
  let F := SheafOfModules.free (R := (Spec B).ringCatSheaf) (ULift.{u} (Fin m))
  let N := ModuleCat.of ((Spec B).sheaf.obj.obj (op U)) (F.val.obj (op U))
  let eF := tildeBasisIso E (bE.reindex Equiv.ulift.symm)
  have g : E ⟶ (ModuleCat.restrictScalars (coefficientScalar U)).obj N := by
    change E ⟶ (modulesSpecToSheaf.obj F).presheaf.obj (op U)
    exact tilde.toOpen E U ≫ (modulesSpecToSheaf.map eF.hom).hom.app (op U)
  exact (ModuleCat.semilinearMapAddEquiv (coefficientScalar U) E N).symm g

private theorem coefficientFrameSemilinear_basis {B : CommRingCat.{u}} (E : ModuleCat.{u} B)
    (m : ℕ) (bE : Module.Basis (Fin m) B E) (U : (Spec B).Opens) (i : Fin m) :
    letI := coefficientFreeModule (Spec B) U m
    coefficientFrameSemilinear E m bE U (bE i) =
      (SheafOfModules.freeSection (R := (Spec B).ringCatSheaf) (ULift.up i)).val (op U) := by
  let := coefficientFreeModule (Spec B) U m
  change (tildeBasisIso E (bE.reindex Equiv.ulift.symm)).hom.val.app (op U)
    (tilde.toOpen E U (bE i)) = _
  simpa only [Module.Basis.reindex_apply, Equiv.symm_symm, Equiv.ulift_apply, ULift.down_up]
    using tildeBasisIso_hom_toOpen E (bE.reindex Equiv.ulift.symm) (ULift.up i) U

private theorem coefficientSemilinearDet {K D V W : Type*} [CommRing K] [CommRing D]
    [AddCommGroup V] [Module K V] [AddCommGroup W] [Module D W] {m : ℕ}
    (bV : Module.Basis (Fin m) K V) (bW : Module.Basis (Fin m) D W)
    {φ : K →+* D} (f : V →ₛₗ[φ] W) (hf : ∀ i, f (bV i) = bW i) (v : Fin m → V) :
    bW.det (f ∘ v) = φ (bV.det v) := by
  have H := Module.Basis.exteriorPowerTopEquiv_mapSemilinear bV bW f
    (exteriorPower.ιMulti K m v)
  have hfb : f ∘ bV = bW := funext hf
  rw [exteriorPower.mapSemilinear_apply_ιMulti, Module.Basis.exteriorPowerTopEquiv_ιMulti,
    Module.Basis.exteriorPowerTopEquiv_ιMulti, hfb, bW.det_self, one_mul] at H
  exact H

private def coefficientTopFrame {B : CommRingCat.{u}} (N : (Spec B).Modules)
    (E : ModuleCat.{u} B) (m : ℕ) (bE : Module.Basis (Fin m) B E) (eN : N ≅ tilde E) :
    moduleExteriorPower (Spec B) N m ≅ SheafOfModules.unit (Spec B).ringCatSheaf :=
  (moduleExteriorPowerFunctor (Spec B) m).mapIso
    (eN ≪≫ tildeBasisIso E (bE.reindex Equiv.ulift.symm)) ≪≫
      SheafOfModulesOfCommRing.exteriorTopFreeIso (Spec B).sheaf m

private def coefficientWedge {B : CommRingCat.{u}} (N : (Spec B).Modules)
    (E : ModuleCat.{u} B) (m : ℕ) (eN : N ≅ tilde E)
    (U : (Spec B).Opens) (v : Fin m → E) :
    (moduleExteriorPower (Spec B) N m).val.obj (op U) :=
  (SheafOfModulesOfCommRing.exteriorPowerMk (Spec B).sheaf N m).app (op U)
    (fun i => eN.inv.val.app (op U) (tilde.toOpen E U (v i)))

private theorem coefficientTopFrame_wedge {B : CommRingCat.{u}} (N : (Spec B).Modules)
    (E : ModuleCat.{u} B) (m : ℕ) (bE : Module.Basis (Fin m) B E) (eN : N ≅ tilde E)
    (U : (Spec B).Opens) (v : Fin m → E) :
    (coefficientTopFrame N E m bE eN).hom.val.app (op U)
      (coefficientWedge N E m eN U v) = algebraMap B Γ(Spec B, U) (bE.det v) := by
  let := coefficientFreeModule (Spec B) U m
  let eF := eN ≪≫ tildeBasisIso E (bE.reindex Equiv.ulift.symm)
  let bF := SheafOfModulesOfCommRing.freeFinSectionsBasis (Spec B).sheaf m (op U)
  let vN := fun i => eN.inv.val.app (op U) (tilde.toOpen E U (v i))
  have hw := congrArg
    ((SheafOfModulesOfCommRing.exteriorTopFreeHom (Spec B).sheaf m).val.app (op U))
    (SheafOfModulesOfCommRing.exteriorPowerFunctor_map_mk (Spec B).sheaf eF.hom m
      (op U) vN)
  have hd := SheafOfModulesOfCommRing.exteriorTopFreeHom_mk (Spec B).sheaf m (op U)
    (fun i => eF.hom.val.app (op U) (vN i))
  change _ = bF.det (fun i => eF.hom.val.app (op U) (vN i)) at hd
  have hfamily : (fun i => eF.hom.val.app (op U) (vN i)) =
      coefficientFrameSemilinear E m bE U ∘ v := by
    funext i
    have h := congrArg (fun k => k.val.app (op U) (tilde.toOpen E U (v i))) eN.inv_hom_id
    exact congrArg ((tildeBasisIso E (bE.reindex Equiv.ulift.symm)).hom.val.app (op U)) h
  have hf (i : Fin m) : coefficientFrameSemilinear E m bE U (bE i) = bF i :=
    (coefficientFrameSemilinear_basis E m bE U i).trans
      (SheafOfModulesOfCommRing.freeFinSectionsBasis_apply (Spec B).sheaf m (op U) i).symm
  have hdet := coefficientSemilinearDet bE bF (coefficientFrameSemilinear E m bE U) hf v
  exact hw.trans (hd.trans ((congrArg bF.det hfamily).trans hdet))

private theorem coefficientWedge_map {B : CommRingCat.{u}} {N N' : (Spec B).Modules}
    {E E' : ModuleCat.{u} B} (e : N ≅ tilde E) (e' : N' ≅ tilde E')
    (f : E ⟶ E') (n : ℕ) (U : (Spec B).Opens) (v : Fin n → E) :
    ((moduleExteriorPowerFunctor (Spec B) n).map
      (e.hom ≫ (tilde.functor B).map f ≫ e'.inv)).val.app (op U)
        (coefficientWedge N E n e U v) =
      coefficientWedge N' E' n e' U (fun i => f (v i)) := by
  let g := e.hom ≫ (tilde.functor B).map f ≫ e'.inv
  let v₀ := fun i => e.inv.val.app (op U) (tilde.toOpen E U (v i))
  have hg (i : Fin n) : g.val.app (op U) (v₀ i) =
      e'.inv.val.app (op U) (tilde.toOpen E' U (f (v i))) := by
    have hc := congrArg (fun z => z.val.app (op U) (tilde.toOpen E U (v i))) e.inv_hom_id
    have hf := ConcreteCategory.congr_hom (tilde.toOpen_map_app f U) (v i)
    exact congrArg (e'.inv.val.app (op U))
      ((congrArg (((tilde.functor B).map f).val.app (op U)) hc).trans hf)
  have hw := SheafOfModulesOfCommRing.exteriorPowerFunctor_map_mk
    (Spec B).sheaf g n (op U) v₀
  exact hw.trans (congrArg
    ((SheafOfModulesOfCommRing.exteriorPowerMk (Spec B).sheaf N' n).app (op U)) (funext hg))

private theorem coefficientTopFrame_map {B : CommRingCat.{u}}
    {N N' : (Spec B).Modules} {E E' : ModuleCat.{u} B}
    (e : N ≅ tilde E) (e' : N' ≅ tilde E') (f : E ⟶ E') (n : ℕ)
    (b : Module.Basis (Fin n) B E) (b' : Module.Basis (Fin n) B E') :
    (coefficientTopFrame N E n b e).inv ≫
        (moduleExteriorPowerFunctor (Spec B) n).map
          (e.hom ≫ (tilde.functor B).map f ≫ e'.inv) ≫
        (coefficientTopFrame N' E' n b' e').hom =
      unitMul (Spec B) ((Scheme.ΓSpecIso B).inv (b'.det (fun i => f (b i)))) := by
  let Z := Spec B
  let a := coefficientTopFrame N E n b e
  let w := coefficientWedge N E n e (⊤ : Z.Opens) b
  have hw : a.hom.val.app (op ⊤) w = (1 : Γ(Z, ⊤)) := by
    simpa only [Module.Basis.det_self, map_one] using
      coefficientTopFrame_wedge N E n b e (⊤ : Z.Opens) b
  have hpre : a.inv.val.app (op ⊤) (1 : Γ(Z, ⊤)) = w :=
    (congrArg (a.inv.val.app (op ⊤)) hw.symm).trans
      (congrArg (fun k => k.val.app (op ⊤) w) a.hom_inv_id)
  apply (unitHomGlobalSectionsEquiv Z (SheafOfModules.unit Z.ringCatSheaf)).injective
  change (coefficientTopFrame N' E' n b' e').hom.val.app (op ⊤)
      (((moduleExteriorPowerFunctor Z n).map
        (e.hom ≫ (tilde.functor B).map f ≫ e'.inv)).val.app (op ⊤)
          (a.inv.val.app (op ⊤) (1 : Γ(Z, ⊤)))) =
    (1 : Γ(Z, ⊤)) * coefficientScalar (⊤ : Z.Opens) (b'.det (fun i => f (b i)))
  rw [hpre, one_mul]
  change (coefficientTopFrame N' E' n b' e').hom.val.app (op ⊤)
      (((moduleExteriorPowerFunctor Z n).map
        (e.hom ≫ (tilde.functor B).map f ≫ e'.inv)).val.app (op ⊤)
          (coefficientWedge N E n e (⊤ : Z.Opens) b)) = _
  rw [coefficientWedge_map, coefficientTopFrame_wedge]
  rfl

private def coefficientExtensionUnit {A B : CommRingCat.{u}} (q : A ⟶ B)
    (E : ModuleCat.{u} A) : E →ₛₗ[q.hom] (ModuleCat.extendScalars q.hom).obj E :=
  (ModuleCat.semilinearMapAddEquiv q.hom E ((ModuleCat.extendScalars q.hom).obj E)).symm
    ((ModuleCat.extendRestrictScalarsAdj q.hom).unit.app E)

private theorem coefficientExtensionUnit_apply {A B : CommRingCat.{u}} (q : A ⟶ B)
    (E : ModuleCat.{u} A) (x : E) :
    coefficientExtensionUnit q E x = (1 : B) ⊗ₜ[A,q.hom] x := rfl

private theorem coefficientBaseChangedBasis_apply {R A : CommRingCat.{u}} (α : R ⟶ A)
    (s : List A) (n : ℕ) (b : Module.Basis (Fin n) A (CommRingCat.KaehlerDifferential α))
    (i : Fin n) :
    affineConormalAmbientBaseChangedBasis α s n b i =
      (1 : regularListQuotientRing s) ⊗ₜ[A,(regularListQuotientMap s).hom] b i := by
  let := (regularListQuotientMap s).hom.toAlgebra
  simp only [affineConormalAmbientBaseChangedBasis, Module.Basis.map_apply,
    Module.Basis.baseChange_apply]
  rfl

private theorem coefficientBaseChanged_det {R S A : CommRingCat.{u}}
    (α : R ⟶ A) (β : S ⟶ A) (s : List A) (n : ℕ)
    (b : Module.Basis (Fin n) A (CommRingCat.KaehlerDifferential α))
    (b' : Module.Basis (Fin n) A (CommRingCat.KaehlerDifferential β))
    (f : CommRingCat.KaehlerDifferential α ⟶ CommRingCat.KaehlerDifferential β) :
    (affineConormalAmbientBaseChangedBasis β s n b').det
        (fun i => (ModuleCat.extendScalars (regularListQuotientMap s).hom).map f
          (affineConormalAmbientBaseChangedBasis α s n b i)) =
      (regularListQuotientMap s) (b'.det (fun i => f (b i))) := by
  let q := regularListQuotientMap s
  let bB := affineConormalAmbientBaseChangedBasis β s n b'
  have hb (i : Fin n) : coefficientExtensionUnit q (CommRingCat.KaehlerDifferential β) (b' i) =
      bB i := by
    rw [coefficientExtensionUnit_apply]
    exact (coefficientBaseChangedBasis_apply β s n b' i).symm
  have hd := coefficientSemilinearDet b' bB
    (coefficientExtensionUnit q (CommRingCat.KaehlerDifferential β)) hb (fun i => f (b i))
  have hm : (fun i => (ModuleCat.extendScalars q.hom).map f
      (affineConormalAmbientBaseChangedBasis α s n b i)) =
    coefficientExtensionUnit q (CommRingCat.KaehlerDifferential β) ∘ (fun i => f (b i)) := by
    funext i
    rw [coefficientBaseChangedBasis_apply, ModuleCat.ExtendScalars.map_tmul]
    rfl
  rw [hm]
  exact hd

private theorem coefficientUnitMul_pullback {X Y : Scheme.{u}} (k : X ⟶ Y) (r : Γ(Y, ⊤)) :
    (pullback k).map (unitMul Y r) ≫ (pullbackUnitIso k).hom =
      (pullbackUnitIso k).hom ≫ unitMul X (k.appTop.hom r) := by
  apply ((pullbackPushforwardAdjunction k).homEquiv _ _).injective
  rw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_right,
    pullbackUnitIso_homEquiv]
  apply AlgebraicGeometry.Scheme.Modules.hom_ext
  intro U
  ext x
  change Γ(Y, U) at x
  change (k.app U).hom (x * (Y.presheaf.map U.leTop.op).hom r) =
    (k.app U).hom x * (X.presheaf.map
      (homOfLE (show k ⁻¹ᵁ U ≤ ⊤ from le_top)).op).hom (k.appTop.hom r)
  rw [map_mul]
  congr 1
  have h : Y.presheaf.map U.leTop.op ≫ k.app U =
      k.appTop ≫ X.presheaf.map (homOfLE (show k ⁻¹ᵁ U ≤ ⊤ from le_top)).op := by
    rw [Scheme.Hom.app_eq_appLE, Scheme.Hom.appTop,
      Scheme.Hom.app_eq_appLE,
      Scheme.Hom.map_appLE, Scheme.Hom.appLE_map]
  exact congrArg (fun f => CommRingCat.Hom.hom f r) h


private theorem coefficientPullbackConjugate {X Y : Scheme.{u}} (k : X ⟶ Y)
    {L L' : Y.Modules} (e : L ≅ SheafOfModules.unit Y.ringCatSheaf)
    (e' : L' ≅ SheafOfModules.unit Y.ringCatSheaf) (f : L ⟶ L')
    (r : Γ(Y, ⊤)) (h : e.inv ≫ f ≫ e'.hom = unitMul Y r) :
    ((pullback k).mapIso e ≪≫ pullbackUnitIso k).inv ≫ (pullback k).map f ≫
        ((pullback k).mapIso e' ≪≫ pullbackUnitIso k).hom =
      unitMul X (k.appTop.hom r) := by
  simp only [Iso.trans_inv, Iso.trans_hom, Functor.mapIso_inv, Functor.mapIso_hom]
  rw [Category.assoc, ← Functor.map_comp_assoc, ← Functor.map_comp_assoc,
    Category.assoc, h, coefficientUnitMul_pullback, Iso.inv_hom_id_assoc]

private theorem coefficientIso_naturality {R S A : CommRingCat.{u}}
    (α : R ⟶ A) (β : S ⟶ A) (s : List A) (n : ℕ)
    (b : Module.Basis (Fin n) A (CommRingCat.KaehlerDifferential α))
    (b' : Module.Basis (Fin n) A (CommRingCat.KaehlerDifferential β))
    (f : CommRingCat.KaehlerDifferential α ⟶ CommRingCat.KaehlerDifferential β) :
    let B := regularListQuotientRing s
    let q := regularListQuotientMap s
    let dA := (relativeDifferentialAffineIso α).hom ≫ (tilde.functor A).map f ≫
      (relativeDifferentialAffineIso β).inv
    let dM := (relativeConormalAffineMiddleIso α q).hom ≫
      (tilde.functor B).map ((ModuleCat.extendScalars q.hom).map f) ≫
      (relativeConormalAffineMiddleIso β q).inv
    (affineConormalAmbientCoefficientIso α s n b).hom ≫
        (pullback (Spec.map q)).map ((moduleExteriorPowerFunctor (Spec A) n).map dA) =
      (moduleExteriorPowerFunctor (Spec B) n).map dM ≫
        (affineConormalAmbientCoefficientIso β s n b').hom := by
  intro B q dA dM
  let a := affineConormalAmbientMiddleTopFrame α s n b
  let a' := affineConormalAmbientMiddleTopFrame β s n b'
  let e := affineRelativeTopFrame α n b
  let e' := affineRelativeTopFrame β n b'
  let p := (pullback (Spec.map q)).mapIso e ≪≫ pullbackUnitIso (Spec.map q)
  let p' := (pullback (Spec.map q)).mapIso e' ≪≫ pullbackUnitIso (Spec.map q)
  let F := (moduleExteriorPowerFunctor (Spec A) n).map dA
  let G := (moduleExteriorPowerFunctor (Spec B) n).map dM
  let r := b'.det (fun i => f (b i))
  have hA : e.inv ≫ F ≫ e'.hom = unitMul (Spec A) ((Scheme.ΓSpecIso A).inv r) :=
    coefficientTopFrame_map (relativeDifferentialAffineIso α)
      (relativeDifferentialAffineIso β) f n b b'
  have hP := coefficientPullbackConjugate (Spec.map q) e e' F
    ((Scheme.ΓSpecIso A).inv r) hA
  have hΓ := ConcreteCategory.congr_hom (Scheme.ΓSpecIso_inv_naturality q) r
  change (Scheme.ΓSpecIso B).inv (q r) =
    (Spec.map q).appTop.hom ((Scheme.ΓSpecIso A).inv r) at hΓ
  rw [← hΓ] at hP
  have hM := coefficientTopFrame_map (relativeConormalAffineMiddleIso α q)
    (relativeConormalAffineMiddleIso β q) ((ModuleCat.extendScalars q.hom).map f) n
    (affineConormalAmbientBaseChangedBasis α s n b)
    (affineConormalAmbientBaseChangedBasis β s n b')
  change a.inv ≫ G ≫ a'.hom = unitMul (Spec B)
    ((Scheme.ΓSpecIso B).inv
      ((affineConormalAmbientBaseChangedBasis β s n b').det
        (fun i => (ModuleCat.extendScalars q.hom).map f
          (affineConormalAmbientBaseChangedBasis α s n b i)))) at hM
  rw [coefficientBaseChanged_det] at hM
  have hratio : a.inv ≫ G ≫ a'.hom = p.inv ≫ (pullback (Spec.map q)).map F ≫ p'.hom :=
    hM.trans hP.symm
  change (a ≪≫ p.symm).hom ≫ (pullback (Spec.map q)).map F =
    G ≫ (a' ≪≫ p'.symm).hom
  apply (cancel_epi a.inv).mp
  apply (cancel_mono p'.hom).mp
  simpa only [Iso.trans_hom, Iso.symm_hom, Category.assoc,
    Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id] using hratio.symm

/-- The actual ambient coefficient bridge commutes with the original native base
map. Both differential bases are arbitrary; the base map need not be invertible. -/
theorem canonicalBaseAmbientCoefficient
    {R S A : CommRingCat.{u}} (ρ : R ⟶ S) (β : S ⟶ A) (s : List A) (n : ℕ)
    (b : Module.Basis (Fin n) A (CommRingCat.KaehlerDifferential (ρ ≫ β)))
    (b' : Module.Basis (Fin n) A (CommRingCat.KaehlerDifferential β)) :
    let B := regularListQuotientRing s
    let q := regularListQuotientMap s
    let dA := (relativeDifferentialAffineIso (ρ ≫ β)).hom ≫
      (tilde.functor A).map (canonicalBaseDifferentialMap ρ β) ≫
      (relativeDifferentialAffineIso β).inv
    let dM := (relativeConormalAffineMiddleIso (ρ ≫ β) q).hom ≫
      (tilde.functor B).map
        ((ModuleCat.extendScalars q.hom).map (canonicalBaseDifferentialMap ρ β)) ≫
      (relativeConormalAffineMiddleIso β q).inv
    (affineConormalAmbientCoefficientIso (ρ ≫ β) s n b).hom ≫
        (pullback (Spec.map q)).map ((moduleExteriorPowerFunctor (Spec A) n).map dA) =
      (moduleExteriorPowerFunctor (Spec B) n).map dM ≫
        (affineConormalAmbientCoefficientIso β s n b').hom :=
  coefficientIso_naturality (ρ ≫ β) β s n b b' (canonicalBaseDifferentialMap ρ β)

/-- The same actual coefficient square uses the original identity/source-open
relative differential comparison, rather than a chosen replacement map. -/
theorem canonicalBaseAmbientCoefficient_geometry
    {R S A : CommRingCat.{u}} (ρ : R ⟶ S) (β : S ⟶ A)
    [IsOpenImmersion (Spec.map ρ)]
    (h : 𝟙 (Spec A) ≫ Spec.map (ρ ≫ β) = Spec.map β ≫ Spec.map ρ)
    (s : List A) (n : ℕ)
    (b : Module.Basis (Fin n) A (CommRingCat.KaehlerDifferential (ρ ≫ β)))
    (b' : Module.Basis (Fin n) A (CommRingCat.KaehlerDifferential β)) :
    let B := regularListQuotientRing s
    let q := regularListQuotientMap s
    let dM := (relativeConormalAffineMiddleIso (ρ ≫ β) q).hom ≫
      (tilde.functor B).map
        ((ModuleCat.extendScalars q.hom).map (canonicalBaseDifferentialMap ρ β)) ≫
      (relativeConormalAffineMiddleIso β q).inv
    (affineConormalAmbientCoefficientIso (ρ ≫ β) s n b).hom ≫
        (pullback (Spec.map q)).map ((moduleExteriorPowerFunctor (Spec A) n).map
          (canonicalBaseDifferentialSheafMap ρ β h)) =
      (moduleExteriorPowerFunctor (Spec B) n).map dM ≫
        (affineConormalAmbientCoefficientIso β s n b').hom := by
  intro B q dM
  have hg := canonicalBaseDifferentialMap_geometry ρ β h
  change canonicalBaseDifferentialSheafMap ρ β h = _ at hg
  rw [hg]
  exact canonicalBaseAmbientCoefficient ρ β s n b b'

end AlgebraicGeometry.Scheme.Modules
