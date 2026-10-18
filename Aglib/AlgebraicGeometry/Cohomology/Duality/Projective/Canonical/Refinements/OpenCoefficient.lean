/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.Canonical.Refinements.OpenCoefficient.Units
public import Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.Canonical.Refinements.OpenPullback

/-!
# The original ambient coefficient bridge on an affine open square

Original unit sections and their wedges compare the actual framed ambient
coefficient maps when both affine rings change. The native restriction,
pullback and exterior comparison maps remain explicit.
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

private def pulledUnitSection {X Y : Scheme.{u}} (f : X ⟶ Y) {M : Y.Modules}
    (v : SheafOfModules.unit Y.ringCatSheaf ⟶ M) :
    SheafOfModules.unit X.ringCatSheaf ⟶ (pullback f).obj M :=
  (pullbackUnitIso f).inv ≫ (pullback f).map v

private def restrictedUnitSection {X Y : Scheme.{u}} (j : X ⟶ Y) [IsOpenImmersion j]
    {M : Y.Modules} (v : SheafOfModules.unit Y.ringCatSheaf ⟶ M) :
    SheafOfModules.unit X.ringCatSheaf ⟶ M.restrict j :=
  (restrictUnitIso j).inv ≫ (restrictFunctor j).map v

private theorem restrictedUnitSection_app {X Y : Scheme.{u}} (j : X ⟶ Y)
    [IsOpenImmersion j] {M : Y.Modules} (v : SheafOfModules.unit Y.ringCatSheaf ⟶ M)
    (U : X.Opens) :
    (restrictedUnitSection j v).val.app (op U) (1 : Γ(X, U)) =
      v.val.app (op (j ''ᵁ U)) (1 : Γ(Y, j ''ᵁ U)) := by
  change v.val.app (op (j ''ᵁ U)) ((j.appIso U).inv (1 : Γ(X, U))) = _
  rw [map_one]

private def wedgeUnitSection (X : Scheme.{u}) (M : X.Modules) (n : ℕ)
    (v : Fin n → (SheafOfModules.unit X.ringCatSheaf ⟶ M)) :
    SheafOfModules.unit X.ringCatSheaf ⟶ moduleExteriorPower X M n :=
  (unitHomGlobalSectionsEquiv X (moduleExteriorPower X M n)).symm
    ((SheafOfModulesOfCommRing.exteriorPowerMk X.sheaf M n).app (op ⊤)
      (fun i => (v i).val.app (op ⊤) (1 : Γ(X, ⊤))))

private theorem wedgeUnitSection_app (X : Scheme.{u}) (M : X.Modules) (n : ℕ)
    (v : Fin n → (SheafOfModules.unit X.ringCatSheaf ⟶ M)) (U : X.Opens) :
    (wedgeUnitSection X M n v).val.app (op U) (1 : Γ(X, U)) =
      (SheafOfModulesOfCommRing.exteriorPowerMk X.sheaf M n).app (op U)
        (fun i => (v i).val.app (op U) (1 : Γ(X, U))) := by
  rw [show (wedgeUnitSection X M n v).val.app (op U) (1 : Γ(X, U)) =
      (1 : Γ(X, U)) • (moduleExteriorPower X M n).presheaf.map U.leTop.op
        ((SheafOfModulesOfCommRing.exteriorPowerMk X.sheaf M n).app (op ⊤)
          (fun i => (v i).val.app (op ⊤) (1 : Γ(X, ⊤)))) from
    unitHomGlobalSectionsEquiv_symm_app X (moduleExteriorPower X M n) _ U 1]
  rw [one_smul]
  have hv (i : Fin n) : M.presheaf.map U.leTop.op
      ((v i).val.app (op ⊤) (1 : Γ(X, ⊤))) = (v i).val.app (op U) (1 : Γ(X, U)) := by
    have hh := unitHomGlobalSectionsEquiv_symm_app X M
      (unitHomGlobalSectionsEquiv X M (v i)) U 1
    rw [Equiv.symm_apply_apply, one_smul] at hh
    exact hh.symm
  exact (SheafOfModulesOfCommRing.exteriorPowerMk_naturality X.sheaf M n U.leTop.op _).trans
    (congrArg ((SheafOfModulesOfCommRing.exteriorPowerMk X.sheaf M n).app (op U)) (funext hv))

private theorem wedgeUnitSection_map (X : Scheme.{u}) {M N : X.Modules} (f : M ⟶ N)
    (n : ℕ) (v : Fin n → (SheafOfModules.unit X.ringCatSheaf ⟶ M)) :
    wedgeUnitSection X M n v ≫ (moduleExteriorPowerFunctor X n).map f =
      wedgeUnitSection X N n (fun i => v i ≫ f) := by
  apply (unitHomGlobalSectionsEquiv X (moduleExteriorPower X N n)).injective
  change ((moduleExteriorPowerFunctor X n).map f).val.app (op ⊤)
      ((wedgeUnitSection X M n v).val.app (op ⊤) (1 : Γ(X, ⊤))) =
    (wedgeUnitSection X N n (fun i => v i ≫ f)).val.app (op ⊤) (1 : Γ(X, ⊤))
  rw [wedgeUnitSection_app, wedgeUnitSection_app]
  exact SheafOfModulesOfCommRing.exteriorPowerFunctor_map_mk X.sheaf f n (op ⊤) _

private theorem wedgeUnitSection_restrict {X Y : Scheme.{u}} (j : X ⟶ Y)
    [IsOpenImmersion j] (M : Y.Modules) (n : ℕ)
    (v : Fin n → (SheafOfModules.unit Y.ringCatSheaf ⟶ M)) :
    restrictedUnitSection j (wedgeUnitSection Y M n v) ≫
        (moduleExteriorPowerRestrictionIso j M n).inv =
      wedgeUnitSection X (M.restrict j) n (fun i => restrictedUnitSection j (v i)) := by
  apply (unitHomGlobalSectionsEquiv X (moduleExteriorPower X (M.restrict j) n)).injective
  change (moduleExteriorPowerRestrictionIso j M n).inv.val.app (op ⊤)
      ((restrictedUnitSection j (wedgeUnitSection Y M n v)).val.app (op ⊤)
        (1 : Γ(X, ⊤))) =
    (wedgeUnitSection X (M.restrict j) n (fun i => restrictedUnitSection j (v i))).val.app
      (op ⊤) (1 : Γ(X, ⊤))
  rw [restrictedUnitSection_app, wedgeUnitSection_app, wedgeUnitSection_app,
    moduleExteriorPowerRestrictionIso_inv_mk]
  congr 1
  funext i
  exact (restrictedUnitSection_app j (v i) ⊤).symm

/-- The native mixed square carries each original pulled section to the pullback
of its original restriction, with both original unit isomorphisms retained. -/
theorem canonicalOpenPullbackSquare_section
    {W X V Y : Scheme.{u}} (p : W ⟶ X) (q : W ⟶ V) (f : X ⟶ Y) (j : V ⟶ Y)
    [IsOpenImmersion p] [IsOpenImmersion j] (h : p ≫ f = q ≫ j)
    {M : Y.Modules} (v : SheafOfModules.unit Y.ringCatSheaf ⟶ M) :
    (restrictUnitIso p).inv ≫
        (restrictFunctor p).map ((pullbackUnitIso f).inv ≫ (pullback f).map v) ≫
        (pullbackOpenSquare p q f j h).hom.app M =
      (pullbackUnitIso q).inv ≫
        (pullback q).map ((restrictUnitIso j).inv ≫ (restrictFunctor j).map v) := by
  let S := pullbackOpenSquare p q f j h
  have hu : (restrictUnitIso p).inv ≫
      (restrictFunctor p).map (pullbackUnitIso f).inv ≫
      S.hom.app (SheafOfModules.unit Y.ringCatSheaf) =
    (pullbackUnitIso q).inv ≫ (pullback q).map (restrictUnitIso j).inv := by
    apply (cancel_mono ((pullback q).map (restrictUnitIso j).hom)).mp
    apply (cancel_mono (pullbackUnitIso q).hom).mp
    simp only [Category.assoc]
    rw [canonicalOpenPullbackSquare_unit]
    simp only [← Functor.map_comp_assoc, Iso.inv_hom_id]
    erw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id]
    simp only [Category.id_comp, Iso.inv_hom_id]
  have hn := S.hom.naturality v
  change (restrictFunctor p).map ((pullback f).map v) ≫ S.hom.app M =
    S.hom.app (SheafOfModules.unit Y.ringCatSheaf) ≫
      (pullback q).map ((restrictFunctor j).map v) at hn
  simp only [Functor.map_comp, Category.assoc]
  rw [hn]
  exact (congrArg (fun k => k ≫ (pullback q).map ((restrictFunctor j).map v)) hu)

private theorem canonicalAffineUnitSection_surjective {A : CommRingCat.{u}}
    (E : ModuleCat.{u} A) : Function.Surjective (canonicalAffineUnitSection E) := by
  intro v
  obtain ⟨x, hx⟩ := (tilde.isoTop E).toLinearEquiv.surjective
    (unitHomGlobalSectionsEquiv (Spec A) (tilde E) v)
  refine ⟨x, ?_⟩
  apply (unitHomGlobalSectionsEquiv (Spec A) (tilde E)).injective
  simp only [canonicalAffineUnitSection, Equiv.apply_symm_apply]
  change tilde.toOpen E ⊤ x = _ at hx
  exact hx

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



/-- The original affine differential vector as its actual structure-module section. -/
def canonicalDifferentialUnitSection {R A : CommRingCat.{u}} (α : R ⟶ A)
    (x : CommRingCat.KaehlerDifferential α) :
    SheafOfModules.unit (Spec A).ringCatSheaf ⟶ relativeDifferentialSheaf (Spec.map α) :=
  canonicalAffineUnitSection (CommRingCat.KaehlerDifferential α) x ≫
    (relativeDifferentialAffineIso α).inv

/-- The original differential section on every open. -/
theorem canonicalDifferentialUnitSection_app {R A : CommRingCat.{u}} (α : R ⟶ A)
    (x : CommRingCat.KaehlerDifferential α) (U : (Spec A).Opens) :
    (canonicalDifferentialUnitSection α x).val.app (op U) (1 : Γ(Spec A, U)) =
      (relativeDifferentialAffineIso α).inv.val.app (op U)
        (tilde.toOpen (CommRingCat.KaehlerDifferential α) U x) := by
  change (relativeDifferentialAffineIso α).inv.val.app (op U)
    ((canonicalAffineUnitSection (CommRingCat.KaehlerDifferential α) x).val.app (op U)
      (1 : Γ(Spec A, U))) = _
  rw [canonicalAffineUnitSection_app]

/-- The actual pullback of an affine differential section is its original unit tensor. -/
theorem canonicalDifferentialUnitSection_pullback_hom
    {R A B : CommRingCat.{u}} (α : R ⟶ A) (σ : A ⟶ B)
    (x : CommRingCat.KaehlerDifferential α) :
    (pullbackUnitIso (Spec.map σ)).inv ≫
        (pullback (Spec.map σ)).map (canonicalDifferentialUnitSection α x) =
      canonicalAffineUnitSection
          ((ModuleCat.extendScalars σ.hom).obj (CommRingCat.KaehlerDifferential α))
          ((1 : B) ⊗ₜ[A,σ.hom] x) ≫
        (relativeConormalAffineMiddleIso α σ).inv := by
  apply (cancel_mono (relativeConormalAffineMiddleIso α σ).hom).mp
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  simp only [canonicalDifferentialUnitSection, relativeConormalAffineMiddleIso,
    Iso.trans_hom, Functor.mapIso_hom, Functor.map_comp, Category.assoc]
  have hc : (pullback (Spec.map σ)).map (relativeDifferentialAffineIso α).inv ≫
      (pullback (Spec.map σ)).map (relativeDifferentialAffineIso α).hom = 𝟙 _ := by
    rw [← Functor.map_comp, Iso.inv_hom_id, CategoryTheory.Functor.map_id]
  erw [reassoc_of% hc]
  exact canonicalAffineUnitSection_pullback σ (CommRingCat.KaehlerDifferential α) x

/-- The original affine middle comparison retains the same unit tensor on every open. -/
theorem canonicalDifferentialUnitSection_pullback_app
    {R A B : CommRingCat.{u}} (α : R ⟶ A) (σ : A ⟶ B)
    (x : CommRingCat.KaehlerDifferential α) (U : (Spec B).Opens) :
    ((pullbackUnitIso (Spec.map σ)).inv ≫
      (pullback (Spec.map σ)).map (canonicalDifferentialUnitSection α x)).val.app (op U)
        (1 : Γ(Spec B, U)) =
      (relativeConormalAffineMiddleIso α σ).inv.val.app (op U)
        (tilde.toOpen
          ((ModuleCat.extendScalars σ.hom).obj (CommRingCat.KaehlerDifferential α)) U
          ((1 : B) ⊗ₜ[A,σ.hom] x)) := by
  rw [canonicalDifferentialUnitSection_pullback_hom]
  change (relativeConormalAffineMiddleIso α σ).inv.val.app (op U)
    ((canonicalAffineUnitSection
      ((ModuleCat.extendScalars σ.hom).obj (CommRingCat.KaehlerDifferential α))
        ((1 : B) ⊗ₜ[A,σ.hom] x)).val.app (op U) (1 : Γ(Spec B, U))) = _
  rw [canonicalAffineUnitSection_app]

private theorem framedWedgeUnitSection {A : CommRingCat.{u}} (N : (Spec A).Modules)
    (E : ModuleCat.{u} A) (e : N ≅ tilde E) (n : ℕ)
    (b : Module.Basis (Fin n) A E) (v : Fin n → E) :
    wedgeUnitSection (Spec A) N n (fun i => canonicalAffineUnitSection E (v i) ≫ e.inv) ≫
        (coefficientTopFrame N E n b e).hom =
      unitMul (Spec A) ((Scheme.ΓSpecIso A).inv (b.det v)) := by
  apply (unitHomGlobalSectionsEquiv (Spec A)
    (SheafOfModules.unit (Spec A).ringCatSheaf)).injective
  change (coefficientTopFrame N E n b e).hom.val.app (op ⊤)
      ((wedgeUnitSection (Spec A) N n
        (fun i => canonicalAffineUnitSection E (v i) ≫ e.inv)).val.app (op ⊤)
          (1 : Γ(Spec A, ⊤))) =
    (1 : Γ(Spec A, ⊤)) * coefficientScalar (⊤ : (Spec A).Opens) (b.det v)
  rw [wedgeUnitSection_app, one_mul]
  have hv : (fun i => (canonicalAffineUnitSection E (v i) ≫ e.inv).val.app (op ⊤)
      (1 : Γ(Spec A, ⊤))) =
    fun i => e.inv.val.app (op ⊤) (tilde.toOpen E ⊤ (v i)) := by
    funext i
    change e.inv.val.app (op ⊤)
      ((canonicalAffineUnitSection E (v i)).val.app (op ⊤) (1 : Γ(Spec A, ⊤))) = _
    rw [canonicalAffineUnitSection_app]
  rw [hv]
  exact coefficientTopFrame_wedge N E n b e ⊤ v

private theorem pulledWedgeUnitSection_frame {R A : CommRingCat.{u}} (α : R ⟶ A)
    (s : List A) (n : ℕ)
    (b : Module.Basis (Fin n) A (CommRingCat.KaehlerDifferential α))
    (v : Fin n → CommRingCat.KaehlerDifferential α) :
    wedgeUnitSection (Spec (regularListQuotientRing s))
        ((pullback (Spec.map (regularListQuotientMap s))).obj
          (relativeDifferentialSheaf (Spec.map α))) n
        (fun i => pulledUnitSection (Spec.map (regularListQuotientMap s))
          (canonicalDifferentialUnitSection α (v i))) ≫
        (affineConormalAmbientMiddleTopFrame α s n b).hom =
      unitMul (Spec (regularListQuotientRing s))
        ((Scheme.ΓSpecIso (regularListQuotientRing s)).inv
          ((regularListQuotientMap s) (b.det v))) := by
  let B := regularListQuotientRing s
  let q := regularListQuotientMap s
  let E := CommRingCat.KaehlerDifferential α
  let E' := (ModuleCat.extendScalars q.hom).obj E
  let b' := affineConormalAmbientBaseChangedBasis α s n b
  have hv : (fun i => pulledUnitSection (Spec.map q) (canonicalDifferentialUnitSection α (v i))) =
      fun i => canonicalAffineUnitSection E' ((1 : B) ⊗ₜ[A,q.hom] v i) ≫
        (relativeConormalAffineMiddleIso α q).inv := by
    funext i
    exact canonicalDifferentialUnitSection_pullback_hom α q (v i)
  rw [hv]
  have hb (i : Fin n) : coefficientExtensionUnit q E (b i) = b' i := by
    rw [coefficientExtensionUnit_apply]
    exact (coefficientBaseChangedBasis_apply α s n b i).symm
  have hd := coefficientSemilinearDet b b' (coefficientExtensionUnit q E) hb v
  change b'.det (fun i => (1 : B) ⊗ₜ[A,q.hom] v i) = q (b.det v) at hd
  have hh := framedWedgeUnitSection
    ((pullback (Spec.map q)).obj (relativeDifferentialSheaf (Spec.map α))) E'
    (relativeConormalAffineMiddleIso α q) n b' (fun i => (1 : B) ⊗ₜ[A,q.hom] v i)
  rw [hd] at hh
  exact hh

private theorem coefficient_wedge_vectors {R A : CommRingCat.{u}} (α : R ⟶ A)
    (s : List A) (n : ℕ)
    (b : Module.Basis (Fin n) A (CommRingCat.KaehlerDifferential α))
    (v : Fin n → CommRingCat.KaehlerDifferential α) :
    wedgeUnitSection (Spec (regularListQuotientRing s))
        ((pullback (Spec.map (regularListQuotientMap s))).obj
          (relativeDifferentialSheaf (Spec.map α))) n
        (fun i => pulledUnitSection (Spec.map (regularListQuotientMap s))
          (canonicalDifferentialUnitSection α (v i))) ≫
        (affineConormalAmbientCoefficientIso α s n b).hom =
      pulledUnitSection (Spec.map (regularListQuotientMap s))
        (wedgeUnitSection (Spec A) (relativeDifferentialSheaf (Spec.map α)) n
          (fun i => canonicalDifferentialUnitSection α (v i))) := by
  let B := regularListQuotientRing s
  let q := regularListQuotientMap s
  let a := affineConormalAmbientMiddleTopFrame α s n b
  let e := affineRelativeTopFrame α n b
  let p := (pullback (Spec.map q)).mapIso e ≪≫ pullbackUnitIso (Spec.map q)
  let w := wedgeUnitSection (Spec A) (relativeDifferentialSheaf (Spec.map α)) n
    (fun i => canonicalDifferentialUnitSection α (v i))
  have hA : w ≫ e.hom = unitMul (Spec A) ((Scheme.ΓSpecIso A).inv (b.det v)) :=
    framedWedgeUnitSection _ _ (relativeDifferentialAffineIso α) n b v
  have hP : pulledUnitSection (Spec.map q) w ≫ p.hom =
      unitMul (Spec B) ((Spec.map q).appTop.hom ((Scheme.ΓSpecIso A).inv (b.det v))) := by
    simp only [pulledUnitSection, p, Iso.trans_hom, Functor.mapIso_hom, Category.assoc]
    rw [← Functor.map_comp_assoc, hA, coefficientUnitMul_pullback, Iso.inv_hom_id_assoc]
  have hΓ := ConcreteCategory.congr_hom (Scheme.ΓSpecIso_inv_naturality q) (b.det v)
  change (Scheme.ΓSpecIso B).inv (q (b.det v)) =
    (Spec.map q).appTop.hom ((Scheme.ΓSpecIso A).inv (b.det v)) at hΓ
  rw [← hΓ] at hP
  apply (cancel_mono p.hom).mp
  change (_ ≫ (a ≪≫ p.symm).hom) ≫ p.hom = pulledUnitSection (Spec.map q) w ≫ p.hom
  simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  exact (pulledWedgeUnitSection_frame α s n b v).trans hP.symm

private theorem coefficient_wedge_sections {R A : CommRingCat.{u}} (α : R ⟶ A)
    (s : List A) (n : ℕ)
    (b : Module.Basis (Fin n) A (CommRingCat.KaehlerDifferential α))
    (v : Fin n → (SheafOfModules.unit (Spec A).ringCatSheaf ⟶
      relativeDifferentialSheaf (Spec.map α))) :
    wedgeUnitSection (Spec (regularListQuotientRing s))
        ((pullback (Spec.map (regularListQuotientMap s))).obj
          (relativeDifferentialSheaf (Spec.map α))) n
        (fun i => pulledUnitSection (Spec.map (regularListQuotientMap s)) (v i)) ≫
        (affineConormalAmbientCoefficientIso α s n b).hom =
      pulledUnitSection (Spec.map (regularListQuotientMap s))
        (wedgeUnitSection (Spec A) (relativeDifferentialSheaf (Spec.map α)) n v) := by
  classical
  have hv (i : Fin n) : ∃ x : CommRingCat.KaehlerDifferential α,
      canonicalDifferentialUnitSection α x = v i := by
    obtain ⟨x, hx⟩ := canonicalAffineUnitSection_surjective
      (CommRingCat.KaehlerDifferential α) (v i ≫ (relativeDifferentialAffineIso α).hom)
    refine ⟨x, ?_⟩
    simp only [canonicalDifferentialUnitSection, hx, Category.assoc, Iso.hom_inv_id,
      Category.comp_id]
  choose x hx using hv
  have hf : (fun i => canonicalDifferentialUnitSection α (x i)) = v := funext hx
  rw [← hf]
  exact coefficient_wedge_vectors α s n b x

private theorem pulledUnitSection_comp {X Y : Scheme.{u}} (f : X ⟶ Y)
    {M N : Y.Modules} (v : SheafOfModules.unit Y.ringCatSheaf ⟶ M) (g : M ⟶ N) :
    pulledUnitSection f v ≫ (pullback f).map g = pulledUnitSection f (v ≫ g) := by
  simp only [pulledUnitSection, Functor.map_comp, Category.assoc]

private theorem restrictedUnitSection_comp {X Y : Scheme.{u}} (j : X ⟶ Y)
    [IsOpenImmersion j] {M N : Y.Modules}
    (v : SheafOfModules.unit Y.ringCatSheaf ⟶ M) (g : M ⟶ N) :
    restrictedUnitSection j v ≫ (restrictFunctor j).map g =
      restrictedUnitSection j (v ≫ g) := by
  simp only [restrictedUnitSection, Functor.map_comp, Category.assoc]

private theorem wedgeUnitSection_topRestriction {X Y : Scheme.{u}} (j : X ⟶ Y)
    [IsOpenImmersion j] {M : Y.Modules} {N : X.Modules} (e : M.restrict j ≅ N)
    (n : ℕ) (v : Fin n → (SheafOfModules.unit Y.ringCatSheaf ⟶ M)) :
    restrictedUnitSection j (wedgeUnitSection Y M n v) ≫
        ((moduleExteriorPowerRestrictionIso j M n).symm ≪≫
          (moduleExteriorPowerFunctor X n).mapIso e).hom =
      wedgeUnitSection X N n (fun i => restrictedUnitSection j (v i) ≫ e.hom) := by
  simp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom]
  rw [← Category.assoc, wedgeUnitSection_restrict, wedgeUnitSection_map]

/-- The original affine ambient coefficient bridge commutes with the native mixed
open square and the original exterior-restriction maps. The two bases are arbitrary.
The ambient comparison is used as its actual morphism; no naturality premise is supplied. -/
theorem canonicalOpenAmbientCoefficient
    {R A R' A' : CommRingCat.{u}} (α : R ⟶ A) (α' : R' ⟶ A')
    (s : List A) (t : List A') (n : ℕ)
    (b : Module.Basis (Fin n) A (CommRingCat.KaehlerDifferential α))
    (b' : Module.Basis (Fin n) A' (CommRingCat.KaehlerDifferential α'))
    (p : Spec (regularListQuotientRing t) ⟶ Spec (regularListQuotientRing s))
    (j : Spec A' ⟶ Spec A) [IsOpenImmersion p] [IsOpenImmersion j]
    (H : p ≫ Spec.map (regularListQuotientMap s) = Spec.map (regularListQuotientMap t) ≫ j)
    (eA : (relativeDifferentialSheaf (Spec.map α)).restrict j ≅
      relativeDifferentialSheaf (Spec.map α')) :
    let S := canonicalPullbackOpenSquareIso (Spec.map (regularListQuotientMap s))
      (Spec.map (regularListQuotientMap t)) p j H
    let eM := S.app (relativeDifferentialSheaf (Spec.map α)) ≪≫
      (pullback (Spec.map (regularListQuotientMap t))).mapIso eA
    let eT := (moduleExteriorPowerRestrictionIso j
      (relativeDifferentialSheaf (Spec.map α)) n).symm ≪≫
        (moduleExteriorPowerFunctor (Spec A') n).mapIso eA
    let eC := S.app (moduleExteriorPower (Spec A) (relativeDifferentialSheaf (Spec.map α)) n) ≪≫
      (pullback (Spec.map (regularListQuotientMap t))).mapIso eT
    let eMT := (moduleExteriorPowerRestrictionIso p
      ((pullback (Spec.map (regularListQuotientMap s))).obj
        (relativeDifferentialSheaf (Spec.map α))) n).symm ≪≫
      (moduleExteriorPowerFunctor (Spec (regularListQuotientRing t)) n).mapIso eM
    (restrictFunctor p).map (affineConormalAmbientCoefficientIso α s n b).hom ≫ eC.hom =
      eMT.hom ≫ (affineConormalAmbientCoefficientIso α' t n b').hom := by
  intro S eM eT eC eMT
  let X := Spec A
  let X' := Spec A'
  let Y := Spec (regularListQuotientRing s)
  let Y' := Spec (regularListQuotientRing t)
  let f := Spec.map (regularListQuotientMap s)
  let f' := Spec.map (regularListQuotientMap t)
  let Ω := relativeDifferentialSheaf (Spec.map α)
  let Ω' := relativeDifferentialSheaf (Spec.map α')
  let M := (pullback f).obj Ω
  let M' := (pullback f').obj Ω'
  let v : Fin n → (SheafOfModules.unit X.ringCatSheaf ⟶ Ω) :=
    fun k => canonicalDifferentialUnitSection α (b k)
  let v' : Fin n → (SheafOfModules.unit X'.ringCatSheaf ⟶ Ω') :=
    fun k => restrictedUnitSection j (v k) ≫ eA.hom
  let w := wedgeUnitSection Y M n (fun k => pulledUnitSection f (v k))
  let wA := wedgeUnitSection X Ω n v
  let wA' := wedgeUnitSection X' Ω' n v'
  let a := affineConormalAmbientMiddleTopFrame α s n b
  have hw : w ≫ a.hom = 𝟙 _ := by
    simpa only [w, v, a, Module.Basis.det_self, map_one, unitMul_one] using
      pulledWedgeUnitSection_frame α s n b b
  have hwIso : w = a.inv := by
    apply (cancel_mono a.hom).mp
    rw [hw, Iso.inv_hom_id]
  let : IsIso w := by rw [hwIso]; infer_instance
  let : IsIso (restrictedUnitSection p w) := by
    dsimp only [restrictedUnitSection]
    infer_instance
  apply (cancel_epi (restrictedUnitSection p w)).mp
  have hS {N : X.Modules} (u : SheafOfModules.unit X.ringCatSheaf ⟶ N) :
      restrictedUnitSection p (pulledUnitSection f u) ≫ S.hom.app N =
        pulledUnitSection f' (restrictedUnitSection j u) :=
    canonicalOpenPullbackSquare_section p f' f j H u
  have hC : w ≫ (affineConormalAmbientCoefficientIso α s n b).hom =
      pulledUnitSection f wA := coefficient_wedge_sections α s n b v
  have hT : restrictedUnitSection j wA ≫ eT.hom = wA' :=
    wedgeUnitSection_topRestriction j eA n v
  have hM (k : Fin n) : restrictedUnitSection p (pulledUnitSection f (v k)) ≫ eM.hom =
      pulledUnitSection f' (v' k) := by
    change restrictedUnitSection p (pulledUnitSection f (v k)) ≫
      S.hom.app Ω ≫ (pullback f').map eA.hom = _
    rw [← Category.assoc, hS, pulledUnitSection_comp]
  have hMT : restrictedUnitSection p w ≫ eMT.hom =
      wedgeUnitSection Y' M' n (fun k => pulledUnitSection f' (v' k)) := by
    have ht := wedgeUnitSection_topRestriction p eM n (fun k => pulledUnitSection f (v k))
    change restrictedUnitSection p w ≫ eMT.hom =
      wedgeUnitSection Y' M' n
        (fun k => restrictedUnitSection p (pulledUnitSection f (v k)) ≫ eM.hom) at ht
    exact ht.trans (congrArg (wedgeUnitSection Y' M' n) (funext hM))
  have hleft : restrictedUnitSection p w ≫
      (restrictFunctor p).map (affineConormalAmbientCoefficientIso α s n b).hom ≫ eC.hom =
      pulledUnitSection f' wA' := by
    calc
      _ = restrictedUnitSection p (w ≫ (affineConormalAmbientCoefficientIso α s n b).hom) ≫
          eC.hom := by
        simp only [restrictedUnitSection, Functor.map_comp, Category.assoc]
      _ = restrictedUnitSection p (pulledUnitSection f wA) ≫
          S.hom.app (moduleExteriorPower X Ω n) ≫ (pullback f').map eT.hom := by
        rw [hC]
        rfl
      _ = pulledUnitSection f' (restrictedUnitSection j wA) ≫ (pullback f').map eT.hom := by
        rw [← Category.assoc, hS]
      _ = _ := by rw [pulledUnitSection_comp, hT]
  have hright : restrictedUnitSection p w ≫ eMT.hom ≫
      (affineConormalAmbientCoefficientIso α' t n b').hom = pulledUnitSection f' wA' := by
    rw [← Category.assoc, hMT]
    exact coefficient_wedge_sections α' t n b' v'
  exact hleft.trans hright.symm

end AlgebraicGeometry.Scheme.Modules
