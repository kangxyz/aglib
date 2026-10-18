/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Aglib.AlgebraicGeometry.Modules.Differentials.Relative.Conormal.Determinant.Affine
public import Aglib.AlgebraicGeometry.Modules.ExteriorPower.OpenRestriction
public import Mathlib.RingTheory.Regular.Flat
public import Mathlib.LinearAlgebra.TensorProduct.Basis
/-!
# Principal localization of the conormal determinant

The normal-first conormal determinant acts on arbitrary sections by concatenating
normal vectors and tangent lifts. Its whole morphism commutes with principal
localization of the same ordered regular list, using the original conormal
localization maps, exterior restriction comparisons and tensor restriction.
The localized determinant retains the explicit list-length transport.
-/

@[expose] public section
noncomputable section
open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Scheme.Hom AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Modules.Differentials
open scoped TensorProduct
universe u
namespace AlgebraicGeometry.Scheme.Modules.Differentials
variable {R A B : CommRingCat.{u}} (α : R ⟶ A) (σ : A ⟶ B) (hσ : Function.Surjective σ)
  (s : List A) (hs : RingTheory.Sequence.IsWeaklyRegular A s)
  (hker : Ideal.ofList s = RingHom.ker σ.hom)
  (hA : α.hom.FormallySmooth) (hB : (α ≫ σ).hom.FormallySmooth) {n : ℕ}
  (bQ : Module.Basis (Fin n) B (CommRingCat.KaehlerDifferential (α ≫ σ)))

local notation "C" => relativeConormalAffineModule α σ hσ
local notation "Q" => CommRingCat.KaehlerDifferential (α ≫ σ)

include hσ hs hker hA hB bQ

private def middleBasis : Module.Basis (Fin s.length ⊕ Fin n) B
    ((ModuleCat.extendScalars σ.hom).obj (CommRingCat.KaehlerDifferential α)) := by
  let := σ.hom.toAlgebra
  exact Classical.choose (relativeConormalAffineNormalFirstFrame α σ hσ s hs hker hA hB bQ)

private def orderedMiddleBasis : Module.Basis (Fin (s.length + n)) B
    ((ModuleCat.extendScalars σ.hom).obj (CommRingCat.KaehlerDifferential α)) :=
  (middleBasis α σ hσ s hs hker hA hB bQ).reindex (finSumFinEquiv)

private def quotientFreeIso :
    (relativeConormalAffineComplex α σ hσ).X₃ ≅
      SheafOfModules.free (R := (Spec B).ringCatSheaf) (ULift.{u} (Fin n)) :=
  relativeDifferentialAffineIso (α ≫ σ) ≪≫
    tildeBasisIso (CommRingCat.KaehlerDifferential (α ≫ σ)) (bQ.reindex Equiv.ulift.symm)

private def middleFreeIso :
    (relativeConormalAffineComplex α σ hσ).X₂ ≅
      SheafOfModules.free (R := (Spec B).ringCatSheaf) (ULift.{u} (Fin (s.length + n))) :=
  relativeConormalAffineMiddleIso α σ ≪≫
    tildeBasisIso ((ModuleCat.extendScalars σ.hom).obj (CommRingCat.KaehlerDifferential α))
      ((orderedMiddleBasis α σ hσ s hs hker hA hB bQ).reindex Equiv.ulift.symm)

omit hσ hs hker hA hB bQ in
private def actualTopFrame {X : Scheme.{u}} (M : X.Modules) (d : ℕ)
    (e : M ≅ SheafOfModules.free (R := X.ringCatSheaf) (ULift.{u} (Fin d))) :
    moduleExteriorPower X M d ≅ SheafOfModules.unit X.ringCatSheaf :=
  (moduleExteriorPowerFunctor X d).mapIso e ≪≫
    SheafOfModulesOfCommRing.exteriorTopFreeIso X.sheaf d

omit hσ hs hker hA hB bQ in
private abbrev nativeFreeModule (X : Scheme.{u}) (U : X.Opens) (d : ℕ) :
    Module (X.sheaf.obj.obj (Opposite.op U))
      ((SheafOfModules.free (R := X.ringCatSheaf) (ULift.{u} (Fin d))).val.obj
        (Opposite.op U)) := by
  change Module (X.ringCatSheaf.obj.obj (Opposite.op U))
    ((SheafOfModules.free (R := X.ringCatSheaf) (ULift.{u} (Fin d))).val.obj
      (Opposite.op U))
  infer_instance

omit hσ hs hker hA hB bQ in
private theorem actualTopFrame_mk {X : Scheme.{u}} (M : X.Modules) (d : ℕ)
    (e : M ≅ SheafOfModules.free (R := X.ringCatSheaf) (ULift.{u} (Fin d)))
    (U : X.Opens) (v : Fin d → M.val.obj (Opposite.op U)) :
    letI := nativeFreeModule X U d
    (actualTopFrame M d e).hom.val.app (Opposite.op U)
      ((SheafOfModulesOfCommRing.exteriorPowerMk X.sheaf M d).app (Opposite.op U) v) =
      (SheafOfModulesOfCommRing.freeFinSectionsBasis X.sheaf d (Opposite.op U)).det.toFun
        (fun i => e.hom.val.app (Opposite.op U) (v i)) := by
  let := nativeFreeModule X U d
  change (SheafOfModulesOfCommRing.exteriorTopFreeHom X.sheaf d).val.app (Opposite.op U)
    (((moduleExteriorPowerFunctor X d).map e.hom).val.app (Opposite.op U)
      ((SheafOfModulesOfCommRing.exteriorPowerMk X.sheaf M d).app (Opposite.op U) v)) = _
  exact (congrArg
    ((SheafOfModulesOfCommRing.exteriorTopFreeHom X.sheaf d).val.app (Opposite.op U))
    (SheafOfModulesOfCommRing.exteriorPowerFunctor_map_mk X.sheaf e.hom d
      (Opposite.op U) v)).trans
      (SheafOfModulesOfCommRing.exteriorTopFreeHom_mk X.sheaf d (Opposite.op U)
        (fun i => e.hom.val.app (Opposite.op U) (v i)))

omit hσ hs hker hA hB bQ in
private def affineFreeIso {D : CommRingCat.{u}} (N : (Spec D).Modules) (E : ModuleCat.{u} D)
    (d : ℕ) (b : Module.Basis (Fin d) D E) (e : N ≅ tilde E) :
    N ≅ SheafOfModules.free (R := (Spec D).ringCatSheaf) (ULift.{u} (Fin d)) :=
  e ≪≫ tildeBasisIso E (b.reindex Equiv.ulift.symm)

omit hσ hs hker hA hB bQ in
private def actualLineTensorIso {X : Scheme.{u}} {L N P : X.Modules}
    (eL : L ≅ SheafOfModules.unit X.ringCatSheaf)
    (eN : N ≅ SheafOfModules.unit X.ringCatSheaf)
    (eP : P ≅ SheafOfModules.unit X.ringCatSheaf) :
    (moduleTensorLeftFunctor X L).obj N ≅ P :=
  ((SheafOfModulesOfCommRing.tensorFunctor X.sheaf).mapIso eL).app N ≪≫
    (SheafOfModulesOfCommRing.tensorLeftUnitIso X.sheaf).app N ≪≫ eN ≪≫ eP.symm

omit hσ hs hker hA hB bQ in
private theorem actualLineTensorIso_coordinates {X : Scheme.{u}} {L N P : X.Modules}
    (eL : L ≅ SheafOfModules.unit X.ringCatSheaf)
    (eN : N ≅ SheafOfModules.unit X.ringCatSheaf)
    (eP : P ≅ SheafOfModules.unit X.ringCatSheaf)
    (U : X.Opens) (a : L.val.obj (Opposite.op U)) (b : N.val.obj (Opposite.op U)) :
    eP.hom.val.app (Opposite.op U)
      ((actualLineTensorIso eL eN eP).hom.val.app (Opposite.op U)
        (moduleTensorSection X L N U a b)) =
      (show Γ(X, U) from eL.hom.val.app (Opposite.op U) a) *
        (show Γ(X, U) from eN.hom.val.app (Opposite.op U) b) := by
  have hunit := tensorToUnit_section eL.hom N U a b
  have hP := congrArg (fun k => k.val.app (Opposite.op U)
    (eN.hom.val.app (Opposite.op U)
      (((tensorToUnit eL.hom).app N).val.app (Opposite.op U)
        (moduleTensorSection X L N U a b)))) eP.inv_hom_id
  change eP.hom.val.app (Opposite.op U)
    (eP.inv.val.app (Opposite.op U)
      (eN.hom.val.app (Opposite.op U)
        (((tensorToUnit eL.hom).app N).val.app (Opposite.op U)
          (moduleTensorSection X L N U a b)))) = _
  exact hP.trans ((congrArg (eN.hom.val.app (Opposite.op U)) hunit).trans
    ((eN.hom.val.app (Opposite.op U)).hom.map_smul
      (show Γ(X, U) from eL.hom.val.app (Opposite.op U) a) b))

variable {D : CommRingCat.{u}}

omit hσ hs hker hA hB bQ in
private def affineCoefficientMap (U : (Spec D).Opens) :
    D →+* (Spec D).sheaf.obj.obj (Opposite.op U) := by
  change D →+* Γ(Spec D, U)
  exact ((Scheme.ΓSpecIso D).inv ≫ (Spec D).presheaf.map U.leTop.op).hom

omit hσ hs hker hA hB bQ in
private def affineFrameSemilinear (E : ModuleCat.{u} D) (d : ℕ) (b : Module.Basis (Fin d) D E)
    (U : (Spec D).Opens) :
    letI := nativeFreeModule (Spec D) U d
    E →ₛₗ[affineCoefficientMap U]
      ((SheafOfModules.free (R := (Spec D).ringCatSheaf) (ULift.{u} (Fin d))).val.obj
        (Opposite.op U)) := by
  letI := nativeFreeModule (Spec D) U d
  let F := SheafOfModules.free (R := (Spec D).ringCatSheaf) (ULift.{u} (Fin d))
  let φ := affineCoefficientMap U
  let N := ModuleCat.of ((Spec D).sheaf.obj.obj (Opposite.op U)) (F.val.obj (Opposite.op U))
  let e := tildeBasisIso E (b.reindex Equiv.ulift.symm)
  have g : E ⟶ (ModuleCat.restrictScalars φ).obj N := by
    change E ⟶ (modulesSpecToSheaf.obj F).presheaf.obj (Opposite.op U)
    exact tilde.toOpen E U ≫ (modulesSpecToSheaf.map e.hom).hom.app (Opposite.op U)
  exact (ModuleCat.semilinearMapAddEquiv φ E N).symm g

omit hσ hs hker hA hB bQ in
private theorem affineFrameSemilinear_basis (E : ModuleCat.{u} D) (d : ℕ)
    (b : Module.Basis (Fin d) D E) (U : (Spec D).Opens) (i : Fin d) :
    letI := nativeFreeModule (Spec D) U d
    affineFrameSemilinear E d b U (b i) =
      (SheafOfModules.freeSection (R := (Spec D).ringCatSheaf) (ULift.up i)).val
        (Opposite.op U) := by
  let := nativeFreeModule (Spec D) U d
  change (tildeBasisIso E (b.reindex Equiv.ulift.symm)).hom.val.app (Opposite.op U)
    (tilde.toOpen E U (b i)) = _
  simpa only [Module.Basis.reindex_apply, Equiv.symm_symm, Equiv.ulift_apply, ULift.down_up]
    using tildeBasisIso_hom_toOpen E (b.reindex Equiv.ulift.symm) (ULift.up i) U

omit hσ hs hker hA hB bQ in
private theorem semilinearDeterminant {K L M N : Type*} [CommRing K] [CommRing L]
    [AddCommGroup M] [Module K M] [AddCommGroup N] [Module L N] {d : ℕ}
    (b : Module.Basis (Fin d) K M) (c : Module.Basis (Fin d) L N)
    {φ : K →+* L} (f : M →ₛₗ[φ] N) (hf : ∀ i, f (b i) = c i) (v : Fin d → M) :
    c.det (f ∘ v) = φ (b.det v) := by
  have H := Module.Basis.exteriorPowerTopEquiv_mapSemilinear b c f (exteriorPower.ιMulti K d v)
  have hfc : f ∘ b = c := funext hf
  rw [exteriorPower.mapSemilinear_apply_ιMulti, Module.Basis.exteriorPowerTopEquiv_ιMulti,
    Module.Basis.exteriorPowerTopEquiv_ιMulti, hfc, c.det_self, one_mul] at H
  exact H

omit hσ hs hker hA hB bQ in
private theorem affineFrameSemilinear_det (E : ModuleCat.{u} D) (d : ℕ)
    (b : Module.Basis (Fin d) D E) (U : (Spec D).Opens) (v : Fin d → E) :
    letI := nativeFreeModule (Spec D) U d
    (SheafOfModulesOfCommRing.freeFinSectionsBasis (Spec D).sheaf d (Opposite.op U)).det.toFun
      (fun i => affineFrameSemilinear E d b U (v i)) = affineCoefficientMap U (b.det v) := by
  let := nativeFreeModule (Spec D) U d
  let f := affineFrameSemilinear E d b U
  let c := SheafOfModulesOfCommRing.freeFinSectionsBasis (Spec D).sheaf d (Opposite.op U)
  have hf (i : Fin d) : f (b i) = c.repr.symm.toFun (Finsupp.single i 1) :=
    (affineFrameSemilinear_basis E d b U i).trans
      (SheafOfModulesOfCommRing.freeFinSectionsBasis_apply (Spec D).sheaf d (Opposite.op U) i).symm
  exact semilinearDeterminant b c f hf v


omit hσ hs hker hA hB bQ in
omit hσ hs hker hA hB bQ in
private theorem affineTopFrame_nativeWedge {D : CommRingCat.{u}} (N : (Spec D).Modules)
    (E : ModuleCat.{u} D) (d : ℕ) (b : Module.Basis (Fin d) D E) (e : N ≅ tilde E)
    (U : (Spec D).Opens) (v : Fin d → E) :
    (actualTopFrame N d (affineFreeIso N E d b e)).hom.val.app (Opposite.op U)
      ((SheafOfModulesOfCommRing.exteriorPowerMk (Spec D).sheaf N d).app (Opposite.op U)
        (fun i => e.inv.val.app (Opposite.op U) (tilde.toOpen E U (v i)))) =
      algebraMap D Γ(Spec D, U) (b.det v) := by
  let := nativeFreeModule (Spec D) U d
  let f := affineFrameSemilinear E d b U
  let bF := SheafOfModulesOfCommRing.freeFinSectionsBasis (Spec D).sheaf d (Opposite.op U)
  rw [actualTopFrame_mk]
  have hfamily :
      (fun i => (affineFreeIso N E d b e).hom.val.app (Opposite.op U)
        (e.inv.val.app (Opposite.op U) (tilde.toOpen E U (v i)))) = f ∘ v := by
    funext i
    have h := congrArg (fun k => k.val.app (Opposite.op U) (tilde.toOpen E U (v i)))
      e.inv_hom_id
    exact congrArg
      ((tildeBasisIso E (b.reindex Equiv.ulift.symm)).hom.val.app (Opposite.op U)) h
  exact (congrArg bF.det.toFun hfamily).trans (affineFrameSemilinear_det E d b U v)

omit hσ hs hker hA hB bQ in
private def affineNativeWedge {D : CommRingCat.{u}} (N : (Spec D).Modules) (E : ModuleCat.{u} D)
    (d : ℕ) (e : N ≅ tilde E) (U : (Spec D).Opens) (v : Fin d → E) :
    (moduleExteriorPower (Spec D) N d).val.obj (Opposite.op U) :=
  (SheafOfModulesOfCommRing.exteriorPowerMk (Spec D).sheaf N d).app (Opposite.op U)
    (fun i => e.inv.val.app (Opposite.op U) (tilde.toOpen E U (v i)))

omit hσ hs hker hA hB bQ in
private theorem isoSectionsHom_injective {X : Scheme.{u}} {L N : X.Modules} (e : L ≅ N)
    (U : X.Opens) : Function.Injective (e.hom.val.app (Opposite.op U)) := by
  intro x y h
  have hx := congrArg (fun k => k.val.app (Opposite.op U) x) e.hom_inv_id
  have hy := congrArg (fun k => k.val.app (Opposite.op U) y) e.hom_inv_id
  exact hx.symm.trans ((congrArg (e.inv.val.app (Opposite.op U)) h).trans hy)

omit hσ hs hker hA hB bQ in
private theorem hom_ext_of_unitFrame {X : Scheme.{u}} {L P : X.Modules}
    (e : L ≅ SheafOfModules.unit X.ringCatSheaf)
    (v : ∀ U : X.Opens, L.val.obj (Opposite.op U))
    (hv : ∀ U : X.Opens, e.hom.val.app (Opposite.op U) (v U) = (1 : Γ(X, U)))
    (f g : L ⟶ P)
    (hfg : ∀ U : X.Opens,
      f.val.app (Opposite.op U) (v U) = g.val.app (Opposite.op U) (v U)) : f = g := by
  suffices h : e.inv ≫ f = e.inv ≫ g by
    have hh := congrArg (fun k => e.hom ≫ k) h
    exact (e.hom_inv_id_assoc f).symm.trans (hh.trans (e.hom_inv_id_assoc g))
  apply (SheafOfModules.unitHomEquiv P).injective
  apply PresheafOfModules.sections_ext
  intro U
  have hi := congrArg (fun k => k.val.app U (1 : X.ringCatSheaf.obj.obj U)) e.inv_hom_id
  have hpoint : e.inv.val.app U (1 : X.ringCatSheaf.obj.obj U) = v U.unop :=
    isoSectionsHom_injective e U.unop (hi.trans (hv U.unop).symm)
  change f.val.app U (e.inv.val.app U (1 : X.ringCatSheaf.obj.obj U)) =
    g.val.app U (e.inv.val.app U (1 : X.ringCatSheaf.obj.obj U))
  rw [hpoint]
  exact hfg U.unop

private def frameDeterminantIso :
    tensorSheaf (Spec B)
      (moduleExteriorPower (Spec B)
        ((pullback (Spec.map σ)).obj (idealModule (Spec.map σ))) s.length)
      (moduleExteriorPower (Spec B) (relativeConormalAffineComplex α σ hσ).X₃ n) ≅
    moduleExteriorPower (Spec B) (relativeConormalAffineComplex α σ hσ).X₂ (s.length + n) := by
  let Qtop := moduleExteriorPower (Spec B) (relativeConormalAffineComplex α σ hσ).X₃ n
  let eC := actualTopFrame _ s.length
    (relativeConormalAffineGeometricFreeIso α σ hσ s hs hker)
  let eQ := actualTopFrame _ n
    (quotientFreeIso α σ hσ bQ)
  let eM := actualTopFrame _ (s.length + n) (middleFreeIso α σ hσ s hs hker hA hB bQ)
  exact ((SheafOfModulesOfCommRing.tensorFunctor (Spec B).sheaf).mapIso eC).app Qtop ≪≫
    (SheafOfModulesOfCommRing.tensorLeftUnitIso (Spec B).sheaf).app Qtop ≪≫ eQ ≪≫ eM.symm

omit hσ hs hker hA hB bQ in
private theorem sectionBlockDet {K C₀ Q₀ M₀ : Type*} [CommRing K]
    [AddCommGroup C₀] [Module K C₀] [AddCommGroup Q₀] [Module K Q₀]
    [AddCommGroup M₀] [Module K M₀] {c d : ℕ}
    (bC : Module.Basis (Fin c) K C₀) (bQ : Module.Basis (Fin d) K Q₀)
    (bM : Module.Basis (Fin c ⊕ Fin d) K M₀) (F : C₀ →ₗ[K] M₀) (G : M₀ →ₗ[K] Q₀)
    (hF : ∀ i, F (bC i) = bM (Sum.inl i))
    (hG₁ : ∀ i, G (bM (Sum.inl i)) = 0)
    (hG₂ : ∀ j, G (bM (Sum.inr j)) = bQ j) (v : Fin c → C₀) (w : Fin d → M₀) :
    bM.det (Sum.elim (fun i => F (v i)) w) = bC.det v * bQ.det (fun j => G (w j)) := by
  classical
  have hFC (i : Fin c) : (bM.coord (Sum.inl i)).comp F = bC.coord i := by
    apply bC.ext
    intro j
    simp [Module.Basis.coord_apply, hF, Finsupp.single_apply]
  have hFN (i : Fin d) : (bM.coord (Sum.inr i)).comp F = 0 := by
    apply bC.ext
    intro j
    simp [Module.Basis.coord_apply, hF]
  have hG (i : Fin d) : (bQ.coord i).comp G = bM.coord (Sum.inr i) := by
    apply bM.ext
    intro j
    cases j with
    | inl j => simp [Module.Basis.coord_apply, hG₁]
    | inr j => simp [Module.Basis.coord_apply, hG₂, Finsupp.single_apply]
  let T : Matrix (Fin c) (Fin d) K := fun i j => bM.repr (w j) (Sum.inl i)
  have hmat : bM.toMatrix (Sum.elim (fun i => F (v i)) w) =
      Matrix.fromBlocks (bC.toMatrix v) T 0 (bQ.toMatrix (fun j => G (w j))) := by
    ext i j
    cases i with
    | inl i => cases j with
      | inl j => exact LinearMap.congr_fun (hFC i) (v j)
      | inr j => rfl
    | inr i => cases j with
      | inl j => exact LinearMap.congr_fun (hFN i) (v j)
      | inr j => exact (LinearMap.congr_fun (hG i) (w j)).symm
  rw [Module.Basis.det_apply, hmat, Matrix.det_fromBlocks_zero₂₁,
    ← Module.Basis.det_apply, ← Module.Basis.det_apply]

omit hσ hs hker hA hB bQ in
private theorem sectionBlockDetFin {K C₀ Q₀ M₀ : Type*} [CommRing K]
    [AddCommGroup C₀] [Module K C₀] [AddCommGroup Q₀] [Module K Q₀]
    [AddCommGroup M₀] [Module K M₀] {c d : ℕ}
    (bC : Module.Basis (Fin c) K C₀) (bQ : Module.Basis (Fin d) K Q₀)
    (bM : Module.Basis (Fin (c + d)) K M₀) (F : C₀ →ₗ[K] M₀) (G : M₀ →ₗ[K] Q₀)
    (hF : ∀ i, F (bC i) = bM (finSumFinEquiv (Sum.inl i)))
    (hG₁ : ∀ i, G (bM (finSumFinEquiv (Sum.inl i))) = 0)
    (hG₂ : ∀ j, G (bM (finSumFinEquiv (Sum.inr j))) = bQ j)
    (v : Fin c → C₀) (w : Fin d → M₀) :
    bM.det (Fin.append (fun i => F (v i)) w) = bC.det v * bQ.det (fun j => G (w j)) := by
  classical
  let bMSum := bM.reindex finSumFinEquiv.symm
  have hF' (i : Fin c) : F (bC i) = bMSum (Sum.inl i) := by
    simpa only [bMSum, Module.Basis.reindex_apply, Equiv.symm_symm] using hF i
  have hG₁' (i : Fin c) : G (bMSum (Sum.inl i)) = 0 := by
    simpa only [bMSum, Module.Basis.reindex_apply, Equiv.symm_symm] using hG₁ i
  have hG₂' (j : Fin d) : G (bMSum (Sum.inr j)) = bQ j := by
    simpa only [bMSum, Module.Basis.reindex_apply, Equiv.symm_symm] using hG₂ j
  have H := sectionBlockDet bC bQ bMSum F G hF' hG₁' hG₂' v w
  have hf : Fin.append (fun i => F (v i)) w ∘ finSumFinEquiv =
      Sum.elim (fun i => F (v i)) w := by
    funext i
    cases i with
    | inl i =>
      simpa only [Function.comp_apply, finSumFinEquiv_apply_left, Sum.elim_inl] using
        Fin.append_left (fun i => F (v i)) w i
    | inr j =>
      simpa only [Function.comp_apply, finSumFinEquiv_apply_right, Sum.elim_inr] using
        Fin.append_right (fun i => F (v i)) w j
  exact (Module.Basis.det_reindex_symm bM (Fin.append (fun i => F (v i)) w)
    finSumFinEquiv).symm.trans ((congrArg bMSum.det hf).trans H)

omit hσ hs hker hA hB bQ in
private theorem frameCancelLeft {C₀ : Type*} [Category C₀] {W E T P G : C₀}
    (a : W ⟶ E) (e : E ≅ T) (f : E ⟶ P) (g : P ⟶ G) :
    (a ≫ e.hom) ≫ (e.inv ≫ f ≫ g) = a ≫ f ≫ g := by
  simp only [Category.assoc, Iso.hom_inv_id_assoc]

omit hσ hs hker hA hB bQ in
private theorem frameCancelRight {C₀ : Type*} [Category C₀] {W E T P G : C₀}
    (a : W ⟶ E) (f : E ⟶ P) (e : T ≅ P) (g : P ⟶ G) :
    (a ≫ f ≫ e.inv) ≫ (e.hom ≫ g) = a ≫ f ≫ g := by
  simp only [Category.assoc, Iso.inv_hom_id_assoc]

omit hσ hs hker hA hB bQ in
private theorem frameCancelRightAssoc {C₀ : Type*} [Category C₀] {W E T P G : C₀}
    (a : W ⟶ E) (f : E ⟶ P) (e : T ≅ P) (g : P ⟶ G) :
    a ≫ (f ≫ e.inv) ≫ (e.hom ≫ g) = a ≫ f ≫ g := by
  simp only [Category.assoc, Iso.inv_hom_id_assoc]

omit hσ hs hker hA hB bQ in
private def coefficientFreeHom {D : CommRingCat.{u}} {E T : ModuleCat.{u} D}
    {c d : ℕ} (bE : Module.Basis (Fin c) D E) (bT : Module.Basis (Fin d) D T) (f : E ⟶ T) :
    SheafOfModules.free (R := (Spec D).ringCatSheaf) (ULift.{u} (Fin c)) ⟶
      SheafOfModules.free (R := (Spec D).ringCatSheaf) (ULift.{u} (Fin d)) :=
  (tildeBasisIso E (bE.reindex Equiv.ulift.symm)).inv ≫ tilde.map f ≫
    (tildeBasisIso T (bT.reindex Equiv.ulift.symm)).hom

omit hσ hs hker hA hB bQ in
private theorem coefficientFreeHom_basis {D : CommRingCat.{u}} {E T : ModuleCat.{u} D}
    {c d : ℕ} (bE : Module.Basis (Fin c) D E) (bT : Module.Basis (Fin d) D T) (f : E ⟶ T)
    (U : (Spec D).Opens) (i : Fin c) :
    letI := nativeFreeModule (Spec D) U d
    (coefficientFreeHom bE bT f).val.app (Opposite.op U)
      ((SheafOfModules.freeSection (R := (Spec D).ringCatSheaf) (ULift.up i)).val
        (Opposite.op U)) = affineFrameSemilinear T d bT U (f (bE i)) := by
  let := nativeFreeModule (Spec D) U d
  let eE := tildeBasisIso E (bE.reindex Equiv.ulift.symm)
  let eT := tildeBasisIso T (bT.reindex Equiv.ulift.symm)
  have he := affineFrameSemilinear_basis E c bE U i
  change eE.hom.val.app (Opposite.op U) (tilde.toOpen E U (bE i)) = _ at he
  have hi : eE.inv.val.app (Opposite.op U)
      ((SheafOfModules.freeSection (R := (Spec D).ringCatSheaf) (ULift.up i)).val
        (Opposite.op U)) = tilde.toOpen E U (bE i) :=
    (congrArg (eE.inv.val.app (Opposite.op U)) he.symm).trans
      (congrArg (fun k => k.val.app (Opposite.op U) (tilde.toOpen E U (bE i))) eE.hom_inv_id)
  have hf := ConcreteCategory.congr_hom (tilde.toOpen_map_app f U) (bE i)
  change (tilde.map f).val.app (Opposite.op U) (tilde.toOpen E U (bE i)) =
    tilde.toOpen T U (f (bE i)) at hf
  change eT.hom.val.app (Opposite.op U)
    ((tilde.map f).val.app (Opposite.op U) (eE.inv.val.app (Opposite.op U) _)) = _
  exact (congrArg (fun x => eT.hom.val.app (Opposite.op U)
    ((tilde.map f).val.app (Opposite.op U) x)) hi).trans
      (congrArg (eT.hom.val.app (Opposite.op U)) hf)


private theorem middleBasis_F (i : Fin s.length) :
    relativeConormalAffineLinearF α σ hσ (relativeConormalAffineBasis α σ hσ s hs hker i) =
      orderedMiddleBasis α σ hσ s hs hker hA hB bQ (finSumFinEquiv (Sum.inl i)) := by
  let := σ.hom.toAlgebra
  rw [relativeConormalAffineBasis_apply, relativeConormalAffineLinearF_class]
  rw [orderedMiddleBasis, Module.Basis.reindex_apply, Equiv.symm_apply_apply]
  change (1 : B) ⊗ₜ[A] CommRingCat.KaehlerDifferential.d (f := α) (s.get i) =
    (middleBasis α σ hσ s hs hker hA hB bQ) (Sum.inl i)
  exact ((Classical.choose_spec
    (relativeConormalAffineNormalFirstFrame α σ hσ s hs hker hA hB bQ)).1 i).symm

private theorem middleBasis_G₁ (i : Fin s.length) :
    relativeConormalAffineLinearG α σ hσ
      (orderedMiddleBasis α σ hσ s hs hker hA hB bQ (finSumFinEquiv (Sum.inl i))) = 0 := by
  rw [← middleBasis_F α σ hσ s hs hker hA hB bQ i]
  exact ConcreteCategory.congr_hom (relativeConormalAffineLinearComplex α σ hσ).zero
    (relativeConormalAffineBasis α σ hσ s hs hker i)

private theorem middleBasis_G₂ (j : Fin n) :
    relativeConormalAffineLinearG α σ hσ
      (orderedMiddleBasis α σ hσ s hs hker hA hB bQ (finSumFinEquiv (Sum.inr j))) = bQ j := by
  let := σ.hom.toAlgebra
  rw [orderedMiddleBasis, Module.Basis.reindex_apply, Equiv.symm_apply_apply]
  change relativeConormalAffineLinearG α σ hσ
    (middleBasis α σ hσ s hs hker hA hB bQ (Sum.inr j)) = bQ j
  exact (Classical.choose_spec
    (relativeConormalAffineNormalFirstFrame α σ hσ s hs hker hA hB bQ)).2.1 j

private def sectionFreeF := coefficientFreeHom
  (relativeConormalAffineBasis α σ hσ s hs hker)
  (orderedMiddleBasis α σ hσ s hs hker hA hB bQ) (relativeConormalAffineLinearF α σ hσ)

private def sectionFreeG := coefficientFreeHom
  (orderedMiddleBasis α σ hσ s hs hker hA hB bQ) bQ (relativeConormalAffineLinearG α σ hσ)

private theorem sectionFreeF_basis (U : (Spec B).Opens) (i : Fin s.length) :
    (sectionFreeF α σ hσ s hs hker hA hB bQ).val.app (Opposite.op U)
      ((SheafOfModules.freeSection (R := (Spec B).ringCatSheaf) (ULift.up i)).val
        (Opposite.op U)) =
    (SheafOfModules.freeSection (R := (Spec B).ringCatSheaf)
      (ULift.up (finSumFinEquiv (Sum.inl i)))).val (Opposite.op U) := by
  let := nativeFreeModule (Spec B) U (s.length + n)
  have h := coefficientFreeHom_basis
    (relativeConormalAffineBasis α σ hσ s hs hker)
    (orderedMiddleBasis α σ hσ s hs hker hA hB bQ)
    (relativeConormalAffineLinearF α σ hσ) U i
  exact h.trans ((congrArg
    (affineFrameSemilinear ((ModuleCat.extendScalars σ.hom).obj
      (CommRingCat.KaehlerDifferential α)) (s.length + n)
      (orderedMiddleBasis α σ hσ s hs hker hA hB bQ) U)
    (middleBasis_F α σ hσ s hs hker hA hB bQ i)).trans
      (affineFrameSemilinear_basis _ _ _ U (finSumFinEquiv (Sum.inl i))))

private theorem sectionFreeG_basis₁ (U : (Spec B).Opens) (i : Fin s.length) :
    (sectionFreeG α σ hσ s hs hker hA hB bQ).val.app (Opposite.op U)
      ((SheafOfModules.freeSection (R := (Spec B).ringCatSheaf)
        (ULift.up (finSumFinEquiv (Sum.inl i)))).val (Opposite.op U)) = 0 := by
  let := nativeFreeModule (Spec B) U n
  have h := coefficientFreeHom_basis (orderedMiddleBasis α σ hσ s hs hker hA hB bQ)
    bQ (relativeConormalAffineLinearG α σ hσ) U (finSumFinEquiv (Sum.inl i))
  exact h.trans ((congrArg (affineFrameSemilinear Q n bQ U)
    (middleBasis_G₁ α σ hσ s hs hker hA hB bQ i)).trans
      (affineFrameSemilinear Q n bQ U).map_zero)

private theorem sectionFreeG_basis₂ (U : (Spec B).Opens) (j : Fin n) :
    (sectionFreeG α σ hσ s hs hker hA hB bQ).val.app (Opposite.op U)
      ((SheafOfModules.freeSection (R := (Spec B).ringCatSheaf)
        (ULift.up (finSumFinEquiv (Sum.inr j)))).val (Opposite.op U)) =
    (SheafOfModules.freeSection (R := (Spec B).ringCatSheaf) (ULift.up j)).val
      (Opposite.op U) := by
  let := nativeFreeModule (Spec B) U n
  have h := coefficientFreeHom_basis (orderedMiddleBasis α σ hσ s hs hker hA hB bQ)
    bQ (relativeConormalAffineLinearG α σ hσ) U (finSumFinEquiv (Sum.inr j))
  exact h.trans ((congrArg (affineFrameSemilinear Q n bQ U)
    (middleBasis_G₂ α σ hσ s hs hker hA hB bQ j)).trans
      (affineFrameSemilinear_basis Q n bQ U j))

omit hσ hs hker hA hB bQ in
private abbrev freePointLinear {X : Scheme.{u}} {c d : ℕ}
    (f : SheafOfModules.free (R := X.ringCatSheaf) (ULift.{u} (Fin c)) ⟶
      SheafOfModules.free (R := X.ringCatSheaf) (ULift.{u} (Fin d))) (U : X.Opens) :
    letI := nativeFreeModule X U c
    letI := nativeFreeModule X U d
    (SheafOfModules.free (R := X.ringCatSheaf) (ULift.{u} (Fin c))).val.obj (Opposite.op U) →ₗ[
      X.sheaf.obj.obj (Opposite.op U)]
      (SheafOfModules.free (R := X.ringCatSheaf) (ULift.{u} (Fin d))).val.obj (Opposite.op U) := by
  letI := nativeFreeModule X U c
  letI := nativeFreeModule X U d
  change _ →ₗ[X.ringCatSheaf.obj.obj (Opposite.op U)] _
  exact (f.val.app (Opposite.op U)).hom

private theorem sectionFreeF_naturality :
    (relativeConormalAffineGeometricFreeIso α σ hσ s hs hker).hom ≫
        sectionFreeF α σ hσ s hs hker hA hB bQ =
      (relativeConormalAffineIdealPullbackIso α σ hσ).hom ≫
        (relativeConormalAffineComplex α σ hσ).f ≫
          (middleFreeIso α σ hσ s hs hker hA hB bQ).hom := by
  let eC := tildeBasisIso C
    ((relativeConormalAffineBasis α σ hσ s hs hker).reindex Equiv.ulift.symm)
  let eM := tildeBasisIso ((ModuleCat.extendScalars σ.hom).obj
    (CommRingCat.KaehlerDifferential α))
    ((orderedMiddleBasis α σ hσ s hs hker hA hB bQ).reindex Equiv.ulift.symm)
  change ((relativeConormalAffineIdealPullbackIso α σ hσ).hom ≫ eC.hom) ≫
      (eC.inv ≫ tilde.map (relativeConormalAffineLinearF α σ hσ) ≫ eM.hom) =
    (relativeConormalAffineIdealPullbackIso α σ hσ).hom ≫
      (tilde.map (relativeConormalAffineLinearF α σ hσ) ≫
        (relativeConormalAffineMiddleIso α σ).inv) ≫
          ((relativeConormalAffineMiddleIso α σ).hom ≫ eM.hom)
  exact (frameCancelLeft (relativeConormalAffineIdealPullbackIso α σ hσ).hom eC
    (tilde.map (relativeConormalAffineLinearF α σ hσ)) eM.hom).trans
      (frameCancelRightAssoc (relativeConormalAffineIdealPullbackIso α σ hσ).hom
        (tilde.map (relativeConormalAffineLinearF α σ hσ))
        (relativeConormalAffineMiddleIso α σ) eM.hom).symm

private theorem sectionFreeG_naturality :
    (middleFreeIso α σ hσ s hs hker hA hB bQ).hom ≫
        sectionFreeG α σ hσ s hs hker hA hB bQ =
      (relativeConormalAffineComplex α σ hσ).g ≫
        (quotientFreeIso α σ hσ bQ).hom := by
  let eM := tildeBasisIso ((ModuleCat.extendScalars σ.hom).obj
    (CommRingCat.KaehlerDifferential α))
    ((orderedMiddleBasis α σ hσ s hs hker hA hB bQ).reindex Equiv.ulift.symm)
  let eQ := tildeBasisIso Q (bQ.reindex Equiv.ulift.symm)
  change ((relativeConormalAffineMiddleIso α σ).hom ≫ eM.hom) ≫
      (eM.inv ≫ tilde.map (relativeConormalAffineLinearG α σ hσ) ≫ eQ.hom) =
    ((relativeConormalAffineMiddleIso α σ).hom ≫
      tilde.map (relativeConormalAffineLinearG α σ hσ) ≫
        (relativeDifferentialAffineIso (α ≫ σ)).inv) ≫
          ((relativeDifferentialAffineIso (α ≫ σ)).hom ≫ eQ.hom)
  exact (frameCancelLeft (relativeConormalAffineMiddleIso α σ).hom eM
    (tilde.map (relativeConormalAffineLinearG α σ hσ)) eQ.hom).trans
      (frameCancelRight (relativeConormalAffineMiddleIso α σ).hom
        (tilde.map (relativeConormalAffineLinearG α σ hσ))
        (relativeDifferentialAffineIso (α ≫ σ)) eQ.hom).symm

private theorem freePointBlockDet (U : (Spec B).Opens)
    (v : Fin s.length →
      (SheafOfModules.free (R := (Spec B).ringCatSheaf)
        (ULift.{u} (Fin s.length))).val.obj (Opposite.op U))
    (w : Fin n →
      (SheafOfModules.free (R := (Spec B).ringCatSheaf)
        (ULift.{u} (Fin (s.length + n)))).val.obj (Opposite.op U)) :
    letI := nativeFreeModule (Spec B) U s.length
    letI := nativeFreeModule (Spec B) U n
    letI := nativeFreeModule (Spec B) U (s.length + n)
    (SheafOfModulesOfCommRing.freeFinSectionsBasis (Spec B).sheaf (s.length + n)
      (Opposite.op U)).det.toFun
        (Fin.append (fun i =>
          (sectionFreeF α σ hσ s hs hker hA hB bQ).val.app (Opposite.op U) (v i)) w) =
      (SheafOfModulesOfCommRing.freeFinSectionsBasis (Spec B).sheaf s.length
        (Opposite.op U)).det.toFun v *
      (SheafOfModulesOfCommRing.freeFinSectionsBasis (Spec B).sheaf n
        (Opposite.op U)).det.toFun (fun j =>
          (sectionFreeG α σ hσ s hs hker hA hB bQ).val.app (Opposite.op U) (w j)) := by
  classical
  let := nativeFreeModule (Spec B) U s.length
  let := nativeFreeModule (Spec B) U n
  let := nativeFreeModule (Spec B) U (s.length + n)
  let bC := SheafOfModulesOfCommRing.freeFinSectionsBasis (Spec B).sheaf s.length
    (Opposite.op U)
  let bQΓ := SheafOfModulesOfCommRing.freeFinSectionsBasis (Spec B).sheaf n
    (Opposite.op U)
  let bM := SheafOfModulesOfCommRing.freeFinSectionsBasis (Spec B).sheaf (s.length + n)
    (Opposite.op U)
  let F := freePointLinear (sectionFreeF α σ hσ s hs hker hA hB bQ) U
  let G := freePointLinear (sectionFreeG α σ hσ s hs hker hA hB bQ) U
  apply sectionBlockDetFin bC bQΓ bM F G _ _ _ v w
  · intro i
    exact ((congrArg F
      (SheafOfModulesOfCommRing.freeFinSectionsBasis_apply (Spec B).sheaf s.length
        (Opposite.op U) i)).trans
      (sectionFreeF_basis α σ hσ s hs hker hA hB bQ U i)).trans
        (SheafOfModulesOfCommRing.freeFinSectionsBasis_apply (Spec B).sheaf (s.length + n)
          (Opposite.op U) (finSumFinEquiv (Sum.inl i))).symm
  · intro i
    exact (congrArg G
      (SheafOfModulesOfCommRing.freeFinSectionsBasis_apply (Spec B).sheaf (s.length + n)
        (Opposite.op U) (finSumFinEquiv (Sum.inl i)))).trans
      (sectionFreeG_basis₁ α σ hσ s hs hker hA hB bQ U i)
  · intro j
    exact ((congrArg G
      (SheafOfModulesOfCommRing.freeFinSectionsBasis_apply (Spec B).sheaf (s.length + n)
        (Opposite.op U) (finSumFinEquiv (Sum.inr j)))).trans
      (sectionFreeG_basis₂ α σ hσ s hs hker hA hB bQ U j)).trans
        (SheafOfModulesOfCommRing.freeFinSectionsBasis_apply (Spec B).sheaf n
          (Opposite.op U) j).symm

private theorem frameDeterminantIso_sectionWedge (U : (Spec B).Opens)
    (v : Fin s.length →
      ((pullback (Spec.map σ)).obj (idealModule (Spec.map σ))).val.obj (Opposite.op U))
    (w : Fin n → (relativeConormalAffineComplex α σ hσ).X₂.val.obj (Opposite.op U)) :
    (frameDeterminantIso α σ hσ s hs hker hA hB bQ).hom.val.app (Opposite.op U)
      (moduleTensorSection (Spec B) _ _ U
        ((SheafOfModulesOfCommRing.exteriorPowerMk (Spec B).sheaf
          ((pullback (Spec.map σ)).obj (idealModule (Spec.map σ))) s.length).app
            (Opposite.op U) v)
        ((SheafOfModulesOfCommRing.exteriorPowerMk (Spec B).sheaf
          (relativeConormalAffineComplex α σ hσ).X₃ n).app (Opposite.op U)
          (fun j => (relativeConormalAffineComplex α σ hσ).g.val.app (Opposite.op U) (w j)))) =
      (SheafOfModulesOfCommRing.exteriorPowerMk (Spec B).sheaf
        (relativeConormalAffineComplex α σ hσ).X₂ (s.length + n)).app (Opposite.op U)
        (Fin.append (fun i => (relativeConormalAffineComplex α σ hσ).f.val.app (Opposite.op U)
          ((relativeConormalAffineIdealPullbackIso α σ hσ).hom.val.app (Opposite.op U)
            (v i))) w) := by
  let := nativeFreeModule (Spec B) U s.length
  let := nativeFreeModule (Spec B) U n
  let := nativeFreeModule (Spec B) U (s.length + n)
  let eC := relativeConormalAffineGeometricFreeIso α σ hσ s hs hker
  let eQ := quotientFreeIso α σ hσ bQ
  let eM := middleFreeIso α σ hσ s hs hker hA hB bQ
  let tC := actualTopFrame _ s.length eC
  let tQ := actualTopFrame _ n eQ
  let tM := actualTopFrame _ (s.length + n) eM
  let vv := fun i => eC.hom.val.app (Opposite.op U) (v i)
  let ww := fun j => eM.hom.val.app (Opposite.op U) (w j)
  let fv := fun i => (relativeConormalAffineComplex α σ hσ).f.val.app (Opposite.op U)
    ((relativeConormalAffineIdealPullbackIso α σ hσ).hom.val.app (Opposite.op U) (v i))
  let gw := fun j => (relativeConormalAffineComplex α σ hσ).g.val.app (Opposite.op U) (w j)
  have hF (i : Fin s.length) :
      (sectionFreeF α σ hσ s hs hker hA hB bQ).val.app (Opposite.op U) (vv i) =
        eM.hom.val.app (Opposite.op U) (fv i) :=
    congrArg (fun f => f.val.app (Opposite.op U) (v i))
      (sectionFreeF_naturality α σ hσ s hs hker hA hB bQ)
  have hG (j : Fin n) :
      (sectionFreeG α σ hσ s hs hker hA hB bQ).val.app (Opposite.op U) (ww j) =
        eQ.hom.val.app (Opposite.op U) (gw j) :=
    congrArg (fun f => f.val.app (Opposite.op U) (w j))
      (sectionFreeG_naturality α σ hσ s hs hker hA hB bQ)
  have hfamily :
      Fin.append (fun i =>
        (sectionFreeF α σ hσ s hs hker hA hB bQ).val.app (Opposite.op U) (vv i)) ww =
      fun k => eM.hom.val.app (Opposite.op U) (Fin.append fv w k) := by
    funext k
    obtain ⟨k, rfl⟩ := finSumFinEquiv.surjective k
    cases k with
    | inl i =>
      simpa only [finSumFinEquiv_apply_left, Fin.append_left] using hF i
    | inr j => simp only [finSumFinEquiv_apply_right, Fin.append_right, ww]
  have hdet := freePointBlockDet α σ hσ s hs hker hA hB bQ U vv ww
  have hdet' :
      (SheafOfModulesOfCommRing.freeFinSectionsBasis (Spec B).sheaf (s.length + n)
        (Opposite.op U)).det.toFun (fun k =>
          eM.hom.val.app (Opposite.op U) (Fin.append fv w k)) =
      (SheafOfModulesOfCommRing.freeFinSectionsBasis (Spec B).sheaf s.length
        (Opposite.op U)).det.toFun vv *
      (SheafOfModulesOfCommRing.freeFinSectionsBasis (Spec B).sheaf n
        (Opposite.op U)).det.toFun (fun j => eQ.hom.val.app (Opposite.op U) (gw j)) := by
    exact (congrArg
      (fun z => (SheafOfModulesOfCommRing.freeFinSectionsBasis (Spec B).sheaf
        (s.length + n) (Opposite.op U)).det.toFun z) hfamily).symm.trans
      (hdet.trans (congrArg (fun z =>
        (SheafOfModulesOfCommRing.freeFinSectionsBasis (Spec B).sheaf s.length
          (Opposite.op U)).det.toFun vv *
        (SheafOfModulesOfCommRing.freeFinSectionsBasis (Spec B).sheaf n
          (Opposite.op U)).det.toFun z) (funext hG)))
  apply isoSectionsHom_injective tM U
  have hleft := actualLineTensorIso_coordinates tC tQ tM U
    ((SheafOfModulesOfCommRing.exteriorPowerMk (Spec B).sheaf
      ((pullback (Spec.map σ)).obj (idealModule (Spec.map σ))) s.length).app
        (Opposite.op U) v)
    ((SheafOfModulesOfCommRing.exteriorPowerMk (Spec B).sheaf
      (relativeConormalAffineComplex α σ hσ).X₃ n).app (Opposite.op U) gw)
  have hC := actualTopFrame_mk _ s.length eC U v
  have hQ := actualTopFrame_mk _ n eQ U gw
  have hM := actualTopFrame_mk _ (s.length + n) eM U (Fin.append fv w)
  exact hleft.trans ((congrArg₂ (fun a b : Γ(Spec B, U) => a * b) hC hQ).trans
    (hdet'.symm.trans hM.symm))

private theorem frameDeterminantIso_eq :
    relativeConormalAffineDeterminantIso α σ hσ s hs hker hA hB bQ =
      frameDeterminantIso α σ hσ s hs hker hA hB bQ := by
  let NC := (pullback (Spec.map σ)).obj (idealModule (Spec.map σ))
  let NQ := (relativeConormalAffineComplex α σ hσ).X₃
  let NM := (relativeConormalAffineComplex α σ hσ).X₂
  let bC := relativeConormalAffineBasis α σ hσ s hs hker
  let bM := orderedMiddleBasis α σ hσ s hs hker hA hB bQ
  let eC0 := relativeConormalAffineIdealPullbackIso α σ hσ
  let eQ0 := relativeDifferentialAffineIso (α ≫ σ)
  let eM0 := relativeConormalAffineMiddleIso α σ
  let eC := actualTopFrame NC s.length (affineFreeIso NC C s.length bC eC0)
  let eQ := actualTopFrame NQ n (affineFreeIso NQ Q n bQ eQ0)
  let eM := actualTopFrame NM (s.length + n)
    (affineFreeIso NM ((ModuleCat.extendScalars σ.hom).obj
      (CommRingCat.KaehlerDifferential α)) (s.length + n) bM eM0)
  let eS := actualLineTensorIso eC eQ
    (Iso.refl (SheafOfModules.unit (Spec B).ringCatSheaf))
  let a := fun U => affineNativeWedge NC C s.length eC0 U bC
  let b := fun U => affineNativeWedge NQ Q n eQ0 U bQ
  let z := fun U => moduleTensorSection (Spec B)
    (moduleExteriorPower (Spec B) NC s.length) (moduleExteriorPower (Spec B) NQ n) U
      (a U) (b U)
  have hv (U : (Spec B).Opens) :
      eS.hom.val.app (Opposite.op U) (z U) = (1 : Γ(Spec B, U)) := by
    have h := actualLineTensorIso_coordinates eC eQ
      (Iso.refl (SheafOfModules.unit (Spec B).ringCatSheaf)) U (a U) (b U)
    have hC := affineTopFrame_nativeWedge NC C s.length bC eC0 U bC
    have hQ := affineTopFrame_nativeWedge NQ Q n bQ eQ0 U bQ
    rw [Module.Basis.det_self, _root_.map_one] at hC hQ
    exact h.trans ((congrArg₂ (fun x y : Γ(Spec B, U) => x * y) hC hQ).trans
      (one_mul 1))
  let w := fun j => bM (finSumFinEquiv (Sum.inr j))
  have hq : (fun j => relativeConormalAffineLinearG α σ hσ (w j)) = bQ :=
    funext (middleBasis_G₂ α σ hσ s hs hker hA hB bQ)
  have hmid : Fin.append (fun i => relativeConormalAffineLinearF α σ hσ (bC i)) w =
      bM := by
    funext k
    obtain ⟨k, rfl⟩ := finSumFinEquiv.surjective k
    cases k with
    | inl i =>
      simpa only [finSumFinEquiv_apply_left, Fin.append_left] using
        middleBasis_F α σ hσ s hs hker hA hB bQ i
    | inr j => simp only [finSumFinEquiv_apply_right, Fin.append_right, w]
  apply Iso.ext
  apply hom_ext_of_unitFrame eS z hv
  intro U
  have ho := relativeConormalAffineDeterminantIso_wedge α σ hσ s hs hker hA hB bQ U bC w
  have hq_apply (j : Fin n) : relativeConormalAffineLinearG α σ hσ (w j) = bQ j :=
    congrFun hq j
  simp only [hq_apply] at ho
  refine ho.trans (isoSectionsHom_injective eM U ?_)
  have hM := affineTopFrame_nativeWedge NM ((ModuleCat.extendScalars σ.hom).obj
    (CommRingCat.KaehlerDifferential α)) (s.length + n) bM eM0 U
      (Fin.append (fun i => relativeConormalAffineLinearF α σ hσ (bC i)) w)
  have hdet : bM.det (Fin.append
      (fun i => relativeConormalAffineLinearF α σ hσ (bC i)) w) = (1 : B) :=
    (congrArg bM.det hmid).trans (Module.Basis.det_self bM)
  rw [hdet, _root_.map_one] at hM
  have h := actualLineTensorIso_coordinates eC eQ eM U (a U) (b U)
  have hC := affineTopFrame_nativeWedge NC C s.length bC eC0 U bC
  have hQ := affineTopFrame_nativeWedge NQ Q n bQ eQ0 U bQ
  rw [Module.Basis.det_self, _root_.map_one] at hC hQ
  exact hM.trans (h.trans ((congrArg₂ (fun x y : Γ(Spec B, U) => x * y) hC hQ).trans
    (one_mul 1))).symm

/-- The conormal determinant concatenates arbitrary normal sections and tangent lifts. -/
theorem relativeConormalAffineDeterminantIso_sectionWedge (U : (Spec B).Opens)
    (v : Fin s.length →
      ((pullback (Spec.map σ)).obj (idealModule (Spec.map σ))).val.obj (Opposite.op U))
    (w : Fin n → (relativeConormalAffineComplex α σ hσ).X₂.val.obj (Opposite.op U)) :
    (relativeConormalAffineDeterminantIso α σ hσ s hs hker hA hB bQ).hom.val.app (Opposite.op U)
      (moduleTensorSection (Spec B) _ _ U
        ((SheafOfModulesOfCommRing.exteriorPowerMk (Spec B).sheaf
          ((pullback (Spec.map σ)).obj (idealModule (Spec.map σ))) s.length).app
            (Opposite.op U) v)
        ((SheafOfModulesOfCommRing.exteriorPowerMk (Spec B).sheaf
          (relativeConormalAffineComplex α σ hσ).X₃ n).app (Opposite.op U)
          (fun j => (relativeConormalAffineComplex α σ hσ).g.val.app (Opposite.op U) (w j)))) =
      (SheafOfModulesOfCommRing.exteriorPowerMk (Spec B).sheaf
        (relativeConormalAffineComplex α σ hσ).X₂ (s.length + n)).app (Opposite.op U)
        (Fin.append (fun i => (relativeConormalAffineComplex α σ hσ).f.val.app (Opposite.op U)
          ((relativeConormalAffineIdealPullbackIso α σ hσ).hom.val.app (Opposite.op U)
            (v i))) w) := by
  rw [frameDeterminantIso_eq α σ hσ s hs hker hA hB bQ]
  exact frameDeterminantIso_sectionWedge α σ hσ s hs hker hA hB bQ U v w

omit hσ hs hker hA hB bQ in
private theorem freeSectionDet (X : Scheme.{u}) (U : X.Opens) (d : ℕ) :
    letI := nativeFreeModule X U d
    (SheafOfModulesOfCommRing.freeFinSectionsBasis X.sheaf d (Opposite.op U)).det.toFun
      (fun i => (SheafOfModules.freeSection (R := X.ringCatSheaf) (ULift.up i)).val
        (Opposite.op U)) = (1 : Γ(X, U)) := by
  let := nativeFreeModule X U d
  let b := SheafOfModulesOfCommRing.freeFinSectionsBasis X.sheaf d (Opposite.op U)
  exact (congrArg b.det.toFun (funext fun i =>
    SheafOfModulesOfCommRing.freeFinSectionsBasis_apply X.sheaf d (Opposite.op U) i)).symm.trans
      (Module.Basis.det_self b)

omit hσ hs hker hA hB bQ in
private def inverseFrameSections {X : Scheme.{u}} {M : X.Modules} {d : ℕ}
    (e : M ≅ SheafOfModules.free (R := X.ringCatSheaf) (ULift.{u} (Fin d)))
    (U : X.Opens) (i : Fin d) : M.val.obj (Opposite.op U) :=
  e.inv.val.app (Opposite.op U)
    ((SheafOfModules.freeSection (R := X.ringCatSheaf) (ULift.up i)).val (Opposite.op U))

omit hσ hs hker hA hB bQ in
private theorem inverseFrameSections_coordinates {X : Scheme.{u}} {M : X.Modules} {d : ℕ}
    (e : M ≅ SheafOfModules.free (R := X.ringCatSheaf) (ULift.{u} (Fin d)))
    (U : X.Opens) (i : Fin d) :
    e.hom.val.app (Opposite.op U) (inverseFrameSections e U i) =
      (SheafOfModules.freeSection (R := X.ringCatSheaf) (ULift.up i)).val (Opposite.op U) :=
  congrArg (fun f => f.val.app (Opposite.op U)
    ((SheafOfModules.freeSection (R := X.ringCatSheaf) (ULift.up i)).val (Opposite.op U)))
      e.inv_hom_id

omit hσ hs hker hA hB bQ in
private theorem actualTopFrame_coordinateOne {X : Scheme.{u}} {M : X.Modules} {d : ℕ}
    (e : M ≅ SheafOfModules.free (R := X.ringCatSheaf) (ULift.{u} (Fin d)))
    (U : X.Opens) (v : Fin d → M.val.obj (Opposite.op U))
    (hv : ∀ i, e.hom.val.app (Opposite.op U) (v i) =
      (SheafOfModules.freeSection (R := X.ringCatSheaf) (ULift.up i)).val (Opposite.op U)) :
    (actualTopFrame M d e).hom.val.app (Opposite.op U)
      ((SheafOfModulesOfCommRing.exteriorPowerMk X.sheaf M d).app
        (Opposite.op U) v) = (1 : Γ(X, U)) := by
  let := nativeFreeModule X U d
  exact (actualTopFrame_mk M d e U v).trans ((congrArg
    (SheafOfModulesOfCommRing.freeFinSectionsBasis X.sheaf d (Opposite.op U)).det.toFun
      (funext hv)).trans (freeSectionDet X U d))

private def tangentLiftSections (U : (Spec B).Opens) (j : Fin n) :=
  inverseFrameSections (middleFreeIso α σ hσ s hs hker hA hB bQ) U
    (finSumFinEquiv (Sum.inr j))

private theorem tangentLiftSections_coordinates (U : (Spec B).Opens) (j : Fin n) :
    (quotientFreeIso α σ hσ bQ).hom.val.app (Opposite.op U)
      ((relativeConormalAffineComplex α σ hσ).g.val.app (Opposite.op U)
        (tangentLiftSections α σ hσ s hs hker hA hB bQ U j)) =
      (SheafOfModules.freeSection (R := (Spec B).ringCatSheaf) (ULift.up j)).val
        (Opposite.op U) := by
  have h := congrArg (fun f => f.val.app (Opposite.op U)
    (tangentLiftSections α σ hσ s hs hker hA hB bQ U j))
      (sectionFreeG_naturality α σ hσ s hs hker hA hB bQ)
  exact h.symm.trans ((congrArg
    ((sectionFreeG α σ hσ s hs hker hA hB bQ).val.app (Opposite.op U))
    (inverseFrameSections_coordinates (middleFreeIso α σ hσ s hs hker hA hB bQ)
      U (finSumFinEquiv (Sum.inr j)))).trans
        (sectionFreeG_basis₂ α σ hσ s hs hker hA hB bQ U j))

end AlgebraicGeometry.Scheme.Modules.Differentials

namespace AlgebraicGeometry.Scheme.Modules.Differentials
open scoped ChangeOfRings
variable {R A B : CommRingCat.{u}} (α : R ⟶ A) (σ : A ⟶ B)
  (hσ : Function.Surjective σ) (s : List A)

private theorem localizedWeak (hs : RingTheory.Sequence.IsWeaklyRegular A s) (r : A) :
    RingTheory.Sequence.IsWeaklyRegular (Localization.Away r)
      (s.map (algebraMap A (Localization.Away r))) := hs.of_flat

private theorem localizedKernel (hk : Ideal.ofList s = RingHom.ker σ.hom) (r : A) :
    Ideal.ofList (s.map (algebraMap A (Localization.Away r))) =
      RingHom.ker (relativeConormalAffineLocalizationMap σ r).hom := by
  rw [← Ideal.map_ofList, hk]
  have hmap : (relativeConormalAffineLocalizationMap σ r).hom =
      IsLocalization.Away.map (Localization.Away r) (Localization.Away (σ r)) σ.hom r := by
    apply IsLocalization.ringHom_ext (Submonoid.powers r)
    apply RingHom.ext
    intro a
    change relativeConormalAffineLocalizationMap σ r (algebraMap A (Localization.Away r) a) = _
    rw [relativeConormalAffineLocalizationMap_algebraMap]
    simp only [IsLocalization.Away.map, RingHom.comp_apply, IsLocalization.map_eq]
  rw [hmap]
  symm
  simpa only [IsLocalization.Away.map] using
    (IsLocalization.ker_map (S := Localization.Away r) (M := Submonoid.powers r)
      (T := Submonoid.powers (σ r)) (Localization.Away (σ r)) σ.hom
      (by rw [Submonoid.map_powers]))

private theorem localizedFormalAmbient (hA : α.hom.FormallySmooth) (r : A) :
    (α ≫ CommRingCat.ofHom (algebraMap A (Localization.Away r))).hom.FormallySmooth := by
  exact hA.comp (RingHom.formallySmooth_algebraMap.mpr
    (Algebra.FormallySmooth.of_isLocalization (Submonoid.powers r)))

private theorem localizedFormalTarget (hB : (α ≫ σ).hom.FormallySmooth) (r : A) :
    ((α ≫ CommRingCat.ofHom (algebraMap A (Localization.Away r))) ≫
      relativeConormalAffineLocalizationMap σ r).hom.FormallySmooth := by
  have H : (α ≫ CommRingCat.ofHom (algebraMap A (Localization.Away r))) ≫
      relativeConormalAffineLocalizationMap σ r =
      (α ≫ σ) ≫ CommRingCat.ofHom (algebraMap B (Localization.Away (σ r))) := by
    rw [Category.assoc, relativeConormalAffineLocalizationMap_square]
    rfl
  rw [H]
  exact hB.comp (RingHom.formallySmooth_algebraMap.mpr
    (Algebra.FormallySmooth.of_isLocalization (Submonoid.powers (σ r))))

/-- The quotient differential basis transported by the original localization map. -/
def relativeConormalAffineLocalizedQuotientBasis {n : ℕ}
    (bQ : Module.Basis (Fin n) B (CommRingCat.KaehlerDifferential (α ≫ σ))) (r : A) :
    Module.Basis (Fin n) (Localization.Away (σ r))
      (CommRingCat.KaehlerDifferential
        ((α ≫ CommRingCat.ofHom (algebraMap A (Localization.Away r))) ≫
          relativeConormalAffineLocalizationMap σ r)) := by
  let B' := CommRingCat.of (Localization.Away (σ r))
  let aBB' : Algebra B B' := (algebraMap B B').toAlgebra
  let : Algebra B B' := aBB'
  let : Module B B' := @Algebra.toModule B B' _ _ aBB'
  let : SMul B B' := aBB'.toSMul
  let τ := relativeConormalAffineLinearLocalizationIso α σ hσ r
  let e := (asIso τ.hom.τ₃).toLinearEquiv
  exact (bQ.baseChange B').map e

private def topRestrictionComparison {X Y : Scheme.{u}} (j : X ⟶ Y) [IsOpenImmersion j]
    {M : Y.Modules} {N : X.Modules} (e : M.restrict j ≅ N) (d : ℕ) :
    (moduleExteriorPower Y M d).restrict j ≅ moduleExteriorPower X N d :=
  (moduleExteriorPowerRestrictionIso j M d).symm ≪≫
    (moduleExteriorPowerFunctor X d).mapIso e

/-- The original conormal ideal-pullback comparison under principal localization. -/
@[no_expose] def relativeConormalAffineGeometricRestrictionLocalizationIso (r : A) :
    let B' := CommRingCat.of (Localization.Away (σ r))
    let σ' := relativeConormalAffineLocalizationMap σ r
    let j := Spec.map (CommRingCat.ofHom (algebraMap B B'))
    ((pullback (Spec.map σ)).obj (idealModule (Spec.map σ))).restrict j ≅
      (pullback (Spec.map σ')).obj (idealModule (Spec.map σ')) := by
  intro B' σ' j
  let A' := CommRingCat.of (Localization.Away r)
  let α' := α ≫ CommRingCat.ofHom (algebraMap A A')
  let hσ' := relativeConormalAffineLocalizationMap_surjective σ hσ r
  let τ := relativeConormalAffineRestrictionLocalizationIso α σ hσ r
  exact (restrictFunctor j).mapIso (relativeConormalAffineIdealPullbackIso α σ hσ) ≪≫
    ShortComplex.π₁.mapIso τ ≪≫ (relativeConormalAffineIdealPullbackIso α' σ' hσ').symm

/-- Restriction of the two exterior factors, with the normal factor first. -/
@[no_expose] def relativeConormalAffineDeterminantSourceRestrictionIso (r : A) (c d : ℕ) :
    let A' := CommRingCat.of (Localization.Away r)
    let B' := CommRingCat.of (Localization.Away (σ r))
    let α' := α ≫ CommRingCat.ofHom (algebraMap A A')
    let σ' := relativeConormalAffineLocalizationMap σ r
    let hσ' := relativeConormalAffineLocalizationMap_surjective σ hσ r
    let j := Spec.map (CommRingCat.ofHom (algebraMap B B'))
    (restrictFunctor j).obj (tensorSheaf (Spec B)
      (moduleExteriorPower (Spec B)
        ((pullback (Spec.map σ)).obj (idealModule (Spec.map σ))) c)
      (moduleExteriorPower (Spec B) (relativeConormalAffineComplex α σ hσ).X₃ d)) ≅
    tensorSheaf (Spec B')
      (moduleExteriorPower (Spec B')
        ((pullback (Spec.map σ')).obj (idealModule (Spec.map σ'))) c)
      (moduleExteriorPower (Spec B') (relativeConormalAffineComplex α' σ' hσ').X₃ d) := by
  intro _A' B' α' σ' hσ' j
  let τ := relativeConormalAffineRestrictionLocalizationIso α σ hσ r
  let Ctop := moduleExteriorPower (Spec B)
    ((pullback (Spec.map σ)).obj (idealModule (Spec.map σ))) c
  let Qtop := moduleExteriorPower (Spec B) (relativeConormalAffineComplex α σ hσ).X₃ d
  let eC := topRestrictionComparison j (relativeConormalAffineGeometricRestrictionLocalizationIso
    α σ hσ r) c
  let eQ := topRestrictionComparison j (asIso τ.hom.τ₃) d
  exact (tensorRestrictionIso j Ctop Qtop).symm ≪≫
    ((SheafOfModulesOfCommRing.tensorFunctor (Spec B').sheaf).mapIso eC).app ((restrictFunctor
      j).obj Qtop) ≪≫
      (moduleTensorLeftFunctor (Spec B') _).mapIso eQ

/-- Restriction of the ambient exterior factor through the original conormal comparison. -/
@[no_expose] def relativeConormalAffineDeterminantTargetRestrictionIso (r : A) (d : ℕ) :
    let A' := CommRingCat.of (Localization.Away r)
    let B' := CommRingCat.of (Localization.Away (σ r))
    let α' := α ≫ CommRingCat.ofHom (algebraMap A A')
    let σ' := relativeConormalAffineLocalizationMap σ r
    let hσ' := relativeConormalAffineLocalizationMap_surjective σ hσ r
    let j := Spec.map (CommRingCat.ofHom (algebraMap B B'))
    (moduleExteriorPower (Spec B) (relativeConormalAffineComplex α σ hσ).X₂ d).restrict j ≅
      moduleExteriorPower (Spec B') (relativeConormalAffineComplex α' σ' hσ').X₂ d := by
  intro A' B' α' σ' hσ' j
  exact topRestrictionComparison j
    (asIso (relativeConormalAffineRestrictionLocalizationIso α σ hσ r).hom.τ₂) d

private def castDeterminantIso (X : Scheme.{u}) (C Q M : X.Modules) (n : ℕ) {c d : ℕ}
    (h : c = d) (e : tensorSheaf X (moduleExteriorPower X C c) (moduleExteriorPower X Q n) ≅
      moduleExteriorPower X M (c + n)) :
    tensorSheaf X (moduleExteriorPower X C d) (moduleExteriorPower X Q n) ≅
      moduleExteriorPower X M (d + n) :=
  (eqToIso (congrArg (fun k => tensorSheaf X
    (moduleExteriorPower X C k) (moduleExteriorPower X Q n)) h)).symm ≪≫ e ≪≫
      eqToIso (congrArg (fun k => moduleExteriorPower X M (k + n)) h)

/-- The same-list localized determinant, with its explicit list-length transport. -/
@[no_expose] def relativeConormalAffineLocalizedDeterminantIso
    (hs : RingTheory.Sequence.IsWeaklyRegular A s) (hk : Ideal.ofList s = RingHom.ker σ.hom)
    (hA : α.hom.FormallySmooth) (hB : (α ≫ σ).hom.FormallySmooth) {n : ℕ}
    (bQ : Module.Basis (Fin n) B (CommRingCat.KaehlerDifferential (α ≫ σ))) (r : A) :
    let A' := CommRingCat.of (Localization.Away r)
    let B' := CommRingCat.of (Localization.Away (σ r))
    let α' := α ≫ CommRingCat.ofHom (algebraMap A A')
    let σ' := relativeConormalAffineLocalizationMap σ r
    let hσ' := relativeConormalAffineLocalizationMap_surjective σ hσ r
    tensorSheaf (Spec B')
      (moduleExteriorPower (Spec B')
        ((pullback (Spec.map σ')).obj (idealModule (Spec.map σ'))) s.length)
      (moduleExteriorPower (Spec B') (relativeConormalAffineComplex α' σ' hσ').X₃ n) ≅
    moduleExteriorPower (Spec B') (relativeConormalAffineComplex α' σ' hσ').X₂ (s.length + n) := by
  intro A' B' α' σ' hσ'
  let t := s.map (algebraMap A A')
  let ht := localizedWeak s hs r
  let hkt := localizedKernel σ s hk r
  let ha := localizedFormalAmbient α hA r
  let hb := localizedFormalTarget α σ hB r
  let b := relativeConormalAffineLocalizedQuotientBasis α σ hσ bQ r
  let e := relativeConormalAffineDeterminantIso α' σ' hσ' t ht hkt ha hb b
  exact castDeterminantIso (Spec B') _ _ _ n (List.length_map (algebraMap A A')) e

private theorem topRestrictionComparison_mk {X Y : Scheme.{u}} (j : X ⟶ Y)
    [IsOpenImmersion j] {M : Y.Modules} {N : X.Modules} (e : M.restrict j ≅ N)
    (d : ℕ) (U : X.Opens) (v : Fin d → (M.restrict j).val.obj (Opposite.op U)) :
    (topRestrictionComparison j e d).hom.val.app (Opposite.op U)
      ((SheafOfModulesOfCommRing.exteriorPowerMk Y.sheaf M d).app
        (Opposite.op (j ''ᵁ U)) v) =
      (SheafOfModulesOfCommRing.exteriorPowerMk X.sheaf N d).app
        (Opposite.op U) (fun i => e.hom.val.app (Opposite.op U) (v i)) := by
  change ((moduleExteriorPowerFunctor X d).map e.hom).val.app (Opposite.op U)
    ((moduleExteriorPowerRestrictionIso j M d).inv.val.app (Opposite.op U) _) = _
  exact (congrArg (((moduleExteriorPowerFunctor X d).map e.hom).val.app (Opposite.op U))
    (moduleExteriorPowerRestrictionIso_inv_mk j M d U v)).trans
      (SheafOfModulesOfCommRing.exteriorPowerFunctor_map_mk X.sheaf e.hom d
        (Opposite.op U) v)

private theorem tensorRestrictionComparison_section {X Y : Scheme.{u}} (j : X ⟶ Y)
    [IsOpenImmersion j] (E M : Y.Modules) {E' M' : X.Modules}
    (eE : E.restrict j ≅ E') (eM : M.restrict j ≅ M') (U : X.Opens)
    (a : (E.restrict j).val.obj (Opposite.op U))
    (b : (M.restrict j).val.obj (Opposite.op U)) :
    ((tensorRestrictionIso j E M).symm ≪≫
      ((SheafOfModulesOfCommRing.tensorFunctor X.sheaf).mapIso eE).app (M.restrict j) ≪≫
        (moduleTensorLeftFunctor X E').mapIso eM).hom.val.app (Opposite.op U)
      (moduleTensorSection Y E M (j ''ᵁ U) a b) =
      moduleTensorSection X E' M' U (eE.hom.val.app (Opposite.op U) a)
        (eM.hom.val.app (Opposite.op U) b) := by
  let t := tensorRestrictionIso j E M
  have hi : t.inv.val.app (Opposite.op U)
      (moduleTensorSection Y E M (j ''ᵁ U) a b) =
        moduleTensorSection X (E.restrict j) (M.restrict j) U a b :=
    (congrArg (t.inv.val.app (Opposite.op U))
      (tensorRestrictionIso_section j E M U a b).symm).trans
        (congrArg (fun f => f.val.app (Opposite.op U)
          (moduleTensorSection X (E.restrict j) (M.restrict j) U a b)) t.hom_inv_id)
  change ((moduleTensorLeftFunctor X E').map eM.hom).val.app (Opposite.op U)
    (((moduleTensorCoefficientMap X eE.hom).app (M.restrict j)).val.app (Opposite.op U)
      (t.inv.val.app (Opposite.op U) _)) = _
  exact (congrArg (fun x =>
    ((moduleTensorLeftFunctor X E').map eM.hom).val.app (Opposite.op U)
      (((moduleTensorCoefficientMap X eE.hom).app (M.restrict j)).val.app
        (Opposite.op U) x)) hi).trans
    ((congrArg (((moduleTensorLeftFunctor X E').map eM.hom).val.app (Opposite.op U))
      (moduleTensorCoefficientMap_section eE.hom (M.restrict j) U a b)).trans
        (moduleTensorLeftFunctor_map_section E' eM.hom U
          (eE.hom.val.app (Opposite.op U) a) b))

private theorem restrictedUnitFrame {X Y : Scheme.{u}} (j : X ⟶ Y) [IsOpenImmersion j]
    {L : Y.Modules} (e : L ≅ SheafOfModules.unit Y.ringCatSheaf)
    (v : ∀ W : Y.Opens, L.val.obj (Opposite.op W))
    (hv : ∀ W : Y.Opens, e.hom.val.app (Opposite.op W) (v W) = (1 : Γ(Y, W)))
    (U : X.Opens) :
    (((restrictFunctor j).mapIso e) ≪≫ restrictUnitIso j).hom.val.app (Opposite.op U)
      (v (j ''ᵁ U)) = (1 : Γ(X, U)) := by
  change (j.appIso U).hom (e.hom.val.app (Opposite.op (j ''ᵁ U)) (v (j ''ᵁ U))) = 1
  exact (congrArg (j.appIso U).hom (hv (j ''ᵁ U))).trans
    ((j.appIso U).hom.hom.map_one)

private theorem castDeterminantIso_sectionWedge
    (X : Scheme.{u}) (C Q M : X.Modules) (f : C ⟶ M) (g : M ⟶ Q)
    {c d n : ℕ} (hc : c = d)
    (D : tensorSheaf X (moduleExteriorPower X C c) (moduleExteriorPower X Q n) ≅
      moduleExteriorPower X M (c + n))
    (hD : ∀ (U : X.Opens) (v : Fin c → C.val.obj (Opposite.op U))
        (w : Fin n → M.val.obj (Opposite.op U)),
      D.hom.val.app (Opposite.op U) (moduleTensorSection X _ _ U
        ((SheafOfModulesOfCommRing.exteriorPowerMk X.sheaf C c).app (Opposite.op U) v)
        ((SheafOfModulesOfCommRing.exteriorPowerMk X.sheaf Q n).app (Opposite.op U)
          (fun j => g.val.app (Opposite.op U) (w j)))) =
        (SheafOfModulesOfCommRing.exteriorPowerMk X.sheaf M (c + n)).app (Opposite.op U)
          (Fin.append (fun i => f.val.app (Opposite.op U) (v i)) w))
    (U : X.Opens) (v : Fin d → C.val.obj (Opposite.op U))
    (w : Fin n → M.val.obj (Opposite.op U)) :
    (castDeterminantIso X C Q M n hc D).hom.val.app (Opposite.op U)
      (moduleTensorSection X _ _ U
        ((SheafOfModulesOfCommRing.exteriorPowerMk X.sheaf C d).app (Opposite.op U) v)
        ((SheafOfModulesOfCommRing.exteriorPowerMk X.sheaf Q n).app (Opposite.op U)
          (fun j => g.val.app (Opposite.op U) (w j)))) =
      (SheafOfModulesOfCommRing.exteriorPowerMk X.sheaf M (d + n)).app (Opposite.op U)
        (Fin.append (fun i => f.val.app (Opposite.op U) (v i)) w) := by
  cases hc
  exact hD U v w

private theorem relativeConormalAffineLocalizedDeterminantIso_sectionWedge
    (hs : RingTheory.Sequence.IsWeaklyRegular A s) (hk : Ideal.ofList s = RingHom.ker σ.hom)
    (hA : α.hom.FormallySmooth) (hB : (α ≫ σ).hom.FormallySmooth) {n : ℕ}
    (bQ : Module.Basis (Fin n) B (CommRingCat.KaehlerDifferential (α ≫ σ))) (r : A) :
    let A' := CommRingCat.of (Localization.Away r)
    let B' := CommRingCat.of (Localization.Away (σ r))
    let α' := α ≫ CommRingCat.ofHom (algebraMap A A')
    let σ' := relativeConormalAffineLocalizationMap σ r
    let hσ' := relativeConormalAffineLocalizationMap_surjective σ hσ r
    ∀ (U : (Spec B').Opens)
      (v : Fin s.length →
        ((pullback (Spec.map σ')).obj (idealModule (Spec.map σ'))).val.obj (Opposite.op U))
      (w : Fin n → (relativeConormalAffineComplex α' σ' hσ').X₂.val.obj (Opposite.op U)),
      (relativeConormalAffineLocalizedDeterminantIso α σ hσ s hs hk hA hB bQ r).hom.val.app
        (Opposite.op U)
        (moduleTensorSection (Spec B') _ _ U
          ((SheafOfModulesOfCommRing.exteriorPowerMk (Spec B').sheaf
            ((pullback (Spec.map σ')).obj (idealModule (Spec.map σ'))) s.length).app
              (Opposite.op U) v)
          ((SheafOfModulesOfCommRing.exteriorPowerMk (Spec B').sheaf
            (relativeConormalAffineComplex α' σ' hσ').X₃ n).app (Opposite.op U)
            (fun j => (relativeConormalAffineComplex α' σ' hσ').g.val.app
              (Opposite.op U) (w j)))) =
        (SheafOfModulesOfCommRing.exteriorPowerMk (Spec B').sheaf
          (relativeConormalAffineComplex α' σ' hσ').X₂ (s.length + n)).app (Opposite.op U)
          (Fin.append (fun i => (relativeConormalAffineComplex α' σ' hσ').f.val.app
            (Opposite.op U) ((relativeConormalAffineIdealPullbackIso α' σ' hσ').hom.val.app
              (Opposite.op U) (v i))) w) := by
  intro A' B' α' σ' hσ' U v w
  let t := s.map (algebraMap A A')
  let ht := localizedWeak s hs r
  let hkt := localizedKernel σ s hk r
  let ha := localizedFormalAmbient α hA r
  let hb := localizedFormalTarget α σ hB r
  let b := relativeConormalAffineLocalizedQuotientBasis α σ hσ bQ r
  exact castDeterminantIso_sectionWedge (Spec B') _ _ _
    ((relativeConormalAffineIdealPullbackIso α' σ' hσ').hom ≫
      (relativeConormalAffineComplex α' σ' hσ').f)
    (relativeConormalAffineComplex α' σ' hσ').g (List.length_map (algebraMap A A'))
    (relativeConormalAffineDeterminantIso α' σ' hσ' t ht hkt ha hb b)
    (relativeConormalAffineDeterminantIso_sectionWedge α' σ' hσ' t ht hkt ha hb b) U v w

private theorem mapAppend {C₀ D₀ : Type*} {c d : ℕ} (f : C₀ → D₀)
    (v : Fin c → C₀) (w : Fin d → C₀) :
    (fun k => f (Fin.append v w k)) = Fin.append (fun i => f (v i)) (fun j => f (w j)) := by
  funext k
  refine Fin.addCases (fun i => ?_) (fun j => ?_) k
  · simp only [Fin.append_left]
  · simp only [Fin.append_right]

private theorem relativeConormalAffineDeterminantIso_principal_section
    (hs : RingTheory.Sequence.IsWeaklyRegular A s) (hk : Ideal.ofList s = RingHom.ker σ.hom)
    (hA : α.hom.FormallySmooth) (hB : (α ≫ σ).hom.FormallySmooth) {n : ℕ}
    (bQ : Module.Basis (Fin n) B (CommRingCat.KaehlerDifferential (α ≫ σ))) (r : A) :
    let B' := CommRingCat.of (Localization.Away (σ r))
    let j := Spec.map (CommRingCat.ofHom (algebraMap B B'))
    ∀ (U : (Spec B').Opens)
      (v : Fin s.length →
        (((pullback (Spec.map σ)).obj (idealModule (Spec.map σ))).restrict j).val.obj
          (Opposite.op U))
      (w : Fin n → ((relativeConormalAffineComplex α σ hσ).X₂.restrict j).val.obj
        (Opposite.op U)),
    ((restrictFunctor j).map
        (relativeConormalAffineDeterminantIso α σ hσ s hs hk hA hB bQ).hom ≫
      (relativeConormalAffineDeterminantTargetRestrictionIso α σ hσ r (s.length + n)).hom).val.app
        (Opposite.op U) (moduleTensorSection (Spec B)
        (moduleExteriorPower (Spec B)
          ((pullback (Spec.map σ)).obj (idealModule (Spec.map σ))) s.length)
        (moduleExteriorPower (Spec B) (relativeConormalAffineComplex α σ hσ).X₃ n)
        (j ''ᵁ U)
        ((SheafOfModulesOfCommRing.exteriorPowerMk (Spec B).sheaf
          ((pullback (Spec.map σ)).obj (idealModule (Spec.map σ))) s.length).app
            (Opposite.op (j ''ᵁ U)) v)
        ((SheafOfModulesOfCommRing.exteriorPowerMk (Spec B).sheaf
          (relativeConormalAffineComplex α σ hσ).X₃ n).app
            (Opposite.op (j ''ᵁ U)) (fun k =>
              (relativeConormalAffineComplex α σ hσ).g.val.app (Opposite.op (j ''ᵁ U)) (w k)))) =
    ((relativeConormalAffineDeterminantSourceRestrictionIso α σ hσ r s.length n).hom ≫
      (relativeConormalAffineLocalizedDeterminantIso α σ hσ s hs hk hA hB bQ r).hom).val.app
        (Opposite.op U) (moduleTensorSection (Spec B)
        (moduleExteriorPower (Spec B)
          ((pullback (Spec.map σ)).obj (idealModule (Spec.map σ))) s.length)
        (moduleExteriorPower (Spec B) (relativeConormalAffineComplex α σ hσ).X₃ n)
        (j ''ᵁ U)
        ((SheafOfModulesOfCommRing.exteriorPowerMk (Spec B).sheaf
          ((pullback (Spec.map σ)).obj (idealModule (Spec.map σ))) s.length).app
            (Opposite.op (j ''ᵁ U)) v)
        ((SheafOfModulesOfCommRing.exteriorPowerMk (Spec B).sheaf
          (relativeConormalAffineComplex α σ hσ).X₃ n).app
            (Opposite.op (j ''ᵁ U)) (fun k =>
              (relativeConormalAffineComplex α σ hσ).g.val.app (Opposite.op (j ''ᵁ U)) (w k)))) :=
                by
  intro B' j U v w
  let A' := CommRingCat.of (Localization.Away r)
  let α' := α ≫ CommRingCat.ofHom (algebraMap A A')
  let σ' := relativeConormalAffineLocalizationMap σ r
  let hσ' := relativeConormalAffineLocalizationMap_surjective σ hσ r
  let S := relativeConormalAffineComplex α σ hσ
  let S' := relativeConormalAffineComplex α' σ' hσ'
  let NC := (pullback (Spec.map σ)).obj (idealModule (Spec.map σ))
  let NC' := (pullback (Spec.map σ')).obj (idealModule (Spec.map σ'))
  let τ := relativeConormalAffineRestrictionLocalizationIso α σ hσ r
  let τC := relativeConormalAffineGeometricRestrictionLocalizationIso α σ hσ r
  let τM := asIso τ.hom.τ₂
  let τQ := asIso τ.hom.τ₃
  let W := j ''ᵁ U
  let a := (SheafOfModulesOfCommRing.exteriorPowerMk (Spec B).sheaf NC s.length).app
    (Opposite.op W) v
  let b := (SheafOfModulesOfCommRing.exteriorPowerMk (Spec B).sheaf S.X₃ n).app
    (Opposite.op W) (fun k => S.g.val.app (Opposite.op W) (w k))
  let z := moduleTensorSection (Spec B)
    (moduleExteriorPower (Spec B) NC s.length)
    (moduleExteriorPower (Spec B) S.X₃ n) W a b
  let v' := fun i => τC.hom.val.app (Opposite.op U) (v i)
  let w' := fun j => τM.hom.val.app (Opposite.op U) (w j)
  let fv := fun i => S.f.val.app (Opposite.op W)
    ((relativeConormalAffineIdealPullbackIso α σ hσ).hom.val.app (Opposite.op W) (v i))
  let fv' := fun i => S'.f.val.app (Opposite.op U)
    ((relativeConormalAffineIdealPullbackIso α' σ' hσ').hom.val.app (Opposite.op U) (v' i))
  have hC (i : Fin s.length) :
      (relativeConormalAffineIdealPullbackIso α' σ' hσ').hom.val.app (Opposite.op U)
        (v' i) =
      τ.hom.τ₁.val.app (Opposite.op U)
        ((relativeConormalAffineIdealPullbackIso α σ hσ).hom.val.app (Opposite.op W)
          (v i)) := by
    change (relativeConormalAffineIdealPullbackIso α' σ' hσ').hom.val.app (Opposite.op U)
      ((relativeConormalAffineIdealPullbackIso α' σ' hσ').inv.val.app (Opposite.op U) _) = _
    exact congrArg (fun f => f.val.app (Opposite.op U)
      (τ.hom.τ₁.val.app (Opposite.op U)
        ((relativeConormalAffineIdealPullbackIso α σ hσ).hom.val.app (Opposite.op W)
          (v i)))) (relativeConormalAffineIdealPullbackIso α' σ' hσ').inv_hom_id
  have hF (i : Fin s.length) : fv' i = τM.hom.val.app (Opposite.op U) (fv i) :=
    (congrArg (S'.f.val.app (Opposite.op U)) (hC i)).trans
      (congrArg (fun f => f.val.app (Opposite.op U)
        ((relativeConormalAffineIdealPullbackIso α σ hσ).hom.val.app (Opposite.op W)
          (v i))) τ.hom.comm₁₂)
  have hG (k : Fin n) :
      τQ.hom.val.app (Opposite.op U) (S.g.val.app (Opposite.op W) (w k)) = S'.g.val.app
        (Opposite.op U) (w' k) :=
    (congrArg (fun f => f.val.app (Opposite.op U) (w k)) τ.hom.comm₂₃).symm
  let eCt := topRestrictionComparison j τC s.length
  let eQt := topRestrictionComparison j τQ n
  have hsource := tensorRestrictionComparison_section j
    (moduleExteriorPower (Spec B) NC s.length) (moduleExteriorPower (Spec B) S.X₃ n)
    eCt eQt U a b
  have hsource' :
      (relativeConormalAffineDeterminantSourceRestrictionIso α σ hσ r s.length n).hom.val.app
        (Opposite.op U)
        z = moduleTensorSection (Spec B')
        (moduleExteriorPower (Spec B') NC' s.length)
        (moduleExteriorPower (Spec B') S'.X₃ n) U
        ((SheafOfModulesOfCommRing.exteriorPowerMk (Spec B').sheaf NC' s.length).app
          (Opposite.op U) v')
        ((SheafOfModulesOfCommRing.exteriorPowerMk (Spec B').sheaf S'.X₃ n).app
          (Opposite.op U) (fun k => S'.g.val.app (Opposite.op U) (w' k))) := by
    exact hsource.trans (congrArg₂ (moduleTensorSection (Spec B')
      (moduleExteriorPower (Spec B') NC' s.length)
      (moduleExteriorPower (Spec B') S'.X₃ n) U)
      (topRestrictionComparison_mk j τC s.length U v)
      ((topRestrictionComparison_mk j τQ n U (fun k => S.g.val.app (Opposite.op W) (w k))).trans
        (congrArg ((SheafOfModulesOfCommRing.exteriorPowerMk (Spec B').sheaf S'.X₃ n).app
          (Opposite.op U)) (funext hG))))
  have hright := (congrArg
    ((relativeConormalAffineLocalizedDeterminantIso α σ hσ s hs hk hA hB bQ r).hom.val.app
      (Opposite.op U))
    hsource').trans
      (relativeConormalAffineLocalizedDeterminantIso_sectionWedge α σ hσ s hs hk hA hB bQ r U v' w')
  have hleft := (congrArg
    ((relativeConormalAffineDeterminantTargetRestrictionIso α σ hσ r (s.length + n)).hom.val.app
      (Opposite.op U))
    (relativeConormalAffineDeterminantIso_sectionWedge α σ hσ s hs hk hA hB bQ W v w)).trans
      (topRestrictionComparison_mk j τM (s.length + n) U (Fin.append fv w))
  have hfamily : (fun k => τM.hom.val.app (Opposite.op U) (Fin.append fv w k)) =
      Fin.append fv' w' :=
    (mapAppend (τM.hom.val.app (Opposite.op U)) fv w).trans
      (congrArg₂ Fin.append (funext fun i => (hF i).symm) rfl)
  exact hleft.trans ((congrArg
    ((SheafOfModulesOfCommRing.exteriorPowerMk (Spec B').sheaf S'.X₂ (s.length + n)).app
      (Opposite.op U)) hfamily).trans hright.symm)

/-- Principal localization commutes with the same-list conormal determinant. -/
theorem relativeConormalAffineDeterminantIso_principal
    (hs : RingTheory.Sequence.IsWeaklyRegular A s) (hk : Ideal.ofList s = RingHom.ker σ.hom)
    (hA : α.hom.FormallySmooth) (hB : (α ≫ σ).hom.FormallySmooth) {n : ℕ}
    (bQ : Module.Basis (Fin n) B (CommRingCat.KaehlerDifferential (α ≫ σ))) (r : A) :
    let B' := CommRingCat.of (Localization.Away (σ r))
    let j := Spec.map (CommRingCat.ofHom (algebraMap B B'))
    (restrictFunctor j).map
        (relativeConormalAffineDeterminantIso α σ hσ s hs hk hA hB bQ).hom ≫
      (relativeConormalAffineDeterminantTargetRestrictionIso α σ hσ r (s.length + n)).hom =
    (relativeConormalAffineDeterminantSourceRestrictionIso α σ hσ r s.length n).hom ≫
      (relativeConormalAffineLocalizedDeterminantIso α σ hσ s hs hk hA hB bQ r).hom := by
  intro B' j
  let S := relativeConormalAffineComplex α σ hσ
  let NC := (pullback (Spec.map σ)).obj (idealModule (Spec.map σ))
  let eC := relativeConormalAffineGeometricFreeIso α σ hσ s hs hk
  let eQ := quotientFreeIso α σ hσ bQ
  let tC := actualTopFrame NC s.length eC
  let tQ := actualTopFrame S.X₃ n eQ
  let eS := actualLineTensorIso tC tQ (Iso.refl (SheafOfModules.unit (Spec B).ringCatSheaf))
  let v := fun W => inverseFrameSections eC W
  let w := fun W => tangentLiftSections α σ hσ s hs hk hA hB bQ W
  let q := fun W j => S.g.val.app (Opposite.op W) (w W j)
  let a := fun W => (SheafOfModulesOfCommRing.exteriorPowerMk (Spec B).sheaf NC s.length).app
    (Opposite.op W) (v W)
  let b := fun W => (SheafOfModulesOfCommRing.exteriorPowerMk (Spec B).sheaf S.X₃ n).app
    (Opposite.op W) (q W)
  let z := fun W => moduleTensorSection (Spec B)
    (moduleExteriorPower (Spec B) NC s.length)
    (moduleExteriorPower (Spec B) S.X₃ n) W (a W) (b W)
  have hv (W : (Spec B).Opens) :
      eS.hom.val.app (Opposite.op W) (z W) = (1 : Γ(Spec B, W)) := by
    have h1 := actualLineTensorIso_coordinates tC tQ
      (Iso.refl (SheafOfModules.unit (Spec B).ringCatSheaf)) W (a W) (b W)
    have hC := actualTopFrame_coordinateOne eC W (v W)
      (inverseFrameSections_coordinates eC W)
    have hQ := actualTopFrame_coordinateOne eQ W (q W)
      (tangentLiftSections_coordinates α σ hσ s hs hk hA hB bQ W)
    exact h1.trans ((congrArg₂ (fun x y : Γ(Spec B, W) => x * y) hC hQ).trans (one_mul 1))
  apply hom_ext_of_unitFrame
    (((restrictFunctor j).mapIso eS) ≪≫ restrictUnitIso j)
    (fun U => z (j ''ᵁ U)) (restrictedUnitFrame j eS z hv)
  intro U
  exact relativeConormalAffineDeterminantIso_principal_section α σ hσ s hs hk hA hB bQ r U
    (v (j ''ᵁ U)) (w (j ''ᵁ U))

end AlgebraicGeometry.Scheme.Modules.Differentials
