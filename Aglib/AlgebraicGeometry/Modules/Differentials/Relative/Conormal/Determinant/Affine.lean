/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Aglib.AlgebraicGeometry.Modules.Differentials.Relative.Conormal.Frames
public import Aglib.LinearAlgebra.ExteriorPower.TopDegree
public import Aglib.Algebra.Category.ModuleCat.Sheaf.ExteriorPower.FreeTop
public import Aglib.AlgebraicGeometry.Modules.ExteriorPower.Restriction
public import Aglib.AlgebraicGeometry.Modules.Tensor.Basic
public import Aglib.AlgebraicGeometry.Modules.Tensor.Sections
public import Aglib.AlgebraicGeometry.Modules.Tensor.ToUnit
/-!
# The actual affine conormal exterior-line isomorphism

The same ordered regular-kernel classes and original conormal arrows give
an isomorphism from the conormal top exterior line tensor the quotient
relative differential top line to the pulled-back ambient top line.
Conormal vectors come FIRST. On every open, the original pure tensor of
native wedges maps to the original concatenated wedge of the original
conormal images and tangent lifts. Equality of the actual sheaf
isomorphisms proves independence of the quotient differential basis.

The construction retains the original ideal-pullback, tilde and free-frame
comparisons, tensor orientation and native unit. The coefficient rings
are arbitrary, including zero rings, and both exterior degrees may be zero.
The rank comparison uses a target point rather than a public nontriviality
hypothesis. Independent principal-localization compatibility, global
canonical-line gluing and purity/trace transport are later consumers.
The ambient projective coefficient determinant remains explicit.
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

private theorem middleBasis_det (v : Fin s.length → C)
    (w : Fin n → (ModuleCat.extendScalars σ.hom).obj (CommRingCat.KaehlerDifferential α)) :
    (middleBasis α σ hσ s hs hker hA hB bQ).det
      (Sum.elim (fun i => relativeConormalAffineLinearF α σ hσ (v i)) w) =
      (relativeConormalAffineBasis α σ hσ s hs hker).det v *
        bQ.det (fun j => relativeConormalAffineLinearG α σ hσ (w j)) := by
  let := σ.hom.toAlgebra
  exact (Classical.choose_spec
    (relativeConormalAffineNormalFirstFrame α σ hσ s hs hker hA hB bQ)).2.2 v w

private def orderedMiddleBasis : Module.Basis (Fin (s.length + n)) B
    ((ModuleCat.extendScalars σ.hom).obj (CommRingCat.KaehlerDifferential α)) :=
  (middleBasis α σ hσ s hs hker hA hB bQ).reindex (finSumFinEquiv)

private def determinantIso :
    ((⋀[B]^s.length C) ⊗[B] (⋀[B]^n Q)) ≃ₗ[B]
      (⋀[B]^(s.length + n) ((ModuleCat.extendScalars σ.hom).obj
        (CommRingCat.KaehlerDifferential α))) :=
  (TensorProduct.congr
    (relativeConormalAffineBasis α σ hσ s hs hker).exteriorPowerTopEquiv
    bQ.exteriorPowerTopEquiv) ≪≫ₗ TensorProduct.lid B B ≪≫ₗ
      (orderedMiddleBasis α σ hσ s hs hker hA hB bQ).exteriorPowerTopEquiv.symm

private theorem determinantIso_wedge (v : Fin s.length → C)
    (w : Fin n → (ModuleCat.extendScalars σ.hom).obj (CommRingCat.KaehlerDifferential α)) :
    determinantIso α σ hσ s hs hker hA hB bQ
      (exteriorPower.ιMulti B s.length v ⊗ₜ[B]
        exteriorPower.ιMulti B n (fun j => relativeConormalAffineLinearG α σ hσ (w j))) =
      exteriorPower.ιMulti B (s.length + n)
        (Fin.append (fun i => relativeConormalAffineLinearF α σ hσ (v i)) w) := by
  apply (orderedMiddleBasis α σ hσ s hs hker hA hB bQ).exteriorPowerTopEquiv.injective
  have hleft :
      (orderedMiddleBasis α σ hσ s hs hker hA hB bQ).exteriorPowerTopEquiv
        (determinantIso α σ hσ s hs hker hA hB bQ
          (exteriorPower.ιMulti B s.length v ⊗ₜ[B]
            exteriorPower.ιMulti B n (fun j => relativeConormalAffineLinearG α σ hσ (w j)))) =
      (relativeConormalAffineBasis α σ hσ s hs hker).det v *
        bQ.det (fun j => relativeConormalAffineLinearG α σ hσ (w j)) := by
    simp only [determinantIso, LinearEquiv.trans_apply, TensorProduct.congr_tmul,
      Module.Basis.exteriorPowerTopEquiv_ιMulti, TensorProduct.lid_tmul,
      smul_eq_mul, LinearEquiv.apply_symm_apply]
  rw [hleft, Module.Basis.exteriorPowerTopEquiv_ιMulti]
  rw [orderedMiddleBasis, Module.Basis.det_reindex]
  have hfamily :
      Fin.append (fun i => relativeConormalAffineLinearF α σ hσ (v i)) w ∘
        finSumFinEquiv =
      Sum.elim (fun i => relativeConormalAffineLinearF α σ hσ (v i)) w := by
    funext i
    cases i with
    | inl i =>
      simpa only [Function.comp_apply, finSumFinEquiv_apply_left, Sum.elim_inl] using
        Fin.append_left (fun i => relativeConormalAffineLinearF α σ hσ (v i)) w i
    | inr j =>
      simpa only [Function.comp_apply, finSumFinEquiv_apply_right, Sum.elim_inr] using
        Fin.append_right (fun i => relativeConormalAffineLinearF α σ hσ (v i)) w j
  rw [hfamily]
  exact (middleBasis_det α σ hσ s hs hker hA hB bQ v w).symm

/-- The same normal-FIRST middle frame has ambient rank equal to the two block ranks.
A target point supplies nontriviality internally; the empty source needs no rank bound. -/
theorem relativeConormalAffineDimension_eq (N : ℕ)
    (bN : Module.Basis (Fin N) B
      ((ModuleCat.extendScalars σ.hom).obj (CommRingCat.KaehlerDifferential α)))
    (p : PrimeSpectrum B) : N = s.length + n := by
  let : Nontrivial B := (algebraMap B (Localization.AtPrime p.asIdeal)).domain_nontrivial
  have h1 := Module.finrank_eq_card_basis bN
  have h2 := Module.finrank_eq_card_basis (middleBasis α σ hσ s hs hker hA hB bQ)
  simpa only [Fintype.card_fin, Fintype.card_sum] using h1.symm.trans h2

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

private def geometricDeterminantIso :
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

/-- The actual normal-FIRST conormal determinant isomorphism for the original spectral map. -/
def relativeConormalAffineDeterminantIso :
    tensorSheaf (Spec B)
      (moduleExteriorPower (Spec B)
        ((pullback (Spec.map σ)).obj (idealModule (Spec.map σ))) s.length)
      (moduleExteriorPower (Spec B) (relativeConormalAffineComplex α σ hσ).X₃ n) ≅
    moduleExteriorPower (Spec B) (relativeConormalAffineComplex α σ hσ).X₂ (s.length + n) :=
  private_decl% (geometricDeterminantIso α σ hσ s hs hker hA hB bQ)

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

private theorem orderedMiddleBasis_det (v : Fin s.length → C)
    (w : Fin n → (ModuleCat.extendScalars σ.hom).obj (CommRingCat.KaehlerDifferential α)) :
    (orderedMiddleBasis α σ hσ s hs hker hA hB bQ).det
      (Fin.append (fun i => relativeConormalAffineLinearF α σ hσ (v i)) w) =
      (relativeConormalAffineBasis α σ hσ s hs hker).det v *
        bQ.det (fun j => relativeConormalAffineLinearG α σ hσ (w j)) := by
  have h := congrArg
    (orderedMiddleBasis α σ hσ s hs hker hA hB bQ).exteriorPowerTopEquiv
    (determinantIso_wedge α σ hσ s hs hker hA hB bQ v w)
  simpa only [determinantIso, LinearEquiv.trans_apply, TensorProduct.congr_tmul,
    Module.Basis.exteriorPowerTopEquiv_ιMulti, TensorProduct.lid_tmul,
    smul_eq_mul, LinearEquiv.apply_symm_apply] using h.symm

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

private theorem geometricDeterminantIso_nativeWedge (U : (Spec B).Opens) (v : Fin s.length → C)
    (w : Fin n → (ModuleCat.extendScalars σ.hom).obj (CommRingCat.KaehlerDifferential α)) :
    (geometricDeterminantIso α σ hσ s hs hker hA hB bQ).hom.val.app (Opposite.op U)
      (moduleTensorSection (Spec B)
        (moduleExteriorPower (Spec B)
          ((pullback (Spec.map σ)).obj (idealModule (Spec.map σ))) s.length)
        (moduleExteriorPower (Spec B) (relativeConormalAffineComplex α σ hσ).X₃ n) U
        (affineNativeWedge _ C s.length (relativeConormalAffineIdealPullbackIso α σ hσ) U v)
        (affineNativeWedge _ Q n (relativeDifferentialAffineIso (α ≫ σ)) U
          (fun j => relativeConormalAffineLinearG α σ hσ (w j)))) =
      affineNativeWedge _ ((ModuleCat.extendScalars σ.hom).obj
        (CommRingCat.KaehlerDifferential α)) (s.length + n)
        (relativeConormalAffineMiddleIso α σ) U
        (Fin.append (fun i => relativeConormalAffineLinearF α σ hσ (v i)) w) := by
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
  let a := affineNativeWedge NC C s.length eC0 U v
  let b := affineNativeWedge NQ Q n eQ0 U
    (fun j => relativeConormalAffineLinearG α σ hσ (w j))
  let z := affineNativeWedge NM ((ModuleCat.extendScalars σ.hom).obj
    (CommRingCat.KaehlerDifferential α)) (s.length + n) eM0 U
    (Fin.append (fun i => relativeConormalAffineLinearF α σ hσ (v i)) w)
  apply isoSectionsHom_injective eM U
  change eM.hom.val.app (Opposite.op U)
    ((actualLineTensorIso eC eQ eM).hom.val.app (Opposite.op U)
      (moduleTensorSection (Spec B) _ _ U a b)) = eM.hom.val.app (Opposite.op U) z
  have hC := affineTopFrame_nativeWedge NC C s.length bC eC0 U v
  have hQ := affineTopFrame_nativeWedge NQ Q n bQ eQ0 U
    (fun j => relativeConormalAffineLinearG α σ hσ (w j))
  have hM := affineTopFrame_nativeWedge NM ((ModuleCat.extendScalars σ.hom).obj
    (CommRingCat.KaehlerDifferential α)) (s.length + n) bM eM0 U
    (Fin.append (fun i => relativeConormalAffineLinearF α σ hσ (v i)) w)
  change (show Γ(Spec B, U) from eC.hom.val.app (Opposite.op U) a) =
    algebraMap B Γ(Spec B, U) (bC.det v) at hC
  change (show Γ(Spec B, U) from eQ.hom.val.app (Opposite.op U) b) =
    algebraMap B Γ(Spec B, U)
      (bQ.det (fun j => relativeConormalAffineLinearG α σ hσ (w j))) at hQ
  change (show Γ(Spec B, U) from eM.hom.val.app (Opposite.op U) z) =
    algebraMap B Γ(Spec B, U)
      (bM.det (Fin.append (fun i => relativeConormalAffineLinearF α σ hσ (v i)) w)) at hM
  have hleft := actualLineTensorIso_coordinates eC eQ eM U a b
  have hmul := congrArg₂ (fun x y : Γ(Spec B, U) => x * y) hC hQ
  have hφ := congrArg (algebraMap B Γ(Spec B, U))
    (orderedMiddleBasis_det α σ hσ s hs hker hA hB bQ v w).symm
  rw [_root_.map_mul] at hφ
  exact hleft.trans (hmul.trans (hφ.trans hM.symm))



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

private theorem geometricDeterminantIso_independent_basis
    (bQ' : Module.Basis (Fin n) B Q) :
    geometricDeterminantIso α σ hσ s hs hker hA hB bQ =
      geometricDeterminantIso α σ hσ s hs hker hA hB bQ' := by
  let NC := (pullback (Spec.map σ)).obj (idealModule (Spec.map σ))
  let NQ := (relativeConormalAffineComplex α σ hσ).X₃
  let bC := relativeConormalAffineBasis α σ hσ s hs hker
  let eC0 := relativeConormalAffineIdealPullbackIso α σ hσ
  let eQ0 := relativeDifferentialAffineIso (α ≫ σ)
  let eC := actualTopFrame NC s.length (affineFreeIso NC C s.length bC eC0)
  let eQ := actualTopFrame NQ n (affineFreeIso NQ Q n bQ eQ0)
  let eS := actualLineTensorIso eC eQ (Iso.refl (SheafOfModules.unit (Spec B).ringCatSheaf))
  let a := fun U => affineNativeWedge NC C s.length eC0 U bC
  let b := fun U => affineNativeWedge NQ Q n eQ0 U bQ
  let v := fun U => moduleTensorSection (Spec B)
    (moduleExteriorPower (Spec B) NC s.length) (moduleExteriorPower (Spec B) NQ n) U
    (a U) (b U)
  have hv (U : (Spec B).Opens) :
      eS.hom.val.app (Opposite.op U) (v U) = (1 : Γ(Spec B, U)) := by
    have h := actualLineTensorIso_coordinates eC eQ
      (Iso.refl (SheafOfModules.unit (Spec B).ringCatSheaf)) U (a U) (b U)
    have hC := affineTopFrame_nativeWedge NC C s.length bC eC0 U bC
    have hQ := affineTopFrame_nativeWedge NQ Q n bQ eQ0 U bQ
    rw [Module.Basis.det_self, _root_.map_one] at hC hQ
    change (show Γ(Spec B, U) from eC.hom.val.app (Opposite.op U) (a U)) = 1 at hC
    change (show Γ(Spec B, U) from eQ.hom.val.app (Opposite.op U) (b U)) = 1 at hQ
    exact h.trans ((congrArg₂ (fun x y : Γ(Spec B, U) => x * y) hC hQ).trans (one_mul 1))
  apply Iso.ext
  apply hom_ext_of_unitFrame eS v hv
  intro U
  have hsurj : Function.Surjective (relativeConormalAffineLinearG α σ hσ) :=
    (ModuleCat.epi_iff_surjective _).mp (relativeConormalAffineLinearComplex_epi α σ hσ)
  choose w hw using fun j => hsurj (bQ j)
  have hq : (fun j => relativeConormalAffineLinearG α σ hσ (w j)) = bQ := funext hw
  have h1 := geometricDeterminantIso_nativeWedge α σ hσ s hs hker hA hB bQ U bC w
  have h2 := geometricDeterminantIso_nativeWedge α σ hσ s hs hker hA hB bQ' U bC w
  rw [hq] at h1 h2
  exact h1.trans h2.symm

/-- On every open, the original conormal wedge and quotient image wedge map to the
literal normal-FIRST wedge; the original maps and tangent lifts are preserved. -/
theorem relativeConormalAffineDeterminantIso_wedge (U : (Spec B).Opens)
    (v : Fin s.length → C)
    (w : Fin n → (ModuleCat.extendScalars σ.hom).obj (CommRingCat.KaehlerDifferential α)) :
    (relativeConormalAffineDeterminantIso α σ hσ s hs hker hA hB bQ).hom.val.app
      (Opposite.op U)
      (moduleTensorSection (Spec B)
        (moduleExteriorPower (Spec B)
          ((pullback (Spec.map σ)).obj (idealModule (Spec.map σ))) s.length)
        (moduleExteriorPower (Spec B) (relativeConormalAffineComplex α σ hσ).X₃ n) U
        ((SheafOfModulesOfCommRing.exteriorPowerMk (Spec B).sheaf
          ((pullback (Spec.map σ)).obj (idealModule (Spec.map σ))) s.length).app
          (Opposite.op U) (fun i =>
            (relativeConormalAffineIdealPullbackIso α σ hσ).inv.val.app (Opposite.op U)
              (tilde.toOpen C U (v i))))
        ((SheafOfModulesOfCommRing.exteriorPowerMk (Spec B).sheaf
          (relativeConormalAffineComplex α σ hσ).X₃ n).app (Opposite.op U) (fun j =>
            (relativeDifferentialAffineIso (α ≫ σ)).inv.val.app (Opposite.op U)
              (tilde.toOpen Q U (relativeConormalAffineLinearG α σ hσ (w j)))))) =
      (SheafOfModulesOfCommRing.exteriorPowerMk (Spec B).sheaf
        (relativeConormalAffineComplex α σ hσ).X₂ (s.length + n)).app (Opposite.op U)
        (fun k => (relativeConormalAffineMiddleIso α σ).inv.val.app (Opposite.op U)
          (tilde.toOpen ((ModuleCat.extendScalars σ.hom).obj
            (CommRingCat.KaehlerDifferential α)) U
            (Fin.append (fun i => relativeConormalAffineLinearF α σ hσ (v i)) w k))) :=
  geometricDeterminantIso_nativeWedge α σ hσ s hs hker hA hB bQ U v w

/-- The actual sheaf isomorphism is independent of the displayed quotient differential basis. -/
theorem relativeConormalAffineDeterminantIso_independent_basis
    (bQ' : Module.Basis (Fin n) B Q) :
    relativeConormalAffineDeterminantIso α σ hσ s hs hker hA hB bQ =
      relativeConormalAffineDeterminantIso α σ hσ s hs hker hA hB bQ' :=
  geometricDeterminantIso_independent_basis α σ hσ s hs hker hA hB bQ bQ'

end AlgebraicGeometry.Scheme.Modules.Differentials
