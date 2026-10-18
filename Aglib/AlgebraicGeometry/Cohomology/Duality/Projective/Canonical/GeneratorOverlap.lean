/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.Canonical.AffineDeterminant
public import Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.Canonical.GeneratorCancellation
public import Aglib.Algebra.Homology.Koszul.Ext.GeneratorChange
public import Aglib.AlgebraicGeometry.Modules.StructureSheaf.Sections

/-!
# Canonical purity overlap for ordered regular generators

Equal-ideal and equal-degree transports identify the original native Ext
classes. The determinant factor comes from the actual recursive Koszul
comparison and cancels against the same ordered conormal dual frame.
The resulting actual canonical top-homology arrows agree for arbitrary
ambient, tangent and coefficient frames. The original normal-first
determinant, scalar-extension maps, pullback unit and native counit are
retained throughout. The matrix need not be invertible over the ambient ring.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Abelian AlgebraicGeometry Opposite
open CategoryTheory.MonoidalCategory
open AlgebraicGeometry.Scheme.Modules.Differentials
open AlgebraicGeometry.Scheme.Modules.Invertible
open AlgebraicGeometry.Scheme.Hom
open scoped TensorProduct

universe u w a b

namespace AlgebraicGeometry.Scheme.Modules

variable {A : CommRingCat.{u}}

section NativeExt
variable [HasExt.{w} (ModuleCat.{u} A)]

/-- The original top class transported only through the displayed ideal and
degree equalities, on a fixed quotient module and a fixed degree. -/
def regularListTopExtClassAt (I : Ideal A) (c : ℕ) (s : List A)
    (hs : RingTheory.Sequence.IsWeaklyRegular A s)
    (hI : Ideal.ofList s = I) (hc : s.length = c) (r : A) :
    Ext.{w} (ModuleCat.of A (A ⧸ I)) (ModuleCat.of A A) c := by
  subst I c
  exact ChainComplex.Koszul.topExtClass s hs (ModuleCat.of A A) r

private theorem regularListTopExtClassAt_eq (I : Ideal A) (c : ℕ) (s : List A)
    (hs : RingTheory.Sequence.IsWeaklyRegular A s)
    (hI : Ideal.ofList s = I) (hc : s.length = c) (r : A) :
    let q : ModuleCat.of A (A ⧸ I) ⟶ ModuleCat.of A (A ⧸ Ideal.ofList s) :=
      ModuleCat.ofHom (I.mapQ (Ideal.ofList s) LinearMap.id hI.ge)
    regularListTopExtClassAt I c s hs hI hc r =
      (Ext.mk₀ q).comp
        (cast (congrArg (fun k => Ext.{w} (ModuleCat.of A (A ⧸ Ideal.ofList s))
          (ModuleCat.of A A) k) hc)
          (ChainComplex.Koszul.topExtClass s hs (ModuleCat.of A A) r))
        (zero_add c) := by
  subst I c
  dsimp only [regularListTopExtClassAt]
  have hq : ModuleCat.ofHom ((Ideal.ofList s).mapQ (Ideal.ofList s) LinearMap.id le_rfl) =
      𝟙 (ModuleCat.of A (A ⧸ Ideal.ofList s)) := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective z
    rfl
  rw [hq, Ext.mk₀_id_comp]
  rfl

/-- On the same quotient and in the same degree the original class gains
exactly the matrix determinant. -/
theorem regularListTopExtClassAt_generatorChange (I : Ideal A) (c : ℕ)
    (s t : List A) (hs : RingTheory.Sequence.IsWeaklyRegular A s)
    (ht : RingTheory.Sequence.IsWeaklyRegular A t)
    (hsI : Ideal.ofList s = I) (htI : Ideal.ofList t = I)
    (hsc : s.length = c) (htc : t.length = c)
    (M : Matrix (Fin s.length) (Fin s.length) A)
    (hM : t = List.ofFn (fun i => ∑ j, M i j * s.get j)) (r : A) :
    regularListTopExtClassAt I c s hs hsI hsc r =
      regularListTopExtClassAt I c t ht htI htc (M.det * r) := by
  cases htI
  cases htc
  change regularListTopExtClassAt (Ideal.ofList t) t.length s hs hsI hsc r =
    ChainComplex.Koszul.topExtClass t ht (ModuleCat.of A A) (M.det * r)
  rw [regularListTopExtClassAt_eq]
  exact ChainComplex.Koszul.topExtClass_generatorChange s t hs ht M hM hsI.symm r

section NativeClasses

variable (I : Ideal A) (c : ℕ) {L : (Spec A).Modules} [L.IsQuasicoherent]
  (e : moduleSpecΓFunctor.obj L ≅ ModuleCat.of A A)
  [HasDerivedCategory.{a} (Spec A).Modules]
  [HasDerivedCategory.{b} (Spec (CommRingCat.of (A ⧸ I))).Modules]

private abbrev commonQuotientMap : A ⟶ CommRingCat.of (A ⧸ I) :=
  CommRingCat.ofHom (Ideal.Quotient.mk I)

/-- The fixed native top homology object on the common quotient. -/
abbrev regularListNativeTopHomologyAt :=
  let q : A ⟶ CommRingCat.of (A ⧸ I) := CommRingCat.ofHom (Ideal.Quotient.mk I)
  (DerivedCategory.Plus.homologyFunctor (Spec (CommRingCat.of (A ⧸ I))).Modules
    (c : ℤ)).obj
    ((closedImmersionRightAdjoint (Spec.map q)).rightDerivedFunctorPlus.obj
      ((DerivedCategory.Plus.singleFunctor (Spec A).Modules 0).obj L))

private abbrev commonModel :=
  ((closedImmersionRightAdjoint (Spec.map (commonQuotientMap I))).mapHomologicalComplex
    (.up ℤ)).obj (injectiveResolution L).cochainComplex

local instance : (moduleSpecΓFunctor (R := CommRingCat.of (A ⧸ I))).Additive :=
  moduleSpecΓFunctor_additive _

private def commonModelIso :
    regularListNativeTopHomologyAt (L := L) I c ≅ (commonModel (L := L) I).homology (c : ℤ) :=
  ((DerivedCategory.Plus.homologyFunctor (Spec (CommRingCat.of (A ⧸ I))).Modules
    (c : ℤ)).mapIso
      ((injectiveResolution L).rightDerivedFunctorPlusIso
        (closedImmersionRightAdjoint (Spec.map (commonQuotientMap I))))).symm ≪≫
    (DerivedCategory.Plus.homologyFunctorFactors
      (A := (Spec (CommRingCat.of (A ⧸ I))).Modules) (n := (c : ℤ))).app
      ((closedImmersionRightAdjoint (Spec.map (commonQuotientMap I))).mapCochainComplexPlus.obj
        (injectiveResolution L).cochainComplexPlus)

omit [HasExt.{w} (ModuleCat.{u} A)] [HasDerivedCategory.{a} (Spec A).Modules] in
include e in
private theorem commonModel_counit_quasiIso (s : List A)
    (hs : RingTheory.Sequence.IsWeaklyRegular A s) (hI : Ideal.ofList s = I) :
    QuasiIso (Complex.tildeGlobalSectionsCounit (CommRingCat.of (A ⧸ I)) (.up ℤ)
      (commonModel (L := L) I)) := by
  subst I
  exact closedImmersionRightAdjointRegularListResolutionTildeCounit_quasiIso
    s hs (injectiveResolution L) e

private def commonExtSection
    [QuasiIso (Complex.tildeGlobalSectionsCounit (CommRingCat.of (A ⧸ I)) (.up ℤ)
      (commonModel (L := L) I))]
    (z : Ext.{w} (ModuleCat.of A (A ⧸ I)) (moduleSpecΓFunctor.obj L) c)
    (U : (Spec (CommRingCat.of (A ⧸ I))).Opens) :
    (regularListNativeTopHomologyAt (L := L) I c).val.obj (op U) :=
  (commonModelIso (L := L) I c).inv.val.app (op U)
    ((Complex.tildeGlobalSectionsHomologyIso (CommRingCat.of (A ⧸ I)) (.up ℤ)
      (commonModel (L := L) I) (c : ℤ)).hom.val.app (op U)
      (tilde.toOpen
        ((((moduleSpecΓFunctor (R := CommRingCat.of (A ⧸ I))).mapHomologicalComplex
          (.up ℤ)).obj (commonModel (L := L) I)).homology (c : ℤ)) U
        ((affineClosedRightAdjointResolutionExtAddEquiv (commonQuotientMap I)
          (injectiveResolution L) c).symm z)))

/-- Only equality transport is used to place the original native class on
the common quotient and in the common degree. -/
def regularListNativeTopClassAt (s : List A)
    (hs : RingTheory.Sequence.IsWeaklyRegular A s)
    (hI : Ideal.ofList s = I) (hc : s.length = c) (r : A)
    (U : (Spec (CommRingCat.of (A ⧸ I))).Opens) :
    (regularListNativeTopHomologyAt (L := L) I c).val.obj (op U) := by
  subst I c
  exact closedImmersionRegularListNativeTopClass s hs e r U

private theorem regularListNativeTopClassAt_eq
    [QuasiIso (Complex.tildeGlobalSectionsCounit (CommRingCat.of (A ⧸ I)) (.up ℤ)
      (commonModel (L := L) I))]
    (s : List A) (hs : RingTheory.Sequence.IsWeaklyRegular A s)
    (hI : Ideal.ofList s = I) (hc : s.length = c) (r : A)
    (U : (Spec (CommRingCat.of (A ⧸ I))).Opens) :
    regularListNativeTopClassAt I c e s hs hI hc r U =
      commonExtSection I c
        ((regularListTopExtClassAt I c s hs hI hc r).comp (Ext.mk₀ e.inv) (Nat.add_zero c)) U := by
  subst I c
  have hm : derivedClosedImmersionRightAdjointRegularListModelHomologyIso
      s (injectiveResolution L) (s.length : ℤ) =
        commonModelIso (L := L) (Ideal.ofList s) s.length := by
    apply Iso.ext
    rw [derivedClosedImmersionRightAdjointRegularListModelHomologyIso_hom]
    rfl
  change closedImmersionRegularListNativeTopClass s hs e r U = _
  rw [closedImmersionRegularListNativeTopClass_eq]
  dsimp only
  rw [closedImmersionRightAdjointRegularListResolutionSectionsExtAddEquiv_eq_affine, hm]
  rfl

/-- The native model, affine counit and tilde section preserve the original
matrix determinant law on the common quotient. -/
theorem regularListNativeTopClassAt_generatorChange
    (s t : List A) (hs : RingTheory.Sequence.IsWeaklyRegular A s)
    (ht : RingTheory.Sequence.IsWeaklyRegular A t)
    (hsI : Ideal.ofList s = I) (htI : Ideal.ofList t = I)
    (hsc : s.length = c) (htc : t.length = c)
    (M : Matrix (Fin s.length) (Fin s.length) A)
    (hM : t = List.ofFn (fun i => ∑ j, M i j * s.get j)) (r : A)
    (U : (Spec (CommRingCat.of (A ⧸ I))).Opens) :
    regularListNativeTopClassAt I c e s hs hsI hsc r U =
      regularListNativeTopClassAt I c e t ht htI htc (M.det * r) U := by
  let := commonModel_counit_quasiIso I e t ht htI
  rw [regularListNativeTopClassAt_eq, regularListNativeTopClassAt_eq,
    regularListTopExtClassAt_generatorChange I c s t hs ht hsI htI hsc htc M hM r]

end NativeClasses
end NativeExt

section NormalDeterminants

variable {R B : CommRingCat.{u}} (α : R ⟶ A) (σ : A ⟶ B)
  (hσ : Function.Surjective σ)

private theorem conormalClass_sum_smul {m : ℕ} (a : Fin m → A)
    (v : Fin m → RingHom.ker σ.hom) :
    relativeConormalAffineClass α σ hσ (∑ j, a j • v j) =
      ∑ j, σ (a j) • relativeConormalAffineClass α σ hσ (v j) := by
  let := α.hom.toAlgebra
  let := (α ≫ σ).hom.toAlgebra
  let := σ.hom.toAlgebra
  change Algebra.Extension.Cotangent.mk (P := relativeConormalAffineExtension α σ hσ)
      (∑ j, a j • v j) =
    ∑ j, (algebraMap A B (a j)) •
      Algebra.Extension.Cotangent.mk (P := relativeConormalAffineExtension α σ hσ) (v j)
  simp only [map_sum, algebraMap_smul]
  apply Finset.sum_congr rfl
  intro j _
  exact (Algebra.Extension.Cotangent.mk (P := relativeConormalAffineExtension α σ hσ)).map_smul
    (a j) (v j)

private theorem basis_det_rowCombination {K : Type u} [CommRing K]
    {V : Type u} [AddCommGroup V] [Module K V] {m : ℕ}
    (b : Module.Basis (Fin m) K V) (M : Matrix (Fin m) (Fin m) K) :
    b.det (fun i => ∑ j, M i j • b j) = M.det := by
  classical
  have h : b.toMatrix (fun i => ∑ j, M i j • b j) = M.transpose := by
    ext i j
    simp [Module.Basis.toMatrix_apply, Finsupp.single_apply]
  rw [Module.Basis.det_apply, h, Matrix.det_transpose]

/-- The determinant in the original conormal basis of the matrix-transformed
ordered kernel vectors is the reduction of the same ambient determinant. -/
theorem relativeConormalAffineBasis_det_generatorRows (s : List A)
    (hs : RingTheory.Sequence.IsWeaklyRegular A s)
    (hker : Ideal.ofList s = RingHom.ker σ.hom)
    (M : Matrix (Fin s.length) (Fin s.length) A) :
    (relativeConormalAffineBasis α σ hσ s hs hker).det
      (fun i => relativeConormalAffineClass α σ hσ
        (∑ j, M i j • (⟨s.get j, hker.le (Ideal.subset_span (s.get_mem j))⟩ :
          RingHom.ker σ.hom))) = σ M.det := by
  simp_rw [conormalClass_sum_smul, ← relativeConormalAffineBasis_apply α σ hσ s hs hker]
  rw [basis_det_rowCombination]
  exact (RingHom.map_det σ.hom M).symm

end NormalDeterminants

private abbrev overlapFreeModule (X : Scheme.{u}) (U : X.Opens) (m : ℕ) :
    Module (X.sheaf.obj.obj (op U))
      ((SheafOfModules.free (R := X.ringCatSheaf) (ULift.{u} (Fin m))).val.obj (op U)) := by
  change Module (X.ringCatSheaf.obj.obj (op U))
    ((SheafOfModules.free (R := X.ringCatSheaf) (ULift.{u} (Fin m))).val.obj (op U))
  infer_instance

private def overlapScalar {B : CommRingCat.{u}} (U : (Spec B).Opens) :
    B →+* Γ(Spec B, U) :=
  ((Scheme.ΓSpecIso B).inv ≫ (Spec B).presheaf.map U.leTop.op).hom

/-- The original structure-ring section of a scalar on the common quotient. -/
def regularListOverlapScalar (I : Ideal A)
    (U : (Spec (CommRingCat.of (A ⧸ I))).Opens) :
    (A ⧸ I) →+* Γ(Spec (CommRingCat.of (A ⧸ I)), U) :=
  ((Scheme.ΓSpecIso (CommRingCat.of (A ⧸ I))).inv ≫
    (Spec (CommRingCat.of (A ⧸ I))).presheaf.map U.leTop.op).hom

private def overlapFrameSemilinear {B : CommRingCat.{u}} (E : ModuleCat.{u} B)
    (m : ℕ) (bE : Module.Basis (Fin m) B E) (U : (Spec B).Opens) :
    letI := overlapFreeModule (Spec B) U m
    E →ₛₗ[overlapScalar U]
      ((SheafOfModules.free (R := (Spec B).ringCatSheaf) (ULift.{u} (Fin m))).val.obj
        (op U)) := by
  letI := overlapFreeModule (Spec B) U m
  let F := SheafOfModules.free (R := (Spec B).ringCatSheaf) (ULift.{u} (Fin m))
  let N := ModuleCat.of ((Spec B).sheaf.obj.obj (op U)) (F.val.obj (op U))
  let eF := tildeBasisIso E (bE.reindex Equiv.ulift.symm)
  have g : E ⟶ (ModuleCat.restrictScalars (overlapScalar U)).obj N := by
    change E ⟶ (modulesSpecToSheaf.obj F).presheaf.obj (op U)
    exact tilde.toOpen E U ≫ (modulesSpecToSheaf.map eF.hom).hom.app (op U)
  exact (ModuleCat.semilinearMapAddEquiv (overlapScalar U) E N).symm g

private theorem overlapFrameSemilinear_basis {B : CommRingCat.{u}} (E : ModuleCat.{u} B)
    (m : ℕ) (bE : Module.Basis (Fin m) B E) (U : (Spec B).Opens) (i : Fin m) :
    letI := overlapFreeModule (Spec B) U m
    overlapFrameSemilinear E m bE U (bE i) =
      (SheafOfModules.freeSection (R := (Spec B).ringCatSheaf) (ULift.up i)).val (op U) := by
  let := overlapFreeModule (Spec B) U m
  change (tildeBasisIso E (bE.reindex Equiv.ulift.symm)).hom.val.app (op U)
    (tilde.toOpen E U (bE i)) = _
  simpa only [Module.Basis.reindex_apply, Equiv.symm_symm, Equiv.ulift_apply, ULift.down_up]
    using tildeBasisIso_hom_toOpen E (bE.reindex Equiv.ulift.symm) (ULift.up i) U

private theorem overlapSemilinearDet {K D V W : Type*} [CommRing K] [CommRing D]
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

private def overlapTopFrame {B : CommRingCat.{u}} (N : (Spec B).Modules)
    (E : ModuleCat.{u} B) (m : ℕ) (bE : Module.Basis (Fin m) B E) (eN : N ≅ tilde E) :
    moduleExteriorPower (Spec B) N m ≅ SheafOfModules.unit (Spec B).ringCatSheaf :=
  (moduleExteriorPowerFunctor (Spec B) m).mapIso
    (eN ≪≫ tildeBasisIso E (bE.reindex Equiv.ulift.symm)) ≪≫
      SheafOfModulesOfCommRing.exteriorTopFreeIso (Spec B).sheaf m

private def overlapWedge {B : CommRingCat.{u}} (N : (Spec B).Modules)
    (E : ModuleCat.{u} B) (m : ℕ) (eN : N ≅ tilde E)
    (U : (Spec B).Opens) (v : Fin m → E) :
    (moduleExteriorPower (Spec B) N m).val.obj (op U) :=
  (SheafOfModulesOfCommRing.exteriorPowerMk (Spec B).sheaf N m).app (op U)
    (fun i => eN.inv.val.app (op U) (tilde.toOpen E U (v i)))

private theorem overlapTopFrame_wedge {B : CommRingCat.{u}} (N : (Spec B).Modules)
    (E : ModuleCat.{u} B) (m : ℕ) (bE : Module.Basis (Fin m) B E) (eN : N ≅ tilde E)
    (U : (Spec B).Opens) (v : Fin m → E) :
    (overlapTopFrame N E m bE eN).hom.val.app (op U)
      (overlapWedge N E m eN U v) = algebraMap B Γ(Spec B, U) (bE.det v) := by
  let := overlapFreeModule (Spec B) U m
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
      overlapFrameSemilinear E m bE U ∘ v := by
    funext i
    have h := congrArg (fun k => k.val.app (op U) (tilde.toOpen E U (v i))) eN.inv_hom_id
    exact congrArg ((tildeBasisIso E (bE.reindex Equiv.ulift.symm)).hom.val.app (op U)) h
  have hf (i : Fin m) : overlapFrameSemilinear E m bE U (bE i) = bF i :=
    (overlapFrameSemilinear_basis E m bE U i).trans
      (SheafOfModulesOfCommRing.freeFinSectionsBasis_apply (Spec B).sheaf m (op U) i).symm
  have hdet := overlapSemilinearDet bE bF (overlapFrameSemilinear E m bE U) hf v
  exact hw.trans (hd.trans ((congrArg bF.det hfamily).trans hdet))

section CommonNormal

variable {R : CommRingCat.{u}} (α : R ⟶ A) (I : Ideal A) (c : ℕ)

/-- The intrinsic normal determinant on the common quotient and degree. -/
abbrev regularListNormalAt :=
  moduleExteriorPower (Spec (CommRingCat.of (A ⧸ I)))
    ((pullback (Spec.map
      (CommRingCat.ofHom (Ideal.Quotient.mk I) : A ⟶ CommRingCat.of (A ⧸ I)))).obj
      (idealModule (Spec.map
        (CommRingCat.ofHom (Ideal.Quotient.mk I) : A ⟶ CommRingCat.of (A ⧸ I))))) c

private def commonConormalBasis (s : List A)
    (hs : RingTheory.Sequence.IsWeaklyRegular A s)
    (hI : Ideal.ofList s = I) (hc : s.length = c) :
    Module.Basis (Fin c) (A ⧸ I)
      (relativeConormalAffineModule α (commonQuotientMap I) Ideal.Quotient.mk_surjective) :=
  (relativeConormalAffineBasis α (commonQuotientMap I) Ideal.Quotient.mk_surjective s hs
    (hI.trans Ideal.mk_ker.symm)).reindex (finCongr hc)

/-- The original ordered normal section transported to the common normal determinant. -/
def regularListNormalSectionAt (s : List A)
    (hs : RingTheory.Sequence.IsWeaklyRegular A s)
    (hI : Ideal.ofList s = I) (hc : s.length = c)
    (U : (Spec (CommRingCat.of (A ⧸ I))).Opens) :
    (regularListNormalAt I c).val.obj (op U) := by
  subst I c
  exact closedImmersionRegularListNormalSection α s hs U

/-- The original normal frame on the common determinant. -/
def regularListNormalFrameAt (s : List A)
    (hs : RingTheory.Sequence.IsWeaklyRegular A s)
    (hI : Ideal.ofList s = I) (hc : s.length = c) :
    regularListNormalAt I c ≅ SheafOfModules.unit (Spec (CommRingCat.of (A ⧸ I))).ringCatSheaf := by
  subst I c
  exact closedImmersionRegularListNormalFrameIso α s hs

private theorem commonConormalBasis_generatorRows (s t : List A)
    (hs : RingTheory.Sequence.IsWeaklyRegular A s)
    (ht : RingTheory.Sequence.IsWeaklyRegular A t)
    (hsI : Ideal.ofList s = I) (htI : Ideal.ofList t = I)
    (hsc : s.length = c) (htc : t.length = c)
    (M : Matrix (Fin s.length) (Fin s.length) A)
    (hM : t = List.ofFn (fun i => ∑ j, M i j * s.get j)) :
    (commonConormalBasis α I c s hs hsI hsc).det
      (commonConormalBasis α I c t ht htI htc) = Ideal.Quotient.mk I M.det := by
  cases hsc
  let q := commonQuotientMap I
  let hk : Ideal.ofList s = RingHom.ker q.hom := hsI.trans Ideal.mk_ker.symm
  have htget (i : Fin s.length) : t.get ((finCongr htc).symm i) =
      ∑ j, M i j * s.get j := by
    subst t
    simp
  have hb (i : Fin s.length) : commonConormalBasis α I s.length t ht htI htc i =
      relativeConormalAffineClass α q Ideal.Quotient.mk_surjective
        (∑ j, M i j • (⟨s.get j, hk.le (Ideal.subset_span (s.get_mem j))⟩ :
          RingHom.ker q.hom)) := by
    rw [commonConormalBasis, Module.Basis.reindex_apply, relativeConormalAffineBasis_apply]
    apply congrArg (relativeConormalAffineClass α q Ideal.Quotient.mk_surjective)
    apply Subtype.ext
    simp only [htget, Submodule.coe_sum, SetLike.val_smul, smul_eq_mul]
  have hbs : commonConormalBasis α I s.length s hs hsI rfl =
      relativeConormalAffineBasis α q Ideal.Quotient.mk_surjective s hs hk := by
    simp [commonConormalBasis, q]
  rw [hbs]
  change (relativeConormalAffineBasis α q Ideal.Quotient.mk_surjective s hs hk).det
    (fun i => commonConormalBasis α I s.length t ht htI htc i) = _
  simp_rw [hb]
  exact relativeConormalAffineBasis_det_generatorRows α q Ideal.Quotient.mk_surjective s hs hk M

private theorem regularListNormalSectionAt_wedge (s : List A)
    (hs : RingTheory.Sequence.IsWeaklyRegular A s)
    (hI : Ideal.ofList s = I) (hc : s.length = c)
    (U : (Spec (CommRingCat.of (A ⧸ I))).Opens) :
    regularListNormalSectionAt α I c s hs hI hc U =
      overlapWedge ((pullback (Spec.map (commonQuotientMap I))).obj
        (idealModule (Spec.map (commonQuotientMap I))))
        (relativeConormalAffineModule α (commonQuotientMap I) Ideal.Quotient.mk_surjective) c
        (relativeConormalAffineIdealPullbackIso α (commonQuotientMap I)
          Ideal.Quotient.mk_surjective) U (commonConormalBasis α I c s hs hI hc) := by
  subst I c
  simp only [regularListNormalSectionAt, overlapWedge, commonConormalBasis,
    finCongr_refl, Module.Basis.reindex_refl]
  rw [closedImmersionRegularListNormalSection_eq]
  congr 1
  funext j
  rw [relativeConormalAffineBasis_apply]

private theorem regularListNormalFrameAt_eq (s : List A)
    (hs : RingTheory.Sequence.IsWeaklyRegular A s)
    (hI : Ideal.ofList s = I) (hc : s.length = c) :
    regularListNormalFrameAt α I c s hs hI hc =
      overlapTopFrame ((pullback (Spec.map (commonQuotientMap I))).obj
        (idealModule (Spec.map (commonQuotientMap I))))
        (relativeConormalAffineModule α (commonQuotientMap I) Ideal.Quotient.mk_surjective) c
        (commonConormalBasis α I c s hs hI hc)
        (relativeConormalAffineIdealPullbackIso α (commonQuotientMap I)
          Ideal.Quotient.mk_surjective) := by
  subst I c
  rw [regularListNormalFrameAt, closedImmersionRegularListNormalFrameIso_eq]
  simp [overlapTopFrame, commonConormalBasis, relativeConormalAffineGeometricFreeIso,
    relativeConormalAffineFreeIso, commonQuotientMap]

private theorem regularListNormalFrameAt_section (s : List A)
    (hs : RingTheory.Sequence.IsWeaklyRegular A s)
    (hI : Ideal.ofList s = I) (hc : s.length = c)
    (U : (Spec (CommRingCat.of (A ⧸ I))).Opens) :
    (regularListNormalFrameAt α I c s hs hI hc).hom.val.app (op U)
      (regularListNormalSectionAt α I c s hs hI hc U) =
        (1 : Γ(Spec (CommRingCat.of (A ⧸ I)), U)) := by
  subst I c
  exact closedImmersionRegularListNormalFrameIso_normalSection α s hs U

private theorem overlapIsoSection_injective {X : Scheme.{u}} {N P : X.Modules}
    (e : N ≅ P) (U : X.Opens) : Function.Injective (e.hom.val.app (op U)) := by
  intro x y h
  have hx := congrArg (fun k => k.val.app (op U) x) e.hom_inv_id
  have hy := congrArg (fun k => k.val.app (op U) y) e.hom_inv_id
  exact hx.symm.trans ((congrArg (e.inv.val.app (op U)) h).trans hy)

/-- The original ordered normal wedge changes by the reduction of the same
matrix determinant, on every open of the common quotient. -/
theorem regularListNormalSectionAt_generatorChange (s t : List A)
    (hs : RingTheory.Sequence.IsWeaklyRegular A s)
    (ht : RingTheory.Sequence.IsWeaklyRegular A t)
    (hsI : Ideal.ofList s = I) (htI : Ideal.ofList t = I)
    (hsc : s.length = c) (htc : t.length = c)
    (M : Matrix (Fin s.length) (Fin s.length) A)
    (hM : t = List.ofFn (fun i => ∑ j, M i j * s.get j))
    (U : (Spec (CommRingCat.of (A ⧸ I))).Opens) :
    regularListNormalSectionAt α I c t ht htI htc U =
      regularListOverlapScalar I U (Ideal.Quotient.mk I M.det) •
        regularListNormalSectionAt α I c s hs hsI hsc U := by
  let eS := regularListNormalFrameAt α I c s hs hsI hsc
  apply overlapIsoSection_injective eS U
  have hleft : eS.hom.val.app (op U)
      (regularListNormalSectionAt α I c t ht htI htc U) =
      regularListOverlapScalar I U (Ideal.Quotient.mk I M.det) := by
    dsimp only [eS]
    rw [regularListNormalFrameAt_eq, regularListNormalSectionAt_wedge,
      overlapTopFrame_wedge,
      commonConormalBasis_generatorRows α I c s t hs ht hsI htI hsc htc M hM]
    rfl
  rw [hleft]
  have hright := (eS.hom.val.app (op U)).hom.map_smul
    (regularListOverlapScalar I U (Ideal.Quotient.mk I M.det))
    (regularListNormalSectionAt α I c s hs hsI hsc U)
  rw [regularListNormalFrameAt_section] at hright
  simpa only [smul_eq_mul, mul_one] using hright.symm

/-- The native normal dual section on the common determinant. -/
def regularListNormalDualSectionAt (s : List A)
    (hs : RingTheory.Sequence.IsWeaklyRegular A s)
    (hI : Ideal.ofList s = I) (hc : s.length = c)
    (U : (Spec (CommRingCat.of (A ⧸ I))).Opens) :
    (dualSheaf (Spec (CommRingCat.of (A ⧸ I))) (regularListNormalAt I c)).val.obj (op U) := by
  subst I c
  exact closedImmersionRegularListNormalDualSection α s hs U

private def normalDualFrameAt (s : List A)
    (hs : RingTheory.Sequence.IsWeaklyRegular A s)
    (hI : Ideal.ofList s = I) (hc : s.length = c) :
    dualSheaf (Spec (CommRingCat.of (A ⧸ I))) (regularListNormalAt I c) ≅
      SheafOfModules.unit (Spec (CommRingCat.of (A ⧸ I))).ringCatSheaf := by
  subst I c
  exact closedImmersionRegularListNormalDualFrameIso α s hs

private theorem normalDualFrameAt_section (s : List A)
    (hs : RingTheory.Sequence.IsWeaklyRegular A s)
    (hI : Ideal.ofList s = I) (hc : s.length = c)
    (U : (Spec (CommRingCat.of (A ⧸ I))).Opens) :
    (normalDualFrameAt α I c s hs hI hc).hom.val.app (op U)
      (regularListNormalDualSectionAt α I c s hs hI hc U) =
        (1 : Γ(Spec (CommRingCat.of (A ⧸ I)), U)) := by
  subst I c
  change (closedImmersionRegularListNormalDualFrameIso α s hs).hom.val.app (op U)
    (closedImmersionRegularListNormalDualSection α s hs U) = _
  rw [closedImmersionRegularListNormalDualSection_eq]
  exact congrArg (fun k => k.val.app (op U) (1 : Γ(Spec (regularListQuotientRing s), U)))
    (closedImmersionRegularListNormalDualFrameIso α s hs).inv_hom_id

private theorem normalDualFrameAt_evaluation (s : List A)
    (hs : RingTheory.Sequence.IsWeaklyRegular A s)
    (hI : Ideal.ofList s = I) (hc : s.length = c)
    (U : (Spec (CommRingCat.of (A ⧸ I))).Opens)
    (ell : (dualSheaf (Spec (CommRingCat.of (A ⧸ I)))
      (regularListNormalAt I c)).val.obj (op U)) :
    (normalDualFrameAt α I c s hs hI hc).hom.val.app (op U) ell =
      ell.val.app (op (Over.mk (𝟙 U))) (regularListNormalSectionAt α I c s hs hI hc U) := by
  subst I c
  change (closedImmersionRegularListNormalDualFrameIso α s hs).hom.val.app (op U) ell = _
  rw [closedImmersionRegularListNormalDualFrameIso_hom_evaluation]
  congr 1
  let eS := closedImmersionRegularListNormalFrameIso α s hs
  apply overlapIsoSection_injective eS U
  have h := congrArg (fun k => k.val.app (op U)
    (1 : Γ(Spec (regularListQuotientRing s), U))) eS.inv_hom_id
  exact h.trans (closedImmersionRegularListNormalFrameIso_normalSection α s hs U).symm

private theorem normalDualSectionAt_evaluation (s : List A)
    (hs : RingTheory.Sequence.IsWeaklyRegular A s)
    (hI : Ideal.ofList s = I) (hc : s.length = c)
    (U : (Spec (CommRingCat.of (A ⧸ I))).Opens) :
    (regularListNormalDualSectionAt α I c s hs hI hc U).val.app (op (Over.mk (𝟙 U)))
      (regularListNormalSectionAt α I c s hs hI hc U) =
        (1 : Γ(Spec (CommRingCat.of (A ⧸ I)), U)) := by
  exact (normalDualFrameAt_evaluation α I c s hs hI hc U
    (regularListNormalDualSectionAt α I c s hs hI hc U)).symm.trans
      (normalDualFrameAt_section α I c s hs hI hc U)

/-- The actual dual normal frames absorb the same generator determinant by
evaluation, without dividing by that determinant in the ambient ring. -/
theorem regularListNormalDualSectionAt_generatorChange (s t : List A)
    (hs : RingTheory.Sequence.IsWeaklyRegular A s)
    (ht : RingTheory.Sequence.IsWeaklyRegular A t)
    (hsI : Ideal.ofList s = I) (htI : Ideal.ofList t = I)
    (hsc : s.length = c) (htc : t.length = c)
    (M : Matrix (Fin s.length) (Fin s.length) A)
    (hM : t = List.ofFn (fun i => ∑ j, M i j * s.get j))
    (U : (Spec (CommRingCat.of (A ⧸ I))).Opens) :
    regularListNormalDualSectionAt α I c s hs hsI hsc U =
      regularListOverlapScalar I U (Ideal.Quotient.mk I M.det) •
        regularListNormalDualSectionAt α I c t ht htI htc U := by
  let eD := normalDualFrameAt α I c s hs hsI hsc
  let aU := regularListOverlapScalar I U (Ideal.Quotient.mk I M.det)
  let ell := regularListNormalDualSectionAt α I c t ht htI htc U
  let v := regularListNormalSectionAt α I c s hs hsI hsc U
  apply overlapIsoSection_injective eD U
  rw [normalDualFrameAt_section]
  have hmap := (eD.hom.val.app (op U)).hom.map_smul aU ell
  change eD.hom.val.app (op U) (aU • ell) =
    aU * (show Γ(Spec (CommRingCat.of (A ⧸ I)), U) from eD.hom.val.app (op U) ell) at hmap
  have hframe := normalDualFrameAt_evaluation α I c s hs hsI hsc U ell
  rw [hframe] at hmap
  have heval := normalDualSectionAt_evaluation α I c t ht htI htc U
  rw [regularListNormalSectionAt_generatorChange α I c s t hs ht hsI htI hsc htc M hM U] at heval
  have hlin := ell.property (op (Over.mk (𝟙 U))) aU v
  change ell.val.app (op (Over.mk (𝟙 U))) (aU • v) =
    aU * (show Γ(Spec (CommRingCat.of (A ⧸ I)), U) from
      ell.val.app (op (Over.mk (𝟙 U))) v) at hlin
  change ell.val.app (op (Over.mk (𝟙 U))) (aU • v) =
    (1 : Γ(Spec (CommRingCat.of (A ⧸ I)), U)) at heval
  exact (hmap.trans (hlin.symm.trans heval)).symm

end CommonNormal

private def commonNormalBundle {R : CommRingCat.{u}} (α : R ⟶ A) (I : Ideal A) (c : ℕ)
    (s : List A) (hs : RingTheory.Sequence.IsWeaklyRegular A s)
    (hI : Ideal.ofList s = I) (hc : s.length = c) :
    LineBundle (Spec (CommRingCat.of (A ⧸ I))) := by
  refine ⟨regularListNormalAt I c, ?_⟩
  subst I c
  exact (closedImmersionRegularListNormalLineBundle α s hs).property

section CommonPurity

variable {R : CommRingCat.{u}} (α : R ⟶ A) (I : Ideal A) (c : ℕ)
  {L : (Spec A).Modules} [L.IsQuasicoherent]
  (e : moduleSpecΓFunctor.obj L ≅ ModuleCat.of A A)

private def commonCoefficientFrame :
    (pullback (Spec.map (commonQuotientMap I))).obj L ≅
      SheafOfModules.unit (Spec (CommRingCat.of (A ⧸ I))).ringCatSheaf :=
  (pullback (Spec.map (commonQuotientMap I))).mapIso (asIso L.fromTildeΓ).symm ≪≫
    (tildePullbackIso (commonQuotientMap I)).app (moduleSpecΓFunctor.obj L) ≪≫
    (tilde.functor (CommRingCat.of (A ⧸ I))).mapIso
      ((ModuleCat.extendScalars (commonQuotientMap I).hom).mapIso e ≪≫
        ModuleCat.extendScalarsAlgebraObjIso A (CommRingCat.of (A ⧸ I)) (ModuleCat.of A A) ≪≫
        (TensorProduct.AlgebraTensorModule.rid A (CommRingCat.of (A ⧸ I))
          (CommRingCat.of (A ⧸ I))).toModuleIso) ≪≫ tildeSelf

private def commonCoefficientSection (r : A ⧸ I)
    (U : (Spec (CommRingCat.of (A ⧸ I))).Opens) :
    ((pullback (Spec.map (commonQuotientMap I))).obj L).val.obj (op U) :=
  (commonCoefficientFrame I e).inv.val.app (op U)
    (tilde.toOpen (ModuleCat.of (CommRingCat.of (A ⧸ I)) (CommRingCat.of (A ⧸ I))) U r)

private theorem coefficientSection_eq_common (s : List A) (r : A ⧸ Ideal.ofList s)
    (U : (Spec (regularListQuotientRing s)).Opens) :
    closedImmersionRegularListCoefficientSection s e r U =
      commonCoefficientSection (Ideal.ofList s) e r U := by
  rw [closedImmersionRegularListCoefficientSection_eq]
  rfl

private theorem overlapTildeSelf_scalar {B : CommRingCat.{u}} (U : (Spec B).Opens) (r : B) :
    tilde.toOpen (ModuleCat.of B B) U r = overlapScalar U r := by
  have h := (tilde.toOpen (ModuleCat.of B B) U).hom.map_smul r (1 : B)
  change tilde.toOpen (ModuleCat.of B B) U (r * 1) =
    overlapScalar U r * (show Γ(Spec B, U) from tilde.toOpen (ModuleCat.of B B) U (1 : B)) at h
  rw [mul_one] at h
  exact h.trans ((congrArg (fun z : Γ(Spec B, U) => overlapScalar U r * z)
    (tilde_toOpen_self_one (R := B) U)).trans (mul_one _))

private theorem commonCoefficientSection_mul (r z : A ⧸ I)
    (U : (Spec (CommRingCat.of (A ⧸ I))).Opens) :
    commonCoefficientSection I e (r * z) U =
      regularListOverlapScalar I U r • commonCoefficientSection I e z U := by
  dsimp only [commonCoefficientSection]
  rw [overlapTildeSelf_scalar, overlapTildeSelf_scalar, map_mul]
  exact (commonCoefficientFrame I e).inv.val.app (op U) |>.hom.map_smul
    (regularListOverlapScalar I U r) (regularListOverlapScalar I U z)

/-- The intrinsic inverse-normal/coefficient sheaf on the common quotient. -/
abbrev regularListInverseNormalAt :=
  tensorSheaf (Spec (CommRingCat.of (A ⧸ I)))
    (dualSheaf (Spec (CommRingCat.of (A ⧸ I))) (regularListNormalAt I c))
    ((pullback (Spec.map
      (CommRingCat.ofHom (Ideal.Quotient.mk I) : A ⟶ CommRingCat.of (A ⧸ I)))).obj L)

variable [HasExt.{w} (ModuleCat.{u} A)]
  [HasDerivedCategory.{a} (Spec A).Modules]
  [HasDerivedCategory.{b} (Spec (CommRingCat.of (A ⧸ I))).Modules]

/-- The original conormal purity arrow transported through ideal and degree equalities. -/
def regularListConormalMapAt (s : List A)
    (hs : RingTheory.Sequence.IsWeaklyRegular A s)
    (hI : Ideal.ofList s = I) (hc : s.length = c) :
    regularListNativeTopHomologyAt (L := L) I c ⟶ regularListInverseNormalAt (L := L) I c := by
  subst I c
  exact (derivedClosedImmersionRightAdjointRegularListConormalTopHomologyIso α s hs e).hom

private theorem regularListNativeTopClassAt_hom_ext (s : List A)
    (hs : RingTheory.Sequence.IsWeaklyRegular A s)
    (hI : Ideal.ofList s = I) (hc : s.length = c)
    {N : (Spec (CommRingCat.of (A ⧸ I))).Modules}
    {f g : regularListNativeTopHomologyAt (L := L) I c ⟶ N}
    (hfg : ∀ U : (Spec (CommRingCat.of (A ⧸ I))).Opens,
      f.val.app (op U) (regularListNativeTopClassAt I c e s hs hI hc 1 U) =
        g.val.app (op U) (regularListNativeTopClassAt I c e s hs hI hc 1 U)) : f = g := by
  subst I c
  exact closedImmersionRegularListNativeTopClass_hom_ext s hs e hfg

private theorem regularListConormalMapAt_class (s : List A)
    (hs : RingTheory.Sequence.IsWeaklyRegular A s)
    (hI : Ideal.ofList s = I) (hc : s.length = c) (r : A)
    (U : (Spec (CommRingCat.of (A ⧸ I))).Opens) :
    (regularListConormalMapAt α I c e s hs hI hc).val.app (op U)
      (regularListNativeTopClassAt I c e s hs hI hc r U) =
      moduleTensorSection (Spec (CommRingCat.of (A ⧸ I)))
        (dualSheaf (Spec (CommRingCat.of (A ⧸ I))) (regularListNormalAt I c))
        ((pullback (Spec.map (commonQuotientMap I))).obj L) U
        (regularListNormalDualSectionAt α I c s hs hI hc U)
        (commonCoefficientSection I e (Ideal.Quotient.mk I r) U) := by
  subst I c
  dsimp only [regularListConormalMapAt, regularListNativeTopClassAt,
    regularListNormalDualSectionAt]
  rw [← coefficientSection_eq_common, closedImmersionRegularListNativeTopClass_eq]
  exact derivedClosedImmersionRightAdjointRegularListConormalTopHomologyIso_class α s hs e r U

private theorem overlapTensor_balance {X : Scheme.{u}} (N P : X.Modules) (U : X.Opens)
    (a : Γ(X, U)) (v : N.val.obj (op U)) (z : P.val.obj (op U)) :
    moduleTensorSection X N P U (a • v) z = moduleTensorSection X N P U v (a • z) := by
  unfold moduleTensorSection SheafOfModulesOfCommRing.tensorSection
  exact congrArg
    (((SheafOfModulesOfCommRing.associatedSheafUnit X.sheaf).app
      (((SheafOfModulesOfCommRing.toPresheaf X.sheaf).obj N) ⊗
        ((SheafOfModulesOfCommRing.toPresheaf X.sheaf).obj P))).app (op U))
    (TensorProduct.smul_tmul (R := X.sheaf.obj.obj (op U))
      (R' := X.sheaf.obj.obj (op U)) (show X.sheaf.obj.obj (op U) from a) v z)

/-- Different weakly regular generators give the same actual native inverse-normal
purity map, with the original quotient, resolution, coefficient frame and conormal sheaf. -/
theorem regularListConormalMapAt_generatorChange (s t : List A)
    (hs : RingTheory.Sequence.IsWeaklyRegular A s)
    (ht : RingTheory.Sequence.IsWeaklyRegular A t)
    (hsI : Ideal.ofList s = I) (htI : Ideal.ofList t = I)
    (hsc : s.length = c) (htc : t.length = c)
    (M : Matrix (Fin s.length) (Fin s.length) A)
    (hM : t = List.ofFn (fun i => ∑ j, M i j * s.get j)) :
    regularListConormalMapAt α I c e s hs hsI hsc =
      regularListConormalMapAt α I c e t ht htI htc := by
  apply regularListNativeTopClassAt_hom_ext I c e s hs hsI hsc
  intro U
  rw [regularListConormalMapAt_class,
    regularListNativeTopClassAt_generatorChange I c e s t hs ht hsI htI hsc htc M hM 1 U,
    regularListConormalMapAt_class, mul_one, map_one]
  rw [regularListNormalDualSectionAt_generatorChange α I c s t hs ht hsI htI hsc htc M hM U]
  have hcoef := commonCoefficientSection_mul I e (Ideal.Quotient.mk I M.det) 1 U
  rw [mul_one] at hcoef
  rw [hcoef]
  exact overlapTensor_balance _ _ U _ _ _

variable {Q : (Spec (CommRingCat.of (A ⧸ I))).Modules}
  (Δ : tensorSheaf (Spec (CommRingCat.of (A ⧸ I))) (regularListNormalAt I c) Q ≅
    (pullback (Spec.map
      (CommRingCat.ofHom (Ideal.Quotient.mk I) : A ⟶ CommRingCat.of (A ⧸ I)))).obj L)

/-- The actual canonical homology arrow with a common intrinsic determinant. -/
def regularListCanonicalMapAt (s : List A)
    (hs : RingTheory.Sequence.IsWeaklyRegular A s)
    (hI : Ideal.ofList s = I) (hc : s.length = c) :
    regularListNativeTopHomologyAt (L := L) I c ⟶ Q := by
  subst I c
  exact (derivedClosedImmersionRegularListCanonicalTopHomologyIso α s hs e Δ).hom

private def commonContraction (s : List A)
    (hs : RingTheory.Sequence.IsWeaklyRegular A s)
    (hI : Ideal.ofList s = I) (hc : s.length = c) :
    regularListInverseNormalAt (L := L) I c ≅ Q :=
  normalDeterminantContractionIso (commonNormalBundle α I c s hs hI hc)
    (regularListNormalFrameAt α I c s hs hI hc)
    (normalDualFrameAt α I c s hs hI hc) Δ

private theorem regularListCanonicalMapAt_eq (s : List A)
    (hs : RingTheory.Sequence.IsWeaklyRegular A s)
    (hI : Ideal.ofList s = I) (hc : s.length = c) :
    regularListCanonicalMapAt α I c e Δ s hs hI hc =
      regularListConormalMapAt α I c e s hs hI hc ≫
        (commonContraction α I c Δ s hs hI hc).hom := by
  subst I c
  change (derivedClosedImmersionRegularListCanonicalTopHomologyIso α s hs e Δ).hom = _
  rw [derivedClosedImmersionRegularListCanonicalTopHomologyIso_hom]
  rfl

omit [L.IsQuasicoherent] [HasExt.{w} (ModuleCat.{u} A)]
  [HasDerivedCategory.{a} (Spec A).Modules]
  [HasDerivedCategory.{b} (Spec (CommRingCat.of (A ⧸ I))).Modules] in
private theorem commonContraction_independent (s t : List A)
    (hs : RingTheory.Sequence.IsWeaklyRegular A s)
    (ht : RingTheory.Sequence.IsWeaklyRegular A t)
    (hsI : Ideal.ofList s = I) (htI : Ideal.ofList t = I)
    (hsc : s.length = c) (htc : t.length = c) :
    commonContraction α I c Δ s hs hsI hsc = commonContraction α I c Δ t ht htI htc := by
  change normalDeterminantContractionIso (commonNormalBundle α I c s hs hsI hsc)
      (regularListNormalFrameAt α I c s hs hsI hsc)
      (normalDualFrameAt α I c s hs hsI hsc) Δ =
    normalDeterminantContractionIso (commonNormalBundle α I c s hs hsI hsc)
      (regularListNormalFrameAt α I c t ht htI htc)
      (normalDualFrameAt α I c t ht htI htc) Δ
  exact normalDeterminantContractionIso_independent_frames _ _ _ _ _ _

/-- The original contracted canonical arrows agree for a common determinant;
the proof uses the actual class and dual-normal determinant cancellation. -/
theorem regularListCanonicalMapAt_generatorChange (s t : List A)
    (hs : RingTheory.Sequence.IsWeaklyRegular A s)
    (ht : RingTheory.Sequence.IsWeaklyRegular A t)
    (hsI : Ideal.ofList s = I) (htI : Ideal.ofList t = I)
    (hsc : s.length = c) (htc : t.length = c)
    (M : Matrix (Fin s.length) (Fin s.length) A)
    (hM : t = List.ofFn (fun i => ∑ j, M i j * s.get j)) :
    regularListCanonicalMapAt α I c e Δ s hs hsI hsc =
      regularListCanonicalMapAt α I c e Δ t ht htI htc := by
  rw [regularListCanonicalMapAt_eq, regularListCanonicalMapAt_eq,
    regularListConormalMapAt_generatorChange α I c e s t hs ht hsI htI hsc htc M hM,
    commonContraction_independent α I c Δ s t hs ht hsI htI hsc htc]

end CommonPurity

private def overlapTensorFrame {X : Scheme.{u}} {N P : X.Modules}
    (eN : N ≅ SheafOfModules.unit X.ringCatSheaf)
    (eP : P ≅ SheafOfModules.unit X.ringCatSheaf) :
    tensorSheaf X N P ≅ SheafOfModules.unit X.ringCatSheaf :=
  ((SheafOfModulesOfCommRing.tensorFunctor X.sheaf).mapIso eN).app P ≪≫
    (SheafOfModulesOfCommRing.tensorLeftUnitIso X.sheaf).app P ≪≫ eP

private theorem overlapTensorFrame_section {X : Scheme.{u}} {N P : X.Modules}
    (eN : N ≅ SheafOfModules.unit X.ringCatSheaf)
    (eP : P ≅ SheafOfModules.unit X.ringCatSheaf)
    (U : X.Opens) (v : N.val.obj (op U)) (z : P.val.obj (op U)) :
    (overlapTensorFrame eN eP).hom.val.app (op U) (moduleTensorSection X N P U v z) =
      (show Γ(X, U) from eN.hom.val.app (op U) v) *
        (show Γ(X, U) from eP.hom.val.app (op U) z) := by
  change eP.hom.val.app (op U)
    (((tensorToUnit eN.hom).app P).val.app (op U) (moduleTensorSection X N P U v z)) = _
  exact (congrArg (eP.hom.val.app (op U)) (tensorToUnit_section eN.hom P U v z)).trans
    ((eP.hom.val.app (op U)).hom.map_smul
      (show Γ(X, U) from eN.hom.val.app (op U) v) z)

private theorem overlapHomExtUnitFrame {X : Scheme.{u}} {N P : X.Modules}
    (eN : N ≅ SheafOfModules.unit X.ringCatSheaf)
    (v : ∀ U : X.Opens, N.val.obj (op U))
    (hv : ∀ U, eN.hom.val.app (op U) (v U) = (1 : Γ(X, U)))
    (f g : N ⟶ P) (hfg : ∀ U, f.val.app (op U) (v U) = g.val.app (op U) (v U)) :
    f = g := by
  apply (cancel_epi eN.inv).mp
  apply (SheafOfModules.unitHomEquiv P).injective
  apply PresheafOfModules.sections_ext
  intro U
  have hi := congrArg (fun k => k.val.app U (1 : X.ringCatSheaf.obj.obj U)) eN.inv_hom_id
  have hv' : eN.inv.val.app U (1 : X.ringCatSheaf.obj.obj U) = v U.unop :=
    overlapIsoSection_injective eN U.unop (hi.trans (hv U.unop).symm)
  change f.val.app U (eN.inv.val.app U (1 : X.ringCatSheaf.obj.obj U)) =
    g.val.app U (eN.inv.val.app U (1 : X.ringCatSheaf.obj.obj U))
  rw [hv']
  exact hfg U.unop

section IntrinsicDeterminant

variable {R : CommRingCat.{u}} (α : R ⟶ A) (I : Ideal A) (c d : ℕ)

private abbrev commonNormalBase :=
  (pullback (Spec.map (commonQuotientMap I))).obj (idealModule (Spec.map (commonQuotientMap I)))

private abbrev commonTangentBase := relativeDifferentialSheaf (Spec.map (α ≫ commonQuotientMap I))

private abbrev commonMiddleBase :=
  (pullback (Spec.map (commonQuotientMap I))).obj (relativeDifferentialSheaf (Spec.map α))

/-- The original tangent determinant on the fixed quotient. -/
abbrev regularListTangentTopAt :=
  moduleExteriorPower (Spec (CommRingCat.of (A ⧸ I)))
    (relativeDifferentialSheaf (Spec.map
      (α ≫ (CommRingCat.ofHom (Ideal.Quotient.mk I) : A ⟶ CommRingCat.of (A ⧸ I))))) d

/-- The original top exterior of the pulled-back ambient differential sheaf. -/
abbrev regularListMiddleTopAt (n : ℕ) :=
  moduleExteriorPower (Spec (CommRingCat.of (A ⧸ I)))
    ((pullback (Spec.map
      (CommRingCat.ofHom (Ideal.Quotient.mk I) : A ⟶ CommRingCat.of (A ⧸ I)))).obj
        (relativeDifferentialSheaf (Spec.map α))) n

variable (hA : α.hom.FormallySmooth)
  (hB : (α ≫ (CommRingCat.ofHom (Ideal.Quotient.mk I) :
    A ⟶ CommRingCat.of (A ⧸ I))).hom.FormallySmooth)
  (bQ : Module.Basis (Fin d) (CommRingCat.of (A ⧸ I))
    (CommRingCat.KaehlerDifferential (α ≫ (CommRingCat.ofHom (Ideal.Quotient.mk I) :
      A ⟶ CommRingCat.of (A ⧸ I)))))

/-- The actual normal-first conormal determinant on a common ideal and degree. -/
def regularListConormalDeterminantAt (s : List A)
    (hs : RingTheory.Sequence.IsWeaklyRegular A s)
    (hI : Ideal.ofList s = I) (hc : s.length = c) :
    tensorSheaf (Spec (CommRingCat.of (A ⧸ I))) (regularListNormalAt I c)
      (regularListTangentTopAt α I d) ≅ regularListMiddleTopAt α I (c + d) := by
  subst I c
  exact relativeConormalAffineDeterminantIso α (regularListQuotientMap s)
    Ideal.Quotient.mk_surjective s hs Ideal.mk_ker.symm hA hB bQ

private theorem regularListConormalDeterminantAt_wedge (s : List A)
    (hs : RingTheory.Sequence.IsWeaklyRegular A s)
    (hI : Ideal.ofList s = I) (hc : s.length = c)
    (U : (Spec (CommRingCat.of (A ⧸ I))).Opens)
    (v : Fin c → relativeConormalAffineModule α (commonQuotientMap I) Ideal.Quotient.mk_surjective)
    (w : Fin d → (ModuleCat.extendScalars (commonQuotientMap I).hom).obj
      (CommRingCat.KaehlerDifferential α)) :
    (regularListConormalDeterminantAt α I c d hA hB bQ s hs hI hc).hom.val.app (op U)
      (moduleTensorSection _ (regularListNormalAt I c) (regularListTangentTopAt α I d) U
        (overlapWedge (commonNormalBase I)
          (relativeConormalAffineModule α (commonQuotientMap I) Ideal.Quotient.mk_surjective) c
          (relativeConormalAffineIdealPullbackIso α (commonQuotientMap I)
            Ideal.Quotient.mk_surjective) U v)
        (overlapWedge (commonTangentBase α I)
          (CommRingCat.KaehlerDifferential (α ≫ commonQuotientMap I)) d
          (relativeDifferentialAffineIso (α ≫ commonQuotientMap I)) U
          (fun j => relativeConormalAffineLinearG α (commonQuotientMap I)
            Ideal.Quotient.mk_surjective (w j)))) =
      overlapWedge (commonMiddleBase α I)
        ((ModuleCat.extendScalars (commonQuotientMap I).hom).obj
          (CommRingCat.KaehlerDifferential α)) (c + d)
        (relativeConormalAffineMiddleIso α (commonQuotientMap I)) U
        (Fin.append (fun j => relativeConormalAffineLinearF α (commonQuotientMap I)
          Ideal.Quotient.mk_surjective (v j)) w) := by
  subst I c
  exact relativeConormalAffineDeterminantIso_wedge α (regularListQuotientMap s)
    Ideal.Quotient.mk_surjective s hs Ideal.mk_ker.symm hA hB bQ U v w

/-- The actual conormal determinant is independent of both displayed regular
generators and the displayed tangent basis, on the same quotient and degree. -/
theorem regularListConormalDeterminantAt_independent
    (bQ' : Module.Basis (Fin d) (CommRingCat.of (A ⧸ I))
      (CommRingCat.KaehlerDifferential (α ≫ (CommRingCat.ofHom (Ideal.Quotient.mk I) :
        A ⟶ CommRingCat.of (A ⧸ I)))))
    (s t : List A) (hs : RingTheory.Sequence.IsWeaklyRegular A s)
    (ht : RingTheory.Sequence.IsWeaklyRegular A t)
    (hsI : Ideal.ofList s = I) (htI : Ideal.ofList t = I)
    (hsc : s.length = c) (htc : t.length = c) :
    regularListConormalDeterminantAt α I c d hA hB bQ s hs hsI hsc =
      regularListConormalDeterminantAt α I c d hA hB bQ' t ht htI htc := by
  let C := relativeConormalAffineModule α (commonQuotientMap I) Ideal.Quotient.mk_surjective
  let T := CommRingCat.KaehlerDifferential (α ≫ commonQuotientMap I)
  let eC0 := relativeConormalAffineIdealPullbackIso α (commonQuotientMap I)
    Ideal.Quotient.mk_surjective
  let eQ0 := relativeDifferentialAffineIso (α ≫ commonQuotientMap I)
  let bC := commonConormalBasis α I c s hs hsI hsc
  let eC := overlapTopFrame (commonNormalBase I) C c bC eC0
  let eQ := overlapTopFrame (commonTangentBase α I) T d bQ eQ0
  let eS := overlapTensorFrame eC eQ
  let v := fun U => moduleTensorSection _ (regularListNormalAt I c) (regularListTangentTopAt α I d)
    U (overlapWedge (commonNormalBase I) C c eC0 U bC)
      (overlapWedge (commonTangentBase α I) T d eQ0 U bQ)
  have hv (U : (Spec (CommRingCat.of (A ⧸ I))).Opens) :
      eS.hom.val.app (op U) (v U) = (1 : Γ(Spec (CommRingCat.of (A ⧸ I)), U)) := by
    have h := overlapTensorFrame_section eC eQ U
      (overlapWedge (commonNormalBase I) C c eC0 U bC)
      (overlapWedge (commonTangentBase α I) T d eQ0 U bQ)
    have hC := overlapTopFrame_wedge (commonNormalBase I) C c bC eC0 U bC
    have hQ := overlapTopFrame_wedge (commonTangentBase α I) T d bQ eQ0 U bQ
    rw [Module.Basis.det_self, map_one] at hC hQ
    exact h.trans ((congrArg₂ (fun x y : Γ(Spec (CommRingCat.of (A ⧸ I)), U) => x * y)
      hC hQ).trans (one_mul 1))
  apply Iso.ext
  apply overlapHomExtUnitFrame eS v hv
  intro U
  have hsurj : Function.Surjective
      (relativeConormalAffineLinearG α (commonQuotientMap I) Ideal.Quotient.mk_surjective) :=
    (ModuleCat.epi_iff_surjective _).mp
      (relativeConormalAffineLinearComplex_epi α (commonQuotientMap I) Ideal.Quotient.mk_surjective)
  choose w hw using fun j => hsurj (bQ j)
  have hq : (fun j => relativeConormalAffineLinearG α (commonQuotientMap I)
      Ideal.Quotient.mk_surjective (w j)) = bQ := funext hw
  have h1 := regularListConormalDeterminantAt_wedge α I c d hA hB bQ s hs hsI hsc U bC w
  have h2 := regularListConormalDeterminantAt_wedge α I c d hA hB bQ' t ht htI htc U bC w
  rw [hq] at h1 h2
  exact h1.trans h2.symm

end IntrinsicDeterminant

section ConcreteCanonical

variable {R : CommRingCat.{u}} (α : R ⟶ A) (I : Ideal A) (c d : ℕ)

private def commonAmbientBasis (n : ℕ)
    (bA : Module.Basis (Fin n) A (CommRingCat.KaehlerDifferential α)) :
    Module.Basis (Fin n) (CommRingCat.of (A ⧸ I))
      ((ModuleCat.extendScalars (commonQuotientMap I).hom).obj
        (CommRingCat.KaehlerDifferential α)) := by
  letI := (commonQuotientMap I).hom.toAlgebra
  exact (bA.baseChange (CommRingCat.of (A ⧸ I))).map
    ((ModuleCat.extendScalarsAlgebraObjIso A (CommRingCat.of (A ⧸ I))
      (CommRingCat.KaehlerDifferential α)).symm.toLinearEquiv)

private def commonAmbientMiddleFrame (n : ℕ)
    (bA : Module.Basis (Fin n) A (CommRingCat.KaehlerDifferential α)) :
    regularListMiddleTopAt α I n ≅
      SheafOfModules.unit (Spec (CommRingCat.of (A ⧸ I))).ringCatSheaf :=
  (moduleExteriorPowerFunctor (Spec (CommRingCat.of (A ⧸ I))) n).mapIso
    (relativeConormalAffineMiddleIso α (commonQuotientMap I) ≪≫
      tildeBasisIso _ ((commonAmbientBasis α I n bA).reindex Equiv.ulift.symm)) ≪≫
    SheafOfModulesOfCommRing.exteriorTopFreeIso (Spec (CommRingCat.of (A ⧸ I))).sheaf n

private def commonAmbientCoefficient (n : ℕ)
    (bA : Module.Basis (Fin n) A (CommRingCat.KaehlerDifferential α)) :
    regularListMiddleTopAt α I n ≅
      (pullback (Spec.map (commonQuotientMap I))).obj
        (moduleExteriorPower (Spec A) (relativeDifferentialSheaf (Spec.map α)) n) :=
  commonAmbientMiddleFrame α I n bA ≪≫
    ((pullback (Spec.map (commonQuotientMap I))).mapIso (affineRelativeTopFrame α n bA) ≪≫
      pullbackUnitIso (Spec.map (commonQuotientMap I))).symm

variable (hA : α.hom.FormallySmooth)
  (hB : (α ≫ (CommRingCat.ofHom (Ideal.Quotient.mk I) :
    A ⟶ CommRingCat.of (A ⧸ I))).hom.FormallySmooth)
  (bA : Module.Basis (Fin (c + d)) A (CommRingCat.KaehlerDifferential α))
  (bQ : Module.Basis (Fin d) (CommRingCat.of (A ⧸ I))
    (CommRingCat.KaehlerDifferential (α ≫ (CommRingCat.ofHom (Ideal.Quotient.mk I) :
      A ⟶ CommRingCat.of (A ⧸ I)))))

/-- The concrete affine canonical determinant, transported only by the
actual common ideal and degree equalities. -/
def regularListCanonicalDeterminantAt (s : List A)
    (hs : RingTheory.Sequence.IsWeaklyRegular A s)
    (hI : Ideal.ofList s = I) (hc : s.length = c) :
    tensorSheaf (Spec (CommRingCat.of (A ⧸ I))) (regularListNormalAt I c)
      (regularListTangentTopAt α I d) ≅
      (pullback (Spec.map
        (CommRingCat.ofHom (Ideal.Quotient.mk I) : A ⟶ CommRingCat.of (A ⧸ I)))).obj
          (moduleExteriorPower (Spec A) (relativeDifferentialSheaf (Spec.map α)) (c + d)) := by
  subst I c
  exact affineRegularListCanonicalDeterminant α s hs hA hB bA bQ

private theorem regularListCanonicalDeterminantAt_eq (s : List A)
    (hs : RingTheory.Sequence.IsWeaklyRegular A s)
    (hI : Ideal.ofList s = I) (hc : s.length = c) :
    regularListCanonicalDeterminantAt α I c d hA hB bA bQ s hs hI hc =
      regularListConormalDeterminantAt α I c d hA hB bQ s hs hI hc ≪≫
        commonAmbientCoefficient α I (c + d) bA := by
  subst I c
  change affineRegularListCanonicalDeterminant α s hs hA hB bA bQ = _
  rw [affineRegularListCanonicalDeterminant_eq]
  rfl

/-- The concrete normal-first determinant is unchanged by the regular list
or tangent basis, with the same actual ambient basis. -/
theorem regularListCanonicalDeterminantAt_independent
    (bQ' : Module.Basis (Fin d) (CommRingCat.of (A ⧸ I))
      (CommRingCat.KaehlerDifferential (α ≫ (CommRingCat.ofHom (Ideal.Quotient.mk I) :
        A ⟶ CommRingCat.of (A ⧸ I)))))
    (s t : List A) (hs : RingTheory.Sequence.IsWeaklyRegular A s)
    (ht : RingTheory.Sequence.IsWeaklyRegular A t)
    (hsI : Ideal.ofList s = I) (htI : Ideal.ofList t = I)
    (hsc : s.length = c) (htc : t.length = c) :
    regularListCanonicalDeterminantAt α I c d hA hB bA bQ s hs hsI hsc =
      regularListCanonicalDeterminantAt α I c d hA hB bA bQ' t ht htI htc := by
  rw [regularListCanonicalDeterminantAt_eq, regularListCanonicalDeterminantAt_eq,
    regularListConormalDeterminantAt_independent α I c d hA hB bQ bQ' s t hs ht hsI htI hsc htc]

include bA in
private theorem ambientTop_quasicoherent :
    (moduleExteriorPower (Spec A)
      (relativeDifferentialSheaf (Spec.map α)) (c + d)).IsQuasicoherent :=
  (SheafOfModules.isQuasicoherent (Spec A).ringCatSheaf).prop_of_iso
    (tildeSelf ≪≫ (affineRelativeTopFrame α (c + d) bA).symm) inferInstance

variable [HasExt.{w} (ModuleCat.{u} A)]
  [HasDerivedCategory.{a} (Spec A).Modules]
  [HasDerivedCategory.{b} (Spec (CommRingCat.of (A ⧸ I))).Modules]
  (e : moduleSpecΓFunctor.obj
    (moduleExteriorPower (Spec A) (relativeDifferentialSheaf (Spec.map α)) (c + d)) ≅
      ModuleCat.of A A)

/-- The actual affine canonical top-homology arrow on the common quotient. -/
def affineRegularListCanonicalMapAt (s : List A)
    (hs : RingTheory.Sequence.IsWeaklyRegular A s)
    (hI : Ideal.ofList s = I) (hc : s.length = c) :
    regularListNativeTopHomologyAt
      (L := moduleExteriorPower (Spec A) (relativeDifferentialSheaf (Spec.map α)) (c + d)) I c ⟶
        regularListTangentTopAt α I d := by
  let := private_decl% (ambientTop_quasicoherent α c d bA)
  exact regularListCanonicalMapAt α I c e
    (regularListCanonicalDeterminantAt α I c d hA hB bA bQ s hs hI hc) s hs hI hc

/-- Different ordered regular generators give equal actual canonical
top-homology arrows, with arbitrary displayed tangent bases. The ambient
basis and coefficient frame are shared; no determinant-unit premise is used. -/
theorem affineRegularListCanonicalMapAt_generatorChange
    (bQ' : Module.Basis (Fin d) (CommRingCat.of (A ⧸ I))
      (CommRingCat.KaehlerDifferential (α ≫ (CommRingCat.ofHom (Ideal.Quotient.mk I) :
        A ⟶ CommRingCat.of (A ⧸ I)))))
    (s t : List A) (hs : RingTheory.Sequence.IsWeaklyRegular A s)
    (ht : RingTheory.Sequence.IsWeaklyRegular A t)
    (hsI : Ideal.ofList s = I) (htI : Ideal.ofList t = I)
    (hsc : s.length = c) (htc : t.length = c)
    (M : Matrix (Fin s.length) (Fin s.length) A)
    (hM : t = List.ofFn (fun i => ∑ j, M i j * s.get j)) :
    affineRegularListCanonicalMapAt α I c d hA hB bA bQ e s hs hsI hsc =
      affineRegularListCanonicalMapAt α I c d hA hB bA bQ' e t ht htI htc := by
  let := ambientTop_quasicoherent α c d bA
  unfold affineRegularListCanonicalMapAt
  rw [regularListCanonicalDeterminantAt_independent α I c d hA hB bA bQ bQ'
    s t hs ht hsI htI hsc htc]
  exact regularListCanonicalMapAt_generatorChange α I c e _ s t hs ht hsI htI hsc htc M hM

end ConcreteCanonical

section CoefficientFrames

variable (I : Ideal A) {L : (Spec A).Modules}
  (e f : moduleSpecΓFunctor.obj L ≅ ModuleCat.of A A)

/-- The actual scalar taking the second coefficient generator to the first. -/
def regularListCoefficientTransition : A := f.hom (e.inv 1)

private theorem coefficientInverse_transition :
    e.inv = ModuleCat.ofHom (LinearMap.toSpanSingleton A A (regularListCoefficientTransition e f)) ≫
      f.inv := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext_ring
  have h := ConcreteCategory.congr_hom f.hom_inv_id (e.inv 1)
  change e.inv 1 = f.inv ((1 : A) * regularListCoefficientTransition e f)
  rw [one_mul]
  exact h.symm

private def coefficientExtensionIso :
    (ModuleCat.extendScalars (commonQuotientMap I).hom).obj (moduleSpecΓFunctor.obj L) ≅
      ModuleCat.of (CommRingCat.of (A ⧸ I)) (CommRingCat.of (A ⧸ I)) :=
  (ModuleCat.extendScalars (commonQuotientMap I).hom).mapIso e ≪≫
    ModuleCat.extendScalarsAlgebraObjIso A (CommRingCat.of (A ⧸ I)) (ModuleCat.of A A) ≪≫
      (TensorProduct.AlgebraTensorModule.rid A (CommRingCat.of (A ⧸ I))
        (CommRingCat.of (A ⧸ I))).toModuleIso

private theorem coefficientExtensionIso_transition :
    (coefficientExtensionIso I e).inv ≫ (coefficientExtensionIso I f).hom =
      ModuleCat.ofHom (LinearMap.toSpanSingleton (CommRingCat.of (A ⧸ I))
        (CommRingCat.of (A ⧸ I)) (Ideal.Quotient.mk I (regularListCoefficientTransition e f))) := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext_ring
  let B := CommRingCat.of (A ⧸ I)
  change (TensorProduct.AlgebraTensorModule.rid A B B)
      ((ModuleCat.extendScalarsAlgebraObjIso A B (ModuleCat.of A A)).hom
        ((ModuleCat.extendScalars (commonQuotientMap I).hom).map f.hom
          ((ModuleCat.extendScalars (commonQuotientMap I).hom).map e.inv
            ((ModuleCat.extendScalarsAlgebraObjIso A B (ModuleCat.of A A)).inv
              ((TensorProduct.AlgebraTensorModule.rid A B B).symm (1 : B)))))) =
    (1 : B) * Ideal.Quotient.mk I (regularListCoefficientTransition e f)
  rw [TensorProduct.AlgebraTensorModule.rid_symm_apply,
    ModuleCat.extendScalarsAlgebraObjIso_inv_tmul, ModuleCat.ExtendScalars.map_tmul,
    ModuleCat.ExtendScalars.map_tmul, ModuleCat.extendScalarsAlgebraObjIso_hom_tmul,
    TensorProduct.AlgebraTensorModule.rid_tmul]
  simp only [regularListCoefficientTransition, Algebra.smul_def, one_mul, mul_one]
  rfl

variable [L.IsQuasicoherent]

private theorem overlapFunctorIsoCancel {C D : Type*} [Category C] [Category D]
    (F : C ⥤ D) {V W : D} {X Y : C} (a : V ≅ W) (b : W ≅ F.obj X)
    (e f : X ≅ Y) :
    (a ≪≫ b ≪≫ F.mapIso e ≪≫ Iso.refl (F.obj Y)).inv ≫
      (a ≪≫ b ≪≫ F.mapIso f ≪≫ Iso.refl (F.obj Y)).hom = F.map (e.inv ≫ f.hom) := by
  simp [Category.assoc]

private theorem commonCoefficientFrame_transition :
    (commonCoefficientFrame I e).inv ≫ (commonCoefficientFrame I f).hom =
      (tilde.functor (CommRingCat.of (A ⧸ I))).map
        ((coefficientExtensionIso I e).inv ≫ (coefficientExtensionIso I f).hom) := by
  exact overlapFunctorIsoCancel (tilde.functor (CommRingCat.of (A ⧸ I)))
    ((pullback (Spec.map (commonQuotientMap I))).mapIso (asIso L.fromTildeΓ).symm)
    ((tildePullbackIso (commonQuotientMap I)).app (moduleSpecΓFunctor.obj L))
    (coefficientExtensionIso I e) (coefficientExtensionIso I f)

private theorem commonCoefficientSection_transition (z : A ⧸ I)
    (U : (Spec (CommRingCat.of (A ⧸ I))).Opens) :
    commonCoefficientSection I e z U =
      commonCoefficientSection I f
        (z * Ideal.Quotient.mk I (regularListCoefficientTransition e f)) U := by
  let μ := ModuleCat.ofHom (LinearMap.toSpanSingleton (CommRingCat.of (A ⧸ I))
    (CommRingCat.of (A ⧸ I)) (Ideal.Quotient.mk I (regularListCoefficientTransition e f)))
  have hF := commonCoefficientFrame_transition I e f
  rw [coefficientExtensionIso_transition] at hF
  apply overlapIsoSection_injective (commonCoefficientFrame I f) U
  have h := congrArg (fun k => k.val.app (op U)
    (tilde.toOpen (ModuleCat.of (CommRingCat.of (A ⧸ I)) (CommRingCat.of (A ⧸ I))) U z)) hF
  have ht := ConcreteCategory.congr_hom (tilde.toOpen_map_app μ U) z
  have hi := congrArg (fun k => k.val.app (op U)
    (tilde.toOpen (ModuleCat.of (CommRingCat.of (A ⧸ I)) (CommRingCat.of (A ⧸ I))) U
      (z * Ideal.Quotient.mk I (regularListCoefficientTransition e f))))
    (commonCoefficientFrame I f).inv_hom_id
  exact (h.trans ht).trans hi.symm

variable (c : ℕ) [HasExt.{w} (ModuleCat.{u} A)]

omit [L.IsQuasicoherent] in
private theorem topExtClassAt_postcomp_transition (s : List A)
    (hs : RingTheory.Sequence.IsWeaklyRegular A s)
    (hI : Ideal.ofList s = I) (hc : s.length = c) (r : A) :
    (regularListTopExtClassAt I c s hs hI hc r).comp (Ext.mk₀ e.inv) (Nat.add_zero c) =
      (regularListTopExtClassAt I c s hs hI hc
        (r * regularListCoefficientTransition e f)).comp (Ext.mk₀ f.inv) (Nat.add_zero c) := by
  subst I c
  dsimp only [regularListTopExtClassAt]
  rw [ChainComplex.Koszul.topExtClass_comp_mk₀,
    ChainComplex.Koszul.topExtClass_comp_mk₀]
  have h := ConcreteCategory.congr_hom (coefficientInverse_transition e f) r
  exact congrArg (ChainComplex.Koszul.topExtClass s hs (moduleSpecΓFunctor.obj L)) h

variable [HasDerivedCategory.{a} (Spec A).Modules]
  [HasDerivedCategory.{b} (Spec (CommRingCat.of (A ⧸ I))).Modules]

/-- Changing the original coefficient frame gives its literal postcomposition scalar. -/
theorem regularListNativeTopClassAt_coefficientChange (s : List A)
    (hs : RingTheory.Sequence.IsWeaklyRegular A s)
    (hI : Ideal.ofList s = I) (hc : s.length = c) (r : A)
    (U : (Spec (CommRingCat.of (A ⧸ I))).Opens) :
    regularListNativeTopClassAt I c e s hs hI hc r U =
      regularListNativeTopClassAt I c f s hs hI hc
        (r * regularListCoefficientTransition e f) U := by
  let := commonModel_counit_quasiIso I e s hs hI
  rw [regularListNativeTopClassAt_eq, regularListNativeTopClassAt_eq,
    topExtClassAt_postcomp_transition I e f c s hs hI hc r]

variable {R : CommRingCat.{u}} (α : R ⟶ A)

/-- The actual inverse-normal purity arrow is independent of the coefficient frame. -/
theorem regularListConormalMapAt_coefficient_independent (s : List A)
    (hs : RingTheory.Sequence.IsWeaklyRegular A s)
    (hI : Ideal.ofList s = I) (hc : s.length = c) :
    regularListConormalMapAt α I c e s hs hI hc =
      regularListConormalMapAt α I c f s hs hI hc := by
  apply regularListNativeTopClassAt_hom_ext I c e s hs hI hc
  intro U
  rw [regularListConormalMapAt_class,
    regularListNativeTopClassAt_coefficientChange I e f c s hs hI hc 1 U,
    regularListConormalMapAt_class, one_mul, map_one,
    commonCoefficientSection_transition I e f 1 U, one_mul]

/-- Native contraction preserves independence of the auxiliary coefficient frame. -/
theorem regularListCanonicalMapAt_coefficient_independent
    {Q : (Spec (CommRingCat.of (A ⧸ I))).Modules}
    (Δ : tensorSheaf (Spec (CommRingCat.of (A ⧸ I))) (regularListNormalAt I c) Q ≅
      (pullback (Spec.map
        (CommRingCat.ofHom (Ideal.Quotient.mk I) : A ⟶ CommRingCat.of (A ⧸ I)))).obj L)
    (s : List A) (hs : RingTheory.Sequence.IsWeaklyRegular A s)
    (hI : Ideal.ofList s = I) (hc : s.length = c) :
    regularListCanonicalMapAt α I c e Δ s hs hI hc =
      regularListCanonicalMapAt α I c f Δ s hs hI hc := by
  rw [regularListCanonicalMapAt_eq, regularListCanonicalMapAt_eq,
    regularListConormalMapAt_coefficient_independent I e f c α s hs hI hc]

end CoefficientFrames

private theorem overlapUnitMul_pullback {X Y : Scheme.{u}} (k : X ⟶ Y) (r : Γ(Y, ⊤)) :
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

private theorem overlapTopFrame_transition {B : CommRingCat.{u}} (N : (Spec B).Modules)
    (E : ModuleCat.{u} B) (m : ℕ) (b b' : Module.Basis (Fin m) B E) (eN : N ≅ tilde E) :
    (overlapTopFrame N E m b' eN).inv ≫ (overlapTopFrame N E m b eN).hom =
      unitMul (Spec B) ((Scheme.ΓSpecIso B).inv (b.det b')) := by
  let e' := overlapTopFrame N E m b' eN
  apply overlapHomExtUnitFrame (Iso.refl _) (fun U => (1 : Γ(Spec B, U))) (fun _ => rfl)
  intro U
  have hw' := overlapTopFrame_wedge N E m b' eN U b'
  rw [Module.Basis.det_self, map_one] at hw'
  have hpre : e'.inv.val.app (op U) (1 : Γ(Spec B, U)) = overlapWedge N E m eN U b' :=
    overlapIsoSection_injective e' U
      ((congrArg (fun f => f.val.app (op U) (1 : Γ(Spec B, U))) e'.inv_hom_id).trans hw'.symm)
  change (overlapTopFrame N E m b eN).hom.val.app (op U)
      (e'.inv.val.app (op U) (1 : Γ(Spec B, U))) =
    (1 : Γ(Spec B, U)) * overlapScalar U (b.det b')
  rw [hpre, one_mul]
  exact overlapTopFrame_wedge N E m b eN U b'

private theorem overlapBasisBaseChange_det {K S V : Type u} [CommRing K] [CommRing S]
    [Algebra K S] [AddCommGroup V] [Module K V] {m : ℕ}
    (b b' : Module.Basis (Fin m) K V) :
    (b.baseChange S).det (b'.baseChange S) = algebraMap K S (b.det b') := by
  classical
  have h : (b.baseChange S).toMatrix (b'.baseChange S) =
      (b.toMatrix b').map (algebraMap K S) := by
    ext i j
    simp [Module.Basis.toMatrix_apply, Module.Basis.baseChange_apply,
      Module.Basis.baseChange_repr_tmul, Algebra.smul_def]
  rw [Module.Basis.det_apply, h]
  exact (RingHom.map_det (algebraMap K S) (b.toMatrix b')).symm

private theorem commonAmbientBasis_det {R : CommRingCat.{u}} (α : R ⟶ A)
    (I : Ideal A) (n : ℕ) (b b' : Module.Basis (Fin n) A (CommRingCat.KaehlerDifferential α)) :
    (commonAmbientBasis α I n b).det (commonAmbientBasis α I n b') =
      Ideal.Quotient.mk I (b.det b') := by
  simp only [commonAmbientBasis, Module.Basis.det_map, Function.comp_def,
    Module.Basis.map_apply, LinearEquiv.symm_apply_apply]
  exact overlapBasisBaseChange_det b b'

private theorem overlapPullbackFrameTransition {X Y : Scheme.{u}} (k : X ⟶ Y)
    {L : Y.Modules} (e f : L ≅ SheafOfModules.unit Y.ringCatSheaf) (r : Γ(Y, ⊤))
    (h : f.inv ≫ e.hom = unitMul Y r) :
    ((pullback k).mapIso f ≪≫ pullbackUnitIso k).inv ≫
      ((pullback k).mapIso e ≪≫ pullbackUnitIso k).hom = unitMul X (k.appTop.hom r) := by
  simp only [Iso.trans_inv, Iso.trans_hom, Functor.mapIso_inv, Functor.mapIso_hom]
  rw [Category.assoc, ← Functor.map_comp_assoc, h, overlapUnitMul_pullback,
    Iso.inv_hom_id_assoc]

private theorem overlapIsoRatios {C : Type*} [Category C] {X Y Z : C}
    (a a' : X ≅ Z) (b b' : Y ≅ Z)
    (h : a'.inv ≫ a.hom = b'.inv ≫ b.hom) : a ≪≫ b.symm = a' ≪≫ b'.symm := by
  apply Iso.ext
  apply (cancel_epi a'.inv).mp
  apply (cancel_mono b.hom).mp
  simpa [Category.assoc] using h

private theorem commonAmbientCoefficient_independent {R : CommRingCat.{u}} (α : R ⟶ A)
    (I : Ideal A) (n : ℕ) (b b' : Module.Basis (Fin n) A (CommRingCat.KaehlerDifferential α)) :
    commonAmbientCoefficient α I n b = commonAmbientCoefficient α I n b' := by
  let q := commonQuotientMap I
  let r := b.det b'
  have hA := overlapTopFrame_transition (relativeDifferentialSheaf (Spec.map α))
    (CommRingCat.KaehlerDifferential α) n b b' (relativeDifferentialAffineIso α)
  change (affineRelativeTopFrame α n b').inv ≫ (affineRelativeTopFrame α n b).hom =
    unitMul (Spec A) ((Scheme.ΓSpecIso A).inv r) at hA
  have hP := overlapPullbackFrameTransition (Spec.map q)
    (affineRelativeTopFrame α n b) (affineRelativeTopFrame α n b')
    ((Scheme.ΓSpecIso A).inv r) hA
  have hΓ := ConcreteCategory.congr_hom (Scheme.ΓSpecIso_inv_naturality q) r
  change (Scheme.ΓSpecIso (CommRingCat.of (A ⧸ I))).inv (q r) =
    (Spec.map q).appTop.hom ((Scheme.ΓSpecIso A).inv r) at hΓ
  rw [← hΓ] at hP
  have hC := overlapTopFrame_transition (commonMiddleBase α I)
    ((ModuleCat.extendScalars q.hom).obj (CommRingCat.KaehlerDifferential α)) n
    (commonAmbientBasis α I n b) (commonAmbientBasis α I n b')
    (relativeConormalAffineMiddleIso α q)
  change (commonAmbientMiddleFrame α I n b').inv ≫
      (commonAmbientMiddleFrame α I n b).hom =
    unitMul (Spec (CommRingCat.of (A ⧸ I)))
      ((Scheme.ΓSpecIso (CommRingCat.of (A ⧸ I))).inv
        ((commonAmbientBasis α I n b).det (commonAmbientBasis α I n b'))) at hC
  rw [commonAmbientBasis_det] at hC
  exact overlapIsoRatios (commonAmbientMiddleFrame α I n b)
    (commonAmbientMiddleFrame α I n b')
    ((pullback (Spec.map q)).mapIso (affineRelativeTopFrame α n b) ≪≫ pullbackUnitIso (Spec.map q))
    ((pullback (Spec.map q)).mapIso (affineRelativeTopFrame α n b') ≪≫ pullbackUnitIso (Spec.map q))
    (hC.trans hP.symm)

section AllFrames
variable {R : CommRingCat.{u}} (α : R ⟶ A) (I : Ideal A) (c d : ℕ)
  (hA : α.hom.FormallySmooth)
  (hB : (α ≫ (CommRingCat.ofHom (Ideal.Quotient.mk I) :
    A ⟶ CommRingCat.of (A ⧸ I))).hom.FormallySmooth)
  (bA bA' : Module.Basis (Fin (c + d)) A (CommRingCat.KaehlerDifferential α))
  (bQ bQ' : Module.Basis (Fin d) (CommRingCat.of (A ⧸ I))
    (CommRingCat.KaehlerDifferential (α ≫ (CommRingCat.ofHom (Ideal.Quotient.mk I) :
      A ⟶ CommRingCat.of (A ⧸ I)))))

/-- The concrete determinant is independent of all displayed normal, ambient
and tangent frames, retaining the original pulled-back coefficient sheaf. -/
theorem regularListCanonicalDeterminantAt_allFrames
    (s t : List A) (hs : RingTheory.Sequence.IsWeaklyRegular A s)
    (ht : RingTheory.Sequence.IsWeaklyRegular A t)
    (hsI : Ideal.ofList s = I) (htI : Ideal.ofList t = I)
    (hsc : s.length = c) (htc : t.length = c) :
    regularListCanonicalDeterminantAt α I c d hA hB bA bQ s hs hsI hsc =
      regularListCanonicalDeterminantAt α I c d hA hB bA' bQ' t ht htI htc := by
  rw [regularListCanonicalDeterminantAt_eq, regularListCanonicalDeterminantAt_eq,
    regularListConormalDeterminantAt_independent α I c d hA hB bQ bQ' s t hs ht hsI htI hsc htc,
    commonAmbientCoefficient_independent α I (c + d) bA bA']

variable [HasExt.{w} (ModuleCat.{u} A)]
  [HasDerivedCategory.{a} (Spec A).Modules]
  [HasDerivedCategory.{b} (Spec (CommRingCat.of (A ⧸ I))).Modules]
  (e f : moduleSpecΓFunctor.obj
    (moduleExteriorPower (Spec A) (relativeDifferentialSheaf (Spec.map α)) (c + d)) ≅
      ModuleCat.of A A)

/-- Equality of the actual canonical top-homology arrows for different regular
generators and arbitrary ambient, tangent and coefficient frames. -/
theorem affineRegularListCanonicalMapAt_overlap
    (s t : List A) (hs : RingTheory.Sequence.IsWeaklyRegular A s)
    (ht : RingTheory.Sequence.IsWeaklyRegular A t)
    (hsI : Ideal.ofList s = I) (htI : Ideal.ofList t = I)
    (hsc : s.length = c) (htc : t.length = c)
    (M : Matrix (Fin s.length) (Fin s.length) A)
    (hM : t = List.ofFn (fun i => ∑ j, M i j * s.get j)) :
    affineRegularListCanonicalMapAt α I c d hA hB bA bQ e s hs hsI hsc =
      affineRegularListCanonicalMapAt α I c d hA hB bA' bQ' f t ht htI htc := by
  let := ambientTop_quasicoherent α c d bA
  unfold affineRegularListCanonicalMapAt
  rw [regularListCanonicalDeterminantAt_allFrames α I c d hA hB bA bA' bQ bQ'
    s t hs ht hsI htI hsc htc]
  rw [regularListCanonicalMapAt_coefficient_independent I e f c α _ s hs hsI hsc]
  exact regularListCanonicalMapAt_generatorChange α I c f _ s t hs ht hsI htI hsc htc M hM

end AllFrames

end AlgebraicGeometry.Scheme.Modules
