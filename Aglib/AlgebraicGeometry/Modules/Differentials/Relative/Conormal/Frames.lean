/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Aglib.AlgebraicGeometry.Modules.Differentials.Relative.Conormal.Affine
public import Aglib.AlgebraicGeometry.IdealSheaf.Affine
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Affine.Free.Sections
public import Aglib.RingTheory.Extension.Cotangent.RegularSequence
public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.LinearAlgebra.Basis.Prod
/-!
# Original affine geometric conormal frames

The actual pulled-back kernel ideal module of the original spectral
surjection identifies with the tilde of its native extension cotangent
module. The comparison uses the original `affineIdealIso`,
`tildePullbackIso` and `Extension.cotangentEquiv`; the original quotient
scalar action is preserved.

A weakly regular ordered kernel list gives the actual geometric free
frame. On every open, its literal cotangent classes map to the original
free sections, and the inverse recovers those same classes. The original
conormal arrow has the positive class-to-differential formula.

For a displayed quotient differential basis, formal smoothness of the
original ambient and quotient maps gives a normal-FIRST frame of the
same exact conormal sequence. Its original block determinant factors
as conormal determinant times quotient differential determinant, including
empty blocks and zero rings. No field, Noetherian or nontriviality premise
or alternate conormal object is introduced. The ambient projective
determinant retains its degree-one coefficient determinant. Global
canonical-line gluing and geometric purity/trace transport are subsequent
consumers; no trace normalization follows from the block order alone.
-/

@[expose] public section
noncomputable section
open CategoryTheory Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme.Hom AlgebraicGeometry.Scheme.Modules
open scoped TensorProduct
universe u
namespace AlgebraicGeometry.Scheme.Modules.Differentials
variable {R A B : CommRingCat.{u}} (α : R ⟶ A) (σ : A ⟶ B)
variable (hσ : Function.Surjective σ)

/-- The actual pulled-back spectral kernel ideal is the original native conormal sheaf. -/
def relativeConormalAffineIdealPullbackIso :
    (pullback (Spec.map σ)).obj (idealModule (Spec.map σ)) ≅
      tilde (relativeConormalAffineModule α σ hσ) := by
  let := α.hom.toAlgebra
  let := (α ≫ σ).hom.toAlgebra
  let := σ.hom.toAlgebra
  let E := relativeConormalAffineExtension α σ hσ
  exact (pullback (Spec.map σ)).mapIso (affineIdealIso σ).symm ≪≫
    (tildePullbackIso σ).app (ModuleCat.of A (RingHom.ker σ.hom)) ≪≫
    (tilde.functor B).mapIso E.cotangentEquiv.toModuleIso

/-- The original ordered regular-kernel classes form the native conormal basis. -/
def relativeConormalAffineBasis (s : List A)
    (hs : RingTheory.Sequence.IsWeaklyRegular A s) (hker : Ideal.ofList s = RingHom.ker σ.hom) :
    Module.Basis (Fin s.length) B (relativeConormalAffineModule α σ hσ) := by
  let := α.hom.toAlgebra
  let := (α ≫ σ).hom.toAlgebra
  exact (relativeConormalAffineExtension α σ hσ).cotangentBasisOfWeaklyRegular s hs hker

/-- Every native conormal basis vector is the same original ordered kernel class. -/
theorem relativeConormalAffineBasis_apply (s : List A)
    (hs : RingTheory.Sequence.IsWeaklyRegular A s) (hker : Ideal.ofList s = RingHom.ker σ.hom)
    (i : Fin s.length) :
    relativeConormalAffineBasis α σ hσ s hs hker i =
      relativeConormalAffineClass α σ hσ
        ⟨s.get i, hker.le (Ideal.subset_span (s.get_mem i))⟩ := by
  let := α.hom.toAlgebra
  let := (α ≫ σ).hom.toAlgebra
  exact (relativeConormalAffineExtension α σ hσ).cotangentBasisOfWeaklyRegular_apply
    s hs hker i

/-- The original tilde conormal module in its same-list free frame. -/
def relativeConormalAffineFreeIso (s : List A)
    (hs : RingTheory.Sequence.IsWeaklyRegular A s) (hker : Ideal.ofList s = RingHom.ker σ.hom) :
    (relativeConormalAffineComplex α σ hσ).X₁ ≅
      SheafOfModules.free (R := (Spec B).ringCatSheaf) (ULift.{u} (Fin s.length)) :=
  tildeBasisIso (relativeConormalAffineModule α σ hσ)
    ((relativeConormalAffineBasis α σ hσ s hs hker).reindex Equiv.ulift.symm)

/-- The original ordered cotangent class maps to the original free section on every open. -/
theorem relativeConormalAffineFreeIso_class (s : List A)
    (hs : RingTheory.Sequence.IsWeaklyRegular A s) (hker : Ideal.ofList s = RingHom.ker σ.hom)
    (i : Fin s.length) (U : (Spec B).Opens) :
    (relativeConormalAffineFreeIso α σ hσ s hs hker).hom.val.app (op U)
      (tilde.toOpen (relativeConormalAffineModule α σ hσ) U
        (relativeConormalAffineClass α σ hσ
          ⟨s.get i, hker.le (Ideal.subset_span (s.get_mem i))⟩)) =
      (SheafOfModules.freeSection (R := (Spec B).ringCatSheaf) (ULift.up i)).val (op U) := by
  have hb : ((relativeConormalAffineBasis α σ hσ s hs hker).reindex Equiv.ulift.symm)
      (ULift.up i) = relativeConormalAffineClass α σ hσ
        ⟨s.get i, hker.le (Ideal.subset_span (s.get_mem i))⟩ := by
    simpa only [Module.Basis.reindex_apply, Equiv.symm_symm, Equiv.ulift_apply, ULift.down_up]
      using relativeConormalAffineBasis_apply α σ hσ s hs hker i
  rw [← hb]
  exact tildeBasisIso_hom_toOpen (relativeConormalAffineModule α σ hσ)
    ((relativeConormalAffineBasis α σ hσ s hs hker).reindex Equiv.ulift.symm) (ULift.up i) U

/-- The actual geometric conormal module in the same ordered free frame. -/
def relativeConormalAffineGeometricFreeIso (s : List A)
    (hs : RingTheory.Sequence.IsWeaklyRegular A s) (hker : Ideal.ofList s = RingHom.ker σ.hom) :
    (pullback (Spec.map σ)).obj (idealModule (Spec.map σ)) ≅
      SheafOfModules.free (R := (Spec B).ringCatSheaf) (ULift.{u} (Fin s.length)) :=
  relativeConormalAffineIdealPullbackIso α σ hσ ≪≫ relativeConormalAffineFreeIso α σ hσ s hs hker

/-- The inverse free frame recovers the same original ordered cotangent class on every open. -/
theorem relativeConormalAffineFreeIso_inv_freeSection (s : List A)
    (hs : RingTheory.Sequence.IsWeaklyRegular A s) (hker : Ideal.ofList s = RingHom.ker σ.hom)
    (i : Fin s.length) (U : (Spec B).Opens) :
    (relativeConormalAffineFreeIso α σ hσ s hs hker).inv.val.app (op U)
      ((SheafOfModules.freeSection (R := (Spec B).ringCatSheaf) (ULift.up i)).val (op U)) =
      tilde.toOpen (relativeConormalAffineModule α σ hσ) U
        (relativeConormalAffineClass α σ hσ
          ⟨s.get i, hker.le (Ideal.subset_span (s.get_mem i))⟩) :=
  (congrArg ((relativeConormalAffineFreeIso α σ hσ s hs hker).inv.val.app (op U))
    (relativeConormalAffineFreeIso_class α σ hσ s hs hker i U).symm).trans
      (congrArg (fun k => k.val.app (op U)
        (tilde.toOpen (relativeConormalAffineModule α σ hσ) U
          (relativeConormalAffineClass α σ hσ
            ⟨s.get i, hker.le (Ideal.subset_span (s.get_mem i))⟩)))
        (relativeConormalAffineFreeIso α σ hσ s hs hker).hom_inv_id)

/-- The actual geometric conormal frame uses those same literal classes on every open. -/
theorem relativeConormalAffineGeometricFreeIso_class (s : List A)
    (hs : RingTheory.Sequence.IsWeaklyRegular A s) (hker : Ideal.ofList s = RingHom.ker σ.hom)
    (i : Fin s.length) (U : (Spec B).Opens) :
    (relativeConormalAffineGeometricFreeIso α σ hσ s hs hker).hom.val.app (op U)
      ((relativeConormalAffineIdealPullbackIso α σ hσ).inv.val.app (op U)
        (tilde.toOpen (relativeConormalAffineModule α σ hσ) U
          (relativeConormalAffineClass α σ hσ
            ⟨s.get i, hker.le (Ideal.subset_span (s.get_mem i))⟩))) =
      (SheafOfModules.freeSection (R := (Spec B).ringCatSheaf) (ULift.up i)).val (op U) := by
  change (relativeConormalAffineFreeIso α σ hσ s hs hker).hom.val.app (op U)
    ((relativeConormalAffineIdealPullbackIso α σ hσ).hom.val.app (op U)
      ((relativeConormalAffineIdealPullbackIso α σ hσ).inv.val.app (op U) _)) = _
  have h := congrArg (fun k => k.val.app (op U)
    (tilde.toOpen (relativeConormalAffineModule α σ hσ) U
      (relativeConormalAffineClass α σ hσ
        ⟨s.get i, hker.le (Ideal.subset_span (s.get_mem i))⟩)))
    (relativeConormalAffineIdealPullbackIso α σ hσ).inv_hom_id
  exact (congrArg
    ((relativeConormalAffineFreeIso α σ hσ s hs hker).hom.val.app (op U)) h).trans
      (relativeConormalAffineFreeIso_class α σ hσ s hs hker i U)

/-- The original conormal arrow takes the same inverse free section to the positive differential. -/
theorem relativeConormalAffineFreeIso_f (s : List A)
    (hs : RingTheory.Sequence.IsWeaklyRegular A s) (hker : Ideal.ofList s = RingHom.ker σ.hom)
    (i : Fin s.length) (r : B) :
    letI := σ.hom.toAlgebra
    (relativeConormalAffineMiddleIso α σ).hom.val.app (op (PrimeSpectrum.basicOpen r))
      ((relativeConormalAffineComplex α σ hσ).f.val.app (op (PrimeSpectrum.basicOpen r))
        ((relativeConormalAffineFreeIso α σ hσ s hs hker).inv.val.app
          (op (PrimeSpectrum.basicOpen r))
          ((SheafOfModules.freeSection (R := (Spec B).ringCatSheaf)
            (ULift.up i)).val (op (PrimeSpectrum.basicOpen r))))) =
      tilde.toOpen ((ModuleCat.extendScalars σ.hom).obj (CommRingCat.KaehlerDifferential α))
        (PrimeSpectrum.basicOpen r)
        ((1 : B) ⊗ₜ[A] CommRingCat.KaehlerDifferential.d (f := α) (s.get i)) := by
  let := σ.hom.toAlgebra
  have h := relativeConormalAffineFreeIso_inv_freeSection α σ hσ s hs hker i
    (PrimeSpectrum.basicOpen r)
  exact (congrArg (fun z =>
    (relativeConormalAffineMiddleIso α σ).hom.val.app (op (PrimeSpectrum.basicOpen r))
      ((relativeConormalAffineComplex α σ hσ).f.val.app (op (PrimeSpectrum.basicOpen r)) z))
    h).trans (relativeConormalAffineComplex_f_class α σ hσ r
      ⟨s.get i, hker.le (Ideal.subset_span (s.get_mem i))⟩)

section Product
variable {K C Q : Type*} [CommRing K] [AddCommGroup C] [AddCommGroup Q]
  [Module K C] [Module K Q]

private theorem conormalFrameProductDeterminant {c n : ℕ}
    (bC : Module.Basis (Fin c) K C) (bQ : Module.Basis (Fin n) K Q)
    (v : Fin c → C) (w : Fin n → C × Q) :
    (bC.prod bQ).det (Sum.elim (fun i => (v i, 0)) w) =
      bC.det v * bQ.det (fun j => (w j).2) := by
  classical
  let T : Matrix (Fin c) (Fin n) K := fun i j => bC.repr (w j).1 i
  have hmat : (bC.prod bQ).toMatrix (Sum.elim (fun i => (v i, 0)) w) =
      Matrix.fromBlocks (bC.toMatrix v) T 0 (bQ.toMatrix (fun j => (w j).2)) := by
    ext i j
    cases i with
    | inl i => cases j with
      | inl j => rfl
      | inr j => rfl
    | inr i => cases j with
      | inl j =>
        change bQ.repr 0 i = 0
        rw [map_zero, Finsupp.zero_apply]
      | inr j => rfl
  rw [Module.Basis.det_apply, hmat, Matrix.det_fromBlocks_zero₂₁,
    ← Module.Basis.det_apply, ← Module.Basis.det_apply]

end Product

section NativeSequence
universe u_cd v_cd w_cd
variable {R : Type u_cd} {B : Type v_cd} [CommRing R] [CommRing B] [Algebra R B]

private theorem conormalFrameNativeNormalFirst (E : Algebra.Extension.{w_cd} R B)
    [Algebra.FormallySmooth R E.Ring] [Algebra.FormallySmooth R B]
    (s : List E.Ring) (hs : RingTheory.Sequence.IsWeaklyRegular E.Ring s)
    (hker : Ideal.ofList s = E.ker) {n : ℕ}
    (bQ : Module.Basis (Fin n) B (KaehlerDifferential R B)) :
    ∃ bM : Module.Basis (Fin s.length ⊕ Fin n) B E.CotangentSpace,
      (∀ i, bM (Sum.inl i) = (1 : B) ⊗ₜ[E.Ring]
        KaehlerDifferential.D R E.Ring (s.get i)) ∧
      (∀ j, E.toKaehler (bM (Sum.inr j)) = bQ j) ∧
      (∀ (vC : Fin s.length → E.Cotangent) (wM : Fin n → E.CotangentSpace),
        bM.det (Sum.elim (fun i => E.cotangentComplex (vC i)) wM) =
          (E.cotangentBasisOfWeaklyRegular s hs hker).det vC *
            bQ.det (fun j => E.toKaehler (wM j))) := by
  choose v hv using fun j => Algebra.Extension.toKaehler_surjective (P := E) (bQ j)
  let l := bQ.constr B v
  have hl : E.toKaehler ∘ₗ l = LinearMap.id := by
    apply bQ.ext
    intro j
    simp only [LinearMap.comp_apply, l, Module.Basis.constr_basis, LinearMap.id_apply]
    exact hv j
  have hf : Function.Injective E.cotangentComplex :=
    (Algebra.Extension.cotangentComplex_injective_iff E).mpr inferInstance
  let e := ((Algebra.Extension.exact_cotangentComplex_toKaehler (P := E)).splitSurjectiveEquiv
    hf) ⟨l, hl⟩
  let bC := E.cotangentBasisOfWeaklyRegular s hs hker
  let bM := (bC.prod bQ).map e.val.symm
  have hF : E.cotangentComplex =
      e.val.symm.toLinearMap ∘ₗ LinearMap.inl B E.Cotangent (KaehlerDifferential R B) :=
    e.property.1
  have hG : E.toKaehler =
      LinearMap.snd B E.Cotangent (KaehlerDifferential R B) ∘ₗ e.val.toLinearMap :=
    e.property.2
  refine ⟨bM, ?_, ?_, ?_⟩
  · intro i
    change e.val.symm ((bC.prod bQ) (Sum.inl i)) = _
    rw [Module.Basis.prod_apply]
    change (e.val.symm.toLinearMap ∘ₗ
      LinearMap.inl B E.Cotangent (KaehlerDifferential R B)) (bC i) = _
    rw [← hF]
    rw [Algebra.Extension.cotangentBasisOfWeaklyRegular_apply,
      Algebra.Extension.cotangentComplex_mk]
  · intro j
    change E.toKaehler (e.val.symm ((bC.prod bQ) (Sum.inr j))) = _
    exact (LinearMap.congr_fun hG _).trans (by
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply,
        Module.Basis.prod_apply, LinearMap.snd_apply]
      rfl)
  · intro vC wM
    have heF (a : E.Cotangent) : e.val (E.cotangentComplex a) = (a, 0) := by
      exact (congrArg e.val (LinearMap.congr_fun hF a)).trans
        (e.val.apply_symm_apply (a, 0))
    have heG (m : E.CotangentSpace) : (e.val m).2 = E.toKaehler m :=
      (LinearMap.congr_fun hG m).symm
    have hfamily : e.val ∘ Sum.elim (fun i => E.cotangentComplex (vC i)) wM =
        Sum.elim (fun i => (vC i, 0)) (fun j => e.val (wM j)) := by
      funext i
      cases i with
      | inl i => exact heF (vC i)
      | inr j => rfl
    change ((bC.prod bQ).map e.val.symm).det _ = _
    rw [Module.Basis.det_map, LinearEquiv.symm_symm, hfamily, conormalFrameProductDeterminant]
    congr 1
    apply congrArg bQ.det
    funext j
    exact heG (wM j)

end NativeSequence
/-- A normal-first frame of the original conormal sequence and its actual block determinant. -/
theorem relativeConormalAffineNormalFirstFrame (s : List A)
    (hs : RingTheory.Sequence.IsWeaklyRegular A s) (hker : Ideal.ofList s = RingHom.ker σ.hom)
    (hA : α.hom.FormallySmooth) (hB : (α ≫ σ).hom.FormallySmooth) {n : ℕ}
    (bQ : Module.Basis (Fin n) B (CommRingCat.KaehlerDifferential (α ≫ σ))) :
    letI := σ.hom.toAlgebra
    ∃ bM : Module.Basis (Fin s.length ⊕ Fin n) B
        ((ModuleCat.extendScalars σ.hom).obj (CommRingCat.KaehlerDifferential α)),
      (∀ i, bM (Sum.inl i) = (1 : B) ⊗ₜ[A]
        CommRingCat.KaehlerDifferential.d (f := α) (s.get i)) ∧
      (∀ j, relativeConormalAffineLinearG α σ hσ (bM (Sum.inr j)) = bQ j) ∧
      (∀ (vC : Fin s.length → relativeConormalAffineModule α σ hσ)
          (wM : Fin n → (ModuleCat.extendScalars σ.hom).obj
            (CommRingCat.KaehlerDifferential α)),
        bM.det (Sum.elim (fun i => relativeConormalAffineLinearF α σ hσ (vC i)) wM) =
          (relativeConormalAffineBasis α σ hσ s hs hker).det vC *
            bQ.det (fun j => relativeConormalAffineLinearG α σ hσ (wM j))) := by
  let := α.hom.toAlgebra
  let := (α ≫ σ).hom.toAlgebra
  let := σ.hom.toAlgebra
  let : IsScalarTower R A B := IsScalarTower.of_algebraMap_eq' rfl
  let : Algebra.FormallySmooth R A := hA
  let : Algebra.FormallySmooth R B := hB
  let E := relativeConormalAffineExtension α σ hσ
  let : Algebra.FormallySmooth R E.Ring := by
    change @Algebra.FormallySmooth R A _ _ α.hom.toAlgebra
    exact hA
  exact conormalFrameNativeNormalFirst E s hs hker bQ

end AlgebraicGeometry.Scheme.Modules.Differentials
