/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Normalization.GenericFiniteEtale.RootCancellation
public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.StrictHenselianSection
public import Aglib.RingTheory.Henselian.StrictHenselization.FiniteLocalFactors

/-! # The original generic embedding from a normalized root-cover section

One section of the same finite-etale normalization gives an evaluation of its
original generic tensor and hence an embedding of the original covering field.
No product splitting or replacement field is chosen.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

namespace AlgebraicGeometry.Scheme.FiniteEtale.GenericNormalization

universe u

/-- A section of the actual normalization restricts to a section of the
unchanged generic finite-etale cover. -/
theorem exists_generic_section_of_normalization_section
    (X : Scheme.{u}) [IsIntegral X] (C : Scheme.FiniteEtale (Spec X.functionField))
    (s : X ⟶ (C.obj.hom ≫ X.fromSpecStalk (genericPoint X)).normalization)
    (hs : s ≫ (C.obj.hom ≫ X.fromSpecStalk (genericPoint X)).fromNormalization = 𝟙 X) :
    ∃ t : Spec X.functionField ⟶ C.obj.left, t ≫ C.obj.hom = 𝟙 _ := by
  let γ := X.fromSpecStalk (genericPoint X)
  let q := C.obj.hom ≫ γ
  have hs' : s ≫ q.fromNormalization = 𝟙 X := hs
  let z : Spec X.functionField ⟶ pullback q.fromNormalization γ :=
    pullback.lift (γ ≫ s) (𝟙 _) (by simp only [Category.assoc, hs',
      Category.comp_id, Category.id_comp])
  refine ⟨z ≫ (genericFiberOverIso X C).inv.left, ?_⟩
  rw [Category.assoc, Over.w]
  exact pullback.lift_snd _ _ _

section TensorSection

variable (K F L : Type u) [Field K] [Field F] [Field L] [Algebra K F] [Algebra K L]

/-- A section of the actual tensor spectrum produces a map from the original
right-hand field to the original left-hand field, with their original base action. -/
theorem exists_algHom_of_tensorSpectrum_section
    (t : Spec (.of F) ⟶ Spec (.of (F ⊗[K] L)))
    (ht : t ≫ Spec.algebraMap F (F ⊗[K] L) = 𝟙 _) :
    Nonempty (L →ₐ[K] F) := by
  obtain ⟨φ, hφ⟩ := Spec.map_surjective t
  have hmap : Spec.map (CommRingCat.ofHom (algebraMap F (F ⊗[K] L)) ≫ φ) =
      Spec.map (𝟙 (.of F)) := by
    rw [Spec.map_comp, hφ, Spec.map_id]
    exact ht
  have hc := Spec.map_injective hmap
  let ψ : (F ⊗[K] L) →ₐ[F] F :=
    { φ.hom with
      commutes' := fun r => by
        have h := congrArg (fun a : CommRingCat.of F ⟶ CommRingCat.of F => a r) hc
        exact h }
  exact ⟨(ψ.restrictScalars K).comp Algebra.TensorProduct.includeRight⟩

end TensorSection

namespace OpenRecovery

variable (R : Type u) [CommRing R] [IsDomain R] (x : R)
  [Nonempty (Spec (.of (Localization.Away x)))]

local instance embeddingOpenIntegral : IsIntegral (Spec (.of (Localization.Away x))) :=
  isIntegral_of_isOpenImmersion (Spec.algebraMap R (Localization.Away x))

local instance embeddingAffineFieldAlgebra : Algebra R (Spec (.of R)).functionField :=
  AlgebraicGeometry.instAlgebraCarrierFunctionFieldSpec (.of R)

/-- A section of the original normalization supplies an embedding of the
original covering field. The complete generic comparison and evaluation are
constructed here; no Henselianity, normality or field comparison is assumed. -/
theorem exists_generic_embedding_of_normalization_section
    {X : Scheme.{u}} [IsIntegral X]
    (g : Spec (.of (Localization.Away x)) ⟶ X) [IsDominant g]
    (Y : Scheme.FiniteEtale X) [IsIntegral Y.obj.left]
    (s : Spec (.of R) ⟶ (genericMap (Spec.algebraMap R (Localization.Away x))
      ((Scheme.FiniteEtale.baseChange g).obj Y).obj.hom).normalization)
    (hs : s ≫ (genericMap (Spec.algebraMap R (Localization.Away x))
      ((Scheme.FiniteEtale.baseChange g).obj Y).obj.hom).fromNormalization = 𝟙 _) :
    letI := baseChangeFieldAlgebra (Spec.algebraMap R (Localization.Away x)) g
    letI := GenericGalois.algebra Y
    Nonempty (Y.obj.left.functionField →ₐ[X.functionField] (Spec (.of R)).functionField) := by
  let := baseChangeFieldAlgebra (Spec.algebraMap R (Localization.Away x)) g
  let := GenericGalois.algebra Y
  let j := Spec.algebraMap R (Localization.Away x)
  let C := genericCover j ((Scheme.FiniteEtale.baseChange g).obj Y).obj.hom
  let e := baseChangeFieldSpectrumIso j g Y
  obtain ⟨t, ht⟩ := exists_generic_section_of_normalization_section (Spec (.of R)) C s hs
  apply exists_algHom_of_tensorSpectrum_section X.functionField
    (Spec (.of R)).functionField Y.obj.left.functionField (t ≫ e.inv)
  have he : e.inv ≫ Spec.algebraMap (Spec (.of R)).functionField
      ((Spec (.of R)).functionField ⊗[X.functionField] Y.obj.left.functionField) = C.obj.hom := by
    apply (cancel_epi e.hom).mp
    rw [Iso.hom_inv_id_assoc]
    exact (baseChangeFieldSpectrumIso_hom_over j g Y).symm
  rw [Category.assoc, he]
  exact ht

/-- Etaleness of the same normalization over a strictly Henselian base supplies
an embedding between the original function fields. Its generic comparison is
constructed from the original cover, not supplied as a premise. -/
theorem exists_generic_embedding_of_strictHenselian
    [HenselianLocalRing R] [IsSepClosed (IsLocalRing.ResidueField R)]
    [IsNoetherianRing R] [IsIntegrallyClosed R]
    {X : Scheme.{u}} [IsIntegral X]
    (g : Spec (.of (Localization.Away x)) ⟶ X) [IsDominant g]
    (Y : Scheme.FiniteEtale X) [IsIntegral Y.obj.left]
    [Etale (genericMap (Spec.algebraMap R (Localization.Away x))
      ((Scheme.FiniteEtale.baseChange g).obj Y).obj.hom).fromNormalization] :
    letI := baseChangeFieldAlgebra (Spec.algebraMap R (Localization.Away x)) g
    letI := GenericGalois.algebra Y
    Nonempty (Y.obj.left.functionField →ₐ[X.functionField] (Spec (.of R)).functionField) := by
  let := baseChangeFieldAlgebra (Spec.algebraMap R (Localization.Away x)) g
  let := GenericGalois.algebra Y
  let j := Spec.algebraMap R (Localization.Away x)
  let q := genericMap j ((Scheme.FiniteEtale.baseChange g).obj Y).obj.hom
  let e := baseChangeFieldSpectrumIso j g Y
  let : ∀ z : Spec (.of R), IsIntegrallyClosed ((Spec (.of R)).presheaf.stalk z) :=
    fun z => (isIntegrallyClosed_and_isDomain_stalk_Spec R z).1
  let : IsFinite q.fromNormalization := fromNormalization_isFinite j _
  let : Nonempty q.normalization :=
    ⟨q.toNormalization (e.hom (Classical.choice inferInstance))⟩
  obtain ⟨s, hs⟩ := exists_section_of_isSepClosed_residue R q.fromNormalization
  exact exists_generic_embedding_of_normalization_section R x g Y s hs

end OpenRecovery

namespace RootCancellation

open Algebra.Kummer

/-- The original map of root complements is dominant whenever its guarded
ring map is injective. -/
theorem rootComplement_dominant
    (R : Type u) [CommRing R] [IsDomain R] (N : ℕ) (f : R)
    [IsDomain (RootAlgebra N f)] (hN : 0 < N) (hf : f ≠ 0) :
    IsDominant (Spec.map (CommRingCat.ofHom (rootComplementHom N f))) := by
  constructor
  change DenseRange (PrimeSpectrum.comap (rootComplementHom N f))
  rw [PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical,
    (RingHom.injective_iff_ker_eq_bot _).mp (rootComplementHom_injective N f hN hf)]
  exact bot_le

variable (R : Type u) [CommRing R] [HenselianLocalRing R]
  [IsSepClosed (IsLocalRing.ResidueField R)] [IsNoetherianRing R]
  (f : R) (hf : f ∈ IsLocalRing.maximalIdeal R)
  [IsRegularLocalRing (R ⧸ Ideal.span {f})]
  (N : ℕ) (hN : 0 < N) (hreg : IsSMulRegular R f)

local notation "T" => RootAlgebra N f
local notation "θ" => AdjoinRoot.root (rootPolynomial N f)
local notation "U" => Localization.Away f
local notation "V" => Localization.Away θ
local notation "j" => Spec.algebraMap T V
local notation "g" => Spec.map (CommRingCat.ofHom (rootComplementHom N f))

include hf hN hreg

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Bounded root cancellation over an actual Noetherian strictly Henselian
regular parameter supplies an embedding of the original covering field into
the original root function field. The target normalization and its section
are constructed, not hypotheses; no product splitting is chosen. -/
theorem exists_generic_embedding :
    letI : IsRegularLocalRing R := IsRegularLocalRing.of_quotient_span_singleton R f hreg
    letI : IsDomain R := IsRegularLocalRing.isDomain_of_regularLocal R
    letI : IsDomain U := Localization.Away.isDomain (parameter_ne_zero R f hreg)
    letI : IsRegularLocalRing T := parameterRoot_isRegularLocalRing R f hf N hN hreg
    letI : IsDomain T := IsRegularLocalRing.isDomain_of_regularLocal T
    letI : IsDomain V := Localization.Away.isDomain (root_ne_zero R f N hN hreg)
    letI : IsDominant g := rootComplement_dominant R N f hN (parameter_ne_zero R f hreg)
    ∀ (Y : Scheme.FiniteEtale (Spec (.of U))) [IsIntegral Y.obj.left]
      [CategoryTheory.PreGaloisCategory.IsGalois Y],
    IsUnit (N : R) → Nat.card (Aut Y) ∣ N →
    letI := OpenRecovery.baseChangeFieldAlgebra j g
    letI := GenericGalois.algebra Y
    Nonempty (Y.obj.left.functionField →ₐ[(Spec (.of U)).functionField]
      (Spec (.of T)).functionField) := by
  let : IsRegularLocalRing R := IsRegularLocalRing.of_quotient_span_singleton R f hreg
  let : IsDomain R := IsRegularLocalRing.isDomain_of_regularLocal R
  let : IsDomain U := Localization.Away.isDomain (parameter_ne_zero R f hreg)
  let : IsRegularLocalRing T := parameterRoot_isRegularLocalRing R f hf N hN hreg
  let : IsDomain T := IsRegularLocalRing.isDomain_of_regularLocal T
  let : IsDomain V := Localization.Away.isDomain (root_ne_zero R f N hN hreg)
  let : IsDominant g := rootComplement_dominant R N f hN (parameter_ne_zero R f hreg)
  intro Y hYint hYgal hunit hcard
  let := OpenRecovery.baseChangeFieldAlgebra j g
  let := GenericGalois.algebra Y
  let : Module.Finite R T := root_finite N hN f
  let : HenselianLocalRing T := HenselianLocalRing.of_finite_local_algebra R T
  let : IsSepClosed (IsLocalRing.ResidueField T) :=
    HenselianLocalRing.residueField_isSepClosed_of_finite_local_algebra R T
  let : IsIntegrallyClosed T := IsRegularLocalRing.isIntegrallyClosed_of_regularLocal T
  let : Etale (OpenRecovery.genericMap j
      ((Scheme.FiniteEtale.baseChange g).obj Y).obj.hom).fromNormalization :=
    fromNormalization_etale R f hf N hN hreg Y hunit hcard
  exact OpenRecovery.exists_generic_embedding_of_strictHenselian T θ g Y

end RootCancellation

end AlgebraicGeometry.Scheme.FiniteEtale.GenericNormalization
