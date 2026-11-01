/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Morphisms.Finite.GenericSubalgebraSquare
public import Aglib.AlgebraicGeometry.Morphisms.UniversallyInjective.GenericFinite
public import Aglib.AlgebraicGeometry.Morphisms.Etale.FiniteStalkNeighborhood
public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.RingTheory.LocalProperties.Reduced
public import Mathlib.RingTheory.Localization.Finiteness

/-! # Spreading the canonical generic radicial--etale factorization -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace AlgebraicGeometry.Scheme.FiniteGenericFactorization

universe u

private theorem universallyInjective_restrict_mono {X Y : Scheme.{u}} (f : X ⟶ Y)
    {U V : Y.Opens} (h : U ≤ V) [UniversallyInjective (f ∣_ V)] :
    UniversallyInjective (f ∣_ U) := by
  have : UniversallyInjective ((f ∣_ U) ≫ U.ι) := by
    rw [morphismRestrict_ι, ← X.homOfLE_ι (f.preimage_mono h), Category.assoc,
      ← morphismRestrict_ι]
    exact MorphismProperty.comp_mem @UniversallyInjective _ _ inferInstance
      (MorphismProperty.comp_mem @UniversallyInjective _ _ inferInstance inferInstance)
  apply ((tfae_universallyInjective (f ∣_ U)).out 2 1).mp
  intro K _ a b hab
  have hinj : ∀ (L : Type u) [Field L], Function.Injective
      (fun c : Spec (.of L) ⟶ (f ⁻¹ᵁ U) => c ≫ ((f ∣_ U) ≫ U.ι)) :=
    ((tfae_universallyInjective ((f ∣_ U) ≫ U.ι)).out 1 2).mp
      (inferInstance : UniversallyInjective ((f ∣_ U) ≫ U.ι))
  apply hinj K
  simpa only [Category.assoc] using congrArg (fun z => z ≫ U.ι) hab

/-- A finite factorization whose actual generic-stalk squares are radicial and
etale acquires these properties simultaneously on an actual affine open in the
original base. No irreducibility of the intermediate scheme is required. -/
theorem exists_affine_open_etale_radicial_of_generic_squares
    {X Y S X' Y' : Scheme.{u}} [IrreducibleSpace S] [IsNoetherian S]
    (f : X ⟶ Y) (g : Y ⟶ S) [IsFinite f] [IsFinite g]
    [LocallyOfFinitePresentation g]
    (a : X' ⟶ X) (b : X' ⟶ Y') (k : Y' ⟶ Y)
    (l : Y' ⟶ Spec (S.presheaf.stalk (genericPoint S)))
    (hX : IsPullback a b f k)
    (hY : IsPullback k l g (S.fromSpecStalk (genericPoint S)))
    [UniversallyInjective b] [Etale l] :
    ∃ U : S.Opens, IsAffineOpen U ∧ genericPoint S ∈ U ∧
      Etale (g ∣_ U) ∧ UniversallyInjective (f ∣_ (g ⁻¹ᵁ U)) := by
  have : UniversallyInjective (pullback.fst k f) := by
    have : UniversallyInjective (hX.flip.isoPullback.inv ≫ b) :=
      MorphismProperty.comp_mem @UniversallyInjective _ _ inferInstance inferInstance
    simpa only [IsPullback.isoPullback_inv_fst] using this
  obtain ⟨V, hV, hrad⟩ :=
    exists_open_universallyInjective_of_generic_cartesian_baseChange f g
      (S.fromSpecStalk (genericPoint S))
      (IsLocalRing.closedPoint (S.presheaf.stalk (genericPoint S)))
      (fromSpecStalk_closedPoint (x := genericPoint S)) k l hY
  have het : Etale (pullback.snd g (S.fromSpecStalk (genericPoint S))) := by
    have : Etale (hY.isoPullback.inv ≫ l) := inferInstance
    simpa only [IsPullback.isoPullback_inv_snd] using this
  obtain ⟨U, hUa, hU, hUV, he⟩ :=
    g.exists_affine_etale_target_neighborhood_of_finite (genericPoint S) het V hV
  have : UniversallyInjective (f ∣_ (g ⁻¹ᵁ V)) := by
    let H := isPullback_morphismRestrict f (g ⁻¹ᵁ V)
    have : UniversallyInjective (pullback.fst (g ⁻¹ᵁ V).ι f) := hrad
    have : UniversallyInjective (H.isoPullback.hom ≫ pullback.fst (g ⁻¹ᵁ V).ι f) :=
      MorphismProperty.comp_mem @UniversallyInjective _ _ inferInstance inferInstance
    simpa only [IsPullback.isoPullback_hom_fst] using this
  exact ⟨U, hUa, hU, he, universallyInjective_restrict_mono f (g.preimage_mono hUV)⟩

private noncomputable instance originalFunctionFieldAlgebra (R : Type u)
    [CommRing R] [IsDomain R] : Algebra R (Spec (.of R)).functionField :=
  instAlgebraCarrierFunctionFieldSpec (.of R)

private instance originalFunctionFieldFractionRing (R : Type u) [CommRing R] [IsDomain R] :
    IsFractionRing R (Spec (.of R)).functionField :=
  functionField_isFractionRing_of_affine (.of R)

open scoped nonZeroDivisors

/-- The canonical intermediate subalgebra of a finite algebra has an actual
radicial--etale factorization on a dense affine open. The generic algebra is an
explicit localization over the original generic stalk; its reducedness is kept
as a hypothesis until the reduced-localization theorem is applied. -/
theorem exists_affine_open_etale_radicial
    (R : CommRingCat.{u}) (A A' : Type u) [IsDomain R] [IsNoetherianRing R]
    [CommRing A] [Algebra R A] [Module.Finite R A] [CommRing A']
    [Algebra R A'] [Algebra A A']
    [Algebra (Spec R).functionField A']
    [IsScalarTower R A A'] [IsScalarTower R (Spec R).functionField A']
    [IsLocalization (R⁰.map (algebraMap R A)) A']
    [Module.Finite (Spec R).functionField A'] [_root_.IsReduced A'] :
    ∃ U : (Spec R).Opens, IsAffineOpen U ∧ genericPoint (Spec R) ∈ U ∧
      Etale (FiniteGenericSubalgebra.structureMap R (Spec R).functionField A A' ∣_ U) ∧
      UniversallyInjective (FiniteGenericSubalgebra.projection R
        (Spec R).functionField A A' ∣_
        (FiniteGenericSubalgebra.structureMap R (Spec R).functionField A A' ⁻¹ᵁ U)) := by
  let K := (Spec R).functionField
  let B := Algebra.FiniteGenericSubalgebra.model R K A A'
  let C := Algebra.FiniteGenericSubalgebra.genericPart K A'
  let f := FiniteGenericSubalgebra.projection R K A A'
  let g := FiniteGenericSubalgebra.structureMap R K A A'
  let a := Spec.map (CommRingCat.ofHom (algebraMap A A'))
  let b := Spec.map (CommRingCat.ofHom C.val.toRingHom)
  let k := Spec.map (CommRingCat.ofHom (algebraMap B C))
  let l := Spec.map (CommRingCat.ofHom (algebraMap K C))
  have hX : IsPullback a b f k :=
    FiniteGenericSubalgebra.projection_generic_isPullback R K A A' R⁰
  have hY : IsPullback k l g ((Spec R).fromSpecStalk (genericPoint (Spec R))) := by
    rw [Spec.fromSpecStalk_eq']
    exact FiniteGenericSubalgebra.generic_isPullback R K A A' R⁰
  exact exists_affine_open_etale_radicial_of_generic_squares f g a b k l hX hY

open scoped TensorProduct

/-- Every finite reduced algebra over a Noetherian domain admits an actual
finite intermediate subalgebra whose spectrum is generically etale over the
base and over which the original source is finite, surjective and generically
radicial. The conclusion retains the literal original structural triangle. -/
theorem exists_subalgebra_affine_open_etale_radicial
    (R A : Type u) [CommRing R] [IsDomain R] [IsNoetherianRing R]
    [CommRing A] [Algebra R A] [Module.Finite R A] [_root_.IsReduced A] :
    ∃ B : Subalgebra R A, Module.Finite R B ∧
      IsFinite (Spec.map (CommRingCat.ofHom B.val.toRingHom)) ∧
      Surjective (Spec.map (CommRingCat.ofHom B.val.toRingHom)) ∧
      Spec.map (CommRingCat.ofHom B.val.toRingHom) ≫
        Spec.map (CommRingCat.ofHom (algebraMap R B)) =
          Spec.map (CommRingCat.ofHom (algebraMap R A)) ∧
      ∃ U : (Spec (.of R)).Opens, IsAffineOpen U ∧ genericPoint (Spec (.of R)) ∈ U ∧
        Etale (Spec.map (CommRingCat.ofHom (algebraMap R B)) ∣_ U) ∧
        UniversallyInjective (Spec.map (CommRingCat.ofHom B.val.toRingHom) ∣_
          (Spec.map (CommRingCat.ofHom (algebraMap R B)) ⁻¹ᵁ U)) := by
  let K := (Spec (.of R)).functionField
  let A' := K ⊗[R] A
  let : Algebra A A' := Algebra.TensorProduct.rightAlgebra
  have hloc : IsLocalization (Algebra.algebraMapSubmonoid A R⁰) A' :=
    (Algebra.isLocalization_iff_isPushout R⁰ K (T := A) (B := A')).mpr inferInstance
  have : IsLocalization (R⁰.map (algebraMap R A)) A' := hloc
  have : Module.Finite K A' := inferInstance
  have : _root_.IsReduced A' :=
    isReduced_localizationPreserves (R⁰.map (algebraMap R A)) A' inferInstance
  let B := Algebra.FiniteGenericSubalgebra.model R K A A'
  obtain ⟨U, hUa, hU, he, hr⟩ := exists_affine_open_etale_radicial (.of R) A A'
  refine ⟨B, inferInstance, ?_, ?_, ?_, U, hUa, hU, he, hr⟩
  · exact FiniteGenericSubalgebra.projection_finite R K A A'
  · exact FiniteGenericSubalgebra.projection_surjective R K A A'
  · exact FiniteGenericSubalgebra.projection_structureMap R K A A'

end AlgebraicGeometry.Scheme.FiniteGenericFactorization
