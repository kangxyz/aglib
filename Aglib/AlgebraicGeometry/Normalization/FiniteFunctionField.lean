/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Normalization.FunctionField
public import Aglib.RingTheory.Nagata.Basic

/-!
# Normalization in an arbitrary finite extension of the original function field

The source is the actual Spec L and its specified algebra over K(X).
On each nonempty affine chart, the original section map forms the scalar
tower through K(X). The chart's original section algebra is identified
with the same L. Japanese finiteness applies to that actual integral
closure; ordinary finite-extension integral-closure normality gives the
actual normal stalks. Neither separability nor etaleness is assumed.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme.FiniteFunctionField

variable (X : Scheme.{u}) [IsIntegral X]
  (L : Type u) [Field L] [Algebra X.functionField L]

/-- The actual original field extension as a spectral morphism. -/
def genericCover : Spec (.of L) ⟶ Spec X.functionField :=
  Spec.map (CommRingCat.ofHom (algebraMap X.functionField L))

instance genericCover_isAffineHom : IsAffineHom (genericCover X L) := by
  unfold genericCover
  infer_instance

instance genericCover_isSurjective : Surjective (genericCover X L) := by
  let : Subsingleton (Spec X.functionField) :=
    inferInstanceAs (Subsingleton (PrimeSpectrum X.functionField))
  exact ⟨Function.surjective_to_subsingleton _⟩

/-- The original L-valued generic map to X. -/
def genericMap : Spec (.of L) ⟶ X :=
  genericCover X L ≫ X.fromSpecStalk (genericPoint X)

instance genericMap_isQuasiCompact : QuasiCompact (genericMap X L) := by
  unfold genericMap
  infer_instance

instance genericMap_isQuasiSeparated : QuasiSeparated (genericMap X L) := by
  unfold genericMap
  infer_instance

instance genericMap_isDominant : IsDominant (genericMap X L) := by
  unfold genericMap
  infer_instance

/-- The literal relative normalization of the specified generic map. -/
def normalization : Scheme.{u} := (genericMap X L).normalization

/-- The original structural morphism of the relative normalization. -/
def fromNormalization : normalization X L ⟶ X := (genericMap X L).fromNormalization

instance fromNormalization_isAffineHom : IsAffineHom (fromNormalization X L) :=
  inferInstanceAs (IsAffineHom (genericMap X L).fromNormalization)

/-- The original field point in its relative normalization. -/
def toNormalization : Spec (.of L) ⟶ normalization X L := (genericMap X L).toNormalization

instance normalization_isIntegral : IsIntegral (normalization X L) :=
  inferInstanceAs (IsIntegral (genericMap X L).normalization)

instance toNormalization_isDominant : IsDominant (toNormalization X L) :=
  inferInstanceAs (IsDominant (genericMap X L).toNormalization)

@[reassoc]
theorem toNormalization_fromNormalization :
    toNormalization X L ≫ fromNormalization X L = genericMap X L :=
  Scheme.Hom.toNormalization_fromNormalization _

instance fromNormalization_isDominant : IsDominant (fromNormalization X L) := by
  have : IsDominant (toNormalization X L ≫ fromNormalization X L) := by
    rw [toNormalization_fromNormalization]
    infer_instance
  exact IsDominant.of_comp (toNormalization X L) (fromNormalization X L)

section Chart

variable (U : X.Opens) [Nonempty U]

/-- A nonempty original base open pulls back to the whole original field spectrum. -/
theorem preimage_genericMap : (genericMap X L) ⁻¹ᵁ U = ⊤ := by
  simp only [genericMap, Scheme.Hom.comp_preimage, fromSpecStalk_genericPoint_preimage,
    Scheme.Hom.preimage_top]

/-- The actual generic chart sections, through their original restriction isomorphism. -/
def chartOriginalSectionsIso :
    Γ(Spec (.of L), (genericMap X L) ⁻¹ᵁ U) ≅ Γ(Spec (.of L), ⊤) :=
  (Spec (.of L)).presheaf.mapIso (eqToIso (preimage_genericMap X L U).symm).op

/-- The actual chart sections identify with the same original extension field. -/
def chartFieldIso : Γ(Spec (.of L), (genericMap X L) ⁻¹ᵁ U) ≅ CommRingCat.of L :=
  chartOriginalSectionsIso X L U ≪≫ Scheme.ΓSpecIso (.of L)

/-- The function-field action is the original section map of the specified generic cover. -/
def chartFunctionFieldMap :
    X.functionField ⟶ Γ(Spec (.of L), (genericMap X L) ⁻¹ᵁ U) :=
  (Scheme.ΓSpecIso X.functionField).inv ≫
    (genericCover X L).appLE ⊤ ((genericMap X L) ⁻¹ᵁ U) (by simp)

instance chartFunctionFieldAlgebra :
    Algebra X.functionField Γ(Spec (.of L), (genericMap X L) ⁻¹ᵁ U) :=
  (chartFunctionFieldMap X L U).hom.toAlgebra

/-- The base-chart action is the literal map used by relative normalization. -/
instance chartBaseAlgebra :
    Algebra Γ(X, U) Γ(Spec (.of L), (genericMap X L) ⁻¹ᵁ U) :=
  ((genericMap X L).app U).hom.toAlgebra

private theorem genericAppLE_square :
    (X.fromSpecStalk (genericPoint X)).appLE U ⊤
        (by rw [fromSpecStalk_genericPoint_preimage]) =
      X.germToFunctionField U ≫ (Scheme.ΓSpecIso X.functionField).inv := by
  apply (cancel_mono (Scheme.ΓSpecIso X.functionField).hom).mp
  simp only [Scheme.Hom.appLE, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  have he : (homOfLE (show ⊤ ≤ (X.fromSpecStalk (genericPoint X)) ⁻¹ᵁ U from
      (fromSpecStalk_genericPoint_preimage X U).symm.le)).op =
      (eqToIso (fromSpecStalk_genericPoint_preimage X U).symm).op.hom :=
    Subsingleton.elim _ _
  rw [he]
  exact fromSpecStalk_genericPoint_app_functionFieldSectionsIso X U

/-- The literal section map of the composite is the original function-field tower. -/
theorem chartFunctionFieldMap_comp :
    X.germToFunctionField U ≫ chartFunctionFieldMap X L U =
      (genericMap X L).app U := by
  have hcomp :
      (X.fromSpecStalk (genericPoint X)).appLE U ⊤
          (by rw [fromSpecStalk_genericPoint_preimage]) ≫
        (genericCover X L).appLE ⊤ ((genericMap X L) ⁻¹ᵁ U) (by simp) =
      (genericMap X L).app U := by
    exact (Scheme.Hom.appLE_comp_appLE (genericCover X L)
      (X.fromSpecStalk (genericPoint X)) U ⊤ ((genericMap X L) ⁻¹ᵁ U)
      (by rw [fromSpecStalk_genericPoint_preimage]) (by simp)).trans
        (Scheme.Hom.appLE_eq_app (genericMap X L))
  calc
    X.germToFunctionField U ≫ chartFunctionFieldMap X L U =
        (X.germToFunctionField U ≫ (Scheme.ΓSpecIso X.functionField).inv) ≫
          (genericCover X L).appLE ⊤ ((genericMap X L) ⁻¹ᵁ U) (by simp) := by
      simp only [chartFunctionFieldMap, Category.assoc]
    _ = (X.fromSpecStalk (genericPoint X)).appLE U ⊤
          (by rw [fromSpecStalk_genericPoint_preimage]) ≫
        (genericCover X L).appLE ⊤ ((genericMap X L) ⁻¹ᵁ U) (by simp) :=
      congrArg (fun f : Γ(X, U) ⟶ Γ(Spec X.functionField, ⊤) ↦
        f ≫ (genericCover X L).appLE ⊤ ((genericMap X L) ⁻¹ᵁ U) (by simp))
          (genericAppLE_square X U).symm
    _ = (genericMap X L).app U := hcomp

/-- The original normalization section action factors through the actual function field. -/
instance chartScalarTower :
    IsScalarTower Γ(X, U) X.functionField Γ(Spec (.of L), (genericMap X L) ⁻¹ᵁ U) := by
  apply IsScalarTower.of_algebraMap_eq'
  change ((genericMap X L).app U).hom =
    (X.germToFunctionField U ≫ chartFunctionFieldMap X L U).hom
  exact congrArg CommRingCat.Hom.hom (chartFunctionFieldMap_comp X L U).symm

/-- The original chart-to-field isomorphism preserves the specified K(X)-action. -/
theorem chartFunctionFieldMap_fieldIso :
    chartFunctionFieldMap X L U ≫ (chartFieldIso X L U).hom =
      CommRingCat.ofHom (algebraMap X.functionField L) := by
  have hcover :
      (genericCover X L).appLE ⊤ ((genericMap X L) ⁻¹ᵁ U) (by simp) ≫
          (chartOriginalSectionsIso X L U).hom =
        (genericCover X L).appTop := by
    change (genericCover X L).appLE ⊤ ((genericMap X L) ⁻¹ᵁ U) (by simp) ≫
      (Spec (.of L)).presheaf.map (eqToHom (preimage_genericMap X L U).symm).op = _
    exact (Scheme.Hom.appLE_map (genericCover X L) (U := ⊤)
      (show (genericMap X L) ⁻¹ᵁ U ≤ (genericCover X L) ⁻¹ᵁ ⊤ from by simp)
      (eqToHom (preimage_genericMap X L U).symm).op).trans
        (Scheme.Hom.appLE_eq_app (genericCover X L) (U := ⊤))
  calc
    chartFunctionFieldMap X L U ≫ (chartFieldIso X L U).hom =
        (Scheme.ΓSpecIso X.functionField).inv ≫
          ((genericCover X L).appLE ⊤ ((genericMap X L) ⁻¹ᵁ U) (by simp) ≫
            (chartOriginalSectionsIso X L U).hom) ≫ (Scheme.ΓSpecIso (.of L)).hom := by
      simp only [chartFunctionFieldMap, chartFieldIso, Iso.trans_hom, Category.assoc]
    _ = (Scheme.ΓSpecIso X.functionField).inv ≫
        (genericCover X L).appTop ≫ (Scheme.ΓSpecIso (.of L)).hom :=
      congrArg (fun f : Γ(Spec X.functionField, ⊤) ⟶ Γ(Spec (.of L), ⊤) ↦
        (Scheme.ΓSpecIso X.functionField).inv ≫ f ≫ (Scheme.ΓSpecIso (.of L)).hom) hcover
    _ = CommRingCat.ofHom (algebraMap X.functionField L) := by
      change (Scheme.ΓSpecIso X.functionField).inv ≫
        (Spec.map (CommRingCat.ofHom (algebraMap X.functionField L))).appTop ≫
          (Scheme.ΓSpecIso (.of L)).hom = _
      rw [← Scheme.ΓSpecIso_inv_naturality_assoc, Iso.inv_hom_id, Category.comp_id]

/-- The field equivalence preserves the original intermediate field action. -/
def chartFieldEquiv :
    Γ(Spec (.of L), (genericMap X L) ⁻¹ᵁ U) ≃ₐ[X.functionField] L :=
  { (chartFieldIso X L U).commRingCatIsoToRingEquiv with
    commutes' r := by
      exact congrArg (fun f : X.functionField ⟶ CommRingCat.of L ↦ f.hom r)
        (chartFunctionFieldMap_fieldIso X L U) }

private theorem chart_isField :
    IsField Γ(Spec (.of L), (genericMap X L) ⁻¹ᵁ U) := by
  rw [preimage_genericMap]
  let : Subsingleton (Spec (.of L)) := inferInstanceAs (Subsingleton (PrimeSpectrum L))
  exact isField_of_isIntegral_of_subsingleton (Spec (.of L))

instance chartAlgebraFinite [Module.Finite X.functionField L] :
    Module.Finite X.functionField Γ(Spec (.of L), (genericMap X L) ⁻¹ᵁ U) :=
  Module.Finite.equiv (chartFieldEquiv X L U).symm.toLinearEquiv

end Chart

section FiniteExtension

variable [Module.Finite X.functionField L]

instance genericCover_isFinite : IsFinite (genericCover X L) :=
  (IsFinite.SpecMap_iff _).mpr
    (RingHom.finite_algebraMap.mpr (inferInstance : Module.Finite X.functionField L))

private theorem normalization_sections_normal
    (U : X.Opens) (hU : IsAffineOpen U) [Nonempty U] :
    IsDomain Γ(normalization X L, (fromNormalization X L) ⁻¹ᵁ U) ∧
      IsIntegrallyClosed Γ(normalization X L, (fromNormalization X L) ⁻¹ᵁ U) := by
  let : Field Γ(Spec (.of L), (genericMap X L) ⁻¹ᵁ U) :=
    { (chart_isField X L U).toField with
      toCommRing := inferInstanceAs (CommRing Γ(Spec (.of L), (genericMap X L) ⁻¹ᵁ U)) }
  let : IsFractionRing Γ(X, U) X.functionField :=
    functionField_isFractionRing_of_isAffineOpen X U hU
  let : IsIntegrallyClosed
      (integralClosure Γ(X, U) Γ(Spec (.of L), (genericMap X L) ⁻¹ᵁ U)) :=
    integralClosure.isIntegrallyClosedOfFiniteExtension
      (R := Γ(X, U)) X.functionField
      (L := Γ(Spec (.of L), (genericMap X L) ⁻¹ᵁ U))
  let e := ((genericMap X L).normalizationObjIso hU).commRingCatIsoToRingEquiv
  exact ⟨Function.Injective.isDomain e.toRingHom e.injective,
    IsIntegrallyClosed.of_equiv e.symm⟩

/-- The actual relative normalization has normal domain stalks for an arbitrary
finite field extension. Base normality and separability are not hypotheses. -/
theorem normalization_normalStalks : NormalStalks (normalization X L) := by
  intro y
  obtain ⟨_, ⟨U, hU, rfl⟩, hyU, _⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open
    (Set.mem_univ (fromNormalization X L y)) isOpen_univ
  let : Nonempty U := ⟨⟨fromNormalization X L y, hyU⟩⟩
  let V := (fromNormalization X L) ⁻¹ᵁ U
  have hV : IsAffineOpen V := hU.preimage (fromNormalization X L)
  obtain ⟨hdom, hnormal⟩ := normalization_sections_normal X L U hU
  let : IsDomain Γ(normalization X L, V) := hdom
  let : IsIntegrallyClosed Γ(normalization X L, V) := hnormal
  let : Algebra Γ(normalization X L, V) ((normalization X L).presheaf.stalk y) :=
    TopCat.Presheaf.algebra_section_stalk (normalization X L).presheaf ⟨y, hyU⟩
  let p := hV.primeIdealOf ⟨y, hyU⟩
  let : IsLocalization.AtPrime ((normalization X L).presheaf.stalk y) p.asIdeal :=
    hV.isLocalization_stalk ⟨y, hyU⟩
  refine ⟨inferInstance, ?_⟩
  exact isIntegrallyClosed_of_isLocalization ((normalization X L).presheaf.stalk y)
    p.asIdeal.primeCompl p.asIdeal.primeCompl_le_nonZeroDivisors

private theorem fromNormalization_finite_app
    (U : X.Opens) (hU : IsAffineOpen U) [Nonempty U]
    (hNagata : IsNagataRing.{u, 0} Γ(X, U)) :
    ((fromNormalization X L).app U).hom.Finite := by
  let : Field Γ(Spec (.of L), (genericMap X L) ⁻¹ᵁ U) :=
    { (chart_isField X L U).toField with
      toCommRing := inferInstanceAs (CommRing Γ(Spec (.of L), (genericMap X L) ⁻¹ᵁ U)) }
  let : IsFractionRing Γ(X, U) X.functionField :=
    functionField_isFractionRing_of_isAffineOpen X U hU
  let : Module.Finite Γ(X, U)
      (integralClosure Γ(X, U) Γ(Spec (.of L), (genericMap X L) ⁻¹ᵁ U)) :=
    hNagata.isJapaneseRing.finite_integralClosure_of_isFractionRing X.functionField
      Γ(Spec (.of L), (genericMap X L) ⁻¹ᵁ U)
  change (((genericMap X L).fromNormalization).app U).hom.Finite
  rw [Scheme.Hom.fromNormalization_app _ hU]
  exact (RingHom.Finite.of_surjective _
    (ConcreteCategory.bijective_of_isIso ((genericMap X L).normalizationObjIso hU).inv).2).comp
      (RingHom.finite_algebraMap.mpr
        (inferInstanceAs
          (Module.Finite Γ(X, U)
            (integralClosure Γ(X, U) Γ(Spec (.of L), (genericMap X L) ⁻¹ᵁ U)))))

/-- Actual affine-chart Nagata properties make the original relative-normalization
map finite. The final hypothesis is on original chart rings, not on the desired map. -/
theorem fromNormalization_isFinite
    (hNagata : ∀ U : X.affineOpens, Nonempty U.1 → IsNagataRing.{u, 0} Γ(X, U.1)) :
    IsFinite (fromNormalization X L) := by
  refine { toIsAffineHom := inferInstance, finite_app := ?_ }
  intro U hU
  by_cases hne : Nonempty U
  · let := hne
    exact fromNormalization_finite_app X L U hU (hNagata ⟨U, hU⟩ hne)
  · have hbot : U = ⊥ := by
      apply le_antisymm
      · intro x hx
        exact (hne ⟨⟨x, hx⟩⟩).elim
      · exact bot_le
    subst U
    let : Subsingleton Γ(normalization X L, (fromNormalization X L) ⁻¹ᵁ ⊥) := by
      simpa only [Scheme.Hom.preimage_bot] using
        (inferInstanceAs (Subsingleton Γ(normalization X L, ⊥)))
    exact RingHom.Finite.of_surjective _ (Function.surjective_to_subsingleton _)

/-- Local Noetherianity follows from the actual finite normalization map. -/
theorem normalization_isLocallyNoetherian [IsLocallyNoetherian X]
    (hNagata : ∀ U : X.affineOpens, Nonempty U.1 → IsNagataRing.{u, 0} Γ(X, U.1)) :
    IsLocallyNoetherian (normalization X L) := by
  let : IsFinite (fromNormalization X L) := fromNormalization_isFinite X L hNagata
  exact LocallyOfFiniteType.isLocallyNoetherian (fromNormalization X L)

end FiniteExtension

end AlgebraicGeometry.Scheme.FiniteFunctionField
