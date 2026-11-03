/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.FunctionField.AffineCharts
public import Aglib.AlgebraicGeometry.Properties.Normal.Basic
public import Aglib.AlgebraicGeometry.Stalk.FlatBaseChange
public import Aglib.RingTheory.Nagata.Normalization
public import Mathlib.AlgebraicGeometry.Normalization
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed

/-!
# Normalization in the original function field

For an integral scheme W, normalize the literal generic inclusion
`W.fromSpecStalk (genericPoint W)`. Its normalization is integral and
normal, and its original structural morphism is dominant and induces
an isomorphism of the actual function fields.

Nagata properties of the actual nonempty affine section rings make this
original morphism finite. The construction uses `normalizationObjIso`
and `fromNormalization_app` with their original coefficient maps.

The current consumer is the normalization of the schematic image of a
punctured complementary section in the general-surface resolution argument.
The consumer must supply its actual affine chart Nagata data.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace

namespace AlgebraicGeometry.Scheme

universe u

variable (W : Scheme.{u}) [IsIntegral W]

local notation "γ" => W.fromSpecStalk (genericPoint W)

/-- The actual coefficient ring used by relative normalization is a
fraction ring of the actual affine chart, through its original structural
map. The algebra-equivalence compatibility is the original germ equation. -/
private theorem genericSection_isFractionRing
    (U : W.Opens) (hU : IsAffineOpen U) [Nonempty U] :
    letI := ((γ).app U).hom.toAlgebra
    IsFractionRing Γ(W, U) Γ(Spec W.functionField, γ ⁻¹ᵁ U) := by
  let := ((γ).app U).hom.toAlgebra
  let : IsFractionRing Γ(W, U) W.functionField :=
    AlgebraicGeometry.functionField_isFractionRing_of_isAffineOpen W U hU
  let e : Γ(Spec W.functionField, γ ⁻¹ᵁ U) ≃ₐ[Γ(W, U)] W.functionField :=
    { (Scheme.functionFieldSectionsIso W U).commRingCatIsoToRingEquiv with
      commutes' r := by
        exact congr($(Scheme.fromSpecStalk_genericPoint_app_functionFieldSectionsIso W U) r) }
  exact IsFractionRing.of_algEquiv e.symm

/-- The actual affine normalization section ring is a normal domain.
This uses integral closure in the actual fraction ring, with no finiteness
or openness of a normal locus. -/
private theorem genericNormalization_sections_normal
    (U : W.Opens) (hU : IsAffineOpen U) [Nonempty U] :
    IsDomain Γ((γ).normalization, (γ).fromNormalization ⁻¹ᵁ U) ∧
      IsIntegrallyClosed Γ((γ).normalization, (γ).fromNormalization ⁻¹ᵁ U) := by
  let := ((γ).app U).hom.toAlgebra
  let : IsFractionRing Γ(W, U) Γ(Spec W.functionField, γ ⁻¹ᵁ U) :=
    genericSection_isFractionRing W U hU
  let : Field Γ(Spec W.functionField, γ ⁻¹ᵁ U) :=
    IsFractionRing.toField Γ(W, U)
  let : IsIntegrallyClosed (integralClosure Γ(W, U)
      Γ(Spec W.functionField, γ ⁻¹ᵁ U)) :=
    integralClosure.isIntegrallyClosedOfFiniteExtension
      (R := Γ(W, U)) Γ(Spec W.functionField, γ ⁻¹ᵁ U)
        (L := Γ(Spec W.functionField, γ ⁻¹ᵁ U))
  let e := ((γ).normalizationObjIso hU).commRingCatIsoToRingEquiv
  exact ⟨Function.Injective.isDomain e.toRingHom e.injective,
    IsIntegrallyClosed.of_equiv e.symm⟩

/-- Localizing the literal normal affine closures makes the actual
normalization normal at every stalk. -/
theorem genericNormalization_normalStalks : Scheme.NormalStalks (γ).normalization := by
  intro n
  obtain ⟨_, ⟨U, hU, rfl⟩, hnU, _⟩ := W.isBasis_affineOpens.exists_subset_of_mem_open
    (Set.mem_univ ((γ).fromNormalization n)) isOpen_univ
  let : Nonempty U := ⟨⟨(γ).fromNormalization n, hnU⟩⟩
  let V := (γ).fromNormalization ⁻¹ᵁ U
  have hV : IsAffineOpen V := hU.preimage (γ).fromNormalization
  obtain ⟨hdom, hnormal⟩ := genericNormalization_sections_normal W U hU
  let : IsDomain Γ((γ).normalization, V) := hdom
  let : IsIntegrallyClosed Γ((γ).normalization, V) := hnormal
  let : Algebra Γ((γ).normalization, V) ((γ).normalization.presheaf.stalk n) :=
    TopCat.Presheaf.algebra_section_stalk (γ).normalization.presheaf ⟨n, hnU⟩
  let p := hV.primeIdealOf ⟨n, hnU⟩
  let : IsLocalization.AtPrime ((γ).normalization.presheaf.stalk n) p.asIdeal :=
    hV.isLocalization_stalk ⟨n, hnU⟩
  refine ⟨inferInstance, ?_⟩
  exact isIntegrallyClosed_of_isLocalization ((γ).normalization.presheaf.stalk n)
    p.asIdeal.primeCompl p.asIdeal.primeCompl_le_nonZeroDivisors

/-- The generic-point inclusion induces an isomorphism on the original
function fields, by its actual stalk map. -/
theorem genericInclusion_fieldMap_isIso :
    IsIso (CommRingCat.ofHom (Scheme.functionFieldMap γ)) := by
  let : Flat γ := Scheme.fromSpecStalk_flat W (genericPoint W)
  let : IsIso ((γ).stalkMap (genericPoint (Spec W.functionField))) :=
    Scheme.Hom.isIso_stalkMap_of_flat_of_surjectiveOnStalks
      γ (genericPoint (Spec W.functionField))
  change IsIso (W.presheaf.stalkSpecializes _ ≫
    (γ).stalkMap (genericPoint (Spec W.functionField)))
  have he : W.presheaf.stalkSpecializes
      (specializes_of_eq (Scheme.map_genericPoint_of_isDominant (Spec W.functionField) γ)) =
      (W.presheaf.stalkCongr (.of_eq
        (Scheme.map_genericPoint_of_isDominant (Spec W.functionField) γ).symm)).hom := rfl
  rw [he]
  infer_instance

/-- The original normalization map is dominant, using its actual
factorization of the original generic-point inclusion. -/
theorem genericNormalization_isDominant : IsDominant (γ).fromNormalization := by
  let : IsDominant ((γ).toNormalization ≫ (γ).fromNormalization) := by
    rw [Scheme.Hom.toNormalization_fromNormalization]
    infer_instance
  exact IsDominant.of_comp (γ).toNormalization (γ).fromNormalization

/-- Birationality is on the original normalization map. The proof cancels
the actual injective field map of toNormalization from the original
factorization, rather than choosing a new fraction-field equivalence. -/
theorem genericNormalization_fieldMap_isIso :
    letI := genericNormalization_isDominant W
    IsIso (CommRingCat.ofHom (Scheme.functionFieldMap (γ).fromNormalization)) := by
  let := genericNormalization_isDominant W
  let : IsIso (CommRingCat.ofHom (Scheme.functionFieldMap γ)) :=
    genericInclusion_fieldMap_isIso W
  have hcongr {a b : Spec W.functionField ⟶ W}
      [IsDominant a] [IsDominant b] (hab : a = b) :
      Scheme.functionFieldMap a = Scheme.functionFieldMap b := by
    subst b
    rfl
  have hmap : (Scheme.functionFieldMap (γ).toNormalization).comp
      (Scheme.functionFieldMap (γ).fromNormalization) =
      Scheme.functionFieldMap γ :=
    (Scheme.functionFieldMap_comp (γ).toNormalization (γ).fromNormalization).symm.trans
      (hcongr (Scheme.Hom.toNormalization_fromNormalization γ))
  apply (ConcreteCategory.isIso_iff_bijective _).mpr
  refine ⟨(Scheme.functionFieldMap (γ).fromNormalization).injective, ?_⟩
  intro y
  obtain ⟨x, hx⟩ := (ConcreteCategory.bijective_of_isIso
    (CommRingCat.ofHom (Scheme.functionFieldMap γ))).2
      (Scheme.functionFieldMap (γ).toNormalization y)
  refine ⟨x, (Scheme.functionFieldMap (γ).toNormalization).injective ?_⟩
  change ((Scheme.functionFieldMap (γ).toNormalization).comp
    (Scheme.functionFieldMap (γ).fromNormalization)) x = _
  exact (RingHom.congr_fun hmap x).trans hx

/-- A nonempty actual affine chart contributes a finite original
normalization map on sections. No replacement closure or scalar action is
introduced. -/
private theorem genericNormalization_finite_app
    (U : W.Opens) (hU : IsAffineOpen U) [Nonempty U]
    (hB : IsNagataRing.{u, 0} Γ(W, U)) :
    (((γ).fromNormalization).app U).hom.Finite := by
  let := ((γ).app U).hom.toAlgebra
  let : IsFractionRing Γ(W, U) Γ(Spec W.functionField, γ ⁻¹ᵁ U) :=
    genericSection_isFractionRing W U hU
  let : Module.Finite Γ(W, U)
      (integralClosure Γ(W, U) Γ(Spec W.functionField, γ ⁻¹ᵁ U)) :=
    integralClosure.finite_of_isNagataRing Γ(W, U) hB
      Γ(Spec W.functionField, γ ⁻¹ᵁ U)
  rw [Scheme.Hom.fromNormalization_app _ hU]
  exact (RingHom.Finite.of_surjective _
    (ConcreteCategory.bijective_of_isIso ((γ).normalizationObjIso hU).inv).2).comp
      (RingHom.finite_algebraMap.mpr
        (inferInstanceAs (Module.Finite Γ(W, U)
          (integralClosure Γ(W, U) Γ(Spec W.functionField, γ ⁻¹ᵁ U)))))

/-- Finiteness of the actual generic normalization follows from Nagata
properties of the actual nonempty affine chart rings. The empty chart is
handled as the literal zero-ring section map. -/
theorem genericNormalization_isFinite
    (hNagata : ∀ U : W.affineOpens, Nonempty U.1 → IsNagataRing.{u, 0} Γ(W, U.1)) :
    IsFinite (γ).fromNormalization := by
  refine { toIsAffineHom := inferInstance, finite_app := ?_ }
  intro U hU
  by_cases hne : Nonempty U
  · let := hne
    exact genericNormalization_finite_app W U hU (hNagata ⟨U, hU⟩ hne)
  · have hbot : U = ⊥ := by
      apply le_antisymm
      · intro x hx
        exact (hne ⟨⟨x, hx⟩⟩).elim
      · exact bot_le
    subst U
    let : Subsingleton Γ((γ).normalization, (γ).fromNormalization ⁻¹ᵁ ⊥) := by
      simpa only [Scheme.Hom.preimage_bot] using
        (inferInstanceAs (Subsingleton Γ((γ).normalization, ⊥)))
    exact RingHom.Finite.of_surjective _ (Function.surjective_to_subsingleton _)

end AlgebraicGeometry.Scheme
