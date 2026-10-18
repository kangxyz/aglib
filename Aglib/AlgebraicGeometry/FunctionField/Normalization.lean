/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.FunctionField.Basic
public import Aglib.AlgebraicGeometry.Properties.Normal.Affine
public import Mathlib.AlgebraicGeometry.Normalization

/-!
# Generic-fibre extensions from smooth schemes into integral morphisms

For an integral scheme with integrally closed stalks, the normalization of its canonical
generic inclusion is the original scheme. A generic map from a smooth scheme into an
integral morphism over the base then extends uniquely by relative normalization.
No Noetherian or dimension hypothesis is imposed.

## Extraction basis

Existing declarations from
`R5Lab/AlgebraicGeometry/FiniteEtale/Normalization/GenericFullFaithfulness.lean`, source revision
`79307ff88f07d34fd5c3edb859f799c55e38f290`, SHA-256
`56316f6517043fcd7e709e55d04765986ce74140b7d0d4e98e59a4648ec25c47`.
The source statements, binder universes, hypotheses and chosen maps are retained.
Direct Mathlib carriers/maps replace the recorded source wrappers; source-token correspondence
and those definitional substitutions are separate from native Lean validation.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option linter.style.haveILetI false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace

namespace AlgebraicGeometry.Scheme

universe u

variable (X : Scheme.{u}) [IsIntegral X]
  [∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x)]

/-- The normalization of the literal generic inclusion is the original
normal integral scheme. This is a conclusion from normal local rings,
not an assumed normalization or generic full-faithfulness input. -/
instance instIsIsoFromNormalizationFromSpecStalkGenericPoint :
    IsIso (X.fromSpecStalk (genericPoint X)).fromNormalization := by
  apply IsZariskiLocalAtTarget.of_forall_exists_morphismRestrict
    (P := .isomorphisms _) fun x => ?_
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, _⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open
    (Set.mem_univ x) isOpen_univ
  letI : Nonempty U := ⟨⟨x, hxU⟩⟩
  letI : IsIntegrallyClosed Γ(X, U) := isIntegrallyClosed_sections_of_isAffineOpen X U hU
  letI : IsFractionRing Γ(X, U) X.functionField :=
    functionField_isFractionRing_of_isAffineOpen X U hU
  letI := ((X.fromSpecStalk (genericPoint X)).app U).hom.toAlgebra
  let e : Γ(Spec X.functionField, (X.fromSpecStalk (genericPoint X)) ⁻¹ᵁ U) ≃ₐ[Γ(X, U)]
      X.functionField :=
    { (functionFieldSectionsIso X U).commRingCatIsoToRingEquiv with
      commutes' r := by
        exact congr($(fromSpecStalk_genericPoint_app_functionFieldSectionsIso X U) r) }
  have hbij : Function.Bijective (algebraMap Γ(X, U)
      (integralClosure Γ(X, U) Γ(Spec X.functionField, (X.fromSpecStalk (genericPoint X)) ⁻¹ᵁ U)))
          := by
    constructor
    · intro r s hrs
      apply IsFractionRing.injective Γ(X, U) X.functionField
      have h := congrArg (fun z => e z.val) hrs
      simpa only [Subalgebra.coe_algebraMap, e.commutes] using h
    · intro z
      obtain ⟨r, hr⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral
        (z.property.map e.toAlgHom)
      change algebraMap Γ(X, U) X.functionField r = e z.val at hr
      refine ⟨r, Subtype.ext (e.injective ?_)⟩
      change e (algebraMap Γ(X, U) Γ(Spec X.functionField, (X.fromSpecStalk (genericPoint X)) ⁻¹ᵁ U)
          r) = e z.val
      rw [e.commutes]
      exact hr
  haveI : IsIso (CommRingCat.ofHom (algebraMap Γ(X, U)
      (integralClosure Γ(X, U) Γ(Spec X.functionField, (X.fromSpecStalk (genericPoint X)) ⁻¹ᵁ U))))
          :=
    (ConcreteCategory.isIso_iff_bijective _).mpr hbij
  have happ : IsIso ((X.fromSpecStalk (genericPoint X)).fromNormalization.app U) := by
    rw [Scheme.Hom.fromNormalization_app _ hU]
    infer_instance
  exact ⟨U, hxU, (isIso_morphismRestrict_iff_isIso_app _ hU).mpr happ⟩

section Extension

variable {Y Z : Scheme.{u}} (p : Y ⟶ X) [Smooth p] (q : Z ⟶ X) [IsIntegralHom q]

/-- Smooth base change of the actual generic inclusion has normalization Y.
This is obtained from Mathlib's proved normalization base-change map. -/
instance instIsIsoFromNormalizationGenericPullback :
    IsIso (pullback.snd (X.fromSpecStalk (genericPoint X)) p).fromNormalization := by
  rw [← Scheme.Hom.normalizationPullback_snd]
  infer_instance

/-- Extend an actual generic map into an integral X-scheme. The underlying
source is a supplied smooth X-scheme, and both comparison squares are proved. -/
def extendFromGenericFiber (m : pullback (X.fromSpecStalk (genericPoint X)) p ⟶ Z)
    (hm : m ≫ q = pullback.snd (X.fromSpecStalk (genericPoint X)) p ≫ p) : Y ⟶ Z :=
  inv (pullback.snd (X.fromSpecStalk (genericPoint X)) p).fromNormalization ≫
    (pullback.snd (X.fromSpecStalk (genericPoint X)) p).normalizationDesc
      (pullback.lift m (pullback.snd (X.fromSpecStalk (genericPoint X)) p) hm)
      (pullback.snd q p) (by simp) ≫ pullback.fst q p

/-- The extension commutes with the given structural morphisms to the base. -/
theorem extendFromGenericFiber_over (m : pullback (X.fromSpecStalk (genericPoint X)) p ⟶ Z)
    (hm : m ≫ q = pullback.snd (X.fromSpecStalk (genericPoint X)) p ≫ p) :
    extendFromGenericFiber X p q m hm ≫ q = p := by
  simp only [extendFromGenericFiber, Category.assoc, pullback.condition]
  rw [← Category.assoc _ _ p, Scheme.Hom.normalizationDesc_comp]
  simp

/-- The extension restricts to the originally supplied generic-fibre map. -/
theorem extendFromGenericFiber_comp (m : pullback (X.fromSpecStalk (genericPoint X)) p ⟶ Z)
    (hm : m ≫ q = pullback.snd (X.fromSpecStalk (genericPoint X)) p ≫ p) :
    pullback.snd (X.fromSpecStalk (genericPoint X)) p ≫ extendFromGenericFiber X p q m hm = m := by
  have hi : pullback.snd (X.fromSpecStalk (genericPoint X)) p ≫
      inv (pullback.snd (X.fromSpecStalk (genericPoint X)) p).fromNormalization =
        (pullback.snd (X.fromSpecStalk (genericPoint X)) p).toNormalization := by
    calc
      _ = ((pullback.snd (X.fromSpecStalk (genericPoint X)) p).toNormalization ≫
          (pullback.snd (X.fromSpecStalk (genericPoint X)) p).fromNormalization) ≫
          inv (pullback.snd (X.fromSpecStalk (genericPoint X)) p).fromNormalization :=
        congrArg (fun f => f ≫ inv (pullback.snd (X.fromSpecStalk (genericPoint X))
            p).fromNormalization)
          (Scheme.Hom.toNormalization_fromNormalization
            (pullback.snd (X.fromSpecStalk (genericPoint X)) p)).symm
      _ = _ := by simp
  simp only [extendFromGenericFiber]
  rw [← Category.assoc, hi]
  simp only [Scheme.Hom.toNormalization_normalizationDesc_assoc, pullback.lift_fst]

/-- Uniqueness of the extension is proved from the actual normalization's
universal property, with no faithfulness instance as an input. -/
theorem genericFiber_hom_ext {f g : Y ⟶ Z} (hf : f ≫ q = p) (hg : g ≫ q = p)
    (h : pullback.snd (X.fromSpecStalk (genericPoint X)) p ≫ f =
      pullback.snd (X.fromSpecStalk (genericPoint X)) p ≫ g) : f = g := by
  let jf := pullback.lift f (𝟙 Y) (by simpa using hf)
  let jg := pullback.lift g (𝟙 Y) (by simpa using hg)
  have hj : (pullback.snd (X.fromSpecStalk (genericPoint X)) p).fromNormalization ≫ jf =
      (pullback.snd (X.fromSpecStalk (genericPoint X)) p).fromNormalization ≫ jg := by
    apply Scheme.Hom.normalization.hom_ext
      (pullback.snd (X.fromSpecStalk (genericPoint X)) p) _ _ (pullback.snd q p)
    · simp only [← Category.assoc, Scheme.Hom.toNormalization_fromNormalization]
      apply pullback.hom_ext
      · simpa [jf, jg] using h
      · simp [jf, jg]
    · simp [jf]
    · simp [jg]
  have he : jf = jg := (cancel_epi _).mp hj
  simpa [jf, jg] using congrArg (fun j => j ≫ pullback.fst q p) he

/-- Every map on the literal generic pullback has exactly one extension
between the supplied schemes, including its actual X-square. -/
theorem existsUnique_extensionFromGenericFiber (m : pullback (X.fromSpecStalk (genericPoint X)) p ⟶
    Z)
    (hm : m ≫ q = pullback.snd (X.fromSpecStalk (genericPoint X)) p ≫ p) :
    ∃! f : Y ⟶ Z, f ≫ q = p ∧ pullback.snd (X.fromSpecStalk (genericPoint X)) p ≫ f = m := by
  refine ⟨extendFromGenericFiber X p q m hm,
    ⟨extendFromGenericFiber_over X p q m hm, extendFromGenericFiber_comp X p q m hm⟩, ?_⟩
  intro f hf
  apply genericFiber_hom_ext X p q hf.1 (extendFromGenericFiber_over X p q m hm)
  exact hf.2.trans (extendFromGenericFiber_comp X p q m hm).symm

end Extension

end AlgebraicGeometry.Scheme
