/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Spec.CompletionLocalRing.Normal
public import Aglib.AlgebraicGeometry.Morphisms.Proper.BirationalFunctions
public import Aglib.AlgebraicGeometry.Morphisms.Proper.BirationalDVR
public import Aglib.AlgebraicGeometry.Properties.Normal.Affine
public import Aglib.AlgebraicGeometry.FunctionField.Restriction
public import Aglib.AlgebraicGeometry.RationalMap.QuasiDomination.ProtectedOverlap
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra

/-!
# The literal completed pullback of a supplied regular birational model

The original proper birational structure map proves the original section
bijection. Its actual completed pullback is integral and regular, and the
literal completed base is a normal domain. A genuine original isomorphism
open and its actual inverse image prove invertibility of the original
completed function-field map. No dimension hypothesis, completed-model
oracle or replacement model is used.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme.LocalRing

/-- A supplied regular proper birational model of a normal Noetherian local
domain remains such a model on its literal completed pullback. Normal-domain
completion, source integrality and the original completed function-field
isomorphism are conclusions, with no dimension or Nagata hypothesis. -/
theorem completedRegularModel_properties
    (A : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    [IsDomain A] [IsIntegrallyClosed A]
    {Y : Scheme.{u}} [IsIntegral Y]
    (f : Y ⟶ Spec (.of A)) [IsProper f] [IsDominant f]
    (hY : RegularStalks Y)
    (hff : IsIso (CommRingCat.ofHom (functionFieldMap f))) :
    let H := AdicCompletion (IsLocalRing.maximalIdeal A) A
    let W : Scheme.{u} := pullback f (completionSpecMap A)
    let g : W ⟶ Spec (.of H) := pullback.snd f (completionSpecMap A)
    ∃ hH : IsDomain H,
      letI := hH
      ∃ hW : IsIntegral W,
        letI := hW
        ∃ hg : IsDominant g,
          letI := hg
          IsIntegrallyClosed H ∧ RegularStalks W ∧ IsProper g ∧
            IsIso (CommRingCat.ofHom (functionFieldMap g)) := by
  let H := AdicCompletion (IsLocalRing.maximalIdeal A) A
  let c := completionSpecMap A
  let W : Scheme.{u} := pullback f c
  let g : W ⟶ Spec (.of H) := pullback.snd f c
  have hAN : NormalStalks (Spec (.of A)) :=
    fun x => (isIntegrallyClosed_and_isDomain_stalk_Spec A x).symm
  let : IsIso f.c := isIso_c_of_isProper_birational f hAN hff
  let : IsIso f.appTop := NatIso.isIso_app_of_isIso f.c (Opposite.op ⊤)
  have hbeta : Function.Bijective (properStructuralSectionsMap f) :=
    (ConcreteCategory.bijective_of_isIso f.appTop).comp
      (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of A)).inv)
  obtain ⟨hH, hHN⟩ := completion_normal_of_proper_regular_structuralSections A f hY hbeta
  let : IsDomain H := hH
  obtain ⟨hW, _hWN⟩ :=
    integral_normal_completionBaseChange_of_proper_regular_structuralSections A f hY hbeta
  let : IsIntegral W := hW
  let : IsProper g := inferInstance
  let hg : IsDominant g := inferInstance
  let : IsDominant g := hg
  have hWreg : RegularStalks W := (regularStalks_completionBaseChange_iff A f).mp hY
  let : Module.FaithfullyFlat A H := Module.FaithfullyFlat.of_flat_of_isLocalHom
  have hc : Flat c ∧ Surjective c := by
    apply (flat_and_surjective_SpecMap_iff (CommRingCat.ofHom (algebraMap A H))).mpr
    exact RingHom.faithfullyFlat_algebraMap_iff.mpr inferInstance
  let : Surjective c := hc.2
  let : ValuationRing ((Spec (.of A)).presheaf.stalk (genericPoint (Spec (.of A)))) :=
    inferInstanceAs (ValuationRing (Spec (.of A)).functionField)
  obtain ⟨U, hηU, hU⟩ := exists_isIso_restrict_of_isProper_birational_at_valuationRing
    f hff (genericPoint (Spec (.of A)))
  let : IsIso (f ∣_ U) := hU
  obtain ⟨z, hz⟩ := c.surjective (genericPoint (Spec (.of A)))
  let : Nonempty (c ⁻¹ᵁ U) := ⟨⟨z, by change c z ∈ U; rw [hz]; exact hηU⟩⟩
  have hgU : IsIso (g ∣_ c ⁻¹ᵁ U) := QuasiDomination.pullback_snd_restrict_isIso f c U
  have hgff : IsIso (CommRingCat.ofHom (functionFieldMap g)) :=
    Scheme.functionFieldMap_isIso_of_isIso_restrict g (c ⁻¹ᵁ U) hgU
  exact ⟨hH, hW, hg, hHN, hWreg, inferInstance, hgff⟩

end AlgebraicGeometry.Scheme.LocalRing
