/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Coherent.Localization.Fullness
public import Aglib.AlgebraicGeometry.Modules.Coherent.Extension.Noetherian

/-!
# Coherent localization by closed support

Essential surjectivity of restriction implies equivalence of its support quotient and the open
coherent category. On a Noetherian scheme coherent extension supplies essential surjectivity,
giving the ordinary Serre localization.
-/

/-!
Source: frozen dirty Quillen `6db56ddd3fdb898ef5de29d5fe51a0c61f9ba116`.
`Quillen/AlgebraicGeometry/Scheme/Coherent/GlobalLocalizationQuotient.lean`.
SHA-256: `84c4256b0f55dcd507885fade768b622aeb5727185f58bb52bd61b754662b633`.
`Quillen/AlgebraicGeometry/Scheme/Coherent/GlobalLocalization.lean`.
SHA-256: `f92ecc4ad2506e2fd4c98716cfbf4a983e8a4492685c754e9995ed4eca37d54a`.
Selected original statements and proofs; canonical lower APIs replace the recorded source wrappers.
-/

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u v
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open ModuleCat
open AlgebraicGeometry.Scheme.Modules
attribute [local instance] Abelian.hasFiniteBiproducts
open AlgebraicGeometry.Scheme.Modules.QuasiCoherent
open CategoryTheory.ExactCategory
namespace AlgebraicGeometry.Scheme.Modules.Coherent

section
variable {U X : Scheme.{u}} [IsLocallyNoetherian X] [IsLocallyNoetherian U]
  (j : U ⟶ X) [IsOpenImmersion j]
variable [(finiteTypeSheavesRestriction j).EssSurj]

/-- Actual coherent object extension descends to essential surjectivity of
the canonical functor from the support quotient. -/
theorem quotientCoherentRestriction_essSurj_of_restriction :
    (quotientCoherentRestriction j).EssSurj where
  mem_essImage A := by
    obtain ⟨M, ⟨e⟩⟩ := Functor.EssSurj.mem_essImage (finiteTypeSheavesRestriction j) A
    refine ⟨(finiteTypeSheavesSupportedAway j).isoModSerre.Q.obj M, ⟨?_⟩⟩
    exact (quotientCoherentRestrictionFactorsIso j).app M ≪≫ e

/-- The full, faithful actual quotient functor is an equivalence once
actual coherent extension is known. -/
theorem quotientCoherentRestriction_isEquivalence_of_essSurj :
    (quotientCoherentRestriction j).IsEquivalence where
  essSurj := quotientCoherentRestriction_essSurj_of_restriction j

/-- The original geometric restriction is localization by actual coherent
support, using the equivalence of its constructed quotient. -/
theorem finiteTypeSheavesRestriction_isLocalization_of_essSurj :
    (finiteTypeSheavesRestriction j).IsLocalization
      (finiteTypeSheavesSupportedAway j).isoModSerre := by
  let := quotientCoherentRestriction_isEquivalence_of_essSurj j
  exact Functor.IsLocalization.of_equivalence_target
    (finiteTypeSheavesSupportedAway j).isoModSerre.Q (finiteTypeSheavesSupportedAway j).isoModSerre
    (finiteTypeSheavesRestriction j) (quotientCoherentRestriction j).asEquivalence
    (quotientCoherentRestrictionFactorsIso j)

/-- Equivalently, actual open restriction is localization by its kernel. -/
theorem finiteTypeSheavesRestriction_isLocalization_kernel_of_essSurj :
    (finiteTypeSheavesRestriction j).IsLocalization
      (finiteTypeSheavesRestriction j).kernel.isoModSerre := by
  have h : (finiteTypeSheavesRestriction j).kernel.isoModSerre =
      (finiteTypeSheavesSupportedAway j).isoModSerre := by
    funext M N f
    apply propext
    change ((finiteTypeSheavesRestriction j).kernel (kernel f) ∧
      (finiteTypeSheavesRestriction j).kernel (cokernel f)) ↔ _
    rw [finiteTypeSheavesRestriction_kernel_eq_support]
    rfl
  rw [h]
  exact finiteTypeSheavesRestriction_isLocalization_of_essSurj j

end

section
variable {U X : Scheme.{u}} [IsNoetherian X]
  [IsLocallyNoetherian U] (j : U ⟶ X) [IsOpenImmersion j]

/-- The actual supported quotient is essentially surjective by coherent
object extension from the open. -/
instance quotientCoherentRestriction_essSurj :
    (quotientCoherentRestriction j).EssSurj :=
  quotientCoherentRestriction_essSurj_of_restriction j

/-- The canonical functor from the actual coherent support quotient to the
open is an equivalence, by proved fullness, faithfulness and extension. -/
instance quotientCoherentRestriction_isEquivalence :
    (quotientCoherentRestriction j).IsEquivalence :=
  quotientCoherentRestriction_isEquivalence_of_essSurj j

/-- The actual geometric equivalence between the supported Serre quotient
and coherent sheaves on the open. -/
def coherentSupportQuotientEquivalence : CoherentSupportQuotient j ≌ FiniteTypeSheaves U :=
  (quotientCoherentRestriction j).asEquivalence

/-- Actual restriction of coherent sheaves is the Serre localization by
sheaves whose ordinary stalk support lies outside the open. -/
instance finiteTypeSheavesRestriction_isLocalization :
    (finiteTypeSheavesRestriction j).IsLocalization
      (finiteTypeSheavesSupportedAway j).isoModSerre :=
  finiteTypeSheavesRestriction_isLocalization_of_essSurj j

/-- The same actual geometric localization, expressed by its kernel. -/
instance finiteTypeSheavesRestriction_isLocalization_kernel :
    (finiteTypeSheavesRestriction j).IsLocalization
      (finiteTypeSheavesRestriction j).kernel.isoModSerre :=
  finiteTypeSheavesRestriction_isLocalization_kernel_of_essSurj j

local instance : PreservesFiniteLimits (coherentRestrictionExact j).toFunctor :=
  finiteTypeSheavesRestriction_preservesFiniteLimits j

local instance : PreservesFiniteColimits (coherentRestrictionExact j).toFunctor :=
  finiteTypeSheavesRestriction_preservesFiniteColimits j

local instance : (coherentRestrictionExact j).toFunctor.IsLocalization
    (coherentRestrictionExact j).toFunctor.kernel.isoModSerre :=
  finiteTypeSheavesRestriction_isLocalization_kernel j

end

end AlgebraicGeometry.Scheme.Modules.Coherent
