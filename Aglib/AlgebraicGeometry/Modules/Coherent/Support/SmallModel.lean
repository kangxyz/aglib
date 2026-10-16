/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Coherent.Restriction
public import Aglib.CategoryTheory.SmallModel.Functor
public import Aglib.CategoryTheory.SmallModel.Abelian
public import Aglib.CategoryTheory.Abelian.Subcategory.Exact

/-!
# Small presentations of supported coherent sheaves

The kernel of the actual small-model restriction agrees with geometric closed support. The
chosen SmallModel.{u + 1} presentations give the support equivalence, exact inclusion comparison
and their literal commuting square.
-/

/-!
Source: frozen dirty Quillen `6db56ddd3fdb898ef5de29d5fe51a0c61f9ba116`.
`Quillen/AlgebraicGeometry/Scheme/Coherent/GlobalLocalizationSupport.lean`.
SHA-256: `29edb8f24f2d55b6e054d5872530fa31214916a9b1914efaacf6ece7fb71cb59`.
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
variable {U X : Scheme.{u}} [IsLocallyNoetherian X] [IsLocallyNoetherian U]
  (j : U ⟶ X) [IsOpenImmersion j]

/-- Actual global coherent restriction in the upper-universe small models. -/
abbrev coherentGlobalSmallRestriction :=
  CategoryTheory.SmallModel.functor.{u + 1} (finiteTypeSheavesRestriction j)

/-- Its actual kernel property. -/
abbrev coherentGlobalSmallSupport := (coherentGlobalSmallRestriction j).kernel

omit [IsLocallyNoetherian X] in
/-- Membership means that the represented actual sheaf vanishes on the open. -/
theorem coherentGlobalSmallSupport_iff (M : SmallModel.{u + 1} (FiniteTypeSheaves X)) :
    coherentGlobalSmallSupport j M ↔
      finiteTypeSheavesSupportedAway j
        ((equivSmallModel.{u + 1} (FiniteTypeSheaves X)).inverse.obj M) := by
  have h := CategoryTheory.SmallModel.kernel_iff.{u + 1}
    (finiteTypeSheavesRestriction j) M
  rw [finiteTypeSheavesRestriction_kernel_eq_support] at h
  exact h

/-- The compatible support category is an actual small presentation of the
geometric supported coherent category. -/
def coherentGlobalSmallSupportEquivalence :
    (coherentGlobalSmallSupport j).FullSubcategory ≌
      SupportedFiniteTypeSheaves j :=
  (equivSmallModel.{u + 1} (FiniteTypeSheaves X)).symm.congrFullSubcategory (by
    funext M
    apply propext
    exact (coherentGlobalSmallSupport_iff j M).symm)

/-- This actual small support presentation commutes with the original
geometric inclusion of supported coherent sheaves. -/
theorem coherentGlobalSmallSupportEquivalence_comp_inclusion :
    (coherentGlobalSmallSupportEquivalence j).functor ⋙ (finiteTypeSheavesSupportedAway j).ι =
      (coherentGlobalSmallSupport j).ι ⋙
        (equivSmallModel.{u + 1} (FiniteTypeSheaves X)).inverse := rfl

/-- The genuine exact inclusion of actual supported coherent sheaves. -/
def supportedCoherentInclusionExact :
    ExactFunctor (supportedCoherentExactStructure j) (coherentExactStructure X) :=
  CategoryTheory.ObjectProperty.exactInclusion (finiteTypeSheavesSupportedAway j)

/-- The compatible support category is abelian under the actual noetherian
hypotheses, using its Serre-class closure properties. -/
instance instAbelianCoherentGlobalSmallSupport :
    Abelian (coherentGlobalSmallSupport j).FullSubcategory :=
  CategoryTheory.ObjectProperty.subcategoryAbelian (coherentGlobalSmallSupport j)

/-- The comparison between the two actual small support presentations. -/
def coherentGlobalSupportSmallModelEquivalence :
    SmallModel.{u + 1} (SupportedFiniteTypeSheaves j) ≌
      (coherentGlobalSmallSupport j).FullSubcategory :=
  (equivSmallModel.{u + 1} (SupportedFiniteTypeSheaves j)).symm.trans
    (coherentGlobalSmallSupportEquivalence j).symm

/-- The original small support comparison functor is additive. -/
instance coherentGlobalSupportSmallModelEquivalence_additive :
    (coherentGlobalSupportSmallModelEquivalence j).functor.Additive := by
  let := preservesBinaryBiproducts_of_preservesBinaryProducts
    (coherentGlobalSupportSmallModelEquivalence j).functor
  exact Functor.additive_of_preservesBinaryBiproducts _

/-- The exact comparison of support presentations. -/
def coherentGlobalSupportComparison :
    ExactFunctor (supportedCoherentExactStructure j).smallModel
      (abelianExactStructure (coherentGlobalSmallSupport j).FullSubcategory) where
  toFunctor := (coherentGlobalSupportSmallModelEquivalence j).functor
  map_conflation S h := by
    change (abelianExactStructure (SupportedFiniteTypeSheaves j)).smallModel.conflation S at h
    rw [abelianExactStructure_smallModel] at h
    exact h.map_of_exact _

/-- The comparison square is the actual support inclusion square, already
at the level of exact functors, before applying K-theory. -/
theorem coherentGlobalSupportComparison_comp_inclusion :
    (coherentGlobalSupportComparison j).comp
        (CategoryTheory.ObjectProperty.exactInclusion (coherentGlobalSmallSupport j)) =
      (supportedCoherentInclusionExact j).smallModel.comp
        (CategoryTheory.SmallModel.abelianExactComparison.{u + 1} (FiniteTypeSheaves X)) := rfl

/-- The exact support comparison has the original equivalence as its underlying functor. -/
instance coherentGlobalSupportComparison_isEquivalence :
    (coherentGlobalSupportComparison j).toFunctor.IsEquivalence :=
  (coherentGlobalSupportSmallModelEquivalence j).isEquivalence_functor

end AlgebraicGeometry.Scheme.Modules.Coherent
