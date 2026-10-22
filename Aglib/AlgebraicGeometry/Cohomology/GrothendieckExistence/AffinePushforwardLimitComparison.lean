/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.GrothendieckExistence.AffinePushforwardFormalFunctions
public import Aglib.Algebra.Category.ModuleCat.NatTowerExactUniverses

/-! # Identification of the ORIGINAL comparison limit with formal functions

Bijectivity belongs to the whole compatible-family map. No injectivity or
invertibility of an individual finite-stage comparison is used.
-/

@[expose] public noncomputable section
open CategoryTheory Opposite
namespace AlgebraicGeometry.Scheme.Modules.Coherent
universe u
variable {B : CommRingCat.{u}} [IsNoetherianRing B]
  {Y : Scheme.{u}} [IsLocallyNoetherian Y]
  (p : Y ⟶ Spec B) [IsProper p] (J : Ideal B) (G : Y.CoherentSheaf)

local instance : G.obj.IsQuasicoherent :=
  QuasiCoherent.quasicoherent_of_affineCharts _ (fun R j _ => (G.property R j).1)

omit [IsNoetherianRing B] [IsProper p] in
/-- On original classes, the tower coordinate is the original quotient map. -/
theorem affinePushforwardReduction_map (n : ℕ) :
    moduleSpecΓFunctor.map ((pushforward p).map
      ((idealSheafQuotientUnit Y (idealThickeningIdealSheaf p J ^ n)).app G.obj)) ≫
        (affinePushforwardQuotientTowerIso p J G).hom.app (op n) =
      (Cohomology.pushforwardSpecSectionsIso p).hom.app G.obj ≫
        (Cohomology.moduleGlobalSectionsFunctorOfHom Y
          (Cohomology.affineFormalFunctionsScalar p)).map
            (idealQuotientπ Y (idealThickeningBaseScalar p) G.obj (J ^ n)) := by
  have hu : (idealSheafQuotientUnit Y (idealThickeningIdealSheaf p J ^ n)).app G.obj ≫
      (Cohomology.idealPowerQuotientIdealSheafIso p J G.obj n).inv =
        idealQuotientπ Y (idealThickeningBaseScalar p) G.obj (J ^ n) := by
    rw [← Cohomology.idealQuotientπ_idealSheafIso_hom p J G.obj n]
    simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  change moduleSpecΓFunctor.map ((pushforward p).map _) ≫
    (moduleSpecΓFunctor.map ((pushforward p).map
      (Cohomology.idealPowerQuotientIdealSheafIso p J G.obj n).inv) ≫
        (Cohomology.pushforwardSpecSectionsIso p).hom.app _) = _
  rw [← Category.assoc, ← Functor.map_comp, ← Functor.map_comp, hu]
  exact (Cohomology.pushforwardSpecSectionsIso p).hom.naturality _

/-- Apply the native section-map constructor while the diagrams remain abstract. -/
def originalDiagramSectionsMap {R : Type*} [Ring R]
    {C : Type*} [Category C] {F G : C ⥤ ModuleCat R} (ψ : F ⟶ G) :
    ModuleCat.sectionsSubmodule F →ₗ[R] ModuleCat.sectionsSubmodule G :=
  ModuleCat.sectionsMapOfLinearMaps (fun j => (ψ.app j).hom)
    (fun a x => ConcreteCategory.congr_hom (ψ.naturality a) x)

/-- Compare native compatible families using the whole original unit certificate. -/
theorem originalDiagramSectionsMap_eq {R : Type*} [Ring R]
    {F G H : ℕᵒᵖ ⥤ ModuleCat R} (M : ModuleCat R)
    (u : ∀ n, M ⟶ F.obj (op n)) (v : ∀ n, M ⟶ G.obj (op n))
    (w : ∀ n, M ⟶ H.obj (op n))
    (c : {ψ : F ⟶ G // ∀ n, u n ≫ ψ.app (op n) = v n}) (e : G ≅ H)
    (s : ModuleCat.sectionsSubmodule F) (t : ModuleCat.sectionsSubmodule G) (x : M)
    (hs : ∀ n, s.val (op n) = u n x)
    (hv : ∀ n, v n ≫ e.hom.app (op n) = w n)
    (ht : ∀ n, (ModuleCat.sectionsSubmoduleCongr e t).val (op n) = w n x) :
    originalDiagramSectionsMap c.val s = t := by
  apply (ModuleCat.sectionsSubmoduleCongr e).injective
  apply Subtype.ext
  funext j
  change e.hom.app j (c.val.app j (s.val j)) = _
  rw [hs j.unop]
  change (u j.unop ≫ c.val.app j ≫ e.hom.app j) x = _
  rw [← Category.assoc, c.property, hv]
  exact (ht j.unop).symm

/-- Literal bijectivity, with the native linear map's carriers kept abstract. -/
def originalLimitBijective {R : Type*} [Semiring R]
    {P Q : Type*} [AddCommMonoid P] [Module R P] [AddCommMonoid Q] [Module R Q]
    (m : P →ₗ[R] Q) : Prop := Function.Bijective m

/-- The original map agrees with the completion equivalence and is bijective. -/
def originalCompletionComparison {R : Type*} [CommRing R] (I : Ideal R)
    (M : ModuleCat R) {P Q : Type*}
    [AddCommGroup P] [Module R P] [AddCommGroup Q] [Module R Q]
    (e₀ : AdicCompletion I M ≃ₗ[R] P) (e₁ : AdicCompletion I M ≃ₗ[R] Q)
    (m : P →ₗ[R] Q) : Prop :=
  m.comp e₀.toLinearMap = e₁.toLinearMap ∧ originalLimitBijective m

/-- Density of the original module identifies the actual whole-family map. -/
theorem originalCompletionComparison_of {R : Type*} [CommRing R] (I : Ideal R) (hI : I.FG)
    (M : ModuleCat R) {P Q : Type*}
    [AddCommGroup P] [Module R P] [AddCommGroup Q] [Module R Q]
    (e₀ : AdicCompletion I M ≃ₗ[R] P) (e₁ : AdicCompletion I M ≃ₗ[R] Q)
    (m : P →ₗ[R] Q)
    (h : ∀ x : M, m (e₀ (AdicCompletion.of I M x)) = e₁ (AdicCompletion.of I M x)) :
    originalCompletionComparison I M e₀ e₁ m := by
  let := AdicCompletion.isAdicComplete (M := M) hI
  have he : m.comp e₀.toLinearMap = e₁.toLinearMap := by
    have hh : e₁.symm.toLinearMap.comp (m.comp e₀.toLinearMap) =
        e₁.symm.toLinearMap.comp e₁.toLinearMap := by
      apply AdicCompletion.linearMap_ext_of I hI
      intro x
      exact congrArg e₁.symm (h x)
    apply LinearMap.ext
    intro x
    exact e₁.symm.injective (LinearMap.congr_fun hh x)
  refine ⟨he, ?_⟩
  have hb : Function.Bijective (m.comp e₀.toLinearMap) := by
    rw [he]
    exact e₁.bijective
  exact ⟨fun x y hxy => by
    obtain ⟨a, rfl⟩ := e₀.surjective x
    obtain ⟨b, rfl⟩ := e₀.surjective y
    exact congrArg e₀ (hb.injective hxy), fun y => by
      obtain ⟨x, hx⟩ := hb.surjective y
      exact ⟨e₀ x, hx⟩⟩

/-- Construct the actual native map and all original completion certificates together. -/
def originalDiagramLimitComparison {R : Type*} [CommRing R]
    (I : Ideal R) (hI : I.FG) (M : ModuleCat R)
    {F G H : ℕᵒᵖ ⥤ ModuleCat R}
    (u : ∀ n, M ⟶ F.obj (op n)) (v : ∀ n, M ⟶ G.obj (op n))
    (w : ∀ n, M ⟶ H.obj (op n))
    (c : {ψ : F ⟶ G // ∀ n, u n ≫ ψ.app (op n) = v n}) (e : G ≅ H)
    (e₀ : AdicCompletion I M ≃ₗ[R] ModuleCat.sectionsSubmodule F)
    (e₁ : AdicCompletion I M ≃ₗ[R] ModuleCat.sectionsSubmodule G)
    (hs : ∀ x n, (e₀ (AdicCompletion.of I M x)).val (op n) = u n x)
    (hv : ∀ n, v n ≫ e.hom.app (op n) = w n)
    (ht : ∀ x n, (ModuleCat.sectionsSubmoduleCongr e
      (e₁ (AdicCompletion.of I M x))).val (op n) = w n x) :
    {m : ModuleCat.sectionsSubmodule F →ₗ[R] ModuleCat.sectionsSubmodule G //
      originalCompletionComparison I M e₀ e₁ m ∧ m = originalDiagramSectionsMap c.val} :=
  ⟨originalDiagramSectionsMap c.val,
    originalCompletionComparison_of I hI M e₀ e₁ _
      (fun x => originalDiagramSectionsMap_eq M u v w c e _ _ x (hs x) hv (ht x)), rfl⟩

/-- Keep bijectivity on the specified original map, not just an isomorphic replacement. -/
theorem originalDiagramLimitComparison_bijective {R : Type*} [CommRing R]
    (I : Ideal R) (M : ModuleCat R) {P Q : Type*}
    [AddCommGroup P] [Module R P] [AddCommGroup Q] [Module R Q]
    (e₀ : AdicCompletion I M ≃ₗ[R] P) (e₁ : AdicCompletion I M ≃ₗ[R] Q)
    (m₀ : P →ₗ[R] Q)
    (c : {m : P →ₗ[R] Q // originalCompletionComparison I M e₀ e₁ m ∧ m = m₀}) :
    originalLimitBijective m₀ := c.property.2 ▸ c.property.1.2

/-- The original affine limit map, its formal-functions equation and literal-map identity. -/
def affinePushforwardLimitComparisonData :
    {m : ((completionFunctor (Spec B) (idealThickeningIdealSheaf (𝟙 (Spec B)) J)).obj
        (properPushforwardCoefficient p G)).affineFormalSections →ₗ[B]
        ModuleCat.sectionsSubmodule (affinePushforwardCompletionTower p J G) //
      originalCompletionComparison J
        (moduleSpecΓFunctor.obj ((pushforward p).obj G.obj))
        (generatedCompletionSectionsEquiv B (properPushforwardCoefficient p G) J)
        (affinePushforwardFormalFunctionsEquiv p J G) m ∧
      m = originalDiagramSectionsMap (affinePushforwardComparison p J G)} :=
  originalDiagramLimitComparison J (IsNoetherian.noetherian J)
    (moduleSpecΓFunctor.obj ((pushforward p).obj G.obj))
    (F := ((completionFunctor (Spec B) (idealThickeningIdealSheaf (𝟙 (Spec B)) J)).obj
      (properPushforwardCoefficient p G)).affineSectionsTower)
    (G := affinePushforwardCompletionTower p J G)
    (H := Cohomology.idealPowerQuotientGlobalSections Y
      (Cohomology.affineFormalFunctionsScalar p) G.obj J)
    (fun n => moduleSpecΓFunctor.map ((idealSheafQuotientUnit (Spec B)
      (idealThickeningIdealSheaf (𝟙 (Spec B)) J ^ n)).app ((pushforward p).obj G.obj)))
    (fun n => moduleSpecΓFunctor.map ((pushforward p).map
      ((idealSheafQuotientUnit Y (idealThickeningIdealSheaf p J ^ n)).app G.obj)))
    (fun n => (Cohomology.pushforwardSpecSectionsIso p).hom.app G.obj ≫
      (Cohomology.moduleGlobalSectionsFunctorOfHom Y
        (Cohomology.affineFormalFunctionsScalar p)).map
          (idealQuotientπ Y (idealThickeningBaseScalar p) G.obj (J ^ n)))
    (affinePushforwardComparisonData p J G) (affinePushforwardQuotientTowerIso p J G)
    (generatedCompletionSectionsEquiv B (properPushforwardCoefficient p G) J)
    (affinePushforwardFormalFunctionsEquiv p J G)
    (generatedCompletionSectionsEquiv_of B (properPushforwardCoefficient p G) J)
    (affinePushforwardReduction_map p J G)
    (affinePushforwardFormalFunctionsEquiv_of p J G)

/-- The original compatible-family map, projected after its whole certificate. -/
def affinePushforwardLimitMap :
    ((completionFunctor (Spec B) (idealThickeningIdealSheaf (𝟙 (Spec B)) J)).obj
      (properPushforwardCoefficient p G)).affineFormalSections →ₗ[B]
      ModuleCat.sectionsSubmodule (affinePushforwardCompletionTower p J G) :=
  (affinePushforwardLimitComparisonData p J G).val

/-- The limit of the original comparison is the actual formal-functions map. -/
theorem affinePushforwardLimitMap_completion :
    (affinePushforwardLimitMap p J G).comp
      (generatedCompletionSectionsEquiv B (properPushforwardCoefficient p G) J).toLinearMap =
        (affinePushforwardFormalFunctionsEquiv p J G).toLinearMap :=
  (affinePushforwardLimitComparisonData p J G).property.1.1

/-- Formal functions makes the specified original whole-family comparison bijective. -/
theorem affinePushforwardLimitMap_bijective :
    originalLimitBijective (originalDiagramSectionsMap (affinePushforwardComparison p J G)) :=
  originalDiagramLimitComparison_bijective J
    (moduleSpecΓFunctor.obj ((pushforward p).obj G.obj))
    (generatedCompletionSectionsEquiv B (properPushforwardCoefficient p G) J)
    (affinePushforwardFormalFunctionsEquiv p J G) _
    (affinePushforwardLimitComparisonData p J G)

end AlgebraicGeometry.Scheme.Modules.Coherent
