/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Category.ModuleCat.Sheaf.FiniteConstantCharts
public import Aglib.Algebra.Category.ModuleCat.Sheaf.ConstantRestriction
public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.Modules.LocallyConstant
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Open.ModuleAdjunction

/-!
# Native finite locally constant modules give the original finite chart sieve

An actual etale trivialization is transported through the original slice
restriction equivalence. The existing constant-over and inverse-image-constant
maps identify its constant module value on that same slice. Its original
constant unit gives a locally bijective presentation, and the original jointly
surjective family makes the already defined finite-type chart sieve covering.
No new chart predicate, sheaf realization, or local freeness is introduced.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Constructible.Modules

universe u

variable {R : Type (u + 1)} [CommRing R] {X : Scheme.{u}}

attribute [local instance] hasSheafifyLarge ModuleCat.Sheaf.hasSheafify

namespace FiniteTypeLocalTrivialization

variable {F : ModuleSheaf R X} (t : FiniteTypeLocalTrivialization F) (i : t.index)

/-- The actual chart isomorphism on the original slice, through the specified native maps. -/
def sliceChartIso :
    (constantSheaf (X.smallEtaleTopology.over (t.chart i)) (ModuleCat.{u + 1} R)).obj
        (t.value i) ≅
      (X.smallEtaleTopology.overPullback (ModuleCat.{u + 1} R) (t.chart i)).obj F := by
  let f := (t.chart i).hom
  let E := moduleEtaleSliceSheafEquivalence f R
  let e : X.smallEtaleTopology.overPullback (ModuleCat.{u + 1} R) (t.chart i) ⋙ E.inverse ≅
      moduleInverseImage R f :=
    moduleEtaleSliceRestrictionIso f R ≪≫ (Coefficients.moduleValuedInverseImageEtaleIso f R).symm
  exact E.inverse.preimageIso
    (E.inverse.mapIso (ModuleCat.Sheaf.constantOverIso X.smallEtaleTopology
      (t.chart i) (t.value i)) ≪≫
      e.app ((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} R)).obj (t.value i)) ≪≫
      (moduleInverseImageConstantIso R f).app (t.value i) ≪≫
      (t.trivialization i).symm ≪≫ (e.app F).symm)

/-- The chart presentation is the original constant unit followed by its actual chart arrow. -/
def sliceChartPresentation :
    (Functor.const (Over (t.chart i))ᵒᵖ).obj (t.value i) ⟶
      ((X.smallEtaleTopology.overPullback (ModuleCat.{u + 1} R) (t.chart i)).obj F).obj :=
  ModuleCat.Sheaf.constantUnit (X.smallEtaleTopology.over (t.chart i)) (t.value i) ≫
    (t.sliceChartIso i).hom.hom

/-- The original constant-unit factorization is retained before any object evaluation. -/
theorem sliceChartPresentation_unit :
    t.sliceChartPresentation i =
      ModuleCat.Sheaf.constantUnit (X.smallEtaleTopology.over (t.chart i)) (t.value i) ≫
        (t.sliceChartIso i).hom.hom := rfl

/-- The original chart presentation is locally surjective on the original slice. -/
instance sliceChartPresentation_isLocallySurjective :
    CategoryTheory.Presheaf.IsLocallySurjective
      (X.smallEtaleTopology.over (t.chart i)) (t.sliceChartPresentation i) := by
  let J := X.smallEtaleTopology.over (t.chart i)
  let : PreservesFilteredColimits (CategoryTheory.forget (ModuleCat.{u + 1} R)) :=
    ModuleCat.Sheaf.forget_preservesFilteredColimits R
  let : J.PreservesSheafification (CategoryTheory.forget (ModuleCat.{u + 1} R)) :=
    GrothendieckTopology.instPreservesSheafification J
      (CategoryTheory.forget (ModuleCat.{u + 1} R))
  let : CategoryTheory.Presheaf.IsLocallySurjective J
      (ModuleCat.Sheaf.constantUnit J (t.value i)) :=
    CategoryTheory.Presheaf.isLocallySurjective_toSheafify' J
      (D := ModuleCat.{u + 1} R) ((Functor.const (Over (t.chart i))ᵒᵖ).obj (t.value i))
  let : IsIso (t.sliceChartIso i).hom.hom := by
    change IsIso ((sheafToPresheaf J (ModuleCat.{u + 1} R)).map (t.sliceChartIso i).hom)
    infer_instance
  dsimp only [sliceChartPresentation]
  infer_instance

/-- The original chart presentation is locally injective on the original slice. -/
instance sliceChartPresentation_isLocallyInjective :
    CategoryTheory.Presheaf.IsLocallyInjective
      (X.smallEtaleTopology.over (t.chart i)) (t.sliceChartPresentation i) := by
  let J := X.smallEtaleTopology.over (t.chart i)
  let : PreservesFilteredColimits (CategoryTheory.forget (ModuleCat.{u + 1} R)) :=
    ModuleCat.Sheaf.forget_preservesFilteredColimits R
  let : J.PreservesSheafification (CategoryTheory.forget (ModuleCat.{u + 1} R)) :=
    GrothendieckTopology.instPreservesSheafification J
      (CategoryTheory.forget (ModuleCat.{u + 1} R))
  let : CategoryTheory.Presheaf.IsLocallyInjective J
      (ModuleCat.Sheaf.constantUnit J (t.value i)) :=
    CategoryTheory.Presheaf.isLocallyInjective_toSheafify' J
      (D := ModuleCat.{u + 1} R) ((Functor.const (Over (t.chart i))ᵒᵖ).obj (t.value i))
  let : IsIso (t.sliceChartIso i).hom.hom := by
    change IsIso ((sheafToPresheaf J (ModuleCat.{u + 1} R)).map (t.sliceChartIso i).hom)
    infer_instance
  dsimp only [sliceChartPresentation]
  infer_instance

include t in
/-- The actual jointly surjective chart family lies in the original finite-type chart sieve. -/
theorem finiteTypeConstantChartSieve_mem :
    ModuleCat.Sheaf.finiteTypeConstantChartSieve X.smallEtaleTopology F (etaleTerminal X) ∈
      X.smallEtaleTopology (etaleTerminal X) := by
  let f : ∀ j : t.index, t.chart j ⟶ etaleTerminal X :=
    fun j => (etaleTerminalIsTerminal X).from (t.chart j)
  have hc : Sieve.ofArrows t.chart f ∈ X.smallEtaleTopology (etaleTerminal X) := by
    rw [Scheme.ofArrows_mem_smallEtaleTopology_iff]
    ext x
    simp only [Set.mem_iUnion, Set.mem_range, Set.mem_univ, iff_true]
    obtain ⟨j, y, hy⟩ := t.covers x
    exact ⟨j, y, hy⟩
  apply X.smallEtaleTopology.superset_covering _ hc
  rw [Sieve.generate_le_iff, Presieve.ofArrows_le_iff]
  intro j
  exact ⟨t.value j, t.finite_value j, t.sliceChartPresentation j,
    inferInstance, inferInstance⟩

end FiniteTypeLocalTrivialization

/-- Native finite-type local constancy supplies the lower actual finite chart hypothesis. -/
theorem hasFiniteTypeConstantCharts_of_isFiniteTypeLocallyConstant
    (F : ModuleSheaf R X) (hF : IsFiniteTypeLocallyConstant F) :
    ModuleCat.Sheaf.HasFiniteTypeConstantCharts X.smallEtaleTopology F := by
  obtain ⟨t⟩ := hF
  exact ModuleCat.Sheaf.hasFiniteTypeConstantCharts_of_terminal X.smallEtaleTopology F
    (etaleTerminalIsTerminal X) t.finiteTypeConstantChartSieve_mem

end AlgebraicGeometry.Scheme.EtaleCohomology.Constructible.Modules
