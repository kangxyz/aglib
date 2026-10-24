/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.Modules.ClosureCharts
public import Mathlib.CategoryTheory.Comma.Arrow

/-! # Actual local constant presentations of module coefficient morphisms

A morphism from a constant finitely presented module is, on a jointly
surjective family of actual etale charts, isomorphic as an arrow to a constant
module morphism. This uses finite generators and relations, the original
sheafification unit, and native slice and inverse-image comparisons. It does
not assert that constant coefficients are globally full on disconnected charts.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Constructible.Modules

universe u r

attribute [local instance] hasSheafifyLarge ModuleCat.Sheaf.hasSheafify

variable {R : Type r} [CommRing R] {X : Scheme.{u}}

/-- A local unit equation gives an isomorphism of the original inverse-image
arrow with an actual constant module arrow on that chart. -/
def constantMapChartIsoOfUnit {M N : ModuleCat.{u + 1} R}
    (φ : (constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} R)).obj M ⟶
      (constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} R)).obj N)
    (U : X.Etale) (a : M ⟶ N)
    (ha : (ModuleCat.Sheaf.constantUnit X.smallEtaleTopology M).app (op U) ≫
        φ.hom.app (op U) =
      a ≫ (ModuleCat.Sheaf.constantUnit X.smallEtaleTopology N).app (op U)) :
    Arrow.mk ((constantSheaf U.left.smallEtaleTopology (ModuleCat.{u + 1} R)).map a) ≅
      Arrow.mk ((moduleInverseImage R U.hom).map φ) :=
  Arrow.isoOfNatIso (moduleEtaleSliceConstantIso R U) (Arrow.mk a) ≪≫
    (moduleEtaleSliceEquivalence R U).inverse.mapArrow.mapIso
      (Arrow.isoMk' _ _
        (ModuleCat.Sheaf.constantOverIso X.smallEtaleTopology U M)
        (ModuleCat.Sheaf.constantOverIso X.smallEtaleTopology U N)
        (ModuleCat.Sheaf.constantOverMap_naturality_of_unit X.smallEtaleTopology φ U a ha)) ≪≫
    Arrow.isoOfNatIso
      (moduleEtaleSliceRestrictionIso R U ≪≫ (moduleInverseImageEtaleIso R U.hom).symm)
      (Arrow.mk φ)

/-- Every point admits an actual etale chart on which the original morphism
is a constant module morphism. Finite presentation is needed only in its source. -/
theorem exists_constantMap_chart {M N : ModuleCat.{u + 1} R}
    [Module.FinitePresentation R M]
    (φ : (constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} R)).obj M ⟶
      (constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} R)).obj N) (x : X) :
    ∃ (U : X.Etale) (y : U.left), U.hom y = x ∧
      ∃ a : M ⟶ N, Nonempty
        (Arrow.mk ((constantSheaf U.left.smallEtaleTopology (ModuleCat.{u + 1} R)).map a) ≅
          Arrow.mk ((moduleInverseImage R U.hom).map φ)) := by
  have hS := ModuleCat.Sheaf.constantMapSieve_mem X.smallEtaleTopology φ (etaleTerminal X)
  let T : Sieve (etaleTerminal X) :=
    ModuleCat.Sheaf.constantMapSieve X.smallEtaleTopology φ (etaleTerminal X)
  let P : MorphismProperty Scheme.{u} := fun {S T} (g : S ⟶ T) => Etale g
  have htop := congrArg
    (fun J : GrothendieckTopology X.Etale => T ∈ J (etaleTerminal X))
    (Scheme.smallGrothendieckTopology_eq_toGrothendieck_smallPretopology X
      (P := P) (Q := P) le_rfl)
  have hpoints : ∀ z : X, ∃ (U : X.Etale) (f : U ⟶ etaleTerminal X) (y : U.left),
      T f ∧ Etale f.left ∧ (f.left : U.left ⟶ X) y = z :=
    (Scheme.mem_toGrothendieck_smallPretopology
      (P := P) (Q := P) (etaleTerminal X) T).mp (Eq.mp htop hS)
  obtain ⟨U, f, y, ⟨a, ha⟩, _, hy⟩ := hpoints x
  refine ⟨U, y, ?_, a, ⟨constantMapChartIsoOfUnit φ U a ha⟩⟩
  have hf : (f.left : U.left ⟶ X) = U.hom := by
    have hw := MorphismProperty.Over.w f
    change f.left ≫ 𝟙 X = U.hom at hw
    exact (Category.comp_id f.left).symm.trans hw
  exact (congrArg (fun k : U.left ⟶ X => k y) hf).symm.trans hy

end AlgebraicGeometry.Scheme.EtaleCohomology.Constructible.Modules
