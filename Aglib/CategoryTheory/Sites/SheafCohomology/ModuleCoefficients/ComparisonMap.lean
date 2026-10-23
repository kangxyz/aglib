/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Sites.SheafCohomology.ModuleCoefficients.Unit
public import Aglib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Aglib.Algebra.Homology.DerivedCategory.Ext.AcyclicComparison

/-!
# The original module-to-abelian cohomology map

The comparison is the actual exact scalar-forgetting Ext map, precomposed
with the integer-to-rank-one source morphism. Scalar and module universes
remain independent. This leaf establishes the map and its normalizations;
all-degree bijectivity requires the genuine acyclicity supplier separately.
-/

@[expose] public noncomputable section

universe u v r w eM eA

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian

namespace CategoryTheory.Sheaf.ModuleCoefficients

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  {T : C} (hT : IsTerminal T) (R : Sheaf J RingCat.{r})
  [HasSheafify J AddCommGrpCat.{max r w}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max r w}]
  [HasExt.{eM} (SheafOfModules.{max r w} R)]
  [HasExt.{eA} (Sheaf J AddCommGrpCat.{max r w})]

/-- The actual exact-forgetting comparison, with its original section-one source map. -/
def cohomologyMap (M : SheafOfModules.{max r w} R) (n : ℕ) :
    Ext.{eM} (SheafOfModules.liftedUnit.{u, v, w, r} R) M n →+
      Sheaf.H.{eA} ((SheafOfModules.toSheaf R).obj M) n :=
  (SheafOfModules.toSheaf R).extPrecompMap (liftedUnitIntegerMap hT R) M n

/-- Degree zero is scalar forgetting after the actual integer-to-unit map. -/
theorem cohomologyMap_mk₀ (M : SheafOfModules.{max r w} R)
    (f : SheafOfModules.liftedUnit.{u, v, w, r} R ⟶ M) :
    cohomologyMap hT R M 0 (Ext.mk₀ f) =
      Ext.mk₀ (liftedUnitIntegerMap hT R ≫ (SheafOfModules.toSheaf R).map f) :=
  Functor.extPrecompMap_mk₀ _ _ f

/-- The original comparison is bijective in degree zero. -/
theorem cohomologyMap_bijective_zero (M : SheafOfModules.{max r w} R) :
    Function.Bijective (cohomologyMap hT R M 0) := by
  constructor
  · intro x y h
    obtain ⟨f, rfl⟩ := (Ext.mk₀_bijective _ _).surjective x
    obtain ⟨g, rfl⟩ := (Ext.mk₀_bijective _ _).surjective y
    rw [cohomologyMap_mk₀, cohomologyMap_mk₀] at h
    apply congrArg Ext.mk₀
    apply (liftedUnitIntegerHomEquiv hT R M).injective
    simpa only [liftedUnitIntegerHomEquiv_apply] using
      (Ext.mk₀_bijective _ _).injective h
  · intro x
    obtain ⟨g, rfl⟩ := (Ext.mk₀_bijective _ _).surjective x
    obtain ⟨f, hf⟩ := (liftedUnitIntegerHomEquiv hT R M).surjective g
    refine ⟨Ext.mk₀ f, ?_⟩
    rw [cohomologyMap_mk₀, ← liftedUnitIntegerHomEquiv_apply, hf]

/-- Yoneda composition uses the original exact scalar-forgetting functor. -/
theorem cohomologyMap_comp {M N : SheafOfModules.{max r w} R} {i j k : ℕ}
    (x : Ext.{eM} (SheafOfModules.liftedUnit.{u, v, w, r} R) M i)
    (y : Ext.{eM} M N j) (h : i + j = k) :
    cohomologyMap hT R N k (x.comp y h) =
      (cohomologyMap hT R M i x).comp
        (y.mapExactFunctor (SheafOfModules.toSheaf R)) h :=
  Functor.extPrecompMap_comp _ _ x y h

/-- Naturality is expressed using the original abelian cohomology coefficient map. -/
theorem cohomologyMap_naturality {M N : SheafOfModules.{max r w} R}
    (f : M ⟶ N) (n : ℕ)
    (x : Ext.{eM} (SheafOfModules.liftedUnit.{u, v, w, r} R) M n) :
    cohomologyMap hT R N n (x.comp (Ext.mk₀ f) (Nat.add_zero n)) =
      Sheaf.H.map ((SheafOfModules.toSheaf R).map f) n (cohomologyMap hT R M n x) := by
  rw [cohomologyMap_comp, Ext.mapExactFunctor_mk₀]
  rfl

/-- The connecting map is the native extension class of the original short exact sequence. -/
theorem cohomologyMap_connecting (S : ShortComplex (SheafOfModules.{max r w} R))
    (hS : S.ShortExact) (n : ℕ)
    (x : Ext.{eM} (SheafOfModules.liftedUnit.{u, v, w, r} R) S.X₃ n) :
    cohomologyMap hT R S.X₁ (n + 1) (x.comp hS.extClass rfl) =
      (cohomologyMap hT R S.X₃ n x).comp
        (hS.map_of_exact (SheafOfModules.toSheaf R)).extClass rfl := by
  rw [cohomologyMap_comp, Ext.mapExactFunctor_extClass]

end CategoryTheory.Sheaf.ModuleCoefficients
