/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Coefficients.ClosedExactness
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Coefficients.ModuleUnitInverseImage
public import Aglib.AlgebraicGeometry.EtaleCohomology.Duality.ZModLinear
public import Aglib.AlgebraicGeometry.EtaleCohomology.Coefficients.ModuleCohomologyPullback
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Coefficients.NativeAdjunctionUnderlying
public import Aglib.AlgebraicGeometry.EtaleCohomology.Finite.Cohomology
public import Aglib.Algebra.Homology.DerivedCategory.Ext.AcyclicComparison
public import Aglib.CategoryTheory.Adjunction.LowerShriekUnderlying
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.MapAdjunction
public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor

/-!
# Original finite pushforward comparisons for module Ext

Finite direct image is exact on the genuine constant-ring module sheaves.
The existing exact adjunction and the original unit pullback isomorphism give
the ordinary unit-Ext comparison, with independent Ext universes. Its whole
forward and inverse maps, degree-zero values and coefficient naturality retain
the original unit, counit and exact-functor maps.

This ordinary-cohomology construction does not assert finite-étale ambidexterity,
compact-support comparison or normalized trace compatibility. Those original-map
obligations are separate from the finite exact adjunction used here.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian AlgebraicGeometry

universe u wX wY vX vY

namespace AlgebraicGeometry.Scheme.EtaleCohomology

open Coefficients

attribute [local instance] hasSheafifyLarge hasSheafifyModules
  CategoryTheory.TorsionZMod.Ringed.abWEqualsLocallyBijectiveStandard moduleSheafExtZModModule

variable {Y X : Scheme.{u}} (f : Y ⟶ X) [IsFinite f] (n : ℕ)

/-- The existing finite homology exactness supplies finite colimits of the same direct image. -/
local instance finitePushforward_preservesFiniteColimits :
    PreservesFiniteColimits (moduleDirectImage f (ULift.{u + 1} (ZMod n))) :=
  Functor.preservesFiniteColimits_of_preservesHomology _

variable [HasExt.{wX} (ModuleSheaf X (ULift.{u + 1} (ZMod n)))]
  [HasExt.{wY} (ModuleSheaf Y (ULift.{u + 1} (ZMod n)))]

/-- The actual exact finite-image adjunction, with the original unit coefficient. -/
def moduleFiniteUnitExtAddEquiv (M : ModuleSheaf Y (ULift.{u + 1} (ZMod n))) (q : ℕ) :
    Ext.{wX} (moduleUnit X (ULift.{u + 1} (ZMod n)))
        ((moduleDirectImage f (ULift.{u + 1} (ZMod n))).obj M) q ≃+
      Ext.{wY} (moduleUnit Y (ULift.{u + 1} (ZMod n))) M q :=
  (moduleInverseImageAdjunction f (ULift.{u + 1} (ZMod n))).extEquiv.symm.trans
    ((((extFunctor q).mapIso
      (moduleUnitInverseImageIso f n).symm.op).app M).addCommGroupIsoToAddEquiv)

/-- The entire forward map is the original exact pullback, counit and source-unit comparison. -/
theorem moduleFiniteUnitExtAddEquiv_toAddMonoidHom
    (M : ModuleSheaf Y (ULift.{u + 1} (ZMod n))) (q : ℕ) :
    (moduleFiniteUnitExtAddEquiv f n M q).toAddMonoidHom =
      ((Ext.mk₀ (moduleUnitInverseImageIso f n).inv).precomp M (zero_add q)).comp
        (((Ext.mk₀
          ((moduleInverseImageAdjunction f (ULift.{u + 1} (ZMod n))).counit.app M)).postcomp
          ((moduleInverseImage f (ULift.{u + 1} (ZMod n))).obj
            (moduleUnit X (ULift.{u + 1} (ZMod n)))) (add_zero q)).comp
          ((moduleInverseImage f (ULift.{u + 1} (ZMod n))).mapExtAddHom
            (moduleUnit X (ULift.{u + 1} (ZMod n)))
            ((moduleDirectImage f (ULift.{u + 1} (ZMod n))).obj M) q)) := rfl

/-- Evaluation of the whole original forward comparison. -/
theorem moduleFiniteUnitExtAddEquiv_apply
    (M : ModuleSheaf Y (ULift.{u + 1} (ZMod n))) (q : ℕ)
    (e : Ext.{wX} (moduleUnit X (ULift.{u + 1} (ZMod n)))
      ((moduleDirectImage f (ULift.{u + 1} (ZMod n))).obj M) q) :
    moduleFiniteUnitExtAddEquiv f n M q e =
      (Ext.mk₀ (moduleUnitInverseImageIso f n).inv).comp
        ((e.mapExactFunctor (moduleInverseImage f (ULift.{u + 1} (ZMod n)))).comp
          (Ext.mk₀ ((moduleInverseImageAdjunction f (ULift.{u + 1} (ZMod n))).counit.app M))
          (add_zero q)) (zero_add q) := rfl

/-- The degree-zero comparison keeps the original adjunction transpose of a morphism. -/
theorem moduleFiniteUnitExtAddEquiv_mk₀
    (M : ModuleSheaf Y (ULift.{u + 1} (ZMod n)))
    (a : moduleUnit X (ULift.{u + 1} (ZMod n)) ⟶
      (moduleDirectImage f (ULift.{u + 1} (ZMod n))).obj M) :
    moduleFiniteUnitExtAddEquiv f n M 0 (Ext.mk₀ a) =
      Ext.mk₀ ((moduleUnitInverseImageIso f n).inv ≫
        (moduleInverseImage f (ULift.{u + 1} (ZMod n))).map a ≫
          (moduleInverseImageAdjunction f (ULift.{u + 1} (ZMod n))).counit.app M) := by
  rw [moduleFiniteUnitExtAddEquiv_apply, Ext.mapExactFunctor_mk₀,
    Ext.mk₀_comp_mk₀, Ext.mk₀_comp_mk₀]

/-- The inverse whole comparison is the existing exact-functor map with its original unit. -/
theorem moduleFiniteUnitExtAddEquiv_symm_toAddMonoidHom
    (M : ModuleSheaf Y (ULift.{u + 1} (ZMod n))) (q : ℕ) :
    (moduleFiniteUnitExtAddEquiv f n M q).symm.toAddMonoidHom =
      (moduleDirectImage f (ULift.{u + 1} (ZMod n))).extPrecompMap
        ((moduleInverseImageAdjunction f (ULift.{u + 1} (ZMod n))).unit.app
            (moduleUnit X (ULift.{u + 1} (ZMod n))) ≫
          (moduleDirectImage f (ULift.{u + 1} (ZMod n))).map
            (moduleUnitInverseImageIso f n).hom) M q := by
  ext e
  change (Ext.mk₀ ((moduleInverseImageAdjunction f (ULift.{u + 1} (ZMod n))).unit.app
      (moduleUnit X (ULift.{u + 1} (ZMod n))))).comp
    (((Ext.mk₀ (moduleUnitInverseImageIso f n).hom).comp e (zero_add q)).mapExactFunctor
      (moduleDirectImage f (ULift.{u + 1} (ZMod n)))) (zero_add q) = _
  rw [Ext.mapExactFunctor_comp, Ext.mapExactFunctor_mk₀, Ext.mk₀_comp_mk₀_assoc]
  rfl

/-- Whole coefficient naturality on the two original Ext carriers. -/
theorem moduleFiniteUnitExtAddEquiv_naturality
    {M N : ModuleSheaf Y (ULift.{u + 1} (ZMod n))} (a : M ⟶ N) (q : ℕ) :
    (moduleFiniteUnitExtAddEquiv f n N q).toAddMonoidHom.comp
        ((Ext.mk₀ ((moduleDirectImage f (ULift.{u + 1} (ZMod n))).map a)).postcomp
          (moduleUnit X (ULift.{u + 1} (ZMod n))) (add_zero q)) =
      ((Ext.mk₀ a).postcomp (moduleUnit Y (ULift.{u + 1} (ZMod n))) (add_zero q)).comp
        (moduleFiniteUnitExtAddEquiv f n M q).toAddMonoidHom := by
  ext e
  change moduleFiniteUnitExtAddEquiv f n N q
      (e.comp (Ext.mk₀ ((moduleDirectImage f (ULift.{u + 1} (ZMod n))).map a)) (add_zero q)) =
    (moduleFiniteUnitExtAddEquiv f n M q e).comp (Ext.mk₀ a) (add_zero q)
  rw [moduleFiniteUnitExtAddEquiv_apply, moduleFiniteUnitExtAddEquiv_apply,
    Ext.mapExactFunctor_comp, Ext.mapExactFunctor_mk₀]
  rw [Ext.comp_assoc_of_third_deg_zero, Ext.mk₀_comp_mk₀]
  have h := (moduleInverseImageAdjunction f (ULift.{u + 1} (ZMod n))).counit.naturality a
  dsimp only [CategoryTheory.Functor.comp_map, CategoryTheory.Functor.id_map] at h
  rw [h]
  rw [← Ext.mk₀_comp_mk₀]
  simp only [Ext.comp_assoc_of_third_deg_zero]

/-- The same comparison is linear for the existing canonical ZMod Ext actions. -/
def moduleFiniteUnitExtLinearEquiv (M : ModuleSheaf Y (ULift.{u + 1} (ZMod n))) (q : ℕ) :
    Ext.{wX} (moduleUnit X (ULift.{u + 1} (ZMod n)))
        ((moduleDirectImage f (ULift.{u + 1} (ZMod n))).obj M) q ≃ₗ[ZMod n]
      Ext.{wY} (moduleUnit Y (ULift.{u + 1} (ZMod n))) M q where
  toAddEquiv := moduleFiniteUnitExtAddEquiv f n M q
  map_smul' := ZMod.map_smul (moduleFiniteUnitExtAddEquiv f n M q)

/-- The linear comparison retains exactly the original additive comparison. -/
theorem moduleFiniteUnitExtLinearEquiv_toAddEquiv
    (M : ModuleSheaf Y (ULift.{u + 1} (ZMod n))) (q : ℕ) :
    (moduleFiniteUnitExtLinearEquiv f n M q).toAddEquiv = moduleFiniteUnitExtAddEquiv f n M q :=
  rfl

/-- The whole finite comparison is the shared original module pullback followed by its counit. -/
theorem moduleFiniteUnitExtAddEquiv_eq_pullback
    (M : ModuleSheaf Y (ULift.{u + 1} (ZMod n))) (q : ℕ) :
    (moduleFiniteUnitExtAddEquiv f n M q).toAddMonoidHom =
      ((Ext.mk₀
        ((moduleInverseImageAdjunction f (ULift.{u + 1} (ZMod n))).counit.app M)).postcomp
          (moduleUnit Y (ULift.{u + 1} (ZMod n))) (add_zero q)).comp
        (moduleUnitExtPullback f n
          ((moduleDirectImage f (ULift.{u + 1} (ZMod n))).obj M) q) := by
  apply AddMonoidHom.ext
  intro e
  change moduleFiniteUnitExtAddEquiv f n M q e =
    (moduleUnitExtPullback f n ((moduleDirectImage f (ULift.{u + 1} (ZMod n))).obj M) q e).comp
      (Ext.mk₀ ((moduleInverseImageAdjunction f (ULift.{u + 1} (ZMod n))).counit.app M))
      (add_zero q)
  rw [moduleFiniteUnitExtAddEquiv_apply, moduleUnitExtPullback_apply,
    Ext.comp_assoc_of_third_deg_zero]

variable [HasExt.{vX} (AbelianSheaf.{u, u + 1} X)]
  [HasExt.{vY} (AbelianSheaf.{u, u + 1} Y)]

/-- The entire finite module-unit comparison is the original abelian finite cohomology
comparison underneath. All four Ext universes remain independent. -/
theorem moduleFiniteUnitExtCohomology_square
    (M : ModuleSheaf Y (ULift.{u + 1} (ZMod n))) (q : ℕ) :
    (etaleModuleExtCohomologyAddEquivLargeScalars Y
        (constantRing Y (ULift.{u + 1} (ZMod n))) M q).toAddMonoidHom.comp
      (moduleFiniteUnitExtAddEquiv f n M q).toAddMonoidHom =
    (Finite.finiteCohomologyDirectImageAddEquiv f
        ((SheafOfModules.toSheaf
          (constantRing Y (ULift.{u + 1} (ZMod n)))).obj M) q).toAddMonoidHom.comp
      ((Sheaf.H.map
          ((moduleDirectImageUnderlyingIso f (ULift.{u + 1} (ZMod n))).hom.app M) q).comp
        (etaleModuleExtCohomologyAddEquivLargeScalars X
          (constantRing X (ULift.{u + 1} (ZMod n)))
          ((moduleDirectImage f (ULift.{u + 1} (ZMod n))).obj M) q).toAddMonoidHom) := by
  apply AddMonoidHom.ext
  intro e
  have he := DFunLike.congr_fun (moduleFiniteUnitExtAddEquiv_eq_pullback f n M q) e
  change moduleFiniteUnitExtAddEquiv f n M q e =
    (moduleUnitExtPullback f n ((moduleDirectImage f (ULift.{u + 1} (ZMod n))).obj M) q e).comp
      (Ext.mk₀ ((moduleInverseImageAdjunction f (ULift.{u + 1} (ZMod n))).counit.app M))
      (add_zero q) at he
  change etaleModuleExtCohomologyAddEquivLargeScalars Y
      (constantRing Y (ULift.{u + 1} (ZMod n))) M q (moduleFiniteUnitExtAddEquiv f n M q e) =
    Finite.finiteCohomologyDirectImageAddEquiv f
      ((SheafOfModules.toSheaf (constantRing Y (ULift.{u + 1} (ZMod n)))).obj M) q
      (Sheaf.H.map ((moduleDirectImageUnderlyingIso f (ULift.{u + 1} (ZMod n))).hom.app M) q
        (etaleModuleExtCohomologyAddEquivLargeScalars X
          (constantRing X (ULift.{u + 1} (ZMod n)))
          ((moduleDirectImage f (ULift.{u + 1} (ZMod n))).obj M) q e))
  rw [he, moduleUnitExtAddEquiv_naturality]
  have hc := Adjunction.underlying_counit_app
    (moduleInverseImageAdjunction f (ULift.{u + 1} (ZMod n))) (inverseImageAdjunction f)
    (moduleInverseImageUnderlyingIso (ULift.{u + 1} (ZMod n)) f)
    (moduleDirectImageUnderlyingIso f (ULift.{u + 1} (ZMod n)))
    (mate_moduleInverseImageUnderlyingIso_inv (Λ := ULift.{u + 1} (ZMod n)) (f := f)) M
  rw [hc]
  simp only [Sheaf.H.map_comp_apply]
  have hp := DFunLike.congr_fun
    (moduleUnitExtCohomologyPullback_square.{u, wX, wY, vX, vY} f n
      ((moduleDirectImage f (ULift.{u + 1} (ZMod n))).obj M) q) e
  simp only [AddMonoidHom.comp_apply] at hp
  let ε := (inverseImageAdjunction f).counit.app
    ((SheafOfModules.toSheaf (constantRing Y (ULift.{u + 1} (ZMod n)))).obj M)
  let δ := (moduleDirectImageUnderlyingIso f (ULift.{u + 1} (ZMod n))).hom.app M
  have h₁ := congrArg ((Sheaf.H.map ε q).comp
    (Sheaf.H.map ((inverseImage f).map δ) q)) hp
  have h₂ := congrArg (Sheaf.H.map ε q)
    (cohomologyPullback_coefficientMap f δ q
      (etaleModuleExtCohomologyAddEquivLargeScalars X
        (constantRing X (ULift.{u + 1} (ZMod n)))
        ((moduleDirectImage f (ULift.{u + 1} (ZMod n))).obj M) q e)).symm
  exact h₁.trans (h₂.trans (Finite.finiteCohomologyDirectImageAddEquiv_apply f _ q _).symm)

end AlgebraicGeometry.Scheme.EtaleCohomology
