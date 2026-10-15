/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.Modules.FinitePresentation.Basic
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Affine.FiniteGenerators
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Affine.FiniteTypeRestriction
public import Mathlib.RingTheory.Localization.Finiteness
/-!
# Finite global sections of affine vector bundles

Finite local generators are restricted to principal affine opens. Their global
sections are finite modules, and the actual tilde/localization comparison and
the local finite-generation criterion descend this to the original affine.
-/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open scoped ModuleCat.Algebra

namespace AlgebraicGeometry.Scheme.Modules

/-- Transport generators on the over-site of an open to its actual scheme
restriction. The index set, and hence its finiteness, is unchanged. -/
def generatingSectionsOverToRestrict {X : Scheme.{u}} {M : X.Modules} (U : X.Opens)
    (G : (M.over U).GeneratingSections) : (M.restrict U.ι).GeneratingSections :=
  (G.map (Scheme.Modules.overEquiv U).functor
    (U.sheafOfModulesEquivOverUnit X.ringCatSheaf).symm).ofEpi
      ((Scheme.Modules.overFunctorEquiv U).app M).hom

instance generatingSectionsOverToRestrict_isFiniteType {X : Scheme.{u}} {M : X.Modules}
    (U : X.Opens) (G : (M.over U).GeneratingSections) [G.IsFiniteType] :
    (generatingSectionsOverToRestrict U G).IsFiniteType := by
  dsimp [generatingSectionsOverToRestrict]
  infer_instance

/-- A finite family on an open gives finite global sections on every
principal affine open contained in it. -/
theorem finite_restrictPrincipal_of_overGenerators (R : CommRingCat.{u})
    (M : (Spec R).Modules) [M.IsQuasicoherent] (r : R) (U : (Spec R).Opens)
    (h : PrimeSpectrum.basicOpen r ≤ U) (G : (M.over U).GeneratingSections)
    [G.IsFiniteType] : Module.Finite (Localization.Away r)
      (moduleSpecΓFunctor.obj
        (M.restrict (Scheme.Modules.QuasiCoherent.principalOpen R r))) := by
  let t := (Spec R).homOfLE (U := PrimeSpectrum.basicOpen r) (V := U) h
  let j := (basicOpenIsoSpecAway r).inv ≫ t
  let e : Scheme.Modules.restrictFunctor U.ι ⋙ Scheme.Modules.restrictFunctor j ≅
      Scheme.Modules.restrictFunctor (Scheme.Modules.QuasiCoherent.principalOpen R r) :=
    (Scheme.Modules.restrictFunctorComp j U.ι).symm ≪≫
      Scheme.Modules.restrictFunctorCongr (by simp [j, t, basicOpenIsoSpecAway])
  have : PreservesColimitsOfSize.{u, u} (Scheme.Modules.restrictFunctor j) := inferInstance
  let G' := ((generatingSectionsOverToRestrict U G).map
    (Scheme.Modules.restrictFunctor j) (Scheme.Modules.restrictUnitIso j).symm).ofEpi
      (e.app M).hom
  exact Scheme.Modules.QuasiCoherent.finite_globalSections_of_generatingSections _ _ G'

/-- Quasicoherent affine sheaves with finite local generators have finite
global sections. The principal opens on which the generators are finite
cover the spectrum; localization detects finite generation. -/
theorem finite_globalSections_of_localGenerators (R : CommRingCat.{u})
    (M : (Spec R).Modules) [M.IsQuasicoherent]
    (q : SheafOfModules.LocalGeneratorsData.{u} M) [hq : q.IsFiniteType] :
    Module.Finite R (moduleSpecΓFunctor.obj M) := by
  classical
  let N := moduleSpecΓFunctor.obj M
  let T : Set R := {r | Module.Finite (Localization.Away r)
    (Scheme.Modules.QuasiCoherent.restrictionGlobalSections R r N)}
  have hT : Ideal.span T = ⊤ := by
    apply PrimeSpectrum.iSup_basicOpen_eq_top_iff'.mp
    apply top_unique
    intro x hx
    obtain ⟨V, f, ⟨i, ⟨g⟩⟩, hxV⟩ := q.coversTop ⊤ x (by simp)
    have hxi : x ∈ q.X i := (leOfHom g) hxV
    obtain ⟨a, ⟨_, ⟨r, rfl⟩, rfl⟩, hxr, hrU : PrimeSpectrum.basicOpen _ ≤ _⟩ :=
      PrimeSpectrum.isBasis_basic_opens.exists_subset_of_mem_open hxi (q.X i).2
    have hr : r ∈ T := by
      have := hq.isFiniteType i
      have hfin := finite_restrictPrincipal_of_overGenerators R M r (q.X i) hrU (q.generators i)
      let e := moduleSpecΓFunctor.mapIso
        ((Scheme.Modules.restrictFunctor
          (Scheme.Modules.QuasiCoherent.principalOpen R r)).mapIso
          (asIso M.fromTildeΓ))
      exact Module.Finite.of_surjective e.inv.hom
        (ConcreteCategory.bijective_of_isIso e.inv).surjective
    exact Opens.mem_iSup.mpr ⟨r, Opens.mem_iSup.mpr ⟨hr, hxr⟩⟩
  exact Module.Finite.of_localizationSpan' T hT
    (Rₚ := fun r => Localization.Away r.val)
    (fun r => Scheme.Modules.QuasiCoherent.toRestrictionGlobalSections R r.val N)
    (fun r => r.property)

/-- Quasicoherent sheaves of finite type on an affine scheme have finite
global sections. This formulation needs no chosen local generators. -/
theorem finite_globalSections_of_finiteType (R : CommRingCat.{u})
    (M : (Spec R).Modules) [M.IsQuasicoherent] [M.IsFiniteType] :
    Module.Finite R (moduleSpecΓFunctor.obj M) := by
  obtain ⟨q, hq⟩ := SheafOfModules.IsFiniteType.exists_localGeneratorsData M
  exact finite_globalSections_of_localGenerators R M q

/-- Finite local presentations on an affine scheme give finite global
sections; no noetherianity hypothesis is needed. -/
theorem finite_globalSections_of_finitePresentation (R : CommRingCat.{u})
    (M : (Spec R).Modules) [M.IsFinitePresentation] :
    Module.Finite R (moduleSpecΓFunctor.obj M) :=
  finite_globalSections_of_finiteType R M

end AlgebraicGeometry.Scheme.Modules
