/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.InternalHom.Coherent
public import Aglib.AlgebraicGeometry.Modules.LocallyFree.Affine.Projective
public import Aglib.AlgebraicGeometry.Modules.LocallyFree.Locality
public import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix

/-! # Finite local freeness of the actual internal Hom

Common principal refinements of the original local bases make the actual
Hom section modules finite free. The existing localization comparison proves
quasicoherence, so these section bases give bases of the unchanged sheaf.
No Noetherian hypothesis or alternate internal-Hom model is used.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open scoped ModuleCat.Algebra

namespace AlgebraicGeometry.Scheme.Modules.InternalHom

universe u

open QuasiCoherent

variable {X : Scheme.{u}} (M N : X.Modules)
  [IsFiniteLocallyFree X M] [IsFiniteLocallyFree X N]

/-- The original internal Hom is finite locally free on every actual affine chart. -/
theorem finiteLocallyFree_affineRestriction {R : CommRingCat.{u}}
    (j : Spec R ⟶ X) [IsOpenImmersion j] :
    IsFiniteLocallyFree (Spec R) ((show X.Modules from sheaf X M N).restrict j) := by
  let H : X.Modules := sheaf X M N
  apply finiteLocallyFree_iff_pointwise.mpr
  intro x
  obtain ⟨U, hxU, GM, hGM, hfGM⟩ := finiteLocallyFree_iff_pointwise.mp
    (inferInstance : IsFiniteLocallyFree (Spec R) (M.restrict j)) x
  obtain ⟨V, hxV, GN, hGN, hfGN⟩ := finiteLocallyFree_iff_pointwise.mp
    (inferInstance : IsFiniteLocallyFree (Spec R) (N.restrict j)) x
  obtain ⟨_, ⟨_, ⟨r, rfl⟩, rfl⟩, hxr, hr⟩ :=
    PrimeSpectrum.isBasis_basic_opens.exists_subset_of_mem_open
      (show x ∈ U ⊓ V from ⟨hxU, hxV⟩) (U ⊓ V).isOpen
  let k := principalOpen R r
  let eM : moduleSpecΓFunctor.obj (M.restrict (k ≫ j)) ≅
      moduleSpecΓFunctor.obj ((M.restrict j).restrict k) :=
    moduleSpecΓFunctor.mapIso ((restrictFunctorComp k j).app M)
  let eN : moduleSpecΓFunctor.obj (N.restrict (k ≫ j)) ≅
      moduleSpecΓFunctor.obj ((N.restrict j).restrict k) :=
    moduleSpecΓFunctor.mapIso ((restrictFunctorComp k j).app N)
  have : Module.Free (Localization.Away r)
      (moduleSpecΓFunctor.obj ((M.restrict j).restrict k)) :=
    free_restrictPrincipal_of_overBasis R (M.restrict j) r U (hr.trans inf_le_left) GM
  have : Module.Free (Localization.Away r)
      (moduleSpecΓFunctor.obj ((N.restrict j).restrict k)) :=
    free_restrictPrincipal_of_overBasis R (N.restrict j) r V (hr.trans inf_le_right) GN
  have : Module.Free (Localization.Away r)
      (moduleSpecΓFunctor.obj (M.restrict (k ≫ j))) :=
    Module.Free.of_equiv eM.toLinearEquiv.symm
  have : Module.Free (Localization.Away r)
      (moduleSpecΓFunctor.obj (N.restrict (k ≫ j))) :=
    Module.Free.of_equiv eN.toLinearEquiv.symm
  have : Module.Finite (Localization.Away r)
      (moduleSpecΓFunctor.obj (M.restrict (k ≫ j))) :=
    finite_globalSections_of_finiteLocallyFree (.of (Localization.Away r)) _
  have : Module.Finite (Localization.Away r)
      (moduleSpecΓFunctor.obj (N.restrict (k ≫ j))) :=
    finite_globalSections_of_finiteLocallyFree (.of (Localization.Away r)) _
  have : Module.FinitePresentation (Localization.Away r)
      (moduleSpecΓFunctor.obj (M.restrict (k ≫ j))) :=
    finitePresentation_globalSections_of_finiteLocallyFree (.of (Localization.Away r)) _
  have : (H.restrict (k ≫ j)).IsQuasicoherent := quasicoherent_affineRestriction (k ≫ j) M N
  let eH := affineRestrictionSectionsEquiv (k ≫ j) M N
  have : Module.Free (Localization.Away r) (moduleSpecΓFunctor.obj (H.restrict (k ≫ j))) :=
    Module.Free.of_equiv eH.symm
  have : Module.Finite (Localization.Away r) (moduleSpecΓFunctor.obj (H.restrict (k ≫ j))) :=
    Module.Finite.equiv eH.symm
  obtain ⟨G, hG, hfG⟩ := exists_finiteGlobalBasis_of_free_sections
    (.of (Localization.Away r)) (H.restrict (k ≫ j))
  let G' := G.ofEpi ((restrictFunctorComp k j).app H).hom
  exact ⟨PrimeSpectrum.basicOpen r, hxr,
    generatingSectionsPrincipalToOver R (H.restrict j) r G', inferInstance, inferInstance⟩

/-- Internal Hom of finite locally free modules is finite locally free on an arbitrary scheme. -/
theorem finiteLocallyFree : IsFiniteLocallyFree X (sheaf X M N) := by
  let 𝒰 := X.affineOpenCover
  exact finiteLocallyFree_of_affineCharts (sheaf X M N) 𝒰.X 𝒰.f
    (fun x => ⟨𝒰.idx x, 𝒰.covers x⟩)
    (fun i => finiteLocallyFree_affineRestriction M N (𝒰.f i))

/-- The actual dual of a vector bundle is finite locally free, without a Noetherian premise. -/
theorem finiteLocallyFree_dual :
    IsFiniteLocallyFree X (sheaf X M (SheafOfModules.unit X.ringCatSheaf)) := by
  let e : SheafOfModules.free (R := X.ringCatSheaf) PUnit.{u + 1} ≅
      SheafOfModules.unit X.ringCatSheaf :=
    coproductUniqueIso (fun _ : PUnit.{u + 1} => SheafOfModules.unit X.ringCatSheaf)
  let : IsFiniteLocallyFree X (SheafOfModules.unit X.ringCatSheaf) :=
    finiteLocallyFree_of_iso e
  exact finiteLocallyFree M _

end AlgebraicGeometry.Scheme.Modules.InternalHom
