/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.Modules.Images
public import Aglib.AlgebraicGeometry.EtaleCohomology.Finite.Cohomology
public import Aglib.CategoryTheory.Sites.SheafCohomology.ModuleCoefficients.ConstantScalars
public import Mathlib.RingTheory.Finiteness.Basic

/-! # Scalar-linear original cohomology of finite direct images

For actual constant-ring module sheaves, the existing finite direct-image
comparison is linear for the original coefficient actions. Its forward map is
the existing comparison after the native underlying-sheaf isomorphism. Scalar
compatibility follows from coefficient naturality at scalar endomorphisms.

Only finiteness of the scheme morphism is required. The two Ext universes are
independent, and neither the coefficient ring nor its modules must be finite.
-/

@[expose] public noncomputable section

open CategoryTheory

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Finite

open Constructible.Modules

universe u r wX wS

attribute [local instance] hasSheafifyLarge ModuleCat.Sheaf.hasSheafify
  ModuleCat.Sheaf.cohomologyModule

variable (R : Type r) [CommRing R] {X S : Scheme.{u}}
  [HasExt.{wX} (AbelianSheaf.{u, u + 1} X)]
  [HasExt.{wS} (AbelianSheaf.{u, u + 1} S)]
  (f : X ⟶ S) [IsFinite f]

/-- The existing finite cohomology comparison for actual module coefficients,
linear for the original scalar actions and with independent Ext universes. -/
def finiteModuleCohomologyDirectImageLinearEquiv (F : ModuleSheaf R X) (q : ℕ) :
    Sheaf.H.{wS} ((moduleUnderlying R S).obj ((moduleDirectImage R f).obj F)) q ≃ₗ[R]
      Sheaf.H.{wX} ((moduleUnderlying R X).obj F) q where
  toAddEquiv :=
    ((Sheaf.functorH S.smallEtaleTopology q).mapIso
      ((moduleDirectImageUnderlyingIso R f).app F)).addCommGroupIsoToAddEquiv.trans
        (finiteCohomologyDirectImageAddEquiv f ((moduleUnderlying R X).obj F) q)
  map_smul' r x := by
    change finiteCohomologyDirectImageAddEquiv f ((moduleUnderlying R X).obj F) q
        (Sheaf.H.map ((moduleDirectImageUnderlyingIso R f).hom.app F) q
          (Sheaf.H.map ((moduleUnderlying R S).map
            (r • 𝟙 ((moduleDirectImage R f).obj F))) q x)) =
      Sheaf.H.map ((moduleUnderlying R X).map (r • 𝟙 F)) q
        (finiteCohomologyDirectImageAddEquiv f ((moduleUnderlying R X).obj F) q
          (Sheaf.H.map ((moduleDirectImageUnderlyingIso R f).hom.app F) q x))
    have hscalar : (moduleDirectImage R f).map (r • 𝟙 F) =
        r • 𝟙 ((moduleDirectImage R f).obj F) := rfl
    have h : (moduleUnderlying R S).map (r • 𝟙 ((moduleDirectImage R f).obj F)) ≫
          (moduleDirectImageUnderlyingIso R f).hom.app F =
        (moduleDirectImageUnderlyingIso R f).hom.app F ≫
          (directImage f).map ((moduleUnderlying R X).map (r • 𝟙 F)) := by
      simpa only [Functor.comp_map, hscalar] using
        (moduleDirectImageUnderlyingIso R f).hom.naturality (r • 𝟙 F)
    rw [← Sheaf.H.map_comp_apply, h, Sheaf.H.map_comp_apply]
    exact finiteCohomologyDirectImageAddEquiv_naturality f
      ((moduleUnderlying R X).map (r • 𝟙 F)) q _

/-- The linear equivalence retains the existing finite comparison and the native
underlying direct-image isomorphism, with no replacement cohomology map. -/
@[simp]
theorem finiteModuleCohomologyDirectImageLinearEquiv_apply
    (F : ModuleSheaf R X) (q : ℕ)
    (x : Sheaf.H.{wS} ((moduleUnderlying R S).obj ((moduleDirectImage R f).obj F)) q) :
    finiteModuleCohomologyDirectImageLinearEquiv R f F q x =
      finiteCohomologyDirectImageAddEquiv f ((moduleUnderlying R X).obj F) q
        (Sheaf.H.map ((moduleDirectImageUnderlyingIso R f).hom.app F) q x) := rfl

/-- The original pullback and adjunction counit identify the linear equivalence's
forward map, after the actual underlying direct-image comparison. -/
theorem finiteModuleCohomologyDirectImageLinearEquiv_apply_eq_pullback
    (F : ModuleSheaf R X) (q : ℕ)
    (x : Sheaf.H.{wS} ((moduleUnderlying R S).obj ((moduleDirectImage R f).obj F)) q) :
    finiteModuleCohomologyDirectImageLinearEquiv R f F q x =
      Sheaf.H.map ((inverseImageAdjunction f).counit.app ((moduleUnderlying R X).obj F)) q
        (cohomologyPullback f ((directImage f).obj ((moduleUnderlying R X).obj F)) q
          (Sheaf.H.map ((moduleDirectImageUnderlyingIso R f).hom.app F) q x)) :=
  finiteCohomologyDirectImageAddEquiv_apply f ((moduleUnderlying R X).obj F) q _

/-- Coefficient naturality is expressed by the original module cohomology maps. -/
theorem finiteModuleCohomologyDirectImageLinearEquiv_naturality
    {F G : ModuleSheaf R X} (a : F ⟶ G) (q : ℕ)
    (x : Sheaf.H.{wS} ((moduleUnderlying R S).obj ((moduleDirectImage R f).obj F)) q) :
    finiteModuleCohomologyDirectImageLinearEquiv R f G q
        (Sheaf.H.map ((moduleUnderlying R S).map ((moduleDirectImage R f).map a)) q x) =
      Sheaf.H.map ((moduleUnderlying R X).map a) q
        (finiteModuleCohomologyDirectImageLinearEquiv R f F q x) := by
  simp only [finiteModuleCohomologyDirectImageLinearEquiv_apply]
  rw [← Sheaf.H.map_comp_apply]
  have h := (moduleDirectImageUnderlyingIso R f).hom.naturality a
  change (moduleUnderlying R S).map ((moduleDirectImage R f).map a) ≫
      (moduleDirectImageUnderlyingIso R f).hom.app G =
    (moduleDirectImageUnderlyingIso R f).hom.app F ≫
      (directImage f).map ((moduleUnderlying R X).map a) at h
  rw [h, Sheaf.H.map_comp_apply]
  exact finiteCohomologyDirectImageAddEquiv_naturality f
    ((moduleUnderlying R X).map a) q _

/-- Finite generation over the original coefficient ring is equivalent for a
finite direct image and its source, without finite-underlying-group assumptions. -/
theorem finite_moduleCohomology_directImage_iff (F : ModuleSheaf R X) (q : ℕ) :
    Module.Finite R
        ((ModuleCat.Sheaf.cohomology S.smallEtaleTopology R q).obj
          ((moduleDirectImage R f).obj F)) ↔
      Module.Finite R ((ModuleCat.Sheaf.cohomology X.smallEtaleTopology R q).obj F) :=
  Module.Finite.equiv_iff (finiteModuleCohomologyDirectImageLinearEquiv R f F q)

end AlgebraicGeometry.Scheme.EtaleCohomology.Finite
