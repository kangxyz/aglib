/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.EtaleRepresentedModuleTransfer
public import Aglib.AlgebraicGeometry.EtaleCohomology.Fields.FiniteEtaleTransfer.Trace
public import Aglib.CategoryTheory.Preadditive.CoprimeScalar

/-! # Finite-etale module-sheaf trace and retraction

The existing represented transfer and its coefficient-natural abelian sheaf
trace induce a trace in the original ModuleCat-valued sheaf category. Rank
inversion and retraction therefore preserve the scalar structure, without
requiring the underlying additive groups to be finite. Any further functor
preserves this actual module-sheaf retraction.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.Sheaf.Hypercohomology

namespace AlgebraicGeometry.Scheme.EtaleCohomology

open Constructible.Modules

universe u r c h

attribute [local instance] hasSheafifyLarge ModuleCat.Sheaf.hasSheafify

variable (R : Type r) [CommRing R] {X : Scheme.{u}} (Y : Scheme.FiniteEtale X)

/-- Actual finite-etale trace, natural in module coefficients, with its exact
original module adjunction unit and actual constant finite-flat rank. -/
theorem exists_finiteEtale_moduleSheafTrace (n : ℕ)
    (hn : ∀ x : X, Y.obj.hom.finrank x = n) :
    ∃ tr : moduleInverseImage R Y.obj.hom ⋙ moduleDirectImage R Y.obj.hom ⟶
        𝟭 (ModuleSheaf R X),
      ∀ F, (moduleImageAdjunction R Y.obj.hom).unit.app F ≫ tr.app F = n • 𝟙 F := by
  obtain ⟨a, ha⟩ := Scheme.FiniteEtale.exists_freeRepresentable_transfer Y n hn
  let U : X.Etale := (Scheme.FiniteEtale.toEtale X).obj Y
  refine ⟨etaleRepresentedModuleTrace R U a, fun F => ?_⟩
  exact etaleRepresentedModuleTrace_rank R U a n ha F

/-- Coprime rank gives an actual module-linear retraction of the original unit. -/
theorem exists_finiteEtale_moduleSheafRetraction (n : ℕ)
    (hn : ∀ x : X, Y.obj.hom.finrank x = n)
    (F : ModuleSheaf R X) (p : ℕ) (hcop : n.Coprime p)
    (hp : p • 𝟙 F = 0) :
    ∃ r : (moduleDirectImage R Y.obj.hom).obj ((moduleInverseImage R Y.obj.hom).obj F) ⟶ F,
      (moduleImageAdjunction R Y.obj.hom).unit.app F ≫ r = 𝟙 F := by
  obtain ⟨tr, htr⟩ := exists_finiteEtale_moduleSheafTrace R Y n hn
  let : IsIso (n • 𝟙 F) := Preadditive.isIso_nsmul_id_of_coprime F n p hcop hp
  refine ⟨tr.app F ≫ inv (n • 𝟙 F), ?_⟩
  rw [← Category.assoc, htr F]
  exact IsIso.hom_inv_id (n • 𝟙 F)

/-- The exact module-sheaf unit is split under the coprime-annihilator hypotheses. -/
theorem finiteEtale_moduleUnit_isSplitMono (n : ℕ)
    (hn : ∀ x : X, Y.obj.hom.finrank x = n)
    (F : ModuleSheaf R X) (p : ℕ) (hcop : n.Coprime p)
    (hp : p • 𝟙 F = 0) :
    IsSplitMono ((moduleImageAdjunction R Y.obj.hom).unit.app F) := by
  obtain ⟨r, hr⟩ := exists_finiteEtale_moduleSheafRetraction R Y n hn F p hcop hp
  exact IsSplitMono.mk' ⟨r, hr⟩

/-- Any further functor preserves the genuine scalar-linear sheaf retraction. -/
theorem exists_finiteEtale_moduleSheafRetraction_map (n : ℕ)
    (hn : ∀ x : X, Y.obj.hom.finrank x = n)
    (F : ModuleSheaf R X) (p : ℕ) (hcop : n.Coprime p)
    (hp : p • 𝟙 F = 0) {C : Type c} [Category.{h} C]
    (G : ModuleSheaf R X ⥤ C) :
    ∃ r : G.obj ((moduleDirectImage R Y.obj.hom).obj
        ((moduleInverseImage R Y.obj.hom).obj F)) ⟶ G.obj F,
      G.map ((moduleImageAdjunction R Y.obj.hom).unit.app F) ≫ r = 𝟙 _ := by
  obtain ⟨r, hr⟩ := exists_finiteEtale_moduleSheafRetraction R Y n hn F p hcop hp
  refine ⟨G.map r, ?_⟩
  exact (G.map_comp _ _).symm.trans ((congrArg G.map hr).trans (G.map_id F))

end AlgebraicGeometry.Scheme.EtaleCohomology
