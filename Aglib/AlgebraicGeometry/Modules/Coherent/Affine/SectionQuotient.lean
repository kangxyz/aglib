/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Affine.FiniteTypeComparison
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Affine.TildeExact

/-!
# Actual affine quotients from section presentations

A surjection from the actual sections of a quasicoherent ambient module
produces its canonical tilde quotient. Both the original section map and
its finite target module are retained.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Modules.QuasiCoherent

namespace AlgebraicGeometry.Scheme.Modules.Coherent

universe u
variable {R : CommRingCat.{u}} (M : (Spec R).Modules) [M.IsQuasicoherent]
  (N : ModuleCat.{u} R) (q : moduleSpecΓFunctor.obj M ⟶ N)

/-- The quotient associated with the actual section presentation, using the
original affine counit to identify the ambient module. -/
def affineQuotientFromSections : M ⟶ tilde N :=
  (asIso M.fromTildeΓ).inv ≫ tilde.map q

/-- A surjective section presentation gives a sheaf epimorphism. -/
theorem affineQuotientFromSections_epi (hq : Function.Surjective q) :
    Epi (affineQuotientFromSections M N q) := by
  let : Epi q := (ModuleCat.epi_iff_surjective q).mpr hq
  have : Epi (tilde.map q) := inferInstanceAs (Epi ((tilde.functor R).map q))
  dsimp only [affineQuotientFromSections]
  infer_instance

/-- The quotient has the original section map under the canonical tilde/Gamma
unit, not only an abstract isomorphism of section modules. -/
@[reassoc]
theorem affineQuotientFromSections_sections :
    moduleSpecΓFunctor.map (affineQuotientFromSections M N q) ≫
      (tilde.toTildeΓNatIso.app N).inv = q := by
  have hunit : (tilde.toTildeΓNatIso.app (moduleSpecΓFunctor.obj M)).hom ≫
      moduleSpecΓFunctor.map M.fromTildeΓ = 𝟙 _ :=
    (tilde.adjunction (R := R)).right_triangle_components M
  have hinv : moduleSpecΓFunctor.map (asIso M.fromTildeΓ).inv =
      (tilde.toTildeΓNatIso.app (moduleSpecΓFunctor.obj M)).hom := by
    apply (cancel_mono (moduleSpecΓFunctor.map M.fromTildeΓ)).mp
    rw [← Functor.map_comp, asIso_inv, IsIso.inv_hom_id, CategoryTheory.Functor.map_id]
    exact hunit.symm
  dsimp only [affineQuotientFromSections]
  rw [Functor.map_comp, hinv, Category.assoc]
  have hnat := tilde.toTildeΓNatIso.hom.naturality q
  change q ≫ (tilde.toTildeΓNatIso.app N).hom =
    (tilde.toTildeΓNatIso.app (moduleSpecΓFunctor.obj M)).hom ≫
      moduleSpecΓFunctor.map (tilde.map q) at hnat
  rw [← Category.assoc, ← hnat, Category.assoc, Iso.hom_inv_id, Category.comp_id]

/-- A finite module gives an actual affine-locally finite-type tilde module.
No Noetherianity or finite presentation assumption is needed here. -/
theorem affineLocallyFiniteType_tilde [Module.Finite R N] :
    affineLocallyFiniteType (Spec R) (tilde N) := by
  apply (affineLocallyFiniteType_spec_iff R (tilde N)).mpr
  let e : N ≅ moduleSpecΓFunctor.obj (tilde N) := tilde.toTildeΓNatIso.app N
  exact ⟨inferInstance, Module.Finite.equiv e.toLinearEquiv⟩

end AlgebraicGeometry.Scheme.Modules.Coherent
