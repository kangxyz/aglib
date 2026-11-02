/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.FiniteType.Extension.Subobject
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Localization.AffineSectionsGlobal
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Affine.FiniteGenerators
public import Mathlib.AlgebraicGeometry.QuasiAffine

/-! # Finite global generators on an original quasi-affine scheme

The canonical affine open immersion, its actual direct image and restriction
counit, and the existing finite-type subsheaf extension produce generators of
the original module. No Noetherian hypothesis or substitute module is used.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.Modules.QuasiCoherent

universe u

variable (X : Scheme.{u}) [X.IsQuasiAffine] (M : X.Modules)

/-- Finite-type quasicoherent modules on a quasi-affine scheme admit an
actual finite global generating family. Quasi-affineness includes compactness. -/
theorem quasiAffine_exists_finiteGeneratingSections
    (hM : affineLocallyFiniteType X M) :
    ∃ G : M.GeneratingSections, G.IsFiniteType := by
  let : M.IsQuasicoherent :=
    quasicoherent_of_affineCharts M (fun R j _ => (hM R j).1)
  let j := X.toSpecΓ
  let P := (Scheme.Modules.pushforward j).obj M
  let : P.IsQuasicoherent := quasicoherent_pushforward_open j M
  let c : P.restrict j ≅ M := (restrictFunctorAdjCounitIso j).app M
  obtain ⟨B, b, hb, e, he⟩ :=
    affineLocallyFiniteType_subobject_extension_affine_of_quasiCompact
      Γ(X, ⊤) j P (⟨M, hM⟩ : FiniteTypeSheaves X) c.inv
  obtain ⟨G, hG⟩ := affineFiniteSheaf_exists_generatingSections Γ(X, ⊤)
    ((affineLocallyFiniteType_spec_iff Γ(X, ⊤) B.obj).mp B.property)
  have : PreservesColimitsOfSize.{u, u} (restrictFunctor j) := inferInstance
  exact ⟨(G.map (restrictFunctor j) (restrictUnitIso j).symm).ofEpi e.hom, inferInstance⟩

/-- The generators give an epimorphism from a finite free original structure module. -/
theorem quasiAffine_exists_finiteFree_epi (hM : affineLocallyFiniteType X M) :
    ∃ I : Type u, Finite I ∧
      ∃ p : SheafOfModules.free (R := X.ringCatSheaf) I ⟶ M, Epi p := by
  obtain ⟨G, hG⟩ := quasiAffine_exists_finiteGeneratingSections X M hM
  exact ⟨G.I, inferInstance, G.π, G.epi⟩

end AlgebraicGeometry.Scheme.Modules.QuasiCoherent
