/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.Modules.LocallyFree.Basic
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Affine.FiniteType

/-!
# Finite-type affine global sections of finite locally free sheaves
-/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace

namespace AlgebraicGeometry.Scheme.Modules

/-- Every finite locally free sheaf on an affine scheme has a finite module
of global sections. No noetherianity or globally free assumption is needed. -/
theorem finite_globalSections_of_finiteLocallyFree (R : CommRingCat.{u})
    (M : (Spec R).Modules) [hM : IsFiniteLocallyFree (Spec R) M] :
    Module.Finite R (moduleSpecΓFunctor.obj M) := by
  obtain ⟨q, hq, hf⟩ := hM.exists_localBasis
  exact finite_globalSections_of_localGenerators R M q

/-- Finite locally free sheaves satisfy the actual affine finite
quasicoherent predicate. -/
theorem affineFiniteSheaf_of_finiteLocallyFree (R : CommRingCat.{u})
    (M : (Spec R).Modules) [IsFiniteLocallyFree (Spec R) M] :
    Scheme.Modules.QuasiCoherent.affineFiniteSheaf R M :=
  ⟨inferInstance, finite_globalSections_of_finiteLocallyFree R M⟩

end AlgebraicGeometry.Scheme.Modules
