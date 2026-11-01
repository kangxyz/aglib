/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Coherent.Support.Hypersurface

/-! The scalar hypersurface formula uses no regularity or Noetherian premise. -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.QuasiCoherent
open AlgebraicGeometry.Scheme.Modules.Invertible SheafOfModulesOfCommRing

universe u

example {X : Scheme.{u}} (M : X.Modules) (hM : affineLocallyFiniteType X M) (a : Γ(X, ⊤)) :
    support (cokernel (globalScalarEndomorphism X M a)) =
      support M ∩ (X.basicOpen a : Set X)ᶜ :=
  support_cokernel_globalScalarEndomorphism M hM a

example {X : Scheme.{u}} (L : LineBundle X) (s : Γ(L.val, ⊤))
    (M : X.Modules) (hM : affineLocallyFiniteType X M) :
    support (cokernel ((tensorLeftUnitIso X.sheaf).inv.app M ≫
      (moduleTensorCoefficientMap X ((unitHomGlobalSectionsEquiv X L.val).symm s)).app M)) =
      support M ∩ (nonvanishingOpen L s : Set X)ᶜ :=
  support_cokernel_tensor_section L s M hM

end
