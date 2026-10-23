/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Modules.Scalars
public import Aglib.AlgebraicGeometry.Modules.StructureSheaf.Hom
public import Aglib.AlgebraicGeometry.Modules.Tensor.Monoidal.Basic

/-!
# Global sections as morphisms out of the unit module

`Scheme.Cohomology.unitHomH0Equiv M : (𝟙_ ⟶ M) ≃ H^0(X, M)` composes
`Scheme.Modules.unitHomGlobalSectionsEquiv` with `Sheaf.H.equiv₀`, for every scheme `X` and module
`M`. It is natural: composing a section with `g : M ⟶ N` is applying `H^0(g)`, linearly over any
structural ring map `α : R →+* Γ(X, ⊤)` (`unitHomH0Equiv_comp`).
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.MonoidalCategory

universe u

namespace AlgebraicGeometry.Scheme.Cohomology

/-- **Global sections as elements of `H^0`**: morphisms `𝟙_ ⟶ M` from the unit module are the
elements of `H^0(X, M)` (`unitHomGlobalSectionsEquiv`, then `Sheaf.H.equiv₀`). -/
def unitHomH0Equiv {X : Scheme.{u}} (M : X.Modules) :
    (𝟙_ X.Modules ⟶ M) ≃ Sheaf.H.{u + 1} (moduleAddSheaf X M) 0 :=
  (Scheme.Modules.unitHomGlobalSectionsEquiv X M).trans
    (Sheaf.H.equiv₀ (moduleAddSheaf X M) Limits.isTerminalTop).symm.toEquiv

-- The section of `s ≫ g` is compared with `H^0(g)` through the presentation of `Sheaf.H`.
set_option backward.isDefEq.respectTransparency false in
/-- `unitHomH0Equiv` is natural: composing a section with `g` is applying `H^0(g)`. -/
theorem unitHomH0Equiv_comp {X : Scheme.{u}} {R : Type u} [CommRing R] (α : R →+* Γ(X, ⊤))
    {M N : X.Modules} (s : 𝟙_ X.Modules ⟶ M) (g : M ⟶ N) :
    unitHomH0Equiv N (s ≫ g) = moduleCohomologyMapOfHom X α g 0 (unitHomH0Equiv M s) := by
  change (Sheaf.H.equiv₀ (moduleAddSheaf X N) Limits.isTerminalTop).symm
      (Scheme.Modules.Hom.app g ⊤ (Scheme.Modules.unitHomGlobalSectionsEquiv X M s)) =
    Sheaf.H.map ((SheafOfModules.toSheaf X.ringCatSheaf).map g) 0
      ((Sheaf.H.equiv₀ (moduleAddSheaf X M) Limits.isTerminalTop).symm
        (Scheme.Modules.unitHomGlobalSectionsEquiv X M s))
  rw [Sheaf.H.equiv₀_symm_naturality]
  rfl

end AlgebraicGeometry.Scheme.Cohomology
