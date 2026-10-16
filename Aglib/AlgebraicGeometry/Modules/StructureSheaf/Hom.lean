/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.StructureSheaf.Sections
public import Aglib.CategoryTheory.Functor.Sections.Initial

/-!
# Morphisms from the actual structure module and global sections

The original unit-module Hom equivalence, followed by evaluation of native
sections at the whole space, identifies morphisms from the structure module
with global sections. Its forward map is evaluation on one, and the inverse
uses the original restriction maps. Global structure-module multiplication
also preserves zero and addition.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

namespace AlgebraicGeometry.Scheme.Modules

universe u

/-- The original unit-module Hom equivalence evaluated at the actual whole open. -/
def unitHomGlobalSectionsEquiv (X : Scheme.{u}) (M : X.Modules) :
    (SheafOfModules.unit X.ringCatSheaf ⟶ M) ≃ Γ(M, ⊤) :=
  M.unitHomEquiv.trans
    ((M.presheaf ⋙ CategoryTheory.forget AddCommGrpCat.{u}).sectionsEquivOfIsInitial
      (isTerminalTop (α := X.Opens)).op)

/-- The unit-module Hom equivalence is evaluation of the original morphism on one. -/
theorem unitHomGlobalSectionsEquiv_apply (X : Scheme.{u}) (M : X.Modules)
    (f : SheafOfModules.unit X.ringCatSheaf ⟶ M) :
    unitHomGlobalSectionsEquiv X M f =
      Scheme.Modules.Hom.app f ⊤ (1 : Γ(X, ⊤)) := rfl

/-- The original unit-module Hom/global-section comparison is additive. -/
def unitHomGlobalSectionsAddEquiv (X : Scheme.{u}) (M : X.Modules) :
    (SheafOfModules.unit X.ringCatSheaf ⟶ M) ≃+ Γ(M, ⊤) where
  __ := unitHomGlobalSectionsEquiv X M
  map_add' f g := by
    change Scheme.Modules.Hom.app (f + g) ⊤ (1 : Γ(X, ⊤)) =
      Scheme.Modules.Hom.app f ⊤ (1 : Γ(X, ⊤)) +
        Scheme.Modules.Hom.app g ⊤ (1 : Γ(X, ⊤))
    rw [Hom.add_app]
    rfl

/-- The unit-module/global-section comparison keeps the original coefficient map. -/
theorem unitHomGlobalSectionsEquiv_naturality (X : Scheme.{u}) {M N : X.Modules}
    (f : SheafOfModules.unit X.ringCatSheaf ⟶ M) (g : M ⟶ N) :
    unitHomGlobalSectionsEquiv X N (f ≫ g) =
      Scheme.Modules.Hom.app g ⊤ (unitHomGlobalSectionsEquiv X M f) := rfl

/-- The inverse comparison is multiplication by the original restricted global section. -/
theorem unitHomGlobalSectionsEquiv_symm_app (X : Scheme.{u}) (M : X.Modules)
    (m : Γ(M, ⊤)) (U : X.Opens) (r : Γ(X, U)) :
    Scheme.Modules.Hom.app ((unitHomGlobalSectionsEquiv X M).symm m) U r =
      r • M.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op m := by
  change r • M.presheaf.map ((isTerminalTop (α := X.Opens)).op.to (op U)) m = _
  congr 1

/-- Global structure-module multiplication sends zero to the actual zero morphism. -/
@[simp]
theorem unitMul_zero (X : Scheme.{u}) : unitMul X 0 = 0 := by
  apply Scheme.Modules.hom_ext
  intro U
  ext r
  change Γ(X, U) at r
  change r * (X.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op).hom 0 = 0
  simp

/-- Global structure-module multiplication preserves addition on the actual morphisms. -/
theorem unitMul_add (X : Scheme.{u}) (a b : Γ(X, ⊤)) :
    unitMul X (a + b) = unitMul X a + unitMul X b := by
  apply Scheme.Modules.hom_ext
  intro U
  ext r
  change Γ(X, U) at r
  change r * (X.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op).hom (a + b) =
    r * (X.presheaf.map (homOfLE le_top).op).hom a +
      r * (X.presheaf.map (homOfLE le_top).op).hom b
  simp [mul_add]

end AlgebraicGeometry.Scheme.Modules
