/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.StructureSheaf.Hom
public import Mathlib.Algebra.Category.ModuleCat.Limits
public import Mathlib.CategoryTheory.Limits.Types.Limits
public import Mathlib.CategoryTheory.Limits.Yoneda

/-! # Original unit-Hom cones and section cones

The native unit-Hom/global-section equivalence transports the universal
property, retaining all original coefficient maps. No new section object or
replacement limit is chosen.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.Modules

universe u v w

/-- A limiting original section cone is also limiting on maps from the actual unit module. -/
theorem unitCoyoneda_isLimit_of_sections (X : Scheme.{u})
    {J : Type v} [Category.{w} J] {F : J ⥤ X.Modules} (c : Cone F)
    (h : IsLimit ((SheafOfModules.evaluation X.ringCatSheaf (op ⊤)).mapCone c)) :
    Nonempty (IsLimit ((coyoneda.obj (op (SheafOfModules.unit X.ringCatSheaf))).mapCone c)) := by
  let E := SheafOfModules.evaluation X.ringCatSheaf (op ⊤)
  have hT := isLimitOfPreserves (CategoryTheory.forget (ModuleCat.{u} Γ(X, ⊤))) h
  have hu := (Types.isLimit_iff _).mp ⟨hT⟩
  apply (Types.isLimit_iff _).mpr
  intro s hs
  let t (j : J) := unitHomGlobalSectionsEquiv X (F.obj j) (s j)
  have ht : t ∈ (F ⋙ E ⋙ CategoryTheory.forget (ModuleCat.{u} Γ(X, ⊤))).sections := by
    intro j k f
    change Hom.app (F.map f) ⊤ (t j) = t k
    exact (unitHomGlobalSectionsEquiv_naturality X (s j) (F.map f)).symm.trans
      (congrArg (unitHomGlobalSectionsEquiv X (F.obj k)) (hs f))
  obtain ⟨x, hx, huniq⟩ := hu t ht
  let a := (unitHomGlobalSectionsEquiv X c.pt).symm x
  have ha (j : J) : a ≫ c.π.app j = s j := by
    apply (unitHomGlobalSectionsEquiv X (F.obj j)).injective
    calc
      unitHomGlobalSectionsEquiv X (F.obj j) (a ≫ c.π.app j) =
          Hom.app (c.π.app j) ⊤ x := by
        rw [unitHomGlobalSectionsEquiv_naturality]
        exact congrArg (Hom.app (c.π.app j) ⊤)
          ((unitHomGlobalSectionsEquiv X c.pt).apply_symm_apply x)
      _ = t j := hx j
  refine ⟨a, ha, ?_⟩
  intro b hb
  apply (unitHomGlobalSectionsEquiv X c.pt).injective
  have hbx : unitHomGlobalSectionsEquiv X c.pt b = x := by
    apply huniq
    intro j
    exact (unitHomGlobalSectionsEquiv_naturality X b (c.π.app j)).symm.trans
      (congrArg (unitHomGlobalSectionsEquiv X (F.obj j)) (hb j))
  exact hbx.trans ((unitHomGlobalSectionsEquiv X c.pt).apply_symm_apply x).symm

end AlgebraicGeometry.Scheme.Modules
