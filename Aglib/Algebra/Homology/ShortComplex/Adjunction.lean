/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.ShortComplex.MapHomology

/-!
# The canonical adjunction mate on homology

An additive adjunction whose right adjoint preserves homology gives a canonical
map from the left adjoint of homology to the homology of the left-adjoint image.
It is the mate of the actual adjunction unit, normalized by the native homology
comparisons. Its unit equation and naturality retain the original maps.

When the displayed homologies are preserved by the left adjoint, this mate is
the inverse of the native homology-comparison isomorphism. No scalar extension
or finite-projective hypothesis is needed in this generic owner.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Adjunction

variable {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
  {F : C ⥤ D} {G : D ⥤ C} [F.Additive] [G.Additive] [G.PreservesHomology]

/-- Homology of the original adjunction unit, normalized by the native homology
comparisons for the identity functor and the right adjoint. -/
def homologyUnit (adj : F ⊣ G) (S : ShortComplex C) :
    S.homology ⟶ G.obj (S.map F).homology :=
  (S.mapHomologyIso (𝟭 C)).inv ≫
    ShortComplex.homologyMap (S.mapNatTrans adj.unit) ≫
      ((S.map F).mapHomologyIso G).hom

/-- The canonical homology comparison is the actual mate of the unit on homology. -/
def homologyComparison (adj : F ⊣ G) (S : ShortComplex C) :
    F.obj S.homology ⟶ (S.map F).homology :=
  (adj.homEquiv _ _).symm (adj.homologyUnit S)

/-- The homology comparison retains the original adjunction-unit equation. -/
theorem homologyComparison_unit (adj : F ⊣ G) (S : ShortComplex C) :
    adj.unit.app S.homology ≫ G.map (adj.homologyComparison S) = adj.homologyUnit S :=
  (adj.homEquiv _ _).apply_symm_apply _

/-- The original homology unit is natural in the coefficient short complex. -/
theorem homologyUnit_naturality (adj : F ⊣ G) {S T : ShortComplex C} (f : S ⟶ T) :
    ShortComplex.homologyMap f ≫ adj.homologyUnit T =
      adj.homologyUnit S ≫ G.map (ShortComplex.homologyMap (F.mapShortComplex.map f)) := by
  have hu : f ≫ T.mapNatTrans adj.unit =
      S.mapNatTrans adj.unit ≫ (F ⋙ G).mapShortComplex.map f := by
    ext <;> exact adj.unit.naturality _
  have hId : (𝟭 C).mapShortComplex.map f = f := by ext <;> rfl
  have hComp : (F ⋙ G).mapShortComplex.map f =
      G.mapShortComplex.map (F.mapShortComplex.map f) := by ext <;> rfl
  have hh := congrArg (fun q => ShortComplex.homologyMap q) hu
  simp only [ShortComplex.homologyMap_comp] at hh
  unfold homologyUnit
  calc
    _ = (S.mapHomologyIso (𝟭 C)).inv ≫ ShortComplex.homologyMap f ≫
        ShortComplex.homologyMap (T.mapNatTrans adj.unit) ≫
          ((T.map F).mapHomologyIso G).hom := by
      simpa only [Category.assoc, Functor.id_map, hId] using congrArg
        (fun q => q ≫ ShortComplex.homologyMap (T.mapNatTrans adj.unit) ≫
          ((T.map F).mapHomologyIso G).hom)
        (ShortComplex.mapHomologyIso_inv_naturality f (𝟭 C))
    _ = (S.mapHomologyIso (𝟭 C)).inv ≫
        ShortComplex.homologyMap (S.mapNatTrans adj.unit) ≫
          ShortComplex.homologyMap ((F ⋙ G).mapShortComplex.map f) ≫
            ((T.map F).mapHomologyIso G).hom := by
      simpa only [Category.assoc] using congrArg
        (fun q => (S.mapHomologyIso (𝟭 C)).inv ≫ q ≫
          ((T.map F).mapHomologyIso G).hom) hh
    _ = _ := by
      simpa only [Category.assoc, ← hComp, Functor.mapShortComplex_obj] using congrArg
        (fun q => (S.mapHomologyIso (𝟭 C)).inv ≫
          ShortComplex.homologyMap (S.mapNatTrans adj.unit) ≫ q)
        (ShortComplex.mapHomologyIso_hom_naturality (F.mapShortComplex.map f) G)

/-- Naturality retains the actual mapped coefficient arrow on both sides. -/
@[reassoc]
theorem homologyComparison_naturality (adj : F ⊣ G) {S T : ShortComplex C} (f : S ⟶ T) :
    F.map (ShortComplex.homologyMap f) ≫ adj.homologyComparison T =
      adj.homologyComparison S ≫ ShortComplex.homologyMap (F.mapShortComplex.map f) := by
  apply (adj.homEquiv _ _).injective
  rw [adj.homEquiv_naturality_left, adj.homEquiv_naturality_right]
  simp only [homologyComparison, Equiv.apply_symm_apply]
  exact adj.homologyUnit_naturality f

/-- When the displayed left homologies are preserved, the adjunction mate is
exactly the inverse of the native homology-comparison isomorphism. -/
theorem homologyComparison_eq_mapHomologyIso_inv (adj : F ⊣ G) (S : ShortComplex C)
    [F.PreservesLeftHomologyOf S] [F.PreservesRightHomologyOf S]
    [(F ⋙ G).PreservesLeftHomologyOf S] [(F ⋙ G).PreservesRightHomologyOf S] :
    adj.homologyComparison S = (S.mapHomologyIso F).inv := by
  apply (adj.homEquiv _ _).injective
  apply (cancel_mono (G.map (S.mapHomologyIso F).hom)).mp
  simp only [homologyComparison, Equiv.apply_symm_apply, homologyUnit,
    ShortComplex.homologyMap_mapNatTrans, Adjunction.homEquiv_unit,
    Category.assoc, Iso.inv_hom_id_assoc]
  rw [← ShortComplex.mapHomologyIso_comp_hom_of_preservesLeftHomology F G S]
  simp [← G.map_comp]

end CategoryTheory.Adjunction
