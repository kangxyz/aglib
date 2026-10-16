/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.ShortComplex.Adjunction.Counit
public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
public import Mathlib.CategoryTheory.Adjunction.FullyFaithful

/-!
# Homology under an exact reflector

An additive adjunction with invertible counit and homology-preserving
left adjoint identifies the reflection of the original included homology
with the original homology in the reflective category. Its canonical unit
is the actual adjunction unit followed by this comparison. Reflecting that
unit gives an isomorphism, normalized by the original counit equation.
The right adjoint need not preserve homology.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Adjunction

variable {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
    {F : C ⥤ D} {G : D ⥤ C} [F.Additive] [G.Additive] [F.PreservesHomology]
    (adj : F ⊣ G)

section

variable [IsIso adj.counit]

/-- Reflecting the original included short-complex homology gives the original homology,
using the native homology comparison and original counit. -/
def reflectedHomologyIso (S : ShortComplex D) :
    F.obj (S.map G).homology ≅ S.homology :=
  ((S.map G).mapHomologyIso F).symm ≪≫
    (ShortComplex.homologyFunctor D).mapIso (S.mapNatIso (asIso adj.counit))

/-- The original reflection comparison is natural for actual coefficient maps. -/
@[reassoc]
theorem reflectedHomologyIso_naturality {S T : ShortComplex D} (f : S ⟶ T) :
    F.map (ShortComplex.homologyMap (G.mapShortComplex.map f)) ≫
        (adj.reflectedHomologyIso T).hom =
      (adj.reflectedHomologyIso S).hom ≫ ShortComplex.homologyMap f := by
  have hn : (G ⋙ F).mapShortComplex.map f ≫ T.mapNatTrans adj.counit =
      S.mapNatTrans adj.counit ≫ f := by
    ext <;> exact adj.counit.naturality _
  have hh : ShortComplex.homologyMap ((G ⋙ F).mapShortComplex.map f) ≫
        ShortComplex.homologyMap (T.mapNatTrans adj.counit) =
      ShortComplex.homologyMap (S.mapNatTrans adj.counit) ≫
        ShortComplex.homologyMap f := by
    rw [← ShortComplex.homologyMap_comp, ← ShortComplex.homologyMap_comp, hn]
  have hp : F.map (ShortComplex.homologyMap (G.mapShortComplex.map f)) ≫
        ((T.map G).mapHomologyIso F).inv =
      ((S.map G).mapHomologyIso F).inv ≫
        ShortComplex.homologyMap ((G ⋙ F).mapShortComplex.map f) :=
    ShortComplex.mapHomologyIso_inv_naturality (G.mapShortComplex.map f) F
  change F.map (ShortComplex.homologyMap (G.mapShortComplex.map f)) ≫
      ((T.map G).mapHomologyIso F).inv ≫
        ShortComplex.homologyMap (T.mapNatTrans adj.counit) =
    (((S.map G).mapHomologyIso F).inv ≫
      ShortComplex.homologyMap (S.mapNatTrans adj.counit)) ≫ ShortComplex.homologyMap f
  rw [← Category.assoc, hp, Category.assoc]
  simpa only [Category.assoc] using
    congrArg (fun z => ((S.map G).mapHomologyIso F).inv ≫ z) hh

end

/-- The canonical unit from included homology to the inclusion of original homology. -/
def homologyReflectionUnit [IsIso adj.counit] (S : ShortComplex D) :
    (S.map G).homology ⟶ G.obj S.homology :=
  adj.homologyCounitMate S

section

variable [IsIso adj.counit]

/-- The canonical reflection unit retains actual coefficient naturality. -/
@[reassoc]
theorem homologyReflectionUnit_naturality {S T : ShortComplex D} (f : S ⟶ T) :
    ShortComplex.homologyMap (G.mapShortComplex.map f) ≫ adj.homologyReflectionUnit T =
      adj.homologyReflectionUnit S ≫ G.map (ShortComplex.homologyMap f) := by
  have hu : ShortComplex.homologyMap (G.mapShortComplex.map f) ≫
        adj.unit.app (T.map G).homology =
      adj.unit.app (S.map G).homology ≫
        G.map (F.map (ShortComplex.homologyMap (G.mapShortComplex.map f))) :=
    adj.unit.naturality _
  change ShortComplex.homologyMap (G.mapShortComplex.map f) ≫
      (adj.unit.app (T.map G).homology ≫ G.map (adj.reflectedHomologyIso T).hom) =
    (adj.unit.app (S.map G).homology ≫ G.map (adj.reflectedHomologyIso S).hom) ≫
      G.map (ShortComplex.homologyMap f)
  rw [← Category.assoc, hu, Category.assoc]
  rw [← G.map_comp, adj.reflectedHomologyIso_naturality, G.map_comp]
  exact (Category.assoc _ _ _).symm

/-- After reflection, the original unit and counit give exactly the native homology
comparison. This equation fixes the orientation of the sheafification comparison. -/
@[reassoc]
theorem map_homologyReflectionUnit_counit (S : ShortComplex D) :
    F.map (adj.homologyReflectionUnit S) ≫ adj.counit.app S.homology =
      (adj.reflectedHomologyIso S).hom := by
  exact adj.map_homologyCounitMate_counit S

/-- The image of the original homology reflection unit is invertible. No homology
preservation by the right adjoint is required. -/
theorem map_homologyReflectionUnit_isIso (S : ShortComplex D) :
    IsIso (F.map (adj.homologyReflectionUnit S)) := by
  have hu : F.map (adj.homologyReflectionUnit S) =
      (adj.reflectedHomologyIso S).hom ≫ inv (adj.counit.app S.homology) := by
    apply (cancel_mono (adj.counit.app S.homology)).mp
    rw [Category.assoc, IsIso.inv_hom_id, Category.comp_id]
    exact adj.map_homologyReflectionUnit_counit S
  rw [hu]
  infer_instance

end

end CategoryTheory.Adjunction
