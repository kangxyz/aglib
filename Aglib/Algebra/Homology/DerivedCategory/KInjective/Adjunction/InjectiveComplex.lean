/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.DerivedCategory.KInjective.Adjunction
public import Mathlib.CategoryTheory.Preadditive.Injective.Preserves

/-!
# Derived Hom adjunction at bounded-below injective targets

When an additive left adjoint preserves monomorphisms, its ordinary right
adjoint sends injectives to injectives. Both the original bounded-below
injective target and its actual right-adjoint image are therefore
K-injective. The pointwise derived Hom adjunction requires no supplied
K-injectivity conditions and retains the original chain-adjoint maps.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits

universe u v w u' v' w'

namespace CategoryTheory.Adjunction

variable {C : Type u} [Category.{v} C] [Abelian C]
    {D : Type u'} [Category.{v'} D] [Abelian D]
    {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G) [G.Additive]
    [F.PreservesMonomorphisms]

include adj in
/-- The actual right-adjoint image of a bounded-below injective complex is
K-injective when the original left adjoint preserves monomorphisms. -/
theorem isKInjective_map_of_injectiveComplex
    (I : CochainComplex D ℤ) (a : ℤ) [I.IsStrictlyGE a]
    [∀ n : ℤ, Injective (I.X n)] :
    CochainComplex.IsKInjective ((G.mapHomologicalComplex (.up ℤ)).obj I) := by
  let : G.PreservesInjectiveObjects :=
    Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms adj
  let J : CochainComplex C ℤ := (G.mapHomologicalComplex (.up ℤ)).obj I
  let : J.IsStrictlyGE a := by dsimp [J]; infer_instance
  let : ∀ n : ℤ, Injective (J.X n) := fun n => by
    change Injective (G.obj (I.X n))
    infer_instance
  exact CochainComplex.isKInjective_of_injective J a

variable [HasDerivedCategory.{w} C] [HasDerivedCategory.{w'} D] [F.Additive]

/-- An ordinary adjunction computes actual derived Hom at every supplied
bounded-below complex of injectives. Both K-injectivity conditions are proved. -/
def cochainDerivedHomEquivOfInjectiveComplex (K : CochainComplex C ℤ)
    (I : CochainComplex D ℤ) (a : ℤ) [I.IsStrictlyGE a]
    [∀ n : ℤ, Injective (I.X n)] :
    (DerivedCategory.Q.obj ((F.mapHomologicalComplex (.up ℤ)).obj K) ⟶
      DerivedCategory.Q.obj I) ≃+
    (DerivedCategory.Q.obj K ⟶
      DerivedCategory.Q.obj ((G.mapHomologicalComplex (.up ℤ)).obj I)) := by
  let : I.IsKInjective := CochainComplex.isKInjective_of_injective I a
  let := adj.isKInjective_map_of_injectiveComplex I a
  exact adj.cochainDerivedHomEquivOfKInjective K I

/-- The derived equivalence sends each original chain map to its original
ordinary chain adjoint, with no replacement of either map. -/
@[simp]
theorem cochainDerivedHomEquivOfInjectiveComplex_map (K : CochainComplex C ℤ)
    (I : CochainComplex D ℤ) (a : ℤ) [I.IsStrictlyGE a]
    [∀ n : ℤ, Injective (I.X n)]
    (p : (F.mapHomologicalComplex (.up ℤ)).obj K ⟶ I) :
    adj.cochainDerivedHomEquivOfInjectiveComplex K I a (DerivedCategory.Q.map p) =
      DerivedCategory.Q.map ((adj.mapHomologicalComplex (.up ℤ)).homEquiv K I p) := by
  let : I.IsKInjective := CochainComplex.isKInjective_of_injective I a
  let := adj.isKInjective_map_of_injectiveComplex I a
  change adj.cochainDerivedHomEquivOfKInjective K I (DerivedCategory.Q.map p) = _
  exact adj.cochainDerivedHomEquivOfKInjective_map K I p

/-- The inverse likewise retains the original chain adjoint. -/
@[simp]
theorem cochainDerivedHomEquivOfInjectiveComplex_symm_map (K : CochainComplex C ℤ)
    (I : CochainComplex D ℤ) (a : ℤ) [I.IsStrictlyGE a]
    [∀ n : ℤ, Injective (I.X n)]
    (p : K ⟶ (G.mapHomologicalComplex (.up ℤ)).obj I) :
    (adj.cochainDerivedHomEquivOfInjectiveComplex K I a).symm (DerivedCategory.Q.map p) =
      DerivedCategory.Q.map (((adj.mapHomologicalComplex (.up ℤ)).homEquiv K I).symm p) := by
  let : I.IsKInjective := CochainComplex.isKInjective_of_injective I a
  let := adj.isKInjective_map_of_injectiveComplex I a
  change (adj.cochainDerivedHomEquivOfKInjective K I).symm (DerivedCategory.Q.map p) = _
  exact adj.cochainDerivedHomEquivOfKInjective_symm_map K I p

end CategoryTheory.Adjunction
