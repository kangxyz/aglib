/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Linear.ModuleValued

/-!
# Natural transformations of canonical module-valued lifts

Naturality at the original scalar endomorphisms makes every transformation
between additive functors linear on their canonical module-valued lifts.
Precomposition with a linear functor preserves this scalar action, not merely
the underlying additive carrier.
-/

@[expose] public noncomputable section

namespace CategoryTheory.Functor

universe r u v u' v' w

variable (R : Type r) [CommRing R]

attribute [local instance] moduleObj

section Transformations

variable {C : Type u} [Category.{v} C] [Preadditive C] [CategoryTheory.Linear R C]
  {F G : C ⥤ AddCommGrpCat.{w}} [F.Additive] [G.Additive]

/-- The original additive transformation, linear for the canonical scalar actions. -/
def moduleValuedNatTrans (τ : F ⟶ G) : moduleValued R F ⟶ moduleValued R G where
  app X := ModuleCat.ofHom
    { toAddHom := (τ.app X).hom
      map_smul' r x := by
        change τ.app X (F.map (r • 𝟙 X) x) = G.map (r • 𝟙 X) (τ.app X x)
        exact ConcreteCategory.congr_hom (τ.naturality (r • 𝟙 X)) x }
  naturality X Y f := by
    ext x
    exact ConcreteCategory.congr_hom (τ.naturality f) x

/-- Scalar enrichment leaves the transformation's actual component function unchanged. -/
@[simp]
lemma moduleValuedNatTrans_app_apply (τ : F ⟶ G) (X : C) (x : F.obj X) :
    (moduleValuedNatTrans R τ).app X x = τ.app X x := rfl

/-- The original natural isomorphism, with both directions linear. -/
def moduleValuedNatIso (e : F ≅ G) : moduleValued R F ≅ moduleValued R G where
  hom := moduleValuedNatTrans R e.hom
  inv := moduleValuedNatTrans R e.inv
  hom_inv_id := by
    ext X x
    exact ConcreteCategory.congr_hom (e.hom_inv_id_app X) x
  inv_hom_id := by
    ext X x
    exact ConcreteCategory.congr_hom (e.inv_hom_id_app X) x

/-- The enriched isomorphism retains the original forward map. -/
@[simp]
lemma moduleValuedNatIso_hom_app_apply (e : F ≅ G) (X : C) (x : F.obj X) :
    (moduleValuedNatIso R e).hom.app X x = e.hom.app X x := rfl

end Transformations

section Precomposition

variable {C : Type u} [Category.{v} C] [Preadditive C] [CategoryTheory.Linear R C]
  {D : Type u'} [Category.{v'} D] [Preadditive D] [CategoryTheory.Linear R D]
  (K : C ⥤ D) [K.Additive] [K.Linear R]
  (F : D ⥤ AddCommGrpCat.{w}) [F.Additive]

/-- A linear precomposition preserves the actual canonical scalar action.
The components are identities on the original additive values. -/
def moduleValuedCompIso :
    K ⋙ moduleValued R F ≅ moduleValued R (K ⋙ F) :=
  NatIso.ofComponents (fun X => LinearEquiv.toModuleIso
    { toFun := id
      invFun := id
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := fun r x => by
        change F.map (r • 𝟙 (K.obj X)) x = F.map (K.map (r • 𝟙 X)) x
        rw [K.map_smul, K.map_id] }) (by
    intro X Y f
    ext x
    rfl)

/-- The scalar-compatible precomposition comparison is the identity function. -/
lemma moduleValuedCompIso_hom_app_apply (X : C) (x : F.obj (K.obj X)) :
    (moduleValuedCompIso R K F).hom.app X x = x := rfl

end Precomposition

end CategoryTheory.Functor
