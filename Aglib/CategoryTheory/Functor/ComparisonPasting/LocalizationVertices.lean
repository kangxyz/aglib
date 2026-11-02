/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.CategoryTheory.Whiskering
public import Mathlib.CategoryTheory.EqToHom

/-! # Whole localization vertex comparisons from the original factors

The two original localization comparisons construct one natural isomorphism.
Its components retain their specified order, and the original adjunction
factor equations identify the transported unit and counit. The construction
applies to bounded-below and unbounded localization without identifying their
categories or choosing any additional realization.
-/

@[expose] public noncomputable section

namespace CategoryTheory.Functor

universe uC vC uD vD uC' vC' uD' vD'

variable {C : Type uC} [Category.{vC} C] {D : Type uD} [Category.{vD} D]
  {C' : Type uC'} [Category.{vC'} C'] {D' : Type uD'} [Category.{vD'} D']
  {F : D ⥤ C} {G : C ⥤ D} {Q : C ⥤ C'} {P : D ⥤ D'}
  {F' : D' ⥤ C'} {G' : C' ⥤ D'}

/-- The whole vertex comparison built from its two specified localization factors. -/
def compositeLocalizationIso (a : F ⋙ Q ≅ P ⋙ F') (b : G ⋙ P ≅ Q ⋙ G') :
    G ⋙ F ⋙ Q ≅ Q ⋙ G' ⋙ F' :=
  NatIso.ofComponents (fun K => a.app (G.obj K) ≪≫ F'.mapIso (b.app K)) (by
    intro K L f
    change Q.map (F.map (G.map f)) ≫
        (a.hom.app (G.obj L) ≫ F'.map (b.hom.app L)) =
      (a.hom.app (G.obj K) ≫ F'.map (b.hom.app K)) ≫
        F'.map (G'.map (Q.map f))
    have ha := a.hom.naturality (G.map f)
    have hb := b.hom.naturality f
    simp only [comp_map] at ha hb
    rw [← Category.assoc, ha, Category.assoc, ← F'.map_comp, hb]
    simp only [map_comp, Category.assoc])

/-- Each component is the original first factor followed by the mapped second factor. -/
theorem compositeLocalizationIso_app (a : F ⋙ Q ≅ P ⋙ F')
    (b : G ⋙ P ≅ Q ⋙ G') (K : C) :
    (compositeLocalizationIso a b).app K =
      a.app (G.obj K) ≪≫ F'.mapIso (b.app K) := rfl

/-- Replace only the source presentation using its actual object and map equalities. -/
def isoOfSourceMap {T V W : C ⥤ C'} (e : V ≅ W)
    (hobj : T.obj = V.obj) (hmap : HEq (@T.map) (@V.map)) : T ≅ W := by
  have h : T = V := by
    cases T
    cases V
    cases hobj
    cases hmap
    rfl
  exact eqToIso h ≪≫ e

/-- Equality of source functors changes no component of the specified comparison. -/
theorem isoOfSourceMap_hom_app {T V W : C ⥤ C'} (e : V ≅ W)
    (hobj : T.obj = V.obj) (hmap : HEq (@T.map) (@V.map)) (K : C) :
    (isoOfSourceMap e hobj hmap).hom.app K =
      eqToHom (congrFun hobj K) ≫ e.hom.app K := by
  cases T
  cases V
  cases hobj
  cases hmap
  simp [isoOfSourceMap]

/-- The original counit factor equation identifies the whole vertex comparison. -/
theorem compositeLocalizationIso_counit (a : F ⋙ Q ≅ P ⋙ F')
    (b : G ⋙ P ≅ Q ⋙ G') (ε : G ⋙ F ⟶ 𝟭 C) (ε' : G' ⋙ F' ⟶ 𝟭 C')
    (h : ∀ K, F'.map (b.hom.app K) ≫ ε'.app (Q.obj K) =
      a.inv.app (G.obj K) ≫ Q.map (ε.app K)) (K : C) :
    (compositeLocalizationIso a b).hom.app K ≫ ε'.app (Q.obj K) =
      Q.map (ε.app K) := by
  change (a.hom.app (G.obj K) ≫ F'.map (b.hom.app K)) ≫ _ = _
  rw [Category.assoc, h, ← Category.assoc, Iso.hom_inv_id_app, Category.id_comp]

/-- A counit expressed by the inverse original factors gives the same comparison. -/
theorem compositeLocalizationIso_counit_of_formula (a : F ⋙ Q ≅ P ⋙ F')
    (b : G ⋙ P ≅ Q ⋙ G') (ε : G ⋙ F ⟶ 𝟭 C) (ε' : G' ⋙ F' ⟶ 𝟭 C')
    (h : ∀ K, ε'.app (Q.obj K) = F'.map (b.inv.app K) ≫
      a.inv.app (G.obj K) ≫ Q.map (ε.app K)) (K : C) :
    (compositeLocalizationIso a b).hom.app K ≫ ε'.app (Q.obj K) =
      Q.map (ε.app K) := by
  apply compositeLocalizationIso_counit a b ε ε' _ K
  intro L
  rw [h]
  simp only [← Category.assoc, ← map_comp, Iso.hom_inv_id_app, map_id, Category.id_comp]

/-- The original unit factor equation identifies the whole closed-vertex comparison. -/
theorem compositeLocalizationIso_unit (a : F ⋙ Q ≅ P ⋙ F')
    (b : G ⋙ P ≅ Q ⋙ G') (η : 𝟭 C ⟶ G ⋙ F) (η' : 𝟭 C' ⟶ G' ⋙ F')
    (h : ∀ K, η'.app (Q.obj K) ≫ F'.map (b.inv.app K) =
      Q.map (η.app K) ≫ a.hom.app (G.obj K)) (K : C) :
    Q.map (η.app K) ≫ (compositeLocalizationIso a b).hom.app K =
      η'.app (Q.obj K) := by
  change _ ≫ (a.hom.app (G.obj K) ≫ F'.map (b.hom.app K)) = _
  rw [← Category.assoc, ← h, Category.assoc, ← F'.map_comp, Iso.inv_hom_id_app]
  exact (congrArg (fun t => η'.app (Q.obj K) ≫ t)
    (F'.map_id ((Q ⋙ G').obj K))).trans (Category.comp_id _)

end CategoryTheory.Functor
