/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Continuity.PullbackUnitSections

/-! # Original unit representatives and relative section transport -/

@[expose] public noncomputable section

open CategoryTheory Limits Opposite

private theorem map_op_iso_factor {C D : Type*} [Category C] [Category D]
    (P : Cᵒᵖ ⥤ D) {A B E H : C} (i : A ≅ B) (a : E ⟶ B) (b : H ⟶ E) :
    P.map i.hom.op ≫ P.map (b ≫ a ≫ i.inv).op = P.map a.op ≫ P.map b.op := by
  have h : (b ≫ a ≫ i.inv) ≫ i.hom = b ≫ a := by simp only [Category.assoc,
    Iso.inv_hom_id, Category.comp_id]
  simpa only [op_comp, Functor.map_comp] using congrArg (fun k => P.map k.op) h

private theorem unit_section_composition {C : Type*} [Category C]
    {A B C₀ D E H J K L : C}
    (u : A ⟶ B) (a : B ⟶ C₀) (v : C₀ ⟶ D) (b : D ⟶ E) (k : E ⟶ H)
    (v₀ : B ⟶ J) (a₀ : J ⟶ D) (c : J ⟶ K) (d : K ⟶ E)
    (u₀ : A ⟶ L) (t : L ⟶ K) (p : L ⟶ H) (tW : H ⟶ E)
    (hn : a ≫ v = v₀ ≫ a₀) (hm : c ≫ d = a₀ ≫ b)
    (hu : u ≫ v₀ ≫ c = u₀ ≫ t) (hc : t ≫ d = p ≫ tW) (hi : tW ≫ k = 𝟙 H) :
    (u ≫ a) ≫ (v ≫ b) ≫ k = u₀ ≫ p := by
  calc
    (u ≫ a) ≫ (v ≫ b) ≫ k = (u ≫ (a ≫ v)) ≫ b ≫ k := by simp only [Category.assoc]
    _ = (u ≫ (v₀ ≫ a₀)) ≫ b ≫ k := by rw [hn]
    _ = (u ≫ v₀) ≫ (a₀ ≫ b) ≫ k := by simp only [Category.assoc]
    _ = (u ≫ v₀) ≫ (c ≫ d) ≫ k := by rw [← hm]
    _ = ((u ≫ v₀) ≫ c) ≫ d ≫ k := by simp only [Category.assoc]
    _ = (u₀ ≫ t) ≫ d ≫ k := by rw [Category.assoc u v₀ c, hu]
    _ = u₀ ≫ ((t ≫ d) ≫ k) := by simp only [Category.assoc]
    _ = u₀ ≫ ((p ≫ tW) ≫ k) := by rw [hc]
    _ = u₀ ≫ p := by rw [Category.assoc p tW k, hi, Category.comp_id]

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Continuity

universe u

attribute [local instance] hasSheafifyLarge

/-- An original inverse-image unit followed by restriction on a test scheme. -/
def unitSectionMap {X S : Scheme.{u}} (f : S ⟶ X)
    (F : AbelianSheaf.{u, u + 1} X) {U : X.Etale} {V : S.Etale}
    (a : V ⟶ (siteBaseChange f).obj U) :
    F.obj.obj (op U) ⟶ ((inverseImage f).obj F).obj.obj (op V) :=
  ((inverseImageAdjunction f).unit.app F).hom.app (op U) ≫
    ((inverseImage f).obj F).obj.map a.op

/-- The actual composite test morphism uses the original pullback-composition iso. -/
def composedTestMap {X S T : Scheme.{u}} (f : S ⟶ X) (g : T ⟶ S)
    {U : X.Etale} {V : S.Etale} {W : T.Etale}
    (a : V ⟶ (siteBaseChange f).obj U) (b : W ⟶ (siteBaseChange g).obj V) :
    W ⟶ (siteBaseChange (g ≫ f)).obj U :=
  b ≫ (siteBaseChange g).map a ≫ (siteBaseChangeComp f g).inv.app U

/-- Composition of original local unit representatives, through the native coefficient iso. -/
theorem unitSectionMap_comp {X S T : Scheme.{u}} (f : S ⟶ X) (g : T ⟶ S)
    (F : AbelianSheaf.{u, u + 1} X) {U : X.Etale} {V : S.Etale} {W : T.Etale}
    (a : V ⟶ (siteBaseChange f).obj U) (b : W ⟶ (siteBaseChange g).obj V) :
    unitSectionMap f F a ≫ unitSectionMap g ((inverseImage f).obj F) b ≫
        ((inverseImageComp f g).inv.app F).hom.app (op W) =
      unitSectionMap (g ≫ f) F (composedTestMap f g a b) := by
  let P := ((inverseImage g).obj ((inverseImage f).obj F)).obj
  let c := composedTestMap f g a b
  have hn := ((inverseImageAdjunction g).unit.app ((inverseImage f).obj F)).hom.naturality a.op
  have hm := map_op_iso_factor P ((siteBaseChangeComp f g).app U)
    ((siteBaseChange g).map a) b
  have hu := EtaleAffineBasis.inverseImageUnit_comp f g F U
  have hc := (((inverseImageComp f g).hom.app F).hom.naturality c.op).symm
  have hi : ((inverseImageComp f g).hom.app F).hom.app (op W) ≫
      ((inverseImageComp f g).inv.app F).hom.app (op W) = 𝟙 _ :=
    congrArg (fun q => q.hom.app (op W)) ((inverseImageComp f g).hom_inv_id_app F)
  exact unit_section_composition _ _ _ _ _ _ _ _ _ _ _ _ _ hn hm hu hc hi

end AlgebraicGeometry.Scheme.EtaleCohomology.Continuity
