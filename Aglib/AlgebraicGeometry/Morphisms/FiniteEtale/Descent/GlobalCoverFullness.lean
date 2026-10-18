/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.Descent.GlobalOpenCoverColimits

/-!
# GlobalCoverFullness

General constructions and comparisons for this native mathematical family.
-/

@[expose] public section

noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open _root_.AlgebraicGeometry.Scheme.FiniteEtale (baseChange)

namespace AlgebraicGeometry.Scheme.FiniteEtale.PurelyInseparable.Global

universe u
variable {X T : Scheme.{u}} (f : T ⟶ X) [Surjective f] [Flat f] [QuasiCompact f]
  (𝒰 : X.OpenCover) [Category.{u} 𝒰.I₀] [𝒰.LocallyDirected]
  [∀ i, (baseChange (pullback.fst (𝒰.f i) f)).Full]

include 𝒰 in
/-- Fullness of actual cover base change is local on the original base. -/
theorem baseChange_full_of_local_full : (baseChange f).Full where
  map_surjective {Y Z} q := by
    let G := Over.pullback f
    let 𝒱 := 𝒰.pullback₁ Y.obj.hom
    let D := overCoverDiagram Y.obj 𝒱
    let c := overCoverCocone Y.obj 𝒱
    let hc := overCoverCoconeIsColimit Y.obj 𝒱
    have h (i : 𝒰.I₀) : ∃ g : D.obj i ⟶ Z.obj,
        G.map g = G.map (c.ι.app i) ≫ q.hom := by
      let A := (baseChange (𝒰.f i)).obj Y
      let e : D.obj i ≅ (Over.map (𝒰.f i)).obj A.obj :=
        Over.isoMk (Iso.refl _) (by
          change (𝟙 (pullback Y.obj.hom (𝒰.f i))) ≫
              (pullback.snd Y.obj.hom (𝒰.f i) ≫ 𝒰.f i) =
            pullback.fst Y.obj.hom (𝒰.f i) ≫ Y.obj.hom
          rw [Category.id_comp]
          exact pullback.condition.symm)
      let eZ : (Over.map (𝟙 X)).obj Z.obj ≅ Z.obj := (Over.mapId X).app Z.obj
      let q' := (G.mapIso e).inv ≫ (G.map (c.ι.app i) ≫ q.hom) ≫ (G.mapIso eZ).inv
      obtain ⟨g, hg⟩ := local_overMap_surjective f (𝒰.f i) (𝟙 X) (𝒰.f i)
        (Category.comp_id _) A Z q'
      refine ⟨e.hom ≫ g ≫ eZ.hom, ?_⟩
      rw [Functor.map_comp, Functor.map_comp, hg]
      simp only [q', Functor.mapIso_inv, Functor.const_obj_obj, Category.assoc,
        ← Functor.map_comp, Iso.inv_hom_id, CategoryTheory.Functor.map_id,
        Iso.map_hom_inv_id_assoc]
      change G.map (c.ι.app i) ≫ (q.hom ≫ 𝟙 (G.obj Z.obj)) =
        G.map (c.ι.app i) ≫ q.hom
      exact congrArg (fun k : G.obj Y.obj ⟶ G.obj Z.obj ↦ G.map (c.ι.app i) ≫ k)
        (Category.comp_id q.hom)
    choose g hg using h
    let s : Cocone D :=
      { pt := Z.obj
        ι :=
          { app := g
            naturality i j d := by
              apply G.map_injective
              change G.map (D.map d ≫ g j) = G.map (g i ≫ 𝟙 Z.obj)
              rw [Category.comp_id, Functor.map_comp, hg j, hg i,
                ← Category.assoc, ← Functor.map_comp, c.w d] } }
    let g₀ : Y.obj ⟶ Z.obj := hc.desc s
    refine ⟨ObjectProperty.homMk g₀, ?_⟩
    apply ObjectProperty.hom_ext
    apply (pullbackOverCoverCoconeIsColimit Y.obj 𝒱 f).hom_ext
    intro i
    change G.map (c.ι.app i) ≫ G.map g₀ = G.map (c.ι.app i) ≫ q.hom
    rw [← Functor.map_comp, hc.fac s i]
    exact hg i

end AlgebraicGeometry.Scheme.FiniteEtale.PurelyInseparable.Global

/- Migration source: the R5Lab/Aglib mirror; exact module in the migration record.
R5 revision c82abf3a72ce1e1cedf4a4f1fe08bea994ad4df5.
SHA256 8073b9238e35d5f30a655de0a32c57169364b78bdeb408a0e97cb0577acc4152.
Definitions, hypotheses and universes are retained modulo native names. -/
