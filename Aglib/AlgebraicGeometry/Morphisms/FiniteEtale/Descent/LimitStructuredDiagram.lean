/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Descent.FinitePresentation.Schemes
public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.Descent.FiniteFieldModelTransfer

/-!
# Structured finite diagrams at a common limit stage

Actual finite-etale chart models descend with their transition arrows, the
functor laws and structural naturality. These finitely many equations are
imposed at a later stage; no faithful-flatness of the limit projections is used.
The cover is the literal iterated pullback cover, avoiding unnecessary choices
of identifications between successive pullbacks.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme.FiniteEtale.PurelyInseparable.Global
open AlgebraicGeometry.Scheme.FiniteEtale.FieldCoverDescent

namespace AlgebraicGeometry.Scheme.FiniteEtale.LimitDescent

universe u

private theorem exists_structure_equations
    {I : Type u} [Category.{u} I] [IsCofiltered I]
    (D : I ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
    [∀ {i j} (f : i ⟶ j), IsAffineHom (D.map f)]
    [∀ i, CompactSpace (D.obj i)] (i : I)
    {J : Type u} [Category.{u} J] [Finite J] [∀ l r : J, Finite (l ⟶ r)]
    (B : J → Over (D.obj i)) [∀ l, QuasiCompact (B l).hom]
    (C : J ⥤ Over (D.obj i)) [∀ l, LocallyOfFiniteType (C.obj l).hom]
    (m : ∀ l, B l ⟶ C.obj l)
    (G : J ⥤ Over c.pt) (n : G ⟶ C ⋙ Over.pullback (c.π.app i))
    (β : ∀ l, (Over.pullback (c.π.app i)).obj (B l) ≅ G.obj l)
    (hm : ∀ l, (Over.pullback (c.π.app i)).map (m l) = (β l).hom ≫ n.app l)
    (g : ∀ {l r : J}, (l ⟶ r) → (B l ⟶ B r))
    (hg : ∀ {l r : J} (d : l ⟶ r),
      (Over.pullback (c.π.app i)).map (g d) ≫ (β r).hom = (β l).hom ≫ G.map d)
    [∀ l, LocallyOfFiniteType (B l).hom] :
    ∃ k : Over i,
      (∀ l, (Over.pullback (D.map k.hom)).map (g (𝟙 l)) = 𝟙 _) ∧
      (∀ {l r s : J} (d : l ⟶ r) (e : r ⟶ s),
        (Over.pullback (D.map k.hom)).map (g (d ≫ e)) =
          (Over.pullback (D.map k.hom)).map (g d) ≫
            (Over.pullback (D.map k.hom)).map (g e)) ∧
      (∀ {l r : J} (d : l ⟶ r),
        (Over.pullback (D.map k.hom)).map (g d ≫ m r) =
          (Over.pullback (D.map k.hom)).map (m l ≫ C.map d)) := by
  let Arrows := Σ (l r : J), l ⟶ r
  let Compositions := Σ (l r s : J), (l ⟶ r) × (r ⟶ s)
  let Relations := (J ⊕ Compositions) ⊕ Arrows
  let source : Relations → J :=
    Sum.elim (Sum.elim id (fun d ↦ d.1)) (fun d ↦ d.1)
  let target : Relations → Over (D.obj i) :=
    Sum.elim (Sum.elim B (fun d ↦ B d.2.2.1)) (fun d ↦ C.obj d.2.1)
  let lhs : ∀ r, B (source r) ⟶ target r := fun r ↦ by
    rcases r with (l | ⟨l, r, s, d, e⟩) | ⟨l, r, d⟩
    · exact g (𝟙 l)
    · exact g (d ≫ e)
    · exact g d ≫ m r
  let rhs : ∀ r, B (source r) ⟶ target r := fun r ↦ by
    rcases r with (l | ⟨l, r, s, d, e⟩) | ⟨l, r, d⟩
    · exact 𝟙 (B l)
    · exact g d ≫ g e
    · exact m l ≫ C.map d
  have heq (r : Relations) :
      (Over.pullback (c.π.app i)).map (lhs r) =
        (Over.pullback (c.π.app i)).map (rhs r) := by
    rcases r with (l | ⟨l, r, s, d, e⟩) | ⟨l, r, d⟩
    · apply (cancel_mono (β l).hom).mp
      change (Over.pullback (c.π.app i)).map (g (𝟙 l)) ≫ (β l).hom =
        (Over.pullback (c.π.app i)).map (𝟙 (B l)) ≫ (β l).hom
      rw [hg]
      simp
    · apply (cancel_mono (β s).hom).mp
      change (Over.pullback (c.π.app i)).map (g (d ≫ e)) ≫ (β s).hom =
        (Over.pullback (c.π.app i)).map (g d ≫ g e) ≫ (β s).hom
      rw [hg]
      simp only [Functor.map_comp, Category.assoc]
      rw [hg]
      simpa only [Category.assoc] using (congrArg (· ≫ G.map e) (hg d)).symm
    · change (Over.pullback (c.π.app i)).map (g d ≫ m r) =
        (Over.pullback (c.π.app i)).map (m l ≫ C.map d)
      simp only [Functor.map_comp, hm, ← Category.assoc]
      rw [hg, Category.assoc, n.naturality d]
      simp only [Functor.comp_map, Category.assoc]
  have (r : Relations) : LocallyOfFiniteType (target r).hom := by
    rcases r with (l | ⟨l, r, s, d, e⟩) | ⟨l, r, d⟩ <;>
      dsimp [target] <;> infer_instance
  obtain ⟨k, hk⟩ := Scheme.exists_common_stage_baseChange_map_eq_of_isLimit D c hc i
    (fun r ↦ (B (source r)).hom) (fun r ↦ (target r).hom) lhs rhs heq
  refine ⟨k, ?_, ?_, ?_⟩
  · intro l
    have H := hk (.inl (.inl l))
    change (Over.pullback (D.map k.hom)).map (g (𝟙 l)) =
      (Over.pullback (D.map k.hom)).map (𝟙 (B l)) at H
    exact H.trans ((Over.pullback (D.map k.hom)).map_id _)
  · intro l r s d e
    have H := hk (.inl (.inr ⟨l, r, s, d, e⟩))
    change (Over.pullback (D.map k.hom)).map (g (d ≫ e)) =
      (Over.pullback (D.map k.hom)).map (g d ≫ g e) at H
    exact H.trans ((Over.pullback (D.map k.hom)).map_comp _ _)
  · intro l r d
    exact hk (.inr ⟨l, r, d⟩)

private theorem exists_rebased_structure
    {S S' T : Scheme.{u}} (𝒲 : S.OpenCover.{u})
    [Category.{u} 𝒲.I₀] [𝒲.LocallyDirected]
    (a : S' ⟶ S) (b : T ⟶ S') (f : T ⟶ S) (h : b ≫ a = f)
    (Y : FiniteEtale T) (B : 𝒲.I₀ → Over S)
    (m : ∀ l, B l ⟶ (chartDiagram 𝒲).obj l)
    [∀ l, IsFinite (m l).left] [∀ l, Etale (m l).left]
    (β : ∀ l, (Over.pullback f).obj (B l) ≅ (geometricLocalDiagram f 𝒲 Y).obj l)
    (hm : ∀ l, (Over.pullback f).map (m l) =
      (β l).hom ≫ (geometricLocalStructure f 𝒲 Y).app l)
    (g : ∀ {l r : 𝒲.I₀}, (l ⟶ r) → (B l ⟶ B r))
    (hg : ∀ {l r : 𝒲.I₀} (d : l ⟶ r), (Over.pullback f).map (g d) =
      (β l).hom ≫ (geometricLocalDiagram f 𝒲 Y).map d ≫ (β r).inv)
    (hid : ∀ l, (Over.pullback a).map (g (𝟙 l)) = 𝟙 _)
    (hcomp : ∀ {l r s : 𝒲.I₀} (d : l ⟶ r) (e : r ⟶ s),
      (Over.pullback a).map (g (d ≫ e)) =
        (Over.pullback a).map (g d) ≫ (Over.pullback a).map (g e))
    (hnat : ∀ {l r : 𝒲.I₀} (d : l ⟶ r),
      (Over.pullback a).map (g d ≫ m r) =
        (Over.pullback a).map (m l ≫ (chartDiagram 𝒲).map d)) :
    ∃ (F : (𝒲.pullback₁ a).I₀ ⥤ Over S') (n : F ⟶ chartDiagram (𝒲.pullback₁ a)),
      (∀ l, IsFinite (n.app l).left) ∧ (∀ l, Etale (n.app l).left) ∧
      ∃ e : F ⋙ Over.pullback b ≅ geometricLocalDiagram b (𝒲.pullback₁ a) Y,
        ∀ l, (Over.pullback b).map (n.app l) =
          e.hom.app l ≫ (geometricLocalStructure b (𝒲.pullback₁ a) Y).app l := by
  let 𝒱 := 𝒲.pullback₁ a
  let F : 𝒱.I₀ ⥤ Over S' :=
    { obj := fun l ↦ (Over.pullback a).obj (B l)
      map := fun d ↦ (Over.pullback a).map (g d)
      map_id := hid
      map_comp := hcomp }
  let n : F ⟶ chartDiagram 𝒱 :=
    { app := transferredStructure 𝒲 a B m
      naturality := fun l r d ↦ by
        have H := hnat d
        change (Over.pullback a).map (g d) ≫
            ((Over.pullback a).map (m r) ≫ (chartPullbackIso 𝒲 a).inv.app r) =
          ((Over.pullback a).map (m l) ≫ (chartPullbackIso 𝒲 a).inv.app l) ≫
            (chartDiagram 𝒱).map d
        rw [← Category.assoc, ← Functor.map_comp, H, Functor.map_comp, Category.assoc]
        exact congrArg ((Over.pullback a).map (m l) ≫ ·)
          ((chartPullbackIso 𝒲 a).inv.naturality d) }
  let β' := transferredIso 𝒲 a b f h Y B β
  have hg' {l r : 𝒱.I₀} (d : l ⟶ r) :
      (Over.pullback b).map (F.map d) =
        (β' l).hom ≫ (geometricLocalDiagram b 𝒱 Y).map d ≫ (β' r).inv := by
    apply transferred_arrow 𝒲 a b f h Y B β d
    change (Over.pullback b).map ((Over.pullback a).map (g d)) ≫
        (overCompIso a b f h (B r)).hom = _
    rw [overCompIso_naturality, hg]
  let e : F ⋙ Over.pullback b ≅ geometricLocalDiagram b 𝒱 Y :=
    NatIso.ofComponents β' (fun d ↦ by
      change (Over.pullback b).map (F.map d) ≫ _ = _
      rw [hg']
      simp)
  refine ⟨F, n, ?_, ?_, e, ?_⟩
  · intro l
    exact inferInstanceAs (IsFinite (transferredStructure 𝒲 a B m l).left)
  · intro l
    exact inferInstanceAs (Etale (transferredStructure 𝒲 a B m l).left)
  · exact transferredStructure_commutes 𝒲 a b f h Y B m β hm

variable {I : Type u} [Category.{u} I] [IsCofiltered I]
  (D : I ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
  [∀ {i j} (f : i ⟶ j), IsAffineHom (D.map f)]
  [∀ i, CompactSpace (D.obj i)] [∀ i, QuasiSeparatedSpace (D.obj i)]
  (i : I) (𝒰 : (D.obj i).OpenCover.{u})
  [Category.{u} 𝒰.I₀] [𝒰.LocallyDirected] [Quiver.IsThin 𝒰.I₀] [Finite 𝒰.I₀]
  [∀ j, CompactSpace (𝒰.X j)] [∀ j, QuasiSeparatedSpace (𝒰.X j)]
  (Y : Scheme.FiniteEtale c.pt) (A : 𝒰.I₀ → Over (D.obj i))
  (m : ∀ j, A j ⟶ (chartDiagram 𝒰).obj j)
  [∀ j, IsFinite (m j).left] [∀ j, Etale (m j).left]
  (α : ∀ j, (Over.pullback (c.π.app i)).obj (A j) ≅
    (geometricLocalDiagram (c.π.app i) 𝒰 Y).obj j)
  (hm : ∀ j, (Over.pullback (c.π.app i)).map (m j) =
    (α j).hom ≫ (geometricLocalStructure (c.π.app i) 𝒰 Y).app j)

include hc hm in
/-- A finite family of actual local models has a structured diagram after two
later base changes. The structural components remain finite etale and the
comparison is a natural isomorphism compatible with their original maps. -/
theorem exists_diagram_with_structure :
    ∃ (j : Over i) (k : Over j.left),
      let 𝒱 := (𝒰.pullback₁ (D.map j.hom)).pullback₁ (D.map k.hom)
      ∃ (F : 𝒱.I₀ ⥤ Over (D.obj k.left)) (n : F ⟶ chartDiagram 𝒱),
        (∀ l, IsFinite (n.app l).left) ∧ (∀ l, Etale (n.app l).left) ∧
        ∃ e : F ⋙ Over.pullback (c.π.app k.left) ≅
            geometricLocalDiagram (c.π.app k.left) 𝒱 Y,
          ∀ l, (Over.pullback (c.π.app k.left)).map (n.app l) =
            e.hom.app l ≫ (geometricLocalStructure (c.π.app k.left) 𝒱 Y).app l := by
  classical
  have (l : 𝒰.I₀) : CompactSpace ((chartDiagram 𝒰).obj l).left :=
    inferInstanceAs (CompactSpace (𝒰.X l))
  have (l : 𝒰.I₀) : QuasiSeparatedSpace ((chartDiagram 𝒰).obj l).left :=
    inferInstanceAs (QuasiSeparatedSpace (𝒰.X l))
  have (l : 𝒰.I₀) : LocallyOfFinitePresentation ((chartDiagram 𝒰).obj l).hom :=
    inferInstanceAs (LocallyOfFinitePresentation (𝒰.f l))
  have (l : 𝒰.I₀) : CompactSpace (A l).left :=
    QuasiCompact.compactSpace_of_compactSpace (m l).left
  have (l : 𝒰.I₀) : QuasiSeparatedSpace (A l).left :=
    quasiSeparatedSpace_of_quasiSeparated (m l).left
  have (l : 𝒰.I₀) : LocallyOfFinitePresentation (A l).hom := by
    rw [← Over.w (m l)]
    infer_instance
  let Arrows := Σ (l r : 𝒰.I₀), l ⟶ r
  let U : Arrows → Over (D.obj i) := fun d ↦ A d.1
  let V : Arrows → Over (D.obj i) := fun d ↦ A d.2.1
  let q (d : Arrows) : (Over.pullback (c.π.app i)).obj (U d) ⟶
      (Over.pullback (c.π.app i)).obj (V d) :=
    (α d.1).hom ≫ (geometricLocalDiagram (c.π.app i) 𝒰 Y).map d.2.2 ≫ (α d.2.1).inv
  obtain ⟨j, hj⟩ := exists_common_tail_overHom D c hc i U V q
  let a := D.map j.hom
  let b := c.π.app j.left
  let f := c.π.app i
  let h : b ≫ a = f := c.w j.hom
  let 𝒲 := 𝒰.pullback₁ a
  let B := transferredObject 𝒰 a A
  let n := transferredStructure 𝒰 a A m
  let β := transferredIso 𝒰 a b f h Y A α
  have hn : ∀ l, (Over.pullback b).map (n l) =
      (β l).hom ≫ (geometricLocalStructure b 𝒲 Y).app l :=
    transferredStructure_commutes 𝒰 a b f h Y A m α hm
  have hl : ∀ {l r : 𝒲.I₀} (d : l ⟶ r), ∃ g : B l ⟶ B r,
      (Over.pullback b).map g =
        (β l).hom ≫ (geometricLocalDiagram b 𝒲 Y).map d ≫ (β r).inv := by
    intro l r d
    obtain ⟨g, hg⟩ := hj ⟨l, r, d⟩
    exact ⟨g, transferred_arrow 𝒰 a b f h Y A α d g hg⟩
  let g {l r : 𝒲.I₀} (d : l ⟶ r) : B l ⟶ B r := (hl d).choose
  have hg {l r : 𝒲.I₀} (d : l ⟶ r) :
      (Over.pullback b).map (g d) =
        (β l).hom ≫ (geometricLocalDiagram b 𝒲 Y).map d ≫ (β r).inv :=
    (hl d).choose_spec
  have hg' {l r : 𝒲.I₀} (d : l ⟶ r) :
      (Over.pullback b).map (g d) ≫ (β r).hom =
        (β l).hom ≫ (geometricLocalDiagram b 𝒲 Y).map d := by
    rw [hg]
    simp
  have (l : 𝒲.I₀) : QuasiCompact (B l).hom := by
    dsimp [B, transferredObject, a]
    infer_instance
  have (l : 𝒲.I₀) : LocallyOfFiniteType (B l).hom := by
    dsimp [B, transferredObject, a]
    infer_instance
  have (l : 𝒲.I₀) : LocallyOfFiniteType ((chartDiagram 𝒲).obj l).hom :=
    inferInstanceAs (LocallyOfFiniteType (𝒲.f l))
  obtain ⟨k, hid, hcomp, hnat⟩ := exists_structure_equations D c hc j.left
    B (chartDiagram 𝒲) n (geometricLocalDiagram b 𝒲 Y)
    (geometricLocalStructure b 𝒲 Y) β hn g hg'
  obtain ⟨F, n', hfin, het, e, he⟩ := exists_rebased_structure 𝒲
    (D.map k.hom) (c.π.app k.left) b (c.w k.hom) Y B n β hn g hg hid hcomp hnat
  exact ⟨j, k, F, n', hfin, het, e, he⟩

end AlgebraicGeometry.Scheme.FiniteEtale.LimitDescent
