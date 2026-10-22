/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.Descent.LimitCartesian
public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.Basic

/-!
# Eventual equifiberedness of finite-etale model diagrams

The comparison targets are the actual scheme pullbacks of finite-etale
structural maps. This supplies their finite presentation without any
separatedness hypothesis on the ambient schemes or on the chart system.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.FiniteEtale.LimitDescent

universe u v

section Comparison

variable {S : Scheme.{u}} {A B E Z : Over S}
  (a : A ⟶ B) (b : A ⟶ E) (f : B ⟶ Z) (g : E ⟶ Z)
  (w : a ≫ f = b ≫ g)

/-- The native scheme pullback of the two lower-right arrows, viewed over the base. -/
def comparisonTarget : Over S :=
  Over.mk (pullback.snd f.left g.left ≫ E.hom)

/-- First projection of the cartesian comparison target. -/
def comparisonFirst : comparisonTarget f g ⟶ B :=
  Over.homMk (pullback.fst f.left g.left) (by
    change pullback.fst f.left g.left ≫ B.hom = pullback.snd f.left g.left ≫ E.hom
    rw [← Over.w f, pullback.condition_assoc, Over.w g])

/-- Second projection of the cartesian comparison target. -/
def comparisonSecond : comparisonTarget f g ⟶ E :=
  Over.homMk (pullback.snd f.left g.left) rfl

/-- The actual comparison target is a pullback also in the over category. -/
theorem comparison_isPullback :
    IsPullback (comparisonFirst f g) (comparisonSecond f g) f g := by
  apply IsPullback.of_map (Over.forget S)
  · apply Over.OverMorphism.ext
    exact pullback.condition
  · exact IsPullback.of_hasPullback f.left g.left

/-- The cartesian comparison map, not the original transition arrow. -/
def comparisonMap : A ⟶ comparisonTarget f g :=
  Over.homMk (pullback.lift a.left b.left (congrArg (fun h ↦ h.left) w)) (by
    change pullback.lift a.left b.left _ ≫ (pullback.snd f.left g.left ≫ E.hom) = A.hom
    rw [← Category.assoc, pullback.lift_snd, Over.w b])

@[reassoc] theorem comparisonMap_first :
    comparisonMap a b f g w ≫ comparisonFirst f g = a := by
  apply Over.OverMorphism.ext
  exact pullback.lift_fst _ _ _

@[reassoc] theorem comparisonMap_second :
    comparisonMap a b f g w ≫ comparisonSecond f g = b := by
  apply Over.OverMorphism.ext
  exact pullback.lift_snd _ _ _

end Comparison

/-- A natural transformation between finite diagrams with finite-etale components
becomes equifibered at a common stage when it is equifibered at the limit. -/
theorem exists_equifibered_stage
    {I : Type u} [Category.{u} I] [IsCofiltered I]
    (D : I ⥤ Scheme.{u})
    [∀ {i j} (f : i ⟶ j), IsAffineHom (D.map f)]
    [∀ i, CompactSpace (D.obj i)] [∀ i, QuasiSeparatedSpace (D.obj i)]
    (c : Cone D) (hc : IsLimit c) (i : I)
    {J : Type v} [SmallCategory J] [Finite J] [∀ j k : J, Finite (j ⟶ k)]
    (F G : J ⥤ Over (D.obj i)) (n : F ⟶ G)
    [∀ j, IsFinite (n.app j).left] [∀ j, Etale (n.app j).left]
    [∀ j, LocallyOfFinitePresentation (G.obj j).hom]
    [∀ j, QuasiCompact (G.obj j).hom] [∀ j, QuasiSeparated (G.obj j).hom]
    (H : (Functor.whiskerRight n (Over.pullback (c.π.app i))).Equifibered) :
    ∃ k : Over i, (Functor.whiskerRight n (Over.pullback (D.map k.hom))).Equifibered := by
  let Arrows := Σ j : J, Σ k : J, (j ⟶ k)
  let A (d : Arrows) := F.obj d.1
  let B (d : Arrows) := F.obj d.2.1
  let E (d : Arrows) := G.obj d.1
  let Z (d : Arrows) := G.obj d.2.1
  let a (d : Arrows) := F.map d.2.2
  let b (d : Arrows) := n.app d.1
  let f (d : Arrows) := n.app d.2.1
  let g (d : Arrows) := G.map d.2.2
  let P (d : Arrows) := comparisonTarget (f d) (g d)
  have (d : Arrows) : LocallyOfFinitePresentation (A d).hom := by
    rw [← Over.w (b d)]
    infer_instance
  have (d : Arrows) : QuasiCompact (A d).hom := by
    rw [← Over.w (b d)]
    infer_instance
  have (d : Arrows) : LocallyOfFinitePresentation (P d).hom := by
    change LocallyOfFinitePresentation (pullback.snd (f d).left (g d).left ≫ (E d).hom)
    infer_instance
  have (d : Arrows) : QuasiCompact (P d).hom := by
    change QuasiCompact (pullback.snd (f d).left (g d).left ≫ (E d).hom)
    infer_instance
  have (d : Arrows) : QuasiSeparated (P d).hom := by
    change QuasiSeparated (pullback.snd (f d).left (g d).left ≫ (E d).hom)
    infer_instance
  obtain ⟨k, hk⟩ := exists_common_cartesian_stage D c hc i A P B E Z a b
    (fun d ↦ comparisonFirst (f d) (g d)) (fun d ↦ comparisonSecond (f d) (g d)) f g
    (fun d ↦ comparison_isPullback (f d) (g d))
    (fun d ↦ comparisonMap (a d) (b d) (f d) (g d) (n.naturality d.2.2))
    (fun d ↦ comparisonMap_first _ _ _ _ _) (fun d ↦ comparisonMap_second _ _ _ _ _)
    (fun d ↦ H d.2.2)
  exact ⟨k, fun {_ _} d ↦ hk ⟨_, _, d⟩⟩

end AlgebraicGeometry.Scheme.FiniteEtale.LimitDescent
