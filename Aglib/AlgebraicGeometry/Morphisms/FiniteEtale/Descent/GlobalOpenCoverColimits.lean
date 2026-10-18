/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.Descent.GlobalLocalCoverMaps
public import Mathlib.AlgebraicGeometry.Cover.Directed

/-!
# GlobalOpenCoverColimits

General constructions and comparisons for this native mathematical family.
-/

@[expose] public section

noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.FiniteEtale.PurelyInseparable.Global

universe u
variable {X T : Scheme.{u}} (Z : Over X) (𝒱 : Z.left.OpenCover)
  [Category.{u} 𝒱.I₀] [𝒱.LocallyDirected]

/-- The locally directed open-cover diagram of `Z.left` , regarded as a diagram in `Over X` . -/
def overCoverDiagram : 𝒱.I₀ ⥤ Over X :=
  Over.lift 𝒱.functorOfLocallyDirected
    (𝒱.functorOfLocallyDirectedHomBase ≫ (Functor.const 𝒱.I₀).map Z.hom)

/-- The cocone from the open-cover diagram to `Z` , with legs given by the open-chart maps. -/
def overCoverCocone : Cocone (overCoverDiagram Z 𝒱) where
  pt := Z
  ι :=
    { app i := Over.homMk (𝒱.f i) rfl
      naturality _ _ d := Over.OverMorphism.ext (𝒱.trans_map d) }

/-- The colimit structure on the open-cover cocone, with descent given by gluing over `X` . -/
def overCoverCoconeIsColimit : IsColimit (overCoverCocone Z 𝒱) where
  desc s := 𝒱.glueMorphismsOverOfLocallyDirected (fun i ↦ (s.ι.app i).left)
    (fun {_ _} d ↦ congrArg (fun k ↦ k.left) (s.w d)) (fun i ↦ Over.w (s.ι.app i))
  fac s i := Over.OverMorphism.ext (by
    exact Scheme.OpenCover.map_glueMorphismsOverOfLocallyDirected_left 𝒱 _ _ _ i)
  uniq s m hm := by
    apply Over.OverMorphism.ext
    apply 𝒱.hom_ext
    intro i
    rw [Scheme.OpenCover.map_glueMorphismsOverOfLocallyDirected_left]
    exact congrArg (fun k ↦ k.left) (hm i)

variable (f : T ⟶ X)

/-- The open cover of the base change of `Z` obtained by pulling back `𝒱` along the first
projection. -/
abbrev pulledOpenCover : ((Over.pullback f).obj Z).left.OpenCover :=
  𝒱.pullback₁ (pullback.fst Z.hom f)

/-- The isomorphism from the base change of `U → X` to the corresponding chart over the base
change of `Z` . -/
def pullbackOpenComponentIso {U : Scheme.{u}} (i : U ⟶ Z.left) :
    pullback (i ≫ Z.hom) f ≅ pullback (pullback.fst Z.hom f) i :=
  (pullbackRightPullbackFstIso Z.hom f i).symm ≪≫ pullbackSymmetry i (pullback.fst Z.hom f)

theorem pullbackOpenComponentIso_hom_base {U : Scheme.{u}} (i : U ⟶ Z.left) :
    (pullbackOpenComponentIso Z f i).hom ≫ pullback.fst (pullback.fst Z.hom f) i =
      ((Over.pullback f).map (Over.homMk i rfl : Over.mk (i ≫ Z.hom) ⟶ Z)).left := by
  simp only [pullbackOpenComponentIso, Iso.trans_hom, Category.assoc,
    pullbackSymmetry_hom_comp_fst]
  exact (localPullbackPushforwardIso_structure f Z.hom (Over.mk i)).symm

/-- The isomorphism over `T` between a base-changed open chart and the pulled-back-cover
chart. -/
def pullbackOpenComponentOverIso (i : 𝒱.I₀) :
    ((overCoverDiagram Z 𝒱) ⋙ Over.pullback f).obj i ≅
      (overCoverDiagram ((Over.pullback f).obj Z) (pulledOpenCover Z 𝒱 f)).obj i :=
  Over.isoMk (pullbackOpenComponentIso Z f (𝒱.f i)) (by
    change (pullbackOpenComponentIso Z f (𝒱.f i)).hom ≫
        (pullback.fst (pullback.fst Z.hom f) (𝒱.f i) ≫ pullback.snd Z.hom f) = _
    rw [← Category.assoc, pullbackOpenComponentIso_hom_base]
    exact Over.w ((Over.pullback f).map ((overCoverCocone Z 𝒱).ι.app i)))

theorem pullbackOpenComponentOverIso_hom_ι (i : 𝒱.I₀) :
    (pullbackOpenComponentOverIso Z 𝒱 f i).hom ≫
      (overCoverCocone ((Over.pullback f).obj Z) (pulledOpenCover Z 𝒱 f)).ι.app i =
        (Over.pullback f).map ((overCoverCocone Z 𝒱).ι.app i) := by
  apply Over.OverMorphism.ext
  exact pullbackOpenComponentIso_hom_base Z f (𝒱.f i)

/-- The natural isomorphism between the base-changed open-cover diagram and the
pulled-back-cover diagram. -/
def pullbackOpenCoverDiagramIso :
    overCoverDiagram Z 𝒱 ⋙ Over.pullback f ≅
      overCoverDiagram ((Over.pullback f).obj Z) (pulledOpenCover Z 𝒱 f) :=
  NatIso.ofComponents (pullbackOpenComponentOverIso Z 𝒱 f) (by
    intro i j d
    let c := overCoverCocone ((Over.pullback f).obj Z) (pulledOpenCover Z 𝒱 f)
    have : Mono (c.ι.app j).left :=
      inferInstanceAs (Mono ((pulledOpenCover Z 𝒱 f).f j))
    let : Mono (c.ι.app j) := Over.mono_of_mono_left _
    apply (cancel_mono (c.ι.app j)).mp
    change ((Over.pullback f).map ((overCoverDiagram Z 𝒱).map d) ≫
        (pullbackOpenComponentOverIso Z 𝒱 f j).hom) ≫ c.ι.app j =
      ((pullbackOpenComponentOverIso Z 𝒱 f i).hom ≫
        (overCoverDiagram ((Over.pullback f).obj Z) (pulledOpenCover Z 𝒱 f)).map d) ≫ c.ι.app j
    rw [Category.assoc, pullbackOpenComponentOverIso_hom_ι, ← Functor.map_comp,
      (overCoverCocone Z 𝒱).w d, Category.assoc, c.w d]
    exact (pullbackOpenComponentOverIso_hom_ι Z 𝒱 f i).symm)

/-- Arbitrary scheme base change preserves an actual locally directed open
cover colimit in the over category. -/
def pullbackOverCoverCoconeIsColimit :
    IsColimit ((Over.pullback f).mapCocone (overCoverCocone Z 𝒱)) := by
  let e := pullbackOpenCoverDiagramIso Z 𝒱 f
  let c := overCoverCocone ((Over.pullback f).obj Z) (pulledOpenCover Z 𝒱 f)
  have hc := (IsColimit.precomposeHomEquiv e c).symm
    (overCoverCoconeIsColimit ((Over.pullback f).obj Z) (pulledOpenCover Z 𝒱 f))
  apply IsColimit.ofIsoColimit hc
  refine Cocone.ext (Iso.refl _) ?_
  intro i
  change ((pullbackOpenComponentOverIso Z 𝒱 f i).hom ≫
    (overCoverCocone ((Over.pullback f).obj Z) (pulledOpenCover Z 𝒱 f)).ι.app i) ≫ 𝟙 _ =
      (Over.pullback f).map ((overCoverCocone Z 𝒱).ι.app i)
  rw [Category.comp_id]
  exact pullbackOpenComponentOverIso_hom_ι Z 𝒱 f i

theorem overPullback_preserves_overCoverDiagram :
    PreservesColimit (overCoverDiagram Z 𝒱) (Over.pullback f) :=
  preservesColimit_of_preserves_colimit_cocone (overCoverCoconeIsColimit Z 𝒱)
    (pullbackOverCoverCoconeIsColimit Z 𝒱 f)

end AlgebraicGeometry.Scheme.FiniteEtale.PurelyInseparable.Global

/- Migration source: the R5Lab/Aglib mirror; exact module in the migration record.
R5 revision c82abf3a72ce1e1cedf4a4f1fe08bea994ad4df5.
SHA256 6327c8a6bf5502837b628e70a949fbca77ff20514ec5ebcd011721689b15e1a1.
Definitions, hypotheses and universes are retained modulo native names. -/
