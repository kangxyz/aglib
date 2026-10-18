/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.Descent.GlobalRelativeDiagram
public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.Descent.GlobalOpenCoverColimits
public import Mathlib.CategoryTheory.Limits.Over

/-!
# GlobalGluedCover

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
  [Small.{u} 𝒰.I₀] [Quiver.IsThin 𝒰.I₀]
  [∀ i, (baseChange (pullback.fst (𝒰.f i) f)).IsEquivalence]
  (Y : Scheme.FiniteEtale T)

/-- The cocone from the descended local diagram to the global cover candidate, using gluing
inclusions. -/
def descendedCocone : Cocone (descendedLocalDiagram f 𝒰 Y) where
  pt := (globalCoverCandidate f 𝒰 Y).obj
  ι :=
    { app i := Over.homMk (colimit.ι (relativeDescentData f 𝒰 Y).functor i)
        ((relativeDescentData f 𝒰 Y).ι_toBase i)
      naturality i j d := by
        apply Over.OverMorphism.ext
        change (relativeDescentData f 𝒰 Y).functor.map d ≫
            colimit.ι (relativeDescentData f 𝒰 Y).functor j =
          colimit.ι (relativeDescentData f 𝒰 Y).functor i ≫ 𝟙 _
        rw [Category.comp_id]
        exact colimit.w (relativeDescentData f 𝒰 Y).functor d }

/-- The colimit structure on the descended cocone, reflected from the underlying scheme colimit. -/
def descendedCoconeIsColimit : IsColimit (descendedCocone f 𝒰 Y) := by
  apply isColimitOfReflects (Over.forget X)
  change IsColimit (colimit.cocone (relativeDescentData f 𝒰 Y).functor)
  exact colimit.isColimit _

/-- The comparison from the descended local diagram to the open-cover diagram of the global
candidate. -/
def descendedDiagramCoverIso :
    descendedLocalDiagram f 𝒰 Y ≅
      overCoverDiagram (globalCoverCandidate f 𝒰 Y).obj (relativeDescentData f 𝒰 Y).cover :=
  NatIso.ofComponents (fun i ↦ Over.isoMk (Iso.refl _) (by
    change (𝟙 ((descendedLocalDiagram f 𝒰 Y).obj i).left) ≫
        (colimit.ι (relativeDescentData f 𝒰 Y).functor i ≫
          (relativeDescentData f 𝒰 Y).toBase) =
      (localModel f 𝒰 Y i).obj.hom ≫ 𝒰.f i
    rw [Category.id_comp]
    exact (relativeDescentData f 𝒰 Y).ι_toBase i)) (by
      intro i j d
      apply Over.OverMorphism.ext
      change ((descendedLocalDiagram f 𝒰 Y).map d).left ≫ 𝟙 _ =
        𝟙 _ ≫ ((descendedLocalDiagram f 𝒰 Y).map d).left
      simp)

/-- The colimit structure on the descended cocone after pullback along `f`. -/
def pulledDescendedCoconeIsColimit :
    IsColimit ((Over.pullback f).mapCocone (descendedCocone f 𝒰 Y)) := by
  let : PreservesColimit
      (overCoverDiagram (globalCoverCandidate f 𝒰 Y).obj (relativeDescentData f 𝒰 Y).cover)
      (Over.pullback f) :=
    overPullback_preserves_overCoverDiagram (globalCoverCandidate f 𝒰 Y).obj
      (relativeDescentData f 𝒰 Y).cover f
  let : PreservesColimit (descendedLocalDiagram f 𝒰 Y) (Over.pullback f) :=
    preservesColimit_of_iso_diagram (Over.pullback f) (descendedDiagramCoverIso f 𝒰 Y).symm
  exact isColimitOfPreserves (Over.pullback f) (descendedCoconeIsColimit f 𝒰 Y)

/-- The open cover of `Y` obtained by pulling `𝒰` back along `Y.obj.hom ≫ f`. -/
abbrev targetOpenCover : Y.obj.left.OpenCover := 𝒰.pullback₁ (Y.obj.hom ≫ f)

/-- The cocone from the geometric local diagram to `Y`, with legs given by pullback projections. -/
def geometricLocalCocone : Cocone (geometricLocalDiagram f 𝒰 Y) where
  pt := Y.obj
  ι :=
    { app i := Over.homMk (pullback.snd (pullback.snd (𝒰.f i) f) Y.obj.hom) rfl
      naturality i j d := by
        apply Over.OverMorphism.ext
        change (((Over.pullback Y.obj.hom).map
          ((Over.pullback f).map ((chartDiagram 𝒰).map d))).left) ≫
            pullback.snd (pullback.snd (𝒰.f j) f) Y.obj.hom =
          pullback.snd (pullback.snd (𝒰.f i) f) Y.obj.hom ≫ 𝟙 _
        rw [Category.comp_id]
        exact Over.w ((Over.pullback Y.obj.hom).map
          ((Over.pullback f).map ((chartDiagram 𝒰).map d))) }

/-- The component comparison between the iterated pullback and the corresponding chart of `Y`. -/
def geometricTargetComponentIso (i : 𝒰.I₀) :
    (geometricLocalDiagram f 𝒰 Y).obj i ≅
      (overCoverDiagram Y.obj (targetOpenCover f 𝒰 Y)).obj i :=
  Over.isoMk
    (pullbackLeftPullbackSndIso (𝒰.f i) f Y.obj.hom ≪≫
      pullbackSymmetry (𝒰.f i) (Y.obj.hom ≫ f)) (by
      change (_ ≫ _) ≫ (pullback.fst (Y.obj.hom ≫ f) (𝒰.f i) ≫ Y.obj.hom) =
        pullback.snd (pullback.snd (𝒰.f i) f) Y.obj.hom ≫ Y.obj.hom
      simp only [Category.assoc, pullbackSymmetry_hom_comp_fst_assoc,
        pullbackLeftPullbackSndIso_hom_snd_assoc])

set_option linter.unusedSectionVars false in
-- Preserve the original supplied hypotheses and binder order.
-- Keep the original supplied class/data inputs and binder order of this interface.
@[nolint unusedArguments]
theorem geometricTargetComponentIso_hom_ι (i : 𝒰.I₀) :
    (geometricTargetComponentIso f 𝒰 Y i).hom ≫
      (overCoverCocone Y.obj (targetOpenCover f 𝒰 Y)).ι.app i =
        (geometricLocalCocone f 𝒰 Y).ι.app i := by
  apply Over.OverMorphism.ext
  change (_ ≫ _) ≫ pullback.fst (Y.obj.hom ≫ f) (𝒰.f i) =
    pullback.snd (pullback.snd (𝒰.f i) f) Y.obj.hom
  simp only [Category.assoc, pullbackSymmetry_hom_comp_fst, pullbackLeftPullbackSndIso_hom_snd]

/-- The natural comparison from the geometric local diagram to the open-cover diagram of `Y`. -/
def geometricTargetDiagramIso :
    geometricLocalDiagram f 𝒰 Y ≅ overCoverDiagram Y.obj (targetOpenCover f 𝒰 Y) :=
  NatIso.ofComponents (geometricTargetComponentIso f 𝒰 Y) (by
    intro i j d
    let c := overCoverCocone Y.obj (targetOpenCover f 𝒰 Y)
    have : Mono (c.ι.app j).left := inferInstanceAs (Mono ((targetOpenCover f 𝒰 Y).f j))
    let : Mono (c.ι.app j) := Over.mono_of_mono_left _
    apply (cancel_mono (c.ι.app j)).mp
    rw [Category.assoc, geometricTargetComponentIso_hom_ι,
      (geometricLocalCocone f 𝒰 Y).w d, Category.assoc, c.w d]
    exact (geometricTargetComponentIso_hom_ι f 𝒰 Y i).symm)

/-- The colimit structure on the geometric local cocone, transported from the open-cover
colimit. -/
def geometricLocalCoconeIsColimit : IsColimit (geometricLocalCocone f 𝒰 Y) := by
  let e := geometricTargetDiagramIso f 𝒰 Y
  let c := overCoverCocone Y.obj (targetOpenCover f 𝒰 Y)
  have hc := (IsColimit.precomposeHomEquiv e c).symm
    (overCoverCoconeIsColimit Y.obj (targetOpenCover f 𝒰 Y))
  apply IsColimit.ofIsoColimit hc
  refine Cocone.ext (Iso.refl _) ?_
  intro i
  change ((geometricTargetComponentIso f 𝒰 Y i).hom ≫ c.ι.app i) ≫ 𝟙 _ =
    (geometricLocalCocone f 𝒰 Y).ι.app i
  rw [Category.comp_id]
  exact geometricTargetComponentIso_hom_ι f 𝒰 Y i

/-- The constructed glued cover pulls back to the original cover, with an
actual isomorphism in the original finite-étale cover category. -/
def globalBaseChangeIso : (baseChange f).obj (globalCoverCandidate f 𝒰 Y) ≅ Y :=
  ObjectProperty.isoMk _
    ((pulledDescendedCoconeIsColimit f 𝒰 Y).coconePointsIsoOfNatIso
      (geometricLocalCoconeIsColimit f 𝒰 Y)
      (CategoryTheory.Functor.DiagramLift.diagramLiftIso (Over.pullback f) (geometricLocalDiagram
        f 𝒰 Y)
        (localModelOver f 𝒰 Y) (localModelGeometricIso f 𝒰 Y)
        (localModel_arrow_lifts f 𝒰 Y)))

include 𝒰 in
theorem baseChange_essSurj_of_local_equivalence : (baseChange f).EssSurj where
  mem_essImage Y := ⟨globalCoverCandidate f 𝒰 Y, ⟨globalBaseChangeIso f 𝒰 Y⟩⟩

end AlgebraicGeometry.Scheme.FiniteEtale.PurelyInseparable.Global

/- Migration source: the R5Lab/Aglib mirror; exact module in the migration record.
R5 revision c82abf3a72ce1e1cedf4a4f1fe08bea994ad4df5.
SHA256 e11619f15b34bb5873e8cee2cc41222aa9c28c6dd638b1ade0b9176954d4f307.
Definitions, hypotheses and universes are retained modulo native names. -/
