/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Aglib.AlgebraicGeometry.Descent.FinitePresentation.Gluing
public import Aglib.AlgebraicGeometry.EtaleCohomology.PullbackComposition
/-! # Actual affine chart tails over the original coefficient base -/
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme.EtaleAffineBasis
universe u
variable {I : Type u} [Category.{u} I] {X : Scheme.{u}}

/-- Actual pullbacks of a stage chart, still over the original base scheme. -/
def relativeChartTail (D : I ⥤ Over X) (i : I) (U : (D.obj i).left.Etale) :
    Over i ⥤ Over X :=
  Over.post (D ⋙ Over.forget X) ⋙ Over.pullback U.hom ⋙ Over.map (U.hom ≫ (D.obj i).hom)

/-- The original limit cone base-changed to a stage chart and retained over the base. -/
def relativeChartTailCone (D : I ⥤ Over X) (c : Cone D) (i : I)
    (U : (D.obj i).left.Etale) : Cone (relativeChartTail D i U) :=
  (Over.pullback U.hom ⋙ Over.map (U.hom ≫ (D.obj i).hom)).mapCone
    ((Over.conePost (D ⋙ Over.forget X) i).obj ((Over.forget X).mapCone c))

/-- The supplied underlying scheme limit remains the actual chart-tail limit. -/
def relativeChartTailConeIsLimit [IsCofiltered I]
    (D : I ⥤ Over X) (c : Cone D) (hc : IsLimit ((Over.forget X).mapCone c))
    (i : I) (U : (D.obj i).left.Etale) :
    IsLimit ((Over.forget X).mapCone (relativeChartTailCone D c i U)) := by
  change IsLimit (Scheme.baseChangeCone (D ⋙ Over.forget X)
    ((Over.forget X).mapCone c) i U.hom)
  exact Scheme.isLimitBaseChangeCone (D ⋙ Over.forget X)
    ((Over.forget X).mapCone c) hc i U.hom

/-- Affine transitions make the actual pullback stages of an affine chart affine. -/
instance relativeChartTail_isAffine_obj (D : I ⥤ Over X)
    [∀ {i j} (a : i ⟶ j), IsAffineHom (D.map a).left]
    (i : I) (U : (D.obj i).left.Etale) [IsAffine U.left] (j : Over i) :
    IsAffine ((relativeChartTail D i U).obj j).left := by
  change IsAffine (pullback (D.map j.hom).left U.hom)
  have : IsAffineHom (pullback.snd (D.map j.hom).left U.hom) :=
    @MorphismProperty.IsStableUnderBaseChange.of_isPullback
      Scheme.{u} _ (@IsAffineHom) isAffineHom_isStableUnderBaseChange
      U.left (D.obj j.left).left (pullback (D.map j.hom).left U.hom) (D.obj i).left
      U.hom (D.map j.hom).left
      (pullback.fst (D.map j.hom).left U.hom) (pullback.snd (D.map j.hom).left U.hom)
      (IsPullback.of_hasPullback (D.map j.hom).left U.hom)
      (inferInstance : IsAffineHom (D.map j.hom).left)
  have : IsAffine ((𝟭 Scheme).obj U.left) := inferInstanceAs (IsAffine U.left)
  exact isAffine_of_isAffineHom (pullback.snd (D.map j.hom).left U.hom)

/-- The native chart-tail projection has the original first pullback projection. -/
theorem relativeChartTailCone_π_fst (D : I ⥤ Over X) (c : Cone D)
    (i : I) (U : (D.obj i).left.Etale) (j : Over i) :
    ((relativeChartTailCone D c i U).π.app j).left ≫
        pullback.fst (D.map j.hom).left U.hom =
      pullback.fst (c.π.app i).left U.hom ≫ (c.π.app j.left).left := by
  exact Scheme.baseChangeCone_π_app_fst (D ⋙ Over.forget X)
    ((Over.forget X).mapCone c) i U.hom j

/-- The native chart-tail projection preserves the original chart coordinate. -/
theorem relativeChartTailCone_π_snd (D : I ⥤ Over X) (c : Cone D)
    (i : I) (U : (D.obj i).left.Etale) (j : Over i) :
    ((relativeChartTailCone D c i U).π.app j).left ≫
        pullback.snd (D.map j.hom).left U.hom =
      pullback.snd (c.π.app i).left U.hom := by
  exact Scheme.baseChangeCone_π_app_snd (D ⋙ Over.forget X)
    ((Over.forget X).mapCone c) i U.hom j

/-- The original tail arrow preserves the stage coordinate. -/
@[reassoc]
theorem relativeChartTail_map_fst (D : I ⥤ Over X) (i : I)
    (U : (D.obj i).left.Etale) {j k : Over i} (a : j ⟶ k) :
    ((relativeChartTail D i U).map a).left ≫ pullback.fst (D.map k.hom).left U.hom =
      pullback.fst (D.map j.hom).left U.hom ≫ (D.map a.left).left := by
  exact Scheme.baseChangeDiagram_map_fst (D ⋙ Over.forget X) i U.hom a

/-- The original tail arrow preserves the chart coordinate. -/
@[reassoc]
theorem relativeChartTail_map_snd (D : I ⥤ Over X) (i : I)
    (U : (D.obj i).left.Etale) {j k : Over i} (a : j ⟶ k) :
    ((relativeChartTail D i U).map a).left ≫ pullback.snd (D.map k.hom).left U.hom =
      pullback.snd (D.map j.hom).left U.hom := by
  exact Scheme.baseChangeDiagram_map_snd (D ⋙ Over.forget X) i U.hom a

/-- An original chart morphism gives its actual stage pullback map over the base. -/
def relativeChartTailMapApp (D : I ⥤ Over X) (i : I)
    {U V : (D.obj i).left.Etale} (a : U ⟶ V) (j : Over i) :
    (relativeChartTail D i U).obj j ⟶ (relativeChartTail D i V).obj j :=
  Over.homMk (pullback.lift (pullback.fst (D.map j.hom).left U.hom)
    (pullback.snd (D.map j.hom).left U.hom ≫ a.left) (by
      have hw : a.left ≫ V.hom = U.hom := MorphismProperty.Over.w a
      exact pullback.condition.trans ((Category.assoc _ _ _).trans
        (congrArg (fun z ↦ pullback.snd (D.map j.hom).left U.hom ≫ z) hw)).symm)) (by
    change (pullback.lift _ _ _) ≫ (pullback.snd (D.map j.hom).left V.hom ≫
      V.hom ≫ (D.obj i).hom) = pullback.snd (D.map j.hom).left U.hom ≫ U.hom ≫ (D.obj i).hom
    have hw : a.left ≫ V.hom = U.hom := MorphismProperty.Over.w a
    exact (pullback.lift_snd_assoc _ _ _ _).trans
      ((Category.assoc _ _ _).trans
        (congrArg (fun z ↦ pullback.snd (D.map j.hom).left U.hom ≫ z)
          ((Category.assoc _ _ _).symm.trans
            (congrArg (fun z ↦ z ≫ (D.obj i).hom) hw)))))

@[reassoc]
theorem relativeChartTailMapApp_fst (D : I ⥤ Over X) (i : I)
    {U V : (D.obj i).left.Etale} (a : U ⟶ V) (j : Over i) :
    (relativeChartTailMapApp D i a j).left ≫ pullback.fst (D.map j.hom).left V.hom =
      pullback.fst (D.map j.hom).left U.hom := by
  exact pullback.lift_fst _ _ _

@[reassoc]
theorem relativeChartTailMapApp_snd (D : I ⥤ Over X) (i : I)
    {U V : (D.obj i).left.Etale} (a : U ⟶ V) (j : Over i) :
    (relativeChartTailMapApp D i a j).left ≫ pullback.snd (D.map j.hom).left V.hom =
      pullback.snd (D.map j.hom).left U.hom ≫ a.left := by
  exact pullback.lift_snd _ _ _

/-- Chart morphisms act naturally on actual relative chart tails. -/
def relativeChartTailMap (D : I ⥤ Over X) (i : I)
    {U V : (D.obj i).left.Etale} (a : U ⟶ V) :
    relativeChartTail D i U ⟶ relativeChartTail D i V where
  app := relativeChartTailMapApp D i a
  naturality {j k} b := by
    apply Over.OverMorphism.ext
    apply pullback.hom_ext
    · have hleft := (Category.assoc
        ((relativeChartTail D i U).map b).left
        (relativeChartTailMapApp D i a k).left
        (pullback.fst (D.map k.hom).left V.hom)).trans
          ((congrArg (fun z ↦ ((relativeChartTail D i U).map b).left ≫ z)
            (relativeChartTailMapApp_fst D i a k)).trans
              (relativeChartTail_map_fst D i U b))
      have hright := (Category.assoc
        (relativeChartTailMapApp D i a j).left
        ((relativeChartTail D i V).map b).left
        (pullback.fst (D.map k.hom).left V.hom)).trans
          ((congrArg (fun z ↦ (relativeChartTailMapApp D i a j).left ≫ z)
            (relativeChartTail_map_fst D i V b)).trans
              ((Category.assoc _ _ _).symm.trans
                (congrArg (fun z ↦ z ≫ (D.map b.left).left)
                  (relativeChartTailMapApp_fst D i a j))))
      exact hleft.trans hright.symm
    · have hleft := (Category.assoc
        ((relativeChartTail D i U).map b).left
        (relativeChartTailMapApp D i a k).left
        (pullback.snd (D.map k.hom).left V.hom)).trans
          ((congrArg (fun z ↦ ((relativeChartTail D i U).map b).left ≫ z)
            (relativeChartTailMapApp_snd D i a k)).trans
              ((Category.assoc _ _ _).symm.trans
                (congrArg (fun z ↦ z ≫ a.left) (relativeChartTail_map_snd D i U b))))
      have hright := (Category.assoc
        (relativeChartTailMapApp D i a j).left
        ((relativeChartTail D i V).map b).left
        (pullback.snd (D.map k.hom).left V.hom)).trans
          ((congrArg (fun z ↦ (relativeChartTailMapApp D i a j).left ≫ z)
            (relativeChartTail_map_snd D i V b)).trans
              (relativeChartTailMapApp_snd D i a j))
      exact hleft.trans hright.symm

/-- The original stage étale site acts functorially on its actual relative tails. -/
def relativeChartTails (D : I ⥤ Over X) (i : I) :
    (D.obj i).left.Etale ⥤ (Over i ⥤ Over X) where
  obj := relativeChartTail D i
  map := relativeChartTailMap D i
  map_id U := by
    apply NatTrans.ext
    funext j
    apply Over.OverMorphism.ext
    change (relativeChartTailMapApp D i (𝟙 U) j).left = 𝟙 _
    apply pullback.hom_ext
    · exact (relativeChartTailMapApp_fst D i (𝟙 U) j).trans (Category.id_comp _).symm
    · have hid : (show U ⟶ U from 𝟙 U).left = 𝟙 U.left := rfl
      exact (relativeChartTailMapApp_snd D i (𝟙 U) j).trans
        ((congrArg (fun z ↦ pullback.snd (D.map j.hom).left U.hom ≫ z) hid).trans
          ((Category.comp_id _).trans (Category.id_comp _).symm))
  map_comp a b := by
    apply NatTrans.ext
    funext j
    apply Over.OverMorphism.ext
    change (relativeChartTailMapApp D i (a ≫ b) j).left =
      (relativeChartTailMapApp D i a j).left ≫ (relativeChartTailMapApp D i b j).left
    apply pullback.hom_ext
    · exact (relativeChartTailMapApp_fst D i (a ≫ b) j).trans
        ((Category.assoc _ _ _).trans
          ((congrArg (fun z ↦ (relativeChartTailMapApp D i a j).left ≫ z)
            (relativeChartTailMapApp_fst D i b j)).trans
              (relativeChartTailMapApp_fst D i a j))).symm
    · have hab : (a ≫ b).left = a.left ≫ b.left := rfl
      have hleft := (relativeChartTailMapApp_snd D i (a ≫ b) j).trans
        (congrArg (fun z ↦ pullback.snd (D.map j.hom).left _ ≫ z) hab)
      have hright := (Category.assoc
        (relativeChartTailMapApp D i a j).left (relativeChartTailMapApp D i b j).left
        (pullback.snd (D.map j.hom).left _)).trans
          ((congrArg (fun z ↦ (relativeChartTailMapApp D i a j).left ≫ z)
            (relativeChartTailMapApp_snd D i b j)).trans
              ((Category.assoc _ _ _).symm.trans
                ((congrArg (fun z ↦ z ≫ b.left) (relativeChartTailMapApp_snd D i a j)).trans
                  (Category.assoc _ _ _))))
      exact hleft.trans hright.symm

end AlgebraicGeometry.Scheme.EtaleAffineBasis
