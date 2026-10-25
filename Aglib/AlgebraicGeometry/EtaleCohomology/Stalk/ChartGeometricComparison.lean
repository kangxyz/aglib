/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Stalk.ChartPointedComparison

/-! # Original comparison from higher-image stalks to a common geometric fibre

The retained geometric point maps the literal geometric fibre to the chosen
strict-local fibre. Composing its original relative cohomology transfer with
the original stalk comparison gives a map to the geometric fibre. Its value
on every original pointed-neighborhood germ is the original relative pullback
along that same geometric point. No map between two marked models is chosen.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Stalk

universe u w s e

attribute [local instance] hasSheafifyLarge

open Continuity Finite.GeometricNeighborhood

private theorem overPullback_comp_eq
    {X S T A B : Scheme.{u}} (f : X ⟶ S) (t : T ⟶ S) (a : A ⟶ S) (b : B ⟶ S)
    (α : Over.mk (pullback.snd t f) ⟶ Over.mk (pullback.snd a f))
    (β : Over.mk (pullback.snd a f) ⟶ Over.mk (pullback.snd b f))
    (γ : Over.mk (pullback.snd t f) ⟶ Over.mk (pullback.snd b f))
    (m : T ⟶ A) (n : A ⟶ B)
    (hα : α.left ≫ pullback.fst a f = pullback.fst t f ≫ m)
    (hβ : β.left ≫ pullback.fst b f = pullback.fst a f ≫ n)
    (hγ : γ.left ≫ pullback.fst b f = pullback.fst t f ≫ m ≫ n) : α ≫ β = γ := by
  apply Over.OverMorphism.ext
  apply pullback.hom_ext
  · calc
      _ = α.left ≫ (β.left ≫ pullback.fst b f) := Category.assoc _ _ _
      _ = α.left ≫ (pullback.fst a f ≫ n) := congrArg (fun z => α.left ≫ z) hβ
      _ = (α.left ≫ pullback.fst a f) ≫ n := (Category.assoc _ _ _).symm
      _ = (pullback.fst t f ≫ m) ≫ n := congrArg (fun z => z ≫ n) hα
      _ = pullback.fst t f ≫ m ≫ n := Category.assoc _ _ _
      _ = _ := hγ.symm
  · exact (Over.w (α ≫ β)).trans (Over.w γ).symm

private theorem groupMap_comp_hom {A B C : AddCommGrpCat.{e}}
    (f : A ⟶ B) (g : B ⟶ C) (h : A ⟶ C) (heq : f ≫ g = h) :
    g.hom.comp f.hom = h.hom :=
  congrArg (fun k => k.hom) heq

private theorem relativeTransfer_comp_hom
    {X : Scheme.{u}} (F : AbelianSheaf.{u, u + 1} X) (q : ℕ) {A B C : Over X}
    [HasExt.{e} (AbelianSheaf.{u, u + 1} A.left)]
    [HasExt.{e} (AbelianSheaf.{u, u + 1} B.left)]
    [HasExt.{e} (AbelianSheaf.{u, u + 1} C.left)]
    (a : A ⟶ B) (b : B ⟶ C) (c : A ⟶ C) (h : a ≫ b = c) :
    (relativeCohomologyTransfer F q a).hom.comp
      (relativeCohomologyTransfer F q b).hom =
        (relativeCohomologyTransfer F q c).hom := by
  subst c
  exact groupMap_comp_hom
    (relativeCohomologyTransfer F q b) (relativeCohomologyTransfer F q a)
    (relativeCohomologyTransfer F q (a ≫ b)) (relativeCohomologyTransfer_comp F q a b)

universe vA vB vC vD

private theorem comparison_hom_of_leg
    {A : Type vA} {B : Type vB} {C : Type vC} {D : Type vD}
    [AddCommGroup A] [AddCommGroup B] [AddCommGroup C] [AddCommGroup D]
    (φ : A ≃+ B) (κ : B →+ C) (g : D →+ A) (l : D →+ B) (r : D →+ C)
    (hφ : φ.toAddMonoidHom.comp g = l) (hr : κ.comp l = r) :
    (κ.comp φ.toAddMonoidHom).comp g = r :=
  (congrArg (fun h => κ.comp h) hφ).trans hr

private theorem comparison_bijective
    {A : Type vA} {B : Type vB} {C : Type vC}
    [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
    (φ : A ≃+ B) (κ : B →+ C) (hκ : Function.Bijective κ) :
    Function.Bijective (κ.comp φ.toAddMonoidHom) :=
  hκ.comp φ.bijective

variable (Ω : Type u) [Field Ω] [IsSepClosed Ω]
  {X S : Scheme.{u}} (η : Spec (.of Ω) ⟶ S) (f : X ⟶ S)

/-- The literal geometric fibre maps to each original marked neighborhood fibre. -/
def geometricFibrePointedMap (d : (pointSmallEtale η).fiber.Elements) :
    Over.mk (pullback.snd η f) ⟶ (pointedNeighborhoodBaseChangedDiagram Ω η f).obj d := by
  change Over.mk (pullback.snd η f) ⟶ Over.mk (pullback.snd d.obj.hom f)
  let p : Over.mk η ⟶ (Scheme.Etale.forget S).obj d.obj := d.val
  exact Over.homMk
    (pullback.lift (f := d.obj.hom) (g := f)
      (pullback.fst η f ≫ p.left) (pullback.snd η f)
      ((Category.assoc _ _ _).trans
        ((congrArg (fun t => pullback.fst η f ≫ t) (Over.w p)).trans pullback.condition)))
    (pullback.lift_snd _ _ _)

/-- Its first projection retains the original marked point. -/
theorem geometricFibrePointedMap_fst (d : (pointSmallEtale η).fiber.Elements) :
    (geometricFibrePointedMap Ω η f d).left ≫ pullback.fst d.obj.hom f =
      pullback.fst η f ≫ d.val.left :=
  pullback.lift_fst _ _ _

/-- Its second projection is the original map to X. -/
theorem geometricFibrePointedMap_snd (d : (pointSmallEtale η).fiber.Elements) :
    (geometricFibrePointedMap Ω η f d).left ≫ pullback.snd d.obj.hom f =
      pullback.snd η f :=
  pullback.lift_snd _ _ _

variable (R : Type u) [CommRing R] [Algebra R Ω]
  (j : Spec (.of R) ⟶ S) [Etale j] [Mono j]
  (hη : Spec.algebraMap R Ω ≫ j = η)

/-- The retained point gives an actual relative map to the chosen strict-local fibre. -/
def chartGeometricPointMap :
    Over.mk (pullback.snd η f) ⟶ (pointedNeighborhoodBaseChangedCone R Ω j η hη f).pt := by
  change Over.mk (pullback.snd η f) ⟶
    Over.mk (pullback.snd (Spec.algebraMap R (GeometricEtaleColimit R Ω) ≫ j) f)
  exact Over.homMk
    (pullback.lift (f := Spec.algebraMap R (GeometricEtaleColimit R Ω) ≫ j) (g := f)
      (pullback.fst η f ≫ point R Ω) (pullback.snd η f)
      ((Category.assoc _ _ _).trans
        ((congrArg (fun t => pullback.fst η f ≫ t)
          (point_pointedNeighborhood_structure R Ω j η hη)).trans pullback.condition)))
    (pullback.lift_snd _ _ _)

/-- The actual point is retained by the first projection. -/
theorem chartGeometricPointMap_fst :
    (chartGeometricPointMap Ω η f R j hη).left ≫
        pullback.fst (Spec.algebraMap R (GeometricEtaleColimit R Ω) ≫ j) f =
      pullback.fst η f ≫ point R Ω :=
  pullback.lift_fst _ _ _

/-- The second projection remains the original geometric fibre map to X. -/
theorem chartGeometricPointMap_snd :
    (chartGeometricPointMap Ω η f R j hη).left ≫
        pullback.snd (Spec.algebraMap R (GeometricEtaleColimit R Ω) ≫ j) f =
      pullback.snd η f :=
  pullback.lift_snd _ _ _

/-- The original point and cone leg compose to the literal marked-neighborhood map. -/
theorem chartGeometricPointMap_π (d : (pointSmallEtale η).fiber.Elements) :
    chartGeometricPointMap Ω η f R j hη ≫
        (pointedNeighborhoodBaseChangedCone R Ω j η hη f).π.app d =
      geometricFibrePointedMap Ω η f d := by
  have hfst :
      ((pointedNeighborhoodBaseChangedCone R Ω j η hη f).π.app d).left ≫
          pullback.fst d.obj.hom f =
        pullback.fst (Spec.algebraMap R (GeometricEtaleColimit R Ω) ≫ j) f ≫
          (pointedNeighborhoodCone R Ω j η hη).π.app d :=
    pullback.lift_fst _ _ _
  have hγ : (geometricFibrePointedMap Ω η f d).left ≫ pullback.fst d.obj.hom f =
      pullback.fst η f ≫ point R Ω ≫ (pointedNeighborhoodCone R Ω j η hη).π.app d :=
    (geometricFibrePointedMap_fst Ω η f d).trans
      (congrArg (fun z => pullback.fst η f ≫ z)
        (point_pointedNeighborhoodCone_π R Ω j η hη d).symm)
  exact overPullback_comp_eq f η
    (Spec.algebraMap R (GeometricEtaleColimit R Ω) ≫ j) d.obj.hom
    (chartGeometricPointMap Ω η f R j hη)
    ((pointedNeighborhoodBaseChangedCone R Ω j η hη f).π.app d)
    (geometricFibrePointedMap Ω η f d) (point R Ω)
    ((pointedNeighborhoodCone R Ω j η hη).π.app d)
    (chartGeometricPointMap_fst Ω η f R j hη) hfst hγ

variable
  [HasExt.{w} (AbelianSheaf.{u, u + 1} X)]
  [∀ U : S.Etale, HasExt.{s} (Sheaf ((Scheme.smallEtaleTopology X).over
    ((siteBaseChange f).obj U)) AddCommGrpCat.{u + 1})]
  [∀ U : S.Etale, HasExt.{e} (AbelianSheaf.{u, u + 1} (pullback U.hom f))]
  [HasExt.{e} (AbelianSheaf.{u, u + 1}
    (pullback (Spec.algebraMap R (GeometricEtaleColimit R Ω) ≫ j) f))]
  [HasExt.{e} (AbelianSheaf.{u, u + 1} (pullback η f))]
  [QuasiCompact f] [QuasiSeparated f]
  [HasColimitsOfShape (GeometricEtaleNeighborhood R Ω) AddCommGrpCat.{e}]
  (F : AbelianSheaf.{u, u + 1} X) (q : ℕ)

local instance chartGeometricComparisonGeometricExt :
    HasExt.{e} (AbelianSheaf.{u, u + 1} (Over.mk (pullback.snd η f)).left) :=
  inferInstanceAs (HasExt.{e} (AbelianSheaf.{u, u + 1} (pullback η f)))

local instance chartGeometricComparisonApexExt : HasExt.{e} (AbelianSheaf.{u, u + 1}
    (pointedNeighborhoodBaseChangedCone R Ω j η hη f).pt.left) :=
  inferInstanceAs (HasExt.{e} (AbelianSheaf.{u, u + 1}
    (pullback (Spec.algebraMap R (GeometricEtaleColimit R Ω) ≫ j) f)))

local instance chartGeometricComparisonStageExt (d : (pointSmallEtale η).fiber.Elements) :
    HasExt.{e} (AbelianSheaf.{u, u + 1}
      ((pointedNeighborhoodBaseChangedDiagram Ω η f).obj d).left) :=
  inferInstanceAs (HasExt.{e} (AbelianSheaf.{u, u + 1} (pullback d.obj.hom f)))

/-- The original stalk comparison followed by the original geometric-point transfer. -/
def chartGeometricCohomologyComparison :
    ((pointSmallEtale η).sheafFiber (A := AddCommGrpCat.{u + 1})).obj
        ((higherDirectImage f q).obj F) →+
      Sheaf.H.{e} ((inverseImage (pullback.snd η f)).obj F) q :=
  (relativeCohomologyTransfer F q (chartGeometricPointMap Ω η f R j hη)).hom.comp
    (chartStrictLocalCohomologyAddEquiv R Ω j η hη f F q).toAddMonoidHom

omit [HasExt.{e} (AbelianSheaf.{u, u + 1} (pullback η f))] in
/-- Retain the original strict-local comparison as one complete additive-map
identity before postcomposing the actual geometric transfer. -/
private theorem chartStrictLocalComparison_pointedHom
    (d : (pointSmallEtale η).fiber.Elements) :
    (chartStrictLocalCohomologyAddEquiv R Ω j η hη f F q).toAddMonoidHom.comp
        (fibreProductCohomologyGerm f d.obj F q η d.val) =
      (pointedCohomologyLeg R Ω j η hη f F q d).hom := by
  ext x
  exact chartStrictLocalCohomologyAddEquiv_pointedGerm R Ω j η hη f F q d x

omit [HasExt.{w} (AbelianSheaf.{u, u + 1} X)]
  [∀ U : S.Etale, HasExt.{s} (Sheaf ((Scheme.smallEtaleTopology X).over
    ((siteBaseChange f).obj U)) AddCommGrpCat.{u + 1})]
  [QuasiCompact f] [QuasiSeparated f]
  [HasColimitsOfShape (GeometricEtaleNeighborhood R Ω) AddCommGrpCat.{e}] in
/-- Normalize the complete original pointed leg followed by the retained
geometric transfer, before either map is evaluated on cohomology. -/
private theorem chartGeometricTransfer_pointedHom
    (d : (pointSmallEtale η).fiber.Elements) :
    (relativeCohomologyTransfer F q (chartGeometricPointMap Ω η f R j hη)).hom.comp
        (pointedCohomologyLeg R Ω j η hη f F q d).hom =
      (relativeCohomologyTransfer F q (geometricFibrePointedMap Ω η f d)).hom :=
  relativeTransfer_comp_hom F q (chartGeometricPointMap Ω η f R j hη)
    ((pointedNeighborhoodBaseChangedCone R Ω j η hη f).π.app d)
    (geometricFibrePointedMap Ω η f d) (chartGeometricPointMap_π Ω η f R j hη d)

/-- Compose the original two whole-map identities while retaining the literal
public comparison, so the scalar conclusion requires only evaluation. -/
private theorem chartGeometricComparison_pointedHom
    (d : (pointSmallEtale η).fiber.Elements) :
    (chartGeometricCohomologyComparison Ω η f R j hη F q).comp
        (fibreProductCohomologyGerm f d.obj F q η d.val) =
      (relativeCohomologyTransfer F q (geometricFibrePointedMap Ω η f d)).hom :=
  comparison_hom_of_leg
    (chartStrictLocalCohomologyAddEquiv R Ω j η hη f F q)
    (relativeCohomologyTransfer F q (chartGeometricPointMap Ω η f R j hη)).hom
    (fibreProductCohomologyGerm f d.obj F q η d.val)
    (pointedCohomologyLeg R Ω j η hη f F q d).hom
    (relativeCohomologyTransfer F q (geometricFibrePointedMap Ω η f d)).hom
    (chartStrictLocalComparison_pointedHom Ω η f R j hη F q d)
    (chartGeometricTransfer_pointedHom Ω η f R j hη F q d)

/-- On each original germ this comparison is the original geometric-fibre pullback. -/
theorem chartGeometricCohomologyComparison_pointedGerm
    (d : (pointSmallEtale η).fiber.Elements)
    (x : Sheaf.H.{e} ((inverseImage (pullback.snd d.obj.hom f)).obj F) q) :
    chartGeometricCohomologyComparison Ω η f R j hη F q
        (fibreProductCohomologyGerm f d.obj F q η d.val x) =
      relativeCohomologyTransfer F q (geometricFibrePointedMap Ω η f d) x :=
  DFunLike.congr_fun (chartGeometricComparison_pointedHom Ω η f R j hη F q d) x

/-- Actual local-to-geometric bijectivity makes the original stalk comparison bijective. -/
theorem chartGeometricCohomologyComparison_bijective
    (hκ : Function.Bijective
      (relativeCohomologyTransfer F q (chartGeometricPointMap Ω η f R j hη))) :
    Function.Bijective (chartGeometricCohomologyComparison Ω η f R j hη F q) :=
  comparison_bijective (chartStrictLocalCohomologyAddEquiv R Ω j η hη f F q)
    (relativeCohomologyTransfer F q (chartGeometricPointMap Ω η f R j hη)).hom hκ

end AlgebraicGeometry.Scheme.EtaleCohomology.Stalk
