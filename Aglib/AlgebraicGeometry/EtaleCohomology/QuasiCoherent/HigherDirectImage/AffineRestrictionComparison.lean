/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.QuasiCoherent.AdditiveSectionsPostcomp
public import Aglib.AlgebraicGeometry.EtaleCohomology.QuasiCoherent.ModulePullbackCompositionCohomology
public import Aglib.AlgebraicGeometry.EtaleCohomology.BaseChangeMap
public import Aglib.AlgebraicGeometry.EtaleCohomology.QuasiCoherent.HigherDirectImage.AffineSections
public import Aglib.AlgebraicGeometry.EtaleCohomology.QuasiCoherent.HigherDirectImage.AffineTransition
public import Aglib.AlgebraicGeometry.Sites.EtaleAffineBasis.Restriction
public import Aglib.AlgebraicGeometry.Sites.EtaleAffineBasis.ForgetMaps
public import Aglib.CategoryTheory.Over.SitePullbackPasting

/-! # Pre-coefficient comparison for original affine-test restrictions -/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite
open AlgebraicGeometry.Scheme.Cohomology

universe u e e'

namespace AlgebraicGeometry.Scheme.EtaleCohomology.QuasiCoherent

attribute [local instance] HasExt.standard hasSheafifyLarge
  moduleComparisonEnoughSmall moduleComparisonEnoughRaised
  moduleComparisonAbWRaised moduleComparisonTypeWRaised

/-- The actual morphism between native fibre-product tests is cartesian over
the original test morphism. Both original pullback projections are retained. -/
theorem affineTestTransition_isPullback
    {X S : Scheme.{u}} (f : X ⟶ S) {U V : S.AffineEtale} (g : V ⟶ U) :
    IsPullback
      ((siteBaseChange f).map ((Scheme.AffineEtale.Spec S).map g)).left
      (Limits.pullback.fst ((Scheme.AffineEtale.Spec S).obj V).hom f) (Limits.pullback.fst
        ((Scheme.AffineEtale.Spec S).obj U).hom f)
      ((Scheme.AffineEtale.Spec S).map g).left := by
  apply IsPullback.of_two_pullback_projections
    (IsPullback.of_hasPullback ((Scheme.AffineEtale.Spec S).obj V).hom f)
      (IsPullback.of_hasPullback ((Scheme.AffineEtale.Spec S).obj U).hom f)
  · exact MorphismProperty.Over.w ((Scheme.AffineEtale.Spec S).map g)
  · exact Limits.pullback.lift_fst _ _ _
  · exact MorphismProperty.Over.w
      ((siteBaseChange f).map ((Scheme.AffineEtale.Spec S).map g))

private theorem section_postcomp_apply_eq {S : Scheme.{u}}
    {C D : Type*} [Category C] [Category D]
    {R T₀ : CommRingCat.{u}} (j : Spec R ⟶ S) (j' : Spec T₀ ⟶ S)
    (φ : R ⟶ T₀) (hj : Spec.map φ ≫ j = j')
    (F : C ⥤ S.Modules) (G : C ⥤ D) (T : D ⥤ (Spec T₀).Modules)
    (bc : F ⋙ Scheme.Modules.pullback (X := Spec T₀) (Y := S) j' ⟶ G ⋙ T)
    (M : C) [(F.obj M).IsQuasicoherent]
    {Q : Type e} (P : (moduleSpecΓFunctor (R := T₀)).obj (T.obj (G.obj M)) → Q)
    (x : (moduleSpecΓFunctor (R := R)).obj
      ((Scheme.Modules.pullback (X := Spec R) (Y := S) j).obj (F.obj M))) (z : Q)
    (h : P ((moduleSpecΓFunctor (R := T₀)).map
      ((Scheme.Modules.pullbackComp (X := Spec T₀)
        (Y := Spec R) (Z := S) (Spec.map φ) j).hom.app (F.obj M) ≫
        (Scheme.Modules.pullbackCongr (X := Spec T₀) (Y := S)
          hj).hom.app (F.obj M) ≫
        bc.app M)
      ((((Scheme.Modules.pullbackPushforwardAdjunction
        (X := Spec T₀) (Y := Spec R) (Spec.map φ)).unit.app
        ((Scheme.Modules.pullback (X := Spec R) (Y := S) j).obj
          (F.obj M))).app ⊤) x)) = z) :
    P ((moduleSpecΓFunctor (R := T₀)).map (bc.app M)
      (sectionsAddHom S (F.obj M)
        (Over.homMk (U := Over.mk j') (V := Over.mk j) (Spec.map φ) hj) x)) = z :=
  (congrArg P (sectionsAddHom_affine_postcomp (F.obj M) j j' φ hj
    (T.obj (G.obj M)) (bc.app M) x)).trans h


variable {X S : Scheme.{u}} (f : X ⟶ S) [QuasiCompact f] [QuasiSeparated f]
  (M : X.Modules) [M.IsQuasicoherent] (q : ℕ)

local instance :
    (((Scheme.Modules.pushforward f).rightDerived q).obj M).IsQuasicoherent :=
  moduleHigherDirectImage_isQuasicoherent f M q

local instance (U : S.AffineEtale) : Etale ((Scheme.AffineEtale.Spec S).obj U).hom :=
  ((Scheme.AffineEtale.Spec S).obj U).prop

local instance (U : S.AffineEtale)
    [h : HasExt.{e} (AbelianSheaf.{u, u + 1} (Limits.pullback ((Scheme.AffineEtale.Spec S).obj
      U).hom f))] :
    HasExt.{e} (AbelianSheaf.{u, u + 1}
      ((siteBaseChange f).obj ((Scheme.AffineEtale.Spec S).obj U)).left) := h

/-- The complete original pre-coefficient restriction equation. The section
arrow and both original cohomology comparisons are retained as supplied. -/
def AffineSectionsPreCoefficientRestriction
    {W Z : Scheme.{u}} {R T : CommRingCat.{u}}
    (j : Spec R ⟶ S) (j' : Spec T ⟶ S) [Etale j] [Etale j']
    (a : W ⟶ X) (b : W ⟶ Spec R)
    (c : Z ⟶ W) (d : Z ⟶ Spec T) (a' : Z ⟶ X)
    (h : IsPullback a b f j) (H : IsPullback a' d f j') (ha : c ≫ a = a')
    (I : InjectiveResolution ((Scheme.Modules.pullback a).obj M))
    (K : InjectiveResolution ((Scheme.Modules.pullback a').obj M))
    [HasExt.{e} (AbelianSheaf.{u, u + 1} W)]
    [HasExt.{e'} (AbelianSheaf.{u, u + 1} Z)]
    (r : Over.mk j' ⟶ Over.mk j)
    (x : (moduleSpecΓFunctor (R := R)).obj
      ((Scheme.Modules.pullback j).obj
        (((Scheme.Modules.pushforward f).rightDerived q).obj M))) : Prop :=
    let : QuasiCompact b := MorphismProperty.of_isPullback h inferInstance
    let : QuasiSeparated b := MorphismProperty.of_isPullback h inferInstance
    let : QuasiCompact d := MorphismProperty.of_isPullback H inferInstance
    let : QuasiSeparated d := MorphismProperty.of_isPullback H inferInstance
    let N := (Scheme.Modules.pullback a).obj M
    let N' := (Scheme.Modules.pullback a').obj M
    let B := ((Scheme.Modules.pushforward f).rightDerived q).obj M
    let : ((Scheme.Modules.pullback a ⋙ Scheme.Modules.pullback c).obj M).IsQuasicoherent :=
      inferInstanceAs (((Scheme.Modules.pullback c).obj N).IsQuasicoherent)
    @Eq (Sheaf.H.{e'} (additiveCoefficient (Z) N') q)
    (moduleCohomologyComparison.{u, u + 1, e'} (Z) N' q
      (moduleHigherDirectImageAffineSectionsLinearEquiv (R := (T : Type u))
        d N' K q
        ((moduleSpecΓFunctor (R := T)).map
          ((Scheme.Modules.higherDirectImageFlatBaseChangeMap a' d f j' H q).app M)
          (sectionsAddHom S B r x))))
    (Sheaf.H.map (additiveCoefficientMap (Z)
      ((Scheme.Modules.pullbackComp c a).hom.app M ≫
        (Scheme.Modules.pullbackCongr ha).hom.app M)) q
      (additiveCoefficientCohomologyPullback.{u, e, e'} c N q
        (moduleCohomologyComparison.{u, u + 1, e} (W) N q
          (moduleHigherDirectImageAffineSectionsLinearEquiv (R := (R : Type u))
            b N I q
            ((moduleSpecΓFunctor (R := R)).map
              ((Scheme.Modules.higherDirectImageFlatBaseChangeMap
                a b f j h q).app M) x)))))

/-- Complete original affine-test section comparison before specializing the
schemes carrying either cohomology group to a native fibre product. -/
private theorem affineSections_preCoefficient_restriction_of_squares
    {W Z : Scheme.{u}} {R T : CommRingCat.{u}}
    (j : Spec R ⟶ S) (j' : Spec T ⟶ S) (φ : R ⟶ T)
    (hj : Spec.map φ ≫ j = j') [Etale j] [Etale j'] [Etale (Spec.map φ)]
    (a : W ⟶ X) (b : W ⟶ Spec R)
    (c : Z ⟶ W) (d : Z ⟶ Spec T) (a' : Z ⟶ X)
    (h : IsPullback a b f j) (h' : IsPullback c d b (Spec.map φ))
    (H : IsPullback a' d f j') (ha : c ≫ a = a')
    (I : InjectiveResolution ((Scheme.Modules.pullback a).obj M))
    (J : InjectiveResolution ((Scheme.Modules.pullback c).obj
      ((Scheme.Modules.pullback a).obj M)))
    (K : InjectiveResolution ((Scheme.Modules.pullback a').obj M))
    [HasExt.{e} (AbelianSheaf.{u, u + 1} W)]
    [HasExt.{e'} (AbelianSheaf.{u, u + 1} Z)]
    (r : Over.mk j' ⟶ Over.mk j)
    (hr : r = Over.homMk (U := Over.mk j') (V := Over.mk j) (Spec.map φ) hj)
    (x : (moduleSpecΓFunctor (R := R)).obj
      ((Scheme.Modules.pullback j).obj
        (((Scheme.Modules.pushforward f).rightDerived q).obj M))) :
    AffineSectionsPreCoefficientRestriction.{u, e, e'} f M q j j'
      a b c d a' h H ha I K r x := by
  subst r
  unfold AffineSectionsPreCoefficientRestriction
  let : Etale c := MorphismProperty.of_isPullback h'.flip inferInstance
  let : QuasiCompact b := MorphismProperty.of_isPullback h inferInstance
  let : QuasiSeparated b := MorphismProperty.of_isPullback h inferInstance
  let : QuasiCompact d := MorphismProperty.of_isPullback H inferInstance
  let : QuasiSeparated d := MorphismProperty.of_isPullback H inferInstance
  let N := (Scheme.Modules.pullback a).obj M
  let N' := (Scheme.Modules.pullback a').obj M
  let B := ((Scheme.Modules.pushforward f).rightDerived q).obj M
  have triangle := moduleCohomologyComparison_affineFlatBaseChange_triangle.{u, e, e'}
    (R := R) (T := T) (W := W) (Z := Z)
    a b f j h c d φ h' M q a' j' H ha hj I J K x
  have candidate := section_postcomp_apply_eq j j' φ hj
    ((Scheme.Modules.pushforward f).rightDerived q) (Scheme.Modules.pullback a')
    ((Scheme.Modules.pushforward d).rightDerived q)
    (Scheme.Modules.higherDirectImageFlatBaseChangeMap a' d f j' H q) M
    (fun y => moduleCohomologyComparison.{u, u + 1, e'} Z N' q
      (moduleHigherDirectImageAffineSectionsLinearEquiv
        (R := (T : Type u)) d N' K q y)) x _ triangle
  convert candidate using 1

/-- The complete original affine section and inverse coefficient equation,
proved before either chart is specialized to a native fibre product. -/
theorem affineSections_coefficient_restriction_of_squares
    {W Z : Scheme.{u}} {R T : CommRingCat.{u}}
    (j : Spec R ⟶ S) (j' : Spec T ⟶ S) (φ : R ⟶ T)
    (hj : Spec.map φ ≫ j = j') [Etale j] [Etale j'] [Etale (Spec.map φ)]
    (a : W ⟶ X) (b : W ⟶ Spec R)
    (c : Z ⟶ W) (d : Z ⟶ Spec T) (a' : Z ⟶ X)
    (h : IsPullback a b f j) (h' : IsPullback c d b (Spec.map φ))
    (H : IsPullback a' d f j') (ha : c ≫ a = a')
    (I : InjectiveResolution ((Scheme.Modules.pullback a).obj M))
    (J : InjectiveResolution ((Scheme.Modules.pullback c).obj
      ((Scheme.Modules.pullback a).obj M)))
    (K : InjectiveResolution ((Scheme.Modules.pullback a').obj M))
    [HasExt.{e} (AbelianSheaf.{u, u + 1} W)]
    [HasExt.{e'} (AbelianSheaf.{u, u + 1} Z)]
    (r : Over.mk j' ⟶ Over.mk j)
    (hr : r = Over.homMk (U := Over.mk j') (V := Over.mk j) (Spec.map φ) hj)
    (x : (moduleSpecΓFunctor (R := R)).obj
      ((Scheme.Modules.pullback j).obj
        (((Scheme.Modules.pushforward f).rightDerived q).obj M))) :
    let : Etale a := MorphismProperty.of_isPullback h.flip inferInstance
    let : Etale c := MorphismProperty.of_isPullback h'.flip inferInstance
    let : Etale a' := MorphismProperty.of_isPullback H.flip inferInstance
    let : QuasiCompact b := MorphismProperty.of_isPullback h inferInstance
    let : QuasiSeparated b := MorphismProperty.of_isPullback h inferInstance
    let : QuasiCompact d := MorphismProperty.of_isPullback H inferInstance
    let : QuasiSeparated d := MorphismProperty.of_isPullback H inferInstance
    let N := (Scheme.Modules.pullback a).obj M
    let N' := (Scheme.Modules.pullback a').obj M
    Sheaf.H.map (inv (additiveCoefficientPullback a' M)) q
      (moduleCohomologyComparison.{u, u + 1, e'} Z N' q
        (moduleHigherDirectImageAffineSectionsLinearEquiv (R := (T : Type u)) d N' K q
          ((moduleSpecΓFunctor (R := T)).map
            ((Scheme.Modules.higherDirectImageFlatBaseChangeMap a' d f j' H q).app M)
            (sectionsAddHom S (((Scheme.Modules.pushforward f).rightDerived q).obj M) r x)))) =
    Sheaf.H.map
      ((EtaleCohomology.pullbackTriangleIso a' a c ha).inv.app (additiveCoefficient X M)) q
      (cohomologyPullback.{u, e, e'} c ((inverseImage a).obj (additiveCoefficient X M)) q
        (Sheaf.H.map (inv (additiveCoefficientPullback a M)) q
          (moduleCohomologyComparison.{u, u + 1, e} W N q
            (moduleHigherDirectImageAffineSectionsLinearEquiv (R := (R : Type u)) b N I q
              ((moduleSpecΓFunctor (R := R)).map
                ((Scheme.Modules.higherDirectImageFlatBaseChangeMap a b f j h q).app M) x))))) := by
  let : Etale a := MorphismProperty.of_isPullback h.flip inferInstance
  let : Etale c := MorphismProperty.of_isPullback h'.flip inferInstance
  let : Etale a' := MorphismProperty.of_isPullback H.flip inferInstance
  let : QuasiCompact b := MorphismProperty.of_isPullback h inferInstance
  let : QuasiSeparated b := MorphismProperty.of_isPullback h inferInstance
  let : QuasiCompact d := MorphismProperty.of_isPullback H inferInstance
  let : QuasiSeparated d := MorphismProperty.of_isPullback H inferInstance
  dsimp only
  have hp := affineSections_preCoefficient_restriction_of_squares.{u, e, e'} f M q
    (W := W) (Z := Z) (R := R) (T := T)
    j j' φ hj a b c d a' h h' H ha I J K r hr x
  dsimp only [AffineSectionsPreCoefficientRestriction] at hp
  have ht := additiveCoefficientCohomologyPullback_triangle_inv.{u, e, e'}
    a c a' ha M q
      (moduleCohomologyComparison.{u, u + 1, e} W ((Scheme.Modules.pullback a).obj M) q
        (moduleHigherDirectImageAffineSectionsLinearEquiv (R := (R : Type u)) b
          ((Scheme.Modules.pullback a).obj M) I q
          ((moduleSpecΓFunctor (R := R)).map
            ((Scheme.Modules.higherDirectImageFlatBaseChangeMap a b f j h q).app M) x)))
  simp only [Scheme.Modules.pullbackTriangleIso_hom_app] at ht
  dsimp only [Functor.comp_obj] at hp
  have hc := congrArg (Sheaf.H.map (inv (additiveCoefficientPullback a' M)) q) hp
  have hfinal := hc.trans ht
  convert hfinal using 1

/-- The original affine section restriction intertwines the native flat
base-change maps and absolute module/étale comparisons before the final
inverse coefficient map. -/
theorem higherDirectImageAffineSections_preCoefficient_restriction
    {U V : S.AffineEtale} (g : V ⟶ U)
    [hExtU : HasExt.{e} (AbelianSheaf.{u, u + 1} (Limits.pullback ((Scheme.AffineEtale.Spec
      S).obj U).hom f))]
    [hExtV : HasExt.{e'} (AbelianSheaf.{u, u + 1} (Limits.pullback ((Scheme.AffineEtale.Spec
      S).obj V).hom f))]
    (x : (moduleSpecΓFunctor (R := U.left.unop)).obj
      ((Scheme.Modules.pullback ((Scheme.AffineEtale.Spec S).obj U).hom).obj
        (((Scheme.Modules.pushforward f).rightDerived q).obj M))) :
    AffineSectionsPreCoefficientRestriction.{u, e, e'} f M q
      (W := Limits.pullback ((Scheme.AffineEtale.Spec S).obj U).hom f)
      (Z := Limits.pullback ((Scheme.AffineEtale.Spec S).obj V).hom f)
      ((Scheme.AffineEtale.Spec S).obj
      U).hom ((Scheme.AffineEtale.Spec S).obj V).hom
      (Limits.pullback.snd ((Scheme.AffineEtale.Spec S).obj U).hom f) (Limits.pullback.fst
        ((Scheme.AffineEtale.Spec S).obj U).hom f)
      (((siteBaseChange f).map ((Scheme.AffineEtale.Spec S).map g)).left)
      (Limits.pullback.fst ((Scheme.AffineEtale.Spec S).obj V).hom f) (Limits.pullback.snd
        ((Scheme.AffineEtale.Spec S).obj V).hom f)
      (IsPullback.of_hasPullback ((Scheme.AffineEtale.Spec S).obj U).hom f).flip
      (IsPullback.of_hasPullback ((Scheme.AffineEtale.Spec S).obj V).hom f).flip
      (siteBaseChange_map_snd f ((Scheme.AffineEtale.Spec S).map g))
      (injectiveResolution _) (injectiveResolution _)
      ((Scheme.Etale.forget S).map ((Scheme.AffineEtale.Spec S).map g)) x := by
  let : Etale (Spec.map g.left.unop) :=
    inferInstanceAs (Etale ((Scheme.AffineEtale.Spec S).map g).left)
  exact affineSections_preCoefficient_restriction_of_squares.{u, e, e'} f M q
    (W := Limits.pullback ((Scheme.AffineEtale.Spec S).obj U).hom f)
    (Z := Limits.pullback ((Scheme.AffineEtale.Spec S).obj V).hom f)
    ((Scheme.AffineEtale.Spec S).obj U).hom ((Scheme.AffineEtale.Spec S).obj V).hom g.left.unop
    (MorphismProperty.Over.w ((Scheme.AffineEtale.Spec S).map g))
    (Limits.pullback.snd ((Scheme.AffineEtale.Spec S).obj U).hom f) (Limits.pullback.fst
      ((Scheme.AffineEtale.Spec S).obj U).hom f)
    (((siteBaseChange f).map ((Scheme.AffineEtale.Spec S).map g)).left)
    (Limits.pullback.fst ((Scheme.AffineEtale.Spec S).obj V).hom f) (Limits.pullback.snd
      ((Scheme.AffineEtale.Spec S).obj V).hom f)
    (IsPullback.of_hasPullback ((Scheme.AffineEtale.Spec S).obj U).hom f).flip
      (affineTestTransition_isPullback f g)
    (IsPullback.of_hasPullback ((Scheme.AffineEtale.Spec S).obj V).hom f).flip
    (siteBaseChange_map_snd f ((Scheme.AffineEtale.Spec S).map g))
    (injectiveResolution _) (injectiveResolution _) (injectiveResolution _)
    ((Scheme.Etale.forget S).map ((Scheme.AffineEtale.Spec S).map g))
    (Scheme.EtaleAffineBasis.forget_spec_map g) x

end AlgebraicGeometry.Scheme.EtaleCohomology.QuasiCoherent
