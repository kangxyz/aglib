/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Group.Equiv.ComparisonComposite
public import Aglib.AlgebraicGeometry.EtaleCohomology.QuasiCoherent.HigherDirectImage.AffineSections
public import Aglib.AlgebraicGeometry.EtaleCohomology.QuasiCoherent.HigherDirectImage.AffineRestrictionComparison
public import Aglib.AlgebraicGeometry.EtaleCohomology.QuasiCoherent.ModulePullbackCompositionCohomology
public import Aglib.AlgebraicGeometry.EtaleCohomology.Stalk.FibreProductRestrictionCanonical
public import Aglib.AlgebraicGeometry.Sites.EtaleAffineBasis.Restriction
public import Aglib.CategoryTheory.Over.SitePullbackPasting

/-! # Actual affine-test transition of the relative cohomology comparison -/

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

/-- The affine-test equivalence retains every original forward map. -/
theorem higherDirectImageAffineSectionsEquiv_apply
    {X S : Scheme.{u}} (f : X ⟶ S) [QuasiCompact f] [QuasiSeparated f]
    {R : CommRingCat.{u}} (j : Spec R ⟶ S) [Etale j]
    (M : X.Modules) [M.IsQuasicoherent] (q : ℕ)
    [HasExt.{e} (AbelianSheaf.{u, u + 1} (Limits.pullback j f))]
    (x : (moduleSpecΓFunctor (R := R)).obj
      ((Scheme.Modules.pullback j).obj
        (((Scheme.Modules.pushforward f).rightDerived q).obj M))) :
    let a := Limits.pullback.snd j f
    let b := Limits.pullback.fst j f
    let h : IsPullback a b f j := (IsPullback.of_hasPullback j f).flip
    let : QuasiCompact b := inferInstance
    let : QuasiSeparated b := inferInstance
    let N := (Scheme.Modules.pullback a).obj M
    @Eq (Sheaf.H.{e} ((inverseImage a).obj (additiveCoefficient X M)) q)
      (higherDirectImageAffineSectionsEquiv.{u, e} f j M q x)
      (Sheaf.H.map (inv (additiveCoefficientPullback a M)) q
        (moduleCohomologyComparison.{u, u + 1, e} (Limits.pullback j f) N q
          (moduleHigherDirectImageAffineSectionsLinearEquiv b N (injectiveResolution N) q
            ((moduleSpecΓFunctor (R := R)).map
              ((Scheme.Modules.higherDirectImageFlatBaseChangeMap a b f j h q).app M) x)))) := by
  simp only [higherDirectImageAffineSectionsEquiv,
    Sheaf.moduleCohomologyComposite_apply, Functor.mapIso_hom,
    Scheme.Modules.higherDirectImageFlatBaseChangeIso_hom, Iso.symm_hom, asIso_inv]
  rfl

variable {X S : Scheme.{u}} (f : X ⟶ S) [QuasiCompact f] [QuasiSeparated f]
  (M : X.Modules) [M.IsQuasicoherent] (q : ℕ)

local instance :
    (((Scheme.Modules.pushforward f).rightDerived q).obj M).IsQuasicoherent :=
  moduleHigherDirectImage_isQuasicoherent f M q

local instance (U : S.AffineEtale) : Etale ((Scheme.AffineEtale.Spec S).obj U).hom :=
  ((Scheme.AffineEtale.Spec S).obj U).prop

local instance (U : S.AffineEtale)
    [h : HasExt.{e} (AbelianSheaf.{u, u + 1}
      (Limits.pullback ((Scheme.AffineEtale.Spec S).obj U).hom f))] :
    HasExt.{e} (AbelianSheaf.{u, u + 1}
      ((siteBaseChange f).obj ((Scheme.AffineEtale.Spec S).obj U)).left) := h

/-- The whole value formula of the original restriction, retained before any
coefficient or affine-test specialization. -/
def CoefficientRestrictionFormula {X W Z : Scheme.{u}}
    (a : W ⟶ X) (a' : Z ⟶ X) (c : Z ⟶ W) (ha : c ≫ a = a')
    [HasExt.{e} (AbelianSheaf.{u, u + 1} W)]
    [HasExt.{e'} (AbelianSheaf.{u, u + 1} Z)]
    (F : AbelianSheaf.{u, u + 1} X) (q : ℕ)
    (ρ : Sheaf.H.{e} ((inverseImage a).obj F) q →+
      Sheaf.H.{e'} ((inverseImage a').obj F) q) : Prop :=
  ∀ z, ρ z = Sheaf.H.map
    ((EtaleCohomology.pullbackTriangleIso a' a c ha).inv.app F) q
    (cohomologyPullback.{u, e, e'} c ((inverseImage a).obj F) q z)

/-- The original canonical coefficient restriction at literal affine-test pullbacks.
This law keeps the coefficient arbitrary before the higher-image specialization. -/
theorem affineFibreProductCohomologyRestriction_apply
    {X S : Scheme.{u}} (f : X ⟶ S) {U V : S.AffineEtale} (g : V ⟶ U)
    [HasExt.{e} (AbelianSheaf.{u, u + 1}
      (Limits.pullback ((Scheme.AffineEtale.Spec S).obj U).hom f))]
    [HasExt.{e'} (AbelianSheaf.{u, u + 1}
      (Limits.pullback ((Scheme.AffineEtale.Spec S).obj V).hom f))]
    (F : AbelianSheaf.{u, u + 1} X) (q : ℕ) :
    CoefficientRestrictionFormula.{u, e, e'}
      (W := Limits.pullback ((Scheme.AffineEtale.Spec S).obj U).hom f)
      (Z := Limits.pullback ((Scheme.AffineEtale.Spec S).obj V).hom f)
      (Limits.pullback.snd ((Scheme.AffineEtale.Spec S).obj U).hom f)
      (Limits.pullback.snd ((Scheme.AffineEtale.Spec S).obj V).hom f)
      (((siteBaseChange f).map ((Scheme.AffineEtale.Spec S).map g)).left)
      (siteBaseChange_map_snd f ((Scheme.AffineEtale.Spec S).map g)) F q
      (fibreProductCohomologyRestriction f ((Scheme.AffineEtale.Spec S).map g) F q) := by
  intro z
  exact fibreProductCohomologyRestriction_apply_canonical f
    ((Scheme.AffineEtale.Spec S).map g) F q z

/-- The complete equation for the original affine section equivalences and
an original restriction map. No value or cohomology model is replaced. -/
def AffineSectionsRestriction
    {R T : CommRingCat.{u}} (j : Spec R ⟶ S) (j' : Spec T ⟶ S)
    [Etale j] [Etale j']
    [HasExt.{e} (AbelianSheaf.{u, u + 1} (Limits.pullback j f))]
    [HasExt.{e'} (AbelianSheaf.{u, u + 1} (Limits.pullback j' f))]
    (r : Over.mk j' ⟶ Over.mk j)
    (ρ : Sheaf.H.{e} ((inverseImage (Limits.pullback.snd j f)).obj
        (additiveCoefficient X M)) q →+
      Sheaf.H.{e'} ((inverseImage (Limits.pullback.snd j' f)).obj
        (additiveCoefficient X M)) q)
    (x : (moduleSpecΓFunctor (R := R)).obj
      ((Scheme.Modules.pullback j).obj
        (((Scheme.Modules.pushforward f).rightDerived q).obj M))) : Prop :=
  AddEquiv.MapSquare
    (higherDirectImageAffineSectionsEquiv.{u, e} f j M q)
    (higherDirectImageAffineSectionsEquiv.{u, e'} f j' M q)
    (sectionsAddHom S (((Scheme.Modules.pushforward f).rightDerived q).obj M)
      (T := Over.mk j) (U := Over.mk j') r) ρ x

/-- The complete original affine value law at literal structural arrows,
before an affine-site object or morphism is substituted. -/
private theorem higherDirectImageAffineSectionsEquiv_restriction_of_squares
    {R T : CommRingCat.{u}} (j : Spec R ⟶ S) (j' : Spec T ⟶ S)
    (φ : R ⟶ T) (hj : Spec.map φ ≫ j = j')
    [Etale j] [Etale j'] [Etale (Spec.map φ)]
    (c : Limits.pullback j' f ⟶ Limits.pullback j f)
    (hc : IsPullback c (Limits.pullback.fst j' f) (Limits.pullback.fst j f) (Spec.map φ))
    (ha : c ≫ Limits.pullback.snd j f = Limits.pullback.snd j' f)
    [HasExt.{e} (AbelianSheaf.{u, u + 1} (Limits.pullback j f))]
    [HasExt.{e'} (AbelianSheaf.{u, u + 1} (Limits.pullback j' f))]
    (r : Over.mk j' ⟶ Over.mk j)
    (hr : r = Over.homMk (U := Over.mk j') (V := Over.mk j) (Spec.map φ) hj)
    (x : (moduleSpecΓFunctor (R := R)).obj
      ((Scheme.Modules.pullback j).obj
        (((Scheme.Modules.pushforward f).rightDerived q).obj M))) :
    higherDirectImageAffineSectionsEquiv.{u, e'} f j' M q
      (sectionsAddHom S (((Scheme.Modules.pushforward f).rightDerived q).obj M) r x) =
    Sheaf.H.map
      ((EtaleCohomology.pullbackTriangleIso (Limits.pullback.snd j' f)
        (Limits.pullback.snd j f) c ha).inv.app (additiveCoefficient X M)) q
      (cohomologyPullback.{u, e, e'} c
        ((inverseImage (Limits.pullback.snd j f)).obj (additiveCoefficient X M)) q
        (higherDirectImageAffineSectionsEquiv.{u, e} f j M q x)) := by
  rw [higherDirectImageAffineSectionsEquiv_apply,
    higherDirectImageAffineSectionsEquiv_apply]
  have h := affineSections_coefficient_restriction_of_squares.{u, e, e'} f M q
    (R := R) (T := T) (W := Limits.pullback j f) (Z := Limits.pullback j' f)
    j j' φ hj (Limits.pullback.snd j f) (Limits.pullback.fst j f)
    c (Limits.pullback.fst j' f) (Limits.pullback.snd j' f)
    (IsPullback.of_hasPullback j f).flip hc (IsPullback.of_hasPullback j' f).flip ha
    (injectiveResolution _) (injectiveResolution _) (injectiveResolution _)
    r hr x
  convert h using 1

private theorem higherDirectImageAffineSectionsEquiv_restriction_of_formula
    {R T : CommRingCat.{u}} (j : Spec R ⟶ S) (j' : Spec T ⟶ S)
    (φ : R ⟶ T) (hj : Spec.map φ ≫ j = j')
    [Etale j] [Etale j'] [Etale (Spec.map φ)]
    (c : Limits.pullback j' f ⟶ Limits.pullback j f)
    (hc : IsPullback c (Limits.pullback.fst j' f) (Limits.pullback.fst j f) (Spec.map φ))
    (ha : c ≫ Limits.pullback.snd j f = Limits.pullback.snd j' f)
    [HasExt.{e} (AbelianSheaf.{u, u + 1} (Limits.pullback j f))]
    [HasExt.{e'} (AbelianSheaf.{u, u + 1} (Limits.pullback j' f))]
    (r : Over.mk j' ⟶ Over.mk j)
    (hr : r = Over.homMk (U := Over.mk j') (V := Over.mk j) (Spec.map φ) hj)
    (ρ : Sheaf.H.{e} ((inverseImage (Limits.pullback.snd j f)).obj
        (additiveCoefficient X M)) q →+
      Sheaf.H.{e'} ((inverseImage (Limits.pullback.snd j' f)).obj
        (additiveCoefficient X M)) q)
    (hρ : CoefficientRestrictionFormula.{u, e, e'}
      (W := Limits.pullback j f) (Z := Limits.pullback j' f)
      (Limits.pullback.snd j f) (Limits.pullback.snd j' f) c ha
      (additiveCoefficient X M) q ρ)
    (x : (moduleSpecΓFunctor (R := R)).obj
      ((Scheme.Modules.pullback j).obj
        (((Scheme.Modules.pushforward f).rightDerived q).obj M))) :
    AffineSectionsRestriction.{u, e, e'} f M q (R := R) (T := T) j j' r ρ x := by
  unfold AffineSectionsRestriction AddEquiv.MapSquare
  have h := higherDirectImageAffineSectionsEquiv_restriction_of_squares.{u, e, e'}
    f M q (R := R) (T := T) j j' φ hj c hc ha r hr x
  have hfinal := h.trans (hρ (higherDirectImageAffineSectionsEquiv.{u, e} f j M q x)).symm
  convert hfinal using 1

/-- The full relative comparison commutes with the actual affine-site section
restriction and original fibre-product cohomology restriction. -/
theorem higherDirectImageAffineSectionsEquiv_restriction
    {U V : S.AffineEtale} (g : V ⟶ U)
    [HasExt.{e} (AbelianSheaf.{u, u + 1}
      (Limits.pullback ((Scheme.AffineEtale.Spec S).obj U).hom f))]
    [HasExt.{e'} (AbelianSheaf.{u, u + 1}
      (Limits.pullback ((Scheme.AffineEtale.Spec S).obj V).hom f))]
    (x : (moduleSpecΓFunctor (R := U.left.unop)).obj
      ((Scheme.Modules.pullback ((Scheme.AffineEtale.Spec S).obj U).hom).obj
        (((Scheme.Modules.pushforward f).rightDerived q).obj M))) :
    AffineSectionsRestriction.{u, e, e'} f M q
      (R := U.left.unop) (T := V.left.unop)
      ((Scheme.AffineEtale.Spec S).obj U).hom ((Scheme.AffineEtale.Spec S).obj V).hom
      ((Scheme.Etale.forget S).map ((Scheme.AffineEtale.Spec S).map g))
      (fibreProductCohomologyRestriction f ((Scheme.AffineEtale.Spec S).map g)
        (additiveCoefficient X M) q) x := by
  let : Etale (Spec.map g.left.unop) :=
    inferInstanceAs (Etale ((Scheme.AffineEtale.Spec S).map g).left)
  exact higherDirectImageAffineSectionsEquiv_restriction_of_formula.{u, e, e'} f M q
    (R := U.left.unop) (T := V.left.unop)
    ((Scheme.AffineEtale.Spec S).obj U).hom ((Scheme.AffineEtale.Spec S).obj V).hom g.left.unop
    (MorphismProperty.Over.w ((Scheme.AffineEtale.Spec S).map g))
    (((siteBaseChange f).map ((Scheme.AffineEtale.Spec S).map g)).left)
    (affineTestTransition_isPullback f g)
    (siteBaseChange_map_snd f ((Scheme.AffineEtale.Spec S).map g))
    ((Scheme.Etale.forget S).map ((Scheme.AffineEtale.Spec S).map g))
    (Scheme.EtaleAffineBasis.forget_spec_map g)
    (fibreProductCohomologyRestriction f ((Scheme.AffineEtale.Spec S).map g)
      (additiveCoefficient X M) q)
    (affineFibreProductCohomologyRestriction_apply f g (additiveCoefficient X M) q) x

end AlgebraicGeometry.Scheme.EtaleCohomology.QuasiCoherent
