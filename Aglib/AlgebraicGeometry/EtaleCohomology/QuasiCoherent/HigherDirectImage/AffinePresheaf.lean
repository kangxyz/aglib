/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Category.Grp.ComparisonComposite
public import Aglib.AlgebraicGeometry.EtaleCohomology.QuasiCoherent.BaseRestrictionValues
public import Aglib.AlgebraicGeometry.EtaleCohomology.QuasiCoherent.HigherDirectImage.AffineValues
public import Aglib.AlgebraicGeometry.EtaleCohomology.QuasiCoherent.HigherDirectImage.AffineNaturality

/-! # The original affine-test presheaf comparison

The component equivalences assemble by the proved geometric transition law.
The source is literal restriction of the original additive coefficient; the
target is literal restriction of the original group-resized cohomology presheaf.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite
open AlgebraicGeometry.Scheme.Cohomology

universe u w s e

namespace AlgebraicGeometry.Scheme.EtaleCohomology.QuasiCoherent

attribute [local instance] HasExt.standard hasSheafifyLarge
  moduleComparisonEnoughSmall moduleComparisonEnoughRaised
  moduleComparisonAbWRaised moduleComparisonTypeWRaised

/-- Restriction retains the original whole sheaf map before coefficients enter. -/
theorem affineRestriction_map {S : Scheme.{u}}
    (F : AbelianSheaf.{u, u + 1} S) {U V : S.AffineEtale} (g : V ⟶ U) :
    ((EtaleAffineBasis.abelianRestriction S).obj F).obj.map g.op =
      F.obj.map ((Scheme.AffineEtale.Spec S).map g).op := rfl

/-- The coefficient retains the original whole over-category map. -/
theorem additiveCoefficient_map {S : Scheme.{u}} (N : S.Modules) [N.IsQuasicoherent]
    {U V : S.Etale} (g : V ⟶ U) :
    (additiveCoefficient S N).obj.map g.op =
      (additiveSectionsPresheaf S N).map ((Scheme.Etale.forget S).map g).op := rfl

/-- Original affine coefficient restriction before a higher-image module is supplied. -/
theorem affineCoefficient_map_down
    {S : Scheme.{u}} (N : S.Modules) [N.IsQuasicoherent]
    {U V : S.AffineEtale} (g : V ⟶ U)
    (x : ULift.{u + 1} Γ((Scheme.Modules.pullback
      ((Scheme.AffineEtale.Spec S).obj U).hom).obj N, ⊤)) :
    ((((EtaleAffineBasis.abelianRestriction S).obj (additiveCoefficient S N)).obj.map
      g.op x) : ULift.{u + 1} Γ((Scheme.Modules.pullback
        ((Scheme.AffineEtale.Spec S).obj V).hom).obj N, ⊤)).down =
    sectionsAddHom S N ((Scheme.Etale.forget S).map ((Scheme.AffineEtale.Spec S).map g))
      x.down := by
  rw [affineRestriction_map, additiveCoefficient_map]
  exact additiveSectionsPresheaf_map_down N
    ((Scheme.Etale.forget S).map ((Scheme.AffineEtale.Spec S).map g)) x

/-- The original ULift equivalence at a literal test-functor object. -/
def coefficientSectionsULiftEquiv {I : Type*} [Category I] {S : Scheme.{u}}
    (P : I ⥤ Over S) (N : S.Modules) [N.IsQuasicoherent] (U : Iᵒᵖ) :
    (P.op ⋙ additiveSectionsPresheaf S N).obj U ≃+
      Γ((Scheme.Modules.pullback (P.obj U.unop).hom).obj N, ⊤) := AddEquiv.ulift

/-- The original lifted restriction evaluated before any comparison is assembled. -/
theorem coefficientSectionsULiftEquiv_map {I : Type*} [Category I] {S : Scheme.{u}}
    (P : I ⥤ Over S) (N : S.Modules) [N.IsQuasicoherent]
    {U V : Iᵒᵖ} (g : U ⟶ V)
    (x : ULift.{u + 1} Γ((Scheme.Modules.pullback (P.obj U.unop).hom).obj N, ⊤)) :
    coefficientSectionsULiftEquiv P N V ((P.op ⋙ additiveSectionsPresheaf S N).map g x) =
      sectionsAddHom S N (T := P.obj U.unop) (U := P.obj V.unop) (P.map g.unop)
        (coefficientSectionsULiftEquiv P N U x) := by
  dsimp only [coefficientSectionsULiftEquiv, Functor.comp_map, Functor.op_map,
    Functor.comp_obj, Functor.op_obj, AddEquiv.ulift, Equiv.ulift]
  exact additiveSectionsPresheaf_map_down N
    (T := P.obj U.unop) (U := P.obj V.unop) (P.map g.unop) x

/-- Assemble the entire original section-presheaf comparison over a supplied
original test functor. No presheaf is constructed on the intermediate groups. -/
def coefficientSectionsComparisonNatIso
    {I : Type*} [Category I] {S : Scheme.{u}}
    (P : I ⥤ Over S) (N : S.Modules) [N.IsQuasicoherent]
    (Q : Iᵒᵖ ⥤ AddCommGrpCat.{u + 1})
    {C : Iᵒᵖ → Type s} {D : Iᵒᵖ → Type e}
    [∀ U, AddCommGroup (C U)] [∀ U, AddCommGroup (D U)]
    (c : ∀ U : Iᵒᵖ, Γ((Scheme.Modules.pullback (P.obj U.unop).hom).obj N, ⊤) ≃+ C U)
    (t : ∀ U, D U ≃+ C U) (r : ∀ U, D U ≃+ Q.obj U)
    (cmap : ∀ {U V}, (U ⟶ V) → (C U →+ C V))
    (dmap : ∀ {U V}, (U ⟶ V) → (D U →+ D V))
    (hc : ∀ {U V : Iᵒᵖ} (g : U ⟶ V)
      (x : Γ((Scheme.Modules.pullback (P.obj U.unop).hom).obj N, ⊤)),
      c V (sectionsAddHom S N
        (T := P.obj U.unop) (U := P.obj V.unop) (P.map g.unop) x) = cmap g (c U x))
    (ht : ∀ {U V} (g : U ⟶ V) x, t V (dmap g x) = cmap g (t U x))
    (hr : ∀ {U V} (g : U ⟶ V) x, r V (dmap g x) = Q.map g (r U x)) :
    P.op ⋙ additiveSectionsPresheaf S N ≅ Q :=
  CategoryTheory.comparisonCompositeNatIso
    (P.op ⋙ additiveSectionsPresheaf S N) Q
    (coefficientSectionsULiftEquiv P N) c t r
    (fun {U V} g => sectionsAddHom S N
      (T := P.obj U.unop) (U := P.obj V.unop) (P.map g.unop)) cmap dmap
    (fun {_ _} g x => coefficientSectionsULiftEquiv_map P N g x) hc ht hr

/-- Specialize the complete original test-functor construction and source
restriction identity before substituting a concrete higher-image module. -/
def affineCoefficientComparisonNatIso
    {S : Scheme.{u}} (N : S.Modules) [N.IsQuasicoherent]
    (G : S.Etaleᵒᵖ ⥤ AddCommGrpCat.{w}) [∀ U, Small.{u + 1} (G.obj U)]
    {C : S.AffineEtaleᵒᵖ → Type s} [∀ U, AddCommGroup (C U)]
    (c : ∀ U : S.AffineEtaleᵒᵖ,
      (moduleSpecΓFunctor (R := U.unop.left.unop)).obj
        ((Scheme.Modules.pullback (X := Spec U.unop.left.unop) (Y := S)
          ((Scheme.AffineEtale.Spec S).obj U.unop).hom).obj N) ≃+ C U)
    (t : ∀ U, G.obj (op ((Scheme.AffineEtale.Spec S).obj U.unop)) ≃+ C U)
    (cmap : ∀ {U V}, (U ⟶ V) → (C U →+ C V))
    (hc : ∀ {U V : S.AffineEtaleᵒᵖ} (g : U ⟶ V)
      (x : (moduleSpecΓFunctor (R := U.unop.left.unop)).obj
        ((Scheme.Modules.pullback (X := Spec U.unop.left.unop) (Y := S)
          ((Scheme.AffineEtale.Spec S).obj U.unop).hom).obj N)),
      AddEquiv.MapSquare (c U) (c V) (sectionsAddHom S N
        (T := Over.mk (X := S) (Y := Spec U.unop.left.unop)
          ((Scheme.AffineEtale.Spec S).obj U.unop).hom)
        (U := Over.mk (X := S) (Y := Spec V.unop.left.unop)
          ((Scheme.AffineEtale.Spec S).obj V.unop).hom)
        ((Scheme.Etale.forget S).map ((Scheme.AffineEtale.Spec S).map g.unop))) (cmap g) x)
    (ht : ∀ {U V} (g : U ⟶ V) x,
      t V (G.map ((Scheme.AffineEtale.Spec S).map g.unop).op x) = cmap g (t U x)) :
    ((EtaleAffineBasis.abelianRestriction S).obj (additiveCoefficient S N)).obj ≅
      (Scheme.AffineEtale.Spec S).op ⋙ resizeAdditiveDiagram.{u + 1} G :=
  coefficientSectionsComparisonNatIso
    ((Scheme.AffineEtale.Spec S) ⋙ Scheme.Etale.forget S) N
    ((Scheme.AffineEtale.Spec S).op ⋙ resizeAdditiveDiagram.{u + 1} G)
    c t (fun _ => Shrink.addEquiv.symm) cmap
    (fun {_ _} g => (G.map ((Scheme.AffineEtale.Spec S).map g.unop).op).hom)
    (by
      intro U V g x
      have h := hc g x
      unfold AddEquiv.MapSquare at h
      dsimp only [Functor.comp_map, Functor.comp_obj]
      convert h using 1) ht
    (fun {_ _} g x => (resizeAdditiveDiagram_map_shrink_symm G
      ((Scheme.AffineEtale.Spec S).map g.unop).op x).symm)

variable {X S : Scheme.{u}} (f : X ⟶ S) [QuasiCompact f] [QuasiSeparated f]
  (M : X.Modules) [M.IsQuasicoherent] (q : ℕ)
  [HasExt.{w} (AbelianSheaf.{u, u + 1} X)]
  [∀ U : S.Etale, HasExt.{s}
    (Sheaf ((smallEtaleTopology X).over ((siteBaseChange f).obj U)) AddCommGrpCat.{u + 1})]
  [∀ U : S.Etale, HasExt.{e} (AbelianSheaf.{u, u + 1} (Limits.pullback U.hom f))]

local instance :
    (((Scheme.Modules.pushforward f).rightDerived q).obj M).IsQuasicoherent :=
  moduleHigherDirectImage_isQuasicoherent f M q

local instance (U : S.AffineEtale) : Etale ((Scheme.AffineEtale.Spec S).obj U).hom :=
  ((Scheme.AffineEtale.Spec S).obj U).prop

local instance (U : S.AffineEtale) :
    Small.{u + 1} (Sheaf.LargeCohomology.H.{w, u + 1, u, u + 1}
      (Scheme.smallEtaleTopology X) (additiveCoefficient X M) q
      ((siteBaseChange f).obj ((Scheme.AffineEtale.Spec S).obj U))) :=
  originalCohomologyPresheaf_small f (additiveCoefficient X M) q
    (op ((Scheme.AffineEtale.Spec S).obj U))

/-- The full natural isomorphism on the actual affine étale site. Its transition
law uses the original represented-cohomology restrictions, not transported new
maps on the target presheaf. -/
def higherDirectImageAffinePresheafIso :
    ((EtaleAffineBasis.abelianRestriction S).obj
      (additiveCoefficient S (((Scheme.Modules.pushforward f).rightDerived q).obj M))).obj ≅
    (Scheme.AffineEtale.Spec S).op ⋙
      smallOriginalCohomologyPresheaf f (additiveCoefficient X M) q :=
  affineCoefficientComparisonNatIso
    (((Scheme.Modules.pushforward f).rightDerived q).obj M)
    (originalCohomologyPresheaf f (additiveCoefficient X M) q)
    (fun U => higherDirectImageAffineSectionsEquiv.{u, e} f
      ((Scheme.AffineEtale.Spec S).obj U.unop).hom M q)
    (fun U => fibreProductCohomologyEquiv.{u, w, s, e} f
      ((Scheme.AffineEtale.Spec S).obj U.unop) (additiveCoefficient X M) q)
    (fun {_ _} g => fibreProductCohomologyRestriction f ((Scheme.AffineEtale.Spec S).map g.unop)
      (additiveCoefficient X M) q)
    (fun {_ _} g x => by
      have h := higherDirectImageAffineSectionsEquiv_restriction.{u, e, e} f M q g.unop x
      unfold AffineSectionsRestriction at h
      exact h)
    (by
      intro U V g x
      have h := fibreProductCohomologyEquiv_restriction f
        ((Scheme.AffineEtale.Spec S).map g.unop) (additiveCoefficient X M) q x
      exact h)


end AlgebraicGeometry.Scheme.EtaleCohomology.QuasiCoherent
