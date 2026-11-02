/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Picard.FrameTensor
public import Aglib.AlgebraicGeometry.Picard.PowerBaseChange
public import Aglib.AlgebraicGeometry.EtaleCohomology.H1.TorsorClassification
public import Aglib.AlgebraicGeometry.EtaleCohomology.Pullback

/-!
# Ordinary Picard classes and geometric pullback

The comparison uses the original tensor Picard group and the closed descent
and torsor classification suppliers. Its pullback is the actual unit map on
functions, not an asserted inverse-image isomorphism for the multiplicative sheaf.
-/

@[expose] public section
noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme.Modules.Invertible
open AlgebraicGeometry.Scheme.Modules.Invertible.EtaleDescent
open AlgebraicGeometry.Scheme.Modules.Invertible.FrameTorsor
open AlgebraicGeometry.Scheme.Modules.Invertible.FrameTensor
open AlgebraicGeometry.Scheme.Modules.Invertible.PowerBaseChange
open AlgebraicGeometry.Scheme.Modules.Invertible.TrivializedPowerTorsor
open GroupCohomology.Kummer.Coefficients GroupCohomology.Kummer.CoefficientBaseChange

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Picard

universe u w w'

variable {X S : Scheme.{u}}

/-- Pull a genuine frame back over the original small-etale base-change square. -/
def frameSectionPullback (f : S ⟶ X) (L : LineBundle X) (U : X.Etaleᵒᵖ)
    (s : (frameSheaf etaleLineBundleDescent X L).obj.obj U) :
    (frameSheaf etaleLineBundleDescent S (pullbackLineBundle f L)).obj.obj
      ((siteBaseChange f).op.obj U) :=
  (frameSectionsEquiv etaleLineBundleDescent S (pullbackLineBundle f L)
    ((siteBaseChange f).op.obj U)).symm
      (pullbackFrame f L U.unop.hom (Limits.pullback.snd U.unop.hom f)
        (Limits.pullback.fst U.unop.hom f) Limits.pullback.condition
        (frameSectionsEquiv etaleLineBundleDescent X L U s))

/-- The literal frame pullback commutes with restrictions. -/
theorem frameSectionPullback_naturality (f : S ⟶ X) (L : LineBundle X)
    {U V : X.Etaleᵒᵖ} (a : U ⟶ V)
    (s : (frameSheaf etaleLineBundleDescent X L).obj.obj U) :
    (frameSheaf etaleLineBundleDescent S (pullbackLineBundle f L)).obj.map
        ((siteBaseChange f).op.map a) (frameSectionPullback f L U s) =
      frameSectionPullback f L V
        ((frameSheaf etaleLineBundleDescent X L).obj.map a s) := by
  apply (frameSectionsEquiv etaleLineBundleDescent S (pullbackLineBundle f L)
    ((siteBaseChange f).op.obj V)).injective
  simp only [FrameTensor.frameSections_restriction, frameSectionPullback,
    Equiv.apply_symm_apply]
  change nativePullFrame (pullbackLineBundle f L)
    (Limits.pullback.snd U.unop.hom f) (Limits.pullback.snd V.unop.hom f)
    ((siteBaseChange f).map a.unop).left ((siteBaseChange f).map a.unop).w
      (pullbackFrame f L U.unop.hom (Limits.pullback.snd U.unop.hom f)
        (Limits.pullback.fst U.unop.hom f) Limits.pullback.condition
        (frameSectionsEquiv etaleLineBundleDescent X L U s)) =
    pullbackFrame f L V.unop.hom (Limits.pullback.snd V.unop.hom f)
      (Limits.pullback.fst V.unop.hom f) Limits.pullback.condition
      (nativePullFrame L U.unop.hom V.unop.hom a.unop.left a.unop.w
        (frameSectionsEquiv etaleLineBundleDescent X L U s))
  rw [pullbackFrame_restriction]
  unfold pullbackFrame
  rw [nativePullFrame_comp]
  have hk : ((siteBaseChange f).map a.unop).left ≫ Limits.pullback.fst U.unop.hom f =
      Limits.pullback.fst V.unop.hom f ≫ a.unop.left := Limits.pullback.lift_fst _ _ _
  congr 1
  congr 1

private theorem pullbackFrame_scalar_of_eq {X S U V : Scheme.{u}}
    (f : S ⟶ X) (L : LineBundle X) (p : U ⟶ X) (q : V ⟶ S)
    (g : V ⟶ U) (w : g ≫ p = q ≫ f)
    (φ : (Scheme.Modules.pullback p).obj L.val ≅ SheafOfModules.unit U.ringCatSheaf)
    (a : Γ(U, ⊤)ˣ) (b : Γ(V, ⊤)ˣ)
    (hb : b = Units.map g.appTop.hom.toMonoidHom a) :
    pullbackFrame f L p q g w (φ ≪≫ ScalarAutomorphisms.scalarIso U _ a) =
      pullbackFrame f L p q g w φ ≪≫ ScalarAutomorphisms.scalarIso V _ b := by
  rw [pullbackFrame_scalar, hb]

/-- Positive scalar action pulls back along the actual function-unit map. -/
theorem frameSectionPullback_equivariant (f : S ⟶ X) (L : LineBundle X)
    (U : X.Etaleᵒᵖ) (a : (gm X).obj.obj U)
    (s : (frameSheaf etaleLineBundleDescent X L).obj.obj U) :
    frameSectionPullback f L U (frameAction etaleLineBundleDescent X L U a s) =
      frameAction etaleLineBundleDescent S (pullbackLineBundle f L)
        ((siteBaseChange f).op.obj U) ((gmUnit f).hom.app U a)
        (frameSectionPullback f L U s) := by
  apply (frameSectionsEquiv etaleLineBundleDescent S (pullbackLineBundle f L)
    ((siteBaseChange f).op.obj U)).injective
  simp only [frameSectionPullback, Equiv.apply_symm_apply, frameAction_sections]
  exact pullbackFrame_scalar_of_eq f L U.unop.hom
    (Limits.pullback.snd U.unop.hom f) (Limits.pullback.fst U.unop.hom f)
    Limits.pullback.condition (frameSectionsEquiv etaleLineBundleDescent X L U s)
    (unitsSections X U a).toMul
    (unitsSections S ((siteBaseChange f).op.obj U) ((gmUnit f).hom.app U a)).toMul
    (gmUnit_sections f U a)

/-- The ordinary frame torsors form an adjoint morphism over the actual Gm unit. -/
def frameAdjointHom (f : S ⟶ X) (L : LineBundle X) :
    Torsor.AdjointHom f (gmUnit f) (frameTorsor etaleLineBundleDescent X L)
      (frameTorsor etaleLineBundleDescent S (pullbackLineBundle f L)) where
  map := ⟨{ app U := ↾(frameSectionPullback f L U)
            naturality {_ _} a := by
              ext s
              exact (frameSectionPullback_naturality f L a s).symm }⟩
  equivariant := frameSectionPullback_equivariant f L

variable [HasExt.{w} (AbelianSheaf.{u, u + 1} X)]

/-- The existing Picard equivalence, with both original geometric suppliers closed. -/
def picardCohomologyEquiv (X : Scheme.{u})
    [HasExt.{w} (AbelianSheaf.{u, u + 1} X)] :
    PicardGroup X ≃+ Sheaf.H.{w} (gm X) 1 :=
  picardH1Equiv.{u, w} X

variable [HasExt.{w'} (AbelianSheaf.{u, u + 1} S)]

/-- Original cohomological pullback followed by the actual adjoint function-unit map. -/
def gmCohomologyPullback (f : S ⟶ X) (q : ℕ) :
    Sheaf.H.{w} (gm X) q →+ Sheaf.H.{w'} (gm S) q :=
  (Sheaf.H.map (torsorAdjunctionCoefficient f (q := gmUnit f)) q).comp
    (cohomologyPullback f (gm X) q)

/-- The exact geometric square for ordinary Picard classes and original H1. -/
theorem picardCohomologyEquiv_pullback (f : S ⟶ X) (c : PicardGroup X) :
    gmCohomologyPullback f 1 (picardCohomologyEquiv X c) =
      picardCohomologyEquiv S (pullbackClass f c) := by
  induction c using Quotient.inductionOn with
  | h L => exact torsorExtClass_adjunction f (frameAdjointHom f L)

end AlgebraicGeometry.Scheme.EtaleCohomology.Picard
