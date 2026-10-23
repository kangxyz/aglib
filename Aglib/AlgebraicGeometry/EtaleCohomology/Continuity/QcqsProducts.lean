/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Sites.EtaleAffineBasis.QcqsHypercover
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Products
public import Mathlib.CategoryTheory.ObjectProperty.FiniteProducts

/-!
# Finite products of qcqs objects in the original étale slice

These statements concern the chosen categorical products in `Over W`, not
replacement affine objects. They supply the tuple objects in finite Čech
families over a qcqs object of the original small étale site.
-/

@[expose] public noncomputable section

universe u v

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Continuity

private def etaleUnderlying (S : Scheme.{u}) : S.Etale ⥤ Scheme.{u} :=
  MorphismProperty.Over.forget
    (fun {X Y : Scheme.{u}} (f : X ⟶ Y) ↦ AlgebraicGeometry.Etale f) ⊤ S ⋙
      Over.forget S

/-- The native pullback of quasi-separated étale objects is quasi-separated. -/
theorem quasiSeparatedSpace_etale_pullback {S : Scheme.{u}} {U V W : S.Etale}
    [QuasiSeparatedSpace V.left] [QuasiSeparatedSpace W.left]
    (f : V ⟶ U) (g : W ⟶ U) :
    QuasiSeparatedSpace (pullback f g).left := by
  let : Category (MorphismProperty.Over
      (fun {X Y : Scheme.{u}} (f : X ⟶ Y) ↦ AlgebraicGeometry.Etale f) ⊤ S) :=
    inferInstanceAs (Category S.Etale)
  let F₀ : S.Etale ⥤ Over S := MorphismProperty.Over.forget
    (fun {X Y : Scheme.{u}} (f : X ⟶ Y) ↦ AlgebraicGeometry.Etale f) ⊤ S
  let : PreservesFiniteLimits F₀ :=
    MorphismProperty.Over.instPreservesFiniteLimitsTopOverForget
      (fun {X Y : Scheme.{u}} (f : X ⟶ Y) ↦ AlgebraicGeometry.Etale f) S
  let F : S.Etale ⥤ Scheme.{u} := F₀ ⋙ Over.forget S
  have : PreservesLimit (cospan f g) F := by
    dsimp only [F]
    infer_instance
  let e : (pullback f g).left ≅ pullback f.left g.left :=
    PreservesPullback.iso F f g
  have : QuasiSeparatedSpace (pullback f.left g.left : Scheme.{u}) :=
    quasiSeparatedSpace_of_quasiSeparated (pullback.fst f.left g.left)
  exact (quasiSeparatedSpace_congr e.hom.homeomorph).mpr inferInstance

/-- The qcqs property on objects of the original slice category. -/
def qcqsOver {S : Scheme.{u}} (W : S.Etale) : ObjectProperty (Over W) :=
  fun U ↦ CompactSpace U.left.left ∧ QuasiSeparatedSpace U.left.left

instance qcqsOver_closedUnderIsomorphisms {S : Scheme.{u}} (W : S.Etale) :
    (qcqsOver W).IsClosedUnderIsomorphisms where
  of_iso {X Y} e h := by
    let d : X.left.left ≅ Y.left.left :=
      ((Over.forget W) ⋙ etaleUnderlying S).mapIso e
    have : CompactSpace X.left.left := h.1
    exact ⟨d.hom.homeomorph.compactSpace,
      (quasiSeparatedSpace_congr d.hom.homeomorph).mp h.2⟩

private theorem qcqsOver_binary {S : Scheme.{u}} (W : S.Etale)
    [QuasiSeparatedSpace W.left] (U V : Over W)
    (hU : qcqsOver W U) (hV : qcqsOver W V) : qcqsOver W (U ⨯ V) := by
  have : CompactSpace U.left.left := hU.1
  have : CompactSpace V.left.left := hV.1
  have : QuasiSeparatedSpace U.left.left := hU.2
  have : QuasiSeparatedSpace V.left.left := hV.2
  have : CompactSpace (pullback U.hom V.hom).left :=
    EtaleAffineBasis.compactSpace_etale_pullback U.hom V.hom
  have : QuasiSeparatedSpace (pullback U.hom V.hom).left :=
    quasiSeparatedSpace_etale_pullback U.hom V.hom
  let e : (U ⨯ V).left.left ≅ (pullback U.hom V.hom).left :=
    (etaleUnderlying S).mapIso (Over.prodLeftIsoPullback U V)
  exact ⟨e.hom.homeomorph.symm.compactSpace,
    (quasiSeparatedSpace_congr e.hom.homeomorph).mpr inferInstance⟩

instance qcqsOver_closedUnderBinaryProducts {S : Scheme.{u}} (W : S.Etale)
    [QuasiSeparatedSpace W.left] : (qcqsOver W).IsClosedUnderBinaryProducts where
  limitsOfShape_le := by
    rintro X ⟨p⟩
    refine (qcqsOver W).prop_of_iso ?_
      (qcqsOver_binary W _ _ (p.prop_diag_obj (.mk .left))
        (p.prop_diag_obj (.mk .right)))
    exact IsLimit.conePointUniqueUpToIso (prodIsProd _ _)
      ((IsLimit.postcomposeHomEquiv (diagramIsoPair p.diag) _).2 p.isLimit)

instance qcqsOver_closedUnderEmptyProducts {S : Scheme.{u}} (W : S.Etale)
    [CompactSpace W.left] [QuasiSeparatedSpace W.left] :
    (qcqsOver W).IsClosedUnderLimitsOfShape (Discrete.{0} PEmpty) where
  limitsOfShape_le := by
    rintro X ⟨p⟩
    have hX : IsTerminal X :=
      (IsLimit.equivOfNatIsoOfIso p.diag.uniqueFromEmpty _ _
        (by exact Cone.ext (Iso.refl _) (by rintro ⟨⟨⟩⟩))).1 p.isLimit
    exact (qcqsOver W).prop_of_iso (Over.mkIdTerminal.uniqueUpToIso hX)
      (show qcqsOver W (Over.mk (𝟙 W)) from
        ⟨inferInstanceAs (CompactSpace W.left), inferInstanceAs (QuasiSeparatedSpace W.left)⟩)

instance qcqsOver_closedUnderFiniteProducts {S : Scheme.{u}} (W : S.Etale)
    [CompactSpace W.left] [QuasiSeparatedSpace W.left] :
    (qcqsOver W).IsClosedUnderFiniteProducts := .mk'

/-- Arbitrary finite native products of qcqs étale objects over a qcqs target
are qcqs, including the empty product. -/
theorem qcqs_product {S : Scheme.{u}} (W : S.Etale)
    (hW : CompactSpace W.left ∧ QuasiSeparatedSpace W.left)
    {ι : Type v} [Finite ι] (U : ι → Over W)
    (hU : ∀ i, CompactSpace (U i).left.left ∧ QuasiSeparatedSpace (U i).left.left) :
    CompactSpace (∏ᶜ U).left.left ∧ QuasiSeparatedSpace (∏ᶜ U).left.left := by
  have : CompactSpace W.left := hW.1
  have : QuasiSeparatedSpace W.left := hW.2
  exact (qcqsOver W).prop_product hU

end AlgebraicGeometry.Scheme.EtaleCohomology.Continuity
