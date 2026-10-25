/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.AlgebraicGeometry.Sites.SmallAffineZariski
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.Tactic.DepRewrite

/-! # Recover an affine morphism from its original relative section algebra

The original inverse-image section rings localize on principal affine opens.
Their native relative gluing recovers the original source through the original
canonical affine section and pullback/restriction isomorphisms. The full
structural triangle is retained, with no Noetherian or integral assumption.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Constructible.FiniteCogenerators.Global

universe u

open AffineZariskiSite

variable {Y X : Scheme.{u}} (f : Y ⟶ X)

/-- The original rings on inverse images of base opens. -/
def relativeSectionDiagram : X.Opensᵒᵖ ⥤ CommRingCat.{u} where
  obj U := Γ(Y, f ⁻¹ᵁ U.unop)
  map i := Y.presheaf.map (homOfLE (f.preimage_mono i.unop.le)).op
  map_id U := by simp
  map_comp i j :=
    (congrArg Y.presheaf.map (Subsingleton.elim _ _)).trans
      (Y.presheaf.map_comp (homOfLE (f.preimage_mono i.unop.le)).op
        (homOfLE (f.preimage_mono j.unop.le)).op)

/-- The original scheme structural maps into those original rings. -/
def relativeSectionMap : X.presheaf ⟶ relativeSectionDiagram f where
  app U := f.app U.unop
  naturality {_U _V} i := f.naturality i

/-- Actual affine direct-image structure algebras retain principal localization. -/
theorem relativeSectionMap_coequifibered [IsAffineHom f] :
    ((toOpensFunctor X).op.whiskerLeft (relativeSectionMap f)).Coequifibered := by
  refine coequifibered_iff_forall_isLocalizationAway.mpr fun U r => ?_
  let inst : Algebra Γ(Y, f ⁻¹ᵁ U.1) Γ(Y, f ⁻¹ᵁ X.basicOpen r) :=
    (Y.presheaf.map (homOfLE (f.preimage_mono (X.basicOpen_le r))).op).hom.toAlgebra
  change IsLocalization.Away (f.app U.1 r) Γ(Y, f ⁻¹ᵁ X.basicOpen r)
  dsimp +instances [inst]
  rw! (castMode := .all) [f.preimage_basicOpen r]
  exact (U.2.preimage f).isLocalization_basicOpen _

/-- The native relative gluing of the actual affine direct-image algebra. -/
def relativeAffineData [IsAffineHom f] :
    (directedCover X).RelativeGluingData :=
  relativeGluingData (relativeSectionMap_coequifibered f)

instance [IsAffineHom f] :
    ((relativeAffineData f).functor ⋙ Scheme.forget).IsLocallyDirected :=
  Cover.RelativeGluingData.instIsLocallyDirectedI₀CompFunctorForgetOfIsThin ..

/-- The original locally directed preimage open cover. -/
abbrev relativePreimageCover : Y.OpenCover := (directedCover X).pullback₁ f

/-- The original affine-section and original pullback/restriction isomorphisms. -/
def relativeChartIso [IsAffineHom f] (U : X.AffineZariskiSite) :
    Spec Γ(Y, f ⁻¹ᵁ U.1) ≅ (relativePreimageCover f).X U :=
  (U.2.preimage f).isoSpec.symm ≪≫ (pullbackRestrictIsoRestrict f U.1).symm

/-- The component comparison retains exactly the canonical map into Y. -/
@[reassoc]
theorem relativeChartIso_over [IsAffineHom f] (U : X.AffineZariskiSite) :
    (relativeChartIso f U).hom ≫ (relativePreimageCover f).f U =
      (U.2.preimage f).fromSpec := by
  change ((U.2.preimage f).isoSpec.inv ≫ (pullbackRestrictIsoRestrict f U.1).inv) ≫
    pullback.fst f U.1.ι = _
  rw [Category.assoc, pullbackRestrictIsoRestrict_inv_fst]
  exact IsAffineOpen.isoSpec_inv_ι _

/-- Keep the actual affine-site index and the full original projection
equation fixed before assembling the natural isomorphism. -/
theorem relativeChartIso_naturality [IsAffineHom f] {U V : X.AffineZariskiSite}
    (i : U ⟶ V) :
    (relativeAffineData f).functor.map i ≫ (relativeChartIso f V).hom =
      (relativeChartIso f U).hom ≫ (relativePreimageCover f).trans i := by
  have : IsOpenImmersion ((relativePreimageCover f).f V) := by
    change IsOpenImmersion (pullback.fst f V.1.ι)
    infer_instance
  apply (cancel_mono ((relativePreimageCover f).f V)).mp
  let a : Spec Γ(Y, f ⁻¹ᵁ U.1) ⟶ Spec Γ(Y, f ⁻¹ᵁ V.1) :=
    (relativeAffineData f).functor.map i
  have hmap : a ≫ (V.2.preimage f).fromSpec = (U.2.preimage f).fromSpec :=
    (V.2.preimage f).map_fromSpec (U.2.preimage f)
      (homOfLE (f.preimage_mono ((toOpensFunctor X).map i).le)).op
  have hleft : (a ≫ (relativeChartIso f V).hom) ≫ (relativePreimageCover f).f V =
      (U.2.preimage f).fromSpec :=
    (Category.assoc a (relativeChartIso f V).hom ((relativePreimageCover f).f V)).trans
      ((congrArg (fun k => a ≫ k) (relativeChartIso_over f V)).trans hmap)
  have hright : ((relativeChartIso f U).hom ≫ (relativePreimageCover f).trans i) ≫
      (relativePreimageCover f).f V = (U.2.preimage f).fromSpec :=
    (Category.assoc (relativeChartIso f U).hom ((relativePreimageCover f).trans i)
      ((relativePreimageCover f).f V)).trans
        ((congrArg (fun k => (relativeChartIso f U).hom ≫ k)
          ((relativePreimageCover f).trans_map i)).trans (relativeChartIso_over f U))
  exact hleft.trans hright.symm

/-- The whole chart diagram agrees through the original component isomorphisms. -/
def relativeAffineDiagramIsoCover [IsAffineHom f] :
    (relativeAffineData f).functor ≅ (relativePreimageCover f).functorOfLocallyDirected :=
  NatIso.ofComponents (relativeChartIso f) (fun i => relativeChartIso_naturality f i)

/-- The original cocone from all affine inverse-image charts to Y. -/
def relativeSectionCocone [IsAffineHom f] : Cocone (relativeAffineData f).functor where
  pt := Y
  ι := (relativeAffineDiagramIsoCover f).hom ≫
    (relativePreimageCover f).functorOfLocallyDirectedHomBase

/-- Recover Y from the native relative affine gluing. -/
def relativeToSource [IsAffineHom f] : (relativeAffineData f).glued ⟶ Y :=
  colimit.desc _ (relativeSectionCocone f)

/-- The inverse cocone on the actual locally directed preimage cover. -/
def relativeSourceCocone [IsAffineHom f] :
    Cocone (relativePreimageCover f).functorOfLocallyDirected where
  pt := (relativeAffineData f).glued
  ι := (relativeAffineDiagramIsoCover f).inv ≫ (colimit.cocone _).ι

/-- The original open-cover gluing in the other direction. -/
def sourceToRelative [IsAffineHom f] : Y ⟶ (relativeAffineData f).glued :=
  (relativePreimageCover f).isColimitCoconeOfLocallyDirected.desc (relativeSourceCocone f)

@[reassoc]
theorem relativeCover_toSource [IsAffineHom f] (U : X.AffineZariskiSite) :
    (relativeAffineData f).cover.f U ≫ relativeToSource f =
      (U.2.preimage f).fromSpec := by
  change colimit.ι _ U ≫ colimit.desc _ (relativeSectionCocone f) = _
  rw [colimit.ι_desc]
  exact relativeChartIso_over f U

@[reassoc]
theorem preimageCover_toRelative [IsAffineHom f] (U : X.AffineZariskiSite) :
    (relativePreimageCover f).f U ≫ sourceToRelative f =
      (relativeChartIso f U).inv ≫ (relativeAffineData f).cover.f U :=
  (relativePreimageCover f).isColimitCoconeOfLocallyDirected.fac (relativeSourceCocone f) U

private theorem isoCoordinates_roundtrip {C : Type*} [Category* C] {A B P Q : C}
    (e : A ≅ B) (a : A ⟶ P) (b : B ⟶ Q) (p : P ⟶ Q) (q : Q ⟶ P)
    (hp : a ≫ p = e.hom ≫ b) (hq : b ≫ q = e.inv ≫ a) :
    a ≫ (p ≫ q) = a ∧ b ≫ (q ≫ p) = b := by
  constructor
  · exact (Category.assoc a p q).symm.trans
      ((congrArg (fun k => k ≫ q) hp).trans
        ((Category.assoc e.hom b q).trans
          ((congrArg (fun k => e.hom ≫ k) hq).trans (by simp))))
  · exact (Category.assoc b q p).symm.trans
      ((congrArg (fun k => k ≫ p) hq).trans
        ((Category.assoc e.inv a p).trans
          ((congrArg (fun k => e.inv ≫ k) hp).trans (by simp))))

/-- The actual relative affine algebra gluing recovers its original source. -/
def relativeSourceIso [IsAffineHom f] : (relativeAffineData f).glued ≅ Y where
  hom := relativeToSource f
  inv := sourceToRelative f
  hom_inv_id := by
    apply (relativeAffineData f).cover.hom_ext
    intro U
    have h := isoCoordinates_roundtrip (relativeChartIso f U)
      ((relativeAffineData f).cover.f U) ((relativePreimageCover f).f U)
      (relativeToSource f) (sourceToRelative f)
      ((relativeCover_toSource f U).trans (relativeChartIso_over f U).symm)
      (preimageCover_toRelative f U)
    exact h.1.trans (Category.comp_id _).symm
  inv_hom_id := by
    apply (relativePreimageCover f).hom_ext
    intro U
    have h := isoCoordinates_roundtrip (relativeChartIso f U)
      ((relativeAffineData f).cover.f U) ((relativePreimageCover f).f U)
      (relativeToSource f) (sourceToRelative f)
      ((relativeCover_toSource f U).trans (relativeChartIso_over f U).symm)
      (preimageCover_toRelative f U)
    exact h.2.trans (Category.comp_id _).symm

/-- The relative gluing chart retains the original structural map. -/
@[reassoc]
theorem relativeCover_toBase [IsAffineHom f] (U : X.AffineZariskiSite) :
    (relativeAffineData f).cover.f U ≫ (relativeAffineData f).toBase =
      Spec.map (f.app U.1) ≫ U.2.fromSpec := by
  apply (Cover.RelativeGluingData.ι_toBase (relativeAffineData f) U).trans
  change (Spec.map (f.app U.1) ≫ U.2.isoSpec.inv) ≫ U.1.ι =
    Spec.map (f.app U.1) ≫ (U.2.isoSpec.inv ≫ U.1.ι)
  exact Category.assoc _ _ _

/-- The source isomorphism preserves the original full structural triangle. -/
@[reassoc]
theorem relativeSourceIso_hom_over [IsAffineHom f] :
    (relativeSourceIso f).hom ≫ f = (relativeAffineData f).toBase := by
  apply (relativeAffineData f).cover.hom_ext
  intro U
  have h₁ : (relativeAffineData f).cover.f U ≫ ((relativeSourceIso f).hom ≫ f) =
      (U.2.preimage f).fromSpec ≫ f :=
    (Category.assoc ((relativeAffineData f).cover.f U) (relativeSourceIso f).hom f).symm.trans
      (congrArg (fun k => k ≫ f) (relativeCover_toSource f U))
  have h₂ : (U.2.preimage f).fromSpec ≫ f = Spec.map (f.app U.1) ≫ U.2.fromSpec := by
    simpa only [Scheme.Hom.app_eq_appLE] using
      (IsAffineOpen.SpecMap_appLE_fromSpec f U.2 (U.2.preimage f) le_rfl).symm
  exact h₁.trans (h₂.trans (relativeCover_toBase f U).symm)

end AlgebraicGeometry.Scheme.EtaleCohomology.Constructible.FiniteCogenerators.Global
