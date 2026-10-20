/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Coherent.Pushforward.Finite.Charts
public import Aglib.RingTheory.Polynomial.GraphRelations
public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
public import Aglib.AlgebraicGeometry.FunctionField.Basic

/-!
# Polynomial charts of actual schematic images

Source: `R5Lab.Aglib.AlgebraicGeometry.SchemeTheoreticImage.PolynomialCharts`.
R5 packet revision: `f8a3314ddecffcada2ec721d26d56a937bed9690`.
Source SHA-256: `cbc21d4f8fb227222db90a750b1d3ccc3f00ee861bfa703cc84c1e90a9b842c2`.
Actual objects, maps, universes and hypotheses are retained.
Native declaration ownership replaces the source application namespaces.
-/

@[expose] public section

universe u

/- Component: GraphChartDimension; declaration bodies preserved. -/
noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Polynomial TopologicalSpace
namespace AlgebraicGeometry.Scheme

open Modules.Coherent.Pushforward.Finite
variable {S Z : Scheme.{u}} (g : S ⟶ Z) [QuasiCompact g]
    (A : Type u) [CommRing A] [IsDomain A] [IsNoetherianRing A]
    (j : Spec (.of A[X]) ⟶ Z) [IsOpenImmersion j]

omit [QuasiCompact g]
    [IsDomain A]
    [IsNoetherianRing A] in
theorem graphImage_chartSectionRingMap_surjective
    [QuasiCompact g]
    [IsDomain A]
    [IsNoetherianRing A]
    :
    Function.Surjective (chartSectionRingMap g.imageι (.of A[X]) j) := by
  let e := (Scheme.ΓSpecIso (.of A[X])).symm ≪≫ (j.appIso ⊤).symm
  have hU : IsAffineOpen (j ''ᵁ ⊤) := by
    simpa only [Scheme.Hom.image_top_eq_opensRange] using isAffineOpen_opensRange j
  exact (g.imageι.app_surjective _ hU).comp e.commRingCatIsoToRingEquiv.surjective

omit [IsDomain A]
    [IsNoetherianRing A] in
/-- A polynomial relation in the actual graph chart map descends to the
actual scheme-image chart sections. -/
theorem graphImage_chartSectionRingMap_eq_zero
    [IsDomain A]
    [IsNoetherianRing A]
    {r : A[X]}
    (hr : chartSectionRingMap g (.of A[X]) j r = 0) :
    chartSectionRingMap g.imageι (.of A[X]) j r = 0 := by
  let U : Z.affineOpens := ⟨j ''ᵁ ⊤, by
    change IsAffineOpen (j ''ᵁ ⊤)
    simpa only [Scheme.Hom.image_top_eq_opensRange] using isAffineOpen_opensRange j⟩
  let e := (Scheme.ΓSpecIso (.of A[X])).symm ≪≫ (j.appIso ⊤).symm
  have hm : e.hom r ∈ g.ker.ideal U := by
    rw [g.ker_apply U]
    exact hr
  change ((e.hom ≫ g.ker.subschemeι.app U.1).hom r) = 0
  rw [g.ker.subschemeι_app U]
  change (g.ker.subschemeObjIso U).inv ((Ideal.Quotient.mk (g.ker.ideal U)) (e.hom r)) = 0
  rw [Ideal.Quotient.eq_zero_iff_mem.mpr hm, map_zero]

theorem graphImage_chart_ringKrullDim_le_one
    (hA : ringKrullDim A ≤ 1) {r : A[X]} (hr : r ≠ 0)
    (hg : chartSectionRingMap g (.of A[X]) j r = 0) :
    ringKrullDim Γ(g.image, g.imageι ⁻¹ᵁ (j ''ᵁ ⊤)) ≤ 1 :=
  graphChart_ringKrullDim_le_one (chartSectionRingMap g.imageι (.of A[X]) j)
    (graphImage_chartSectionRingMap_surjective g A j) hA hr
    (graphImage_chartSectionRingMap_eq_zero g A j hg)
end AlgebraicGeometry.Scheme
end

/- Component: GraphRelation; declaration bodies preserved. -/
noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite Polynomial
namespace AlgebraicGeometry.Scheme

open Modules.Coherent.Pushforward.Finite

lemma fromSpec_composite_appLE {X : Scheme.{u}} {V : X.Opens} (hV : IsAffineOpen V)
    (R : CommRingCat.{u}) (c : Γ(X, V) ⟶ R)
    (h : ⊤ ≤ (Spec.map c ≫ hV.fromSpec) ⁻¹ᵁ V) :
    (Spec.map c ≫ hV.fromSpec).appLE V ⊤ h = c ≫ (Scheme.ΓSpecIso R).inv := by
  rw [Scheme.Hom.comp_appLE, hV.fromSpec_app_self, Category.assoc,
    Scheme.Hom.map_appLE]
  simp [Scheme.Hom.appLE, ← Scheme.ΓSpecIso_inv_naturality]

lemma hom_appLE_congr {X Y : Scheme.{u}} {f g : X ⟶ Y} (h : f = g)
    (U : Y.Opens) (V : X.Opens) (hf : V ≤ f ⁻¹ᵁ U) (hg : V ≤ g ⁻¹ᵁ U) :
    f.appLE U V hf = g.appLE U V hg := by
  subst g
  rfl

lemma chartSectionRingMap_coeff {X S Z : Scheme.{u}} {V : X.Opens}
    (hV : IsAffineOpen V) (i : S ⟶ X) (g : S ⟶ Z) (p : Z ⟶ X)
    (hgp : g ≫ p = i) (R : CommRingCat.{u})
    (j : Spec R ⟶ Z) [IsOpenImmersion j] (c : Γ(X, V) ⟶ R)
    (hjp : j ≫ p = Spec.map c ≫ hV.fromSpec)
    (hUV : j ''ᵁ ⊤ ≤ p ⁻¹ᵁ V)
    (hWV : g ⁻¹ᵁ (j ''ᵁ ⊤) ≤ i ⁻¹ᵁ V) :
    (chartSectionRingMap g R j).comp c.hom =
      (i.appLE V (g ⁻¹ᵁ (j ''ᵁ ⊤)) hWV).hom := by
  apply CommRingCat.hom_ext_iff.mp
  change c ≫ (Scheme.ΓSpecIso R).inv ≫ (j.appIso ⊤).inv ≫ g.app (j ''ᵁ ⊤) = _
  have H : c ≫ (Scheme.ΓSpecIso R).inv =
      p.appLE V (j ''ᵁ ⊤) hUV ≫ (j.appIso ⊤).hom := by
    rw [Scheme.Hom.appIso_hom', Scheme.Hom.appLE_comp_appLE]
    have ht : ⊤ ≤ (Spec.map c ≫ hV.fromSpec) ⁻¹ᵁ V := by simp
    exact (fromSpec_composite_appLE hV R c ht).symm.trans
      (hom_appLE_congr hjp.symm _ _ _ _)
  rw [← Category.assoc c, H, Category.assoc, Iso.hom_inv_id_assoc]
  rw [Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_comp_appLE]
  exact hom_appLE_congr hgp _ _ _ _
end AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.Scheme

open Modules.Coherent.Pushforward.Finite

lemma chartSectionRingMap_coeff_germ {X S Z : Scheme.{u}} [IsIntegral X]
    {V : X.Opens} (hV : IsAffineOpen V) [Nonempty V]
    (i : S ⟶ X) [IsOpenImmersion i] (g : S ⟶ Z) (p : Z ⟶ X)
    (hgp : g ≫ p = i) (R : CommRingCat.{u})
    (j : Spec R ⟶ Z) [IsOpenImmersion j] (c : Γ(X, V) ⟶ R)
    (hjp : j ≫ p = Spec.map c ≫ hV.fromSpec)
    (hUV : j ''ᵁ ⊤ ≤ p ⁻¹ᵁ V)
    (hWV : g ⁻¹ᵁ (j ''ᵁ ⊤) ≤ i ⁻¹ᵁ V)
    [Nonempty (i ''ᵁ (g ⁻¹ᵁ (j ''ᵁ ⊤)))] :
    c ≫ CommRingCat.ofHom (chartSectionRingMap g R j) ≫
      (i.appIso (g ⁻¹ᵁ (j ''ᵁ ⊤))).inv ≫
        X.germToFunctionField (i ''ᵁ (g ⁻¹ᵁ (j ''ᵁ ⊤))) = X.germToFunctionField V := by
  have hc : c ≫ CommRingCat.ofHom (chartSectionRingMap g R j) =
      i.appLE V (g ⁻¹ᵁ (j ''ᵁ ⊤)) hWV := by
    apply CommRingCat.hom_ext
    exact chartSectionRingMap_coeff hV i g p hgp R j c hjp hUV hWV
  rw [← Category.assoc c, hc, Scheme.Hom.appLE_appIso_inv_assoc]
  exact X.presheaf.germ_res _ _ _

/-- Every actual polynomial chart met by an open graph has a nonzero relation. -/
theorem graphChart_exists_nonzero_relation {X S Z : Scheme.{u}} [IsIntegral X]
    (V : X.Opens) (hV : IsAffineOpen V) [Nonempty V]
    (i : S ⟶ X) [IsOpenImmersion i] (g : S ⟶ Z) (p : Z ⟶ X)
    (hgp : g ≫ p = i)
    (j : Spec (.of Γ(X, V)[X]) ⟶ Z) [IsOpenImmersion j]
    (hjp : j ≫ p = Spec.map (CommRingCat.ofHom (C : Γ(X, V) →+* Γ(X, V)[X])) ≫ hV.fromSpec) :
    ∃ r : Γ(X, V)[X], r ≠ 0 ∧ chartSectionRingMap g (.of Γ(X, V)[X]) j r = 0 := by
  let W := g ⁻¹ᵁ (j ''ᵁ ⊤)
  let f := chartSectionRingMap g (.of Γ(X, V)[X]) j
  by_cases hW : Nonempty W
  · let : Nonempty W := hW
    have hH : Nonempty (i ''ᵁ W) := by
      obtain ⟨w⟩ := hW
      exact ⟨⟨i w.val, ⟨w.val, w.2, rfl⟩⟩⟩
    let : Nonempty (i ''ᵁ W) := hH
    have hUV : j ''ᵁ ⊤ ≤ p ⁻¹ᵁ V := by
      rintro z ⟨q, hq, rfl⟩
      change p (j q) ∈ V
      have he := congrArg (fun k : Spec (.of Γ(X, V)[X]) ⟶ X => k q) hjp
      change p (j q) = hV.fromSpec ((Spec.map (CommRingCat.ofHom C)) q) at he
      rw [he]
      exact hV.range_fromSpec.le ⟨_, rfl⟩
    have hWV : W ≤ i ⁻¹ᵁ V := by
      intro s hs
      have he := congrArg (fun k : S ⟶ X => k s) hgp
      change p (g s) = i s at he
      change i s ∈ V
      rw [← he]
      exact hUV hs
    let E : Γ(S, W) →+* X.functionField :=
      ((i.appIso W).inv ≫ X.germToFunctionField (i ''ᵁ W)).hom
    have hE : Function.Injective E :=
      (X.germToFunctionField_injective (i ''ᵁ W)).comp
        (i.appIso W).symm.commRingCatIsoToRingEquiv.injective
    have hc (a : Γ(X, V)) : E (f (C a)) = algebraMap Γ(X, V) X.functionField a := by
      exact congrArg (fun k : Γ(X, V) ⟶ X.functionField => k a)
        (chartSectionRingMap_coeff_germ hV i g p hgp (.of Γ(X, V)[X]) j
          (CommRingCat.ofHom C) hjp hUV hWV)
    let : IsFractionRing Γ(X, V) X.functionField :=
      functionField_isFractionRing_of_isAffineOpen X V hV
    exact exists_polynomial_relation_of_fractionRing f E hE hc
  · have hbot : W = ⊥ := by
      apply le_bot_iff.mp
      intro s hs
      exact (hW ⟨⟨s, hs⟩⟩).elim
    have : Subsingleton Γ(S, W) := by rw [hbot]; infer_instance
    exact ⟨1, one_ne_zero, Subsingleton.elim _ _⟩

end AlgebraicGeometry.Scheme
end
