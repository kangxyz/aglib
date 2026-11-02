/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Category.Ring.Descent.FinitePresentation.Models
public import Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic
public import Mathlib.Algebra.Polynomial.Lifts
public import Mathlib.RingTheory.IntegralClosure.IsIntegral.Basic

/-! # Integrality at an actual filtered stage

For paired filtered ring diagrams, integrality of a fixed represented element
is witnessed by a monic polynomial at a later stage. Both the original element
and the original colimit map are retained. No injectivity or flatness of the
transition maps is required.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Polynomial

universe u

namespace CommRingCat

variable {I : Type u} [Category.{u} I] [IsFiltered I]
  (F G : I ⥤ CommRingCat.{u}) (η : F ⟶ G)
  (cF : Cocone F) (cG : Cocone G) (hF : IsColimit cF) (hG : IsColimit cG)
  (φ : cF.pt ⟶ cG.pt)
  (hφ : ∀ i, cF.ι.app i ≫ φ = η.app i ≫ cG.ι.app i)

include hF hG hφ

/-- A fixed element is integral at the limit exactly when its original image
at some successor is a root of an actual monic stage polynomial. -/
theorem isIntegralElem_iff_exists_monic_stage (i : I) (x : G.obj i) :
    φ.hom.IsIntegralElem ((cG.ι.app i).hom x) ↔
      ∃ (j : I) (f : i ⟶ j) (p : (F.obj j)[X]),
        p.Monic ∧ p.eval₂ (η.app j).hom ((G.map f).hom x) = 0 := by
  constructor
  · rintro ⟨p, hp, hpx⟩
    obtain ⟨k, hk⟩ := exists_finite_subset_range_ι_app F cF hF
      (p.coeffs : Set cF.pt) p.coeffs.finite_toSet
    have hlift : p ∈ Polynomial.lifts (cF.ι.app k).hom :=
      (Polynomial.lifts_iff_coeffs_subset_range _).mpr hk
    obtain ⟨q, hq, _, hqm⟩ := Polynomial.lifts_and_natDegree_eq_and_monic hlift hp
    let j := IsFiltered.max i k
    let f : i ⟶ j := IsFiltered.leftToMax i k
    let g : k ⟶ j := IsFiltered.rightToMax i k
    let qj := q.map (F.map g).hom
    have hqj : qj.map (cF.ι.app j).hom = p := by
      dsimp only [qj]
      rw [Polynomial.map_map]
      have hw : (cF.ι.app j).hom.comp (F.map g).hom = (cF.ι.app k).hom :=
        congrArg CommRingCat.Hom.hom (cF.w g)
      rw [hw, hq]
    have hcomp : (cG.ι.app j).hom.comp (η.app j).hom =
        φ.hom.comp (cF.ι.app j).hom :=
      (congrArg CommRingCat.Hom.hom (hφ j)).symm
    have hxj : (cG.ι.app j).hom ((G.map f).hom x) = (cG.ι.app i).hom x :=
      ConcreteCategory.congr_hom (cG.w f) x
    have heval : (cG.ι.app j).hom (qj.eval₂ (η.app j).hom ((G.map f).hom x)) =
        (cG.ι.app j).hom 0 := by
      rw [Polynomial.hom_eval₂, hcomp, hxj, ← Polynomial.eval₂_map, hqj, hpx, map_zero]
    obtain ⟨l, a, b, hab⟩ :=
      (Concrete.isColimit_rep_eq_iff_exists G hG _ _).mp heval
    refine ⟨l, f ≫ a, qj.map (F.map a).hom, (hqm.map _).map _, ?_⟩
    have hnat : (η.app l).hom.comp (F.map a).hom =
        (G.map a).hom.comp (η.app j).hom :=
      congrArg CommRingCat.Hom.hom (η.naturality a)
    rw [Polynomial.eval₂_map, hnat, G.map_comp]
    change qj.eval₂ ((G.map a).hom.comp (η.app j).hom)
      ((G.map a).hom ((G.map f).hom x)) = 0
    rw [← Polynomial.hom_eval₂]
    simpa only [map_zero] using hab
  · rintro ⟨j, f, p, hp, hpx⟩
    have hi : (η.app j).hom.IsIntegralElem ((G.map f).hom x) := ⟨p, hp, hpx⟩
    have hm := hi.map (cG.ι.app j).hom
    have hc : (cG.ι.app j).hom.comp (η.app j).hom =
        φ.hom.comp (cF.ι.app j).hom :=
      (congrArg CommRingCat.Hom.hom (hφ j)).symm
    rw [hc] at hm
    have hx : (cG.ι.app j).hom ((G.map f).hom x) = (cG.ι.app i).hom x :=
      ConcreteCategory.congr_hom (cG.w f) x
    rw [hx] at hm
    exact hm.of_comp

/-- Native eventual integrality, retaining the specified source-stage element
and an actual transition arrow rather than a replacement representative. -/
theorem isIntegralElem_iff_exists_stage (i : I) (x : G.obj i) :
    φ.hom.IsIntegralElem ((cG.ι.app i).hom x) ↔
      ∃ (j : I) (f : i ⟶ j), (η.app j).hom.IsIntegralElem ((G.map f).hom x) := by
  rw [isIntegralElem_iff_exists_monic_stage F G η cF cG hF hG φ hφ i x]
  rfl

end CommRingCat
