/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Finiteness.ProperCurveH1Family.EtaleNeighborhood

/-! # Finite original H1 image of an actual proper constant family

Subtracting the inflation of one original fibre value gives zero on that
actual fibre. Proper-henselian rigidity and fixed-coefficient continuity spread
the zero class to a pointed etale neighborhood. Its open image has the same
original value at every rational parameter: a rational lift exists over a
separably closed field, without any asserted Zariski section.

Closed rational points cover the whole Jacobson parameter space by the
closed-complement argument, and compactness then gives finitely many original
H1 values. The fixed proper scheme need not be a curve. No proper base change,
H1 finiteness premise, or alternative cohomology model is used.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme.EtaleCohomology.PointedNaturality

universe u

namespace AlgebraicGeometry.Scheme.EtaleCohomology.ProperCurveH1Family

attribute [local instance] hasSheafifyLarge HasExt.standard

variable {k : Type u} [Field k] [IsAlgClosed k]
  {X Y T : Scheme.{u}} {f : X ⟶ Spec (.of k)} {t : T ⟶ Spec (.of k)}
  {r : Y ⟶ X} {p : Y ⟶ T} (h : IsPullback r p f t)
  (L : AbelianSheaf.{u, u + 1} X)
  (c : H1Etale.{u, u + 1, u + 2} Y ((inverseImage r).obj L))

omit [IsAlgClosed k] in
/-- Every original section satisfying the two original fibre equations gives
the canonical original value. Proof irrelevance changes no scheme arrow. -/
theorem sectionPullback_eq_value (b : Spec (.of k) ⟶ T) (hb : b ≫ t = 𝟙 _)
    (a : X ⟶ Y) (haX : a ≫ r = 𝟙 X) (haT : a ≫ p = f ≫ b) :
    sectionPullback r a haX L c = value h b hb L c := by
  have ha := eq_fibreArrow h b hb a haX haT
  subst a
  rfl

/-- An actual rational fibre value is constant on the rational parameters in
an actual open neighborhood. The open is the image of a pointed etale map,
not a neighborhood equipped with an asserted Zariski section. -/
theorem value_locally_constant [IsProper f] (hL : IsFiniteLocallyConstant L)
    (b : RationalParameter t) :
    ∃ V : Set T, IsOpen V ∧ b.1 (IsLocalRing.closedPoint k) ∈ V ∧
      ∀ b' : RationalParameter t,
        b'.1 (IsLocalRing.closedPoint k) ∈ V →
          value h b'.1 b'.2 L c = value h b.1 b.2 L c := by
  let : IsProper p := MorphismProperty.of_isPullback h inferInstance
  let a := fibreArrow h b.1 b.2
  let ha := fibreArrow_curveMap h b.1 b.2
  let F := (inverseImage r).obj L
  let d : H1Etale.{u, u + 1, u + 2} Y F := difference r a ha L c
  have hd : h1Pullback a F d = 0 := difference_pullback_eq_zero r a ha L c
  have hfactor : ((pullback.snd b.1 p) ≫ r) ≫ a = pullback.snd b.1 p :=
    comp_fibreArrow_eq h b.1 b.2 (pullback.snd b.1 p) (pullback.fst b.1 p)
      pullback.condition.symm
  have hdfibre : h1Pullback (pullback.snd b.1 p) F d = 0 :=
    h1Pullback_eq_zero_of_eq hfactor F d
      (h1Pullback_comp_eq_zero a ((pullback.snd b.1 p) ≫ r) F d hd)
  obtain ⟨U, j, hj, l, hl, hzero⟩ :=
    exists_etale_neighborhood_of_rational_fibre_zero p t b.1 b.2 F
      (isFiniteLocallyConstant_pullback r hL) d hdfibre
  let : Etale j := hj
  refine ⟨Set.range j, j.isOpenMap.isOpen_range, ?_, ?_⟩
  · refine ⟨l (IsLocalRing.closedPoint k), ?_⟩
    exact congrArg (fun q : Spec (.of k) ⟶ T => q (IsLocalRing.closedPoint k)) hl
  · intro b' hb'
    obtain ⟨x, hx⟩ := hb'
    have hx' : j x = b'.1 default := by
      simpa only [Subsingleton.elim (default : Spec (.of k)) (IsLocalRing.closedPoint k)] using hx
    obtain ⟨l', hl', _⟩ := Scheme.exists_fac_of_etale_of_isSepClosed j b'.1 x hx'
    let a' := fibreArrow h b'.1 b'.2
    let aU : X ⟶ pullback j p := pullback.lift (f ≫ l') a'
      (by rw [Category.assoc, hl']; exact (fibreArrow_projection h b'.1 b'.2).symm)
    have haU : aU ≫ pullback.snd j p = a' := pullback.lift_snd _ _ _
    have hzero' : h1Pullback a' F d = 0 :=
      h1Pullback_eq_zero_of_eq haU F d
        (h1Pullback_comp_eq_zero (pullback.snd j p) aU F d hzero)
    exact sectionPullback_eq_of_difference_eq_zero r a ha L c a'
      (fibreArrow_curveMap h b'.1 b'.2) hzero'

/-- A single actual family class has finite image in the original H1 of the
fixed proper scheme. Locally finite type supplies the Jacobson property and
rational closed points; compactness is used only after the full open cover. -/
theorem finite_range_value [IsProper f] [LocallyOfFiniteType t] [CompactSpace T]
    (hL : IsFiniteLocallyConstant L) :
    (Set.range (fun b : RationalParameter t => value h b.1 b.2 L c)).Finite :=
  finite_range_of_rational_local_constancy t _ (value_locally_constant h L c hL)

include h in
/-- Finitely many original values contain every literal original-scheme fibre
restriction satisfying the two projection equations. In particular this
accepts the actual arrows returned by the Kummer-family realization theorem. -/
theorem exists_finset_sectionPullback_values [IsProper f] [LocallyOfFiniteType t]
    [CompactSpace T] (hL : IsFiniteLocallyConstant L) :
    ∃ S : Finset (H1Etale.{u, u + 1, u + 2} X L),
      ∀ (b : Spec (.of k) ⟶ T) (_hb : b ≫ t = 𝟙 _)
        (a : X ⟶ Y) (haX : a ≫ r = 𝟙 X) (_haT : a ≫ p = f ≫ b),
        sectionPullback r a haX L c ∈ S := by
  classical
  let hfinite := finite_range_value h L c hL
  refine ⟨hfinite.toFinset, ?_⟩
  intro b hb a haX haT
  rw [hfinite.mem_toFinset, sectionPullback_eq_value h L c b hb a haX haT]
  exact ⟨⟨b, hb⟩, rfl⟩

end AlgebraicGeometry.Scheme.EtaleCohomology.ProperCurveH1Family
