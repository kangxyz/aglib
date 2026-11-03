/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Surfaces.Birational.NormalizedPointDomination.Comparison
public import Aglib.AlgebraicGeometry.Surfaces.Birational.NormalizedPointDomination.SelectedStep
public import Aglib.AlgebraicGeometry.Surfaces.Birational.NormalizedPointDomination.NormalCommonModel
public import Aglib.AlgebraicGeometry.Surfaces.Birational.NormalizedPointDomination.PointStep
public import Aglib.AlgebraicGeometry.Surfaces.Birational.NormalizedPointDomination.Noncollapse
public import Aglib.AlgebraicGeometry.Surfaces.Birational.NormalizedPointDomination.GenericResidueSection
public import Aglib.AlgebraicGeometry.Surfaces.Birational.NormalizedPointDomination.SelectedFraction

/-!
# Finite elimination of one selected actual contracted curve

Strong induction uses the minimum of the two finite orders of one retained
fraction. Each induction step constructs the literal normalized point blowup
and its actual normal generic graph component. If the curve survives, the
same fraction decreases by the proved normalized-point calculation. The
output contains the actual finite chain and composite proper-image comparison.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace AlgebraicGeometry.Scheme.NormalizedPointDomination

universe u
open Blowup

private theorem stalkMap_injective
    {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    (f : X ⟶ Y) [IsDominant f] (x : X) : Function.Injective (f.stalkMap x) := by
  intro a b hab
  apply IsFractionRing.injective (Y.presheaf.stalk (f x)) Y.functionField
  apply (functionFieldMap f).injective
  rw [functionFieldMap_stalk, functionFieldMap_stalk]
  exact congrArg (algebraMap (X.presheaf.stalk x) X.functionField) hab

private theorem exists_fraction_drop
    {Z Q S : Scheme.{u}} [IsIntegral Z] [IsIntegral Q] [IsIntegral S]
    [IsLocallyNoetherian Z] [IsLocallyNoetherian Q]
    [∀ z : Z, IsIntegrallyClosed (Z.presheaf.stalk z)]
    [∀ y : Q, IsIntegrallyClosed (Q.presheaf.stalk y)]
    (x : S) (hx : IsClosed ({x} : Set S)) (hne : x ≠ genericPoint S)
    [LocallyOfFiniteType (normalizedPointBlowupMap S x hx hne)]
    (c : CodimensionOnePoint Z) (g : Z ⟶ Q) (q : Q ⟶ S)
    (p : Z ⟶ normalizedPointBlowup S x hx hne)
    (w : g ≫ q = p ≫ normalizedPointBlowupMap S x hx hne)
    [IsIso (g.stalkMap c.val)]
    (hclosed : IsClosed ({p c.val} : Set _))
    (η : Q) (he : g c.val = η) (hcenter : q η = x)
    (hc : ringKrullDim (Q.presheaf.stalk η) = 1)
    (u : Q.presheaf.stalk η) (a d : S.presheaf.stalk (q η))
    (ha : q.stalkMap η a ≠ 0) (hd : q.stalkMap η d ≠ 0)
    (hfrac : u * q.stalkMap η d = q.stalkMap η a)
    (hu : letI := (q.residueFieldMap η).hom.toAlgebra
      Transcendental (S.residueField (q η)) (Q.residue η u))
    (n : ℕ)
    (horder : min (CodimensionOnePoint.finiteOrder (X := Q) ⟨η, hc⟩ (q.stalkMap η a))
      (CodimensionOnePoint.finiteOrder (X := Q) ⟨η, hc⟩ (q.stalkMap η d)) = n) :
    let := (p.residueFieldMap c.val).hom.toAlgebra
    ∃ (u' : Z.presheaf.stalk c.val)
      (a' d' : (normalizedPointBlowup S x hx hne).presheaf.stalk (p c.val)),
      p.stalkMap c.val a' ≠ 0 ∧ p.stalkMap c.val d' ≠ 0 ∧
      u' * p.stalkMap c.val d' = p.stalkMap c.val a' ∧
      Transcendental ((normalizedPointBlowup S x hx hne).residueField (p c.val))
        (Z.residue c.val u') ∧
      min (c.finiteOrder (p.stalkMap c.val a'))
        (c.finiteOrder (p.stalkMap c.val d')) < n := by
  subst η
  obtain ⟨a', d', _, _, ha', hd', hf', hu', hltA, hltD⟩ :=
    exists_decreasing_fraction_at_normalizedPoint x hx hne c g q p w hc
      hcenter hclosed u a d ha hd hfrac hu
  refine ⟨g.stalkMap c.val u, a', d', ha', hd', hf', hu', ?_⟩
  rw [← horder]
  exact lt_min (lt_of_le_of_lt (min_le_left _ _) hltA)
    (lt_of_le_of_lt (min_le_right _ _) hltD)

private theorem exists_missing_curve_of_fraction
    {P : Scheme.{u}} [IsIntegral P] [IsNoetherian P]
    (hNagata : ∀ V : P.affineOpens, Nonempty V.1 → IsNagataRing.{u, 0} Γ(P, V.1))
    (hdP : topologicalKrullDim P ≤ 2)
    {S Q : Scheme.{u}} [IsIntegral S] [IsIntegral Q] [IsNoetherian S] [IsNoetherian Q]
    (b : S ⟶ P) [IsProper b] [IsDominant b]
    (hb : IsIso (CommRingCat.ofHom (functionFieldMap b)))
    (hS : NormalStalks S) (hQ : NormalStalks Q) (hdQ : topologicalKrullDim Q ≤ 2)
    (q : Q ⟶ S) [IsProper q] [IsDominant q]
    (hq : IsIso (CommRingCat.ofHom (functionFieldMap q)))
    (C : contractedCurves q) (η : Q) (hη : IsGenericPoint η (C.val : Set Q))
    (hcodim : ringKrullDim (Q.presheaf.stalk η) = 1)
    (u : Q.presheaf.stalk η) (a d : S.presheaf.stalk (q η))
    (ha : q.stalkMap η a ≠ 0) (hd : q.stalkMap η d ≠ 0)
    (hfrac : u * q.stalkMap η d = q.stalkMap η a)
    (hu : letI := (q.residueFieldMap η).hom.toAlgebra
      Transcendental (S.residueField (q η)) (Q.residue η u))
    (n : ℕ)
    (horder : letI : ∀ y : Q, IsIntegrallyClosed (Q.presheaf.stalk y) := fun y ↦ (hQ y).2
      min (CodimensionOnePoint.finiteOrder (X := Q) ⟨η, hcodim⟩ (q.stalkMap η a))
        (CodimensionOnePoint.finiteOrder (X := Q) ⟨η, hcodim⟩ (q.stalkMap η d)) = n) :
    ∃ B : NormalPointComparison q, C ∉ Set.range (B.curveEmbedding hQ hdQ) := by
  classical
  induction n using Nat.strong_induction_on generalizing S Q with
  | h n ih =>
    let : ∀ y : Q, IsIntegrallyClosed (Q.presheaf.stalk y) := fun y ↦ (hQ y).2
    let x := q η
    have hx : IsClosed ({x} : Set S) := by
      have he : η = C.val.isIrreducible.genericPoint :=
        hη.eq (C.val.isIrreducible.isGenericPoint_genericPoint C.val.isClosed)
      simpa only [x, he] using CurveResidue.isClosed_image_point q C.val C.property
    have hne : x ≠ genericPoint S := by
      intro he
      have heη := q.eq_genericPoint_of_map_eq_genericPoint hq hS η he
      exact genericPoint_not_mem_contractedCurve q hq hS C.val C.property (heη ▸ hη.mem)
    let N := normalizedPointBlowup S x hx hne
    let r := normalizedPointBlowupMap S x hx hne
    let : IsIntegral N := normalizedPointBlowup_isIntegral S x hx hne
    let : IsNoetherian N := normalizedPointBlowup_isNoetherian_over_base
      b hNagata hdP hb x hx hne
    let : IsProper r := normalizedPointBlowupMap_isProper_over_base b hNagata hdP hb x hx hne
    let : IsDominant r := normalizedPointBlowupMap_isDominant S x hx hne
    have hr : IsIso (CommRingCat.ofHom (functionFieldMap r)) :=
      normalizedPointBlowupMap_functionFieldMap_isIso S x hx hne
    have hN := normalizedPointBlowup_normalStalks S x hx hne
    have hdN := normalizedPointBlowup_dimension_over_base b hNagata hdP hb x hx hne
    obtain ⟨Z, p, g, hZI, hpD, hgD, hZ, hZN, hdZ, hpP, hgP, hp, hg, w, hfin⟩ :=
      exists_normalCommonModel b hb hS hNagata hdP r hr q hq
    let := hZI
    let := hZN
    let := hpD
    let := hgD
    let := hpP
    let := hgP
    let := hfin
    let : ∀ z : Z, IsIntegrallyClosed (Z.presheaf.stalk z) := fun z ↦ (hZ z).2
    let B : NormalPointComparison q := {
      base := N
      model := Z
      beta := r
      p := p
      g := g
      comm := w.symm
      chain := by
        simpa only [Category.id_comp] using
          NormalizedPointBlowupChain.cons x hx hne (𝟙 N) (.refl N)
      baseNormal := hN
      modelNormal := hZ
      baseDimension := hdN
      modelDimension := hdZ
      betaBirational := hr
      pBirational := hp
      gBirational := hg
      noncollapse := fun D hD ↦ not_subsingleton_image_of_finite_pair p g r q w D hD }
    by_cases hmiss : C ∉ Set.range (B.curveEmbedding hQ hdQ)
    · exact ⟨B, hmiss⟩
    obtain ⟨C', himage⟩ := Classical.not_not.mp hmiss
    have hgen := g.isGenericPoint_irreducibleClosedImage C'.val
    have himage' : g.irreducibleClosedImage C'.val = C.val := congrArg Subtype.val himage
    rw [himage'] at hgen
    have hgη : g C'.val.isIrreducible.genericPoint = η := hgen.eq hη
    generalize hη' : C'.val.isIrreducible.genericPoint = η'
    have hgη' : g η' = η := (congrArg g hη'.symm).trans hgη
    have hc' : ringKrullDim (Z.presheaf.stalk η') = 1 := by
      rw [← hη']
      exact (contractedCurvePoint p hp hN hdZ C'.val C'.property).property
    let c' : CodimensionOnePoint Z := ⟨η', hc'⟩
    let : IsIso (g.stalkMap η') := by
      rw [← hη']
      exact g.isIso_stalkMap_genericPoint_of_not_subsingleton_image hg hQ hdQ C'.val
        (B.noncollapse C'.val C'.property)
    have hclosed : IsClosed ({p η'} : Set N) := by
      rw [← hη']
      exact CurveResidue.isClosed_image_point p C'.val C'.property
    obtain ⟨u', a', d', ha', hd', hfrac', hu', hlt⟩ :=
      exists_fraction_drop x hx hne c' g q p w.symm hclosed η hgη' rfl hcodim
        u a d ha hd hfrac hu n horder
    let n' := min (c'.finiteOrder (p.stalkMap η' a')) (c'.finiteOrder (p.stalkMap η' d'))
    have hrb : IsIso (CommRingCat.ofHom (functionFieldMap (r ≫ b))) := by
      let := hr
      let := hb
      rw [functionFieldMap_comp, CommRingCat.ofHom_comp]
      infer_instance
    have hgeneric' : IsGenericPoint η' (C'.val : Set Z) :=
      hη' ▸ C'.val.isIrreducible.isGenericPoint_genericPoint C'.val.isClosed
    obtain ⟨D, hDmiss⟩ := ih n' hlt (b := r ≫ b) hrb hN hZ hdZ p hp C' η'
      hgeneric' hc' u' a' d' ha' hd' hfrac' hu' rfl
    exact ⟨B.comp D, B.missing_curve_comp D hQ hdQ C C' himage hDmiss⟩

/-- A selected actual contracted curve disappears after a constructed finite
chain of literal normalized point blowups. Strong induction uses the finite
orders of one constructed retained fraction, not a supplied termination path. -/
theorem exists_comparison_missing_curve
    {P S Q : Scheme.{u}} [IsIntegral P] [IsIntegral S] [IsIntegral Q]
    [IsNoetherian P] [IsNoetherian S] [IsNoetherian Q]
    (b : S ⟶ P) [IsProper b] [IsDominant b]
    (hb : IsIso (CommRingCat.ofHom (functionFieldMap b)))
    (hNagata : ∀ V : P.affineOpens, Nonempty V.1 → IsNagataRing.{u, 0} Γ(P, V.1))
    (hdP : topologicalKrullDim P ≤ 2)
    (hS : NormalStalks S) (hQ : NormalStalks Q) (hdQ : topologicalKrullDim Q ≤ 2)
    (q : Q ⟶ S) [IsProper q] [IsDominant q]
    (hq : IsIso (CommRingCat.ofHom (functionFieldMap q))) (C : contractedCurves q) :
    ∃ B : NormalPointComparison q, C ∉ Set.range (B.curveEmbedding hQ hdQ) := by
  let : ∀ y : Q, IsIntegrallyClosed (Q.presheaf.stalk y) := fun y ↦ (hQ y).2
  let c := contractedCurvePoint q hq hS hdQ C.val C.property
  obtain ⟨u, hu⟩ := exists_transcendental_curve_residue q C.val C.property
  obtain ⟨_, a, d, ha, hd, _, _, hfrac⟩ :=
    exists_local_fraction_of_transcendental_residue q hq c.val u hu
  have ha' : q.stalkMap c.val a ≠ 0 :=
    (map_ne_zero_iff (q.stalkMap c.val).hom (stalkMap_injective q c.val)).mpr ha
  have hd' : q.stalkMap c.val d ≠ 0 :=
    (map_ne_zero_iff (q.stalkMap c.val).hom (stalkMap_injective q c.val)).mpr hd
  exact exists_missing_curve_of_fraction hNagata hdP b hb hS hQ hdQ q hq C c.val
    (C.val.isIrreducible.isGenericPoint_genericPoint C.val.isClosed) c.property u a d
    ha' hd' hfrac hu _ rfl

end AlgebraicGeometry.Scheme.NormalizedPointDomination
