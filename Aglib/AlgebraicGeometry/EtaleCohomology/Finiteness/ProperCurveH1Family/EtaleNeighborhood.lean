/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Finiteness.ProperCurveH1Family.FibreValues
public import Aglib.AlgebraicGeometry.EtaleCohomology.H1.ProperHenselian.EtaleZeroSpreading
public import Aglib.AlgebraicGeometry.EtaleCohomology.Finite.GeometricNeighborhoodFunctor
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen

/-! # Actual etale zero neighborhoods over a scheme parameter space

Restrict to an actual affine open containing the rational parameter and use
proper-henselian H1 rigidity with original fixed-coefficient continuity there.
The resulting neighborhood and zero class retain their original pullback maps.
This adapter asserts neither a Zariski section nor general proper base change.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.EtaleCohomology.ProperCurveH1Family

attribute [local instance] hasSheafifyLarge HasExt.standard

/-- An actual rational section of an affine structure map gives a surjective
original ring map; no residue-field isomorphism is assumed. -/
theorem surjective_preimage_of_section {k : Type u} [Field k]
    (R : CommRingCat.{u}) (t : Spec R ⟶ Spec (.of k))
    (b : Spec (.of k) ⟶ Spec R) (hb : b ≫ t = 𝟙 _) :
    Function.Surjective (Spec.preimage b).hom := by
  have hs : Spec.preimage t ≫ Spec.preimage b = 𝟙 (CommRingCat.of k) := by
    apply Spec.map_injective
    rw [Spec.map_comp, Spec.map_preimage, Spec.map_preimage, Spec.map_id]
    exact hb
  intro x
  refine ⟨(Spec.preimage t).hom x, ?_⟩
  exact congrArg (fun z : CommRingCat.of k ⟶ CommRingCat.of k => z.hom x) hs

/-- Zero on the original rational fibre of a proper family spreads to one
actual pointed etale neighborhood, over an arbitrary scheme parameter base.
The henselian and continuity arguments are supplied by the proved affine
zero-spreading theorem, not left as a premise. -/
theorem exists_etale_neighborhood_of_rational_fibre_zero
    {k : Type u} [Field k] {Y T : Scheme.{u}}
    (p : Y ⟶ T) [IsProper p] (t : T ⟶ Spec (.of k))
    (b : Spec (.of k) ⟶ T) (hb : b ≫ t = 𝟙 _)
    (F : AbelianSheaf.{u, u + 1} Y) (hF : IsFiniteLocallyConstant F)
    (c : H1Etale.{u, u + 1, u + 2} Y F)
    (hc : h1Pullback (pullback.snd b p) F c = 0) :
    ∃ (U : Scheme.{u}) (j : U ⟶ T), Etale j ∧
      ∃ a : Spec (.of k) ⟶ U, a ≫ j = b ∧
        h1Pullback (pullback.snd j p) F c = 0 := by
  obtain ⟨R, j, hj, hbj, _⟩ := exists_affine_mem_range_and_range_subset
    (x := b (IsLocalRing.closedPoint k)) (U := ⊤) (by simp)
  let : IsOpenImmersion j := hj
  have hbr : Set.range b ⊆ Set.range j := by
    rintro _ ⟨z, rfl⟩
    simpa only [Subsingleton.elim z (IsLocalRing.closedPoint k)] using hbj
  let bR := IsOpenImmersion.lift j b hbr
  have hbR : bR ≫ j = b := IsOpenImmersion.lift_fac j b hbr
  have hbRS : bR ≫ (j ≫ t) = 𝟙 _ := by rw [← Category.assoc, hbR, hb]
  let : Algebra R k := (Spec.preimage bR).hom.toAlgebra
  have hspec : Spec.algebraMap R k = bR := Spec.map_preimage bR
  have hsurj : Function.Surjective (algebraMap R k) :=
    surjective_preimage_of_section R (j ≫ t) bR hbRS
  let q : pullback j p ⟶ Spec R := pullback.fst j p
  let s : pullback j p ⟶ Y := pullback.snd j p
  let FR := (inverseImage s).obj F
  let cR : H1Etale.{u, u + 1, u + 2} (pullback j p) FR := h1Pullback s F c
  let z : pullback bR q ⟶ pullback j p := pullback.snd bR q
  let v : pullback bR q ⟶ Spec (.of k) := pullback.fst bR q
  have hz : (z ≫ s) ≫ p = v ≫ b := by
    calc
      (z ≫ s) ≫ p = z ≫ q ≫ j := by
        rw [Category.assoc, ← pullback.condition (f := j) (g := p)]
      _ = (v ≫ bR) ≫ j := by
        rw [← Category.assoc, ← pullback.condition (f := bR) (g := q)]
      _ = v ≫ b := by rw [Category.assoc, hbR]
  let a : pullback bR q ⟶ pullback b p := pullback.lift v (z ≫ s) hz.symm
  have ha : a ≫ pullback.snd b p = z ≫ s := pullback.lift_snd _ _ _
  have hzc : h1Pullback (z ≫ s) F c = 0 :=
    h1Pullback_eq_zero_of_eq ha F c (h1Pullback_comp_eq_zero _ a F c hc)
  have hcR : h1Pullback (pullback.snd (Spec.algebraMap R k) q) FR cR = 0 := by
    rw [hspec]
    exact (h1Pullback_comp_eq_zero_iff s z F c).mpr hzc
  let : IsProper q := inferInstanceAs (IsProper (pullback.fst j p))
  obtain ⟨N, hN⟩ := ProperHenselian.exists_etale_h1Pullback_eq_zero R k hsurj q FR
    (isFiniteLocallyConstant_pullback s hF) cR hcR
  let u : Spec (.of N.algebra) ⟶ Spec R := Spec.algebraMap R N.algebra
  let : Etale u := inferInstanceAs
    (Etale (Finite.GeometricNeighborhood.etaleObject R k N).hom)
  let jN := u ≫ j
  let aN : Spec (.of k) ⟶ Spec (.of N.algebra) :=
    Spec.map (CommRingCat.ofHom N.point.toRingHom)
  have hpoint : aN ≫ u = Spec.algebraMap R k :=
    Finite.GeometricNeighborhood.stagePoint_over R k N
  have haN : aN ≫ jN = b := by
    calc
      aN ≫ jN = (aN ≫ u) ≫ j := (Category.assoc _ _ _).symm
      _ = Spec.algebraMap R k ≫ j := congrArg (fun e => e ≫ j) hpoint
      _ = b := by rw [hspec, hbR]
  let sN : pullback u q ⟶ Y := pullback.snd u q ≫ s
  have hsN : h1Pullback sN F c = 0 :=
    (h1Pullback_comp_eq_zero_iff s (pullback.snd u q) F c).mp hN
  let aR : pullback jN p ⟶ pullback j p :=
    pullback.lift (pullback.fst jN p ≫ u) (pullback.snd jN p)
      (by simpa only [Category.assoc] using pullback.condition (f := jN) (g := p))
  let aNN : pullback jN p ⟶ pullback u q :=
    pullback.lift (pullback.fst jN p) aR (by simp only [aR, q, pullback.lift_fst])
  have haNN : aNN ≫ sN = pullback.snd jN p := by
    simp only [aNN, sN, pullback.lift_snd_assoc, aR, s,
      pullback.lift_snd]
  refine ⟨Spec (.of N.algebra), jN, inferInstance, aN, haN, ?_⟩
  exact h1Pullback_eq_zero_of_eq haNN F c (h1Pullback_comp_eq_zero sN aNN F c hsN)

end AlgebraicGeometry.Scheme.EtaleCohomology.ProperCurveH1Family
