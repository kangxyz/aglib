/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.FiniteStratification.ClosedComplement
public import Aglib.AlgebraicGeometry.IdealSheaf.Closed.RadicalSubscheme
public import Aglib.AlgebraicGeometry.Properties.IrreducibleComponents.IntegralOpen

/-! # Noetherian finite partitions from generic open parts

A property of original morphisms to a Noetherian scheme holds on a finite
locally closed partition if it holds on an actual nonempty open part of every
integral affine immersion. Empty schemes use the empty partition. The induction uses
native reduced closed subschemes and retains all original inclusion maps.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Constructible

universe u

private theorem vanishingIdeal_radical {X : Scheme.{u}} (Z : Closeds X) :
    (IdealSheafData.vanishingIdeal Z).radical = IdealSheafData.vanishingIdeal Z := by
  apply Scheme.IdealSheafData.ext
  funext V
  simp only [IdealSheafData.radical_ideal, IdealSheafData.vanishingIdeal_ideal]
  exact Ideal.radical_eq_iff.mpr (PrimeSpectrum.isRadical_vanishingIdeal _)

private theorem exists_integral_affine_open (X : Scheme.{u})
    [IsNoetherian X] [IsReduced X] [Nonempty X] :
    ∃ V : X.Opens, IsAffineOpen V ∧ Nonempty V.toScheme ∧ IsIntegral V.toScheme :=
  Scheme.exists_integral_affine_open_of_noetherian_reduced X

/-- A generic nonempty-open property of actual integral affine immersions
gives a finite partition of the original
Noetherian scheme on which the property holds. -/
theorem exists_finitePartition_of_generic_open
    {X : Scheme.{u}} [IsNoetherian X]
    (Q : ∀ {Y : Scheme.{u}}, (Y ⟶ X) → Prop)
    (hgeneric : ∀ (Y : Scheme.{u}) [IsNoetherian Y] [IsAffine Y] [IsIntegral Y]
      (i : Y ⟶ X) [IsImmersion i],
      ∃ (S : Scheme.{u}) (a : S ⟶ Y),
        IsOpenImmersion a ∧ Nonempty S ∧ Q (a ≫ i)) :
    ∃ p : FiniteLocallyClosedPartition X, ∀ i, Q (p.inclusion i) := by
  let P (Z : Closeds X) : Prop := ∀ (Y : Scheme.{u}) (j : Y ⟶ X),
    IsClosedImmersion j → IsReduced Y → Set.range j = (Z : Set X) →
      ∃ p : FiniteLocallyClosedPartition Y,
        ∀ i, Q (p.inclusion i ≫ j)
  have hP : ∀ Z, P Z := by
    intro Z
    apply wellFounded_lt.induction Z
    clear Z
    intro Z ih Y j hj hred hjrange
    have : IsClosedImmersion j := hj
    have : IsReduced Y := hred
    have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian j
    have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace j
    have : IsNoetherian Y := ⟨⟩
    by_cases hY : Nonempty Y
    · have : Nonempty Y := hY
      obtain ⟨V, hV, -, hVintegral⟩ := exists_integral_affine_open Y
      have : IsAffine V.toScheme := hV
      have : IsIntegral V.toScheme := hVintegral
      have : IsNoetherian V.toScheme := ⟨⟩
      obtain ⟨S, a, ha, hS, haQ⟩ := hgeneric V.toScheme (V.ι ≫ j)
      have : IsOpenImmersion a := ha
      have : Nonempty S := hS
      let b : S ⟶ Y := a ≫ V.ι
      have hbQ : Q (b ≫ j) := by
        simpa only [b, Category.assoc] using haQ
      let I := IdealSheafData.vanishingIdeal b.opensRange.compl
      let k : I.subscheme ⟶ X := I.subschemeι ≫ j
      have hIred : IsReduced I.subscheme :=
        IdealSheafData.subscheme_reduced_of_radical I (vanishingIdeal_radical _)
      let W : Closeds X := ⟨Set.range k, k.isClosedEmbedding.isClosed_range⟩
      have hWle : W ≤ Z := by
        rintro x ⟨z, rfl⟩
        change k z ∈ (Z : Set X)
        rw [← hjrange]
        exact ⟨I.subschemeι z, rfl⟩
      have hWne : W ≠ Z := by
        intro heq
        let s : S := Classical.choice hS
        have hx : j (b s) ∈ (W : Set X) := by
          rw [heq, ← hjrange]
          exact ⟨b s, rfl⟩
        obtain ⟨z, hz⟩ := hx
        have hz' : I.subschemeι z = b s := j.isClosedEmbedding.injective hz
        have hcompl : I.subschemeι z ∉ Set.range b := by
          have hmem : I.subschemeι z ∈ Set.range I.subschemeι := ⟨z, rfl⟩
          rw [IdealSheafData.range_subschemeι,
            IdealSheafData.coe_support_vanishingIdeal] at hmem
          exact hmem
        exact hcompl (hz'.symm ▸ ⟨s, rfl⟩)
      obtain ⟨p, hp⟩ := ih W (lt_of_le_of_ne hWle hWne) I.subscheme k
        inferInstance hIred rfl
      refine ⟨FiniteLocallyClosedPartition.attachOpen b p, ?_⟩
      suffices ∀ i : Option (Fin p.count),
          Q (FiniteLocallyClosedPartition.attachOpenInclusion b p i ≫ j) by
        intro i
        exact this ((Fintype.equivFin (Option (Fin p.count))).symm i)
      intro i
      cases i with
      | none => exact hbQ
      | some i =>
        change Q ((p.inclusion i ≫ I.subschemeι) ≫ j)
        rw [Category.assoc]
        exact hp i
    · have : IsEmpty Y := not_nonempty_iff.mp hY
      refine ⟨{
        count := 0
        stratum := fun i => Fin.elim0 i
        inclusion := fun i => Fin.elim0 i
        immersion := fun i => Fin.elim0 i
        constructible_range := fun i => Fin.elim0 i
        disjoint := fun i => Fin.elim0 i
        covers := fun x => isEmptyElim x }, ?_⟩
      exact fun i => Fin.elim0 i
  let I := IdealSheafData.vanishingIdeal (⊤ : Closeds X)
  have hIred : IsReduced I.subscheme :=
    IdealSheafData.subscheme_reduced_of_radical I (vanishingIdeal_radical _)
  have hIrange : Set.range I.subschemeι = (⊤ : Set X) :=
    (IdealSheafData.range_subschemeι I).trans
      (IdealSheafData.coe_support_vanishingIdeal _)
  have : Surjective I.subschemeι := ⟨by
    intro x
    have hx : x ∈ Set.range I.subschemeι := by rw [hIrange]; trivial
    exact hx⟩
  obtain ⟨p, hp⟩ := hP ⊤ I.subscheme I.subschemeι inferInstance hIred hIrange
  exact ⟨FiniteLocallyClosedPartition.alongSurjectiveClosed I.subschemeι p, hp⟩

end AlgebraicGeometry.Scheme.EtaleCohomology.Constructible
