/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.FiniteStratification.ClosedComplement
public import Aglib.AlgebraicGeometry.IdealSheaf.Closed.RadicalSubscheme

/-! # Reduced closed-support induction for actual finite partitions

Generic-open information on every nonempty reduced closed subscheme constructs
a finite partition of the original scheme, with the property on its actual
component maps. The property need not be supplied on arbitrary restrictions.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Constructible.FiniteLocallyClosedPartition

universe u

private theorem vanishingIdeal_radical {X : Scheme.{u}} (Z : Closeds X) :
    (IdealSheafData.vanishingIdeal Z).radical = IdealSheafData.vanishingIdeal Z := by
  apply Scheme.IdealSheafData.ext
  funext V
  simp only [IdealSheafData.radical_ideal, IdealSheafData.vanishingIdeal_ideal]
  exact Ideal.radical_eq_iff.mpr (PrimeSpectrum.isRadical_vanishingIdeal _)

/-- Actual generic open pieces on reduced closed supports construct an actual
finite partition. The labels, reduced complements and original component maps
are constructed by Noetherian induction, rather than supplied as conclusions. -/
theorem exists_of_noetherian_reducedClosed_open
    {X : Scheme.{u}} [IsNoetherian X]
    (P : ∀ {Y : Scheme.{u}}, (Y ⟶ X) → Prop)
    (hgen : ∀ (Y : Scheme.{u}) (j : Y ⟶ X),
      IsClosedImmersion j → IsReduced Y → Nonempty Y →
      ∃ U : Y.Opens, Nonempty U.toScheme ∧ P (U.ι ≫ j)) :
    ∃ p : FiniteLocallyClosedPartition X, ∀ i, P (p.inclusion i) := by
  classical
  let Q (Z : Closeds X) : Prop := ∀ (Y : Scheme.{u}) (j : Y ⟶ X),
    IsClosedImmersion j → IsReduced Y → Set.range j = (Z : Set X) →
      ∃ p : FiniteLocallyClosedPartition Y, ∀ i, P (p.inclusion i ≫ j)
  have hQ : ∀ Z, Q Z := by
    intro Z
    apply wellFounded_lt.induction Z
    clear Z
    intro Z ih Y j hj hred hjrange
    let : IsClosedImmersion j := hj
    let : IsReduced Y := hred
    let : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian j
    let : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace j
    let : IsNoetherian Y := ⟨⟩
    by_cases hY : Nonempty Y
    · obtain ⟨U, hU, hopen⟩ := hgen Y j hj hred hY
      let I := IdealSheafData.vanishingIdeal U.ι.opensRange.compl
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
        let y : U.toScheme := Classical.choice hU
        have hx : j (U.ι y) ∈ (W : Set X) := by
          rw [heq, ← hjrange]
          exact ⟨U.ι y, rfl⟩
        obtain ⟨z, hz⟩ := hx
        have hz' : I.subschemeι z = U.ι y := j.isClosedEmbedding.injective hz
        have hmem : I.subschemeι z ∈ Set.range I.subschemeι := ⟨z, rfl⟩
        rw [IdealSheafData.range_subschemeι,
          IdealSheafData.coe_support_vanishingIdeal] at hmem
        exact hmem (hz'.symm ▸ ⟨y, rfl⟩)
      obtain ⟨p, hp⟩ := ih W (lt_of_le_of_ne hWle hWne) I.subscheme k
        inferInstance hIred rfl
      refine ⟨attachOpen U.ι p, ?_⟩
      suffices ∀ i : Option (Fin p.count), P (attachOpenInclusion U.ι p i ≫ j) by
        intro i
        exact this ((Fintype.equivFin (Option (Fin p.count))).symm i)
      intro i
      cases i with
      | none => exact hopen
      | some i =>
        change P ((p.inclusion i ≫ I.subschemeι) ≫ j)
        rw [Category.assoc]
        exact hp i
    · let : IsEmpty Y := not_nonempty_iff.mp hY
      let p : FiniteLocallyClosedPartition Y := {
        count := 0
        stratum := fun i => Fin.elim0 i
        inclusion := fun i => Fin.elim0 i
        immersion := fun i => Fin.elim0 i
        constructible_range := fun i => Fin.elim0 i
        disjoint := by intro i; exact Fin.elim0 i
        covers := fun y => isEmptyElim y }
      exact ⟨p, fun i => Fin.elim0 i⟩
  let I := IdealSheafData.vanishingIdeal (⊤ : Closeds X)
  have hIred : IsReduced I.subscheme :=
    IdealSheafData.subscheme_reduced_of_radical I (vanishingIdeal_radical _)
  have hIrange : Set.range I.subschemeι = (⊤ : Set X) :=
    (IdealSheafData.range_subschemeι I).trans (IdealSheafData.coe_support_vanishingIdeal _)
  let : Surjective I.subschemeι := ⟨by
    intro x
    have hx : x ∈ Set.range I.subschemeι := by rw [hIrange]; trivial
    exact hx⟩
  obtain ⟨p, hp⟩ := hQ ⊤ I.subscheme I.subschemeι inferInstance hIred hIrange
  exact ⟨alongSurjectiveClosed I.subschemeι p, hp⟩

end AlgebraicGeometry.Scheme.EtaleCohomology.Constructible.FiniteLocallyClosedPartition
