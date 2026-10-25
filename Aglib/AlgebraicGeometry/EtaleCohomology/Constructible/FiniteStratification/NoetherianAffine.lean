/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.FiniteStratification.AffineOpen
public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.FiniteStratification.ClosedComplement
public import Aglib.AlgebraicGeometry.IdealSheaf.Closed.RadicalSubscheme

/-! # Actual finite strata for affine quasi-finite morphisms over a Noetherian base

Noetherian induction is performed on closed subsets of the original base.
Each recursive source is an actual reduced closed subscheme. A nonempty
integral affine open supplies a finite open part through the actual affine
algebra construction; its reduced closed complement has smaller closed range.
The final reduction immersion keeps the same original base and pullback maps.

The affine-morphism and Noetherian hypotheses are retained. No arbitrary
quasi-compact etale or non-Noetherian stratification is asserted here.
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
    ∃ V : X.Opens, IsAffineOpen V ∧ Nonempty V.toScheme ∧ IsIntegral V.toScheme := by
  let x : X := Classical.choice inferInstance
  obtain ⟨O, hO, ⟨y, hy⟩, hOsub⟩ :=
    NoetherianSpace.exists_isOpen_nonempty_subset_irreducibleComponent
      (irreducibleComponent x) (irreducibleComponent_mem_irreducibleComponents x)
  obtain ⟨V, hV, hyV, hVO⟩ :=
    exists_isAffineOpen_mem_and_subset (U := ⟨O, hO⟩) hy
  have hVirr : IsIrreducible (V : Set X) :=
    ⟨⟨y, hyV⟩, (irreducibleComponent_mem_irreducibleComponents x).1.2.open_subset
      V.isOpen (hVO.trans hOsub)⟩
  have : IrreducibleSpace V.toScheme := Subtype.irreducibleSpace hVirr
  exact ⟨V, hV, ⟨⟨y, hyV⟩⟩, isIntegral_of_irreducibleSpace_of_isReduced _⟩

/-- An affine quasi-finite finite-type morphism over a Noetherian base
admits an actual finite constructible locally closed partition on which
the literal original base-changed structural maps are finite. -/
theorem exists_finitePartition_of_isAffineHom_of_noetherian
    {U X : Scheme.{u}} [IsNoetherian X]
    (f : U ⟶ X) [IsAffineHom f] [LocallyQuasiFinite f] [LocallyOfFiniteType f] :
    ∃ p : FiniteLocallyClosedPartition X,
      ∀ i, IsFinite (pullback.snd f (p.inclusion i)) := by
  let P (Z : Closeds X) : Prop := ∀ (Y : Scheme.{u}) (j : Y ⟶ X),
    IsClosedImmersion j → IsReduced Y → Set.range j = (Z : Set X) →
      ∃ p : FiniteLocallyClosedPartition Y,
        ∀ i, IsFinite (pullback.snd f (p.inclusion i ≫ j))
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
      let fY := pullback.snd f j
      have : IsAffineHom fY := MorphismProperty.pullback_snd f j inferInstance
      let fV := pullback.snd fY V.ι
      have : IsAffineHom fV := MorphismProperty.pullback_snd fY V.ι inferInstance
      obtain ⟨S, a, ha, hS, hafinite⟩ :=
        exists_nonempty_finite_open_of_isAffineHom fV
      have : IsOpenImmersion a := ha
      have : Nonempty S := hS
      let b : S ⟶ Y := a ≫ V.ι
      have hfiniteb : IsFinite (pullback.snd f (b ≫ j)) := by
        apply (isFinite_pullback_snd_comp_iff f j b).mpr
        exact (isFinite_pullback_snd_comp_iff fY V.ι a).mpr hafinite
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
      suffices ∀ i : Option (Fin p.count), IsFinite (pullback.snd f
          (FiniteLocallyClosedPartition.attachOpenInclusion b p i ≫ j)) by
        intro i
        exact this ((Fintype.equivFin (Option (Fin p.count))).symm i)
      intro i
      cases i with
      | none => exact hfiniteb
      | some i =>
        change IsFinite (pullback.snd f ((p.inclusion i ≫ I.subschemeι) ≫ j))
        rw [Category.assoc]
        exact hp i
    · have : IsEmpty Y := not_nonempty_iff.mp hY
      refine ⟨FiniteLocallyClosedPartition.singleton Y, ?_⟩
      intro i
      change IsFinite (pullback.snd f (𝟙 Y ≫ j))
      have : IsEmpty ↑(pullback f (𝟙 Y ≫ j)) :=
        ⟨fun x => isEmptyElim (pullback.snd f (𝟙 Y ≫ j) x)⟩
      infer_instance
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
