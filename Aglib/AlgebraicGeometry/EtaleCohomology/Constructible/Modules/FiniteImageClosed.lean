/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.Modules.FiniteImageClosedComparison
public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.Modules.ClosureConstructibleSums
public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.Modules.Pullback
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation

/-! # Constructible original direct image along a finitely presented closed immersion

The actual source strata, followed by the original closed inclusion, and its
open complement form the partition. Finite base change identifies the original
restriction on each closed stratum, and gives zero on the open complement.
No finiteness of the underlying additive groups or coefficient Noetherianity
is assumed. Finite presentation is used only to make stratum images constructible.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Constructible.Modules

universe u r

attribute [local instance] hasSheafifyLarge ModuleCat.Sheaf.hasSheafify

variable {R : Type r} [CommRing R]

/-- An actual global source partition gives a global partition of its closed
direct image when the original closed inclusion preserves constructible sets. -/
theorem nonempty_finiteImageClosedPartition_of_constructible_images {Z X : Scheme.{u}}
    (i : Z ⟶ X) [IsClosedImmersion i]
    (himage : ∀ s : Set Z, Topology.IsConstructible s →
      Topology.IsConstructible (i '' s))
    (F : ModuleSheaf R Z) (t : ConstructiblePartition F) :
    Nonempty (ConstructiblePartition ((moduleDirectImage R i).obj F)) := by
  classical
  let U : X.Opens := ⟨(Set.range i)ᶜ, i.isClosedEmbedding.isClosed_range.isOpen_compl⟩
  let S : Option (Fin t.count) → Scheme.{u}
    | none => U.toScheme
    | some k => t.stratum k
  let f : ∀ k, S k ⟶ X
    | none => U.ι
    | some k => t.inclusion k ≫ i
  have hf (k) : IsImmersion (f k) := by
    cases k with
    | none => exact inferInstanceAs (IsImmersion U.ι)
    | some k =>
      have := t.immersion k
      exact inferInstanceAs (IsImmersion (t.inclusion k ≫ i))
  have hc (k) : Topology.IsConstructible (Set.range (f k)) := by
    cases k with
    | none =>
      change Topology.IsConstructible (Set.range U.ι)
      rw [U.range_ι]
      change Topology.IsConstructible ((Set.range i)ᶜ)
      apply Topology.IsConstructible.compl
      simpa only [Set.image_univ] using himage Set.univ Topology.IsConstructible.univ
    | some k =>
      change Topology.IsConstructible (Set.range (i ∘ t.inclusion k))
      rw [Set.range_comp]
      exact himage _ (t.constructible_range k)
  have hd : Pairwise fun k l => Disjoint (Set.range (f k)) (Set.range (f l)) := by
    intro k l hkl
    cases k with
    | none =>
      cases l with
      | none => exact False.elim (hkl rfl)
      | some l =>
        apply Set.disjoint_left.mpr
        rintro x ⟨y, rfl⟩ ⟨z, hz⟩
        exact y.property ⟨t.inclusion l z, hz⟩
    | some k =>
      cases l with
      | none =>
        apply Set.disjoint_left.mpr
        rintro x ⟨z, rfl⟩ ⟨y, hy⟩
        exact y.property ⟨t.inclusion k z, hy.symm⟩
      | some l =>
        apply Set.disjoint_left.mpr
        rintro x ⟨y, rfl⟩ ⟨z, hz⟩
        have heq : t.inclusion l z = t.inclusion k y := i.isClosedEmbedding.injective hz
        exact Set.disjoint_left.mp (t.disjoint (fun h => hkl (congrArg some h)))
          ⟨y, rfl⟩ ⟨z, heq⟩
  have hcover : ∀ x : X, ∃ k, ∃ y : S k, f k y = x := by
    intro x
    by_cases hx : x ∈ Set.range i
    · obtain ⟨z, rfl⟩ := hx
      obtain ⟨k, y, hy⟩ := t.covers z
      exact ⟨some k, y, by change i (t.inclusion k y) = i z; rw [hy]⟩
    · exact ⟨none, ⟨x, hx⟩, rfl⟩
  have hlc (k) : IsFiniteTypeLocallyConstant
      ((moduleInverseImage R (f k)).obj ((moduleDirectImage R i).obj F)) := by
    cases k with
    | none =>
      have hz : IsZero ((moduleInverseImage R U.ι).obj ((moduleDirectImage R i).obj F)) :=
        finiteImage_isZero_pullback_of_disjoint R i U.ι
          (by rw [U.range_ι]; exact disjoint_compl_right) F
      exact (isFiniteTypeLocallyConstant_iff_of_iso hz.isoZero).mpr
        (isFiniteTypeLocallyConstant_zero _)
    | some k =>
      let e := (moduleInverseImageComp R i (t.inclusion k)).app
          ((moduleDirectImage R i).obj F) ≪≫
        (moduleInverseImage R (t.inclusion k)).mapIso (finiteImageClosedRestrictionIso R i F)
      exact (isFiniteTypeLocallyConstant_iff_of_iso e).mpr (t.locally_constant k)
  let p := FiniteLocallyClosedPartition.ofFintype S f hf hc hd hcover
  exact ⟨{ toFiniteLocallyClosedPartition := p
           locally_constant := fun k =>
             hlc ((Fintype.equivFin (Option (Fin t.count))).symm k) }⟩

/-- Finite presentation supplies the constructible-image condition by
Chevalley, with no condition on the coefficient ring. -/
theorem nonempty_finiteImageClosedPartition {Z X : Scheme.{u}}
    [CompactSpace X] [QuasiSeparatedSpace X]
    (i : Z ⟶ X) [IsClosedImmersion i] [LocallyOfFinitePresentation i]
    (F : ModuleSheaf R Z) (t : ConstructiblePartition F) :
    Nonempty (ConstructiblePartition ((moduleDirectImage R i).obj F)) :=
  nonempty_finiteImageClosedPartition_of_constructible_images i
    (fun _ hs => i.isConstructible_image hs) F t

/-- A surjective closed immersion transports constructible strata without
finite presentation, using its original homeomorphism on underlying spaces. -/
theorem nonempty_finiteImageSurjectiveClosedPartition {Z X : Scheme.{u}}
    (i : Z ⟶ X) [IsClosedImmersion i] [Surjective i]
    (F : ModuleSheaf R Z) (t : ConstructiblePartition F) :
    Nonempty (ConstructiblePartition ((moduleDirectImage R i).obj F)) := by
  apply nonempty_finiteImageClosedPartition_of_constructible_images i ?_ F t
  intro s hs
  apply hs.image_of_isClosedEmbedding i.isClosedEmbedding
  rw [Set.range_eq_univ.mpr i.surjective, Set.compl_univ]
  exact IsRetrocompact.empty

/-- Over an affine target, actual constructibility supplies the source
partition needed for closed finite-presentation direct image. -/
theorem isConstructible_closedDirectImage_of_isAffine {Z X : Scheme.{u}} [IsAffine X]
    (i : Z ⟶ X) [IsClosedImmersion i] [LocallyOfFinitePresentation i]
    {F : ModuleSheaf R Z} (hF : IsConstructible F) :
    IsConstructible ((moduleDirectImage R i).obj F) := by
  have : IsAffine Z := isAffine_of_isAffineHom i
  obtain ⟨t⟩ := nonempty_constructiblePartition hF
  obtain ⟨p⟩ := nonempty_finiteImageClosedPartition i F t
  intro U
  have : IsAffine U.1.toScheme := U.property
  exact ⟨p.baseChange U.1.ι⟩

/-- Original module direct image along any finitely presented closed immersion
preserves genuine module constructibility on an arbitrary base. -/
theorem isConstructible_closedDirectImage {Z X : Scheme.{u}}
    (i : Z ⟶ X) [IsClosedImmersion i] [LocallyOfFinitePresentation i]
    {F : ModuleSheaf R Z} (hF : IsConstructible F) :
    IsConstructible ((moduleDirectImage R i).obj F) := by
  intro U
  have : IsAffine U.1.toScheme := U.property
  let e := finiteImageBaseChangeIso R i (pullback.snd i U.1.ι) U.1.ι
    (pullback.fst i U.1.ι) (IsPullback.of_hasPullback i U.1.ι)
  have h := isConstructible_closedDirectImage_of_isAffine (pullback.snd i U.1.ι)
    (isConstructible_pullback (pullback.fst i U.1.ι) hF)
  obtain ⟨t⟩ := nonempty_constructiblePartition h
  exact ⟨t.ofIso (e.app F).symm⟩

/-- Surjective closed direct image preserves genuine constructibility,
without finite-presentation or bounded nilpotence hypotheses. -/
theorem isConstructible_surjectiveClosedDirectImage {Z X : Scheme.{u}}
    (i : Z ⟶ X) [IsClosedImmersion i] [Surjective i]
    {F : ModuleSheaf R Z} (hF : IsConstructible F) :
    IsConstructible ((moduleDirectImage R i).obj F) := by
  intro U
  have : IsAffine U.1.toScheme := U.property
  let j := pullback.snd i U.1.ι
  have : IsAffine (pullback i U.1.ι) := isAffine_of_isAffineHom j
  obtain ⟨t⟩ := nonempty_constructiblePartition
    (isConstructible_pullback (pullback.fst i U.1.ι) hF)
  obtain ⟨p⟩ := nonempty_finiteImageSurjectiveClosedPartition j _ t
  let e := finiteImageBaseChangeIso R i j U.1.ι
    (pullback.fst i U.1.ι) (IsPullback.of_hasPullback i U.1.ι)
  exact ⟨p.ofIso (e.app F).symm⟩

end AlgebraicGeometry.Scheme.EtaleCohomology.Constructible.Modules
