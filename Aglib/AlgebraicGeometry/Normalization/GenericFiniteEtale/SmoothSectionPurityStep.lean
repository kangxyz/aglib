/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Morphisms.Smooth.SectionPurityStep
public import Aglib.AlgebraicGeometry.Morphisms.Smooth.NormalStalks
public import Aglib.AlgebraicGeometry.Normalization.GenericFiniteEtale.GaloisSectionNeighborhood
public import Aglib.AlgebraicGeometry.Normalization.GenericFiniteEtale.PointComponent

/-! # The original Galois normalization in the smooth-section purity step

Original Galois fibre transitivity upgrades the lower-dimensional selected
section points to whole punctured-section fibres. The Hartogs step then gives
an actual etale target open containing the unchanged whole local section.
Codimension-one and lower-dimensional section inputs remain explicit.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.PreGaloisCategory

namespace AlgebraicGeometry.Scheme.FiniteEtale.GenericNormalization.OpenRecovery

universe u

/-- The explicit local induction step for the unchanged Galois normalization.
The same finite map is etale on a target open containing the original section. -/
theorem exists_smoothSection_etaleNeighborhood_of_codimensionOne_of_puncturedSection
    (A : Type u) [CommRing A] [IsDomain A] [IsLocalRing A]
    [IsNoetherianRing A] [IsIntegrallyClosed A]
    {X U : Scheme.{u}} [IsIntegral X] [IsIntegral U]
    (p : X ⟶ Spec (.of A)) [Smooth p]
    (j : U ⟶ X) [IsOpenImmersion j]
    (Y : Scheme.FiniteEtale U) [IsIntegral Y.obj.left] [IsGalois Y]
    (s : Spec (.of A) ⟶ X) (hs : s ≫ p = 𝟙 _)
    (a : Spec (.of A) ⟶ (genericMap j Y.obj.hom).normalization)
    (ha : a ≫ (genericMap j Y.obj.hom).fromNormalization = s)
    (hdim : 2 ≤ ringKrullDim A)
    (hheight : ∀ x : X, Order.coheight x = 1 →
      ∀ y : (genericMap j Y.obj.hom).normalization,
        (genericMap j Y.obj.hom).fromNormalization y = x →
        (genericMap j Y.obj.hom).fromNormalization.etaleAt y)
    (hpuncture : ∀ x : Spec (.of A), x ∈ puncturedSpecOpen A →
      (genericMap j Y.obj.hom).fromNormalization.etaleAt (a x)) :
    ∃ W : X.Opens, Set.range s ⊆ W ∧
      Etale ((genericMap j Y.obj.hom).fromNormalization ∣_ W) := by
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian p
  let (x : X) : IsIntegrallyClosed (X.presheaf.stalk x) :=
    (normalStalks_of_smooth_normalBase A p x).2
  let q := genericMap j Y.obj.hom
  let f := q.fromNormalization
  let : IsIntegral (genericCover j Y.obj.hom).obj.left :=
    IsIntegral.of_isIso (originalFieldSpectrumIso j Y).hom
  let : IsIntegral q.normalization := inferInstance
  let (y : q.normalization) : IsIntegrallyClosed (q.normalization.presheaf.stalk y) :=
    (genericMap_normalStalks j Y.obj.hom y).2
  let : IsFinite f := fromNormalization_isFinite j Y.obj.hom
  let : IsDominant Y.obj.hom := GenericGalois.dominant Y
  let : IsDominant j := Scheme.isDominant_of_isOpenImmersion j
  let : IsDominant q := by
    let : IsDominant ((originalFieldSpectrumIso j Y).hom ≫ q) := by
      rw [originalFieldSpectrumIso_hom_genericMap]
      infer_instance
    exact IsDominant.of_comp (originalFieldSpectrumIso j Y).hom q
  let : IsDominant f := by
    let : IsDominant (q.toNormalization ≫ f) := by
      change IsDominant (q.toNormalization ≫ q.fromNormalization)
      rw [Hom.toNormalization_fromNormalization]
      infer_instance
    exact IsDominant.of_comp q.toNormalization f
  obtain ⟨V, hV, hc, _⟩ := exists_isAffineOpen_mem_and_subset
    (show s (IsLocalRing.closedPoint A) ∈ (⊤ : X.Opens) from trivial)
  have hVsection := localSection_range_subset s V hc
  have hp : ∀ x : Spec (.of A), x ∈ puncturedSpecOpen A →
      ∀ y : q.normalization, f y = s x → f.etaleAt y := by
    intro x hx y hy
    have he : f (a x) = s x := congrArg (fun g : Spec (.of A) ⟶ X => g x) ha
    exact genericNormalization_etaleAt_of_image_eq_in_affineOpen j Y V hV
      (a x) y (he.symm ▸ hVsection ⟨x, rfl⟩) (he.trans hy.symm) (hpuncture x hx)
  have het := Hom.etaleAt_liftedSection_of_codimensionOne_of_puncturedSection
    A p f s hs a ha hdim hheight hp
  refine ⟨f.etaleTargetOpen f.isClosedMap, ?_,
    f.etale_restrict_etaleTargetOpen f.isClosedMap⟩
  exact range_subset_etaleTargetOpen_of_section_etaleAt j Y s a ha het

end AlgebraicGeometry.Scheme.FiniteEtale.GenericNormalization.OpenRecovery
