/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.RationalMap.QuasiDomination.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion

/-!
# Recovering a partial map to an immersed target

An actual ambient extension of a map to an immersed target restricts to the
inverse image of the target's canonical coborder open. Schematic density then
factors that restriction through the original target. Its graph is closed if
the ambient target is separated. No projective-resolution assertion is assumed
or hidden in a provider: the input is the actual ambient map and its triangle.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory Limits TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme.QuasiDomination

variable {B U Y P S : Scheme.{u}} (F : B ⟶ P) (e : Y ⟶ P) [IsImmersion e]
  (j : U ⟶ B) (g : U ⟶ Y) (w : j ≫ F = g ≫ e)

/-- The domain is the literal inverse image of the canonical target open. -/
abbrev immersionExtensionDomain : B.Opens := F ⁻¹ᵁ e.coborderRange

include w in
/-- The original source lands in the extension domain, by the actual ambient triangle. -/
lemma range_subset_immersionExtensionDomain :
    Set.range j ⊆ Set.range (immersionExtensionDomain F e).ι := by
  rintro _ ⟨u, rfl⟩
  refine ⟨⟨j u, ?_⟩, rfl⟩
  change F (j u) ∈ e.coborderRange
  have hw := congrArg (fun a => a u) w
  simp only [Hom.comp_apply] at hw
  rw [hw]
  exact subset_coborder ⟨g u, rfl⟩

/-- The actual original source map into the extension domain. -/
def immersionExtensionSource : U ⟶ (immersionExtensionDomain F e).toScheme :=
  IsOpenImmersion.lift (immersionExtensionDomain F e).ι j
    (range_subset_immersionExtensionDomain F e j g w)

@[reassoc (attr := simp)]
lemma immersionExtensionSource_ι :
    immersionExtensionSource F e j g w ≫ (immersionExtensionDomain F e).ι = j :=
  IsOpenImmersion.lift_fac _ _ _

/-- The original-source lift is exactly a flat base change of the original
schematically dominant map. -/
instance immersionExtensionSource_isSchemeTheoreticallyDominant
    [QuasiCompact j] [IsSchemeTheoreticallyDominant j] :
    IsSchemeTheoreticallyDominant (immersionExtensionSource F e j g w) :=
  IsSchemeTheoreticallyDominant.of_isPullback
    (IsOpenImmersion.isPullback_lift_id j (immersionExtensionDomain F e).ι
      (range_subset_immersionExtensionDomain F e j g w)).flip

/-- Compatibility with the original closed immersion in the coborder open. -/
lemma immersionExtensionSource_restrict :
    immersionExtensionSource F e j g w ≫ (F ∣_ e.coborderRange) = g ≫ e.liftCoborder := by
  apply (cancel_mono e.coborderRange.ι).mp
  simpa using w

/-- Schematic density constructs the map to the original immersed target. -/
def immersionExtension [QuasiCompact j] [IsSchemeTheoreticallyDominant j] :
    (immersionExtensionDomain F e).toScheme ⟶ Y :=
  closedTargetLift (immersionExtensionSource F e j g w) e.liftCoborder
    (F ∣_ e.coborderRange) g (immersionExtensionSource_restrict F e j g w)

@[reassoc (attr := simp)]
lemma immersionExtension_liftCoborder [QuasiCompact j] [IsSchemeTheoreticallyDominant j] :
    immersionExtension F e j g w ≫ e.liftCoborder = F ∣_ e.coborderRange :=
  closedTargetLift_comp _ _ _ _ _

/-- The recovered map has the literal original ambient extension. -/
@[reassoc (attr := simp)]
lemma immersionExtension_comp [QuasiCompact j] [IsSchemeTheoreticallyDominant j] :
    immersionExtension F e j g w ≫ e = (immersionExtensionDomain F e).ι ≫ F := by
  calc
    immersionExtension F e j g w ≫ e =
        (immersionExtension F e j g w ≫ e.liftCoborder) ≫ e.coborderRange.ι := by
      simpa only [Category.assoc] using
        congrArg (fun a => immersionExtension F e j g w ≫ a) e.liftCoborder_ι.symm
    _ = (immersionExtensionDomain F e).ι ≫ F := by
      rw [immersionExtension_liftCoborder, morphismRestrict_ι]

/-- The recovered map retains the original map on the original source. -/
@[reassoc (attr := simp)]
lemma source_immersionExtension [QuasiCompact j] [IsSchemeTheoreticallyDominant j] :
    immersionExtensionSource F e j g w ≫ immersionExtension F e j g w = g :=
  comp_closedTargetLift _ _ _ _ _

include w in
/-- The extension domain is dense in the original source scheme. -/
lemma immersionExtensionDomain_dense [QuasiCompact j] [IsSchemeTheoreticallyDominant j] :
    Dense (immersionExtensionDomain F e : Set B) := by
  have h : Set.range j ⊆ (immersionExtensionDomain F e : Set B) := by
    intro b hb
    obtain ⟨a, rfl⟩ := range_subset_immersionExtensionDomain F e j g w hb
    exact a.property
  exact j.denseRange.mono h

variable (p : P ⟶ S)

/-- The recovered map lies over the original ambient structural morphism. -/
lemma immersionExtension_over [QuasiCompact j] [IsSchemeTheoreticallyDominant j] :
    (immersionExtensionDomain F e).ι ≫ (F ≫ p) = immersionExtension F e j g w ≫ (e ≫ p) := by
  simp only [← Category.assoc, immersionExtension_comp]

/-- The literal graph into the product with the original immersed target. -/
def immersionExtensionGraph [QuasiCompact j] [IsSchemeTheoreticallyDominant j] :
    (immersionExtensionDomain F e).toScheme ⟶ pullback (F ≫ p) (e ≫ p) :=
  pullback.lift (immersionExtensionDomain F e).ι (immersionExtension F e j g w)
    (immersionExtension_over F e j g w p)

/-- The canonical map of products induced by the original coborder factorization. -/
def immersionExtensionProductMap :
    pullback (F ≫ p) (e ≫ p) ⟶ pullback (F ≫ p) (e.coborderRange.ι ≫ p) :=
  pullback.map (F ≫ p) (e ≫ p) (F ≫ p) (e.coborderRange.ι ≫ p)
    (𝟙 B) e.liftCoborder (𝟙 S) (by simp) (by simp)

instance immersionExtensionProductMap_mono : Mono (immersionExtensionProductMap F e p) where
  right_cancellation {Z} a b hab := by
    apply pullback.hom_ext
    · simpa [immersionExtensionProductMap] using
        congrArg (fun t => t ≫ pullback.fst (F ≫ p) (e.coborderRange.ι ≫ p)) hab
    · apply (cancel_mono e.liftCoborder).mp
      simpa [immersionExtensionProductMap] using
        congrArg (fun t => t ≫ pullback.snd (F ≫ p) (e.coborderRange.ι ≫ p)) hab

/-- The recovered graph is the actual pullback of the ambient restricted graph. -/
lemma isPullback_immersionExtensionGraph [QuasiCompact j] [IsSchemeTheoreticallyDominant j] :
    IsPullback (immersionExtensionGraph F e j g w p) (𝟙 _)
      (immersionExtensionProductMap F e p) (restrictTargetGraph F p e.coborderRange) := by
  apply IsPullback.of_vert_isIso_mono
  constructor
  apply pullback.hom_ext <;>
    simp [immersionExtensionGraph, immersionExtensionProductMap]

/-- In a separated ambient target the recovered partial map has closed graph. -/
instance immersionExtensionGraph_isClosedImmersion [QuasiCompact j]
    [IsSchemeTheoreticallyDominant j] [IsSeparated p] :
    IsClosedImmersion (immersionExtensionGraph F e j g w p) :=
  MorphismProperty.of_isPullback (isPullback_immersionExtensionGraph F e j g w p).flip
    inferInstance

end AlgebraicGeometry.Scheme.QuasiDomination
