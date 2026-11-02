/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Properties.Normal.PointComponent
public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.Connectedness
public import Aglib.AlgebraicGeometry.Normalization.GenericFiniteEtale.Stalks
public import Aglib.AlgebraicGeometry.Normalization.GenericFiniteEtale.OpenRecovery

/-! # The original open cover inside a pointed normalization component

Dominance of the native normalization map meets every nonempty original
component. Since the original generic source factors through the given open,
its intersection with each integral normal component is nonempty and dense.
No discrete valuation, new field factor or finite prime-localization is used.
-/

@[expose] public noncomputable section

open CategoryTheory

namespace AlgebraicGeometry.Scheme.Hom

universe u

/-- Every nonempty open of the native normalization meets any base open
containing the original source image. The witness comes from that source. -/
theorem exists_toNormalization_mem_open
    {Z X : Scheme.{u}} (q : Z ⟶ X) [QuasiCompact q] [QuasiSeparated q]
    (U : q.normalization.Opens) [Nonempty U]
    (W : X.Opens) (hq : ∀ z, q z ∈ W) :
    ∃ z : Z, q.toNormalization z ∈ U ∧ q.fromNormalization (q.toNormalization z) ∈ W := by
  obtain ⟨x⟩ := ‹Nonempty U›
  obtain ⟨z, hz⟩ := q.toNormalization.denseRange.exists_mem_open U.isOpen ⟨U.ι x, x.property⟩
  refine ⟨z, hz, ?_⟩
  simpa only [← Scheme.Hom.comp_apply, toNormalization_fromNormalization] using hq z

/-- The same intersection is dense in an integral original open component. -/
theorem dense_normalization_open_preimage
    {Z X : Scheme.{u}} (q : Z ⟶ X) [QuasiCompact q] [QuasiSeparated q]
    (U : q.normalization.Opens) [IsIntegral U]
    (W : X.Opens) (hq : ∀ z, q z ∈ W) :
    Dense (U.ι ⁻¹ᵁ q.fromNormalization ⁻¹ᵁ W : Set U) := by
  apply (U.ι ⁻¹ᵁ q.fromNormalization ⁻¹ᵁ W).isOpen.dense
  obtain ⟨z, hz, hw⟩ := exists_toNormalization_mem_open q U W hq
  exact ⟨⟨q.toNormalization z, hz⟩, hw⟩

end AlgebraicGeometry.Scheme.Hom

namespace AlgebraicGeometry.Scheme.FiniteEtale.GenericNormalization.OpenRecovery

universe u

variable {X U E : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
  [∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x)]
  (j : U ⟶ X) [IsOpenImmersion j] [Nonempty U] (p : E ⟶ U) [IsFinite p] [Etale p]

local instance : IsLocallyNoetherian (genericMap j p).normalization := by
  let : IsFinite (genericMap j p).fromNormalization := fromNormalization_isFinite j p
  exact LocallyOfFiniteType.isLocallyNoetherian (genericMap j p).fromNormalization

/-- Normality of the unchanged normalization, including disconnected sources. -/
theorem genericMap_normalStalks : NormalStalks (genericMap j p).normalization := by
  intro x
  have h := stalk_normal_domain X (genericCover j p) x
  exact ⟨h.2, h.1⟩

/-- The original complement is dense in the actual integral component through
the specified normalization point. The original generic map supplies the
source factorization; neither connectedness nor a new field is assumed. -/
theorem dense_pointComponent_open
    (x : (genericMap j p).normalization) :
    let U := normalComponentOpen (genericMap j p).normalization
      (genericMap_normalStalks j p) x
    Dense (U.ι ⁻¹ᵁ (genericMap j p).fromNormalization ⁻¹ᵁ j.opensRange : Set U) := by
  dsimp only
  apply Hom.dense_normalization_open_preimage
  intro z
  rw [genericMap_eq]
  exact ⟨(genericToCover j p ≫ p) z, rfl⟩

omit [IsLocallyNoetherian X] in
/-- The original open-recovery inclusion has exactly the original open image. -/
theorem inclusion_opensRange :
    (inclusion j p).opensRange = (genericMap j p).fromNormalization ⁻¹ᵁ j.opensRange := by
  dsimp only [inclusion]
  rw [Hom.opensRange_comp_of_isIso, Hom.opensRange_pullbackFst]

/-- The component of the unchanged covering source selected by the specified
normalization point is the original preimage open subset. -/
def pointComponentOpen (x : (genericMap j p).normalization) : E.Opens :=
  inclusion j p ⁻¹ᵁ normalComponentOpen (genericMap j p).normalization
    (genericMap_normalStalks j p) x

/-- This same covering-source open is closed. -/
theorem pointComponentOpen_isClosed (x : (genericMap j p).normalization) :
    IsClosed (pointComponentOpen j p x : Set E) :=
  (normalComponentOpen_isClosed _ (genericMap_normalStalks j p) x).preimage
    (inclusion j p).continuous

/-- Nonemptiness is supplied by the original generic source and native
normalization dominance, not by a connectedness assumption. -/
theorem pointComponentOpen_nonempty (x : (genericMap j p).normalization) :
    (pointComponentOpen j p x : Set E).Nonempty := by
  let U := normalComponentOpen (genericMap j p).normalization
    (genericMap_normalStalks j p) x
  obtain ⟨z, hz, hw⟩ := Hom.exists_toNormalization_mem_open (genericMap j p) U j.opensRange (by
    intro z
    rw [genericMap_eq]
    exact ⟨(genericToCover j p ≫ p) z, rfl⟩)
  have hrange : (genericMap j p).toNormalization z ∈ (inclusion j p).opensRange := by
    rw [inclusion_opensRange]
    exact hw
  obtain ⟨y, hy⟩ := hrange
  refine ⟨y, ?_⟩
  change inclusion j p y ∈ U
  rwa [hy]

/-- Integrality holds on the same original clopen subcover. -/
instance pointComponentOpen_isIntegral (x : (genericMap j p).normalization) :
    IsIntegral (pointComponentOpen j p x) := by
  let : IsReduced (genericMap j p).normalization := (genericMap_normalStalks j p).isReduced
  let : IsReduced E := isReduced_of_isOpenImmersion (inclusion j p)
  have hne := pointComponentOpen_nonempty j p x
  let : IrreducibleSpace (pointComponentOpen j p x) :=
    isIrreducible_iff_irreducibleSpace.mp ⟨hne,
      (isIrreducible_irreducibleComponent (x := x)).2.preimage
        (inclusion j p).isOpenEmbedding⟩
  exact isIntegral_of_irreducibleSpace_of_isReduced _

/-- The actual finite-etale subcover, with its unchanged clopen inclusion. -/
def pointComponentCover (x : (genericMap j p).normalization) : FiniteEtale U :=
  Connectedness.clopenCover (FiniteEtale.mk p) (pointComponentOpen j p x)
    (pointComponentOpen_isClosed j p x)

/-- The original categorical inclusion of the selected component. -/
def pointComponentCoverι (x : (genericMap j p).normalization) :
    pointComponentCover j p x ⟶ FiniteEtale.mk p :=
  Connectedness.clopenCoverι (FiniteEtale.mk p) (pointComponentOpen j p x)
    (pointComponentOpen_isClosed j p x)

/-- The subcover inclusion is literally the original open-subscheme map. -/
theorem pointComponentCoverι_left (x : (genericMap j p).normalization) :
    (pointComponentCoverι j p x).hom.left = (pointComponentOpen j p x).ι := rfl

/-- The selected actual subcover is connected, because its original source
open has already been proved integral. -/
instance pointComponentCover_connected (x : (genericMap j p).normalization) :
    CategoryTheory.PreGaloisCategory.IsConnected (pointComponentCover j p x) := by
  let : ConnectedSpace (pointComponentCover j p x).obj.left :=
    inferInstanceAs (ConnectedSpace (pointComponentOpen j p x))
  exact Connectedness.categoricalConnected_of_connectedSpace _

/-- The actual component inclusion is a monomorphism. -/
instance pointComponentCoverι_mono (x : (genericMap j p).normalization) :
    Mono (pointComponentCoverι j p x) := by
  apply (forgetToScheme U).mono_of_mono_map
  change Mono (pointComponentOpen j p x).ι
  infer_instance

end AlgebraicGeometry.Scheme.FiniteEtale.GenericNormalization.OpenRecovery
