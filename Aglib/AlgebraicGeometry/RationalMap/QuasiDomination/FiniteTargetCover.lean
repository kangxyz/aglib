/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.RationalMap.QuasiDomination.TargetOpen.Modification
public import Aglib.AlgebraicGeometry.RationalMap.QuasiDomination.TargetOpen.Pullback
public import Aglib.AlgebraicGeometry.RationalMap.QuasiDomination.ModifiedGraph
public import Aglib.AlgebraicGeometry.RationalMap.QuasiDomination.GraphImage
public import Aglib.AlgebraicGeometry.Blowup.AdmissibleSequence.Refinement

/-!
# A quasi-finite original graph image after finite target-chart modifications

The finite affine target cover supplies actual chart modifications. Their
actual sequences have a common admissible refinement. Pulling their closed
graphs to that refinement gives closed ranges with injective projection,
containing the original graph on each target chart. The resulting locally
quasi-finite morphism is the projection of the single original schematic
image, not a product of independently chosen closures.
-/

@[expose] public noncomputable section

open CategoryTheory Limits TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme.QuasiDomination

/-- Finite affine target charts make the original graph-image projection
locally quasi-finite after an actual protected admissible sequence. -/
theorem exists_locallyQuasiFinite_graphImage_modification
    {X Y : Scheme.{u}} [IsNoetherian X]
    (f : Y ⟶ X) [QuasiCompact f] [LocallyOfFiniteType f]
    (U V : X.Opens) (hUV : U ≤ V)
    (g : U.toScheme ⟶ Y) (hg : g ≫ f = U.ι)
    (hclosed : IsClosed ((pullback.fst (𝟙 X) f ⁻¹ᵁ V).ι ⁻¹'
      Set.range (pullback.lift U.ι g (by simpa using hg.symm)))) :
    ∃ (B : Scheme.{u}) (β : B ⟶ X), Blowup.AdmissibleSequence V β ∧
      LocallyQuasiFinite ((modifiedGraph U f g hg β).imageι ≫ pullback.fst β f) := by
  classical
  let : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian f
  let : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace f
  let : IsNoetherian Y := ⟨⟩
  let C : Y.OpenCover := Y.affineCover.finiteSubcover
  let : Fintype C.I₀ := inferInstanceAs (Fintype Y.affineCover.finiteSubcover.I₀)
  let O : C.I₀ → Y.Opens := fun i ↦ (C.f i).opensRange
  have hO : ∀ i, IsAffineOpen (O i) := fun i ↦
    IsAffine.of_isIso (C.f i).isoOpensRange.inv
  have hcover : (⨆ i, O i) = ⊤ := Scheme.OpenCover.iSup_opensRange C
  choose Bi βi Di di hi ki hwi hseq hdi hki hkhi hci using
    fun i ↦ exists_targetOpen_modification f U V hUV g hg hclosed (O i) (hO i)
  obtain ⟨B, β, a₀, hβ, ha₀⟩ :=
    Blowup.AdmissibleSequence.exists_finite_refinement V Bi βi hseq Finset.univ
  let a : ∀ i, B ⟶ Bi i := fun i ↦ a₀ ⟨i, Finset.mem_univ i⟩
  have ha : ∀ i, a i ≫ βi i = β := fun i ↦ ha₀ ⟨i, Finset.mem_univ i⟩
  let : IsProper β := hβ.isProper
  let : IsLocallyNoetherian B := LocallyOfFiniteType.isLocallyNoetherian β
  let : CompactSpace B := QuasiCompact.compactSpace_of_compactSpace β
  let : IsNoetherian B := ⟨⟩
  let : CompactSpace (β ⁻¹ᵁ U).toScheme := by
    change CompactSpace ((β ⁻¹ᵁ U) : Set B)
    infer_instance
  let : IsNoetherian (β ⁻¹ᵁ U).toScheme := ⟨⟩
  let γ := modifiedGraph U f g hg β
  let : ∀ i, IsImmersion (di i) := hdi
  let : ∀ i, IsClosedImmersion (pullback.lift (di i) (hi i) (hwi i)) := hci
  let : ∀ i, IsIso (βi i ∣_ U) := fun i ↦ by
    let : IsIso (βi i ∣_ V) := (hseq i).restrict_isIso
    exact (βi i).isIso_restrict_of_le hUV
  choose c hc hinj hrange using fun i ↦ exists_pulled_targetOpen_graph U f g hg (O i)
    (βi i) β (a i) (ha i) (di i) (hi i) (ki i) (hwi i) (hki i) (hkhi i) γ
    (modifiedGraph_fst U f g hg β) (modifiedGraph_snd U f g hg β)
  let : ∀ i, IsClosedImmersion (c i) := hc
  refine ⟨B, β, hβ, ?_⟩
  exact locallyQuasiFinite_image_projection_of_closed_ranges γ (pullback.fst β f)
    (fun i ↦ pullback.snd β f ⁻¹ᵁ O i)
    ((pullback.snd β f).iSup_preimage_eq_top hcover)
    (fun i ↦ pullback (di i) (a i)) c hrange hinj

end AlgebraicGeometry.Scheme.QuasiDomination
