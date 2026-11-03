/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Normalization.GenericFiniteEtale.SmoothRelativePurityLocus
public import Aglib.AlgebraicGeometry.Spec.SmoothCompletionClosedFiberGeneric

/-! # The original normalization open contains the actual completion point

The original section supplies a point of the etale open after the actual
base change. Geometric irreducibility supplies density in that closed fibre.
The original affine-chart completion map is flat, hence its same extended
maximal-ideal point maps into that open. No membership assumption, normality
of the new base, or second normalization is introduced.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits IsLocalRing MvPowerSeries

namespace AlgebraicGeometry.Scheme

universe u

/-- Completion on the actual affine chart maps its original power-series
closed-fibre generic point into the original section-containing open. The
argument uses the fibre of the actual base change, not a separate chart-fibre
model or an assumed point of the open. -/
theorem completionPoint_mem_sectionOpen_of_baseChange
    {X S : Scheme.{u}} (p : X ⟶ S) [GeometricallyIrreducible p]
    (s : S ⟶ X) (hs : s ≫ p = 𝟙 S)
    (E : X.Opens) (hE : Set.range s ⊆ E)
    (R B : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    [CommRing B] [Algebra R B] [IsNoetherianRing B]
    (a : Spec (.of R) ⟶ S)
    (i : Spec (.of B) ⟶ pullback p a) [IsOpenImmersion i]
    (hi : i ≫ pullback.snd p a = Spec.algebraMap R B)
    (ε : B →ₐ[R] R) (σ : Type)
    (e : MvPowerSeries σ R ≃ₐ[R] AdicCompletion (RingHom.ker ε.toRingHom) B) :
    (Spec.map (CommRingCat.ofHom (smoothCompletionPowerSeriesMap ε σ e).toRingHom) ≫
      i ≫ pullback.fst p a) (powerSeriesClosedFiberPoint σ R) ∈ E := by
  let pT := pullback.snd p a
  let : GeometricallyIrreducible pT :=
    inferInstanceAs (GeometricallyIrreducible (pullback.snd p a))
  let : IrreducibleSpace (pT.fiber (closedPoint R)) :=
    GeometricallyIrreducible.geometrically_irreducibleSpace (f := pT)
      ((Spec (.of R)).fromSpecResidueField (closedPoint R))
      (pT.fiberι (closedPoint R)) (pT.fiberToSpecResidueField (closedPoint R))
      (IsPullback.of_hasPullback pT
        ((Spec (.of R)).fromSpecResidueField (closedPoint R)))
  let sT : Spec (.of R) ⟶ pullback p a :=
    pullback.lift (a ≫ s) (𝟙 _) (by
      simp only [Category.assoc, hs, Category.comp_id, Category.id_comp])
  have hsT : sT ≫ pT = 𝟙 _ := pullback.lift_snd _ _ _
  have hsX : sT ≫ pullback.fst p a = a ≫ s := pullback.lift_fst _ _ _
  let ET := pullback.fst p a ⁻¹ᵁ E
  have hET : Set.range sT ⊆ ET := by
    rintro z ⟨t, rfl⟩
    change pullback.fst p a (sT t) ∈ E
    have he := congrArg (fun k => k t) hsX
    simp only [Hom.comp_apply] at he
    rw [he]
    exact hE ⟨a t, rfl⟩
  have hnonempty : (pT.fiberι (closedPoint R) ⁻¹' (ET : Set ↥(pullback p a))).Nonempty :=
    (dense_fiber_preimage_of_section_range_subset pT sT hsT ET hET
      (closedPoint R)).nonempty
  let φ := smoothCompletionPowerSeriesMap ε σ e
  let c := Spec.map (CommRingCat.ofHom φ.toRingHom)
  let : Flat c := Flat.SpecMap_iff.mpr (smoothCompletionPowerSeriesMap_flat ε σ e)
  let g := c ≫ i
  have hg : g ≫ pT =
      Spec.map (CommRingCat.ofHom (C : R →+* MvPowerSeries σ R)) := by
    change (c ≫ i) ≫ pullback.snd p a = _
    rw [Category.assoc, hi]
    change Spec.map _ ≫ Spec.map _ = _
    rw [← Spec.map_comp]
    apply congrArg Spec.map
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro r
    exact φ.commutes r
  have hm := PowerSeriesClosedFiber.image_mem_open σ R pT g hg ET hnonempty
  change pullback.fst p a (g (powerSeriesClosedFiberPoint σ R)) ∈ E at hm
  simpa only [g, Hom.comp_apply] using hm

namespace FiniteEtale.GenericNormalization.OpenRecovery

/-- The same original normalization's canonical etale open contains the
actual chart-completion point after the specified base change. Normality is
used only on the original base and original normalization, never imposed on
R or B. This is the membership input to the existing conditional effectivity
producer, not yet descent of the same finite algebra or full relative purity. -/
theorem etaleTargetOpen_completionPoint_mem
    (A : Type u) [CommRing A] [IsDomain A] [IsLocalRing A]
    [IsNoetherianRing A] [IsIntegrallyClosed A]
    {X U : Scheme.{u}} [IsIntegral X] [IsIntegral U]
    (p : X ⟶ Spec (.of A)) [Smooth p] [GeometricallyConnected p]
    (s : Spec (.of A) ⟶ X) (hs : s ≫ p = 𝟙 _)
    (W : (Spec (.of A)).Opens) [Nonempty W]
    (j : U ⟶ X) [IsOpenImmersion j]
    (hj : Set.range j = p ⁻¹' (W : Set (Spec (.of A))))
    (N : ℕ) (hN : 0 < N) (hunit : IsUnit (N : A))
    (Y : FiniteEtale U) [IsIntegral Y.obj.left]
    [CategoryTheory.PreGaloisCategory.IsGalois Y] (hcard : Nat.card (Aut Y) ∣ N)
    (a : Spec (.of A) ⟶ (genericMap j Y.obj.hom).normalization)
    (ha : a ≫ (genericMap j Y.obj.hom).fromNormalization = s)
    (hf : IsClosedMap (genericMap j Y.obj.hom).fromNormalization)
    (R B : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    [CommRing B] [Algebra R B] [IsNoetherianRing B]
    (b : Spec (.of R) ⟶ Spec (.of A))
    (i : Spec (.of B) ⟶ pullback p b) [IsOpenImmersion i]
    (hi : i ≫ pullback.snd p b = Spec.algebraMap R B)
    (ε : B →ₐ[R] R) (σ : Type)
    (e : MvPowerSeries σ R ≃ₐ[R] AdicCompletion (RingHom.ker ε.toRingHom) B) :
    (Spec.map (CommRingCat.ofHom (smoothCompletionPowerSeriesMap ε σ e).toRingHom) ≫
      i ≫ pullback.fst p b) (powerSeriesClosedFiberPoint σ R) ∈
        (genericMap j Y.obj.hom).fromNormalization.etaleTargetOpen hf := by
  let : GeometricallyIntegral p :=
    geometricallyIntegral_of_smooth_of_geometricallyConnected p
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian p
  let (x : X) : IsIntegrallyClosed (X.presheaf.stalk x) :=
    (normalStalks_of_smooth_normalBase A p x).2
  let f := (genericMap j Y.obj.hom).fromNormalization
  let : IsFinite f := fromNormalization_isFinite j Y.obj.hom
  have het := etaleAt_smoothLocal_baseOpen_section A p s hs W j hj
    N hN hunit Y hcard a ha
  have hsection : Set.range s ⊆ f.etaleTargetOpen hf :=
    range_subset_etaleTargetOpen_of_section_etaleAt j Y s a ha het
  exact completionPoint_mem_sectionOpen_of_baseChange p s hs (f.etaleTargetOpen hf)
    hsection R B b i hi ε σ e

end FiniteEtale.GenericNormalization.OpenRecovery
end AlgebraicGeometry.Scheme
