/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.GradedAlgebra.HomogeneousLocalization.BaseChange
public import Mathlib.Algebra.Category.Ring.Constructions
public import Aglib.AlgebraicGeometry.ProjectiveSpectrum.DegreeOneEmbedding
public import Aglib.AlgebraicGeometry.Gluing.SourceOpenCover
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Functor
public import Mathlib.AlgebraicGeometry.Pullbacks

/-!
# Actual scalar base change of Proj on an original degree-one cover

The native graded coefficient map induces the original Proj morphism. Its
original Away maps are identified with the constructed full tensor chart
isomorphisms, giving actual ring pushouts and scheme pullbacks. The native
open-cover criterion glues the specified degree-one chart squares. Both
projections of the resulting isomorphism to the literal pullback are retained.

The degree-one cover condition is algebraic data. No flatness, domain,
Noetherianity or projectivity assumption is introduced. Rees consumers
supply the cover by their existing original degree-one ideal elements.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Graded TensorProduct

universe u

namespace HomogeneousLocalization.Away

variable (R : Type u) [CommRing R] {D : Type u} [CommRing D] [Algebra R D]
  (G : ℕ → Submodule R D) [GradedAlgebra G]
  (S : Type u) [CommRing S] [Algebra R S]

/-- The original graded coefficient inclusion into the full tensor algebra. -/
def scalarGradedMap : G →+*ᵍ scalarGrading R G S where
  __ := (Algebra.TensorProduct.includeRight : D →ₐ[R] S ⊗[R] D).toRingHom
  map_mem ha := Submodule.tmul_mem_baseChange_of_mem _ ha

omit [GradedAlgebra G] in
/-- The coefficient map is exactly the original tensor inclusion. -/
@[simp]
theorem scalarGradedMap_apply (a : D) : scalarGradedMap R G S a = 1 ⊗ₜ[R] a := rfl

/-- The tensor comparison has the original native homogeneous-localization map. -/
theorem scalarExtensionEquiv_one_tmul {f : D} (hf : f ∈ G 1) (x : Away G f) :
    letI := scalarAlgebra R G f
    letI := scalarAlgebra S (scalarGrading R G S) (1 ⊗ₜ[R] f)
    scalarExtensionEquiv R G S hf (1 ⊗ₜ[R] x) =
      Away.map (scalarGradedMap R G S) f x := by
  let := scalarAlgebra R G f
  let := scalarAlgebra S (scalarGrading R G S) (1 ⊗ₜ[R] f)
  obtain ⟨n, a, ha, rfl⟩ := Away.mk_surjective G hf x
  have ha' : a ∈ G n := by simpa only [smul_eq_mul, mul_one] using ha
  rw [Away.map_mk]
  exact scalarExtensionEquiv_tmul_mk R G S hf n a ha' 1

/-- The original coefficient and homogeneous-chart maps form an actual ring pushout. -/
theorem scalarMap_isPushout {f : D} (hf : f ∈ G 1) :
    letI := scalarAlgebra R G f
    letI := scalarAlgebra S (scalarGrading R G S) (1 ⊗ₜ[R] f)
    IsPushout (CommRingCat.ofHom (algebraMap R (Away G f)))
      (CommRingCat.ofHom (algebraMap R S))
      (CommRingCat.ofHom (Away.map (scalarGradedMap R G S) f))
      (CommRingCat.ofHom (algebraMap S
        (Away (scalarGrading R G S) (1 ⊗ₜ[R] f)))) := by
  let := scalarAlgebra R G f
  let := scalarAlgebra S (scalarGrading R G S) (1 ⊗ₜ[R] f)
  let e := (scalarExtensionEquiv R G S hf).toRingEquiv.toCommRingCatIso
  refine (CommRingCat.isPushout_tensorProduct R S (Away G f)).flip.of_iso
    (Iso.refl _) (Iso.refl _) (Iso.refl _) e ?_ ?_ ?_ ?_
  · simp
  · simp
  · apply CommRingCat.hom_ext
    apply RingHom.ext
    intro x
    change scalarExtensionEquiv R G S hf (1 ⊗ₜ[R] x) =
      Away.map (scalarGradedMap R G S) f x
    exact scalarExtensionEquiv_one_tmul R G S hf x
  · apply CommRingCat.hom_ext
    apply RingHom.ext
    intro s
    change scalarExtensionEquiv R G S hf (algebraMap S (S ⊗[R] Away G f) s) =
      algebraMap S (Away (scalarGrading R G S) (1 ⊗ₜ[R] f)) s
    exact (scalarExtensionEquiv R G S hf).commutes s

end HomogeneousLocalization.Away

namespace AlgebraicGeometry.Proj.DegreeOneBaseChange

open HomogeneousLocalization.Away

variable (R : Type u) [CommRing R] {D : Type u} [CommRing D] [Algebra R D]
  (G : ℕ → Submodule R D) [GradedAlgebra G]
  (S : Type u) [CommRing S] [Algebra R S]

/-- Scalar extension retains enough original positive homogeneous elements for Proj. -/
theorem scalar_irrelevant_le_map :
    HomogeneousIdeal.irrelevant (scalarGrading R G S) ≤
      (HomogeneousIdeal.irrelevant G).map (scalarGradedMap R G S) := by
  apply toIdeal_le_toIdeal_iff.mp
  rw [HomogeneousIdeal.toIdeal_irrelevant_le]
  intro n hn c hc
  let J : Ideal (S ⊗[R] D) :=
    ((HomogeneousIdeal.irrelevant G).map (scalarGradedMap R G S)).toIdeal
  have h : (G n).baseChange S ≤ J.restrictScalars S := by
    rw [Submodule.baseChange_eq_span, Submodule.span_le]
    intro z hz
    obtain ⟨a, ha, rfl⟩ := Submodule.mem_map.mp hz
    exact Ideal.mem_map_of_mem (scalarGradedMap R G S)
      (HomogeneousIdeal.mem_irrelevant_of_mem G hn ha)
  exact h hc

/-- The actual Proj morphism induced by the original graded coefficient map. -/
def scalarMap : Proj (scalarGrading R G S) ⟶ Proj G :=
  Proj.map (scalarGradedMap R G S) (scalar_irrelevant_le_map R G S)

/-- The original chart coefficient map through the degree-zero component. -/
abbrev coefficientMap (f : D) : R →+* HomogeneousLocalization.Away G f :=
  @algebraMap R (HomogeneousLocalization.Away G f) _ _ (scalarAlgebra R G f)

/-- The original affine chart retains the original coefficient-ring structure map. -/
theorem chart_toSpec {f : D} (hf : f ∈ G 1) :
    Proj.awayι G f hf Nat.zero_lt_one ≫ DegreeOneEmbedding.structureMap G =
      Spec.map (CommRingCat.ofHom (coefficientMap R G f)) := by
  simp only [DegreeOneEmbedding.structureMap, Proj.awayι_toSpecZero_assoc,
    ← Spec.map_comp]
  apply congrArg (fun k : CommRingCat.of R ⟶
    CommRingCat.of (HomogeneousLocalization.Away G f) => Spec.map k)
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro r
  rfl

/-- The spectra of the original chart-ring maps form a cartesian coefficient square. -/
theorem scalarChart_isPullback {f : D} (hf : f ∈ G 1) :
    IsPullback
      (Spec.map (CommRingCat.ofHom (HomogeneousLocalization.Away.map
        (scalarGradedMap R G S) f)))
      (Spec.map (CommRingCat.ofHom (coefficientMap S (scalarGrading R G S) (1 ⊗ₜ[R] f))))
      (Spec.map (CommRingCat.ofHom (coefficientMap R G f)))
      (Spec.map (CommRingCat.ofHom (algebraMap R S))) := by
  let := scalarAlgebra R G f
  let := scalarAlgebra S (scalarGrading R G S) (1 ⊗ₜ[R] f)
  exact isPullback_SpecMap_of_isPushout _ _ _ _ (scalarMap_isPushout R G S hf)

/-- The native homogeneous chart above an original degree-one chart is its open pullback. -/
theorem scalarChart_awayι_isPullback {f : D} (hf : f ∈ G 1) :
    IsPullback
      (Spec.map (CommRingCat.ofHom (HomogeneousLocalization.Away.map
        (scalarGradedMap R G S) f)))
      (Proj.awayι (scalarGrading R G S) (1 ⊗ₜ[R] f)
        (scalarDenominator_mem R G S hf) Nat.zero_lt_one)
      (Proj.awayι G f hf Nat.zero_lt_one)
      (scalarMap R G S) := by
  apply IsOpenImmersion.isPullback _ _ _ _
    (Proj.awayι_comp_map (scalarGradedMap R G S) (scalar_irrelevant_le_map R G S)
      Nat.zero_lt_one f hf)
  rw [Proj.opensRange_awayι, Proj.opensRange_awayι]
  exact Proj.map_preimage_basicOpen (scalarGradedMap R G S)
    (scalar_irrelevant_le_map R G S) (⟨f, hf⟩ : G 1)

variable {κ : Type u}

/-- The original degree-one cover glues the actual scalar-extension chart pullbacks. -/
theorem isPullback_scalarMap (g : κ → D) (hg : ∀ i, g i ∈ G 1)
    (hcover : (HomogeneousIdeal.irrelevant G).toIdeal ≤ Ideal.span (Set.range g)) :
    IsPullback (scalarMap R G S) (DegreeOneEmbedding.structureMap (scalarGrading R G S))
      (DegreeOneEmbedding.structureMap G)
      (Spec.map (CommRingCat.ofHom (algebraMap R S))) := by
  let C := Proj.affineOpenCoverOfIrrelevantLESpan G g hg (fun _ => Nat.zero_lt_one) hcover
  apply Scheme.SourceOpenCover.isPullback_of_openCover_charts
    (scalarMap R G S) (DegreeOneEmbedding.structureMap (scalarGrading R G S))
    (DegreeOneEmbedding.structureMap G) (Spec.map (CommRingCat.ofHom (algebraMap R S)))
    C.openCover
    (fun i => Spec (CommRingCat.of
      (HomogeneousLocalization.Away (scalarGrading R G S) (1 ⊗ₜ[R] g i))))
    (fun i => Proj.awayι (scalarGrading R G S) (1 ⊗ₜ[R] g i)
      (scalarDenominator_mem R G S (hg i)) Nat.zero_lt_one)
    (fun i => Spec.map (CommRingCat.ofHom (HomogeneousLocalization.Away.map
      (scalarGradedMap R G S) (g i))))
  · intro i
    exact scalarChart_awayι_isPullback R G S (hg i)
  · intro i
    change IsPullback _
      (Proj.awayι (scalarGrading R G S) (1 ⊗ₜ[R] g i)
        (scalarDenominator_mem R G S (hg i)) Nat.zero_lt_one ≫
          DegreeOneEmbedding.structureMap (scalarGrading R G S))
      (Proj.awayι G (g i) (hg i) Nat.zero_lt_one ≫ DegreeOneEmbedding.structureMap G) _
    rw [chart_toSpec R G, chart_toSpec S (scalarGrading R G S)]
    exact scalarChart_isPullback R G S (hg i)

/-- The actual scalar map retains the original R/S structural triangle. -/
theorem scalarMap_toSpec (g : κ → D) (hg : ∀ i, g i ∈ G 1)
    (hcover : (HomogeneousIdeal.irrelevant G).toIdeal ≤ Ideal.span (Set.range g)) :
    scalarMap R G S ≫ DegreeOneEmbedding.structureMap G =
      DegreeOneEmbedding.structureMap (scalarGrading R G S) ≫
        Spec.map (CommRingCat.ofHom (algebraMap R S)) :=
  (isPullback_scalarMap R G S g hg hcover).w

/-- The actual Proj over S is the literal pullback of the original Proj over R. -/
def baseChangeIso (g : κ → D) (hg : ∀ i, g i ∈ G 1)
    (hcover : (HomogeneousIdeal.irrelevant G).toIdeal ≤ Ideal.span (Set.range g)) :
    Proj (scalarGrading R G S) ≅
      pullback (DegreeOneEmbedding.structureMap G)
        (Spec.map (CommRingCat.ofHom (algebraMap R S))) :=
  (isPullback_scalarMap R G S g hg hcover).isoPullback

/-- The first projection is the original graded-coefficient Proj map. -/
@[reassoc (attr := simp)]
theorem baseChangeIso_hom_fst (g : κ → D) (hg : ∀ i, g i ∈ G 1)
    (hcover : (HomogeneousIdeal.irrelevant G).toIdeal ≤ Ideal.span (Set.range g)) :
    (baseChangeIso R G S g hg hcover).hom ≫
      pullback.fst (DegreeOneEmbedding.structureMap G)
        (Spec.map (CommRingCat.ofHom (algebraMap R S))) = scalarMap R G S :=
  (isPullback_scalarMap R G S g hg hcover).isoPullback_hom_fst

/-- The second projection is the original structural map to Spec S. -/
@[reassoc (attr := simp)]
theorem baseChangeIso_hom_snd (g : κ → D) (hg : ∀ i, g i ∈ G 1)
    (hcover : (HomogeneousIdeal.irrelevant G).toIdeal ≤ Ideal.span (Set.range g)) :
    (baseChangeIso R G S g hg hcover).hom ≫
      pullback.snd (DegreeOneEmbedding.structureMap G)
        (Spec.map (CommRingCat.ofHom (algebraMap R S))) =
      DegreeOneEmbedding.structureMap (scalarGrading R G S) :=
  (isPullback_scalarMap R G S g hg hcover).isoPullback_hom_snd

end AlgebraicGeometry.Proj.DegreeOneBaseChange
