/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.DiscreteValuationRing.ParameterProjectedResidue
public import Aglib.RingTheory.DiscreteValuationRing.ParameterPoint

/-! # The actual target map after projecting residue parameters

The original point extends over the source denominators because their images
in the constructed residue field are nonzero. Its residue square and scalar
map are proved on original elements, using the same actual parameter values.
-/

@[expose] public noncomputable section

open IsLocalRing MvPolynomial

namespace ParameterLocalization.ProjectedCentre

variable {R S A K ι : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [CommRing S] [IsDomain S] [IsDiscreteValuationRing S] [Algebra R S]
  [IsLocalHom (algebraMap R S)] [CommRing A] [Algebra R A]
  [Field K] [Algebra (ResidueField R) K] [Finite ι]
  (p : R) [Fact (Irreducible p)] (D : Subalgebra (ResidueField R) K)
  (f : A →+* D)
  (hf : f.comp (algebraMap R A) = (algebraMap (ResidueField R) D).comp (residue R))
  (b : ι → A)
  (hy : AlgebraicIndependent (ResidueField R) (fun i => (f (b i) : K)))
  (χ : A →ₐ[R] S) (e : K →ₐ[ResidueField R] ResidueField S)
  (hχ : ∀ a, e (f a) = residue S (χ a))

omit [Finite ι] in
/-- The selected parameter values remain independent in the actual target residue field. -/
theorem target_parameters_independent {D : Subalgebra (ResidueField R) K} (f : A →+* D) (b : ι → A)
    (hy : AlgebraicIndependent (ResidueField R) (fun i => (f (b i) : K)))
    (χ : A →ₐ[R] S) (e : K →ₐ[ResidueField R] ResidueField S)
    (hχ : ∀ a, e (f a) = residue S (χ a)) :
    AlgebraicIndependent (ResidueField R) (fun i => residue S (χ (b i))) := by
  have h := hy.map' (f := e) e.injective
  simpa only [Function.comp_def, hχ] using h

omit [Finite ι] in
/-- Every denominator of the actual projected chart maps to a target unit. -/
theorem target_denominator_unit (p : R) [Fact (Irreducible p)] (D : Subalgebra (ResidueField R) K)
    (f : A →+* D)
    (hf : f.comp (algebraMap R A) = (algebraMap (ResidueField R) D).comp (residue R))
    (b : ι → A)
    (hy : AlgebraicIndependent (ResidueField R) (fun i => (f (b i) : K)))
    (χ : A →ₐ[R] S) (e : K →ₐ[ResidueField R] ResidueField S)
    (hχ : ∀ a, e (f a) = residue S (χ a))
    (s : sourceDenominators p b) : IsUnit (χ s) := by
  have hu := (IsLocalization.map_units (Localization (sourceDenominators p b)) s).map
    (point p D f hf b hy)
  rw [point_algebraMap] at hu
  have he := hu.map e.toRingHom
  change IsUnit (e (f (s : A))) at he
  rw [hχ] at he
  exact (residue_ne_zero_iff_isUnit _).mp (isUnit_iff_ne_zero.mp he)

/-- The original point extends to the actual source localization, not to a new source ring. -/
def projectedTargetMap (p : R) [Fact (Irreducible p)] (D : Subalgebra (ResidueField R) K)
    (f : A →+* D)
    (hf : f.comp (algebraMap R A) = (algebraMap (ResidueField R) D).comp (residue R))
    (b : ι → A)
    (hy : AlgebraicIndependent (ResidueField R) (fun i => (f (b i) : K)))
    (χ : A →ₐ[R] S) (e : K →ₐ[ResidueField R] ResidueField S)
    (hχ : ∀ a, e (f a) = residue S (χ a)) : Localization (sourceDenominators p b) →ₐ[R] S :=
  IsLocalization.liftAlgHom (target_denominator_unit p D f hf b hy χ e hχ)

omit [Finite ι] in
@[simp] theorem projectedTargetMap_algebraMap (a : A) :
    projectedTargetMap p D f hf b hy χ e hχ
      (algebraMap A (Localization (sourceDenominators p b)) a) = χ a :=
  IsLocalization.lift_eq _ a

omit [Finite ι] in
/-- The entire actual projected source still has the original commuting residue square. -/
theorem projectedTargetMap_residue_square (x : Localization (sourceDenominators p b)) :
    e (point p D f hf b hy x) =
      residue S (projectedTargetMap p D f hf b hy χ e hχ x) := by
  have h : e.toRingHom.comp (point p D f hf b hy) =
      (residue S).comp (projectedTargetMap p D f hf b hy χ e hχ).toRingHom := by
    apply IsLocalization.ringHom_ext (sourceDenominators p b)
    apply RingHom.ext
    intro a
    change e (point p D f hf b hy
      (algebraMap A (Localization (sourceDenominators p b)) a)) =
      residue S (projectedTargetMap p D f hf b hy χ e hχ
        (algebraMap A (Localization (sourceDenominators p b)) a))
    rw [point_algebraMap, projectedTargetMap_algebraMap]
    exact hχ a
  exact DFunLike.congr_fun h x

/-- The new coefficient DVR maps to the target using the same original parameter values. -/
def projectedTargetScalarMap (p : R) [Fact (Irreducible p)]
    {D : Subalgebra (ResidueField R) K} (f : A →+* D) (b : ι → A)
    (hy : AlgebraicIndependent (ResidueField R) (fun i => (f (b i) : K)))
    (χ : A →ₐ[R] S) (e : K →ₐ[ResidueField R] ResidueField S)
    (hχ : ∀ a, e (f a) = residue S (χ a)) : Ring R ι p →ₐ[R] S :=
  ParameterLocalization.point p (fun i => χ (b i))
    (target_parameters_independent f b hy χ e hχ)

omit [Finite ι] in
/-- The actual source scalar map and target point commute after localization. -/
theorem projectedTargetMap_comp_scalarMap :
    (projectedTargetMap p D f hf b hy χ e hχ).toRingHom.comp (scalarMap p b) =
      (projectedTargetScalarMap p f b hy χ e hχ).toRingHom := by
  apply IsLocalization.ringHom_ext (parameterIdeal R ι p).primeCompl
  apply RingHom.ext
  intro q
  change projectedTargetMap p D f hf b hy χ e hχ
    (scalarMap p b (algebraMap (MvPolynomial ι R) (Ring R ι p) q)) =
      projectedTargetScalarMap p f b hy χ e hχ
        (algebraMap (MvPolynomial ι R) (Ring R ι p) q)
  rw [scalarMap_algebraMap, projectedTargetMap_algebraMap,
    projectedTargetScalarMap, ParameterLocalization.point_algebraMap]
  exact MvPolynomial.comp_aeval_apply b χ q

omit [Finite ι] in
/-- The actual new coefficient map preserves the original chosen uniformizer. -/
theorem projectedTargetScalarMap_uniformizer :
    projectedTargetScalarMap p f b hy χ e hχ (algebraMap R (Ring R ι p) p) =
      algebraMap R S p :=
  (projectedTargetScalarMap p f b hy χ e hχ).commutes p

/-- When the original uniformizer is preserved, the actual new coefficient map is local. -/
theorem projectedTargetScalarMap_isLocalHom
    (hpS : Irreducible (algebraMap R S p)) :
    IsLocalHom (projectedTargetScalarMap p f b hy χ e hχ).toRingHom := by
  let : IsDiscreteValuationRing (Ring R ι p) := isDiscreteValuationRing R ι p
  apply IsDiscreteValuationRing.isLocalHom_of_map_irreducible
    (projectedTargetScalarMap p f b hy χ e hχ).toRingHom (uniformizer_irreducible R ι p)
  change Irreducible (projectedTargetScalarMap p f b hy χ e hχ
    (algebraMap R (Ring R ι p) p))
  rw [projectedTargetScalarMap_uniformizer]
  exact hpS

/-- The original residue embedding is linear over the actual SECOND parameter residue field.
Its two actions are constructed from the actual source fraction evaluation and target map. -/
def projectedResidueAlgEmbedding (p : R) [Fact (Irreducible p)] (D : Subalgebra (ResidueField R) K)
    (f : A →+* D)
    (hf : f.comp (algebraMap R A) = (algebraMap (ResidueField R) D).comp (residue R))
    (b : ι → A)
    (hy : AlgebraicIndependent (ResidueField R) (fun i => (f (b i) : K)))
    (χ : A →ₐ[R] S) (e : K →ₐ[ResidueField R] ResidueField S)
    (hχ : ∀ a, e (f a) = residue S (χ a))
    (hpS : Irreducible (algebraMap R S p)) :
    letI : Algebra (Ring R ι p) S :=
      (projectedTargetScalarMap p f b hy χ e hχ).toRingHom.toAlgebra
    letI : IsLocalHom (algebraMap (Ring R ι p) S) :=
      projectedTargetScalarMap_isLocalHom p D f b hy χ e hχ hpS
    letI : Algebra (ResidueField (Ring R ι p)) K :=
      ((SeparatingParameterLocalization.fractionMap D (fun i => f (b i)) hy).comp
        (residueFieldAlgEquiv R ι p).toRingHom).toAlgebra
    K →ₐ[ResidueField (Ring R ι p)] ResidueField S := by
  let : Algebra (Ring R ι p) S :=
    (projectedTargetScalarMap p f b hy χ e hχ).toRingHom.toAlgebra
  let : IsLocalHom (algebraMap (Ring R ι p) S) :=
    projectedTargetScalarMap_isLocalHom p D f b hy χ e hχ hpS
  let : Algebra (ResidueField (Ring R ι p)) K :=
    ((SeparatingParameterLocalization.fractionMap D (fun i => f (b i)) hy).comp
      (residueFieldAlgEquiv R ι p).toRingHom).toAlgebra
  refine { e.toRingHom with commutes' := ?_ }
  intro r
  obtain ⟨a, rfl⟩ := residue_surjective r
  change e (SeparatingParameterLocalization.fractionMap D (fun i => f (b i)) hy
    (residueFieldAlgEquiv R ι p (residue (Ring R ι p) a))) =
      residue S (projectedTargetScalarMap p f b hy χ e hχ a)
  have hs := RingHom.congr_fun (point_comp_scalarMap p D f hf b hy) a
  change point p D f hf b hy (scalarMap p b a) =
    SeparatingParameterLocalization.fractionMap D (fun i => f (b i)) hy
      (residueFieldAlgEquiv R ι p (residue (Ring R ι p) a)) at hs
  rw [← hs, projectedTargetMap_residue_square p D f hf b hy χ e hχ]
  exact congrArg (residue S)
    (RingHom.congr_fun (projectedTargetMap_comp_scalarMap p D f hf b hy χ e hχ) a)

/-- The actual source point as an algebra map over the second parameter DVR. -/
def projectedPointOverParameters (p : R) [Fact (Irreducible p)]
    (D : Subalgebra (ResidueField R) K) (f : A →+* D)
    (hf : f.comp (algebraMap R A) = (algebraMap (ResidueField R) D).comp (residue R))
    (b : ι → A)
    (hy : AlgebraicIndependent (ResidueField R) (fun i => (f (b i) : K))) :
    letI : Algebra (Ring R ι p) (Localization (sourceDenominators p b)) :=
      (scalarMap p b).toAlgebra
    letI : Algebra (Ring R ι p) K :=
      ((SeparatingParameterLocalization.fractionMap D (fun i => f (b i)) hy).comp
        ((residueFieldAlgEquiv R ι p).toRingHom.comp (residue (Ring R ι p)))).toAlgebra
    Localization (sourceDenominators p b) →ₐ[Ring R ι p] K := by
  let : Algebra (Ring R ι p) (Localization (sourceDenominators p b)) :=
    (scalarMap p b).toAlgebra
  let : Algebra (Ring R ι p) K :=
    ((SeparatingParameterLocalization.fractionMap D (fun i => f (b i)) hy).comp
      ((residueFieldAlgEquiv R ι p).toRingHom.comp (residue (Ring R ι p)))).toAlgebra
  refine { point p D f hf b hy with commutes' := ?_ }
  intro a
  exact RingHom.congr_fun (point_comp_scalarMap p D f hf b hy) a

/-- The actual target point as an algebra map over that same parameter DVR. -/
def projectedTargetOverParameters (p : R) [Fact (Irreducible p)] (D : Subalgebra (ResidueField R) K)
    (f : A →+* D)
    (hf : f.comp (algebraMap R A) = (algebraMap (ResidueField R) D).comp (residue R))
    (b : ι → A)
    (hy : AlgebraicIndependent (ResidueField R) (fun i => (f (b i) : K)))
    (χ : A →ₐ[R] S) (e : K →ₐ[ResidueField R] ResidueField S)
    (hχ : ∀ a, e (f a) = residue S (χ a)) :
    letI : Algebra (Ring R ι p) (Localization (sourceDenominators p b)) :=
      (scalarMap p b).toAlgebra
    letI : Algebra (Ring R ι p) S :=
      (projectedTargetScalarMap p f b hy χ e hχ).toRingHom.toAlgebra
    Localization (sourceDenominators p b) →ₐ[Ring R ι p] S := by
  let : Algebra (Ring R ι p) (Localization (sourceDenominators p b)) :=
    (scalarMap p b).toAlgebra
  let : Algebra (Ring R ι p) S :=
    (projectedTargetScalarMap p f b hy χ e hχ).toRingHom.toAlgebra
  refine { (projectedTargetMap p D f hf b hy χ e hχ).toRingHom with commutes' := ?_ }
  intro a
  exact RingHom.congr_fun
    (projectedTargetMap_comp_scalarMap p D f hf b hy χ e hχ) a

end ParameterLocalization.ProjectedCentre
