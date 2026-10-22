/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.DiscreteValuationRing.ParameterProjectedTarget
public import Aglib.RingTheory.DiscreteValuationRing.ParameterChartScalar
public import Aglib.RingTheory.NeronModification.FiniteSeparableCentre

/-! # Strict improvement on the genuine chart with the original centre generators

Finite type is supplied by the actual tensor chart, and point surjectivity is derived
from the actual residue extension. The centre generators are transported unchanged.
-/

@[expose] public noncomputable section

open IsLocalRing MvPolynomial Algebra.NeronModification

namespace ParameterLocalization.ProjectedCentre

variable {R S A K ι β ν : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [CommRing S] [IsDomain S] [IsDiscreteValuationRing S] [Algebra R S]
  [IsLocalHom (algebraMap R S)] [CommRing A] [Algebra R A]
  [Field K] [Algebra (ResidueField R) K] [Finite ι] [Finite β] [Finite ν]
  (p : R) [Fact (Irreducible p)] (D : Subalgebra (ResidueField R) K)
  (f : A →+* D)
  (hf : f.comp (algebraMap R A) = (algebraMap (ResidueField R) D).comp (residue R))
  (b : ι → A)
  (hy : AlgebraicIndependent (ResidueField R) (fun i => (f (b i) : K)))
  (χ : A →ₐ[R] S) (e : K →ₐ[ResidueField R] ResidueField S)
  (hχ : ∀ a, e (f a) = residue S (χ a))
  (hpS : Irreducible (algebraMap R S p))

local notation "R₂" => Ring R ι p
local notation "A'" => Localization (sourceDenominators p b)
local notation "k₂" => ResidueField R₂
local notation "G" => FractionRing (MvPolynomial ι (ResidueField R))

local instance : IsDiscreteValuationRing R₂ := isDiscreteValuationRing R ι p
/-- The parameter DVR acts on the original localized source through the actual
parameter scalar map `scalarMap p b`. -/
local instance projectedStepSourceAlgebra : Algebra R₂ A' := (scalarMap p b).toAlgebra

variable [IsFractionRing D K]

include hpS in
/-- The actual projected strict step keeps the original finite centre family.
The finite-separability assumptions here are supplied by the exact projected
residue transport, not assumptions of the final general-centre theorem. -/
theorem exists_fixed_projected_strict_step :
    letI : Algebra R₂ S :=
      (projectedTargetScalarMap p f b hy χ e hχ).toRingHom.toAlgebra
    letI : IsLocalHom (algebraMap R₂ S) :=
      projectedTargetScalarMap_isLocalHom p D f b hy χ e hχ hpS
    letI : Algebra k₂ K :=
      ((SeparatingParameterLocalization.fractionMap D (fun i => f (b i)) hy).comp
        (residueFieldAlgEquiv R ι p).toRingHom).toAlgebra
    letI : Algebra R₂ K :=
      ((algebraMap k₂ K).comp (residue R₂)).toAlgebra
    ∀ [Module.Finite k₂ K] [Algebra.IsSeparable k₂ K]
      (P : Algebra.Generators R A (β ⊕ ι)) (_hb : ∀ i, P.val (.inr i) = b i)
      (_hs : Function.Surjective f) (g : ν → A)
      (_hgen : Ideal.span (insert (algebraMap R A p) (Set.range g)) = RingHom.ker f)
      (k : ℕ)
      (_hne : (Module.fittingIdeal A' (KaehlerDifferential R₂ A') k).map
        (projectedTargetOverParameters p D f hf b hy χ e hχ).toRingHom ≠ ⊥)
      (_hproper : (Module.fittingIdeal A' (KaehlerDifferential R₂ A') k).map
        (projectedTargetOverParameters p D f hf b hy χ e hχ).toRingHom ≠ ⊤),
    ∃ χM : Modification (algebraMap R A' p) (fun j => algebraMap A A' (g j)) →ₐ[R₂] S,
      (∀ a, χM (of (algebraMap R A' p) (fun j => algebraMap A A' (g j)) a) =
        projectedTargetOverParameters p D f hf b hy χ e hχ a) ∧
      (Module.fittingIdeal A' (KaehlerDifferential R₂ A') k).map
        (projectedTargetOverParameters p D f hf b hy χ e hχ).toRingHom <
      (Module.fittingIdeal _ (KaehlerDifferential R₂
        (Modification (algebraMap R A' p) (fun j => algebraMap A A' (g j)))) k).map
          χM.toRingHom := by
  let : Algebra R₂ S :=
    (projectedTargetScalarMap p f b hy χ e hχ).toRingHom.toAlgebra
  let : IsLocalHom (algebraMap R₂ S) :=
    projectedTargetScalarMap_isLocalHom p D f b hy χ e hχ hpS
  let : Algebra k₂ K :=
    ((SeparatingParameterLocalization.fractionMap D (fun i => f (b i)) hy).comp
      (residueFieldAlgEquiv R ι p).toRingHom).toAlgebra
  let : Algebra R₂ K :=
    ((algebraMap k₂ K).comp (residue R₂)).toAlgebra
  intro _ _ P hb hs g hgen k hne hproper
  let : Algebra (MvPolynomial ι R) A := (aeval b).toRingHom.toAlgebra
  let : IsScalarTower R (MvPolynomial ι R) A :=
    IsScalarTower.of_algebraMap_eq fun r => ((aeval (R := R) b).commutes r).symm
  have ha (i) : algebraMap (MvPolynomial ι R) A (X i) = P.val (.inr i) := by
    change aeval b (X i) = _
    rw [aeval_X, hb]
  let : Algebra.FiniteType R₂ (Chart (A := A) (α := ι) p) := finiteType_chart p P ha
  let E := chartEquivLocalizationOverParameters (A := A) (ι := ι) p
  let : Algebra.FiniteType R₂ A' := Algebra.FiniteType.of_surjective E.toAlgHom E.surjective
  let ψ := SeparatingParameterLocalization.fractionMap D (fun i => f (b i)) hy
  let : Algebra G K := ψ.toAlgebra
  let : Algebra k₂ G := (residueFieldAlgEquiv R ι p).toRingHom.toAlgebra
  let : IsScalarTower k₂ G K := IsScalarTower.of_algebraMap_eq' rfl
  let : Module.Finite G K := Module.Finite.of_restrictScalars_finite k₂ G K
  have halg : Algebra.IsAlgebraic G K := Algebra.IsAlgebraic.of_finite G K
  have hsurj := point_surjective p D f hf b hy hs halg
  let p₂ : R₂ := algebraMap R R₂ p
  have hp₂ : Irreducible p₂ := uniformizer_irreducible R ι p
  have hp₂S : Irreducible (algebraMap R₂ S p₂) := by
    change Irreducible (projectedTargetScalarMap p f b hy χ e hχ (algebraMap R R₂ p))
    rw [projectedTargetScalarMap_uniformizer]
    exact hpS
  have hpA : algebraMap R₂ A' p₂ = algebraMap R A' p := by
    change scalarMap p b (algebraMap R R₂ p) = _
    rw [IsScalarTower.algebraMap_apply R (MvPolynomial ι R) R₂]
    change scalarMap p b (algebraMap (MvPolynomial ι R) R₂ (C p)) = _
    rw [scalarMap_algebraMap, aeval_C, ← IsScalarTower.algebraMap_apply R A A']
  have hcentre : Ideal.span (insert (algebraMap R₂ A' p₂)
      (Set.range fun j => algebraMap A A' (g j))) =
        RingHom.ker (projectedPointOverParameters p D f hf b hy).toRingHom := by
    change _ = RingHom.ker (point p D f hf b hy)
    rw [hpA, ker_point, ← hgen, Ideal.map_span]
    simp only [Set.image_insert_eq, ← Set.range_comp, Function.comp_def,
      ← IsScalarTower.algebraMap_apply R A A']
  have hres (a : A') : residue S (projectedTargetOverParameters p D f hf b hy χ e hχ a) =
      projectedResidueAlgEmbedding p D f hf b hy χ e hχ hpS
        (projectedPointOverParameters p D f hf b hy a) :=
    (projectedTargetMap_residue_square p D f hf b hy χ e hχ a).symm
  let C : A' → Prop := fun a =>
    ∃ χM : Modification a (fun j => algebraMap A A' (g j)) →ₐ[R₂] S,
      (∀ z, χM (of a (fun j => algebraMap A A' (g j)) z) =
        projectedTargetOverParameters p D f hf b hy χ e hχ z) ∧
      (Module.fittingIdeal A' (KaehlerDifferential R₂ A') k).map
        (projectedTargetOverParameters p D f hf b hy χ e hχ).toRingHom <
      (Module.fittingIdeal _ (KaehlerDifferential R₂
        (Modification a (fun j => algebraMap A A' (g j)))) k).map χM.toRingHom
  have hstep : C (algebraMap R₂ A' p₂) :=
    exists_lift_fittingIdeal_lt_of_finiteSeparableCentre R₂ K S
      (projectedResidueAlgEmbedding p D f hf b hy χ e hχ hpS) p₂
      (fun j => algebraMap A A' (g j))
      (projectedTargetOverParameters p D f hf b hy χ e hχ)
      (projectedPointOverParameters p D f hf b hy) hp₂ hp₂S hsurj hres hcentre k hne hproper
  exact Eq.mp (congrArg C hpA) hstep

end ParameterLocalization.ProjectedCentre
