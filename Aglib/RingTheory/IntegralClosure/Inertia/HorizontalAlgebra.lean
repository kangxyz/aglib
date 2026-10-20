/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.RingTheory.IntegralClosure.Inertia.HorizontalNonGalois
public import Aglib.RingTheory.IntegralClosure.FiniteEtale

/-!
Extraction source: `R5Lab.Aglib.RingTheory.IntegralClosure.FiniteEtale.EtaleAlgebra`,
R5 revision
`f8a3314ddecffcada2ec721d26d56a937bed9690`, SHA-256
`298f673bc37d723c22750b05b2826c1f5a992e88126ccb74555639fa986b1894`.
Historical source locators retain their original basis. -/

@[expose] public section

noncomputable section
set_option autoImplicit false
set_option linter.style.haveILetI false

namespace integralClosure.Inertia.HorizontalAlgebra

variable (F R K Ω A : Type*) [Field F] [CharZero F]
  [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Algebra F R]
  [Field K] [Algebra R K] [IsFractionRing R K]
  [Field Ω] [Algebra K Ω] [Algebra R Ω] [IsScalarTower R K Ω]
  [IsGalois K Ω] [IsAlgClosed Ω]
  [CommRing A] [Algebra K A] [Algebra R A] [IsScalarTower R K A]
  [Algebra.Etale K A]

include F

/-- Reverse horizontal inertia criterion for the literal normalization of an
arbitrary finite etale generic algebra. The inertia action is postcomposition
on the actual geometric generic fibre, and no Galois assumption is placed on
its field components. -/
theorem model_etale_of_absolute_inertia_trivial_on_generic_fiber
    (Q : Ideal (integralClosure R Ω)) [Q.IsPrime]
    [Q.LiesOver (IsLocalRing.maximalIdeal R)]
    (htrivial : ∀ σ ∈ Q.inertia (Ω ≃ₐ[K] Ω), ∀ f : A →ₐ[K] Ω,
      σ.toAlgHom.comp f = f) :
    Algebra.Etale R (integralClosure R A) := by
  obtain ⟨ι, hι, L, hL, hKL, e, hfin⟩ :=
    (Algebra.Etale.iff_exists_algEquiv_prod K A).mp inferInstance
  letI := hι
  letI := hL
  letI := hKL
  letI (i : ι) : Algebra R (L i) :=
    (algebraMap K (L i)).comp (algebraMap R K) |>.toAlgebra
  haveI (i : ι) : IsScalarTower R K (L i) := IsScalarTower.of_algebraMap_eq' rfl
  haveI (i : ι) : Module.Finite K (L i) := (hfin i).1
  haveI (i : ι) : Algebra.IsSeparable K (L i) := (hfin i).2
  haveI (i : ι) : Module.Finite R (integralClosure R (L i)) :=
    IsIntegralClosure.finite R K (L i) _
  haveI (i : ι) : Algebra.Etale R (integralClosure R (L i)) := by
    apply HorizontalNonGalois.model_etale_of_absolute_inertia_trivial_on_all_embeddings
      R K Ω F (L i) Q
    intro σ hσ f
    apply AlgHom.ext
    intro y
    obtain ⟨a, ha⟩ := ((Function.surjective_eval i).comp e.surjective) y
    have h := congrArg (fun g : A →ₐ[K] Ω => g a)
      (htrivial σ hσ (f.comp ((Pi.evalAlgHom K L i).comp e.toAlgHom)))
    change σ (f (e a i)) = f (e a i) at h
    change e a i = y at ha
    change σ (f y) = f y
    simpa only [ha] using h
  haveI : Algebra.FinitePresentation R (∀ i, integralClosure R (L i)) :=
    Algebra.FinitePresentation.of_finiteType.mp inferInstance
  haveI : Algebra.Etale R (∀ i, integralClosure R (L i)) := ⟨inferInstance, inferInstance⟩
  exact Algebra.Etale.of_equiv
    (integralClosure.equivPi R A L (e.restrictScalars R)).symm

end integralClosure.Inertia.HorizontalAlgebra
