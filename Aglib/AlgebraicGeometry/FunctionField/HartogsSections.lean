/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.AlgebraicGeometry.FunctionField
public import Aglib.RingTheory.IntegralClosure.HeightOneIntersection
public import Aglib.RingTheory.IntegralClosure.MaximalIdealDual

/-! # Original scalar sections across codimension at least two

The actual restriction from a normal Noetherian domain to an open containing
all height-one primes is bijective. The proof uses only the original generic
stalk and original point stalks. The punctured local spectrum is a thin
specialization; no extension of an arbitrary vector bundle is asserted.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory

namespace AlgebraicGeometry.Scheme

universe u

variable (A : Type u) [CommRing A]

local instance (U : (Spec (.of A)).Opens) : Algebra A Γ(Spec (.of A), U) :=
  IsAffineOpen.instAlgebraCarrierObjOppositeOpensCarrierCarrierCommRingCatSpecPresheafOpOpens
    (R := .of A) (U := U)

/-- Original constants followed by restriction to the unchanged open. -/
def hartogsScalarMap (U : (Spec (.of A)).Opens) : A →+* Γ(Spec (.of A), U) :=
  (((ΓSpecIso (.of A)).inv) ≫ (Spec (.of A)).presheaf.map (homOfLE le_top).op).hom

/-- This is the native structure-sheaf scalar map, not a new algebra action. -/
theorem hartogsScalarMap_eq_algebraMap (U : (Spec (.of A)).Opens) :
    hartogsScalarMap A U = algebraMap A Γ(Spec (.of A), U) := rfl

variable [IsDomain A]

local instance : Algebra A (Spec (.of A)).functionField :=
  AlgebraicGeometry.instAlgebraCarrierFunctionFieldSpec (.of A)

local instance : IsFractionRing A (Spec (.of A)).functionField :=
  functionField_isFractionRing_of_affine (.of A)

/-- The original restriction retains its whole generic-stalk scalar triangle. -/
@[reassoc] theorem hartogsScalarMap_generic (U : (Spec (.of A)).Opens) [Nonempty U] :
    CommRingCat.ofHom (hartogsScalarMap A U) ≫ (Spec (.of A)).germToFunctionField U =
      CommRingCat.ofHom (algebraMap A (Spec (.of A)).functionField) := by
  exact StructureSheaf.algebraMap_germ U (genericPoint (Spec (.of A))) _

/-- Restriction on original constants is injective on every nonempty open. -/
theorem hartogsScalarMap_injective (U : (Spec (.of A)).Opens) [Nonempty U] :
    Function.Injective (hartogsScalarMap A U) := by
  intro a b hab
  apply IsFractionRing.injective A (Spec (.of A)).functionField
  have h := congrArg ((Spec (.of A)).germToFunctionField U) hab
  exact (ConcreteCategory.congr_hom (hartogsScalarMap_generic A U) a).symm.trans
    (h.trans (ConcreteCategory.congr_hom (hartogsScalarMap_generic A U) b))

/-- Height-one regularity of the original section gives its unique original
scalar extension. -/
theorem hartogsScalarMap_bijective [IsNoetherianRing A] [IsIntegrallyClosed A]
    (U : (Spec (.of A)).Opens) [Nonempty U]
    (hU : ∀ p : PrimeSpectrum A, p.asIdeal.height = 1 → p ∈ U) :
    Function.Bijective (hartogsScalarMap A U) := by
  refine ⟨hartogsScalarMap_injective A U, ?_⟩
  intro s
  let K := (Spec (.of A)).functionField
  let v : K := (Spec (.of A)).germToFunctionField U s
  have hv : v ∈ Set.range (algebraMap A K) := by
    apply IsIntegrallyClosed.mem_range_of_forall_height_one
    intro p hp hh
    let q : PrimeSpectrum A := ⟨p, hp⟩
    have hq : q ∈ U := hU q hh
    let : Algebra A ((Spec (.of A)).presheaf.stalk q) := StructureSheaf.stalkAlgebra A q
    let : IsLocalization.AtPrime ((Spec (.of A)).presheaf.stalk q) p :=
      StructureSheaf.IsLocalization.to_stalk A q
    let w := (Spec (.of A)).presheaf.germ U q hq s
    obtain ⟨⟨a, t⟩, ht⟩ := IsLocalization.surj p.primeCompl w
    have hscalar (a : A) :
        algebraMap ((Spec (.of A)).presheaf.stalk q) K
          (algebraMap A ((Spec (.of A)).presheaf.stalk q) a) = algebraMap A K a := by
      exact ConcreteCategory.congr_hom
        (StructureSheaf.toStalk_stalkSpecializes
          ((genericPoint_spec (Spec (.of A))).specializes trivial)) a
    refine ⟨t, t.property, a, ?_⟩
    have he := congrArg (algebraMap ((Spec (.of A)).presheaf.stalk q) K) ht
    rw [map_mul, hscalar, hscalar, algebraMap_germ_eq_germToFunctionField] at he
    exact he.symm
  obtain ⟨a, ha⟩ := hv
  refine ⟨a, (Spec (.of A)).germToFunctionField_injective U ?_⟩
  exact (ConcreteCategory.congr_hom (hartogsScalarMap_generic A U) a).trans ha

/-- The complete ring equivalence has the original restriction as its forward map. -/
def hartogsSectionsEquiv [IsNoetherianRing A] [IsIntegrallyClosed A]
    (U : (Spec (.of A)).Opens) [Nonempty U]
    (hU : ∀ p : PrimeSpectrum A, p.asIdeal.height = 1 → p ∈ U) :
    A ≃+* Γ(Spec (.of A), U) :=
  RingEquiv.ofBijective (hartogsScalarMap A U) (hartogsScalarMap_bijective A U hU)

@[simp] theorem hartogsSectionsEquiv_apply [IsNoetherianRing A] [IsIntegrallyClosed A]
    (U : (Spec (.of A)).Opens) [Nonempty U]
    (hU : ∀ p : PrimeSpectrum A, p.asIdeal.height = 1 → p ∈ U) (a : A) :
    hartogsSectionsEquiv A U hU a = hartogsScalarMap A U a := rfl

@[simp] theorem hartogsScalarMap_hartogsSectionsEquiv_symm
    [IsNoetherianRing A] [IsIntegrallyClosed A]
    (U : (Spec (.of A)).Opens) [Nonempty U]
    (hU : ∀ p : PrimeSpectrum A, p.asIdeal.height = 1 → p ∈ U)
    (s : Γ(Spec (.of A), U)) :
    hartogsScalarMap A U ((hartogsSectionsEquiv A U hU).symm s) = s :=
  (hartogsSectionsEquiv A U hU).apply_symm_apply s

@[simp] theorem hartogsSectionsEquiv_symm_hartogsScalarMap
    [IsNoetherianRing A] [IsIntegrallyClosed A]
    (U : (Spec (.of A)).Opens) [Nonempty U]
    (hU : ∀ p : PrimeSpectrum A, p.asIdeal.height = 1 → p ∈ U) (a : A) :
    (hartogsSectionsEquiv A U hU).symm (hartogsScalarMap A U a) = a :=
  (hartogsSectionsEquiv A U hU).symm_apply_apply a

section Local

variable [IsLocalRing A]

/-- The actual punctured spectrum, without its unique closed point. -/
def puncturedSpecOpen : (Spec (.of A)).Opens :=
  ⟨{IsLocalRing.closedPoint A}ᶜ, (IsLocalRing.isClosed_singleton_closedPoint A).isOpen_compl⟩

omit [IsDomain A] in
/-- Every height-one prime lies in the punctured open in local dimension at least two. -/
theorem height_one_mem_puncturedSpecOpen (hdim : 2 ≤ ringKrullDim A)
    (p : PrimeSpectrum A) (hp : p.asIdeal.height = 1) : p ∈ puncturedSpecOpen A := by
  intro he
  have heq : p = IsLocalRing.closedPoint A := he
  apply IsLocalRing.maximalIdeal_not_le_height_one hdim p.asIdeal hp
  rw [heq]
  exact le_rfl

/-- The actual punctured open is nonempty under the same dimension guard. -/
theorem puncturedSpecOpen_nonempty (hdim : 2 ≤ ringKrullDim A) :
    Nonempty (puncturedSpecOpen A) := by
  refine ⟨⟨(⊥ : PrimeSpectrum A), ?_⟩⟩
  intro he
  have hmax : IsLocalRing.maximalIdeal A = ⊥ :=
    (congrArg PrimeSpectrum.asIdeal he).symm
  have hd := hdim
  rw [← IsLocalRing.maximalIdeal_height_eq_ringKrullDim, hmax, Ideal.height_bot] at hd
  norm_num at hd

/-- The original restriction to the punctured local spectrum is bijective. -/
theorem puncturedSpecScalarMap_bijective [IsNoetherianRing A] [IsIntegrallyClosed A]
    (hdim : 2 ≤ ringKrullDim A) :
    Function.Bijective (hartogsScalarMap A (puncturedSpecOpen A)) := by
  let := puncturedSpecOpen_nonempty A hdim
  exact hartogsScalarMap_bijective A (puncturedSpecOpen A)
    (height_one_mem_puncturedSpecOpen A hdim)

end Local

end AlgebraicGeometry.Scheme
