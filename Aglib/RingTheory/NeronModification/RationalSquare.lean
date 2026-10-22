/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.NeronModification.FormallyEtaleCentre
public import Aglib.RingTheory.NeronModification.ResiduePoint
public import Aglib.RingTheory.NeronModification.OriginStep
public import Aglib.RingTheory.Kaehler.FormallyEtaleFitting
public import Aglib.RingTheory.Extension.Generators.RationalCentre
public import Aglib.RingTheory.DiscreteValuationRing.SameUniformizer

/-! # Descent of a rational-centre strict step along an actual square

Both evaluated differential Fitting ideals are identified along the actual
point square. The same-uniformizer target map reflects strictness. All maps,
centre kernels and algebra structures are actual inputs; no ideal comparison
or lifted modification point is assumed.
-/

@[expose] public noncomputable section

namespace Algebra.NeronModification

open IsLocalRing

variable {R A B T S U ι : Type*}
  [CommRing R] [CommRing A] [CommRing B] [CommRing T] [CommRing S] [CommRing U]
  [Algebra R A] [Algebra R B] [Algebra R T] [Algebra A T] [Algebra B T]
  [IsScalarTower R A T] [IsScalarTower R B T]
  [Algebra R S] [Algebra R U] [Algebra A U] [IsScalarTower R A U]
  [IsLocalRing A] [IsDomain S] [IsDiscreteValuationRing S]
  [IsDomain U] [IsDiscreteValuationRing U]
  [Algebra.FormallyUnramified R A] [Algebra.FormallyEtale B T] [Module.Flat B T]
  [Algebra.FiniteType R B] [Algebra.FiniteType A T] [Finite ι]

/-- A genuine rational residue square after flat formally étale source extension
strictly improves the original modification, not merely its auxiliary model. -/
theorem exists_lift_fittingIdeal_lt_of_rationalSquare
    (p : R) (g : ι → B) (χ : B →ₐ[R] S) (χT : T →ₐ[A] U) (σ : S →ₐ[R] U)
    (hpA : maximalIdeal A = Ideal.span {algebraMap R A p})
    (hpS : Irreducible (algebraMap R S p))
    (hpU : Irreducible (algebraMap R U p))
    (hpoint : ∀ b, χT (algebraMap B T b) = σ (χ b))
    (φ : T →ₐ[A] ResidueField A) (e : ResidueField A →+* ResidueField U)
    (hres : ∀ t, residue U (χT t) = e (φ t))
    (hcentre : RingHom.ker φ.toRingHom =
      (Ideal.span (insert (algebraMap R B p) (Set.range g))).map (algebraMap B T))
    (hg : ∀ i, residue S (χ (g i)) = 0) (k : ℕ)
    (hne : (Module.fittingIdeal B (KaehlerDifferential R B) k).map χ.toRingHom ≠ ⊥)
    (hproper : (Module.fittingIdeal B (KaehlerDifferential R B) k).map χ.toRingHom ≠ ⊤) :
    ∃ χM : Modification (algebraMap R B p) g →ₐ[R] S,
      (∀ b, χM (of (algebraMap R B p) g b) = χ b) ∧
      (Module.fittingIdeal B (KaehlerDifferential R B) k).map χ.toRingHom <
        (Module.fittingIdeal _
          (KaehlerDifferential R (Modification (algebraMap R B p) g)) k).map χM.toRingHom := by
  classical
  let pB := algebraMap R B p
  let pT := algebraMap B T pB
  have hpT : pT = algebraMap A T (algebraMap R A p) := by
    exact (IsScalarTower.algebraMap_apply R B T p).symm.trans
      (IsScalarTower.algebraMap_apply R A T p)
  have hpAU : Irreducible (algebraMap A U (algebraMap R A p)) := by
    rwa [← IsScalarTower.algebraMap_apply]
  have hpσ : Irreducible (σ (algebraMap R S p)) := by
    rwa [σ.commutes]
  have horder (I : Ideal S) :
      IsDiscreteValuationRing.idealOrderIsoENat U (I.map σ.toRingHom) =
        IsDiscreteValuationRing.idealOrderIsoENat S I :=
    IsDiscreteValuationRing.idealOrderIsoENat_map_of_map_irreducible
      σ.toRingHom hpS hpσ I
  have hinj : Function.Injective (Ideal.map σ.toRingHom) := by
    intro I J hij
    apply (IsDiscreteValuationRing.idealOrderIsoENat S).injective
    rw [← horder I, ← horder J, hij]
  have hsquare : χT.toRingHom.comp (algebraMap B T) = σ.toRingHom.comp χ.toRingHom := by
    ext b
    exact hpoint b
  have hfit := KaehlerDifferential.map_fittingIdeal_of_formallyEtale_of_formallyUnramified
    R A B T χ.toRingHom χT.toRingHom σ.toRingHom hsquare k
  have hneT : (Module.fittingIdeal T (KaehlerDifferential A T) k).map χT.toRingHom ≠ ⊥ := by
    rw [hfit]
    intro h
    apply hne
    apply hinj
    exact h.trans (Ideal.map_bot (f := σ.toRingHom)).symm
  have hproperT :
      (Module.fittingIdeal T (KaehlerDifferential A T) k).map χT.toRingHom ≠ ⊤ := by
    rw [hfit]
    intro h
    apply hproper
    apply hinj
    exact h.trans (Ideal.map_top σ.toRingHom).symm
  obtain ⟨n, ⟨P⟩⟩ := Algebra.FiniteType.iff_exists_generators.mp
    (inferInstance : Algebra.FiniteType A T)
  obtain ⟨a, z, hker, hcoords⟩ :=
    P.exists_residueCentre_and_dividedPoint (algebraMap R A p) hpA φ χT e hres hpAU
  let h : Fin n → T := fun i => P.val i - algebraMap A T (a i)
  have hcentres : Ideal.span (insert pT (Set.range (fun i => algebraMap B T (g i)))) =
      Ideal.span (insert pT (Set.range h)) := by
    rw [hpT, ← hker, hcentre]
    rw [Ideal.map_span, Set.image_insert_eq, ← Set.range_comp', ← hpT]
  have horigin := exists_lift_fittingIdeal_lt P (algebraMap R A p) a χT z hpA hpAU
    hcoords k hneT hproperT
  rw [← hpT] at horigin
  obtain ⟨χC, hχC, _, hstrict⟩ := horigin
  obtain ⟨χM, hχM⟩ := exists_lift_of_residue_eq_zero p g χ hpS hg
  refine ⟨χM, hχM, ?_⟩
  let M := Modification pB g
  let C := Modification pT h
  let : CommSemiring M := CommRing.toCommSemiring
  let : Semiring M := CommSemiring.toSemiring
  let : CommSemiring C := CommRing.toCommSemiring
  let : Semiring C := CommSemiring.toSemiring
  let j : M →ₐ[B] C := baseChangeOfCentreEq pB g h hcentres
  have hcoeff (b : B) : χC (j (of pB g b)) = σ (χM (of pB g b)) := by
    rw [baseChangeOfCentreEq_of, hχC, hpoint, hχM]
  have hreg : IsRegular ((χC.toRingHom.comp j.toRingHom) (of pB g pB)) := by
    change IsRegular (χC (j (of pB g pB)))
    rw [hcoeff, hχM, χ.commutes, σ.commutes]
    exact isRegular_iff_ne_zero.mpr hpU.ne_zero
  have hsquareM : χC.toRingHom.comp j.toRingHom = σ.toRingHom.comp χM.toRingHom :=
    ringHom_ext_of_isRegular pB g _ _ hreg hcoeff
  let : Algebra M C := @RingHom.toAlgebra M C inferInstance inferInstance j.toRingHom
  let : IsScalarTower R M C :=
    IsScalarTower.of_algebraMap_eq fun r => ((j.restrictScalars R).commutes r).symm
  let : Algebra.FormallyEtale M C := formallyEtale_baseChangeOfCentreEq pB g h hcentres
  have hfitM := KaehlerDifferential.map_fittingIdeal_of_formallyEtale_of_formallyUnramified
    R A M C χM.toRingHom χC.toRingHom σ.toRingHom hsquareM k
  rw [hfit, hfitM] at hstrict
  apply (IsDiscreteValuationRing.idealOrderIsoENat S).lt_iff_lt.mp
  rw [← horder, ← horder]
  exact (IsDiscreteValuationRing.idealOrderIsoENat U).lt_iff_lt.mpr hstrict

end Algebra.NeronModification
