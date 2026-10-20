/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.Torus.FiniteCorrespondence.PrincipalComposition
public import Aglib.RingTheory.Localization.PrincipalQuotientLength
public import Aglib.RingTheory.Length.ExactSequence
public import Aglib.RingTheory.Multiplicity.PrincipalEuler.Basic
public import Aglib.RingTheory.Multiplicity.PrincipalEuler.Additivity
public import Aglib.RingTheory.ScalarHomology.Basic
public import Aglib.RingTheory.PrimeFiltration.Basic
public import Aglib.RingTheory.Multiplicity.PrincipalEuler.Filtration
public import Aglib.RingTheory.PrimeFiltration.Primes
public import Aglib.RingTheory.Multiplicity.PrincipalEuler.Support
public import Aglib.RingTheory.PrimeFiltration.Length
public import Aglib.RingTheory.PrimeFiltration.Support
public import Aglib.RingTheory.FiniteLength.Support
public import Aglib.RingTheory.PrimeFiltration.Multiplicity
public import Aglib.RingTheory.Multiplicity.PrincipalEuler.Associativity
public import Aglib.RingTheory.Multiplicity.PrincipalEuler.Interchange
public import Aglib.RingTheory.Multiplicity.PrincipalEuler.Localization
public import Aglib.RingTheory.ScalarHomology.BaseChange

/-!
# PrincipalInterchange for finite correspondences on the two-dimensional torus

Native migration from `lean/R5Lab/Aglib/AlgebraicGeometry/Torus/FiniteCorrespondence/`
leaf `PrincipalInterchange.lean` at R5 revision
`f8a3314ddecffcada2ec721d26d56a937bed9690`, SHA-256
`9aa23bf3fb61e5693b63b1350237cdc05e735e3fd5cdb2f28845768de84cfbce`.

The Laurent object is `MonoidAlgebra R (Multiplicative (ℤ × ℤ))` in its original
coordinate order. Statements retain their displayed finiteness, normality,
Noetherianity, flatness, regularity and scalar-map hypotheses.
-/

@[expose] public section

open _root_.Module
  (ScalarCokernel principalEuler principalEuler_congr principalEuler_interchange
    principalEuler_localization_of_surjective)



noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped TensorProduct AlgebraMonoidAlgebra
namespace AlgebraicGeometry.Torus.FiniteCorrespondence
open _root_.Module.CommutingAutomorphisms
open _root_.Module.CommutingAutomorphisms.LaurentSupport
open MonoidAlgebra (FiniteDominantPrime)
open LaurentSupport Module
universe u
variable {R S T : Type u} [CommRing R] [CommRing S] [CommRing T]

/-- The literal source prime quotient localized in the original Laurent ring. -/
abbrev LocalPointQuotient (p : FiniteDominantPrime R) (Q : Ideal (Laurent R)) [Q.IsPrime] :=
  Localization.AtPrime Q ⊗[Laurent R] (Laurent R ⧸ p.val)

/-- Dominance supplies individual scalar regularity after original localization. -/
theorem localPointQuotient_scalar_regular (p : FiniteDominantPrime R) (a : R) (ha : a ≠ 0)
    (Q : Ideal (Laurent R)) [Q.IsPrime] :
    IsSMulRegular (LocalPointQuotient p Q) (algebraMap R (Localization.AtPrime Q) a) := by
  have hr := (pointQuotient_laurentScalar_regular p a ha).lTensor (Localization.AtPrime Q)
  intro x y hxy
  apply hr
  change (algebraMap R (Laurent R) a) • x = (algebraMap R (Laurent R) a) • y
  simpa only [IsScalarTower.algebraMap_apply R (Laurent R) (Localization.AtPrime Q),
    algebraMap_smul] using hxy

variable [Algebra R S]

/-- The first original-local scalar quotient is the localization of the
literal first Laurent quotient fibre, over the original local scalar ring. -/
def pointOriginalCokernelFibreEquiv (p : FiniteDominantPrime R) (a : R)
    (h : Function.Surjective (algebraMap R S))
    (ha : RingHom.ker (algebraMap R S) = Ideal.span ({a} : Set R))
    (Q : Ideal (Laurent S)) [Q.IsPrime] :
    ScalarCokernel (LocalPointQuotient p (Q.under (Laurent R)))
      (algebraMap R (Localization.AtPrime (Q.under (Laurent R))) a) ≃ₗ[
        Localization.AtPrime (Q.under (Laurent R))]
      Localization.AtPrime (Q.under (Laurent R)) ⊗[Laurent R]
        (Laurent S ⧸ p.val.map (coefficientMap (algebraMap R S))) := by
  let B := Localization.AtPrime (Q.under (Laurent R))
  let C := Laurent R ⧸ p.val
  let D := Laurent S ⧸ p.val.map (coefficientMap (algebraMap R S))
  let e₁ := principalCokernelBaseChangeEquiv C B (algebraMap R (Laurent R) a)
  let e₂ : ScalarCokernel C (algebraMap R (Laurent R) a) ≃ₗ[Laurent R] D :=
    (tensorSpecializationCokernelEquiv C (algebraMap R (Laurent R) a)
      (laurentCoefficient_surjective h) (laurentCoefficient_ker_principal a ha)).trans
        ((Ideal.qoutMapEquivTensorQout (I := p.val) (Laurent S)).symm.restrictScalars (Laurent R))
  rw [← IsScalarTower.algebraMap_apply R (Laurent R) B a] at e₁
  exact e₁.symm.trans (e₂.baseChange (Laurent R) B _ _)

/-- Transport both homology lengths before applying interchange. No first
fibre flatness or second-scalar regularity on that fibre is needed. -/
theorem principalEuler_pointFibre_original (p : FiniteDominantPrime R) (a c : R)
    (h : Function.Surjective (algebraMap R S))
    (ha : RingHom.ker (algebraMap R S) = Ideal.span ({a} : Set R))
    (Q : Ideal (Laurent S)) [Q.IsPrime] :
    principalEuler (N := LocalPointFibre (S := S) p Q)
      (algebraMap S (Localization.AtPrime Q) (algebraMap R S c)) =
    principalEuler (N := ScalarCokernel (LocalPointQuotient p (Q.under (Laurent R)))
      (algebraMap R (Localization.AtPrime (Q.under (Laurent R))) a))
      (algebraMap R (Localization.AtPrime (Q.under (Laurent R))) c) := by
  let D := Laurent S ⧸ p.val.map (coefficientMap (algebraMap R S))
  have he := principalEuler_localization_of_surjective (A := Laurent R) (D := Laurent S)
    D (algebraMap R (Laurent R) c) (laurentCoefficient_surjective h) Q
  have hc : coefficientMap (algebraMap R S) (algebraMap R (Laurent R) c) =
      algebraMap S (Laurent S) (algebraMap R S c) := by
    exact RingHom.congr_fun
      (MonoidAlgebra.mapRingHom_comp_algebraMap (M := Character) (algebraMap R S)) c
  change principalEuler (N := Localization.AtPrime (Q.under (Laurent R)) ⊗[Laurent R] D)
    (algebraMap (Laurent R) (Localization.AtPrime (Q.under (Laurent R)))
      (algebraMap R (Laurent R) c)) =
    principalEuler (N := LocalPointFibre (S := S) p Q)
      (algebraMap (Laurent S) (Localization.AtPrime Q)
        (coefficientMap (algebraMap R S) (algebraMap R (Laurent R) c))) at he
  rw [hc, ← IsScalarTower.algebraMap_apply S (Laurent S) (Localization.AtPrime Q),
    ← IsScalarTower.algebraMap_apply R (Laurent R) (Localization.AtPrime (Q.under (Laurent R)))]
      at he
  exact he.symm.trans (principalEuler_congr
    (pointOriginalCokernelFibreEquiv p a h ha Q)
    (algebraMap R (Localization.AtPrime (Q.under (Laurent R))) c)).symm

/-- The existing cycle map with its actual structural ring map made explicit. -/
def quotientFibreCycleMapFor [IsNoetherianRing S] (f : R →+* S) :
    FreeAbelianGroup (FiniteDominantPrime R) →+ FreeAbelianGroup (FiniteDominantPrime S) := by
  let := f.toAlgebra
  exact quotientFibreCycleMap

/-- The double principal Euler expression at the original prime over a final
label, using the literal composite coefficient map. -/
def originalPointDoubleEuler (p : FiniteDominantPrime R) (a b : R) (k : R →+* T) (q :
    FiniteDominantPrime T) : ℤ :=
  principalEuler (N := ScalarCokernel
    (LocalPointQuotient p (q.val.comap (coefficientMap k)))
    (algebraMap R (Localization.AtPrime (q.val.comap (coefficientMap k))) a))
    (algebraMap R (Localization.AtPrime (q.val.comap (coefficientMap k))) b)

/-- Scalar interchange is applied on the actual original point localization.
It needs no regularity on either intermediate quotient. -/
theorem originalPointDoubleEuler_interchange (p : FiniteDominantPrime R) (a b : R)
    (ha : a ≠ 0) (hb : b ≠ 0) (k : R →+* T) (q : FiniteDominantPrime T) :
    originalPointDoubleEuler p a b k q = originalPointDoubleEuler p b a k q := by
  exact principalEuler_interchange _ _
    (localPointQuotient_scalar_regular p a ha _) (localPointQuotient_scalar_regular p b hb _)

omit [Algebra R S] in
/-- A literal composition coefficient is the double scalar Euler expression
on the original prime quotient. All finiteness and minimal-factor regularity
are derived, including when the first quotient has embedded torsion. -/
theorem quotientFibreCycleMapFor_composition_coeff_eq_originalEuler
    [IsNoetherianRing S] [IsNoetherianRing T]
    [IsDomain R] [IsIntegrallyClosed R] [IsDomain S]
    (f : R →+* S) (g : S →+* T) (p : FiniteDominantPrime R) (a b : R)
    (hf : Function.Surjective f) (hfa : RingHom.ker f = Ideal.span ({a} : Set R))
    (hgb : f b ≠ 0) (hg : Function.Surjective g)
    (hgbker : RingHom.ker g = Ideal.span ({f b} : Set S)) (q : FiniteDominantPrime T) :
    FreeAbelianGroup.coeff q ((quotientFibreCycleMapFor g)
      ((quotientFibreCycleMapFor f) (FreeAbelianGroup.of p))) =
    originalPointDoubleEuler p a b (g.comp f) q := by
  let := f.toAlgebra
  let := g.toAlgebra
  have he := (quotientFibreCycleMap_composition_coeff_eq_euler p a hf hfa
    (f b) hgb hg hgbker q).trans
      (principalEuler_pointFibre_original p a b hf hfa (q.val.under (Laurent S)))
  have hQ : (q.val.under (Laurent S)).under (Laurent R) =
      q.val.comap (coefficientMap (g.comp f)) := by
    change (q.val.comap (coefficientMap g)).comap (coefficientMap f) = _
    rw [Ideal.comap_comap]
    congr 1
    exact (MonoidAlgebra.mapRingHom_comp (M := Character) g f).symm
  change FreeAbelianGroup.coeff q (quotientFibreCycleMap (S := T)
    (quotientFibreCycleMap (S := S) (FreeAbelianGroup.of p))) = _
  rw [he]
  let E : PrimeSpectrum (Laurent R) → ℤ := fun P =>
    principalEuler (N := ScalarCokernel (LocalPointQuotient p P.asIdeal)
      (algebraMap R (Localization.AtPrime P.asIdeal) a))
      (algebraMap R (Localization.AtPrime P.asIdeal) b)
  change E ⟨(q.val.under (Laurent S)).under (Laurent R), inferInstance⟩ =
    E ⟨q.val.comap (coefficientMap (g.comp f)), inferInstance⟩
  exact congrArg E (PrimeSpectrum.ext hQ)

variable {U : Type u} [CommRing U]

omit [Algebra R S] in
/-- Literal quotient-fibre cycle maps commute around a principal coordinate
square. The proof is coefficientwise on every actual point generator. -/
theorem quotientFibreCycleMapFor_principal_square
    [IsNoetherianRing S] [IsNoetherianRing U] [IsNoetherianRing T]
    [IsDomain R] [IsIntegrallyClosed R] [IsDomain S] [IsDomain U]
    (f : R →+* S) (g : S →+* T) (f' : R →+* U) (g' : U →+* T)
    (a b : R) (ha : a ≠ 0) (hb : b ≠ 0)
    (hf : Function.Surjective f) (hfa : RingHom.ker f = Ideal.span ({a} : Set R))
    (hfb : f b ≠ 0) (hg : Function.Surjective g)
    (hgb : RingHom.ker g = Ideal.span ({f b} : Set S))
    (hf' : Function.Surjective f') (hf'b : RingHom.ker f' = Ideal.span ({b} : Set R))
    (hf'a : f' a ≠ 0) (hg' : Function.Surjective g')
    (hg'a : RingHom.ker g' = Ideal.span ({f' a} : Set U))
    (hcomp : g.comp f = g'.comp f') :
    (quotientFibreCycleMapFor g).comp (quotientFibreCycleMapFor f) =
      (quotientFibreCycleMapFor g').comp (quotientFibreCycleMapFor f') := by
  apply FreeAbelianGroup.lift_ext
  intro p
  apply (FreeAbelianGroup.equivFinsupp (FiniteDominantPrime T)).injective
  ext q
  change FreeAbelianGroup.coeff q ((quotientFibreCycleMapFor g)
    ((quotientFibreCycleMapFor f) (FreeAbelianGroup.of p))) =
    FreeAbelianGroup.coeff q ((quotientFibreCycleMapFor g')
      ((quotientFibreCycleMapFor f') (FreeAbelianGroup.of p)))
  rw [quotientFibreCycleMapFor_composition_coeff_eq_originalEuler f g p a b hf hfa hfb hg hgb q,
    quotientFibreCycleMapFor_composition_coeff_eq_originalEuler f' g' p b a hf' hf'b hf'a hg'
      hg'a q,
    hcomp]
  exact originalPointDoubleEuler_interchange p a b ha hb _ q

end AlgebraicGeometry.Torus.FiniteCorrespondence
