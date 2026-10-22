/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.DiscreteValuationRing.ParameterDenominators
public import Aglib.RingTheory.Localization.ProjectedResidue

/-! # The projected centre with its actual parameter residue action

The denominator identity is proved from the source coefficient triangle. The
actual source point is then compared with the residue map of the parameter DVR.
-/

@[expose] public noncomputable section

open IsLocalRing MvPolynomial

namespace ParameterLocalization.ProjectedCentre

variable {R A K ι : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [CommRing A] [Algebra R A] [Field K] [Algebra (ResidueField R) K]
variable (p : R) [Fact (Irreducible p)] (D : Subalgebra (ResidueField R) K)
  (f : A →+* D)
  (hf : f.comp (algebraMap R A) = (algebraMap (ResidueField R) D).comp (residue R))
  (b : ι → A)

/-- The denominators are the actual parameter prime complement in the source. -/
def sourceDenominators : Submonoid A :=
  (parameterIdeal R ι p).primeCompl.map (aeval b).toRingHom

/-- Their residue image is proved, not postulated. -/
theorem map_sourceDenominators (p : R) [Fact (Irreducible p)]
    (D : Subalgebra (ResidueField R) K) (f : A →+* D)
    (hf : f.comp (algebraMap R A) = (algebraMap (ResidueField R) D).comp (residue R))
    (b : ι → A) :
    (sourceDenominators p b).map f =
      SeparatingParameterLocalization.denominators D (fun i => f (b i)) :=
  map_parameterDenominators R ι p f hf b

/-- The actual parameter DVR maps to the actual localized source. -/
def scalarMap : Ring R ι p →+* Localization (sourceDenominators p b) :=
  IsLocalization.map (M := (parameterIdeal R ι p).primeCompl)
    (T := sourceDenominators p b) (Localization (sourceDenominators p b))
    (aeval b).toRingHom (parameterIdeal R ι p).primeCompl.le_comap_map

/-- The parameter map preserves each original polynomial in the selected coordinates. -/
@[simp] theorem scalarMap_algebraMap (q : MvPolynomial ι R) :
    scalarMap p b (algebraMap (MvPolynomial ι R) (Ring R ι p) q) =
      algebraMap A (Localization (sourceDenominators p b)) (aeval b q) :=
  IsLocalization.map_eq (M := (parameterIdeal R ι p).primeCompl)
    (S := Ring R ι p) (T := sourceDenominators p b)
    (Q := Localization (sourceDenominators p b))
    (g := (aeval b).toRingHom) (parameterIdeal R ι p).primeCompl.le_comap_map q

variable (hy : AlgebraicIndependent (ResidueField R) (fun i => (f (b i) : K)))

/-- The genuine projected residue point, with no denominator-image hypothesis. -/
def point (p : R) [Fact (Irreducible p)] (D : Subalgebra (ResidueField R) K)
    (f : A →+* D)
    (hf : f.comp (algebraMap R A) = (algebraMap (ResidueField R) D).comp (residue R))
    (b : ι → A)
    (hy : AlgebraicIndependent (ResidueField R) (fun i => (f (b i) : K))) :
    Localization (sourceDenominators p b) →+* K :=
  SeparatingParameterLocalization.projectedPoint D (fun i => f (b i)) f
    (sourceDenominators p b) (map_sourceDenominators p D f hf b) hy

/-- The projected point preserves the original source residue map. -/
@[simp] theorem point_algebraMap (a : A) :
    point p D f hf b hy (algebraMap A (Localization (sourceDenominators p b)) a) =
      (f a : K) :=
  SeparatingParameterLocalization.projectedPoint_algebraMap D (fun i => f (b i)) f
    (sourceDenominators p b) (map_sourceDenominators p D f hf b) hy a

/-- Its centre is exactly the extension of the actual old centre. -/
theorem ker_point :
    RingHom.ker (point p D f hf b hy) =
      (RingHom.ker f).map (algebraMap A (Localization (sourceDenominators p b))) :=
  SeparatingParameterLocalization.ker_projectedPoint D (fun i => f (b i)) f
    (sourceDenominators p b) (map_sourceDenominators p D f hf b) hy

/-- Algebraicity over the actual parameter fraction field makes this point surjective. -/
theorem point_surjective [IsFractionRing D K] (hs : Function.Surjective f)
    (halg : letI :=
        (SeparatingParameterLocalization.fractionMap D (fun i => f (b i)) hy).toAlgebra
      Algebra.IsAlgebraic (FractionRing (MvPolynomial ι (ResidueField R))) K) :
    Function.Surjective (point p D f hf b hy) :=
  SeparatingParameterLocalization.projectedPoint_surjective D (fun i => f (b i)) f
    (sourceDenominators p b) (map_sourceDenominators p D f hf b) hy hs halg

/-- The parameter action is exactly the actual parameter DVR residue action followed by
canonical fraction evaluation. This is the scalar comparison needed for finite separability. -/
theorem point_comp_scalarMap :
    (point p D f hf b hy).comp (scalarMap p b) =
      (SeparatingParameterLocalization.fractionMap D (fun i => f (b i)) hy).comp
        ((residueFieldAlgEquiv R ι p).toRingHom.comp (residue (Ring R ι p))) := by
  apply IsLocalization.ringHom_ext (parameterIdeal R ι p).primeCompl
  have hpoly : f.comp (aeval b).toRingHom =
      (aeval (R := ResidueField R) (fun i => f (b i))).toRingHom.comp
        (MvPolynomial.map (residue R)) := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp only [RingHom.comp_apply, MvPolynomial.map_C]
      change f (aeval b (C r)) =
        aeval (R := ResidueField R) (fun i => f (b i)) (C (residue R r))
      rw [aeval_C, aeval_C]
      exact DFunLike.congr_fun hf r
    · intro i
      simp only [RingHom.comp_apply, MvPolynomial.map_X]
      change f (aeval b (X i)) = aeval (R := ResidueField R) (fun i => f (b i)) (X i)
      rw [aeval_X, aeval_X]
  apply RingHom.ext
  intro q
  simp only [RingHom.comp_apply, scalarMap_algebraMap, point_algebraMap]
  change (f (aeval b q) : K) =
    SeparatingParameterLocalization.fractionMap D (fun i => f (b i)) hy
      (residueFieldAlgEquiv R ι p
        (residue (Ring R ι p) (algebraMap (MvPolynomial ι R) (Ring R ι p) q)))
  rw [residueFieldAlgEquiv_polynomial,
    SeparatingParameterLocalization.fractionMap, IsFractionRing.lift_algebraMap]
  have h := DFunLike.congr_fun hpoly q
  change f (aeval b q) = aeval (fun i => f (b i)) (MvPolynomial.map (residue R) q) at h
  rw [h]
  exact SeparatingParameterLocalization.coe_aeval D (fun i => f (b i)) _

end ParameterLocalization.ProjectedCentre
