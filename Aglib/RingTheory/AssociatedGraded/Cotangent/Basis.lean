/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.MvPolynomial.DegreeOne.Equiv
public import Aglib.RingTheory.AssociatedGraded.Cotangent.Graded
public import Mathlib.LinearAlgebra.Dimension.OrzechProperty
public import Mathlib.RingTheory.LocalRing.ResidueField.Defs

/-!
# Entire original cotangent kernels in two genuine generating bases

Two actual minimal generating families give bases of the original cotangent
quotient. Their linear comparison extends on the same native polynomials,
retaining the whole canonical map and transporting its entire kernel.
-/

@[expose] public noncomputable section
set_option autoImplicit false

universe u v

namespace IsLocalRing

open Module MvPolynomial

variable {A : Type u} [CommRing A] [IsLocalRing A] {ι : Type v} [Fintype ι]

local instance cotangentBasisQuotient_orzechProperty : OrzechProperty (A ⧸ maximalIdeal A) := by
  let : Field (A ⧸ maximalIdeal A) := Ideal.Quotient.field (maximalIdeal A)
  infer_instance

/-- The original cotangent classes form the stock basis forced by actual generation and rank. -/
def cotangentBasisOfGenerators (g : ι → maximalIdeal A)
    (hgen : Ideal.span (Set.range fun i => (g i : A)) = maximalIdeal A)
    (hcard : Fintype.card ι = Module.finrank (A ⧸ maximalIdeal A) (maximalIdeal A).Cotangent) :
    Basis ι (A ⧸ maximalIdeal A) (maximalIdeal A).Cotangent :=
  basisOfTopLeSpanOfCardEqFinrank (fun i => (maximalIdeal A).toCotangent (g i))
    (by rw [Ideal.cotangent_span_of_ideal_span (maximalIdeal A) g hgen]) hcard

/-- Every basis element is the original displayed ideal element modulo the original square. -/
theorem cotangentBasisOfGenerators_apply (g : ι → maximalIdeal A)
    (hgen : Ideal.span (Set.range fun i => (g i : A)) = maximalIdeal A)
    (hcard : Fintype.card ι = Module.finrank (A ⧸ maximalIdeal A) (maximalIdeal A).Cotangent)
    (i : ι) : cotangentBasisOfGenerators g hgen hcard i =
      (maximalIdeal A).toCotangent (g i) := by
  exact congrFun (coe_basisOfTopLeSpanOfCardEqFinrank _ _ _) i

/-- Compare the original polynomial-variable basis with the actual cotangent basis. -/
def cotangentDegreeOneEquiv (g : ι → maximalIdeal A)
    (hgen : Ideal.span (Set.range fun i => (g i : A)) = maximalIdeal A)
    (hcard : Fintype.card ι = Module.finrank (A ⧸ maximalIdeal A) (maximalIdeal A).Cotangent) :
    homogeneousSubmodule ι (A ⧸ maximalIdeal A) 1 ≃ₗ[A ⧸ maximalIdeal A]
      (maximalIdeal A).Cotangent :=
  (homogeneousDegreeOneBasis (A ⧸ maximalIdeal A) ι).equiv
    (cotangentBasisOfGenerators g hgen hcard) (Equiv.refl ι)

/-- Original variables go to their actual cotangent classes under the native basis comparison. -/
theorem cotangentDegreeOneEquiv_basis (g : ι → maximalIdeal A)
    (hgen : Ideal.span (Set.range fun i => (g i : A)) = maximalIdeal A)
    (hcard : Fintype.card ι = Module.finrank (A ⧸ maximalIdeal A) (maximalIdeal A).Cotangent)
    (i : ι) : cotangentDegreeOneEquiv g hgen hcard
      (homogeneousDegreeOneBasis (A ⧸ maximalIdeal A) ι i) =
        (maximalIdeal A).toCotangent (g i) := by
  rw [cotangentDegreeOneEquiv, Basis.equiv_apply, Equiv.refl_apply,
    cotangentBasisOfGenerators_apply]

/-- The original canonical map on degree one is the same native cotangent symbol. -/
theorem cotangentPolynomialMap_degreeOne (g : ι → maximalIdeal A)
    (hgen : Ideal.span (Set.range fun i => (g i : A)) = maximalIdeal A)
    (hcard : Fintype.card ι = Module.finrank (A ⧸ maximalIdeal A) (maximalIdeal A).Cotangent)
    (p : homogeneousSubmodule ι (A ⧸ maximalIdeal A) 1) :
    Ideal.cotangentPolynomialMap (maximalIdeal A) g p.val =
      Ideal.cotangentSymbol (maximalIdeal A) (cotangentDegreeOneEquiv g hgen hcard p) := by
  have h : (Ideal.cotangentPolynomialMap (maximalIdeal A) g).toLinearMap.comp
      (homogeneousSubmodule ι (A ⧸ maximalIdeal A) 1).subtype =
        (Ideal.cotangentSymbol (maximalIdeal A)).comp
          (cotangentDegreeOneEquiv g hgen hcard).toLinearMap := by
    apply (homogeneousDegreeOneBasis (A ⧸ maximalIdeal A) ι).ext
    intro i
    change Ideal.cotangentPolynomialMap (maximalIdeal A) g
      (homogeneousDegreeOneBasis (A ⧸ maximalIdeal A) ι i).val =
        Ideal.cotangentSymbol (maximalIdeal A) (cotangentDegreeOneEquiv g hgen hcard
          (homogeneousDegreeOneBasis (A ⧸ maximalIdeal A) ι i))
    rw [homogeneousDegreeOneBasis_val, cotangentDegreeOneEquiv_basis,
      Ideal.cotangentPolynomialMap_X_cotangent]
  exact LinearMap.congr_fun h p

/-- The unique native polynomial extension of the actual cotangent-basis comparison. -/
def cotangentBasisChange (g g' : ι → maximalIdeal A)
    (hgen : Ideal.span (Set.range fun i => (g i : A)) = maximalIdeal A)
    (hgen' : Ideal.span (Set.range fun i => (g' i : A)) = maximalIdeal A)
    (hcard : Fintype.card ι = Module.finrank (A ⧸ maximalIdeal A) (maximalIdeal A).Cotangent) :
    MvPolynomial ι (A ⧸ maximalIdeal A) ≃ₐ[A ⧸ maximalIdeal A]
      MvPolynomial ι (A ⧸ maximalIdeal A) :=
  degreeOneLinearEquivAlgEquiv
    ((cotangentDegreeOneEquiv g hgen hcard).trans (cotangentDegreeOneEquiv g' hgen' hcard).symm)

/-- The entire original canonical map commutes with the actual change of generating basis. -/
theorem cotangentBasisChange_square (g g' : ι → maximalIdeal A)
    (hgen : Ideal.span (Set.range fun i => (g i : A)) = maximalIdeal A)
    (hgen' : Ideal.span (Set.range fun i => (g' i : A)) = maximalIdeal A)
    (hcard : Fintype.card ι = Module.finrank (A ⧸ maximalIdeal A) (maximalIdeal A).Cotangent) :
    (Ideal.cotangentPolynomialMap (maximalIdeal A) g').comp
        (cotangentBasisChange g g' hgen hgen' hcard).toAlgHom =
      Ideal.cotangentPolynomialMap (maximalIdeal A) g := by
  apply MvPolynomial.algHom_ext
  intro i
  change Ideal.cotangentPolynomialMap (maximalIdeal A) g'
    (degreeOneLinearEquivAlgEquiv
      ((cotangentDegreeOneEquiv g hgen hcard).trans
        (cotangentDegreeOneEquiv g' hgen' hcard).symm) (X i)) = _
  rw [← homogeneousDegreeOneBasis_val (A ⧸ maximalIdeal A) ι i,
    degreeOneLinearEquivAlgEquiv_apply, cotangentPolynomialMap_degreeOne g' hgen' hcard]
  simp only [LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply]
  rw [cotangentDegreeOneEquiv_basis, homogeneousDegreeOneBasis_val,
    Ideal.cotangentPolynomialMap_X_cotangent]

/-- The entire original kernel, not a selected relation, changes by the same polynomial map. -/
theorem cotangentBasisChange_kernel (g g' : ι → maximalIdeal A)
    (hgen : Ideal.span (Set.range fun i => (g i : A)) = maximalIdeal A)
    (hgen' : Ideal.span (Set.range fun i => (g' i : A)) = maximalIdeal A)
    (hcard : Fintype.card ι = Module.finrank (A ⧸ maximalIdeal A) (maximalIdeal A).Cotangent) :
    RingHom.ker (Ideal.cotangentPolynomialMap (maximalIdeal A) g').toRingHom =
      (RingHom.ker (Ideal.cotangentPolynomialMap (maximalIdeal A) g).toRingHom).map
        (cotangentBasisChange g g' hgen hgen' hcard).toRingHom := by
  let σ := cotangentBasisChange g g' hgen hgen' hcard
  have h := congrArg (fun f => RingHom.ker f.toRingHom)
    (cotangentBasisChange_square g g' hgen hgen' hcard)
  change RingHom.ker ((Ideal.cotangentPolynomialMap (maximalIdeal A) g').toRingHom.comp
    σ.toRingHom) = RingHom.ker (Ideal.cotangentPolynomialMap (maximalIdeal A) g).toRingHom at h
  rw [← RingHom.comap_ker] at h
  rw [← h, Ideal.map_comap_of_surjective σ.toRingHom σ.surjective]

/-- A genuine full linear-square kernel remains a full linear-square kernel in the target basis. -/
theorem exists_cotangentBasisChange_square_kernel (g g' : ι → maximalIdeal A)
    (hgen : Ideal.span (Set.range fun i => (g i : A)) = maximalIdeal A)
    (hgen' : Ideal.span (Set.range fun i => (g' i : A)) = maximalIdeal A)
    (hcard : Fintype.card ι = Module.finrank (A ⧸ maximalIdeal A) (maximalIdeal A).Cotangent)
    (L : MvPolynomial ι (A ⧸ maximalIdeal A)) (hL : L.IsHomogeneous 1) (hL0 : L ≠ 0)
    (hker : RingHom.ker (Ideal.cotangentPolynomialMap (maximalIdeal A) g).toRingHom =
      Ideal.span {L ^ 2}) :
    ∃ L' : MvPolynomial ι (A ⧸ maximalIdeal A), L'.IsHomogeneous 1 ∧ L' ≠ 0 ∧
      RingHom.ker (Ideal.cotangentPolynomialMap (maximalIdeal A) g').toRingHom =
        Ideal.span {L' ^ 2} := by
  let σ := cotangentBasisChange g g' hgen hgen' hcard
  refine ⟨σ L, ?_, ?_, ?_⟩
  · exact degreeOneLinearEquivAlgEquiv_isHomogeneous _ hL
  · exact (map_ne_zero_iff σ σ.injective).mpr hL0
  · rw [cotangentBasisChange_kernel g g' hgen hgen' hcard, hker,
      Ideal.map_span, Set.image_singleton, map_pow]
    rfl

end IsLocalRing
