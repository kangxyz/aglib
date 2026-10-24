/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Curves.RiemannRoch.LineBundle
public import Aglib.AlgebraicGeometry.Curves.Picard.Degree.ProperCurveProductFormula

/-! # Bounded effective representatives of actual degree-zero Picard classes

Riemann--Roch gives a nonzero actual section in degree at least the coherent
genus. Its rational function produces an effective divisor in the original
divisor class. Twisting a degree-zero class by `g` times a fixed closed point
therefore represents it by an effective divisor of degree exactly `g`.

All degrees and Picard classes are the existing ones. The proper product
formula and all-genus Riemann--Roch theorem are proved suppliers, not inputs.
No Picard representability, torsion finiteness, or proper base change is used.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.Cohomology
open AlgebraicGeometry.Scheme.Modules.Invertible
open AlgebraicGeometry.Scheme.OverField.Curve.Divisors

universe u

namespace AlgebraicGeometry.Scheme.OverField.Curve.Picard

open DivisorClass Degree

variable {k : Type u} [Field k] [IsAlgClosed k] (X : FScheme k)
  [IsIntegral X.left] [IsNoetherian X.left] [IsProper X.hom]
  [∀ x : ClosedPoint X.left, IsDiscreteValuationRing (X.left.presheaf.stalk x.val)]

/-- Riemann--Roch supplies a nonzero section of the actual divisor sheaf
whenever its original degree is at least the coherent genus. -/
theorem divisorSheaf_exists_nonzero_section_of_genus_le_degree
    (hdim : topologicalKrullDim X.left = 1) (D : Divisor X.left)
    (hD : (coherentGenus k X : ℤ) ≤ degDiv X.left X.hom D) :
    ∃ s : (divisorSheaf X.left D).val.obj (op ⊤), s ≠ 0 := by
  let L := divisorLineBundle X.left hdim.le D
  have hrr := lineBundleRiemannRoch k X hdim.le
    (properCurveProductFormula k X.left X.hom hdim) L inferInstance
    (constants_bijective_of_proper_of_isAlgClosed X)
  have hdegree : lineBundleDegree X.left X.hom hdim.le
      (properCurveProductFormula k X.left X.hom hdim) L = degDiv X.left X.hom D :=
    lineBundleDegree_divisor X.left X.hom hdim.le _ D
  rw [hdegree] at hrr
  have hpos : 0 < Module.finrank k (moduleCohomology k X L.val 0) := by omega
  let : Nontrivial (moduleCohomology k X L.val 0) := Module.nontrivial_of_finrank_pos hpos
  obtain ⟨s, hs⟩ := exists_ne (0 : moduleCohomology k X L.val 0)
  refine ⟨moduleH0Equiv X L.val s, ?_⟩
  intro hz
  exact hs ((moduleH0Equiv X L.val).injective (hz.trans (moduleH0Equiv X L.val).map_zero.symm))

/-- A nonzero rational section gives an actual effective representative of the
same original divisor/Picard class, with unchanged degree. -/
theorem exists_effective_divisor_of_genus_le_degree
    (hdim : topologicalKrullDim X.left = 1) (D : Divisor X.left)
    (hD : (coherentGenus k X : ℤ) ≤ degDiv X.left X.hom D) :
    ∃ E : Divisor X.left, (∀ x, 0 ≤ E x) ∧
      degDiv X.left X.hom E = degDiv X.left X.hom D ∧
      divisorToPicard X.left hdim.le E = divisorToPicard X.left hdim.le D := by
  let : Nonempty (⊤ : X.left.Opens) := ⟨⟨genericPoint X.left, trivial⟩⟩
  obtain ⟨s, hs⟩ := divisorSheaf_exists_nonzero_section_of_genus_le_degree X hdim D hD
  let z : fractionalSections X.left D ⊤ :=
    (divisorSheafSectionsEquiv X.left D ⊤).toFun s
  have hz : (z : X.left.functionField) ≠ 0 := by
    intro hz
    apply hs
    apply (divisorSheafSectionsEquiv X.left D ⊤).injective
    exact (Subtype.ext hz).trans (divisorSheafSectionsEquiv X.left D ⊤).map_zero.symm
  let f : X.left.functionFieldˣ := Units.mk0 (z : X.left.functionField) hz
  refine ⟨principal X.left (Additive.ofMul f) + D, ?_, ?_, ?_⟩
  · intro x
    exact z.property.resolve_left hz x trivial
  · rw [map_add, properCurveProductFormula k X.left X.hom hdim f, zero_add]
  · rw [map_add, divisorToPicard_principal, zero_add]

/-- Every actual degree-zero Picard class is represented by an effective divisor
of degree exactly the coherent genus, minus that many copies of a fixed point.
This includes genus zero. -/
theorem exists_effective_degree_genus_of_picardDegree_eq_zero
    (hdim : topologicalKrullDim X.left = 1) (o : ClosedPoint X.left)
    (L : PicardGroup X.left)
    (hL : picardDegree X.left X.hom hdim.le
      (properCurveProductFormula k X.left X.hom hdim) L = 0) :
    ∃ E : Divisor X.left, (∀ x, 0 ≤ E x) ∧
      degDiv X.left X.hom E = (coherentGenus k X : ℤ) ∧
      L = divisorToPicard X.left hdim.le
        (E - Finsupp.single o (coherentGenus k X : ℤ)) := by
  obtain ⟨a, ha⟩ := divisorClassToPicard_surjective X.left hdim.le L
  obtain ⟨D, rfl⟩ := Quotient.exists_rep a
  have hclass : divisorToPicard X.left hdim.le D = L := ha
  have hdegree : degDiv X.left X.hom D = 0 := by
    rw [← picardDegree_divisor X.left X.hom hdim.le
      (properCurveProductFormula k X.left X.hom hdim)]
    exact (congrArg (picardDegree X.left X.hom hdim.le
      (properCurveProductFormula k X.left X.hom hdim)) hclass).trans hL
  let A := Finsupp.single o (coherentGenus k X : ℤ)
  have hA : degDiv X.left X.hom A = (coherentGenus k X : ℤ) := by
    simp only [A, degDiv_single, weight_eq_one, mul_one]
  have hDA : degDiv X.left X.hom (D + A) = (coherentGenus k X : ℤ) := by
    rw [map_add, hdegree, hA, zero_add]
  obtain ⟨E, heff, hdeg, hE⟩ := exists_effective_divisor_of_genus_le_degree X hdim
    (D + A) hDA.ge
  refine ⟨E, heff, hdeg.trans hDA, ?_⟩
  change L = divisorToPicard X.left hdim.le (E - A)
  rw [map_sub, hE, map_add, add_sub_cancel_right, hclass]

/-- The bounded effective-divisor statement gives an actual module-sheaf
isomorphism for each degree-zero line bundle, not only an abstract parameter. -/
theorem exists_effective_degree_genus_lineBundle_iso
    (hdim : topologicalKrullDim X.left = 1) (o : ClosedPoint X.left)
    (L : LineBundle X.left)
    (hL : lineBundleDegree X.left X.hom hdim.le
      (properCurveProductFormula k X.left X.hom hdim) L = 0) :
    ∃ E : Divisor X.left, (∀ x, 0 ≤ E x) ∧
      degDiv X.left X.hom E = (coherentGenus k X : ℤ) ∧
      Nonempty (L.val ≅ divisorSheaf X.left
        (E - Finsupp.single o (coherentGenus k X : ℤ))) := by
  obtain ⟨E, heff, hdeg, hE⟩ := exists_effective_degree_genus_of_picardDegree_eq_zero
    X hdim o (classOf X.left L) hL
  exact ⟨E, heff, hdeg, (class_eq_iff X.left L
    (divisorLineBundle X.left hdim.le _)).mp hE⟩

end AlgebraicGeometry.Scheme.OverField.Curve.Picard
