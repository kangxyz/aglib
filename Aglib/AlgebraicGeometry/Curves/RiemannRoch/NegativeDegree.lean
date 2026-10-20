/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Curves.Picard.DivisorInverse
public import Aglib.AlgebraicGeometry.Cohomology.Modules.Basic

/-!
# Negative degree has no sections

The degree is the original residue-weighted divisor degree transported through
`divisorPicardEquiv`. A nonzero fractional section of `O(D)` makes
`principal(f) + D` effective. Its nonnegative residue-weighted degree and the
specified principal product formula imply `deg D ≥ 0`.

The proof uses the actual divisor sheaf and the proved actual `O(D)`
identification. It works over every field; properness and algebraic closure
are unnecessary once the principal product formula is supplied.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory Opposite
open AlgebraicGeometry.Scheme.Modules.Invertible
open AlgebraicGeometry.Scheme.Cohomology

namespace AlgebraicGeometry.Scheme.OverField.Curve

universe u

open Divisors Picard.DivisorClass

variable {K : Type u} [Field K] (X : Scheme.{u}) (p : X ⟶ Spec (.of K))

/-- Effective actual divisors have nonnegative residue-weighted degree. -/
theorem divisorDegree_nonneg {D : Divisor X} (hD : ∀ x, 0 ≤ D x) :
    0 ≤ Picard.Degree.degDiv X p D := by
  rw [Picard.Degree.degDiv_apply]
  exact Finset.sum_nonneg fun x _ => mul_nonneg (hD x) (Int.natCast_nonneg _)

variable [IsIntegral X] [IsNoetherian X]
variable [∀ x : ClosedPoint X, IsDiscreteValuationRing (X.presheaf.stalk x.val)]

omit [∀ x : ClosedPoint X, IsDiscreteValuationRing (X.presheaf.stalk x.val)] in
/-- The product formula forces nonnegative degree whenever an actual fractional
section on the whole curve is nonzero. -/
theorem divisorDegree_nonneg_of_fractionalSection
    (hprod : Picard.Degree.PrincipalProductFormula X p)
    {D : Divisor X} {f : X.functionField}
    (hf : IsFractionalSection X D ⊤ f) (hne : f ≠ 0) :
    0 ≤ Picard.Degree.degDiv X p D := by
  let g : X.functionFieldˣ := Units.mk0 f hne
  have heff : ∀ x, 0 ≤ (principal X (Additive.ofMul g) + D) x := by
    intro x
    exact hf.resolve_left hne x (by trivial)
  have hdeg := divisorDegree_nonneg X p heff
  rw [map_add, hprod g, zero_add] at hdeg
  exact hdeg

/-- Negative original divisor degree kills every actual global section of `O(D)`. -/
theorem divisorSheafSections_subsingleton_of_neg_degree
    (hprod : Picard.Degree.PrincipalProductFormula X p)
    (D : Divisor X) (hD : Picard.Degree.degDiv X p D < 0) :
    Subsingleton ((divisorSheaf X D).val.obj (op ⊤)) := by
  let : Nonempty (⊤ : X.Opens) := ⟨⟨genericPoint X, by trivial⟩⟩
  have : Subsingleton (fractionalSections X D ⊤) := by
    apply subsingleton_of_forall_eq 0
    intro f
    apply Subtype.ext
    change (f : X.functionField) = 0
    by_contra hne
    exact (not_le_of_gt hD)
      (divisorDegree_nonneg_of_fractionalSection X p hprod f.property hne)
  exact (divisorSheafSectionsEquiv X D ⊤).injective.subsingleton

/-- Negative original line-bundle degree kills all its actual global sections. -/
theorem lineBundleSections_subsingleton_of_neg_degree
    (hdim : topologicalKrullDim X ≤ 1)
    (hprod : Picard.Degree.PrincipalProductFormula X p)
    (L : LineBundle X) (hL : Picard.Degree.lineBundleDegree X p hdim hprod L < 0) :
    Subsingleton (L.val.val.obj (op ⊤)) := by
  obtain ⟨D, ⟨e⟩⟩ := Picard.DivisorInverse.exists_divisor_iso X L.val L.property hdim
  have he : Picard.Degree.lineBundleDegree X p hdim hprod L =
      Picard.Degree.degDiv X p D :=
    (Picard.Degree.lineBundleDegree_iso X p hdim hprod
      (N := divisorLineBundle X hdim D) e).trans
        (Picard.Degree.lineBundleDegree_divisor X p hdim hprod D)
  have := divisorSheafSections_subsingleton_of_neg_degree X p hprod D (he ▸ hL)
  let E : L.val.val.obj (op ⊤) ≃ₗ[Γ(X, ⊤)] (divisorSheaf X D).val.obj (op ⊤) :=
    ((PresheafOfModules.evaluation X.ringCatSheaf.obj (op ⊤)).mapIso
      ((SheafOfModules.forget _).mapIso e)).toLinearEquiv
  exact E.injective.subsingleton

/-- The same vanishing in actual degree-zero module cohomology, with its original
structural scalar action. -/
theorem lineBundleH0_subsingleton_of_neg_degree (Y : FScheme K)
    [IsIntegral Y.left] [IsNoetherian Y.left]
    [∀ x : ClosedPoint Y.left, IsDiscreteValuationRing (Y.left.presheaf.stalk x.val)]
    (hdim : topologicalKrullDim Y.left ≤ 1)
    (hprod : Picard.Degree.PrincipalProductFormula Y.left Y.hom)
    (L : LineBundle Y.left)
    (hL : Picard.Degree.lineBundleDegree Y.left Y.hom hdim hprod L < 0) :
    Subsingleton (moduleCohomology K Y L.val 0) := by
  have := lineBundleSections_subsingleton_of_neg_degree Y.left Y.hom hdim hprod L hL
  exact (moduleH0Equiv Y L.val).injective.subsingleton

end AlgebraicGeometry.Scheme.OverField.Curve
