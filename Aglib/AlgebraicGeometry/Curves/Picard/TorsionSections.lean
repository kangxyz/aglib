/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Curves.Picard.DivisorInverse
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Aglib.AlgebraicGeometry.Modules.Invertible.Basic
public import Aglib.AlgebraicGeometry.Modules.InternalHom
public import Aglib.AlgebraicGeometry.Modules.Invertible.Dual
public import Aglib.AlgebraicGeometry.Modules.Invertible.Tensor
public import Aglib.AlgebraicGeometry.Modules.Invertible.TensorAssociator
public import Aglib.AlgebraicGeometry.Modules.Pullback.OpenRestriction

/-!
# Regular-curve Picard supplier

Source: `R5Lab.AlgebraicGeometry.Curves.Picard.TorsionSections`, R5 revision
`f8a3314ddecffcada2ec721d26d56a937bed9690`, source SHA-256
`446aa65c8ae0b068534fcbaec0ad0bdce75c4a750465920650671ed5dec85f3c`.
Actual divisors, quotient relations, fractional inclusions, tensor comparisons,
equality transports and principal trivializations are preserved. The original
regularity, level and product-formula premises remain explicit. General native
line-bundle, tensor, descent and cohomology suppliers are reused.
-/

@[expose] public section

open _root_.AlgebraicGeometry.Scheme.Modules.Invertible
open _root_.AlgebraicGeometry.Scheme.Modules.RationalFunctions

open _root_.AlgebraicGeometry.Scheme.Modules.Invertible (LineBundle classOf trivialLineBundle)

/-!
# Global sections of nontrivial degree-zero and torsion line bundles

The actual divisor sheaf `O(D)` has rational sections satisfying
`ord_x(f) + D(x) ≥ 0`. A nonzero global section therefore makes `div(f) + D`
effective. If `D` has degree zero and the principal product formula holds,
this effective divisor has degree zero. Positivity of the actual closed-point
residue-field weights forces it to vanish, so `D` is principal.

The proved actual divisor/Picard comparison transports this argument to every
actual line bundle. A nonzero global section of a degree-zero line bundle
constructs an isomorphism with the structure module sheaf. Consequently the
global section module of a nontrivial degree-zero line bundle is a singleton;
the same holds for any nontrivial positive-level torsion line bundle.

These independently specified statements retain `PrincipalProductFormula` as
an explicit input. Closed-point weight positivity is proved here from local
finite type, without an algebraically closed base-field assumption. The line
bundle results use an integral Noetherian scheme of dimension at most one
with actual closed DVR stalks. They apply to proper regular curves once the
explicit product-formula input is supplied. They establish the global-section
vanishing slice, without asserting semicontinuity or finite-type base spreading.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
open AlgebraicGeometry.Scheme.OverField.Curve.Divisors

namespace AlgebraicGeometry.Scheme.OverField.Curve.Picard.TorsionSections

open DivisorClass DivisorInverse Degree

universe u

variable {k : Type u} [Field k] (X : Scheme.{u}) (p : X ⟶ Spec (.of k))

/-- Actual closed-point residue-field degree is strictly positive under local
finite type over a field. -/
theorem closedPoint_weight_pos [LocallyOfFiniteType p] (x : ClosedPoint X) :
    0 < weight X p x := by
  let := residueAlgebra X p x.val
  let : Module.Finite k (X.residueField x.val) := residue_finite X p x
  change 0 < (Module.finrank k (X.residueField x.val) : ℤ)
  exact_mod_cast (Module.finrank_pos_iff_of_free k (X.residueField x.val)).mpr inferInstance

/-- A divisor with nonnegative coefficients and actual residue-weighted degree
zero is the zero divisor. -/
theorem effective_degree_zero [LocallyOfFiniteType p] (D : Divisor X)
    (heff : ∀ x, 0 ≤ D x) (hdegree : degDiv X p D = 0) : D = 0 := by
  classical
  have hs : ∀ x ∈ D.support, D x * weight X p x = 0 := by
    apply (Finset.sum_eq_zero_iff_of_nonneg (fun x _ =>
      mul_nonneg (heff x) (closedPoint_weight_pos X p x).le)).mp
    rwa [degDiv_apply] at hdegree
  ext x
  change D x = 0
  by_cases hx : x ∈ D.support
  · exact (mul_eq_zero.mp (hs x hx)).resolve_right
      (ne_of_gt (closedPoint_weight_pos X p x))
  · exact Finsupp.notMem_support_iff.mp hx

variable [IsIntegral X] [IsNoetherian X]
variable [∀ x : ClosedPoint X, IsDiscreteValuationRing (X.presheaf.stalk x.val)]
variable [LocallyOfFiniteType p]

local instance : Nonempty (⊤ : X.Opens) := ⟨⟨genericPoint X, trivial⟩⟩

/-- A nonzero global section of an actual degree-zero divisor sheaf constructs
a rational unit whose principal divisor is the displayed divisor. -/
theorem divisor_principal_of_nonzero_section
    (hprod : PrincipalProductFormula X p) (D : Divisor X) (hdegree : degDiv X p D = 0)
    (s : (divisorSheaf X D).val.obj (op ⊤)) (hs : s ≠ 0) :
    ∃ f : X.functionFieldˣ, principal X (Additive.ofMul f) = D := by
  let z := divisorSheafSectionsEquiv X D ⊤ s
  have hz : (z : X.functionField) ≠ 0 := by
    intro hz
    apply hs
    apply (divisorSheafSectionsEquiv X D ⊤).injective
    exact (Subtype.ext hz).trans (divisorSheafSectionsEquiv X D ⊤).map_zero.symm
  let f : X.functionFieldˣ := Units.mk0 (z : X.functionField) hz
  have heff : ∀ x, 0 ≤ (principal X (Additive.ofMul f) + D) x := by
    intro x
    exact z.property.resolve_left hz x trivial
  have hdegree' : degDiv X p (principal X (Additive.ofMul f) + D) = 0 := by
    rw [map_add, hprod f, hdegree, add_zero]
  have hzero := effective_degree_zero X p _ heff hdegree'
  refine ⟨f⁻¹, ?_⟩
  ext x
  have hx := congrArg (fun E : Divisor X => E x) hzero
  change X.ord (f : X.functionField) x.val + D x = 0 at hx
  change X.ord ((f⁻¹ : X.functionFieldˣ) : X.functionField) x.val = D x
  rw [order_inv]
  linarith

/-- The actual divisor class vanishes when its degree-zero divisor sheaf has
a nonzero global section. -/
theorem divisorClass_eq_zero_of_nonzero_section
    (hprod : PrincipalProductFormula X p) (D : Divisor X) (hdegree : degDiv X p D = 0)
    (s : (divisorSheaf X D).val.obj (op ⊤)) (hs : s ≠ 0) :
    (QuotientAddGroup.mk D : Divisor X ⧸ (principal X).range) = 0 := by
  obtain ⟨f, hf⟩ := divisor_principal_of_nonzero_section X p hprod D hdegree s hs
  exact (QuotientAddGroup.eq_zero_iff D).mpr ⟨Additive.ofMul f, hf⟩

/-- The principal-divisor construction gives an actual trivialization of the
degree-zero divisor sheaf carrying a nonzero global section. -/
theorem divisorSheaf_trivial_of_nonzero_section
    (hdim : topologicalKrullDim X ≤ 1) (hprod : PrincipalProductFormula X p)
    (D : Divisor X) (hdegree : degDiv X p D = 0)
    (s : (divisorSheaf X D).val.obj (op ⊤)) (hs : s ≠ 0) :
    Nonempty (divisorSheaf X D ≅ SheafOfModules.unit X.ringCatSheaf) := by
  obtain ⟨f, hf⟩ := divisor_principal_of_nonzero_section X p hprod D hdegree s hs
  rw [← hf]
  exact ⟨principalTrivialization X hdim f⟩

/-- A degree-zero actual line bundle with a nonzero global section is
isomorphic to the actual structure module sheaf. -/
theorem lineBundle_trivial_of_nonzero_section
    (hdim : topologicalKrullDim X ≤ 1) (hprod : PrincipalProductFormula X p)
    (L : LineBundle X) (hdegree : lineBundleDegree X p hdim hprod L = 0)
    (s : L.val.val.obj (op ⊤)) (hs : s ≠ 0) :
    Nonempty (L.val ≅ SheafOfModules.unit X.ringCatSheaf) := by
  obtain ⟨D, ⟨e⟩⟩ := exists_divisor_iso X L.val L.property hdim
  let q : L.val.val.obj (op ⊤) ≃ₗ[Γ(X, ⊤)]
      (divisorSheaf X D).val.obj (op ⊤) :=
    ((PresheafOfModules.evaluation X.ringCatSheaf.obj (op ⊤)).mapIso
      ((SheafOfModules.forget _).mapIso e)).toLinearEquiv
  have ht : q s ≠ 0 := by
    intro ht
    exact hs (q.injective (ht.trans q.map_zero.symm))
  have hD : degDiv X p D = 0 := by
    rw [← lineBundleDegree_divisor X p hdim hprod]
    exact (lineBundleDegree_iso X p hdim hprod e).symm.trans hdegree
  obtain ⟨a⟩ := divisorSheaf_trivial_of_nonzero_section X p hdim hprod D hD (q s) ht
  exact ⟨e ≪≫ a⟩

/-- Every global section of a nontrivial degree-zero actual line bundle is zero. -/
theorem section_eq_zero_of_degree_zero_nontrivial
    (hdim : topologicalKrullDim X ≤ 1) (hprod : PrincipalProductFormula X p)
    (L : LineBundle X) (hdegree : lineBundleDegree X p hdim hprod L = 0)
    (hL : classOf X L ≠ 0) (s : L.val.val.obj (op ⊤)) : s = 0 := by
  by_contra hs
  obtain ⟨e⟩ := lineBundle_trivial_of_nonzero_section X p hdim hprod L hdegree s hs
  apply hL
  change classOf X L = classOf X (trivialLineBundle X)
  exact Quotient.sound ⟨e ≪≫ (CategoryTheory.Limits.coproductUniqueIso
    (fun _ : PUnit.{u + 1} => SheafOfModules.unit X.ringCatSheaf)).symm⟩

/-- Positive-level torsion gives degree zero, so every global section of a
nontrivial torsion line bundle is zero. -/
theorem section_eq_zero_of_nontrivial_torsion
    (hdim : topologicalKrullDim X ≤ 1) (hprod : PrincipalProductFormula X p)
    (L : LineBundle X) (n : ℕ) (hn : 0 < n) (htors : n • classOf X L = 0)
    (hL : classOf X L ≠ 0) (s : L.val.val.obj (op ⊤)) : s = 0 := by
  apply section_eq_zero_of_degree_zero_nontrivial X p hdim hprod L _ hL s
  exact picard_torsion_degree_zero X p hdim hprod n hn (classOf X L) htors

/-- The actual global section module is a singleton for a nontrivial
degree-zero line bundle; this is the vanishing input for future semicontinuity. -/
theorem globalSections_subsingleton_of_degree_zero_nontrivial
    (hdim : topologicalKrullDim X ≤ 1) (hprod : PrincipalProductFormula X p)
    (L : LineBundle X) (hdegree : lineBundleDegree X p hdim hprod L = 0)
    (hL : classOf X L ≠ 0) : Subsingleton (L.val.val.obj (op ⊤)) := by
  refine ⟨fun s t => ?_⟩
  exact (section_eq_zero_of_degree_zero_nontrivial X p hdim hprod L hdegree hL s).trans
    (section_eq_zero_of_degree_zero_nontrivial X p hdim hprod L hdegree hL t).symm

/-- The actual global section module is a singleton for a nontrivial
positive-level torsion line bundle. -/
theorem globalSections_subsingleton_of_nontrivial_torsion
    (hdim : topologicalKrullDim X ≤ 1) (hprod : PrincipalProductFormula X p)
    (L : LineBundle X) (n : ℕ) (hn : 0 < n) (htors : n • classOf X L = 0)
    (hL : classOf X L ≠ 0) : Subsingleton (L.val.val.obj (op ⊤)) := by
  refine ⟨fun s t => ?_⟩
  exact (section_eq_zero_of_nontrivial_torsion X p hdim hprod L n hn htors hL s).trans
    (section_eq_zero_of_nontrivial_torsion X p hdim hprod L n hn htors hL t).symm

end AlgebraicGeometry.Scheme.OverField.Curve.Picard.TorsionSections
