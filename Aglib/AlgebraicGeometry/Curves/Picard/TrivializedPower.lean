/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Invertible.Power.TrivializedPower
public import Aglib.AlgebraicGeometry.Curves.Picard.KummerExactness
public import Aglib.AlgebraicGeometry.Modules.Invertible.Basic
public import Aglib.AlgebraicGeometry.Modules.InternalHom
public import Aglib.AlgebraicGeometry.Modules.Invertible.Dual
public import Aglib.AlgebraicGeometry.Modules.Invertible.Tensor
public import Aglib.AlgebraicGeometry.Modules.Invertible.TensorAssociator
public import Aglib.AlgebraicGeometry.Modules.Pullback.OpenRestriction

/-!
# Regular-curve Picard supplier

Source: `R5Lab.AlgebraicGeometry.Curves.Picard.TrivializedPower`, R5 revision
`f8a3314ddecffcada2ec721d26d56a937bed9690`, source SHA-256
`fc02440ba7c01a5793638f482ce38ba82340e71104008cde5e21569dfbfb88d5`.
Actual divisors, quotient relations, fractional inclusions, tensor comparisons,
equality transports and principal trivializations are preserved. The original
regularity, level and product-formula premises remain explicit. General native
line-bundle, tensor, descent and cohomology suppliers are reused.
-/

@[expose] public section

open _root_.AlgebraicGeometry.Scheme.Modules.Invertible
open _root_.AlgebraicGeometry.Scheme.Modules.Invertible.Torsion
open _root_.AlgebraicGeometry.Scheme.Modules.RationalFunctions
open _root_.AlgebraicGeometry.Scheme.Modules.Invertible.TrivializedPower

open _root_.AlgebraicGeometry.Scheme.Modules.Invertible
  (LineBundle PicardGroup classOf classOf_tensorPower classOf_trivial
    class_eq_iff tensorLineBundle tensorLineBundleAssociator tensorPowerLineBundle
        trivialLineBundle)
open _root_.AlgebraicGeometry.Scheme.Modules
  (tensorSheaf tensorSheafBraiding tensorSheafIso tensorSheafLeftUnit tensorSheafMap)
/-!
Interface migration basis: `46f53465aaf3b0167049e9c8e9e2294111bb4281`.
Accepted object-owner map SHA-256:
`8a638d1a1d17381235478e81285ee940a20aedecb03e9d3ff1ae9878791e1868`.
Imports follow the current object owners; existing R5Lab declaration names and
all construction/proof bodies are preserved. Historical source and validation
receipts below retain their original basis. New-interface validation is pending.
-/
/-!
# Actual line bundles with a chosen tensor-power trivialization

C3 geometric algebraic Kummer classification, K2-018
`lem:k2018-geometric-exact-order`, frozen basis `7f86e4a`.
`Pair X n` consists of an actual line bundle L and an actual module-sheaf
isomorphism tau : L^n ≅ O. Its equivalence relation requires an actual
line-bundle isomorphism whose nth tensor power preserves tau. It is not the
quotient that merely remembers existence of some trivialization.

Tensor product uses the proved actual associators and braiding. Actual
global-unit scalar automorphisms, their tensor/power law, and the description
of automorphisms of O by global units are constructed. If every global unit
has an nth root, a root of the mismatch unit adjusts any underlying
line-bundle isomorphism to an isomorphism of the specified pairs. This proves
classification by actual Picard[n]; the root hypothesis is discharged from
algebraically closed constants and actual global-function surjectivity at
positive n. The transported group law is proved to be literal tensor product.
Level one is explicitly subsingleton.

Composing the independently proved algebraic-pair/Picard classification gives
a genuine additive equivalence from the divisor/function quotient to these
actual pair classes. On every representative it is proved to be
(D,f) ↦ (O(D), multiplication by f), with div(f)=nD. Actual tensor pairs
correspond to adding divisors and multiplying functions. The general units/n
exact sequence remains in KummerExactness; the pair-classification application
here has the assigned algebraically closed geometric scope.

No pair-classification, scalar-automorphism, Picard-equivalence or H1 theorem
is assumed. Source correspondence: Stacks Section 03PK, Lemma 59.28.5.
There is no etale H1 claim in this module. In later root-torsor applications,
normalized sections satisfy f*s^n=1, while trivializations phi:L→O with
phi^n=tau give a^n=f. Their inversion/sign comparison remains explicit C4 work.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open AlgebraicGeometry CategoryTheory TopologicalSpace
open AlgebraicGeometry.Scheme.OverField.Curve.Divisors
namespace AlgebraicGeometry.Scheme.OverField.Curve.Picard.TrivializedPower
universe u
variable (X : Scheme.{u})

variable [IsIntegral X] [AlgebraicGeometry.IsNoetherian X]
variable [∀ x : ClosedPoint X, IsDiscreteValuationRing (X.presheaf.stalk x.val)]
variable (hdim : topologicalKrullDim X ≤ 1)

/-- The actual divisor/function pair determines O(D) and multiplication by f.
This is the positive convention div(f)=nD. -/
def ofDivisorPair (n : ℕ) (p :
    KummerPairs.pairs X n) : Pair X n where
  lineBundle := AlgebraicGeometry.Scheme.OverField.Curve.Picard.DivisorClass.divisorLineBundle
      X hdim p.val.1
  trivialization :=
    AlgebraicGeometry.Scheme.OverField.Curve.Picard.DivisorClass.divisorPowerIso X hdim p.val.1 n ≪≫
      eqToIso (congrArg
          (AlgebraicGeometry.Scheme.OverField.Curve.Picard.DivisorClass.divisorSheaf X)
          p.property.symm) ≪≫
      AlgebraicGeometry.Scheme.OverField.Curve.Picard.DivisorClass.principalTrivialization X
          hdim p.val.2.toMul

/-- The underlying actual Picard class of the explicit divisor pair. -/
theorem ofDivisorPair_class (n : ℕ) (p :
    KummerPairs.pairs X n) :
    classOf X (ofDivisorPair X hdim n p).lineBundle =
      AlgebraicGeometry.Scheme.OverField.Curve.Picard.DivisorClass.divisorPicardEquiv X hdim
          (QuotientAddGroup.mk p.val.1) := rfl

variable {k : Type u} [Field k] [IsAlgClosed k]
variable (p : X ⟶ Spec (.of k))
variable (hconstants : Function.Surjective (((Scheme.ΓSpecIso (.of k)).inv ≫ p.appTop).hom))
variable (n : ℕ) (hn : 0 < n)

/-- Every genuine divisor/function pair gives its actual power-trivialized
line-bundle class, with the positive multiplication-by-f convention. -/
def divisorPairClass (a : KummerPairs.pairs X
    n) : Classes X n :=
  Quotient.mk _ (ofDivisorPair X hdim n a)

theorem divisorPairClass_forget (a :
    KummerPairs.pairs X n) :
    forgetClass X (divisorPairClass X hdim n a) =
      KummerPairs.toPicard X n hdim
          (QuotientAddGroup.mk a) := rfl

/-- Explicit algebraic-pair to actual-power-trivialization equivalence in the
geometric setting. It will be identified with the explicit representative map. -/
def divisorPairEquiv (hdim : topologicalKrullDim X ≤ 1)
    (p : X ⟶ Spec (.of k))
    (hconstants : Function.Surjective (((Scheme.ΓSpecIso (.of k)).inv ≫ p.appTop).hom))
    (n : ℕ) (hn : 0 < n) :
    letI := classesAddCommGroup X n (globalUnits_pow_surjective X p hconstants n hn)
    KummerPairs.T X n ≃+ Classes X n := by
  letI := classesAddCommGroup X n (globalUnits_pow_surjective X p hconstants n hn)
  exact (KummerPairs.picardTorsionEquivOfGlobalConstants X n hdim p hconstants hn).trans
    (picardTorsionAddEquiv X n (globalUnits_pow_surjective X p hconstants n hn)).symm

/-- The proved equivalence is literally (D,f)↦(O(D), multiplication by f),
not a different choice of power trivialization. -/
theorem divisorPairEquiv_mk (a :
    KummerPairs.pairs X n) :
    letI := classesAddCommGroup X n (globalUnits_pow_surjective X p hconstants n hn)
    divisorPairEquiv X hdim p hconstants n hn (QuotientAddGroup.mk a) =
      divisorPairClass X hdim n a := by
  let := classesAddCommGroup X n (globalUnits_pow_surjective X p hconstants n hn)
  apply (picardTorsionEquiv X n (globalUnits_pow_surjective X p hconstants n hn)).injective
  change (picardTorsionEquiv X n (globalUnits_pow_surjective X p hconstants n hn))
    ((picardTorsionEquiv X n (globalUnits_pow_surjective X p hconstants n hn)).symm
      ((KummerPairs.picardTorsionEquivOfGlobalConstants X n hdim p hconstants hn)
        (QuotientAddGroup.mk a))) = _
  rw [Equiv.apply_symm_apply]
  apply Subtype.ext
  rfl

include p hconstants hn in
/-- Literal tensor of the explicitly constructed pairs corresponds to adding
divisors and multiplying rational functions. -/
theorem divisorPairClass_add (a b :
    KummerPairs.pairs X n) :
    divisorPairClass X hdim n (a + b) =
      (Quotient.mk (pairSetoid X n)
        (tensor X (ofDivisorPair X hdim n a) (ofDivisorPair X hdim n b)) : Classes X n) := by
  apply forgetClass_injective X (globalUnits_pow_surjective X p hconstants n hn)
  change classOf X
      (AlgebraicGeometry.Scheme.OverField.Curve.Picard.DivisorClass.divisorLineBundle X hdim
      (a.val.1 + b.val.1)) =
    classOf X (tensor X (ofDivisorPair X hdim n a) (ofDivisorPair X hdim n b)).lineBundle
  rw [tensor_class]
  exact (AlgebraicGeometry.Scheme.OverField.Curve.Picard.DivisorClass.divisorToPicard X
      hdim).map_add a.val.1 b.val.1

end AlgebraicGeometry.Scheme.OverField.Curve.Picard.TrivializedPower
