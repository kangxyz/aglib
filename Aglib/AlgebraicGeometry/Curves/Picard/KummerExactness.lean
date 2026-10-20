/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Picard.Torsion
public import Aglib.AlgebraicGeometry.Curves.Picard.DivisorInverse
public import Aglib.AlgebraicGeometry.Curves.Picard.KummerPairs
public import Aglib.AlgebraicGeometry.Modules.InternalHom
public import Aglib.AlgebraicGeometry.Modules.Invertible.Basic
public import Aglib.AlgebraicGeometry.Modules.Invertible.Dual
public import Aglib.AlgebraicGeometry.Modules.Invertible.Tensor
public import Aglib.AlgebraicGeometry.Modules.Invertible.TensorAssociator
public import Aglib.AlgebraicGeometry.Modules.Pullback.OpenRestriction

/-!
# Regular-curve Picard supplier

Source: `R5Lab.AlgebraicGeometry.Curves.Picard.KummerExactness`, R5 revision
`f8a3314ddecffcada2ec721d26d56a937bed9690`, source SHA-256
`306d100b8b104e8021019bf9690677e63307caa098ae4bd269d1ebf3480bb9cc`.
Actual divisors, quotient relations, fractional inclusions, tensor comparisons,
equality transports and principal trivializations are preserved. The original
regularity, level and product-formula premises remain explicit. General native
line-bundle, tensor, descent and cohomology suppliers are reused.
-/

@[expose] public section

open _root_.AlgebraicGeometry.Scheme.Modules.Invertible
open _root_.AlgebraicGeometry.Scheme.Modules.Invertible.Torsion
open _root_.AlgebraicGeometry.Scheme.Modules.RationalFunctions

open _root_.AlgebraicGeometry.Scheme.Modules.Invertible (PicardGroup classOf)
/-!
Interface migration basis: `46f53465aaf3b0167049e9c8e9e2294111bb4281`.
Accepted object-owner map SHA-256:
`8a638d1a1d17381235478e81285ee940a20aedecb03e9d3ff1ae9878791e1868`.
Imports follow the current object owners; existing R5Lab declaration names and
all construction/proof bodies are preserved. Historical source and validation
receipts below retain their original basis. New-interface validation is pending.
-/
/-!
# Exactness of actual global units, divisor/function pairs, and Picard torsion

C3 algebraic milestone, K2-018 `lem:k2018-geometric-exact-order`, source
basis `7f86e4a`. The global-unit map is the actual generic germ, and its nth
power quotient injects into the genuine divisor/function-pair quotient.
Its image is exactly the kernel of the actual Picard map. The latter is
surjective onto actual nth torsion by the proved divisor/Picard equivalence.
Algebraically closed global constants remove the units/n term. This is an
application of the proved local/global divisor kernel and algebraic closure,
not an assumed Picard injection. Representative divisor/function identities
are inherited unchanged, and their actual line bundles have degree zero at
positive level. Level one remains covered by KummerPairs.level_one_eq_zero.

No étale sheaf, H1, or character comparison is asserted. The classification
by line bundles with chosen power trivializations is built separately.
The generic algebra here is valid even at n=0; algebraic-closure and torsion
degree-zero applications explicitly require n>0. Proper-global-functions
and product-formula applications retain their separately named general
inputs. Source: Stacks Section 03PK, Lemma 59.28.5; the sheaf Kummer
application and its invertible-level hypothesis remain later work.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open AlgebraicGeometry CategoryTheory TopologicalSpace
open AlgebraicGeometry.Scheme.OverField.Curve.Divisors
namespace AlgebraicGeometry.Scheme.OverField.Curve.Picard.KummerPairs
universe u
variable (X : Scheme.{u}) [IsIntegral X] [AlgebraicGeometry.IsNoetherian X]
local instance : Nonempty (⊤ : X.Opens) := ⟨⟨genericPoint X, trivial⟩⟩

/-- Actual global units mapped by the generic germ. -/
def globalUnitMap : Additive Γ(X, ⊤)ˣ →+ Additive X.functionFieldˣ :=
  (Units.map (X.germToFunctionField ⊤).hom.toMonoidHom).toAdditive

omit [IsNoetherian X] in
theorem globalUnitMap_injective [IsNoetherian X] : Function.Injective (globalUnitMap X) := by
  intro a b h
  apply Additive.toMul.injective
  apply Units.ext
  apply X.germToFunctionField_injective ⊤
  exact congrArg (fun a : Additive X.functionFieldˣ => (a.toMul : X.functionField)) h

theorem globalUnitMap_principal (a : Additive Γ(X, ⊤)ˣ) : principal X (globalUnitMap X a) = 0 := by
  ext x
  exact Scheme.ord_of_isUnit a.toMul.isUnit (show x.val ∈ (⊤ : X.Opens) from trivial)

variable (n : ℕ)
def globalUnitPair : Additive Γ(X, ⊤)ˣ →+ pairs X n where
  toFun a := ⟨(0, globalUnitMap X a), by
    change principal X (globalUnitMap X a) = n • (0 : Divisor X)
    rw [globalUnitMap_principal, smul_zero]⟩
  map_zero' := by apply Subtype.ext; simp
  map_add' a b := by apply Subtype.ext; simp

def globalUnitsToT : Additive Γ(X, ⊤)ˣ →+ T X n :=
  (QuotientAddGroup.mk' (relation X n).range).comp (globalUnitPair X n)

theorem globalUnitsToT_toClass (a : Additive Γ(X, ⊤)ˣ) :
    toClass X n (globalUnitsToT X n a) = 0 := rfl

theorem globalUnitsToT_nsmul (a : Additive Γ(X, ⊤)ˣ) : globalUnitsToT X n (n • a) = 0 := by
  apply (QuotientAddGroup.eq_zero_iff _).mpr
  refine ⟨globalUnitMap X a, ?_⟩
  apply Subtype.ext
  apply Prod.ext
  · exact globalUnitMap_principal X a
  · exact ((globalUnitMap X).map_nsmul n a).symm

variable [∀ x : ClosedPoint X, IsDiscreteValuationRing (X.presheaf.stalk x.val)]
variable (hdim : topologicalKrullDim X ≤ 1)

include hdim in
theorem globalUnitsToT_eq_zero_iff (a : Additive Γ(X, ⊤)ˣ) :
    globalUnitsToT X n a = 0 ↔ ∃ b : Additive Γ(X, ⊤)ˣ, n • b = a := by
  constructor
  · intro ha
    obtain ⟨h, hh⟩ := (QuotientAddGroup.eq_zero_iff _).mp ha
    have hh₁ : principal X h = 0 := congrArg (fun p : pairs X n => p.val.1) hh
    have hh₂ : n • h = globalUnitMap X a := congrArg (fun p : pairs X n => p.val.2) hh
    obtain ⟨b, hb⟩ := (principal_eq_zero_iff_globalUnit X
      (point_eq_generic_or_isClosed X hdim) (fun x => coheight_eq_one_of_dvr X x.val)
          h.toMul).mp hh₁
    refine ⟨Additive.ofMul b, globalUnitMap_injective X ?_⟩
    rw [map_nsmul]
    change n • Additive.ofMul (Units.map (X.germToFunctionField ⊤).hom.toMonoidHom b) = _
    rw [hb]
    exact hh₂
  · rintro ⟨b, rfl⟩
    exact globalUnitsToT_nsmul X n b

/-- Global units modulo their actual nth powers, written additively. -/
abbrev globalUnitsModuloPowers := Additive Γ(X, ⊤)ˣ ⧸ (nsmulAddMonoidHom (α := Additive Γ(X,
    ⊤)ˣ) n).range

def unitsModuloToT : globalUnitsModuloPowers X n →+ T X n :=
  QuotientAddGroup.lift _ (globalUnitsToT X n) (by
    rintro a ⟨b, rfl⟩
    exact globalUnitsToT_nsmul X n b)

include hdim in
theorem unitsModuloToT_injective : Function.Injective (unitsModuloToT X n) := by
  apply (injective_iff_map_eq_zero (unitsModuloToT X n)).mpr
  intro a
  induction a using Quotient.inductionOn with
  | h a =>
    intro ha
    obtain ⟨b, hb⟩ := (globalUnitsToT_eq_zero_iff X n hdim a).mp ha
    exact (QuotientAddGroup.eq_zero_iff _).mpr ⟨b, hb⟩

include hdim in
theorem toClass_eq_zero_iff_globalUnit (t : T X n) :
    toClass X n t = 0 ↔ ∃ a : Additive Γ(X, ⊤)ˣ, globalUnitsToT X n a = t := by
  constructor
  · intro ht
    obtain ⟨p, rfl⟩ := QuotientAddGroup.mk_surjective t
    obtain ⟨h, hh⟩ := (QuotientAddGroup.eq_zero_iff _).mp ht
    have hp : principal X (p.val.2 - n • h) = 0 := by
      rw [map_sub, map_nsmul, hh]
      exact sub_eq_zero.mpr p.property
    obtain ⟨a, ha⟩ := (principal_eq_zero_iff_globalUnit X
      (point_eq_generic_or_isClosed X hdim) (fun x => coheight_eq_one_of_dvr X x.val)
      (p.val.2 - n • h).toMul).mp hp
    refine ⟨Additive.ofMul a, ?_⟩
    have he : p = globalUnitPair X n (Additive.ofMul a) + relation X n h := by
      apply Subtype.ext
      apply Prod.ext
      · change p.val.1 = 0 + principal X h
        simpa using hh.symm
      · change p.val.2 = globalUnitMap X (Additive.ofMul a) + n • h
        change p.val.2 = Additive.ofMul (Units.map (X.germToFunctionField ⊤).hom.toMonoidHom a)
            + n • h
        rw [ha]
        change p.val.2 = (p.val.2 - n • h) + n • h
        exact (sub_add_cancel _ _).symm
    have hz : (QuotientAddGroup.mk' (relation X n).range) (relation X n h) = 0 :=
      (QuotientAddGroup.eq_zero_iff _).mpr ⟨h, rfl⟩
    change (QuotientAddGroup.mk' (relation X n).range) _ = (QuotientAddGroup.mk' (relation X
        n).range) p
    rw [he, map_add, hz]
    exact (add_zero ((QuotientAddGroup.mk' (relation X n).range)
      (globalUnitPair X n (Additive.ofMul a)))).symm
  · rintro ⟨a, rfl⟩
    exact globalUnitsToT_toClass X n a

include hdim in
/-- Exactness is at the actual divisor/function quotient, with actual global units. -/
theorem unitsModuloToT_range : (unitsModuloToT X n).range = (toClass X n).ker := by
  ext t
  constructor
  · rintro ⟨a, rfl⟩
    obtain ⟨a, rfl⟩ := QuotientAddGroup.mk_surjective a
    exact globalUnitsToT_toClass X n a
  · intro ht
    obtain ⟨a, ha⟩ := (toClass_eq_zero_iff_globalUnit X n hdim t).mp ht
    exact ⟨QuotientAddGroup.mk a, ha⟩
/-- Restriction of the proved divisor/Picard equivalence to actual torsion. -/
def divisorTorsionPicardEquiv : torsionClasses X n ≃+ picardTorsion X n where
  toFun c := ⟨DivisorClass.divisorPicardEquiv X hdim c.val, by
    change n • AlgebraicGeometry.Scheme.OverField.Curve.Picard.DivisorClass.divisorPicardEquiv
        X hdim c.val = 0
    rw [← map_nsmul, c.property, map_zero]⟩
  invFun c := ⟨(AlgebraicGeometry.Scheme.OverField.Curve.Picard.DivisorClass.divisorPicardEquiv
      X hdim).symm c.val, by
    change n • (AlgebraicGeometry.Scheme.OverField.Curve.Picard.DivisorClass.divisorPicardEquiv
        X hdim).symm c.val = 0
    have hc : n • c.val = 0 := c.property
    rw [← map_nsmul, hc, map_zero]⟩
  left_inv c := by apply Subtype.ext; exact
      (AlgebraicGeometry.Scheme.OverField.Curve.Picard.DivisorClass.divisorPicardEquiv X
      hdim).symm_apply_apply c.val
  right_inv c := by apply Subtype.ext; exact
      (AlgebraicGeometry.Scheme.OverField.Curve.Picard.DivisorClass.divisorPicardEquiv X
      hdim).apply_symm_apply c.val
  map_add' c d := by apply Subtype.ext; exact map_add _ _ _

/-- The actual Picard class of a divisor/function pair. -/
def toPicard : T X n →+ PicardGroup X :=
  (AlgebraicGeometry.Scheme.OverField.Curve.Picard.DivisorClass.divisorPicardEquiv X
      hdim).toAddMonoidHom.comp (toClass X n)

def toPicardTorsion : T X n →+ picardTorsion X n :=
  (divisorTorsionPicardEquiv X n hdim).toAddMonoidHom.comp (toTorsionClasses X n)

theorem toPicardTorsion_surjective : Function.Surjective (toPicardTorsion X n hdim) :=
  (divisorTorsionPicardEquiv X n hdim).surjective.comp (toTorsionClasses_surjective X n)

theorem toPicard_nsmul (t : T X n) : n • toPicard X n hdim t = 0 :=
  (toPicardTorsion X n hdim t).property

theorem unitsModuloToPicard_exact : (unitsModuloToT X n).range = (toPicard X n hdim).ker := by
  rw [unitsModuloToT_range X n hdim]
  ext t
  change toClass X n t = 0 ↔
      AlgebraicGeometry.Scheme.OverField.Curve.Picard.DivisorClass.divisorPicardEquiv X hdim
      (toClass X n t) = 0
  exact ((AlgebraicGeometry.Scheme.OverField.Curve.Picard.DivisorClass.divisorPicardEquiv X
      hdim).map_eq_zero_iff).symm

theorem representative_picard (t : T X n) :
    classOf X (AlgebraicGeometry.Scheme.OverField.Curve.Picard.DivisorClass.divisorLineBundle X
        hdim (divisorRepresentative X n t)) =
      toPicard X n hdim t := by
  exact congrArg
      (AlgebraicGeometry.Scheme.OverField.Curve.Picard.DivisorClass.divisorPicardEquiv X hdim)
      (class_representative X n t)

variable {k : Type u} [Field k]
/-- Algebraically closed global constants kill the units/n term, giving actual Picard torsion. -/
def picardTorsionEquivOfGlobalConstants [IsAlgClosed k]
    (p : X ⟶ Spec (.of k))
    (hconstants : Function.Surjective (((Scheme.ΓSpecIso (.of k)).inv ≫ p.appTop).hom))
    (hn : 0 < n) : T X n ≃+ picardTorsion X n :=
  (torsionEquivOfGlobalConstants X n p hconstants (point_eq_generic_or_isClosed X hdim)
    (fun x => coheight_eq_one_of_dvr X x.val) hn).trans (divisorTorsionPicardEquiv X n hdim)

theorem representative_degree_zero (p : X ⟶ Spec (.of k))
    (hprod : AlgebraicGeometry.Scheme.OverField.Curve.Picard.Degree.PrincipalProductFormula X
        p) (hn : 0 < n) (t : T X n) :
    AlgebraicGeometry.Scheme.OverField.Curve.Picard.Degree.lineBundleDegree X p hdim hprod
      (AlgebraicGeometry.Scheme.OverField.Curve.Picard.DivisorClass.divisorLineBundle X hdim
          (divisorRepresentative X n t)) = 0 := by
  unfold AlgebraicGeometry.Scheme.OverField.Curve.Picard.Degree.lineBundleDegree
  rw [representative_picard]
  exact AlgebraicGeometry.Scheme.OverField.Curve.Picard.Degree.picard_torsion_degree_zero X p
      hdim hprod n hn _ (toPicard_nsmul X n hdim t)

end AlgebraicGeometry.Scheme.OverField.Curve.Picard.KummerPairs
