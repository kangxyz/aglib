/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.RationalFunctions.CommonFractionalIdeal
public import Aglib.AlgebraicGeometry.Curves.Picard.Degree.ProductFormula
public import Aglib.AlgebraicGeometry.Curves.Picard.DivisorSheaf
public import Aglib.AlgebraicGeometry.EffectiveCartierDivisor.Relative.GraphIdeal
public import Aglib.AlgebraicGeometry.Modules.Stalk.Basic
public import Aglib.AlgebraicGeometry.Modules.Stalk.FieldScalars
public import Aglib.AlgebraicGeometry.Modules.Support

/-!
# Common fractional ideals on singular integral curves

Components for the unchanged proper-curve product formula: actual generic
rational sections, the common pullback of the two regular modules, and the
local projection-quotient dictionary. No closed-stalk DVR condition is used.
Proper H1 finiteness and the Euler argument are separate remaining obligations.

Authoring basis `28e33dafb3b1e78e9749a27f20bf4c6e0bc5b26b`, Lean4.34.1,
Mathlibd13f23b723b8a846827a245b89c10fc7d3f11612 and coherent Quillen0.7
83629578a3d70787d41ec631f5234af8758716af. The latter supplies the actual
module-valued stalk and global-unit maps used here.
-/



@[expose] public section

noncomputable section
open AlgebraicGeometry.Scheme.Modules.RationalFunctions.CommonFractionalIdeal
open AlgebraicGeometry.Scheme
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
namespace AlgebraicGeometry.Scheme.OverField.Curve.Picard.Degree.CommonFractionalIdeal
universe u
variable (X : Scheme.{u}) [IsIntegral X]

variable [AlgebraicGeometry.IsNoetherian X]
theorem finite_complement_of_nonempty_open (hdim : topologicalKrullDim X = 1)
    (U : X.Opens) [hU : Nonempty U] : ((U : Set X)ᶜ).Finite := by
  have hc : IsClosed ((U : Set X)ᶜ) := U.isOpen.isClosed_compl
  let : QuasiSober ↥((U : Set X)ᶜ) := hc.isClosedEmbedding_subtypeVal.quasiSober
  have hxg : genericPoint X ∈ U :=
    ((genericPoint_spec X).mem_open_set_iff U.isOpen).mpr (by simpa using hU)
  have hp : closure ((U : Set X)ᶜ) ≠ Set.univ := by
    rw [hc.closure_eq]
    intro he
    have hg : genericPoint X ∈ (U : Set X)ᶜ := he ▸ Set.mem_univ _
    exact hg hxg
  apply (NoetherianSpace.finite_coheight_one_of_closure_ne_univ hp).subset
  intro x hx
  refine ⟨hx, ?_⟩
  rcases Divisors.point_eq_generic_or_isClosed X hdim.le x with hgen | hclosed
  · rw [hgen] at hx
    exact False.elim (hx hxg)
  · exact ProductFormula.closedPoint_coheight_one X hdim x hclosed

theorem exists_finite_closed_quotient_stalk_support (hdim : topologicalKrullDim X = 1)
    (f : X.functionFieldˣ) : ∃ S : Finset X,
      (∀ x ∈ S, IsClosed ({x} : Set X)) ∧
        (∀ x, x ∉ S → Subsingleton ((leftQuotient X f).presheaf.stalk x)) ∧
          (∀ x, x ∉ S → Subsingleton ((rightQuotient X f).presheaf.stalk x)) := by
  classical
  obtain ⟨U, _, s, hn, hs, hu⟩ := exists_isUnit_germ_eq X (f : X.functionField) f.ne_zero
  let : Nonempty U := hn
  let s' : Γ(X,U)ˣ := hu.unit
  have hs' : X.germToFunctionField U s' = (f : X.functionField) := by
    rw [hu.unit_spec]
    exact hs
  have hfinite := finite_complement_of_nonempty_open X hdim U
  have hxg : genericPoint X ∈ U :=
    ((genericPoint_spec X).mem_open_set_iff U.isOpen).mpr (by simpa using hn)
  refine ⟨hfinite.toFinset, ?_, ?_, ?_⟩
  · intro x hx
    have hxU : x ∉ U := (hfinite.mem_toFinset.mp hx)
    rcases Divisors.point_eq_generic_or_isClosed X hdim.le x with hgen | hclosed
    · rw [hgen] at hxU
      exact False.elim (hxU hxg)
    · exact hclosed
  · intro x hx
    have hxU : x ∈ U := by
      by_contra hxU
      exact hx (hfinite.mem_toFinset.mpr hxU)
    exact (quotient_stalks_subsingleton_on_unit_open X f U s' hs' x hxU).1
  · intro x hx
    have hxU : x ∈ U := by
      by_contra hxU
      exact hx (hfinite.mem_toFinset.mpr hxU)
    exact (quotient_stalks_subsingleton_on_unit_open X f U s' hs' x hxU).2
theorem quotient_stalks_finiteLength (x : X) (hc : Order.coheight x = 1)
    (f : X.functionFieldˣ) :
    IsFiniteLength (X.presheaf.stalk x) ((leftQuotient X f).presheaf.stalk x) ∧
      IsFiniteLength (X.presheaf.stalk x) ((rightQuotient X f).presheaf.stalk x) := by
  let : Ring.KrullDimLE 1 (X.presheaf.stalk x) := krullDimLE_of_coheight_le hc.le
  obtain ⟨a,b,ha,hb,hf⟩ := ProductFormula.exists_stalk_fraction X x f
  have hfin := Ideal.principalIntersection_finiteLength (X.presheaf.stalk x) a b ha hb
  have hB := hfin.of_injective (Submodule.subtype_injective
    (Ideal.quotientIdealImage (X.presheaf.stalk x) (Ideal.span {a} ⊓ Ideal.span {b})
      (Ideal.span {b})))
  have hA := hfin.of_injective (Submodule.subtype_injective
    (Ideal.quotientIdealImage (X.presheaf.stalk x) (Ideal.span {a} ⊓ Ideal.span {b})
      (Ideal.span {a})))
  exact ⟨hB.of_injective (leftQuotientStalkImageEquiv X f x a b hb hf.symm).injective,
    hA.of_injective (rightQuotientStalkImageEquiv X f x a b hb hf.symm).injective⟩

theorem order_eq_quotient_stalk_length (x : X) (hc : Order.coheight x = 1)
    (f : X.functionFieldˣ) :
    X.ord (f : X.functionField) x =
      ((Module.length (X.presheaf.stalk x) ((leftQuotient X f).presheaf.stalk x)).toNat : ℤ) -
        ((Module.length (X.presheaf.stalk x) ((rightQuotient X f).presheaf.stalk x)).toNat : ℤ) :=
          by
  obtain ⟨a,b,ha,hb,hf⟩ := ProductFormula.exists_stalk_fraction X x f
  rw [(leftQuotientStalkImageEquiv X f x a b hb hf.symm).length_eq,
    (rightQuotientStalkImageEquiv X f x a b hb hf.symm).length_eq, ← hf]
  exact ProductFormula.order_stalk_fraction_eq_intersection_image_lengths X x hc a b ha hb

open FiniteSupportLengths IsLocalRing
section BaseFieldScalars
variable {k : Type u} [Field k] (p : X ⟶ Spec (.of k))
open AlgebraicGeometry.Scheme.Modules
  (stalkBaseModule stalkBaseTower stalkBaseModule_germ_smul stalkBase_finite)
variable [LocallyOfFiniteType p]
omit [IsIntegral X] [AlgebraicGeometry.IsNoetherian X] in
theorem stalkBase_finrank (M : X.Modules) (x : X) (hx : IsClosed ({x} : Set X))
    (hM : IsFiniteLength (X.presheaf.stalk x) (M.presheaf.stalk x)) :
    letI := stalkBaseModule X p M x
    (Module.finrank k (M.presheaf.stalk x) : ℤ) =
      ((Module.length (X.presheaf.stalk x) (M.presheaf.stalk x)).toNat : ℤ) *
        Picard.Degree.weight X p ⟨x,hx⟩ := by
  let := stalkConstantsAlgebra X p x
  let := residueAlgebraFromStalk X p x
  let := stalkBaseModule X p M x
  rw [weight_eq_residue_finrank X p x hx]
  exact Scheme.Modules.stalkBase_finrank X p M x hx hM

theorem weighted_order_eq_quotient_stalk_finrank (f : X.functionFieldˣ) (x : X)
    (hx : IsClosed ({x} : Set X)) (hc : Order.coheight x = 1) :
    letI := stalkBaseModule X p (leftQuotient X f) x
    letI := stalkBaseModule X p (rightQuotient X f) x
    X.ord (f : X.functionField) x * Picard.Degree.weight X p ⟨x,hx⟩ =
      (Module.finrank k ((leftQuotient X f).presheaf.stalk x) : ℤ) -
        (Module.finrank k ((rightQuotient X f).presheaf.stalk x) : ℤ) := by
  let := stalkBaseModule X p (leftQuotient X f) x
  let := stalkBaseModule X p (rightQuotient X f) x
  have hfin := quotient_stalks_finiteLength X x hc f
  rw [stalkBase_finrank X p (leftQuotient X f) x hx hfin.1,
    stalkBase_finrank X p (rightQuotient X f) x hx hfin.2,
    order_eq_quotient_stalk_length X x hc f]
  ring

end BaseFieldScalars

end AlgebraicGeometry.Scheme.OverField.Curve.Picard.Degree.CommonFractionalIdeal
