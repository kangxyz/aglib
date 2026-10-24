/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Ext.Basic
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences
public import Mathlib.RingTheory.Regular.Category
public import Mathlib.RingTheory.Regular.IsSMulRegular

/-!
# Scalar regularity on Ext from the original source quotient

For actual modules `M` and `N`, a scalar `a` regular on `M` is regular on
`Ext M N q` if `Ext (M / a M) N q` vanishes. The proof uses the original
scalar short exact sequence and the native scalar action on Ext. Neither
the ring nor either module has a finiteness or freeness hypothesis.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory CategoryTheory.Abelian

namespace ModuleCat

/-- Vanishing of Ext from the actual scalar quotient makes the same scalar
regular on Ext from the source, with its native module structure. -/
theorem isSMulRegular_ext_of_subsingleton_quotSMulTop
    {S : Type u} [CommRing S] (M N : ModuleCat.{u} S)
    (a : S) (ha : IsSMulRegular M a) (q : ℕ)
    [Subsingleton (Ext.{u} (ModuleCat.of S (QuotSMulTop a M)) N q)] :
    IsSMulRegular (Ext.{u} M N q) a := by
  let T := M.smulShortComplex a
  have hT : T.ShortExact := ha.smulShortComplex_shortExact
  let : Subsingleton (Ext.{u} T.X₃ N q) := by
    change Subsingleton (Ext.{u} (ModuleCat.of S (QuotSMulTop a M)) N q)
    infer_instance
  apply IsSMulRegular.of_right_eq_zero_of_smul
  intro x hx
  have hscalar : (Ext.mk₀.{u} T.f).comp x (zero_add q) = a • x := by
    change (Ext.mk₀.{u} (a • 𝟙 M)).comp x (zero_add q) = a • x
    rw [Ext.mk₀_smul (R := S)]
    exact (Ext.smul_comp (R := S) (Ext.mk₀.{u} (𝟙 M)) x (zero_add q) a).trans
      (congrArg (fun z => a • z) (Ext.mk₀_id_comp x))
  obtain ⟨y, hy⟩ := Ext.contravariant_sequence_exact₂.{u} hT N x (hscalar.trans hx)
  rw [Subsingleton.elim y 0, Ext.comp_zero] at hy
  exact hy.symm

end ModuleCat
