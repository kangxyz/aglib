/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.Koszul.Single.Ext
public import Aglib.Algebra.Homology.Koszul.Single.Ideal
public import Aglib.Algebra.Homology.DerivedCategory.Ext.Quotient

/-!
# Native Ext for an actual principal ideal quotient

Transport the original one-element Koszul calculation through the actual
principal quotient isomorphism. The degree-one equivalence is linear over
the quotient ring; its action agrees with original Yoneda source
multiplication. Original cocycles and coefficient postcomposition are
retained. Concentration needs regularity on both ring and coefficient.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Abelian

universe u w

namespace ChainComplex.Koszul

variable {R : Type u} [CommRing R] [HasExt.{w} (ModuleCat.{u} R)]
  (a : R) (ha : IsSMulRegular R a) (N : ModuleCat.{u} R)

/-- Original Yoneda precomposition transports native Ext to the actual principal ideal quotient. -/
def singleIdealQuotientExtLinearEquiv (n : ℕ) :
    Ext (ModuleCat.of R (SingleQuotient R a)) N n ≃ₗ[R]
      Ext (ModuleCat.of R (R ⧸ Ideal.span {a})) N n := by
  let e := (singleQuotientIdealLinearEquiv a).toModuleIso
  exact {
    toFun := fun z => (Ext.mk₀ e.inv).comp z (zero_add n)
    invFun := fun z => (Ext.mk₀ e.hom).comp z (zero_add n)
    left_inv := by intro z; simp only [Ext.mk₀_comp_mk₀_assoc, e.hom_inv_id, Ext.mk₀_id_comp]
    right_inv := by intro z; simp only [Ext.mk₀_comp_mk₀_assoc, e.inv_hom_id, Ext.mk₀_id_comp]
    map_add' := by intro z z'; exact Ext.comp_add _ _ _ (zero_add n)
    map_smul' := by intro r z; exact Ext.comp_smul _ _ (zero_add n) r }

/-- Transport uses the original inverse quotient morphism and original Yoneda product. -/
@[simp]
theorem singleIdealQuotientExtLinearEquiv_apply (n : ℕ)
    (z : Ext (ModuleCat.of R (SingleQuotient R a)) N n) :
    singleIdealQuotientExtLinearEquiv a N n z =
      (Ext.mk₀ (singleQuotientIdealLinearEquiv a).toModuleIso.inv).comp z (zero_add n) := rfl

/-- The same transport retains native coefficient postcomposition in every degree. -/
@[simp]
theorem singleIdealQuotientExtLinearEquiv_comp_mk₀ {N' : ModuleCat.{u} R}
    (g : N ⟶ N') (n : ℕ) (z : Ext (ModuleCat.of R (SingleQuotient R a)) N n) :
    (singleIdealQuotientExtLinearEquiv a N n z).comp (Ext.mk₀ g) (add_zero n) =
      singleIdealQuotientExtLinearEquiv a N' n (z.comp (Ext.mk₀ g) (add_zero n)) :=
  Ext.comp_assoc_of_third_deg_zero _ _ _ (zero_add n)

/-- The original Koszul coefficient class in native Ext from the actual ideal quotient. -/
def singleIdealExtOneClass :
    N →ₗ[R] Ext (ModuleCat.of R (R ⧸ Ideal.span {a})) N 1 :=
  (singleIdealQuotientExtLinearEquiv a N 1).toLinearMap.comp (singleExtOneClass a ha N)

/-- This class is the original resolution cocycle followed by original quotient transport. -/
theorem singleIdealExtOneClass_apply (x : N) :
    singleIdealExtOneClass a ha N x =
      (Ext.mk₀ (singleQuotientIdealLinearEquiv a).toModuleIso.inv).comp
        (singleExtOneClass a ha N x) (zero_add 1) := rfl

/-- The actual scalar coefficient quotient computes native Ext from the actual ring quotient. -/
def singleIdealExtOneLinearEquiv :
    SingleQuotient N a ≃ₗ[R] Ext (ModuleCat.of R (R ⧸ Ideal.span {a})) N 1 :=
  (singleExtOneLinearEquiv a ha N).trans (singleIdealQuotientExtLinearEquiv a N 1)

/-- A literal quotient representative is sent to its original transported Koszul class. -/
@[simp]
theorem singleIdealExtOneLinearEquiv_apply_mk (x : N) :
    singleIdealExtOneLinearEquiv a ha N (Submodule.Quotient.mk x) =
      singleIdealExtOneClass a ha N x := by
  simp only [singleIdealExtOneLinearEquiv, LinearEquiv.trans_apply,
    singleExtOneLinearEquiv_apply_mk]
  rfl

/-- The same actual equivalence is linear for the native quotient actions on both sides. -/
def singleIdealExtOneQuotientLinearEquiv :
    letI := singleQuotientModule a N
    letI := Ext.quotientSourceModule (Ideal.span {a}) N 1
    SingleQuotient N a ≃ₗ[R ⧸ Ideal.span {a}]
      Ext (ModuleCat.of R (R ⧸ Ideal.span {a})) N 1 := by
  letI := singleQuotientModule a N
  letI := Ext.quotientSourceModule (Ideal.span {a}) N 1
  exact {
    __ := (singleIdealExtOneLinearEquiv a ha N).toAddEquiv
    map_smul' := by
      intro b x
      obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective b
      simp only [RingHom.id_apply]
      rw [singleQuotientModule_mk_smul, Ext.quotientSourceModule_mk_smul]
      exact (singleIdealExtOneLinearEquiv a ha N).map_smul r x }

/-- Quotient-linearity retains the same original class on literal representatives. -/
@[simp]
theorem singleIdealExtOneQuotientLinearEquiv_apply_mk (x : N) :
    singleIdealExtOneQuotientLinearEquiv a ha N (Submodule.Quotient.mk x) =
      singleIdealExtOneClass a ha N x :=
  singleIdealExtOneLinearEquiv_apply_mk a ha N x

/-- The quotient scalar action agrees with the original Yoneda source action used by coinduction. -/
theorem singleIdealExtOneQuotientLinearEquiv_smul (b : R ⧸ Ideal.span {a})
    (x : SingleQuotient N a) :
    letI := singleQuotientModule a N
    singleIdealExtOneQuotientLinearEquiv a ha N (b • x) =
      (Ext.mk₀ (Ext.quotientSourceMul (Ideal.span {a}) b)).comp
        (singleIdealExtOneQuotientLinearEquiv a ha N x) (zero_add 1) := by
  let := singleQuotientModule a N
  let := Ext.quotientSourceModule (Ideal.span {a}) N 1
  rw [(singleIdealExtOneQuotientLinearEquiv a ha N).map_smul]
  exact Ext.quotientSourceModule_smul_eq_precomp _ _ _ _ _

/-- Coefficient postcomposition retains the original degree-one ideal-quotient class. -/
@[simp]
theorem singleIdealExtOneClass_comp_mk₀ {N' : ModuleCat.{u} R} (g : N ⟶ N') (x : N) :
    (singleIdealExtOneClass a ha N x).comp (Ext.mk₀ g) (add_zero 1) =
      singleIdealExtOneClass a ha N' (g x) := by
  change (singleIdealQuotientExtLinearEquiv a N 1 (singleExtOneClass a ha N x)).comp
      (Ext.mk₀ g) (add_zero 1) =
    singleIdealQuotientExtLinearEquiv a N' 1 (singleExtOneClass a ha N' (g x))
  rw [singleIdealQuotientExtLinearEquiv_comp_mk₀, singleExtOneClass_comp_mk₀]

include ha in
/-- With regularity on ring and coefficient, actual quotient Ext vanishes outside degree one. -/
theorem singleIdealExt_eq_zero_of_ne_one (hN : IsSMulRegular N a) (n : ℕ) (hn : n ≠ 1)
    (z : Ext (ModuleCat.of R (R ⧸ Ideal.span {a})) N n) : z = 0 := by
  apply (singleIdealQuotientExtLinearEquiv a N n).symm.injective
  simpa only [map_zero] using singleExt_eq_zero_of_ne_one a ha N hN n hn
    ((singleIdealQuotientExtLinearEquiv a N n).symm z)


/-- Coefficient regularity alone kills degree-zero Ext from the actual ideal quotient. -/
theorem singleIdealExtZero_eq_zero_of_regular (hN : IsSMulRegular N a)
    (z : Ext (ModuleCat.of R (R ⧸ Ideal.span {a})) N 0) : z = 0 := by
  apply (singleIdealQuotientExtLinearEquiv a N 0).symm.injective
  simpa only [map_zero] using singleExtZero_eq_zero_of_regular a N hN
    ((singleIdealQuotientExtLinearEquiv a N 0).symm z)

omit [HasExt.{w} (ModuleCat.{u} R)] in
include ha in
/-- The actual principal ideal quotient has native projective dimension at most one. -/
theorem singleIdealQuotient_hasProjectiveDimensionLE :
    HasProjectiveDimensionLE (ModuleCat.of R (R ⧸ Ideal.span {a})) 1 := by
  let := singleQuotient_hasProjectiveDimensionLE a ha
  exact hasProjectiveDimensionLT_of_iso (singleQuotientIdealLinearEquiv a).toModuleIso 2

include ha in
/-- Every Ext above degree one vanishes for arbitrary coefficients in the actual ring quotient. -/
theorem singleIdealExt_eq_zero_above_one (n : ℕ) (hn : 1 < n)
    (z : Ext (ModuleCat.of R (R ⧸ Ideal.span {a})) N n) : z = 0 := by
  let := singleIdealQuotient_hasProjectiveDimensionLE a ha
  exact z.eq_zero_of_hasProjectiveDimensionLT 2 (by omega)

end ChainComplex.Koszul
