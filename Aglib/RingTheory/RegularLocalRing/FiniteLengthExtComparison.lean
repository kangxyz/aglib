/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.RegularLocalRing.FiniteLengthExt
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Linear
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

/-!
# Ext comparison across finite-length defects

Over a regular local ring of dimension at least three, a module map with
finite-length kernel and cokernel induces an isomorphism on first Ext into
the ring. The map is the actual contravariant Ext map, not an unspecified
isomorphism of the groups.
-/

@[expose] public section

universe u

open CategoryTheory Abelian

namespace IsRegularLocalRing

private theorem bijective_precomp_g
    {R : Type u} [CommRing R] (S : ShortComplex (ModuleCat.{u} R))
    (hS : S.ShortExact) (T : ModuleCat.{u} R)
    [Subsingleton (Ext S.X₁ T 0)] [Subsingleton (Ext S.X₁ T 1)] :
    Function.Bijective ((Ext.mk₀ S.g).precompOfLinear R T (zero_add 1)) := by
  constructor
  · apply (injective_iff_map_eq_zero _).mpr
    intro x hx
    obtain ⟨y, hy⟩ := Ext.contravariant_sequence_exact₃ hS T x hx (n₀ := 0) rfl
    simpa only [Subsingleton.elim y 0, Ext.comp_zero] using hy.symm
  · intro x
    exact Ext.contravariant_sequence_exact₂ hS T x (Subsingleton.elim _ _)

private theorem bijective_precomp_f
    {R : Type u} [CommRing R] (S : ShortComplex (ModuleCat.{u} R))
    (hS : S.ShortExact) (T : ModuleCat.{u} R)
    [Subsingleton (Ext S.X₃ T 1)] [Subsingleton (Ext S.X₃ T 2)] :
    Function.Bijective ((Ext.mk₀ S.f).precompOfLinear R T (zero_add 1)) := by
  constructor
  · apply (injective_iff_map_eq_zero _).mpr
    intro x hx
    obtain ⟨y, hy⟩ := Ext.contravariant_sequence_exact₂ hS T x hx
    simpa only [Subsingleton.elim y 0, Ext.comp_zero] using hy.symm
  · intro x
    exact Ext.contravariant_sequence_exact₁ hS T x (n₁ := 2) rfl
      (Subsingleton.elim _ _)

/-- First Ext into the ring is unchanged by a map whose kernel and cokernel
have finite length, in regular local dimension at least three. -/
theorem bijective_ext_one_precomp_of_isFiniteLength
    (R : Type u) [CommRing R] [IsRegularLocalRing R]
    {D E : ModuleCat.{u} R} (e : D ⟶ E)
    (hker : IsFiniteLength R (LinearMap.ker e.hom))
    (hcoker : IsFiniteLength R (E ⧸ LinearMap.range e.hom))
    (d : ℕ) (hd : ringKrullDim R = (d : ℕ)) (h3 : 3 ≤ d) :
    Function.Bijective ((Ext.mk₀ e).precompOfLinear R (ModuleCat.of R R) (zero_add 1)) := by
  let T := ModuleCat.of R R
  let p := e.hom.rangeRestrict
  let I := LinearMap.range e.hom
  let S₁ := p.shortComplexKer
  have hS₁ : S₁.ShortExact := LinearMap.shortExact_shortComplexKer
    e.hom.surjective_rangeRestrict
  have hk : IsFiniteLength R (LinearMap.ker p) := by
    change IsFiniteLength R (LinearMap.ker e.hom.rangeRestrict)
    rw [e.hom.ker_rangeRestrict]
    exact hker
  have : Subsingleton (Ext S₁.X₁ T 0) :=
    subsingleton_ext_of_isFiniteLength R S₁.X₁ hk d hd 0 (by omega)
  have : Subsingleton (Ext S₁.X₁ T 1) :=
    subsingleton_ext_of_isFiniteLength R S₁.X₁ hk d hd 1 (by omega)
  have hp := bijective_precomp_g S₁ hS₁ T
  let S₂ := ModuleCat.shortComplexOfCompEqZero I.subtype I.mkQ
    (by ext x; exact (Submodule.Quotient.mk_eq_zero I).mpr x.property)
  have hS₂ : S₂.ShortExact := ModuleCat.shortComplex_shortExact S₂
    (LinearMap.exact_subtype_mkQ I) I.subtype_injective I.mkQ_surjective
  have : Subsingleton (Ext S₂.X₃ T 1) :=
    subsingleton_ext_of_isFiniteLength R S₂.X₃ hcoker d hd 1 (by omega)
  have : Subsingleton (Ext S₂.X₃ T 2) :=
    subsingleton_ext_of_isFiniteLength R S₂.X₃ hcoker d hd 2 (by omega)
  have hi := bijective_precomp_f S₂ hS₂ T
  have hcomp : S₁.g ≫ S₂.f = e := by
    ext x
    rfl
  change Function.Bijective (fun x => (Ext.mk₀ S₁.g).comp x (zero_add 1)) at hp
  change Function.Bijective (fun x => (Ext.mk₀ S₂.f).comp x (zero_add 1)) at hi
  change Function.Bijective (fun x => (Ext.mk₀ e).comp x (zero_add 1))
  simpa only [Function.comp_def, Ext.mk₀_comp_mk₀_assoc, hcomp] using hp.comp hi

/-- The canonical linear equivalence on first Ext induced by a map with
finite-length defects. -/
noncomputable def extOneLinearEquivOfIsFiniteLength
    (R : Type u) [CommRing R] [IsRegularLocalRing R]
    {D E : ModuleCat.{u} R} (e : D ⟶ E)
    (hker : IsFiniteLength R (LinearMap.ker e.hom))
    (hcoker : IsFiniteLength R (E ⧸ LinearMap.range e.hom))
    (d : ℕ) (hd : ringKrullDim R = (d : ℕ)) (h3 : 3 ≤ d) :
    Ext E (ModuleCat.of R R) 1 ≃ₗ[R] Ext D (ModuleCat.of R R) 1 :=
  LinearEquiv.ofBijective ((Ext.mk₀ e).precompOfLinear R (ModuleCat.of R R) (zero_add 1))
    (bijective_ext_one_precomp_of_isFiniteLength R e hker hcoker d hd h3)

end IsRegularLocalRing
