/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.Algebra.Homology.ModuleCat.FiniteParametrix

/-! # The original two-term cone in cohomological degrees zero and one

The explicit shift by minus one moves cone degrees minus one and zero to zero and one.
Negating the original source inclusion cancels the shift sign. Both actual coordinate
maps are isomorphisms and the differential square retains the original linear map.
-/

/-!
Source: `quillen-k-theory/Quillen/Aglib/Algebra/Homology/ModuleCat/LinearMapConeShift.lean` from
the supplied frozen Quillen snapshot.
SHA-256: `c6feed8aa3aa30df9c9dfb4e6ab24767e1061dc05ab359459d31822cb3f6e446`.
Only native objects, maps and mathematical namespaces are used in this extraction.
-/

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open CochainComplex.HomComplex
attribute [local instance] Abelian.hasFiniteBiproducts
universe u v
namespace ModuleCat
variable {R : Type u} [CommRing R] {A B : Type v}
  [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B] (d : A →ₗ[R] B)

/-- The explicit minus-one shift puts the original cone in Cech degrees zero and one. -/
def linearMapCechComplex : CochainComplex (ModuleCat.{v} R) ℤ := (linearMapCone d)⟦(-1 : ℤ)⟧

/-- The source coordinate is negated to cancel the actual differential sign of the shift. -/
def linearMapCechSource : ModuleCat.of R A ⟶ (linearMapCechComplex d).X 0 :=
  -(CochainComplex.mappingCone.inl
    ((single (ModuleCat.{v} R) (.up ℤ) 0).map (ModuleCat.ofHom d))).v 0 (-1) rfl

/-- The original target coordinate is unchanged under the degree shift. -/
def linearMapCechTarget : ModuleCat.of R B ⟶ (linearMapCechComplex d).X 1 :=
  (CochainComplex.mappingCone.inr
    ((single (ModuleCat.{v} R) (.up ℤ) 0).map (ModuleCat.ofHom d))).f 0

/-- Both visible signs cancel, giving exactly the original linear differential
in degrees zero and one. -/
theorem linearMapCechSource_d :
    linearMapCechSource d ≫ (linearMapCechComplex d).d 0 1 =
      ModuleCat.ofHom d ≫ linearMapCechTarget d := by
  let φ := (single (ModuleCat.{v} R) (.up ℤ) 0).map (ModuleCat.ofHom d)
  have h := CochainComplex.mappingCone.inl_v_d φ 0 (-1) 1 rfl rfl
  have hf : φ.f 0 = ModuleCat.ofHom d := rfl
  rw [hf] at h
  simpa [linearMapCechSource, linearMapCechTarget, linearMapCechComplex,
    linearMapCone, CochainComplex.shiftFunctor, φ, Preadditive.neg_comp,
    Preadditive.comp_neg, Cochain.neg_v] using h


/-- The explicitly shifted original cone has no terms outside Cech degrees zero and one. -/
theorem linearMapCechComplex_isZero_X (n : ℤ) (h0 : n ≠ 0) (h1 : n ≠ 1) :
    IsZero ((linearMapCechComplex d).X n) :=
  linearMapCone_isZero_X d (n + -1) (by omega) (by omega)

/-- The actual signed source coordinate identifies the degree-zero term with its original module. -/
def linearMapCechSourceIso : ModuleCat.of R A ≅ (linearMapCechComplex d).X 0 where
  hom := linearMapCechSource d
  inv := -((CochainComplex.mappingCone.fst
    ((single (ModuleCat.{v} R) (.up ℤ) 0).map (ModuleCat.ofHom d))).1.v (-1) 0 rfl)
  hom_inv_id := by
    simp only [linearMapCechSource, Preadditive.neg_comp, Preadditive.comp_neg, neg_neg,
      CochainComplex.mappingCone.inl_v_fst_v]
    rfl
  inv_hom_id := by
    let φ := (single (ModuleCat.{v} R) (.up ℤ) 0).map (ModuleCat.ofHom d)
    have hz := isZero_single_obj_X (.up ℤ) 0 (ModuleCat.of R B) (-1) (by decide)
    have hs : (CochainComplex.mappingCone.snd φ).v (-1) (-1) rfl = 0 := hz.eq_of_tgt _ _
    have hid := CochainComplex.mappingCone.id_X φ (-1) 0 rfl
    simpa [linearMapCechSource, linearMapCechComplex, linearMapCone,
      CochainComplex.shiftFunctor, φ, Preadditive.neg_comp, Preadditive.comp_neg, hs] using hid

/-- The unchanged target coordinate identifies degree one with the original target module. -/
def linearMapCechTargetIso : ModuleCat.of R B ≅ (linearMapCechComplex d).X 1 where
  hom := linearMapCechTarget d
  inv := (CochainComplex.mappingCone.snd
    ((single (ModuleCat.{v} R) (.up ℤ) 0).map (ModuleCat.ofHom d))).v 0 0 rfl
  hom_inv_id := by
    simp only [linearMapCechTarget, CochainComplex.mappingCone.inr_f_snd_v]
    rfl
  inv_hom_id := by
    let φ := (single (ModuleCat.{v} R) (.up ℤ) 0).map (ModuleCat.ofHom d)
    have hz := isZero_single_obj_X (.up ℤ) 0 (ModuleCat.of R A) 1 (by decide)
    have hf : (CochainComplex.mappingCone.fst φ).1.v 0 1 rfl = 0 := hz.eq_of_tgt _ _
    have hid := CochainComplex.mappingCone.id_X φ 0 1 rfl
    simpa [linearMapCechTarget, linearMapCechComplex, linearMapCone,
      CochainComplex.shiftFunctor, φ, hf] using hid

end ModuleCat
