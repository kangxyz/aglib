/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.FunctionField.AffineCharts
public import Aglib.RingTheory.Nagata.FiniteTypeSurface
public import Aglib.AlgebraicGeometry.Stalk.Dimension
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType

/-!
# Actual adapted affine charts of a birational surface morphism

GF2 is applied to the literal section map `f.appLE V U hUV`. The coefficient
ring is an affine chart of the original surface, not a chosen global ring.
The original generic-stalk map supplies algebraicity and injectivity.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory TopologicalSpace
open scoped nonZeroDivisors

namespace AlgebraicGeometry.Scheme.NormalizedPointDomination

universe u

private theorem linearPolynomial_ne_zero {R : Type*} [CommRing R]
    (a s : R) (hs : s ≠ 0) : Polynomial.C s * Polynomial.X - Polynomial.C a ≠ 0 := by
  intro hp
  apply hs
  have hc := congrArg (fun p : Polynomial R ↦ p.coeff 1) hp
  simpa using hc

variable {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
  (f : X ⟶ Y) [IsDominant f]
  (V : Y.Opens) [hVne : Nonempty V] (U : X.Opens) [hUne : Nonempty U] (hUV : U ≤ f ⁻¹ᵁ V)

include hUne in
/-- The literal adapted section map commutes with both original generic germs. -/
theorem appLE_germToFunctionField :
    f.appLE V U hUV ≫ X.germToFunctionField U =
      Y.germToFunctionField V ≫ CommRingCat.ofHom (functionFieldMap f) := by
  let : Nonempty (f ⁻¹ᵁ V) := Nonempty.map (fun x : U ↦ (⟨x.val, hUV x.property⟩ : f ⁻¹ᵁ V))
    hUne
  have hg : genericPoint X ∈ U :=
    ((genericPoint_spec X).mem_open_set_iff U.isOpen).mpr (by simpa using ‹Nonempty U›)
  have hres : X.presheaf.map (homOfLE hUV).op ≫ X.germToFunctionField U =
      X.germToFunctionField (f ⁻¹ᵁ V) :=
    X.presheaf.germ_res (homOfLE hUV) (genericPoint X) hg
  change (f.app V ≫ X.presheaf.map (homOfLE hUV).op) ≫ _ = _
  rw [Category.assoc, hres]
  change f.app V ≫ X.presheaf.germ _ _ _ =
    Y.presheaf.germ V _ _ ≫ (Y.presheaf.stalkSpecializes _ ≫ f.stalkMap (genericPoint X))
  rw [← Category.assoc, TopCat.Presheaf.germ_stalkSpecializes]
  exact (f.germ_stalkMap V (genericPoint X) _).symm

/-- Injectivity is on the original section map, with no replacement scalar action. -/
theorem appLE_injective : Function.Injective (f.appLE V U hUV) := by
  intro a b hab
  apply Y.germToFunctionField_injective V
  apply (functionFieldMap f).injective
  have he (c : Γ(Y, V)) : X.germToFunctionField U (f.appLE V U hUV c) =
      functionFieldMap f (Y.germToFunctionField V c) :=
    congrArg (fun k : Γ(Y, V) ⟶ X.functionField ↦ k c) (appLE_germToFunctionField f V U hUV)
  exact (he a).symm.trans ((congrArg (X.germToFunctionField U) hab).trans (he b))

/-- The original birational field map makes each adapted section algebra algebraic. -/
theorem appLE_isAlgebraic
    (hV : IsAffineOpen V)
    (hff : IsIso (CommRingCat.ofHom (functionFieldMap f))) :
    letI := (f.appLE V U hUV).hom.toAlgebra
    Algebra.IsAlgebraic Γ(Y, V) Γ(X, U) := by
  let := (f.appLE V U hUV).hom.toAlgebra
  let : IsFractionRing Γ(Y, V) Y.functionField :=
    AlgebraicGeometry.functionField_isFractionRing_of_isAffineOpen Y V hV
  let := hff
  have he (a : Γ(Y, V)) : X.germToFunctionField U (f.appLE V U hUV a) =
      functionFieldMap f (algebraMap Γ(Y, V) Y.functionField a) :=
    congrArg (fun k : Γ(Y, V) ⟶ X.functionField ↦ k a) (appLE_germToFunctionField f V U hUV)
  refine ⟨fun b ↦ ?_⟩
  obtain ⟨z, hz⟩ := (ConcreteCategory.bijective_of_isIso
    (CommRingCat.ofHom (functionFieldMap f))).2 (X.germToFunctionField U b)
  obtain ⟨a, s, hs, has⟩ := IsFractionRing.div_surjective Γ(Y, V) z
  have hs0 : s ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp hs
  have hsF : functionFieldMap f (algebraMap Γ(Y, V) Y.functionField s) ≠ 0 := by
    apply (map_ne_zero (functionFieldMap f)).mpr
    exact (map_ne_zero_iff _ (IsFractionRing.injective Γ(Y, V) Y.functionField)).mpr hs0
  have hrat : functionFieldMap f (algebraMap Γ(Y, V) Y.functionField a) /
      functionFieldMap f (algebraMap Γ(Y, V) Y.functionField s) = X.germToFunctionField U b := by
    rw [← map_div₀, has]
    exact hz
  have hrel : f.appLE V U hUV s * b = f.appLE V U hUV a := by
    apply X.germToFunctionField_injective U
    rw [map_mul, he, he]
    exact (mul_comm _ _).trans ((div_eq_iff hsF).mp hrat).symm
  refine ⟨Polynomial.C s * Polynomial.X - Polynomial.C a, ?_, ?_⟩
  · exact linearPolynomial_ne_zero a s hs0
  · change Polynomial.aeval b (Polynomial.C s * Polynomial.X - Polynomial.C a) = 0
    simp only [map_sub, map_mul, Polynomial.aeval_C, Polynomial.aeval_X,
      RingHom.algebraMap_toAlgebra, sub_eq_zero]
    exact hrel

include hUV in
/-- Surface GF2 on an actual adapted pair of nonempty affine charts. There is
no regularity, global field or absolute separatedness hypothesis. -/
theorem adaptedChart_nagata_and_dimension [LocallyOfFiniteType f]
    (hV : IsAffineOpen V) (hU : IsAffineOpen U)
    (hNagata : IsNagataRing.{u, 0} Γ(Y, V)) (hdY : topologicalKrullDim Y ≤ 2)
    (hff : IsIso (CommRingCat.ofHom (functionFieldMap f))) :
    IsNagataRing.{u, 0} Γ(X, U) ∧ ringKrullDim Γ(X, U) ≤ 2 := by
  have hdV : ringKrullDim Γ(Y, V) ≤ 2 := by
    have hd := hV.fromSpec.isOpenEmbedding.isEmbedding.isInducing.topologicalKrullDim_le
    change topologicalKrullDim (PrimeSpectrum Γ(Y, V)) ≤ topologicalKrullDim Y at hd
    rw [PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim] at hd
    exact hd.trans hdY
  let := (f.appLE V U hUV).hom.toAlgebra
  let : Algebra.FiniteType Γ(Y, V) Γ(X, U) := f.finiteType_appLE hV hU hUV
  let : Algebra.IsAlgebraic Γ(Y, V) Γ(X, U) := appLE_isAlgebraic f V U hUV hV hff
  exact hNagata.of_finiteType_isAlgebraic_and_dimLE_two hdV (appLE_injective f V U hUV)

/-- The source dimension bound follows from actual adapted affine charts and
stalk localization. The base is not required affine or regular. -/
theorem dimension_le_two_of_birational [LocallyOfFiniteType f]
    (hNagata : ∀ V : Y.affineOpens, Nonempty V.1 → IsNagataRing.{u, 0} Γ(Y, V.1))
    (hdY : topologicalKrullDim Y ≤ 2)
    (hff : IsIso (CommRingCat.ofHom (functionFieldMap f))) :
    topologicalKrullDim X ≤ 2 := by
  rw [topologicalKrullDim_eq_iSup_stalk]
  apply iSup_le
  intro x
  obtain ⟨V, hV, hxV, _⟩ := exists_isAffineOpen_mem_and_subset
    (show f x ∈ (⊤ : Y.Opens) from trivial)
  obtain ⟨U, hU, hxU, hUV⟩ := exists_isAffineOpen_mem_and_subset
    (show x ∈ f ⁻¹ᵁ V from hxV)
  let : Nonempty V := ⟨⟨f x, hxV⟩⟩
  let : Nonempty U := ⟨⟨x, hxU⟩⟩
  have hdU := (adaptedChart_nagata_and_dimension f V U hUV hV hU
    (hNagata ⟨V, hV⟩ inferInstance) hdY hff).2
  let p := (hU.primeIdealOf ⟨x, hxU⟩).asIdeal
  let : p.IsPrime := (hU.primeIdealOf ⟨x, hxU⟩).isPrime
  let : Algebra Γ(X, U) (X.presheaf.stalk x) := X.presheaf.algebra_section_stalk ⟨x, hxU⟩
  let : IsLocalization.AtPrime (X.presheaf.stalk x) p := hU.isLocalization_stalk ⟨x, hxU⟩
  have hlocal : ringKrullDim (X.presheaf.stalk x) ≤ ringKrullDim Γ(X, U) := by
    rw [IsLocalization.AtPrime.ringKrullDim_eq_height p (X.presheaf.stalk x)]
    exact p.height_le_ringKrullDim_of_isPrime
  exact hlocal.trans hdU

end AlgebraicGeometry.Scheme.NormalizedPointDomination
