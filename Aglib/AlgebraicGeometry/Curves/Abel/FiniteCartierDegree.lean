/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Morphisms.FiniteFlat.DegreeLength
public import Aglib.AlgebraicGeometry.Curves.Picard.DivisorInverse
public import Aglib.AlgebraicGeometry.Curves.Picard.Degree.ProductFormula
public import Aglib.AlgebraicGeometry.Modules.Invertible.ZeroLocus.Regular
public import Aglib.AlgebraicGeometry.Modules.Invertible.ZeroLocus.Uniqueness
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Localization.Algebra
public import Aglib.AlgebraicGeometry.Modules.Invertible.Basic
public import Aglib.AlgebraicGeometry.Modules.InternalHom
public import Aglib.AlgebraicGeometry.Modules.Invertible.Dual
public import Aglib.AlgebraicGeometry.Modules.Invertible.Tensor
public import Aglib.AlgebraicGeometry.Modules.Invertible.TensorAssociator
public import Aglib.AlgebraicGeometry.Modules.Pullback.OpenRestriction

/-!
# Actual finite Cartier-divisor degree foundations

The target is the unchanged `Abel.FiniteCartierIdealDegree` in `Abel/Degree.lean:71`.
Its given product formula and actual locally rank-one kernel ideal are retained
hypotheses. No additional general family is assumed here. The primary-factor
localization dictionary preserves nilpotent multiplicities and identifies those
factors with the actual affine-scheme stalks. The actual ideal inclusion supplies
local generators; its stalk quotients give the residue-weighted coefficients of
the divisor corresponding to its dual. The complete finite sum supplies the
literal original family at the end of this file.

Authoring basis: `3af0d5588a81bbe409c905fd8857866da397491b`, with the frozen
`Picard/Degree/FiniteSupportLengths.lean` and `ProductFormula.lean`; Lean4.34.1,
Mathlibd13f23b723b8a846827a245b89c10fc7d3f11612. Quillen83629578 is outside this
proof closure. The given product formula remains exactly the displayed input
of the original family; no proper cohomology theorem or additional tensor-family
input is used here. Integration basis: `d0dc4cca7af233fe0ba5be27efa436f64cf0e403`.
-/

/-!
Source: `R5Lab.AlgebraicGeometry.Curves.Abel.FiniteCartierDegree`, supplied R5
revision `f8a3314ddecffcada2ec721d26d56a937bed9690`, SHA-256
`7046c18285f374e3baad3a2dcc0c153d6089df9bed15b78e7009f15396daed29`.
The primary components, actual stalk quotients, nilpotent lengths and original
product-formula input are retained. The theorem supplies the original full
finite-Cartier ideal-dual degree family; no representability input is used.
-/

@[expose] public section

open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Hom
open AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.Hom
open AlgebraicGeometry.Scheme.Modules.Invertible
open AlgebraicGeometry.Scheme.OverField.Curve

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite IsLocalRing
open AlgebraicGeometry.Scheme.OverField.Curve.Picard.Degree.FiniteSupportLengths
open AlgebraicGeometry.Scheme.OverField.Curve.Picard
open AlgebraicGeometry.Scheme.OverField.Curve.Picard.RationalTrivialization
open AlgebraicGeometry.Scheme.Hom.FiniteFlat
namespace AlgebraicGeometry.Scheme.OverField.Curve.Abel.FiniteCartierDegree

namespace PrimaryFactors
variable (B : Type*) [CommRing B] [IsArtinianRing B]

/-- The canonical nonreduced primary-product equivalence at an exponent that
annihilates the _root_.nilradical. Its maps are the actual quotient maps. -/
def componentsEquiv (n : ℕ) (hn : _root_.nilradical B ^ (n + 1) = ⊥) :
    B ≃ₐ[B] ∀ m : MaximalSpectrum B, Algebra.ArtinComponent B n m :=
  (AlgEquiv.quotientBot B B).symm.trans
    ((Ideal.quotientEquivAlgOfEq B hn.symm).trans
      (IsArtinianRing.quotNilradicalPowEquivPi (R := B) (n + 1)))

theorem componentsEquiv_apply (n : ℕ) (hn : _root_.nilradical B ^ (n + 1) = ⊥)
    (r : B) (m : MaximalSpectrum B) :
    componentsEquiv B n hn r m = Ideal.Quotient.mk (m.asIdeal ^ (n + 1)) r := by
  simp [componentsEquiv, IsArtinianRing.quotNilradicalPowEquivPi_apply]
  rfl
theorem component_isLocalization (n : ℕ) (hn : _root_.nilradical B ^ (n + 1) = ⊥)
    (m : MaximalSpectrum B) : IsLocalization.AtPrime (Algebra.ArtinComponent B n m) m.asIdeal := by
  classical
  let := m.isMaximal
  let := Ideal.Quotient.field m.asIdeal
  let := Fintype.ofFinite (MaximalSpectrum B)
  let C := Algebra.ArtinComponent B n m
  let h : m.asIdeal ^ (n + 1) ≤ m.asIdeal :=
    Ideal.pow_le_self (I := m.asIdeal) (Nat.succ_ne_zero n)
  let φ : C →+* B ⧸ m.asIdeal := Ideal.Quotient.factor h
  let : IsLocalHom φ := IsLocalHom.of_surjective φ (Ideal.Quotient.factor_surjective h)
  let e : B ≃ₐ[B] ∀ j : MaximalSpectrum B, Algebra.ArtinComponent B n j :=
    (AlgEquiv.quotientBot B B).symm.trans
      ((Ideal.quotientEquivAlgOfEq B hn.symm).trans
        (IsArtinianRing.quotNilradicalPowEquivPi (R := B) (n + 1)))
  have hp (r : B) (j : MaximalSpectrum B) :
      e r j = Ideal.Quotient.mk (j.asIdeal ^ (n + 1)) r := by
    simp [e, IsArtinianRing.quotNilradicalPowEquivPi_apply]
    rfl
  let d : B := e.symm (Pi.single m (1 : C))
  have hd (j : MaximalSpectrum B) : e d j = Pi.single m (1 : C) j := by
    exact congrFun (e.apply_symm_apply (Pi.single m (1 : C))) j
  have hdm : Ideal.Quotient.mk (m.asIdeal ^ (n + 1)) d = 1 := by
    rw [← hp, hd, Pi.single_eq_same]
  have hnot : d ∉ m.asIdeal := by
    intro hin
    have hz : Ideal.Quotient.mk m.asIdeal d = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr hin
    have ho : Ideal.Quotient.mk m.asIdeal d = 1 := by
      change φ (Ideal.Quotient.mk (m.asIdeal ^ (n + 1)) d) = 1
      rw [hdm, map_one]
    exact zero_ne_one (hz.symm.trans ho)
  have hk (r : B) (hr : Ideal.Quotient.mk (m.asIdeal ^ (n + 1)) r = 0) : d * r = 0 := by
    apply e.injective
    rw [map_mul, map_zero]
    ext j
    change e d j * e r j = 0
    rw [hd]
    by_cases hj : j = m
    · subst j
      rw [Pi.single_eq_same, one_mul, hp, hr]
    · rw [Pi.single_eq_of_ne hj, zero_mul]
  refine ⟨{ map_units := ?_, surj := ?_, exists_of_eq := ?_ }⟩
  · intro s
    apply isUnit_of_map_unit φ _
    apply isUnit_iff_ne_zero.mpr
    change Ideal.Quotient.mk m.asIdeal s.val ≠ 0
    exact fun hz => s.property (Ideal.Quotient.eq_zero_iff_mem.mp hz)
  · intro z
    obtain ⟨r, hr⟩ := Ideal.Quotient.mk_surjective z
    refine ⟨⟨r, 1⟩, ?_⟩
    rw [OneMemClass.coe_one, map_one, mul_one]
    change z = Ideal.Quotient.mk (m.asIdeal ^ (n + 1)) r
    exact hr.symm
  · intro x y hxy
    refine ⟨⟨d, hnot⟩, ?_⟩
    have hz : Ideal.Quotient.mk (m.asIdeal ^ (n + 1)) (x - y) = 0 := by
      rw [map_sub]
      exact sub_eq_zero.mpr hxy
    have h0 := hk (x - y) hz
    rwa [mul_sub, sub_eq_zero] at h0
end PrimaryFactors

section ActualStalkDictionary
universe u
variable (D : Scheme.{u}) [IsAffine D] [IsArtinianRing Γ(D, ⊤)]
def componentStalkEquiv (n : ℕ) (hn : _root_.nilradical Γ(D, ⊤) ^ (n + 1) = ⊥)
    (m : MaximalSpectrum Γ(D, ⊤)) :
    let x := (isAffineOpen_top D).fromSpec ⟨m.asIdeal, m.isMaximal.isPrime⟩
    letI : Algebra Γ(D, ⊤) (D.presheaf.stalk x) :=
      TopCat.Presheaf.algebra_section_stalk D.presheaf (⟨x, trivial⟩ : (⊤ : D.Opens))
    Algebra.ArtinComponent Γ(D, ⊤) n m ≃ₐ[Γ(D, ⊤)] D.presheaf.stalk x := by
  let hD := isAffineOpen_top D
  let p : PrimeSpectrum Γ(D, ⊤) := ⟨m.asIdeal, m.isMaximal.isPrime⟩
  let x := hD.fromSpec p
  letI : Algebra Γ(D, ⊤) (D.presheaf.stalk x) :=
    TopCat.Presheaf.algebra_section_stalk D.presheaf (⟨x, trivial⟩ : (⊤ : D.Opens))
  letI : IsLocalization.AtPrime (D.presheaf.stalk x) m.asIdeal :=
    hD.isLocalization_stalk' p trivial
  letI : IsLocalization.AtPrime (Algebra.ArtinComponent Γ(D, ⊤) n m) m.asIdeal :=
    PrimaryFactors.component_isLocalization Γ(D, ⊤) n hn m
  exact IsLocalization.algEquiv m.asIdeal.primeCompl _ _
end ActualStalkDictionary

namespace FiniteStalks
universe u
variable (k : Type u) [Field k] (D : Scheme.{u}) (q : D ⟶ Spec (.of k)) [IsFinite q]
/-- The actual affine-scheme point corresponding to a coordinate maximal ideal. -/
def point (m : MaximalSpectrum Γ(D, ⊤)) : D := by
  let : IsAffine D := isAffine_of_isAffineHom q
  exact (isAffineOpen_top D).fromSpec ⟨m.asIdeal, m.isMaximal.isPrime⟩
/-- Primary-factor/stalk equivalence on the exact structural base-field scalars. -/
def factorStalkEquiv (n : ℕ) (hn : _root_.nilradical Γ(D, ⊤) ^ (n + 1) = ⊥)
    (m : MaximalSpectrum Γ(D, ⊤)) :
    letI : Algebra k Γ(D, ⊤) := coordinateAlgebra k (Over.mk q)
    letI : IsAffine D := isAffine_of_isAffineHom q
    let x := (isAffineOpen_top D).fromSpec (⟨m.asIdeal, m.isMaximal.isPrime⟩ : PrimeSpectrum
        Γ(D, ⊤))
    letI : Algebra k (D.presheaf.stalk x) := stalkConstantsAlgebra D q x
    Algebra.ArtinComponent Γ(D, ⊤) n m ≃ₐ[k] D.presheaf.stalk x := by
  letI : Algebra k Γ(D, ⊤) := coordinateAlgebra k (Over.mk q)
  let : IsAffine D := isAffine_of_isAffineHom q
  let : Module.Finite k Γ(D, ⊤) := finite_coordinate_algebra k D q
  let : IsArtinianRing Γ(D, ⊤) := IsArtinianRing.of_finite k Γ(D, ⊤)
  let x := (isAffineOpen_top D).fromSpec (⟨m.asIdeal, m.isMaximal.isPrime⟩ : PrimeSpectrum Γ(D, ⊤))
  letI : Algebra Γ(D, ⊤) (D.presheaf.stalk x) :=
    TopCat.Presheaf.algebra_section_stalk D.presheaf (⟨x, trivial⟩ : (⊤ : D.Opens))
  letI : Algebra k (D.presheaf.stalk x) := stalkConstantsAlgebra D q x
  let : IsScalarTower k Γ(D, ⊤) (D.presheaf.stalk x) :=
    IsScalarTower.of_algebraMap_eq' (by ext a; rfl)
  have e : Algebra.ArtinComponent Γ(D, ⊤) n m ≃ₐ[Γ(D, ⊤)] D.presheaf.stalk x :=
    componentStalkEquiv D n hn m
  exact e.restrictScalars k


/-- Every finite-scheme degree equals a full sum of actual stalk dimensions.
The chosen exponent remains accompanied by its _root_.nilradical-annihilation proof. -/
theorem degree_eq_sum_stalk_finrank :
    letI : Algebra k Γ(D, ⊤) := coordinateAlgebra k (Over.mk q)
    letI : Module.Finite k Γ(D, ⊤) := finite_coordinate_algebra k D q
    let : IsArtinianRing Γ(D, ⊤) := IsArtinianRing.of_finite k Γ(D, ⊤)
    letI := Fintype.ofFinite (MaximalSpectrum Γ(D, ⊤))
    Scheme.Hom.finiteSchemeDegree k q = ∑ m : MaximalSpectrum Γ(D, ⊤),
      let x := point k D q m
      let : Algebra k (D.presheaf.stalk x) := stalkConstantsAlgebra D q x
      Module.finrank k (D.presheaf.stalk x) := by
  classical
  let : Algebra k Γ(D, ⊤) := coordinateAlgebra k (Over.mk q)
  let : Module.Finite k Γ(D, ⊤) := finite_coordinate_algebra k D q
  let : IsArtinianRing Γ(D, ⊤) := IsArtinianRing.of_finite k Γ(D, ⊤)
  let := Fintype.ofFinite (MaximalSpectrum Γ(D, ⊤))
  obtain ⟨n, hn⟩ := IsArtinianRing.isNilpotent_nilradical (R := Γ(D, ⊤))
  have hz : _root_.nilradical Γ(D, ⊤) ^ (n + 1) = ⊥ := by
    rw [pow_succ, hn, zero_mul, Ideal.zero_eq_bot]
  let e := PrimaryFactors.componentsEquiv Γ(D, ⊤) n hz
  calc
    Scheme.Hom.finiteSchemeDegree k q =
        Module.finrank k (∀ m : MaximalSpectrum Γ(D, ⊤), Algebra.ArtinComponent Γ(D, ⊤) n m) :=
      (e.toLinearEquiv.restrictScalars k).finrank_eq
    _ = ∑ m : MaximalSpectrum Γ(D, ⊤), Module.finrank k (Algebra.ArtinComponent Γ(D, ⊤) n m) :=
      Module.finrank_pi_fintype k
    _ = _ := by
      apply Finset.sum_congr rfl
      intro m _
      let x := point k D q m
      let : Algebra k (D.presheaf.stalk x) := stalkConstantsAlgebra D q x
      have e' : Algebra.ArtinComponent Γ(D, ⊤) n m ≃ₐ[k] D.presheaf.stalk x :=
        factorStalkEquiv k D q n hz m
      exact e'.toLinearEquiv.finrank_eq

end FiniteStalks
namespace LocalizedKernel
universe u
variable {D X : Scheme.{u}} (i : D ⟶ X) [IsClosedImmersion i]
theorem stalkKernel_eq_affine_map (U : X.Opens) (hU : IsAffineOpen U) (y : D) (hy : i y ∈ U) :
    RingHom.ker (i.stalkMap y).hom =
      Ideal.map (X.presheaf.germ U (i y) hy).hom (RingHom.ker (i.app U).hom) := by
  let V := i ⁻¹ᵁ U
  let hV : IsAffineOpen V := hU.preimage i
  let g := (i.app U).hom
  let R := Γ(X, U)
  let S := Γ(D, V)
  let px := hU.primeIdealOf ⟨i y, hy⟩
  let py := hV.primeIdealOf ⟨y, hy⟩
  let M := px.asIdeal.primeCompl
  let T := py.asIdeal.primeCompl
  let : Algebra R (X.presheaf.stalk (i y)) :=
    TopCat.Presheaf.algebra_section_stalk X.presheaf (⟨i y, hy⟩ : U)
  let : Algebra S (D.presheaf.stalk y) :=
    TopCat.Presheaf.algebra_section_stalk D.presheaf (⟨y, hy⟩ : V)
  let : IsLocalization M (X.presheaf.stalk (i y)) := hU.isLocalization_stalk ⟨i y, hy⟩
  let : IsLocalization T (D.presheaf.stalk y) := hV.isLocalization_stalk ⟨y, hy⟩
  have hp : py.comap g = px := by
    simpa [py, px, V, Scheme.Hom.appLE, g] using
      (IsAffineOpen.comap_primeIdealOf_appLE (f := i) (x := y) U hU V hV le_rfl hy)
  have hcomap : Submonoid.comap g T = M := by
    ext r
    change (g r ∉ py.asIdeal) ↔ r ∉ px.asIdeal
    rw [← congrArg PrimeSpectrum.asIdeal hp]
    rfl
  have hT : Submonoid.map g M = T := by
    rw [← hcomap]
    exact Submonoid.map_comap_eq_of_surjective (i.app_surjective U hU) T
  have hcomm : (i.stalkMap y).hom.comp (algebraMap R (X.presheaf.stalk (i y))) =
      (algebraMap S (D.presheaf.stalk y)).comp g := by
    ext r
    exact i.germ_stalkMap_apply U y hy r
  have hf : (i.stalkMap y).hom =
      IsLocalization.map (D.presheaf.stalk y) g (hT.symm ▸ M.le_comap_map) := by
    apply IsLocalization.ringHom_ext M
    exact hcomm.trans (IsLocalization.map_comp (hT.symm ▸ M.le_comap_map)).symm
  rw [hf, IsLocalization.ker_map (D.presheaf.stalk y) g hT]
  rfl
end LocalizedKernel

open Scheme.Modules.Invertible Scheme.Modules.Invertible.RationalTrivialization Scheme.Hom
namespace MapDivisors
universe u
variable (X : Scheme.{u}) [IsIntegral X] (L : LineBundle X)
variable (φ : (show X.Modules from L.val) ⟶ (show X.Modules from SheafOfModules.unit
    X.ringCatSheaf))
variable (U₀ : X.Opens) [Nonempty U₀]
variable (e : L.val.over U₀ ≅ SheafOfModules.unit (X.ringCatSheaf.over U₀))
theorem map_coordinate (V : X.Opens) [Nonempty V] (s : L.val.val.obj (op V)) :
    X.germToFunctionField V (φ.app V s) =
      coordinate X L.val U₀ e V s *
        X.germToFunctionField U₀ (φ.app U₀ (chartGenerator X L.val U₀ e)) := by
  let : Nonempty ((V ⊓ U₀) : X.Opens) := nonempty_inf X V U₀
  rw [← germ_restrict X (homOfLE inf_le_left : V ⊓ U₀ ⟶ V) (φ.app V s)]
  have hn := PresheafOfModules.naturality_apply φ.val
    (homOfLE inf_le_left : V ⊓ U₀ ⟶ V).op s
  change φ.app (V ⊓ U₀) (L.val.val.map _ s) = X.presheaf.map _ (φ.app V s) at hn
  rw [← hn, lineBundleMap_chart_general L φ U₀ e (V ⊓ U₀) inf_le_right, map_mul,
    germ_restrict X (homOfLE inf_le_right : V ⊓ U₀ ⟶ U₀)]
  rfl
omit [IsIntegral X] in
theorem generator_image_ne_zero [IsIntegral X] [Mono φ] : φ.app U₀ (chartGenerator X L.val U₀
    e) ≠ 0 := by
  let ev : X.Modules ⥤ ModuleCat Γ(X, U₀) := SheafOfModules.evaluation X.ringCatSheaf (op U₀)
  have : PreservesLimits ev := inferInstanceAs
    (PreservesLimits (SheafOfModules.evaluation X.ringCatSheaf (op U₀)))
  have hinj : Function.Injective (φ.app U₀) :=
    (ModuleCat.mono_iff_injective (ev.map φ)).mp inferInstance
  intro hz
  have hs : chartGenerator X L.val U₀ e = 0 := hinj (hz.trans (φ.app U₀).hom.map_zero.symm)
  have ho := congrArg (chartSectionEquiv X L.val U₀ e U₀ le_rfl) hs
  simp [chartGenerator] at ho
omit [IsIntegral X] in
theorem imageIdeal_eq_span_generator [IsIntegral X] (W : X.Opens)
    (d : L.val.over W ≅ SheafOfModules.unit (X.ringCatSheaf.over W)) :
    sectionImageIdeal φ W =
      Ideal.span {(show Γ(X, W) from φ.app W (chartGenerator X L.val W d))} := by
  apply le_antisymm
  · rintro a ⟨s, rfl⟩
    apply Ideal.mem_span_singleton.mpr
    have h := lineBundleMap_chart_general L φ W d W le_rfl s
    have hh : (homOfLE le_rfl : W ⟶ W) = 𝟙 W := Subsingleton.elim _ _
    rw [hh, op_id, X.presheaf.map_id] at h
    change (show Γ(X, W) from φ.app W s) = chartSectionEquiv X L.val W d W le_rfl s *
      (show Γ(X, W) from φ.app W (chartGenerator X L.val W d)) at h
    exact ⟨chartSectionEquiv X L.val W d W le_rfl s, h.trans (mul_comm _ _)⟩
  · apply Ideal.span_le.mpr
    intro a ha
    simp only [Set.mem_singleton_iff] at ha
    subst a
    exact ⟨chartGenerator X L.val W d, rfl⟩

def imageUnit [Mono φ] : X.functionFieldˣ :=
  Units.mk0 (X.germToFunctionField U₀ (φ.app U₀ (chartGenerator X L.val U₀ e))) (by
    simpa only [map_zero] using
      (X.germToFunctionField_injective U₀).ne (generator_image_ne_zero X L φ U₀ e))

variable [AlgebraicGeometry.IsNoetherian X]
variable [∀ x : AlgebraicGeometry.Scheme.ClosedPoint X, IsDiscreteValuationRing
    (X.presheaf.stalk x.val)]
def mapDivisor [Mono φ] : Divisors.Divisor X :=
  Divisors.principal X (Additive.ofMul (imageUnit X L φ U₀ e)) -
    divisor X L.val U₀ e L.property

theorem mapDivisor_coefficient [Mono φ] (W : X.Opens) [Nonempty W]
    (d : L.val.over W ≅ SheafOfModules.unit (X.ringCatSheaf.over W))
    (x : AlgebraicGeometry.Scheme.ClosedPoint X) (hx : x.val ∈ W) :
    mapDivisor X L φ U₀ e x =
      X.ord (X.germToFunctionField W (φ.app W (chartGenerator X L.val W d))) x.val := by
  rw [mapDivisor, Finsupp.sub_apply, Divisors.principal_apply, divisor_apply,
    divisorCoefficient_chart X L.val U₀ e L.property W d x hx,
    map_coordinate X L φ U₀ e W (chartGenerator X L.val W d)]
  rw [Scheme.ord_mul (coordinate_generator_ne_zero X L.val U₀ e L.property W d)
    (show X.germToFunctionField U₀ (φ.app U₀ (chartGenerator X L.val U₀ e)) ≠ 0 from
      (imageUnit X L φ U₀ e).ne_zero)]
  change X.ord (imageUnit X L φ U₀ e : X.functionField) x.val -
    (-X.ord (coordinate X L.val U₀ e W (chartGenerator X L.val W d)) x.val) =
      X.ord (coordinate X L.val U₀ e W (chartGenerator X L.val W d)) x.val +
        X.ord (imageUnit X L φ U₀ e : X.functionField) x.val
  omega

variable {k : Type u} [Field k] (p : X ⟶ Spec (.of k))
theorem degree_dual_eq_mapDivisor [Mono φ] (hdim : topologicalKrullDim X ≤ 1)
    (hprod : Picard.Degree.PrincipalProductFormula X p) :
    Picard.Degree.lineBundleDegree X p hdim hprod (dualLineBundle X L) =
      Picard.Degree.degDiv X p (mapDivisor X L φ U₀ e) := by
  have hL : Picard.Degree.lineBundleDegree X p hdim hprod L =
      Picard.Degree.degDiv X p (divisor X L.val U₀ e L.property) := by
    rw [Picard.Degree.lineBundleDegree_iso X p hdim hprod
      (L := L) (N := DivisorClass.divisorLineBundle X hdim (divisor X L.val U₀ e L.property))
      (Picard.DivisorInverse.toDivisorIso X L.val L.property U₀ e hdim)]
    exact Picard.Degree.lineBundleDegree_divisor X p hdim hprod _
  rw [Picard.Degree.lineBundleDegree_dual, hL]
  simp only [mapDivisor, map_sub, hprod (imageUnit X L φ U₀ e)]
  ring

end MapDivisors

namespace CartierLocal
universe u
variable (X : Scheme.{u}) [IsIntegral X] (L : LineBundle X)
variable (φ : (show X.Modules from L.val) ⟶ (show X.Modules from SheafOfModules.unit
    X.ringCatSheaf))
omit [IsIntegral X] in
theorem imageIdeal_eq_span_restrict_generator [IsIntegral X] (W : X.Opens)
    (d : L.val.over W ≅ SheafOfModules.unit (X.ringCatSheaf.over W))
    (V : X.Opens) (h : V ≤ W) :
    sectionImageIdeal φ V = Ideal.span {(show Γ(X, V) from
      X.presheaf.map (homOfLE h).op (φ.app W (chartGenerator X L.val W d)))} := by
  apply le_antisymm
  · rintro a ⟨s, rfl⟩
    apply Ideal.mem_span_singleton.mpr
    have ht := lineBundleMap_chart_general L φ W d V h s
    change (show Γ(X, V) from φ.app V s) = chartSectionEquiv X L.val W d V h s *
      (show Γ(X, V) from X.presheaf.map (homOfLE h).op
        (φ.app W (chartGenerator X L.val W d))) at ht
    exact ⟨chartSectionEquiv X L.val W d V h s, ht.trans (mul_comm _ _)⟩
  · apply Ideal.span_le.mpr
    intro a ha
    simp only [Set.mem_singleton_iff] at ha
    subst a
    refine ⟨L.val.val.map (homOfLE h).op (chartGenerator X L.val W d), ?_⟩
    exact PresheafOfModules.naturality_apply φ.val (homOfLE h).op _

variable {D : Scheme.{u}} (i : D ⟶ X) [IsClosedImmersion i]
variable (hI : Scheme.Modules.Invertible.IsLocallyRankOne X
    (idealModule i))
include hI
theorem ideal_stalkKernel_eq_span_generator (W : X.Opens)
    (d : (idealModule i).over W ≅ SheafOfModules.unit (X.ringCatSheaf.over W))
    (y : D) (hy : i y ∈ W) :
    RingHom.ker (i.stalkMap y).hom = Ideal.span {(show X.presheaf.stalk (i y) from
      X.presheaf.germ W (i y) hy ((idealInclusion i).app W
        (chartGenerator X (idealModule i) W d)))} := by
  obtain ⟨V, hV, hyV, hVW⟩ := exists_isAffineOpen_mem_and_subset hy
  rw [LocalizedKernel.stalkKernel_eq_affine_map i V hV y hyV,
    ← sectionImageIdeal_idealInclusion i V,
    imageIdeal_eq_span_restrict_generator X ⟨idealModule i, hI⟩ (idealInclusion i) W d V hVW,
    Ideal.map_span]
  simp only [Set.image_singleton]
  congr 2
  exact X.presheaf.germ_res_apply (homOfLE hVW) (i y) hyV _

omit hI
variable {k : Type u} [Field k] (p : X ⟶ Spec (.of k))
def stalkMapAlgHom (y : D) :
    letI := stalkConstantsAlgebra X p (i y)
    letI := stalkConstantsAlgebra D (i ≫ p) y
    X.presheaf.stalk (i y) →ₐ[k] D.presheaf.stalk y := by
  letI := stalkConstantsAlgebra X p (i y)
  letI := stalkConstantsAlgebra D (i ≫ p) y
  refine ⟨(i.stalkMap y).hom, ?_⟩
  intro a
  change (i.stalkMap y).hom (stalkConstants X p (i y) a) = stalkConstants D (i ≫ p) y a
  simp only [stalkConstants]
  exact i.germ_stalkMap_apply ⊤ y trivial _
def stalkQuotientEquiv (y : D) (a : X.presheaf.stalk (i y))
    (ha : RingHom.ker (i.stalkMap y).hom = Ideal.span {a}) :
    letI := stalkConstantsAlgebra X p (i y)
    letI := stalkConstantsAlgebra D (i ≫ p) y
    (X.presheaf.stalk (i y) ⧸ Ideal.span {a}) ≃ₐ[k] D.presheaf.stalk y := by
  letI := stalkConstantsAlgebra X p (i y)
  letI := stalkConstantsAlgebra D (i ≫ p) y
  let f : X.presheaf.stalk (i y) →ₐ[k] D.presheaf.stalk y := stalkMapAlgHom X i p y
  have h : RingHom.ker f = Ideal.span {a} := ha
  exact (Ideal.quotientEquivAlgOfEq k h.symm).trans
    (Ideal.quotientKerAlgEquivOfSurjective (f := f) (i.stalkMap_surjective y))

variable [AlgebraicGeometry.IsNoetherian X]
variable [∀ x : AlgebraicGeometry.Scheme.ClosedPoint X, IsDiscreteValuationRing
    (X.presheaf.stalk x.val)]
variable [LocallyOfFiniteType p]
include hI
theorem ideal_mapDivisor_weighted_coefficient (U₀ : X.Opens) [Nonempty U₀]
    (e₀ : (idealModule i).over U₀ ≅ SheafOfModules.unit (X.ringCatSheaf.over U₀))
    (W : X.Opens) (d : (idealModule i).over W ≅ SheafOfModules.unit (X.ringCatSheaf.over W))
    (y : D) (hy : i y ∈ W) (hx : IsClosed ({i y} : Set X)) :
    letI := stalkConstantsAlgebra D (i ≫ p) y
    MapDivisors.mapDivisor X ⟨idealModule i, hI⟩ (idealInclusion i) U₀ e₀ ⟨i y, hx⟩ *
      Picard.Degree.weight X p ⟨i y, hx⟩ =
        (Module.finrank k (D.presheaf.stalk y) : ℤ) := by
  let : Nonempty W := ⟨⟨i y, hy⟩⟩
  let a : X.presheaf.stalk (i y) := X.presheaf.germ W (i y) hy
    ((idealInclusion i).app W (chartGenerator X (idealModule i) W d))
  have ha : a ≠ 0 := by
    simpa only [map_zero] using (germ_injective_of_isIntegral X (i y) hy).ne
      (MapDivisors.generator_image_ne_zero X ⟨idealModule i, hI⟩ (idealInclusion i) W d)
  have hc : Order.coheight (i y) = 1 := by
    let : IsDiscreteValuationRing (X.presheaf.stalk (i y)) := inferInstanceAs
      (IsDiscreteValuationRing (X.presheaf.stalk (⟨i y, hx⟩ :
          AlgebraicGeometry.Scheme.ClosedPoint X).val))
    exact Divisors.coheight_eq_one_of_dvr X (i y)
  let := stalkConstantsAlgebra X p (i y)
  let := stalkConstantsAlgebra D (i ≫ p) y
  have hq : RingHom.ker (i.stalkMap y).hom = Ideal.span {a} :=
    ideal_stalkKernel_eq_span_generator X i hI W d y hy
  have hdim := (stalkQuotientEquiv X i p y a hq).toLinearEquiv.finrank_eq
  have hord := Picard.Degree.ProductFormula.order_stalk_element X (i y) hc a ha
  rw [Scheme.algebraMap_germ_eq_germToFunctionField X hy] at hord
  rw [MapDivisors.mapDivisor_coefficient X ⟨idealModule i, hI⟩ (idealInclusion i) U₀ e₀ W d
    ⟨i y, hx⟩ hy, hord, ← hdim]
  exact (stalkQuotient_finrank_eq_weight_mul_colength X p (i y) hx hc a ha).symm
omit [IsNoetherian X]
    [∀ x : Scheme.ClosedPoint X, IsDiscreteValuationRing (X.presheaf.stalk x.val)] in
theorem ideal_generator_germ_isUnit_of_not_mem_range [IsNoetherian X]
    [∀ x : Scheme.ClosedPoint X, IsDiscreteValuationRing (X.presheaf.stalk x.val)] (W : X.Opens)
    (d : (idealModule i).over W ≅ SheafOfModules.unit (X.ringCatSheaf.over W))
    (x : X) (hx : x ∈ W) (hxr : x ∉ Set.range i) :
    IsUnit (X.presheaf.germ W x hx ((idealInclusion i).app W
      (chartGenerator X (idealModule i) W d))) := by
  obtain ⟨V, hV, hxV, hVW⟩ := exists_isAffineOpen_mem_and_subset hx
  have hsupp : x ∉ i.ker.support := by
    change x ∉ (i.ker.support : Set X)
    rw [Scheme.Hom.support_ker, i.isClosedEmbedding.isClosed_range.closure_eq]
    exact hxr
  have hz : x ∉ X.zeroLocus (U := V) (i.ker.ideal ⟨V, hV⟩) :=
    mt (Scheme.IdealSheafData.mem_support_iff_of_mem (I := i.ker) (U := ⟨V, hV⟩) hxV).mpr hsupp
  rw [Scheme.Hom.ker_apply, ← sectionImageIdeal_idealInclusion i V,
    imageIdeal_eq_span_restrict_generator X ⟨idealModule i, hI⟩ (idealInclusion i) W d V hVW,
    X.zeroLocus_span, X.zeroLocus_singleton] at hz
  have hu := (X.mem_basicOpen _ x hxV).mp (not_not.mp hz)
  rwa [X.presheaf.germ_res_apply (homOfLE hVW) x hxV] at hu

theorem ideal_mapDivisor_eq_zero_of_not_mem_range (U₀ : X.Opens) [Nonempty U₀]
    (e₀ : (idealModule i).over U₀ ≅ SheafOfModules.unit (X.ringCatSheaf.over U₀))
    (x : AlgebraicGeometry.Scheme.ClosedPoint X) (hx : x.val ∉ Set.range i) :
    MapDivisors.mapDivisor X ⟨idealModule i, hI⟩ (idealInclusion i) U₀ e₀ x = 0 := by
  let c := localChart X (idealModule i) hI x.val
  let W := c.1
  let d := c.2.val
  have hxW : x.val ∈ W := c.2.property
  let : Nonempty W := ⟨⟨x.val, hxW⟩⟩
  let f : X.functionFieldˣ := MapDivisors.imageUnit X ⟨idealModule i, hI⟩ (idealInclusion i) W d
  rw [MapDivisors.mapDivisor_coefficient X ⟨idealModule i, hI⟩ (idealInclusion i) U₀ e₀ W d x hxW]
  change X.ord (f : X.functionField) x.val = 0
  apply (Divisors.order_zero_iff_stalk_unit X x.val (Divisors.coheight_eq_one_of_dvr X x.val) f).mpr
  exact ⟨_, ideal_generator_germ_isUnit_of_not_mem_range X i hI W d x.val hxW hx,
    Scheme.algebraMap_germ_eq_germToFunctionField X hxW _⟩
end CartierLocal

namespace CartierSum
universe u
variable (k : Type u) [Field k] (D : Scheme.{u}) (q : D ⟶ Spec (.of k)) [IsFinite q]
theorem point_injective : Function.Injective (FiniteStalks.point k D q) := by
  let : IsAffine D := isAffine_of_isAffineHom q
  exact (isAffineOpen_top D).fromSpec.isOpenEmbedding.injective.comp
    MaximalSpectrum.toPrimeSpectrum_injective

theorem point_surjective : Function.Surjective (FiniteStalks.point k D q) := by
  let : IsAffine D := isAffine_of_isAffineHom q
  let : Algebra k Γ(D, ⊤) := coordinateAlgebra k (Over.mk q)
  let : Module.Finite k Γ(D, ⊤) := finite_coordinate_algebra k D q
  let : IsArtinianRing Γ(D, ⊤) := IsArtinianRing.of_finite k Γ(D, ⊤)
  intro y
  obtain ⟨P, hP⟩ : ∃ P : PrimeSpectrum Γ(D, ⊤), (isAffineOpen_top D).fromSpec P = y := by
    apply (Set.mem_range.mp ?_)
    rw [(isAffineOpen_top D).range_fromSpec]
    exact trivial
  refine ⟨IsArtinianRing.primeSpectrumEquivMaximalSpectrum P, ?_⟩
  exact hP

theorem point_isClosed (m : MaximalSpectrum Γ(D, ⊤)) :
    IsClosed ({FiniteStalks.point k D q m} : Set D) := by
  let : IsAffine D := isAffine_of_isAffineHom q
  let f := (isAffineOpen_top D).fromSpec
  have hf : Function.Surjective f := by
    rw [← Set.range_eq_univ, (isAffineOpen_top D).range_fromSpec]
    rfl
  let : Epi f.base := ConcreteCategory.epi_of_surjective _ hf
  let : IsIso f := IsOpenImmersion.isIso f
  have hm : IsClosed ({m.toPrimeSpectrum} : Set (PrimeSpectrum Γ(D, ⊤))) :=
    (PrimeSpectrum.isClosed_singleton_iff_isMaximal _).mpr m.isMaximal
  change IsClosed ({f m.toPrimeSpectrum} : Set D)
  simpa only [Set.image_singleton] using f.isClosedEmbedding.isClosedMap _ hm

variable {X : Scheme.{u}} (i : D ⟶ X) [IsClosedImmersion i]
def closedPoint (m : MaximalSpectrum Γ(D, ⊤)) : AlgebraicGeometry.Scheme.ClosedPoint X :=
  ⟨i (FiniteStalks.point k D q m), by
    simpa only [Set.image_singleton] using
      i.isClosedEmbedding.isClosedMap _ (point_isClosed k D q m)⟩

theorem closedPoint_injective : Function.Injective (closedPoint k D q i) := by
  intro a b h
  exact point_injective k D q (i.isClosedEmbedding.injective (congrArg Subtype.val h))
end CartierSum
namespace IdealDegree
universe u
variable {k : Type u} [Field k] (X D : Scheme.{u}) [IsIntegral X] [AlgebraicGeometry.IsNoetherian X]
variable [∀ x : AlgebraicGeometry.Scheme.ClosedPoint X, IsDiscreteValuationRing
    (X.presheaf.stalk x.val)]
variable (p : X ⟶ Spec (.of k)) [LocallyOfFiniteType p]
variable (i : D ⟶ X) [IsClosedImmersion i] [IsFinite (i ≫ p)]
variable (hI : Scheme.Modules.Invertible.IsLocallyRankOne X
    (idealModule i))
theorem ideal_mapDivisor_degree (U₀ : X.Opens) [Nonempty U₀]
    (e₀ : (idealModule i).over U₀ ≅ SheafOfModules.unit (X.ringCatSheaf.over U₀)) :
    Picard.Degree.degDiv X p (MapDivisors.mapDivisor X ⟨idealModule i, hI⟩ (idealInclusion i)
        U₀ e₀) =
      (Scheme.Hom.finiteSchemeDegree k (i ≫ p) : ℤ) := by
  classical
  let : Algebra k Γ(D, ⊤) := coordinateAlgebra k (Over.mk (i ≫ p))
  let : Module.Finite k Γ(D, ⊤) := finite_coordinate_algebra k D (i ≫ p)
  let : IsArtinianRing Γ(D, ⊤) := IsArtinianRing.of_finite k Γ(D, ⊤)
  let := Fintype.ofFinite (MaximalSpectrum Γ(D, ⊤))
  let z := MapDivisors.mapDivisor X ⟨idealModule i, hI⟩ (idealInclusion i) U₀ e₀
  let j := CartierSum.closedPoint k D (i ≫ p) i
  let T : Finset (AlgebraicGeometry.Scheme.ClosedPoint X) := Finset.univ.image j
  have hinj : Function.Injective j := CartierSum.closedPoint_injective k D (i ≫ p) i
  have hsub : z.support ⊆ T := by
    intro x hx
    have hr : x.val ∈ Set.range i := by
      by_contra h
      exact (Finsupp.mem_support_iff.mp hx)
        (CartierLocal.ideal_mapDivisor_eq_zero_of_not_mem_range X i hI U₀ e₀ x h)
    obtain ⟨y, hy⟩ := hr
    obtain ⟨m, hm⟩ := CartierSum.point_surjective k D (i ≫ p) y
    apply Finset.mem_image.mpr
    refine ⟨m, Finset.mem_univ _, ?_⟩
    apply Subtype.ext
    exact (congrArg (fun y => i y) hm).trans hy
  have hlocal (m : MaximalSpectrum Γ(D, ⊤)) :
      z (j m) * Picard.Degree.weight X p (j m) =
        (letI := stalkConstantsAlgebra D (i ≫ p) (FiniteStalks.point k D (i ≫ p) m)
         (Module.finrank k (D.presheaf.stalk (FiniteStalks.point k D (i ≫ p) m)) : ℤ)) := by
    let y := FiniteStalks.point k D (i ≫ p) m
    let c := localChart X (idealModule i) hI (i y)
    exact CartierLocal.ideal_mapDivisor_weighted_coefficient X i hI p U₀ e₀ c.1 c.2.val y
      c.2.property (j m).property
  calc
    Picard.Degree.degDiv X p z = ∑ x ∈ z.support, z x * Picard.Degree.weight X p x :=
      Picard.Degree.degDiv_apply X p z
    _ = ∑ x ∈ T, z x * Picard.Degree.weight X p x := by
      apply Finset.sum_subset hsub
      intro x _ hx
      have hz : z x = 0 := by simpa only [Finsupp.mem_support_iff, not_ne_iff] using hx
      rw [hz, zero_mul]
    _ = ∑ m : MaximalSpectrum Γ(D, ⊤), z (j m) * Picard.Degree.weight X p (j m) := by
      exact Finset.sum_image (fun a _ b _ hab => hinj hab)
    _ = ∑ m : MaximalSpectrum Γ(D, ⊤),
        (letI := stalkConstantsAlgebra D (i ≫ p) (FiniteStalks.point k D (i ≫ p) m)
         (Module.finrank k (D.presheaf.stalk (FiniteStalks.point k D (i ≫ p) m)) : ℤ)) :=
      Finset.sum_congr rfl (fun m _ => hlocal m)
    _ = (Scheme.Hom.finiteSchemeDegree k (i ≫ p) : ℤ) := by
      rw [FiniteStalks.degree_eq_sum_stalk_finrank]
      simp only [Nat.cast_sum]
end IdealDegree
universe u
/-- The unchanged full finite-Cartier ideal-dual degree family. -/
theorem finiteCartierIdealDegree :
    ∀ (K : Type u) [Field K] (X D : Scheme.{u}) [IsIntegral X] [IsNoetherian X]
      [∀ x : Scheme.ClosedPoint X, IsDiscreteValuationRing (X.presheaf.stalk x.val)]
      (p : X ⟶ Spec (.of K)) (i : D ⟶ X) (hdim : topologicalKrullDim X ≤ 1)
      (hprod : Picard.Degree.PrincipalProductFormula X p)
      (hI : IsLocallyRankOne X (idealModule i)),
      IsProper p → IsClosedImmersion i → IsFinite (i ≫ p) →
        Picard.Degree.lineBundleDegree X p hdim hprod
          (dualLineBundle X ⟨idealModule i, hI⟩) = (finiteSchemeDegree K (i ≫ p) : ℤ) := by
  intro k _ X D _ _ _ p i hdim hprod hI hp hi hf
  let := hp
  let := hi
  let := hf
  let c := localChart X (idealModule i) hI (genericPoint X)
  let : Nonempty c.1 := ⟨⟨genericPoint X, c.2.property⟩⟩
  exact (MapDivisors.degree_dual_eq_mapDivisor X ⟨idealModule i, hI⟩ (idealInclusion i)
    c.1 c.2.val p hdim hprod).trans
      (IdealDegree.ideal_mapDivisor_degree X D p i hI c.1 c.2.val)

end AlgebraicGeometry.Scheme.OverField.Curve.Abel.FiniteCartierDegree
