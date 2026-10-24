/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.Nagata.Finite
public import Mathlib.RingTheory.Trace.Basic
public import Mathlib.RingTheory.Discriminant
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.LinearAlgebra.Matrix.Adjugate
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.Algebra.Module.Submodule.Equiv
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.RingTheory.Localization.Module
public import Mathlib.RingTheory.Localization.Away.Basic

/-!
# A fixed field-trace lattice for a finite domain algebra

For a finite domain algebra with integrally closed base and compatible actual
fraction fields, a basis of the fraction-field extension can be chosen from
the original upper ring. The original field trace then takes integral values
in the base. Its Gram determinant and adjugate give two original linear maps
whose composites are multiplication by the same nonzero discriminant.

No freeness of the upper ring over the base, invertibility of the field degree,
Noetherianity, locality, dimension or residue-field separability is assumed.
The consumer is the fixed denominator in separable surface H1 boundedness.
-/

@[expose] public noncomputable section

open Module Matrix
open scoped BigOperators nonZeroDivisors

universe u

namespace Algebra.TraceLattice

variable (A B K L : Type u)
  [CommRing A] [IsDomain A] [CommRing B] [IsDomain B]
  [Algebra A B] [Module.Finite A B]
  [Field K] [Algebra A K] [IsFractionRing A K]
  [Field L] [Algebra B L] [IsFractionRing B L] [Algebra A L]
  [IsScalarTower A B L] [Algebra K L] [IsScalarTower A K L]

include A in
/-- The original image of the finite upper algebra contains a basis of its
fraction field over the original base fraction field. -/
theorem exists_fieldBasis :
    ∃ b : Basis (Fin (Module.finrank K L)) K L,
      ∀ i, b i ∈ Set.range (algebraMap B L) := by
  classical
  let : FiniteDimensional K L := IsFractionRing.finite_of_finite_algebra A B K L
  let : Algebra.IsAlgebraic A B :=
    ⟨fun b => (Algebra.IsIntegral.isIntegral (R := A) b).isAlgebraic⟩
  have hinj : Function.Injective (algebraMap A L) := by
    rw [IsScalarTower.algebraMap_eq A K L]
    exact (algebraMap K L).injective.comp (IsFractionRing.injective A K)
  have hspan : (Ideal.span ({1} : Set B) : Set B) ⊆
      (Submodule.span A (Set.univ : Set B) : Set B) := by
    rw [Submodule.span_univ]
    exact Set.subset_univ _
  have hfield := IsFractionRing.ideal_span_singleton_map_subset A
    (K := K) (L := L) (a := (1 : B)) (b := Set.univ) hinj hspan
  have hs : ⊤ ≤ Submodule.span K (Set.range (algebraMap B L)) := by
    intro x _
    change x ∈ (Submodule.span K (Set.range (algebraMap B L)) : Set L)
    simpa only [Set.image_univ] using hfield (show x ∈ Ideal.span {algebraMap B L 1} by simp)
  let e := Basis.ofSpan hs
  let ι := (linearIndepOn_empty K (fun x : L => x)).extend
    (Set.empty_subset (Set.range (algebraMap B L)))
  let : Fintype ι := FiniteDimensional.fintypeBasisIndex e
  let k : ι ≃ Fin (Module.finrank K L) :=
    Fintype.equivFinOfCardEq (Module.finrank_eq_card_basis e).symm
  refine ⟨e.reindex k, ?_⟩
  intro i
  rw [Basis.reindex_apply]
  exact Basis.ofSpan_subset hs (Set.mem_range_self (k.symm i))

/-- One fixed basis, chosen before any geometric model. -/
def fieldBasis : Basis (Fin (Module.finrank K L)) K L :=
  (exists_fieldBasis A B K L).choose

/-- The original upper-ring element representing each fixed basis vector. -/
def basisElement (i : Fin (Module.finrank K L)) : B :=
  ((exists_fieldBasis A B K L).choose_spec i).choose

/-- The basis vectors are the images of the original chosen elements of B. -/
theorem algebraMap_basisElement (i : Fin (Module.finrank K L)) :
    algebraMap B L (basisElement A B K L i) = fieldBasis A B K L i :=
  ((exists_fieldBasis A B K L).choose_spec i).choose_spec

variable [hClosed : IsIntegrallyClosed A]

/-- Restrict the actual field trace to the original finite upper algebra,
and descend its values through the injective original map A → K. -/
def fieldTrace : B →ₗ[A] A := by
  let : FiniteDimensional K L := IsFractionRing.finite_of_finite_algebra A B K L
  let i := Algebra.linearMap A K
  let t : B →ₗ[A] K :=
    ((Algebra.trace K L).restrictScalars A).comp (IsScalarTower.toAlgHom A B L).toLinearMap
  have ht (b : B) : t b ∈ LinearMap.range i := by
    exact IsIntegrallyClosed.algebraMap_eq_of_integral
      (Algebra.isIntegral_trace (R := A)
        ((Algebra.IsIntegral.isIntegral (R := A) b).map (IsScalarTower.toAlgHom A B L)))
  exact (LinearEquiv.ofInjective i (IsFractionRing.injective A K)).symm.toLinearMap.comp
    (t.codRestrict (LinearMap.range i) ht)

/-- The base-valued trace is the original field trace, with its original
embedding in K. This equation uniquely determines it. -/
theorem algebraMap_fieldTrace (b : B) :
    algebraMap A K (fieldTrace A B K L b) =
      Algebra.trace K L (algebraMap B L b) := by
  unfold fieldTrace
  exact LinearEquiv.ofInjective_symm_apply (σ₂₁ := RingHom.id A)
    (Algebra.linearMap A K) (h := IsFractionRing.injective A K) _

/-- Uniqueness is for the actual base-ring value, not a chosen field isomorphism. -/
theorem fieldTrace_unique (b : B) (a : A)
    (h : algebraMap A K a = Algebra.trace K L (algebraMap B L b)) :
    a = fieldTrace A B K L b :=
  IsFractionRing.injective A K (h.trans (algebraMap_fieldTrace A B K L b).symm)

/-- Coordinates given by pairing with the fixed original basis elements. -/
def coordinates : B →ₗ[A] (Fin (Module.finrank K L) → A) :=
  LinearMap.pi fun i =>
    (fieldTrace A B K L).comp (LinearMap.mulLeft A (basisElement A B K L i))

theorem coordinates_apply (b : B) (i : Fin (Module.finrank K L)) :
    coordinates A B K L b i = fieldTrace A B K L (basisElement A B K L i * b) := rfl

/-- The original base-valued field-trace Gram matrix. -/
def gramMatrix : Matrix (Fin (Module.finrank K L)) (Fin (Module.finrank K L)) A :=
  fun i j => fieldTrace A B K L (basisElement A B K L i * basisElement A B K L j)

/-- Extension to K recovers the trace form of the same original field basis. -/
theorem map_gramMatrix :
    (algebraMap A K).mapMatrix (gramMatrix A B K L) =
      (Algebra.traceForm K L).toMatrix (fieldBasis A B K L) := by
  ext i j
  rw [Algebra.traceForm_toMatrix]
  change algebraMap A K
      (fieldTrace A B K L (basisElement A B K L i * basisElement A B K L j)) = _
  rw [algebraMap_fieldTrace, map_mul, algebraMap_basisElement, algebraMap_basisElement]

/-- The fixed denominator is the determinant of the original A-valued matrix. -/
def discriminant : A := (gramMatrix A B K L).det

theorem algebraMap_discriminant :
    algebraMap A K (discriminant A B K L) =
      ((Algebra.traceForm K L).toMatrix (fieldBasis A B K L)).det :=
  ((algebraMap A K).map_det (gramMatrix A B K L)).trans
    (congrArg Matrix.det (map_gramMatrix A B K L))

/-- Expansion uses the original A-action on B and the original basis elements. -/
def expansion : (Fin (Module.finrank K L) → A) →ₗ[A] B where
  toFun v := ∑ i, v i • basisElement A B K L i
  map_add' v w := by simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' a v := by
    simp only [Pi.smul_apply, Finset.smul_sum, smul_eq_mul, smul_smul, RingHom.id_apply]

omit hClosed in
theorem expansion_apply (v : Fin (Module.finrank K L) → A) :
    expansion A B K L v = ∑ i, v i • basisElement A B K L i := rfl

/-- The two original maps have precisely the original Gram matrix as composite. -/
theorem coordinates_expansion (v : Fin (Module.finrank K L) → A) :
    coordinates A B K L (expansion A B K L v) = gramMatrix A B K L *ᵥ v := by
  funext i
  let l : B →ₗ[A] A := (LinearMap.proj i).comp (coordinates A B K L)
  change l (expansion A B K L v) = ∑ j, gramMatrix A B K L i j * v j
  rw [expansion_apply, map_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [map_smul]
  change v j * fieldTrace A B K L (basisElement A B K L i * basisElement A B K L j) =
    fieldTrace A B K L (basisElement A B K L i * basisElement A B K L j) * v j
  exact mul_comm _ _

/-- The original expansion after the adjugate matrix. -/
def adjugateExpansion : (Fin (Module.finrank K L) → A) →ₗ[A] B :=
  (expansion A B K L).comp (gramMatrix A B K L).adjugate.mulVecLin

/-- The first adjugate identity is valid before assuming separability. -/
theorem coordinates_adjugateExpansion (v : Fin (Module.finrank K L) → A) :
    coordinates A B K L (adjugateExpansion A B K L v) = discriminant A B K L • v := by
  change coordinates A B K L
    (expansion A B K L ((gramMatrix A B K L).adjugate *ᵥ v)) =
      (gramMatrix A B K L).det • v
  rw [coordinates_expansion, Matrix.mulVec_mulVec, Matrix.mul_adjugate,
    Matrix.smul_mulVec, Matrix.one_mulVec]

variable [hSeparable : Algebra.IsSeparable K L]

include hSeparable in
/-- Finite separability makes this fixed original denominator nonzero. -/
theorem discriminant_ne_zero : discriminant A B K L ≠ 0 := by
  intro hd
  apply _root_.det_traceForm_ne_zero (fieldBasis A B K L)
  rw [← algebraMap_discriminant A B K L, hd, map_zero]

include hSeparable in
/-- The original trace-coordinate map is injective by the original field pairing. -/
theorem coordinates_injective : Function.Injective (coordinates A B K L) := by
  let : FiniteDimensional K L := IsFractionRing.finite_of_finite_algebra A B K L
  apply (injective_iff_map_eq_zero (coordinates A B K L)).mpr
  intro b hb
  have hform : Algebra.traceForm K L (algebraMap B L b) = 0 := by
    apply (fieldBasis A B K L).ext
    intro i
    have hi := congrArg (algebraMap A K) (congrFun hb i)
    change algebraMap A K
      (fieldTrace A B K L (basisElement A B K L i * b)) = algebraMap A K 0 at hi
    rw [algebraMap_fieldTrace, map_mul, algebraMap_basisElement, map_zero] at hi
    change Algebra.trace K L (algebraMap B L b * fieldBasis A B K L i) = 0
    simpa only [mul_comm] using hi
  apply IsFractionRing.injective B L
  rw [map_zero]
  exact (_root_.traceForm_nondegenerate K L).1 _
    (fun y => DFunLike.congr_fun hform y)

include hSeparable in
/-- The second adjugate identity follows by cancellation of the original
injective trace-coordinate map. -/
theorem adjugateExpansion_coordinates (b : B) :
    adjugateExpansion A B K L (coordinates A B K L b) = discriminant A B K L • b := by
  apply coordinates_injective A B K L
  exact (coordinates_adjugateExpansion A B K L _).trans
    ((coordinates A B K L).map_smul (discriminant A B K L) b).symm

omit hSeparable in
/-- The original first composite as an equality of A-linear maps. -/
theorem coordinates_comp_adjugateExpansion :
    (coordinates A B K L).comp (adjugateExpansion A B K L) =
      discriminant A B K L • LinearMap.id := by
  exact LinearMap.ext (fun v => coordinates_adjugateExpansion A B K L v)

include hSeparable in
/-- The original second composite as an equality of A-linear maps. -/
theorem adjugateExpansion_comp_coordinates :
    (adjugateExpansion A B K L).comp (coordinates A B K L) =
      discriminant A B K L • LinearMap.id := by
  exact LinearMap.ext (fun b => adjugateExpansion_coordinates A B K L b)

include hSeparable in
/-- Multiplication by the same fixed discriminant places every original
element in the original A-span of the fixed basis elements. -/
theorem discriminant_smul_mem_range_expansion (b : B) :
    discriminant A B K L • b ∈ LinearMap.range (expansion A B K L) :=
  ⟨(gramMatrix A B K L).adjugate *ᵥ coordinates A B K L b,
    adjugateExpansion_coordinates A B K L b⟩

omit hClosed hSeparable in
/-- The fixed upper-ring elements are already linearly independent over A. -/
theorem basisElement_linearIndependent : LinearIndependent A (basisElement A B K L) := by
  have hK : LinearIndependent K (fun i => algebraMap B L (basisElement A B K L i)) := by
    simpa only [algebraMap_basisElement] using (fieldBasis A B K L).linearIndependent
  exact LinearIndependent.of_comp (IsScalarTower.toAlgHom A B L).toLinearMap
    (hK.restrict_scalars' A)

section Localization

variable (S D : Type u) [CommRing S] [CommRing D]
  [Algebra A S] [hLocalS : IsLocalization.Away (discriminant A B K L) S]
  [Algebra B D] [hLocalD : IsLocalization.Away (algebraMap A B (discriminant A B K L)) D]
  [Algebra A D] [IsScalarTower A B D] [Algebra S D] [IsScalarTower A S D]

include hClosed hSeparable hLocalS hLocalD in
/-- The original basis elements span after localizing at the same fixed
discriminant. The localizations and all scalar maps are the supplied ones. -/
theorem localized_span_eq_top :
    Submodule.span S (Set.range (fun i => algebraMap B D (basisElement A B K L i))) = ⊤ := by
  classical
  let d := discriminant A B K L
  let f : B →ₗ[A] D := (IsScalarTower.toAlgHom A B D).toLinearMap
  let T : Submodule S D :=
    Submodule.span S (Set.range (fun i => algebraMap B D (basisElement A B K L i)))
  have hmem (b : B) : f (discriminant A B K L • b) ∈ T := by
    obtain ⟨v, hv⟩ := discriminant_smul_mem_range_expansion A B K L b
    rw [← hv, expansion_apply, map_sum]
    apply T.sum_mem
    intro i _
    rw [map_smul, ← algebraMap_smul S]
    exact T.smul_mem _ (Submodule.subset_span (Set.mem_range_self i))
  apply top_unique
  intro x _
  obtain ⟨⟨b, s⟩, hs⟩ := IsLocalizedModule.surj (Submonoid.powers d) f x
  change (s : A) • x = f b at hs
  have hds : (d * (s : A)) • x ∈ T := by
    rw [mul_smul, hs, ← f.map_smul]
    exact hmem b
  have hu : IsUnit (algebraMap A S (d * (s : A))) :=
    IsLocalization.map_units S ⟨d * (s : A),
      (Submonoid.powers d).mul_mem ⟨1, pow_one d⟩ s.property⟩
  apply (T.smul_mem_iff_of_isUnit hu).mp
  rw [algebraMap_smul]
  exact hds

/-- A basis of the actual localized upper ring over the actual localized
base ring, using the images of the same original chosen elements. -/
def localizedBasis : Basis (Fin (Module.finrank K L)) S D :=
  Basis.mk
    ((basisElement_linearIndependent A B K L).localization_localization
      S (Submonoid.powers (discriminant A B K L)) D)
    (by
      have hs : Submodule.span S
          (Set.range (algebraMap B D ∘ basisElement A B K L)) = ⊤ :=
        localized_span_eq_top A B K L S D
      exact hs.ge)

theorem localizedBasis_apply (i : Fin (Module.finrank K L)) :
    localizedBasis A B K L S D i = algebraMap B D (basisElement A B K L i) :=
  Basis.mk_apply _ _ i

include A B K L hClosed hSeparable hLocalS hLocalD in
/-- Localizing at the fixed discriminant makes the original upper algebra
finite free over the localized base, with rank the original field degree. -/
theorem localized_finite_free : Module.Finite S D ∧ Module.Free S D :=
  ⟨Module.Finite.of_basis (localizedBasis A B K L S D),
    Module.Free.of_basis (localizedBasis A B K L S D)⟩

end Localization

/-- The concrete principal localizations, with the native original
localization algebra map, have the same fixed basis. -/
def awayBasis :
    let d := discriminant A B K L
    let S := Localization.Away d
    let D := Localization.Away (algebraMap A B d)
    letI : Algebra S D := _root_.localizationAlgebra (Submonoid.powers d) B
    Basis (Fin (Module.finrank K L)) S D := by
  let d := discriminant A B K L
  let S := Localization.Away d
  let D := Localization.Away (algebraMap A B d)
  let : Algebra S D := _root_.localizationAlgebra (Submonoid.powers d) B
  let : IsScalarTower A S D :=
    _root_.isScalarTower_localizationAlgebra (Submonoid.powers d) B
  exact localizedBasis A B K L S D

/-- The basis of the concrete principal localization retains the original
upper-ring elements under the original localization map. -/
theorem awayBasis_apply (i : Fin (Module.finrank K L)) :
    awayBasis A B K L i =
      algebraMap B (Localization.Away (algebraMap A B (discriminant A B K L)))
        (basisElement A B K L i) := by
  let d := discriminant A B K L
  let S := Localization.Away d
  let D := Localization.Away (algebraMap A B d)
  let : Algebra S D := _root_.localizationAlgebra (Submonoid.powers d) B
  let : IsScalarTower A S D :=
    _root_.isScalarTower_localizationAlgebra (Submonoid.powers d) B
  exact localizedBasis_apply A B K L S D i

end Algebra.TraceLattice
