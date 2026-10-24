/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.Nagata.Finite
public import Mathlib.Algebra.Module.LocalizedModule.Int
public import Mathlib.Algebra.Module.Submodule.Equiv
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.LinearAlgebra.Dimension.Free
public import Mathlib.LinearAlgebra.Dimension.Localization
public import Mathlib.LinearAlgebra.Pi
public import Mathlib.RingTheory.Localization.Module

/-!
# Clearing the coordinates of a finite module inside its generic vector space

No freeness of the finite module is assumed. A common nonzero denominator
places its entire image in the free module of the original generic rank.
-/

@[expose] public noncomputable section

open scoped nonZeroDivisors

namespace IsFractionRing

universe u v

variable (R F : Type u) [CommRing R] [IsDomain R]
  [Field F] [Algebra R F] [IsFractionRing R F]

private def coordinateInclusion (ι : Type v) :
    (ι → R) →ₗ[R] (ι → F) :=
  (Algebra.linearMap R F).compLeft ι

omit [IsDomain R] in
private theorem coordinateInclusion_injective (ι : Type v) :
    Function.Injective (coordinateInclusion R F ι) := by
  intro x y h
  funext i
  exact IsFractionRing.injective R F (congrFun h i)

/-- One original denominator clears every coordinate of the entire finite module.
The conclusion records the actual coordinate equation, not just an embedding. -/
theorem exists_cleared_coordinate_embedding
    {M : Type u} {ι : Type v} [AddCommGroup M] [Module R M] [Module.Finite R M]
    [Finite ι] (f : M →ₗ[R] (ι → F)) (hf : Function.Injective f) :
    ∃ (c : R⁰) (g : M →ₗ[R] (ι → R)), Function.Injective g ∧
      ∀ x i, algebraMap R F (g x i) = (c : R) • f x i := by
  classical
  obtain ⟨n, s, hs⟩ := Module.Finite.exists_fin (R := R) (M := M)
  obtain ⟨c, hc⟩ := IsLocalizedModule.exist_integer_multiples_of_finite R⁰
    (Algebra.linearMap R F) (fun a : Fin n × ι => f (s a.1) a.2)
  let j := coordinateInclusion R F ι
  let t : M →ₗ[R] (ι → F) := (c : R) • f
  have hgen : Submodule.span R (Set.range s) ≤ (LinearMap.range j).comap t := by
    apply Submodule.span_le.mpr
    rintro _ ⟨a, rfl⟩
    have hcoord (i : ι) : ∃ v : R,
        algebraMap R F v = (c : R) • f (s a) i := hc (a, i)
    choose v hv using hcoord
    exact ⟨v, funext hv⟩
  have ht (x : M) : t x ∈ LinearMap.range j := by
    apply hgen
    rw [hs]
    trivial
  let e := LinearEquiv.ofInjective j (coordinateInclusion_injective R F ι)
  let g : M →ₗ[R] (ι → R) := e.symm.toLinearMap.comp (t.codRestrict _ ht)
  have hg (x : M) : j (g x) = t x := by
    exact LinearEquiv.ofInjective_symm_apply (σ₂₁ := RingHom.id R)
      j (h := coordinateInclusion_injective R F ι) _
  have hcF : algebraMap R F (c : R) ≠ 0 := by
    intro h
    exact nonZeroDivisors.ne_zero c.property
      ((IsFractionRing.injective R F) (h.trans (map_zero _).symm))
  refine ⟨c, g, ?_, ?_⟩
  · intro x y h
    apply hf
    funext i
    have heq := congrArg (fun z => j z i) h
    rw [congrFun (hg x) i, congrFun (hg y) i] at heq
    have hmul : algebraMap R F (c : R) * f x i =
        algebraMap R F (c : R) * f y i := by
      simpa only [t, LinearMap.smul_apply, Pi.smul_apply, Algebra.smul_def] using heq
    exact mul_left_cancel₀ hcF hmul
  · intro x i
    exact congrFun (hg x) i

/-- The whole finite domain algebra embeds in a free module whose rank is the
degree of its actual fraction-field extension. No separability is required. -/
theorem exists_finite_rank_embedding
    (S E : Type u) [CommRing S] [IsDomain S]
    [Algebra R S] [Module.Finite R S]
    [Field E] [Algebra S E] [IsFractionRing S E] [Algebra R E]
    [IsScalarTower R S E] [Algebra F E] [IsScalarTower R F E] :
    ∃ g : S →ₗ[R] (Fin (Module.finrank F E) → R), Function.Injective g := by
  let : FiniteDimensional F E := IsFractionRing.finite_of_finite_algebra R S F E
  let b := Module.finBasis F E
  let f : S →ₗ[R] (Fin (Module.finrank F E) → F) :=
    (b.equivFun.toLinearMap.restrictScalars R).comp
      (IsScalarTower.toAlgHom R S E).toLinearMap
  have hf : Function.Injective f :=
    b.equivFun.injective.comp (IsFractionRing.injective S E)
  obtain ⟨_, g, hg, _⟩ := exists_cleared_coordinate_embedding R F
    (M := S) (ι := Fin (Module.finrank F E)) (f := f) (hf := hf)
  exact ⟨g, hg⟩

end IsFractionRing
