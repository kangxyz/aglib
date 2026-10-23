/-
Copyright (c) 2026 Algebraic geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.LocallyFree.Pullback
public import Aglib.AlgebraicGeometry.Modules.LocallyFree.Exact
public import Aglib.AlgebraicGeometry.Modules.LocallyFree.Rank
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Extensions.AffineSections
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Additivity of fibre ranks in short exact sequences

Let `0 → K → M → N → 0` be a short exact sequence of module sheaves on a scheme with `K` and `N`
finite locally free (so `M` is finite locally free). At every field-valued point `p`, the fibre
dimensions satisfy `dim M(p) = dim K(p) + dim N(p)`
(`finrank_moduleFibre_X₂_eq_add_of_shortExact`): the pulled back sequence on the spectrum of the
field is short exact (`shortExact_pullback`, from local splitting) and global sections are exact
on it. Hence `sheafRank M x = sheafRank K x + sheafRank N x` at every point
(`sheafRank_X₂_eq_add_of_shortExact`). A finite free sheaf has fibre rank the number of generators
(`finrank_moduleFibre_free`, `sheafRank_free`).

Source: the text of Stacks, Tag 0B37 (section "Rank and determinant"), states without proof that
ranks add along short exact sequences of finite locally free modules (checked 2026-10-19).
Encoded subset: module sheaves on an arbitrary scheme; the first and last terms finite locally
free; fibre ranks at residue fields (`sheafRank`) and at arbitrary field-valued points.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme.Modules

/-- The fibre of a finite free sheaf at a field-valued point has dimension the number of
generators. -/
theorem finrank_moduleFibre_free {Y : Scheme.{u}} (K : Type u) [Field K]
    (p : Spec (CommRingCat.of K) ⟶ Y) (I : Type u) [Finite I] :
    Module.finrank K (moduleFibre K (SheafOfModules.free (R := Y.ringCatSheaf) I) p) =
      Nat.card I := by
  let _ : Fintype I := Fintype.ofFinite I
  let e : moduleFibre K (SheafOfModules.free (R := Y.ringCatSheaf) I) p ≃ₗ[K] (I → K) :=
    (fieldSectionsIso K (pullbackFreeIso p I)).trans (fieldSectionsFreeEquiv K I)
  rw [e.finrank_eq, Module.finrank_pi, Nat.card_eq_fintype_card]

/-- The fibre rank of a finite free sheaf is the number of generators. -/
theorem sheafRank_free {Y : Scheme.{u}} (I : Type u) [Finite I] (y : Y) :
    sheafRank (SheafOfModules.free (R := Y.ringCatSheaf) I) y = Nat.card I :=
  finrank_moduleFibre_free (Y.residueField y) (Y.fromSpecResidueField y) I

/-- Fibre dimensions are additive along a short exact sequence `0 → K → M → N → 0` of module
sheaves with `K` and `N` finite locally free, at every field-valued point. -/
theorem finrank_moduleFibre_X₂_eq_add_of_shortExact {X : Scheme.{u}} {S : ShortComplex X.Modules}
    (hS : S.ShortExact) [IsFiniteLocallyFree X S.X₁] [IsFiniteLocallyFree X S.X₃]
    (K : Type u) [Field K] (p : Spec (CommRingCat.of K) ⟶ X) :
    Module.finrank K (moduleFibre K S.X₂ p) =
      Module.finrank K (moduleFibre K S.X₁ p) + Module.finrank K (moduleFibre K S.X₃ p) := by
  have : IsFiniteLocallyFree X S.X₂ := finiteLocallyFree_of_shortExact hS
  have hSp := shortExact_pullback p hS
  have : IsFiniteLocallyFree (Spec (CommRingCat.of K)) (S.map (pullback p)).X₁ :=
    finiteLocallyFree_pullback p S.X₁
  have hΓ := AffineCech.shortExact_globalSections_of_quasicoherent_kernel hSp
  let a : moduleFibre K S.X₁ p →ₗ[K] moduleFibre K S.X₂ p :=
    fieldSectionsMap K ((pullback p).map S.f)
  let b : moduleFibre K S.X₂ p →ₗ[K] moduleFibre K S.X₃ p :=
    fieldSectionsMap K ((pullback p).map S.g)
  have ha' : Function.Injective (moduleSpecΓFunctor.map ((pullback p).map S.f)) :=
    (ModuleCat.mono_iff_injective _).mp hΓ.mono_f
  have ha : Function.Injective a := ha'
  have hb : Function.Surjective b := hΓ.moduleCat_surjective_g
  have hba : ∀ y, b (a y) = 0 := fun y ↦ by
    have h : (pullback p).map S.f ≫ (pullback p).map S.g = 0 := by
      rw [← CategoryTheory.Functor.map_comp, S.zero, CategoryTheory.Functor.map_zero]
    change ((((pullback p).map S.f ≫ (pullback p).map S.g).val.app (Opposite.op ⊤)).hom y) = 0
    rw [h]
    rfl
  have hab : LinearMap.range a = LinearMap.ker b := by
    ext z
    refine ⟨?_, fun hz ↦ ?_⟩
    · rintro ⟨y, rfl⟩
      exact hba y
    · obtain ⟨y, hy⟩ := (ShortComplex.moduleCat_exact_iff _).mp hΓ.exact z hz
      exact ⟨y, hy⟩
  have : FiniteDimensional K (moduleFibre K S.X₂ p) := moduleFibre_finite S.X₂ K p
  rw [← LinearMap.finrank_range_add_finrank_ker b, LinearMap.range_eq_top.mpr hb, finrank_top,
    ← hab, LinearMap.finrank_range_of_inj ha, add_comm]

/-- **Fibre ranks are additive** along a short exact sequence `0 → K → M → N → 0` of module
sheaves with `K` and `N` finite locally free: at every point, the rank of `M` is the sum of the
ranks of `K` and `N`. -/
theorem sheafRank_X₂_eq_add_of_shortExact {X : Scheme.{u}} {S : ShortComplex X.Modules}
    (hS : S.ShortExact) [IsFiniteLocallyFree X S.X₁] [IsFiniteLocallyFree X S.X₃] (x : X) :
    sheafRank S.X₂ x = sheafRank S.X₁ x + sheafRank S.X₃ x :=
  finrank_moduleFibre_X₂_eq_add_of_shortExact hS (X.residueField x) (X.fromSpecResidueField x)

end AlgebraicGeometry.Scheme.Modules
