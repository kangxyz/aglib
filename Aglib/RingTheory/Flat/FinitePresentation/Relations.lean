/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.Flat.LocalCriterion.Tensor
public import Aglib.RingTheory.Flat.LocalCriterion.ResidueSyzygies
public import Mathlib.RingTheory.TensorProduct.DirectLimitFG
public import Mathlib.RingTheory.TensorProduct.Maps

/-!
# Finite obstruction and relation descent, residue injections and actual extended ideals

## Extraction basis

Transferred from `R5Lab/AlgebraicGeometry/Curves/RelativeDivisors/FibrewiseRegularity.lean`
at frozen dirty R5Lab revision `79307ff88f07d34fd5c3edb859f799c55e38f290`, SHA-256
`79621aa63046ca16c5f98424d77f16bc8cd45b99a84ddc8bc561fc8f9ccfe923`.
Source line ranges: 1220–1320, 1367–1367, 1375–1425, 1433–1492, 1658–1713, 1721–1814, 1822–1846.
The original rings, modules, canonical maps, universes and hypotheses are retained.
-/

@[expose] public section

noncomputable section
open TensorProduct LinearMap

namespace Algebra.FlatApproximation

section FiniteStage
variable {A R M : Type*} [CommRing A] [CommRing R] [Algebra A R]
  [AddCommGroup M] [Module A M]

/-- Finitely many vanishing tensors can be killed in one finitely generated
intermediate base algebra, retaining a prescribed finitely generated stage. -/
theorem exists_fg_killing_finset (C : Subalgebra A R) (hC : C.FG)
    (s : Finset (C ⊗[A] M))
    (hs : ∀ t ∈ s, C.val.toLinearMap.rTensor M t = 0) :
    ∃ (D : Subalgebra A R) (hCD : C ≤ D), D.FG ∧
      ∀ t ∈ s, (Subalgebra.inclusion hCD).toLinearMap.rTensor M t = 0 := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨C, le_rfl, hC, by simp⟩
  | @insert t s ht ih =>
      obtain ⟨D, hCD, hD, hsD⟩ := ih (fun x hx ↦ hs x (Finset.mem_insert_of_mem hx))
      have ht0 : C.val.toLinearMap.rTensor M t =
          C.val.toLinearMap.rTensor M 0 := by simpa using hs t (Finset.mem_insert_self _ _)
      obtain ⟨E, hCE, hE, htE⟩ := TensorProduct.Algebra.eq_of_fg_of_subtype_eq hC ht0
      refine ⟨D ⊔ E, hCD.trans le_sup_left, hD.sup hE, ?_⟩
      intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hx
      · have hc : (Subalgebra.inclusion (hCD.trans le_sup_left)).toLinearMap =
            (Subalgebra.inclusion (le_sup_right : E ≤ D ⊔ E)).toLinearMap.comp
              (Subalgebra.inclusion hCE).toLinearMap := by ext; rfl
        rw [hc, LinearMap.rTensor_comp, LinearMap.comp_apply, htE, map_zero, map_zero]
      · have hc : (Subalgebra.inclusion (hCD.trans le_sup_left)).toLinearMap =
            (Subalgebra.inclusion (le_sup_left : D ≤ D ⊔ E)).toLinearMap.comp
              (Subalgebra.inclusion hCD).toLinearMap := by ext; rfl
        rw [hc, LinearMap.rTensor_comp, LinearMap.comp_apply, hsD x hx, map_zero]

/-- A finite list of module elements becoming zero after base change becomes
zero over a single finite-type intermediate algebra. -/
theorem exists_fg_killing_elements (s : Finset M)
    (hs : ∀ m ∈ s, (1 : R) ⊗ₜ[A] m = 0) :
    ∃ (C : Subalgebra A R), C.FG ∧ ∀ m ∈ s, (1 : C) ⊗ₜ[A] m = 0 := by
  classical
  let C : Subalgebra A R := ⊥
  let j : M → C ⊗[A] M := fun m ↦ (1 : C) ⊗ₜ[A] m
  have hzero : ∀ t ∈ s.image j, C.val.toLinearMap.rTensor M t = 0 := by
    intro t ht
    obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp ht
    simpa [j] using hs m hm
  obtain ⟨D, hCD, hD, hDzero⟩ := exists_fg_killing_finset C Subalgebra.fg_bot (s.image j) hzero
  refine ⟨D, hD, ?_⟩
  intro m hm
  simpa [j] using hDzero (j m) (Finset.mem_image.mpr ⟨m, hm, rfl⟩)

variable {N Q : Type*} [AddCommGroup N] [Module A N] [AddCommGroup Q] [Module A Q]

/-- A solution of a homogeneous linear equation with a prescribed image can
be realized over a finite-type intermediate base. This records both equations,
which is the finite witness needed to descend a lift of a residue relation. -/
theorem exists_fg_solution (f : M →ₗ[A] N) (g : M →ₗ[A] Q) (x : Q)
    (u : R ⊗[A] M) (hfu : f.baseChange R u = 0)
    (hgu : g.baseChange R u = (1 : R) ⊗ₜ[A] x) :
    ∃ (C : Subalgebra A R), C.FG ∧ ∃ (v : C ⊗[A] M),
      f.baseChange C v = 0 ∧ g.baseChange C v = (1 : C) ⊗ₜ[A] x := by
  obtain ⟨C, hC, v, hfv, hv⟩ := Submodule.exists_fg_of_baseChange_eq_zero f hfu
  have hgv : C.val.toLinearMap.rTensor Q (g.baseChange C v) =
      C.val.toLinearMap.rTensor Q ((1 : C) ⊗ₜ[A] x) := by
    rw [LinearMap.rTensor_baseChange, hv, hgu]
    simp
  obtain ⟨D, hCD, hD, hvD⟩ := TensorProduct.Algebra.eq_of_fg_of_subtype_eq hC hgv
  refine ⟨D, hD, (Subalgebra.inclusion hCD).toLinearMap.rTensor M v, ?_, ?_⟩
  · rw [← LinearMap.rTensor_baseChange, hfv, map_zero]
  · rw [← LinearMap.rTensor_baseChange, hvD]
    simp

/-- Finitely many compatible linear lifting problems admit solutions over one
finite-type intermediate algebra. -/
theorem exists_fg_solutions (f : M →ₗ[A] N) (g : M →ₗ[A] Q) (s : Finset Q)
    (hs : ∀ x ∈ s, ∃ u : R ⊗[A] M,
      f.baseChange R u = 0 ∧ g.baseChange R u = (1 : R) ⊗ₜ[A] x) :
    ∃ (C : Subalgebra A R), C.FG ∧ ∀ x ∈ s, ∃ v : C ⊗[A] M,
      f.baseChange C v = 0 ∧ g.baseChange C v = (1 : C) ⊗ₜ[A] x := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨⊥, Subalgebra.fg_bot, by simp⟩
  | @insert x s hx ih =>
      obtain ⟨D, hD, hsD⟩ := ih (fun y hy ↦ hs y (Finset.mem_insert_of_mem hy))
      obtain ⟨u, hfu, hgu⟩ := hs x (Finset.mem_insert_self _ _)
      obtain ⟨E, hE, v, hfv, hgv⟩ := exists_fg_solution f g x u hfu hgu
      refine ⟨D ⊔ E, hD.sup hE, ?_⟩
      intro y hy
      rcases Finset.mem_insert.mp hy with rfl | hy
      · let j := Subalgebra.inclusion (le_sup_right : E ≤ D ⊔ E)
        refine ⟨j.toLinearMap.rTensor M v, ?_, ?_⟩
        · rw [← LinearMap.rTensor_baseChange, hfv, map_zero]
        · rw [← LinearMap.rTensor_baseChange, hgv]
          simp
      · obtain ⟨v, hfv, hgv⟩ := hsD y hy
        let j := Subalgebra.inclusion (le_sup_left : D ≤ D ⊔ E)
        refine ⟨j.toLinearMap.rTensor M v, ?_, ?_⟩
        · rw [← LinearMap.rTensor_baseChange, hfv, map_zero]
        · rw [← LinearMap.rTensor_baseChange, hgv]
          simp

end FiniteStage


end Algebra.FlatApproximation

namespace Algebra.FlatApproximation

variable {R M N P : Type*} [CommRing R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  [AddCommGroup P] [Module R P]

/-- If a presentation has flat cokernel, every relation modulo an ideal lifts
to an actual relation. This is a Tor-free form of the relation-lifting step
used in local finite-stage flatness descent. -/
theorem exists_relation_lift_of_flat_cokernel_of_surjective [Module.Flat R P]
    (T : Type*) [CommRing T] [Algebra R T] (hT : Function.Surjective (algebraMap R T))
    (f : M →ₗ[R] N) (g : N →ₗ[R] P) (hex : Function.Exact f g)
    (hg : Function.Surjective g) (x : T ⊗[R] M)
    (hx : f.lTensor T x = 0) :
    ∃ m : M, f m = 0 ∧ (1 : T) ⊗ₜ[R] m = x := by
  have hex' : Function.Exact (LinearMap.range f).subtype g := by
    rw [LinearMap.exact_iff, Submodule.range_subtype]
    exact LinearMap.exact_iff.mp hex
  have hi : Function.Injective ((LinearMap.range f).subtype.lTensor T) :=
    LinearMap.lTensor_injective_of_exact_of_flat g hg _ (Submodule.injective_subtype _) hex' _
  have hx' : f.rangeRestrict.lTensor T x = 0 := by
    apply hi
    rw [map_zero]
    have hf : (LinearMap.range f).subtype.comp f.rangeRestrict = f := rfl
    simpa only [← LinearMap.comp_apply, ← LinearMap.lTensor_comp, hf] using hx
  have hexf : Function.Exact (LinearMap.ker f).subtype f.rangeRestrict := by
    intro y
    constructor
    · intro hy
      refine ⟨⟨y, ?_⟩, rfl⟩
      exact congrArg Subtype.val hy
    · rintro ⟨z, rfl⟩
      apply Subtype.ext
      exact z.property
  obtain ⟨z, hz⟩ := (_root_.lTensor_exact T hexf
    (LinearMap.surjective_rangeRestrict f) x).mp hx'
  obtain ⟨m, hm'⟩ := TensorProduct.mk_surjective (R := R) (S := T) (M := LinearMap.ker f) hT z
  refine ⟨m, m.property, ?_⟩
  rw [← hz, ← hm']
  rfl

/-- Specialization to quotienting the base by an ideal. -/
theorem exists_relation_lift_of_flat_cokernel [Module.Flat R P]
    (f : M →ₗ[R] N) (g : N →ₗ[R] P) (hex : Function.Exact f g)
    (hg : Function.Surjective g) (I : Ideal R) (x : (R ⧸ I) ⊗[R] M)
    (hx : f.lTensor (R ⧸ I) x = 0) :
    ∃ m : M, f m = 0 ∧ (1 : R ⧸ I) ⊗ₜ[R] m = x :=
  exists_relation_lift_of_flat_cokernel_of_surjective (R ⧸ I)
    Ideal.Quotient.mk_surjective f g hex hg x hx

end Algebra.FlatApproximation

namespace Algebra.FlatApproximation

variable {A R K M N P : Type*} [CommRing A] [CommRing R] [CommRing K]
  [Algebra A R] [Algebra A K]
  [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N]
  [AddCommGroup P] [Module R P]

/-- A residue relation in an initial presentation admits an actual relation
lift over the limiting flat-cokernel algebra. The residue algebra need only be
a quotient of the initial base. -/
theorem exists_relation_solution_of_flat_baseChange_cokernel [Module.Flat R P]
    (hK : Function.Surjective (algebraMap A K))
    (f : M →ₗ[A] N) (g : R ⊗[A] N →ₗ[R] P)
    (hex : Function.Exact (f.baseChange R) g) (hg : Function.Surjective g)
    (x : K ⊗[A] M) (hx : f.lTensor K x = 0) :
    ∃ u : R ⊗[A] M, f.baseChange R u = 0 ∧
      (TensorProduct.mk A K M 1).baseChange R u = (1 : R) ⊗ₜ[A] x := by
  let H := R ⊗[A] K
  let eM := AlgebraTensorModule.distribBaseChange A R K M
  let eN := AlgebraTensorModule.distribBaseChange A R K N
  have hH : Function.Surjective (algebraMap R H) :=
    Algebra.TensorProduct.includeLeft_surjective R R hK
  have hc : ((f.baseChange R).lTensor H).comp eM.toLinearMap =
      eN.toLinearMap.comp ((f.lTensor K).baseChange R) := by
    apply AlgebraTensorModule.ext
    intro r y
    induction y with
    | tmul k m => rfl
    | add y z hy hz => simp only [tmul_add, map_add, hy, hz]
  have ht : (f.baseChange R).lTensor H (eM ((1 : R) ⊗ₜ[A] x)) = 0 := by
    have h := LinearMap.congr_fun hc ((1 : R) ⊗ₜ[A] x)
    simpa [hx] using h
  obtain ⟨u, hfu, hu⟩ := exists_relation_lift_of_flat_cokernel_of_surjective H hH
    (f.baseChange R) g hex hg (eM ((1 : R) ⊗ₜ[A] x)) ht
  refine ⟨u, hfu, ?_⟩
  have he : eM.symm ((1 : H) ⊗ₜ[R] u) =
      (TensorProduct.mk A K M 1).baseChange R u := by
    clear hfu hu
    induction u with
    | tmul r m => simp [eM, H, Algebra.TensorProduct.one_def]
    | add u v hu hv => simp only [tmul_add, map_add, hu, hv]
  have h := congrArg eM.symm hu
  rwa [he, eM.symm_apply_apply] at h

/-- Finitely many residue relations of a presentation with flat limiting
cokernel lift to actual relations over one finite-type intermediate base.
This is the finite-witness core of local flatness approximation. -/
theorem exists_fg_residue_relation_lifts [Module.Flat R P]
    (hK : Function.Surjective (algebraMap A K))
    (f : M →ₗ[A] N) (g : R ⊗[A] N →ₗ[R] P)
    (hex : Function.Exact (f.baseChange R) g) (hg : Function.Surjective g)
    (s : Finset (K ⊗[A] M)) (hs : ∀ x ∈ s, f.lTensor K x = 0) :
    ∃ (C : Subalgebra A R), C.FG ∧ ∀ x ∈ s, ∃ v : C ⊗[A] M,
      f.baseChange C v = 0 ∧
      (TensorProduct.mk A K M 1).baseChange C v = (1 : C) ⊗ₜ[A] x := by
  apply exists_fg_solutions f (TensorProduct.mk A K M 1) s
  intro x hx
  exact exists_relation_solution_of_flat_baseChange_cokernel hK f g hex hg x (hs x hx)

end Algebra.FlatApproximation

namespace Algebra.FlatApproximation

universe uA uR uB uK uM uN uP
variable {A : Type uA} {R : Type uR} {B : Type uB} {K : Type uK}
  {M : Type uM} {N : Type uN} {P : Type uP}
  [CommRing A] [CommRing R] [CommRing B] [CommRing K]
  [Algebra A R] [Algebra A B] [Algebra A K]
  [AddCommGroup M] [Module A M] [Module B M] [IsScalarTower A B M]
  [AddCommGroup N] [Module A N] [Module B N] [IsScalarTower A B N]
  [AddCommGroup P] [Module R P]

/-- Noetherianity makes all old residue relations descend at one finite-type
stage. The limiting cokernel is flat, but no flatness is assumed at that stage.
This is the algebraic finite-stage obstruction-killing core of local flatness
approximation. -/
theorem exists_fg_universal_residue_relation_lifts
    [IsNoetherianRing B] [Module.Finite B M] [Module.Flat R P]
    (hK : Function.Surjective (algebraMap A K))
    (f : M →ₗ[B] N) (g : R ⊗[A] N →ₗ[R] P)
    (hex : Function.Exact ((f.restrictScalars A).baseChange R) g)
    (hg : Function.Surjective g) :
    ∃ (C : Subalgebra A R), C.FG ∧
      ∀ x : K ⊗[A] M, (f.restrictScalars A).lTensor K x = 0 →
        ∃ v : C ⊗[A] M, (f.restrictScalars A).baseChange C v = 0 ∧
          (TensorProduct.mk A K M 1).baseChange C v = (1 : C) ⊗ₜ[A] x := by
  classical
  obtain ⟨n, xs, hxs, hall⟩ :=
    Module.Flat.ResidueSyzygies.exists_finite_syzygies_suffice K hK f
  let s : Finset (K ⊗[A] M) := Finset.univ.image xs
  have hs : ∀ x ∈ s, (f.restrictScalars A).lTensor K x = 0 := by
    intro x hx
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
    exact hxs i
  obtain ⟨C, hC, hCs⟩ := exists_fg_residue_relation_lifts hK (f.restrictScalars A) g hex hg s hs
  refine ⟨C, hC, hall C ?_⟩
  intro i
  exact hCs (xs i) (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩)

/-- A true relation lift stays a true relation lift on any further base change.
In particular this transfers the finite-stage witnesses to its localization. -/
theorem relation_lifts_baseChange {C D : Type*} [CommRing C] [CommRing D]
    [Algebra A C] [Algebra A D] (j : C →ₐ[A] D) (f : M →ₗ[A] N)
    (hlift : ∀ x : K ⊗[A] M, f.lTensor K x = 0 →
      ∃ u : C ⊗[A] M, f.baseChange C u = 0 ∧
        (TensorProduct.mk A K M 1).baseChange C u = (1 : C) ⊗ₜ[A] x) :
    ∀ x : K ⊗[A] M, f.lTensor K x = 0 →
      ∃ u : D ⊗[A] M, f.baseChange D u = 0 ∧
        (TensorProduct.mk A K M 1).baseChange D u = (1 : D) ⊗ₜ[A] x := by
  intro x hx
  obtain ⟨u, hfu, hqu⟩ := hlift x hx
  refine ⟨j.toLinearMap.rTensor M u, ?_, ?_⟩
  · rw [← LinearMap.rTensor_baseChange, hfu, map_zero]
  · rw [← LinearMap.rTensor_baseChange, hqu]
    simp

end Algebra.FlatApproximation

namespace Algebra.FlatApproximation

variable {A C K L M N : Type*} [CommRing A] [CommRing C] [CommRing K] [CommRing L]
  [Algebra A C] [Algebra A K] [Algebra A L] [Algebra C L] [Algebra K L]
  [IsScalarTower A C L] [IsScalarTower A K L]
  [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N]

/-- The common image of a lifted residue relation in a further coefficient ring. -/
theorem relation_lift_common_image (x : K ⊗[A] M) (u : C ⊗[A] M)
    (h : (TensorProduct.mk A K M 1).baseChange C u = (1 : C) ⊗ₜ[A] x) :
    (IsScalarTower.toAlgHom A C L).toLinearMap.rTensor M u =
      (IsScalarTower.toAlgHom A K L).toLinearMap.rTensor M x := by
  let φ : C ⊗[A] K →ₐ[A] L := Algebra.TensorProduct.lift
    (IsScalarTower.toAlgHom A C L) (IsScalarTower.toAlgHom A K L)
    (fun _ _ ↦ Commute.all _ _)
  let ψ : C ⊗[A] (K ⊗[A] M) →ₗ[A] L ⊗[A] M :=
    (φ.toLinearMap.rTensor M).comp (_root_.TensorProduct.assoc A C K M).symm.toLinearMap
  have hleft : ψ ((TensorProduct.mk A K M 1).baseChange C u) =
      (IsScalarTower.toAlgHom A C L).toLinearMap.rTensor M u := by
    clear h
    induction u with
    | tmul c m => simp [ψ, φ]
    | add u v hu hv => simp only [map_add, hu, hv]
  have hright : ψ ((1 : C) ⊗ₜ[A] x) =
      (IsScalarTower.toAlgHom A K L).toLinearMap.rTensor M x := by
    clear h hleft
    induction x with
    | tmul k m => simp [ψ, φ]
    | add x y hx hy => simp only [tmul_add, map_add, hx, hy]
  exact hleft.symm.trans ((congrArg ψ h).trans hright)

/-- Cancellation on a unit tensor is the base-ring map applied to its coefficients. -/
theorem cancelBaseChange_one_tmul_general (u : C ⊗[A] M) :
    AlgebraTensorModule.cancelBaseChange A C L L M ((1 : L) ⊗ₜ[C] u) =
      (IsScalarTower.toAlgHom A C L).toLinearMap.rTensor M u := by
  induction u with
  | tmul c m => simp [Algebra.smul_def]
  | add u v hu hv => simp only [tmul_add, map_add, hu, hv]

/-- If every old residue relation lifts to an actual relation at a later stage,
then the inclusion of the image of the presentation is injective on the later
residue fibre. Scalar extension between the two residue fields is flat. -/
theorem range_subtype_fibre_injective_of_relation_lifts [Module.Flat K L]
    (f : M →ₗ[A] N)
    (hlift : ∀ x : K ⊗[A] M, f.lTensor K x = 0 →
      ∃ u : C ⊗[A] M, f.baseChange C u = 0 ∧
        (TensorProduct.mk A K M 1).baseChange C u = (1 : C) ⊗ₜ[A] x) :
    Function.Injective ((LinearMap.range (f.baseChange C)).subtype.lTensor L) := by
  let fC := f.baseChange C
  let fK := f.baseChange K
  let eCM := AlgebraTensorModule.cancelBaseChange A C L L M
  let eCN := AlgebraTensorModule.cancelBaseChange A C L L N
  let eKM := AlgebraTensorModule.cancelBaseChange A K L L M
  let eKN := AlgebraTensorModule.cancelBaseChange A K L L N
  let q : L ⊗[K] (K ⊗[A] M) →ₗ[L] L ⊗[C] LinearMap.range fC :=
    (fC.rangeRestrict.baseChange L).comp (eCM.symm.toLinearMap.comp eKM.toLinearMap)
  let g : L ⊗[C] LinearMap.range fC →ₗ[L] L ⊗[K] (K ⊗[A] N) :=
    eKN.symm.toLinearMap.comp
      (eCN.toLinearMap.comp ((LinearMap.range fC).subtype.baseChange L))
  have hq : Function.Surjective q :=
    (LinearMap.baseChange_surjective L (LinearMap.surjective_rangeRestrict fC)).comp
      (eCM.symm.surjective.comp eKM.surjective)
  have hcomm : g.comp q = fK.baseChange L := by
    apply AlgebraTensorModule.ext
    intro l y
    induction y with
    | tmul k m =>
        simp only [LinearEquiv.comp_coe, coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
          LinearEquiv.trans_apply, AlgebraTensorModule.cancelBaseChange_tmul, smul_def,
          AlgebraTensorModule.cancelBaseChange_symm_tmul, baseChange_tmul,
          Submodule.subtype_apply, codRestrict_apply, map_one, one_mul,
          fC, g, eKN, eCN, q, eCM, eKM, fK]
        rw [← Algebra.smul_def, TensorProduct.smul_tmul, TensorProduct.smul_tmul',
          smul_eq_mul, mul_one]
    | add y z hy hz => simp only [tmul_add, map_add, hy, hz]
  have hkill : q.comp ((LinearMap.ker fK).subtype.baseChange L) = 0 := by
    apply kernel_baseChange_killed_of_unit_tensors
    intro x
    obtain ⟨u, hfu, hu⟩ := hlift x x.property
    have he : eCM ((1 : L) ⊗ₜ[C] u) = eKM ((1 : L) ⊗ₜ[K] (x : K ⊗[A] M)) := by
      rw [cancelBaseChange_one_tmul_general, cancelBaseChange_one_tmul_general]
      exact relation_lift_common_image (L := L) _ _ hu
    have he' : eCM.symm (eKM ((1 : L) ⊗ₜ[K] (x : K ⊗[A] M))) = (1 : L) ⊗ₜ[C] u :=
      eCM.symm_apply_eq.mpr he.symm
    change (fC.rangeRestrict.baseChange L)
      (eCM.symm (eKM ((1 : L) ⊗ₜ[K] (x : K ⊗[A] M)))) = 0
    rw [he', LinearMap.baseChange_tmul]
    have hu0 : fC.rangeRestrict u = 0 := Subtype.ext hfu
    rw [hu0, tmul_zero]
  have hg : Function.Injective g :=
    injective_of_kernel_killed_after_baseChange fK q g hq hcomm hkill
  intro x y hxy
  apply hg
  change eKN.symm (eCN (((LinearMap.range fC).subtype.baseChange L) x)) =
    eKN.symm (eCN (((LinearMap.range fC).subtype.baseChange L) y))
  exact congrArg (fun z ↦ eKN.symm (eCN z)) hxy

end Algebra.FlatApproximation

namespace Algebra.FlatApproximation

variable {A B C K L : Type*} [CommRing A] [CommRing B] [CommRing C] [CommRing K] [CommRing L]
  [Algebra A B] [Algebra A C] [Algebra A K] [Algebra A L]
  [Algebra C L] [Algebra K L] [IsScalarTower A C L] [IsScalarTower A K L]

/-- The fibre injection produced by relation lifting is the inclusion of the
actual extended ideal, not a separately assumed ideal or comparison. -/
theorem ideal_map_subtype_fibre_injective_of_relation_lifts [Module.Flat K L]
    (I : Ideal B)
    (hlift : ∀ x : K ⊗[A] I, (I.subtype.restrictScalars A).lTensor K x = 0 →
      ∃ u : C ⊗[A] I, (I.subtype.restrictScalars A).baseChange C u = 0 ∧
        (TensorProduct.mk A K I 1).baseChange C u = (1 : C) ⊗ₜ[A] x) :
    Function.Injective
      (((I.map (Algebra.TensorProduct.includeRight :
        B →ₐ[A] C ⊗[A] B)).subtype.restrictScalars C).lTensor L) := by
  have h := range_subtype_fibre_injective_of_relation_lifts (L := L)
    (I.subtype.restrictScalars A) hlift
  have hrange : LinearMap.range ((I.subtype.restrictScalars A).baseChange C) =
      (I.map (Algebra.TensorProduct.includeRight : B →ₐ[A] C ⊗[A] B)).restrictScalars C :=
    AlgebraTensorModule.range_lTensor_idealMap C C I
  change Function.Injective
    ((Submodule.subtype ((I.map (Algebra.TensorProduct.includeRight :
      B →ₐ[A] C ⊗[A] B)).restrictScalars C)).lTensor L)
  rw [← hrange]
  exact h

end Algebra.FlatApproximation
