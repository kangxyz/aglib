/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.NeronModification.Domain
public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.Noetherian.Basic

/-! # Modification of an actual global point

The centre is the actual kernel of reduction modulo the distinguished scalar,
not the maximal ideal of the target. Its generators therefore supply the
actual divisibility witnesses in that same target. No local or smoothness
conclusion is included among the inputs.
-/

@[expose] public noncomputable section

namespace Algebra.NeronModification

variable {P B C ι : Type*} [CommRing P] [CommRing B] [CommRing C]
variable [Algebra P B] [Algebra P C]

/-- The centre of a global point above the distinguished principal ideal. -/
def residueCentre (p : P) (f : B →ₐ[P] C) : Ideal B :=
  RingHom.ker ((Ideal.Quotient.mk (Ideal.span {algebraMap P C p})).comp f.toRingHom)

/-- Membership in the actual residue kernel is precisely divisibility in the target. -/
theorem mem_residueCentre_iff (p : P) (f : B →ₐ[P] C) (b : B) :
    b ∈ residueCentre p f ↔ algebraMap P C p ∣ f b := by
  change Ideal.Quotient.mk (Ideal.span {algebraMap P C p}) (f b) = 0 ↔ _
  rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]

/-- The original distinguished scalar belongs to the actual centre. -/
theorem scalar_mem_residueCentre (p : P) (f : B →ₐ[P] C) :
    algebraMap P B p ∈ residueCentre p f := by
  rw [mem_residueCentre_iff, f.commutes]

/-- A finite-type source over a Noetherian base has a finitely generated actual centre. -/
theorem residueCentre_fg [IsNoetherianRing P] [Algebra.FiniteType P B]
    (p : P) (f : B →ₐ[P] C) : (residueCentre p f).FG := by
  let : IsNoetherianRing B := Algebra.FiniteType.isNoetherianRing P B
  exact IsNoetherian.noetherian _

/-- Choose finitely many actual centre generators, without changing the centre. -/
theorem exists_residueCentre_generators [IsNoetherianRing P] [Algebra.FiniteType P B]
    (p : P) (f : B →ₐ[P] C) :
    ∃ (n : ℕ) (g : Fin n → B), Ideal.span (Set.range g) = residueCentre p f :=
  Submodule.fg_iff_exists_fin_generating_family.mp (residueCentre_fg p f)

/-- The same actual generators satisfy the centre convention used by the local strict step. -/
theorem span_insert_scalar_eq_residueCentre (p : P) (f : B →ₐ[P] C) (g : ι → B)
    (hg : Ideal.span (Set.range g) = residueCentre p f) :
    Ideal.span (insert (algebraMap P B p) (Set.range g)) = residueCentre p f := by
  rw [Ideal.span_insert, hg, sup_eq_right]
  exact (Ideal.span_singleton_le_iff_mem _).mpr (scalar_mem_residueCentre p f)

/-- Generators of the actual kernel have actual division witnesses in the fixed target. -/
def residueDivision (p : P) (f : B →ₐ[P] C) (g : ι → B)
    (hg : ∀ i, g i ∈ residueCentre p f) (i : ι) : C :=
  Classical.choose ((mem_residueCentre_iff p f (g i)).mp (hg i))

theorem scalar_mul_residueDivision (p : P) (f : B →ₐ[P] C) (g : ι → B)
    (hg : ∀ i, g i ∈ residueCentre p f) (i : ι) :
    f (algebraMap P B p) * residueDivision p f g hg i = f (g i) := by
  rw [f.commutes]
  exact (Classical.choose_spec ((mem_residueCentre_iff p f (g i)).mp (hg i))).symm

/-- The actual global lift is defined in the original target and preserves base scalars. -/
def residueLift (p : P) (f : B →ₐ[P] C) (g : ι → B)
    (hg : ∀ i, g i ∈ residueCentre p f) (hp : IsRegular (algebraMap P C p)) :
    Modification (algebraMap P B p) g →ₐ[P] C where
  __ := lift (algebraMap P B p) g f.toRingHom (residueDivision p f g hg)
    (scalar_mul_residueDivision p f g hg) (by
      change IsRegular (f (algebraMap P B p))
      rw [f.commutes]
      exact hp)
  commutes' a := by
    change lift (algebraMap P B p) g f.toRingHom _ _ _
      (of (algebraMap P B p) g (algebraMap P B a)) = algebraMap P C a
    rw [lift_of]
    exact f.commutes a

/-- All original coefficients, not just the distinguished scalar, keep their values. -/
@[simp] theorem residueLift_of (p : P) (f : B →ₐ[P] C) (g : ι → B)
    (hg : ∀ i, g i ∈ residueCentre p f) (hp : IsRegular (algebraMap P C p)) (b : B) :
    residueLift p f g hg hp (of (algebraMap P B p) g b) = f b := by
  have hp' : IsRegular (f.toRingHom (algebraMap P B p)) := by
    change IsRegular (f (algebraMap P B p))
    rw [f.commutes]
    exact hp
  change lift (algebraMap P B p) g f.toRingHom (residueDivision p f g hg)
    (scalar_mul_residueDivision p f g hg) hp' (of (algebraMap P B p) g b) = f b
  exact lift_of _ _ _ _ _ hp' b

/-- The actual lift of an injective global point is injective. -/
theorem residueLift_injective (p : P) (f : B →ₐ[P] C) (hf : Function.Injective f)
    (g : ι → B) (hg : ∀ i, g i ∈ residueCentre p f)
    (hp : IsRegular (algebraMap P C p)) :
    Function.Injective (residueLift p f g hg hp) := by
  have hp' : IsRegular (f.toRingHom (algebraMap P B p)) := by
    change IsRegular (f (algebraMap P B p))
    rw [f.commutes]
    exact hp
  change Function.Injective (lift (algebraMap P B p) g f.toRingHom
    (residueDivision p f g hg) (scalar_mul_residueDivision p f g hg) hp')
  exact lift_injective _ _ f.toRingHom hf _ _ hp'

/-- Finite many divided coordinates preserve actual finite type over the original base. -/
theorem finiteType_modification [Finite ι] [Algebra.FiniteType P B] (p : B) (g : ι → B) :
    Algebra.FiniteType P (Modification p g) := by
  infer_instance

/-- The next global source is a domain because its actual point is injective. -/
theorem residueLift_isDomain [IsDomain C] (p : P) (f : B →ₐ[P] C)
    (hf : Function.Injective f) (g : ι → B) (hg : ∀ i, g i ∈ residueCentre p f)
    (hp : IsRegular (algebraMap P C p)) : IsDomain (Modification (algebraMap P B p) g) :=
  Function.Injective.isDomain (residueLift p f g hg hp)
    (residueLift_injective p f hf g hg hp)

end Algebra.NeronModification
