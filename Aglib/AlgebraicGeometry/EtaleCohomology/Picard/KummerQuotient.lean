/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Kummer.BoundaryNaturality
public import Mathlib.GroupTheory.QuotientGroup.Basic

/-!
# The Kummer injection from ordinary Picard classes modulo n

Exactness of the existing Kummer sequence identifies the boundary kernel with
n times the original Picard group. Thus its actual quotient injects into H2.
This result makes no Brauer-vanishing or surjectivity assertion.
-/

@[expose] public section
noncomputable section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules.Invertible
open AlgebraicGeometry.Scheme.Modules.Invertible.PullbackTensor.Local
open AlgebraicGeometry.Scheme.EtaleCohomology.Picard
open AlgebraicGeometry.Scheme.EtaleCohomology.Kummer
open GroupCohomology.Kummer.Coefficients GroupCohomology.Kummer.CoefficientBaseChange

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Picard

universe u w w'

private theorem cohomology_nsmul_id {C : Type*} [Category C]
    {J : GrothendieckTopology C} [HasSheafify J AddCommGrpCat.{u}]
    [HasExt.{w} (Sheaf J AddCommGrpCat.{u})]
    (L : Sheaf J AddCommGrpCat.{u}) (n q : ℕ) (a : Sheaf.H.{w} L q) :
    Sheaf.H.map (n • 𝟙 L) q a = n • a := by
  induction n with
  | zero => simp [Sheaf.H.map_apply]
  | succ n ih =>
      rw [succ_nsmul, Sheaf.H.map_add_apply, ih, Sheaf.H.map_id_apply, succ_nsmul]

private theorem exact_nsmul_transport {A B D : Type*} [AddCommGroup A]
    [AddCommGroup B] [AddCommGroup D] (e : A ≃+ B) (p : B →+ B) (d : B →+ D)
    (n : ℕ) (hp : ∀ b, p b = n • b) (hd : Function.Exact p d) (a : A) :
    d (e a) = 0 ↔ ∃ b, n • b = a := by
  rw [hd]
  constructor
  · rintro ⟨b, hb⟩
    refine ⟨e.symm b, e.injective ?_⟩
    rw [map_nsmul, AddEquiv.apply_symm_apply, ← hp, hb]
  · rintro ⟨b, rfl⟩
    exact ⟨e b, by rw [hp, map_nsmul]⟩

variable (X : Scheme.{u}) [HasExt.{w} (AbelianSheaf.{u, u + 1} X)]

/-- The kernel of the original Picard boundary consists exactly of n-multiples. -/
theorem picardBoundary_eq_zero_iff (n : ℕ) (hn : 0 < n)
    (hinv : IsUnit (n : Γ(X, ⊤))) (c : PicardGroup X) :
    picardBoundary X n hn hinv c = 0 ↔ ∃ b : PicardGroup X, n • b = c := by
  exact exact_nsmul_transport (picardCohomologyEquiv X)
    (Sheaf.H.map (power X n) 1) (boundary X n hn hinv 1) n
    (cohomology_nsmul_id (gm X) n 1)
    ((ShortComplex.ab_exact_iff_function_exact _).mp
      (Sheaf.H.longSequence_exact₃' (shortExact X n hn hinv) 1 2 rfl)) c

/-- Equality of native additive subgroups, not just an elementwise exactness statement. -/
theorem picardBoundary_ker (n : ℕ) (hn : 0 < n) (hinv : IsUnit (n : Γ(X, ⊤))) :
    (picardBoundary X n hn hinv).ker =
      (nsmulAddMonoidHom (α := PicardGroup X) n).range := by
  ext c
  exact picardBoundary_eq_zero_iff X n hn hinv c

/-- The actual Kummer map on the native quotient of the ordinary Picard group. -/
def picardQuotientBoundary (n : ℕ) (hn : 0 < n) (hinv : IsUnit (n : Γ(X, ⊤))) :
    PicardGroup X ⧸ (nsmulAddMonoidHom (α := PicardGroup X) n).range →+
      Sheaf.H.{w} (mu X n) 2 :=
  QuotientAddGroup.lift _ (picardBoundary X n hn hinv)
    (picardBoundary_ker X n hn hinv).symm.le

/-- Its representative formula is exactly the original boundary. -/
@[simp] theorem picardQuotientBoundary_mk (n : ℕ) (hn : 0 < n)
    (hinv : IsUnit (n : Γ(X, ⊤))) (c : PicardGroup X) :
    picardQuotientBoundary X n hn hinv (QuotientAddGroup.mk c) =
      picardBoundary X n hn hinv c := rfl

/-- Kummer always gives an injection Pic/n into original H2, on any scheme. -/
theorem picardQuotientBoundary_injective (n : ℕ) (hn : 0 < n)
    (hinv : IsUnit (n : Γ(X, ⊤))) :
    Function.Injective (picardQuotientBoundary X n hn hinv) :=
  (QuotientAddGroup.injective_lift_iff _ _ _).mpr
    (picardBoundary_ker X n hn hinv).symm

variable {X} {S : Scheme.{u}}

/-- The ordinary Picard pullback descends to its native quotient by n-multiples. -/
def picardQuotientPullback (f : S ⟶ X) (n : ℕ) :
    PicardGroup X ⧸ (nsmulAddMonoidHom (α := PicardGroup X) n).range →+
      PicardGroup S ⧸ (nsmulAddMonoidHom (α := PicardGroup S) n).range :=
  QuotientAddGroup.map _ _ (pullbackHom f) (by
    rintro c ⟨b, rfl⟩
    exact ⟨pullbackHom f b, (_root_.map_nsmul (pullbackHom f) n b).symm⟩)

omit [HasExt.{w} (AbelianSheaf.{u, u + 1} X)] in
@[simp] theorem picardQuotientPullback_mk (f : S ⟶ X) (n : ℕ) (c : PicardGroup X) :
    picardQuotientPullback f n (QuotientAddGroup.mk c) =
      QuotientAddGroup.mk (pullbackClass f c) := rfl

variable [HasExt.{w'} (AbelianSheaf.{u, u + 1} S)]

/-- The injection Pic/n into original H2 respects arbitrary geometric pullback. -/
theorem picardQuotientBoundary_pullback (f : S ⟶ X) (n : ℕ) (hn : 0 < n)
    (hinv : IsUnit (n : Γ(X, ⊤)))
    (c : PicardGroup X ⧸ (nsmulAddMonoidHom (α := PicardGroup X) n).range) :
    rootsCohomologyPullback f n hn hinv 2 (picardQuotientBoundary X n hn hinv c) =
      picardQuotientBoundary S n hn (levelInvertible f n hinv)
        (picardQuotientPullback f n c) := by
  induction c using Quotient.inductionOn' with
  | h c => exact picardBoundary_pullback f n hn hinv c

end AlgebraicGeometry.Scheme.EtaleCohomology.Picard
