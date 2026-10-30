/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Kummer.BoundaryNaturality
public import Aglib.GroupTheory.QuotientGroup.Nsmul
public import Aglib.CategoryTheory.Sites.SheafCohomology.Nsmul

/-!
# The Kummer injection from ordinary Picard classes modulo n

Exactness of the existing Kummer sequence identifies the boundary kernel with
n times the original Picard group. Thus its actual quotient injects into H2.
The quotient pullback uses the shared native multiplication-quotient construction, with
identity, composition and the whole original boundary square before evaluation. This result
makes no Brauer-vanishing or surjectivity assertion.
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

variable (X : Scheme.{u}) [HasExt.{w} (AbelianSheaf.{u, u + 1} X)]

/-- The kernel of the original Picard boundary consists exactly of n-multiples. -/
theorem picardBoundary_eq_zero_iff (n : ℕ) (hn : 0 < n)
    (hinv : IsUnit (n : Γ(X, ⊤))) (c : PicardGroup X) :
    picardBoundary X n hn hinv c = 0 ↔ ∃ b : PicardGroup X, n • b = c := by
  have hker := AddEquiv.ker_comp_eq_range_nsmul_of_exact (picardCohomologyEquiv X)
    (Sheaf.H.map (power X n) 1) (boundary X n hn hinv 1) n
    (Sheaf.H.map_nsmul_id (gm X) 1 n)
    ((ShortComplex.ab_exact_iff_function_exact _).mp
      (Sheaf.H.longSequence_exact₃' (shortExact X n hn hinv) 1 2 rfl))
  exact SetLike.ext_iff.mp hker c

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
  QuotientAddGroup.nsmulMap (pullbackHom f) n

omit [HasExt.{w} (AbelianSheaf.{u, u + 1} X)] in
@[simp] theorem picardQuotientPullback_mk (f : S ⟶ X) (n : ℕ) (c : PicardGroup X) :
    picardQuotientPullback f n (QuotientAddGroup.mk c) =
      QuotientAddGroup.mk (pullbackClass f c) := rfl

omit [HasExt.{w} (AbelianSheaf.{u, u + 1} X)] in
/-- The original Picard quotient pullback preserves identity through the shared construction. -/
@[simp] theorem picardQuotientPullback_id (n : ℕ) :
    picardQuotientPullback (𝟙 X) n = AddMonoidHom.id _ := by
  rw [picardQuotientPullback, pullbackHom_id, QuotientAddGroup.nsmulMap_id]

omit [HasExt.{w} (AbelianSheaf.{u, u + 1} X)] in
/-- The whole Picard quotient pullback preserves geometric composition. -/
theorem picardQuotientPullback_comp {T : Scheme.{u}} (f : S ⟶ X) (g : T ⟶ S) (n : ℕ) :
    (picardQuotientPullback g n).comp (picardQuotientPullback f n) =
      picardQuotientPullback (g ≫ f) n := by
  rw [picardQuotientPullback, picardQuotientPullback, QuotientAddGroup.nsmulMap_comp,
    ← pullbackHom_comp]
  rfl

variable [HasExt.{w'} (AbelianSheaf.{u, u + 1} S)]

/-- The whole original Picard-boundary square commutes with geometric pullback. -/
theorem picardQuotientBoundary_naturality (f : S ⟶ X) (n : ℕ) (hn : 0 < n)
    (hinv : IsUnit (n : Γ(X, ⊤))) :
    (rootsCohomologyPullback f n hn hinv 2).comp (picardQuotientBoundary X n hn hinv) =
      (picardQuotientBoundary S n hn (levelInvertible f n hinv)).comp
        (picardQuotientPullback f n) := by
  apply AddMonoidHom.ext
  intro c
  induction c using Quotient.inductionOn' with
  | h c => exact picardBoundary_pullback f n hn hinv c

/-- Evaluation of the whole naturality equation on an actual quotient class. -/
theorem picardQuotientBoundary_pullback (f : S ⟶ X) (n : ℕ) (hn : 0 < n)
    (hinv : IsUnit (n : Γ(X, ⊤)))
    (c : PicardGroup X ⧸ (nsmulAddMonoidHom (α := PicardGroup X) n).range) :
    rootsCohomologyPullback f n hn hinv 2 (picardQuotientBoundary X n hn hinv c) =
      picardQuotientBoundary S n hn (levelInvertible f n hinv)
        (picardQuotientPullback f n c) :=
  DFunLike.congr_fun (picardQuotientBoundary_naturality f n hn hinv) c

end AlgebraicGeometry.Scheme.EtaleCohomology.Picard
