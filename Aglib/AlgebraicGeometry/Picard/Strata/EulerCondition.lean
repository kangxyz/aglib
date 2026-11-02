/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Picard.Strata.FiberConditions
public import Aglib.AlgebraicGeometry.Picard.FiberCondition.RelativeCover

/-!
# The Euler-polynomial fibre condition

The original Euler-condition construction, uniqueness and open cover laws
are independent of the fine-stratum cohomology and base-change bridges.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules.Invertible AlgebraicGeometry.Scheme.Cohomology
open AlgebraicGeometry.ProjectiveSpace

namespace AlgebraicGeometry.Scheme.RelativePicard.Strata

variable {A : Type u} [CommRing A] {ι : Type u} {X : Scheme.{u}}
  (i : X ⟶ ProjectiveSpace A ι) [IsClosedImmersion i] [Flat (i ≫ toSpec A ι)]
  (N : ℕ) (e : ι ≃ Fin (N + 1))

/-- **`C_φ`**: `χ(X_t, L_t^{-1}(n)) = φ(n)` for all `n` (Kleiman (4.8.1), arXiv:math/0504020v1,
p. 28); its subsheaf is `Pic^φ`. -/
def eulerCondition (φ : Polynomial ℚ) : FiberCondition (i ≫ toSpec A ι) :=
  FiberCondition.ofLineBundle (fun T L t => HasFiberDualEulerPolynomial i T.hom φ L t)
    (fun T _ _ ⟨e'⟩ t => hasFiberDualEulerPolynomial_congr i T.hom e' t φ)
    (fun g L t' => by
      have : Finite ι := Finite.of_equiv _ e.symm
      exact hasFiberDualEulerPolynomial_pullback_iff i _ _ g.left (Over.w g) L t' φ)
    (fun T hT L => by
      have := hT
      exact (isClopen_setOf_hasFiberDualEulerPolynomial i T.hom N e L φ).isOpen)

variable {i N e}

theorem eulerCondition_holds_classOf (φ : Polynomial ℚ) (T : Over (Spec (.of A)))
    (L : LineBundle (pullback (i ≫ toSpec A ι) T.hom)) (t : T.left) :
    (eulerCondition i N e φ).Holds T (classOf _ L) t ↔ HasFiberDualEulerPolynomial i T.hom φ L t :=
  Iff.rfl

/-- Every point of every family satisfies `C_φ` for some `φ`. -/
theorem exists_eulerCondition_holds (T : Over (Spec (.of A)))
    (a : (familyPicardFunctor (i ≫ toSpec A ι)).obj (op T)) (t : T.left) :
    ∃ φ : Polynomial ℚ, (eulerCondition i N e φ).Holds T a t := by
  obtain ⟨L, rfl⟩ := Quotient.exists_rep (a : PicardGroup _)
  exact exists_hasFiberDualEulerPolynomial i T.hom L t N e

/-- `C_φ` holds for at most one `φ`. -/
theorem eq_of_eulerCondition_holds {φ φ' : Polynomial ℚ} {T : Over (Spec (.of A))}
    {a : (familyPicardFunctor (i ≫ toSpec A ι)).obj (op T)} {t : T.left}
    (h : (eulerCondition i N e φ).Holds T a t) (h' : (eulerCondition i N e φ').Holds T a t) :
    φ = φ' := by
  obtain ⟨L, rfl⟩ := Quotient.exists_rep (a : PicardGroup _)
  exact HasFiberDualEulerPolynomial.unique i T.hom L t h h'

section Covers

variable {T : Over (Spec (.of A))} [IsLocallyNoetherian T.left]
  (ξ : (fppfPicardSheaf (i ≫ toSpec A ι)).obj.obj (op T))

/-- **The opens of `C_φ` cover `T`** (Kleiman, arXiv:math/0504020v1, p. 29). -/
theorem iSup_opens_eulerCondition : ⨆ φ, (eulerCondition i N e φ).opens ξ = ⊤ :=
  FiberCondition.iSup_opens_eq_top _ (fun T a t => exists_eulerCondition_holds T a t) ξ

/-- **The opens of `C_φ` are pairwise disjoint** (Kleiman, arXiv:math/0504020v1, p. 29). -/
theorem disjoint_opens_eulerCondition {φ φ' : Polynomial ℚ} (h : φ ≠ φ') :
    Disjoint ((eulerCondition i N e φ).opens ξ) ((eulerCondition i N e φ').opens ξ) :=
  (eulerCondition i N e φ).disjoint_opens (fun _ _ _ hC hD => h (eq_of_eulerCondition_holds hC hD))
    ξ

/-- **The opens of `C_φ` are open and closed.** -/
theorem isClopen_setOf_holdsAt_eulerCondition (φ : Polynomial ℚ) :
    IsClopen {t : T.left | (eulerCondition i N e φ).HoldsAt ξ t} :=
  (eulerCondition i N e φ).isClopen_setOf_holdsAt_of_isClosed (fun T hT a => by
    have := hT
    obtain ⟨L, rfl⟩ := Quotient.exists_rep (a : PicardGroup _)
    exact (isClopen_setOf_hasFiberDualEulerPolynomial i T.hom N e L φ).isClosed) ξ

end Covers

end AlgebraicGeometry.Scheme.RelativePicard.Strata
