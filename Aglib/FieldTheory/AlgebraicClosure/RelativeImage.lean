/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.FieldTheory.AlgebraicClosure

/-!
# The image of a specified algebraic closure embedding

Source: `R5Lab.Aglib.FieldTheory.AlgebraicClosure.RelativeImage`,
revision `f8a3314ddecffcada2ec721d26d56a937bed9690`. Exact field, action, embedding and
explicit-data hypotheses are retained. Native objects and maps are reused.
-/

@[expose] public section

noncomputable section
universe u
section AlgebraicClosureImageConstruction
universe v w

/-! # Canonical identification with the algebraic elements in an ambient field

An actual embedding of an algebraic closure identifies it with the literal
relative algebraic closure in the ambient field. This equivalence follows the
specified embedding, rather than an arbitrary chosen algebraic-closure isomorphism.
-/
noncomputable section
namespace IsAlgClosure
variable (F : Type u) (L : Type v) (K : Type w)
  [Field F] [Field L] [Field K] [Algebra F L] [Algebra F K] [Algebra L K]
  [IsScalarTower F L K] [IsAlgClosure F L]

/-- The given algebraic-closure embedding, with image in the actual algebraic subfield. -/
def algebraicImage : L →ₐ[F] algebraicClosure F K where
  toFun x := ⟨algebraMap L K x,
    (Algebra.IsIntegral.isIntegral (R := F) x).map (IsScalarTower.toAlgHom F L K)⟩
  map_zero' := Subtype.ext (map_zero _)
  map_one' := Subtype.ext (map_one _)
  map_add' x y := Subtype.ext (map_add _ x y)
  map_mul' x y := Subtype.ext (map_mul _ x y)
  commutes' x := Subtype.ext (IsScalarTower.algebraMap_apply F L K x).symm

@[simp] theorem algebraicImage_coe (x : L) :
    (algebraicImage F L K x : K) = algebraMap L K x := rfl

/-- Every algebraic element in the ambient field lies in the given embedded
algebraic closure. This does not say arbitrary ambient elements are algebraic. -/
theorem algebraicImage_surjective : Function.Surjective (algebraicImage F L K) := by
  intro x
  let : IsAlgClosed L := IsAlgClosure.isAlgClosed F
  have hx : (x : K) ∈ algebraicClosure L K :=
    mem_algebraicClosure_iff'.mpr (IsIntegral.tower_top x.property)
  have hb : algebraicClosure L K = ⊥ :=
    IntermediateField.eq_bot_of_isAlgClosed_of_isAlgebraic _
  obtain ⟨y, hy⟩ := IntermediateField.mem_bot.mp (hb ▸ hx)
  exact ⟨y, Subtype.ext hy⟩

/-- Canonical onto-image equivalence for the specified embedding. -/
def algebraicImageEquiv : L ≃ₐ[F] algebraicClosure F K :=
  AlgEquiv.ofBijective (algebraicImage F L K)
    ⟨(algebraicImage F L K).injective, algebraicImage_surjective F L K⟩

@[simp] theorem algebraicImageEquiv_coe (x : L) :
    (algebraicImageEquiv F L K x : K) = algebraMap L K x := rfl

/-- Transport an automorphism of the actual algebraic subfield to the chosen
algebraic closure through this exact embedding-compatible equivalence. -/
def algebraicAutomorphismLift
    (σ : (algebraicClosure F K) ≃ₐ[F] (algebraicClosure F K)) : L ≃ₐ[F] L :=
  ((algebraicImageEquiv F L K).trans σ).trans (algebraicImageEquiv F L K).symm

@[simp] theorem algebraicAutomorphismLift_compatible
    (σ : (algebraicClosure F K) ≃ₐ[F] (algebraicClosure F K))
    (x : algebraicClosure F K) :
    algebraMap L K (algebraicAutomorphismLift F L K σ
      ((algebraicImageEquiv F L K).symm x)) = (σ x : K) := by
  change ((algebraicImageEquiv F L K)
    (algebraicAutomorphismLift F L K σ ((algebraicImageEquiv F L K).symm x)) : K) = _
  simp [algebraicAutomorphismLift]

end IsAlgClosure

end
end AlgebraicClosureImageConstruction


/- Source cluster: CompletedGaloisAction; source SHA256
  eebc36698c12eaa23dd7173a560d0f4a871612a1566ce1dafcde607a497a98e3. -/
