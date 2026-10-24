/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.IdealSheaf.GlueCoproduct
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.Proper

/-!
# Flat and proper families over a disjoint union of bases

Let `πZ : Z ⟶ S` and `πH j : H j ⟶ S`, `j ∈ J`, for a small index type `J` (finite in the
application), and let `D j ⊆ Z ×_S H j` be closed subschemes with glued family
`D = sigmaGlue πZ πH D ⊆ Z ×_S ∐_j H j` (`IdealSheaf/GlueCoproduct`). Then `D` is flat, proper or
surjective over `∐_j H j` exactly when every `D j` is so over `H j`:

* `Scheme.IdealSheafData.sigmaGlue_iff`: for a property `P` local at the target,
  `P (D ⟶ ∐ H)` holds exactly when every `P (D j ⟶ H j)` does; the component of `D` over `H j`
  is the base change of `D ⟶ ∐ H` along the open immersion `Sigma.ι H j`
  (`Scheme.isPullback_pullbackSigmaι`), and the `Sigma.ι H j` cover `∐ H` (`sigmaOpenCover`);
* `Scheme.IdealSheafData.flat_sigmaGlue`, `isProper_sigmaGlue`, `surjective_sigmaGlue`.

This is the restriction `D ⊂ X ×_S H` of the universal family to the finite disjoint union `H` of
Hilbert schemes in Nitsure, *Construction of Hilbert and Quot schemes*, arXiv:math/0504590v1,
proof of Thm 6.8, p. 33 ("Let H be the finite disjoint union of the corresponding open subschemes
Hilb^{Φ,L}_{X/S} … the projection p : D → H is proper and flat"), built here directly from
families over the pieces, with no Hilbert-scheme input.

Present consumer: the universal family `D_F` on `Z ×_S ∐_{Φ ∈ F} Hilb^Φ_Z` (plan task HQ10).
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Scheme.IdealSheafData

variable {S Z : Scheme.{u}} (πZ : Z ⟶ S) {J : Type*} [Small.{u} J] {H : J → Scheme.{u}}
  (πH : ∀ j, H j ⟶ S) (D : ∀ j, (pullback πZ (πH j)).IdealSheafData)

/-- **Properties local at the target pass between the glued family and its components**: for a
property `P` of morphisms local at the target (for instance flat, proper or surjective), the glued
family `D ⊆ Z ×_S ∐ H` has `P` over `∐ H` exactly when every `D j` has `P` over `H j`. The
component of `D` over `H j` is the base change of `D ⟶ ∐ H` along the open immersion
`Sigma.ι H j`, and the `Sigma.ι H j` cover `∐ H` (`sigmaOpenCover`). -/
theorem sigmaGlue_iff {P : MorphismProperty Scheme.{u}} [IsZariskiLocalAtTarget P] :
    P ((sigmaGlue πZ πH D).subschemeι ≫ pullback.snd πZ (Sigma.desc πH)) ↔
      ∀ j, P ((D j).subschemeι ≫ pullback.snd πZ (πH j)) := by
  have key : ∀ j, IsPullback
      (pullback.snd (Scheme.pullbackSigmaι πZ πH j) (sigmaGlue πZ πH D).subschemeι)
      (pullback.fst (Scheme.pullbackSigmaι πZ πH j) (sigmaGlue πZ πH D).subschemeι ≫
        pullback.snd πZ (πH j))
      ((sigmaGlue πZ πH D).subschemeι ≫ pullback.snd πZ (Sigma.desc πH)) (Sigma.ι H j) :=
    fun j => (IsPullback.of_hasPullback _ _).flip.paste_vert
      (Scheme.isPullback_pullbackSigmaι πZ πH j)
  have hj : ∀ j, P ((D j).subschemeι ≫ pullback.snd πZ (πH j)) ↔
      P (pullback.fst (Scheme.pullbackSigmaι πZ πH j) (sigmaGlue πZ πH D).subschemeι ≫
        pullback.snd πZ (πH j)) := fun j => by
    conv_lhs => rw [← comap_sigmaGlue πZ πH D j, ← comapIso_hom_fst, Category.assoc]
    exact P.cancel_left_of_respectsIso _ _
  refine ⟨fun h j => (hj j).mpr (IsZariskiLocalAtTarget.of_isPullback (key j) h), fun h => ?_⟩
  refine IsZariskiLocalAtTarget.of_openCover (sigmaOpenCover H) fun j => ?_
  have h' := (hj j).mp (h j)
  rw [← (key j).isoPullback_hom_snd, P.cancel_left_of_respectsIso] at h'
  exact h'

/-- **The glued family is flat** over `∐ H` when every `D j` is flat over `H j`. -/
theorem flat_sigmaGlue (h : ∀ j, Flat ((D j).subschemeι ≫ pullback.snd πZ (πH j))) :
    Flat ((sigmaGlue πZ πH D).subschemeι ≫ pullback.snd πZ (Sigma.desc πH)) :=
  -- Instance search fails to apply `HasRingHomProperty.instIsZariskiLocalAtTarget` here (its
  -- conclusion does not unify with `IsZariskiLocalAtTarget @Flat` during resolution), so the
  -- instance is supplied directly.
  haveI : IsZariskiLocalAtTarget @Flat := HasRingHomProperty.instIsZariskiLocalAtTarget @Flat
  (sigmaGlue_iff πZ πH D (P := @Flat)).mpr h

/-- **The glued family is proper** over `∐ H` when every `D j` is proper over `H j`. -/
theorem isProper_sigmaGlue (h : ∀ j, IsProper ((D j).subschemeι ≫ pullback.snd πZ (πH j))) :
    IsProper ((sigmaGlue πZ πH D).subschemeι ≫ pullback.snd πZ (Sigma.desc πH)) :=
  (sigmaGlue_iff πZ πH D (P := @IsProper)).mpr h

/-- **The glued family is surjective** over `∐ H` when every `D j` is surjective over `H j`. -/
theorem surjective_sigmaGlue
    (h : ∀ j, Surjective ((D j).subschemeι ≫ pullback.snd πZ (πH j))) :
    Surjective ((sigmaGlue πZ πH D).subschemeι ≫ pullback.snd πZ (Sigma.desc πH)) :=
  (sigmaGlue_iff πZ πH D (P := @Surjective)).mpr h

end AlgebraicGeometry.Scheme.IdealSheafData
