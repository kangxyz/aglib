/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.ProjectiveSpace.Segre.ClosedImmersion
public import Aglib.AlgebraicGeometry.ProjectiveSpace.Point
public import Aglib.AlgebraicGeometry.Limits.FiniteProducts

/-!
# Finite products embedded by the original Segre maps

The empty product is the original base spectrum and uses projective zero-space,
not an empty projective coordinate index. All indices remain in the base universe.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.ProjectiveSpace.Segre

variable (R : Type u) [CommRing R]

/-- A finite native over-product of finite nonempty projective spaces admits an
actual closed embedding preserving its original structural morphism. -/
theorem exists_closedImmersion_finiteProductOver {n : ℕ} (σ : Fin n → Type u)
    (hfinite : ∀ i, Finite (σ i)) (hnonempty : ∀ i, Nonempty (σ i)) :
    ∃ (τ : Type u) (_ : Finite τ) (_ : Nonempty τ)
      (j : (Scheme.finiteProductOver (fun i => Over.mk (toSpec R (σ i)))).left ⟶
        ProjectiveSpace R τ),
      IsClosedImmersion j ∧ j ≫ toSpec R τ =
        (Scheme.finiteProductOver (fun i => Over.mk (toSpec R (σ i)))).hom := by
  induction n with
  | zero =>
      refine ⟨PUnit.{u + 1}, inferInstance, inferInstance, (pointIsoSpec R).inv, ?_, ?_⟩
      · exact @IsClosedImmersion.instOfIsIsoScheme _ _ _ (Iso.isIso_inv _)
      · exact (pointIsoSpec R).inv_hom_id
  | succ n ih =>
      obtain ⟨τ, hτ, hτne, j, hjclosed, hjbase⟩ :=
        ih (fun i => σ i.succ) (fun i => hfinite i.succ) (fun i => hnonempty i.succ)
      have : Finite τ := hτ
      have : Nonempty τ := hτne
      have : Finite (σ 0) := hfinite 0
      have : Nonempty (σ 0) := hnonempty 0
      let A := Over.mk (toSpec R (σ 0))
      let B := Over.mk (toSpec R τ)
      let jOver : Scheme.finiteProductOver (fun i => Over.mk (toSpec R (σ i.succ))) ⟶ B :=
        Over.homMk j hjbase
      let t := prod.map (𝟙 A) jOver
      let e := Over.prodLeftIsoPullback A B
      let k := t.left ≫ e.hom ≫ embedding R (σ 0) τ
      refine ⟨σ 0 × τ, inferInstance, inferInstance, k, ?_, ?_⟩
      · have hjOver : IsClosedImmersion jOver.left := hjclosed
        have hId : IsClosedImmersion (Over.Hom.left (𝟙 A)) := by
          change IsClosedImmersion (𝟙 A.left)
          exact @IsClosedImmersion.instOfIsIsoScheme _ _ _ (by infer_instance)
        have ht : IsClosedImmersion t.left :=
          @Scheme.isClosedImmersion_overProd_map _ _ _ _ _ (𝟙 A) jOver hId hjOver
        have he : IsClosedImmersion e.hom :=
          @IsClosedImmersion.instOfIsIsoScheme _ _ _ (Iso.isIso_hom _)
        exact @IsClosedImmersion.comp _ _ _ _ _ ht
          (@IsClosedImmersion.comp _ _ _ _ _ he (instIsClosedImmersionEmbedding R (σ 0) τ))
      · change t.left ≫ (e.hom ≫ embedding R (σ 0) τ) ≫ toSpec R (σ 0 × τ) = _
        rw [Category.assoc, embedding_toSpec]
        change t.left ≫ (e.hom ≫ CategoryTheory.Limits.pullback.fst A.hom B.hom ≫ A.hom) = _
        rw [← Scheme.overProd_hom_eq A B]
        exact t.w

end AlgebraicGeometry.ProjectiveSpace.Segre
