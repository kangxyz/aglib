/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Limits.Monomorphisms
public import Aglib.AlgebraicGeometry.Limits.FiniteCoproductPullback
public import Mathlib.AlgebraicGeometry.PullbackCarrier

/-!
# The components of the base change of a disjoint union

Let `πZ : Z ⟶ S` and `πH j : H j ⟶ S`, `j ∈ J`, for a small index type `J` in any universe. The
base change `Z ×_S ∐_j H j` (`pullback πZ (Sigma.desc πH)`) is covered by the pairwise disjoint
open subschemes `Z ×_S H j`:

* `Scheme.pullbackSigmaι πZ πH j : Z ×_S H j ⟶ Z ×_S ∐ H`, the `pullback.map` of `Sigma.ι H j`, an
  open immersion (Mathlib's `Scheme.pullback_map_isOpenImmersion`), with `pullbackSigmaι_fst` and
  `pullbackSigmaι_snd`;
* `Scheme.isPullback_pullbackSigmaι`: it is the base change of `Sigma.ι H j` along
  `Z ×_S ∐ H ⟶ ∐ H`;
* `Scheme.range_pullbackSigmaι`: its image is the preimage of the `j`-th component; the images
  cover (`Scheme.exists_pullbackSigmaι_eq`) and are pairwise disjoint
  (`Scheme.pairwise_disjoint_range_pullbackSigmaι`, from Mathlib's `isEmpty_pullback_sigmaι_of_ne`).

For finite `J` the `Scheme.pullbackSigmaι πZ πH j` are the coprojections of the comparison
`FiniteCoproductPullback.iso : ∐_j (H j ×_S Z) ≅ (∐ H) ×_S Z` (`Limits/FiniteCoproductPullback`),
up to swapping the factors (`Scheme.pullbackSigmaι_eq_sigmaι_iso`). The other statements here
need no finiteness of `J`.

Present consumers: closed subschemes over a disjoint union of bases (`IdealSheaf/GlueCoproduct`)
and the component maps of the Hilbert functor (`HilbertScheme/Coproduct/Decomposition`).
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

variable {S Z : Scheme.{u}} (πZ : Z ⟶ S) {J : Type*} [Small.{u} J] {H : J → Scheme.{u}}
  (πH : ∀ j, H j ⟶ S)

/-- The `j`-th component `Z ×_S H j ⟶ Z ×_S ∐ H` of the base change of `∐ H` to `Z`: the
`pullback.map` of `Sigma.ι H j`. -/
def Scheme.pullbackSigmaι (j : J) : pullback πZ (πH j) ⟶ pullback πZ (Sigma.desc πH) :=
  pullback.map πZ (πH j) πZ (Sigma.desc πH) (𝟙 Z) (Sigma.ι H j) (𝟙 S) (by simp) (by simp)

@[reassoc (attr := simp)]
theorem Scheme.pullbackSigmaι_fst (j : J) :
    Scheme.pullbackSigmaι πZ πH j ≫ pullback.fst πZ (Sigma.desc πH) = pullback.fst πZ (πH j) :=
  (pullback.lift_fst _ _ _).trans (Category.comp_id _)

@[reassoc (attr := simp)]
theorem Scheme.pullbackSigmaι_snd (j : J) :
    Scheme.pullbackSigmaι πZ πH j ≫ pullback.snd πZ (Sigma.desc πH) =
      pullback.snd πZ (πH j) ≫ Sigma.ι H j :=
  pullback.lift_snd _ _ _

instance (j : J) : IsOpenImmersion (Scheme.pullbackSigmaι πZ πH j) := by
  unfold Scheme.pullbackSigmaι
  infer_instance

/-- **`Z ×_S H j` is the base change of `Z ×_S ∐ H ⟶ ∐ H` along `Sigma.ι H j`.** -/
theorem Scheme.isPullback_pullbackSigmaι (j : J) :
    IsPullback (Scheme.pullbackSigmaι πZ πH j) (pullback.snd πZ (πH j))
      (pullback.snd πZ (Sigma.desc πH)) (Sigma.ι H j) := by
  refine IsPullback.of_right ?_ (Scheme.pullbackSigmaι_snd πZ πH j)
    (IsPullback.of_hasPullback πZ (Sigma.desc πH))
  rw [Scheme.pullbackSigmaι_fst, Sigma.ι_comp_desc]
  exact IsPullback.of_hasPullback πZ (πH j)

/-- The image of `Z ×_S H j` in `Z ×_S ∐ H` is the preimage of the `j`-th component. -/
theorem Scheme.range_pullbackSigmaι (j : J) :
    Set.range (Scheme.pullbackSigmaι πZ πH j) =
      pullback.snd πZ (Sigma.desc πH) ⁻¹' Set.range (Sigma.ι H j) := by
  ext x
  rw [Scheme.pullbackSigmaι, Scheme.Pullback.range_map]
  exact ⟨fun h => h.2, fun h => ⟨⟨pullback.fst πZ (Sigma.desc πH) x, rfl⟩, h⟩⟩

/-- The components `Z ×_S H j` cover `Z ×_S ∐ H`. -/
theorem Scheme.exists_pullbackSigmaι_eq (x : ↑(pullback πZ (Sigma.desc πH))) :
    ∃ j y, Scheme.pullbackSigmaι πZ πH j y = x := by
  obtain ⟨j, y, hy⟩ := Scheme.exists_sigmaι_eq (pullback.snd πZ (Sigma.desc πH) x)
  have hx : x ∈ Set.range (Scheme.pullbackSigmaι πZ πH j) := by
    rw [Scheme.range_pullbackSigmaι]
    exact ⟨y, hy⟩
  obtain ⟨z, hz⟩ := hx
  exact ⟨j, z, hz⟩

/-- The components `Z ×_S H j` of `Z ×_S ∐ H` are pairwise disjoint. -/
theorem Scheme.pairwise_disjoint_range_pullbackSigmaι :
    Pairwise fun i j => Disjoint (Set.range (Scheme.pullbackSigmaι πZ πH i))
      (Set.range (Scheme.pullbackSigmaι πZ πH j)) := by
  intro i j hij
  rw [Scheme.range_pullbackSigmaι, Scheme.range_pullbackSigmaι]
  exact (Scheme.isEmpty_pullback_iff.mp (isEmpty_pullback_sigmaι_of_ne H hij)).preimage _

/-- **For finitely many components, `Scheme.pullbackSigmaι` is a coprojection of the finite
coproduct–pullback comparison**: up to swapping the factors of the pullbacks, the component
`Z ×_S H j ⟶ Z ×_S ∐ H` is `Sigma.ι` followed by `FiniteCoproductPullback.iso`. -/
theorem Scheme.pullbackSigmaι_eq_sigmaι_iso [Finite J] (j : J) :
    Scheme.pullbackSigmaι πZ πH j = (pullbackSymmetry πZ (πH j)).hom ≫
      Sigma.ι (fun j => pullback (πH j) πZ) j ≫ (FiniteCoproductPullback.iso H πH πZ).hom ≫
        (pullbackSymmetry (Sigma.desc πH) πZ).hom := by
  apply pullback.hom_ext
  · simp
  · simp

end AlgebraicGeometry
