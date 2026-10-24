/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.IdealSheaf.GlueDisjoint
public import Aglib.AlgebraicGeometry.Limits.CoproductPullback

/-!
# Closed subschemes over a disjoint union of bases

Let `πZ : Z ⟶ S` and `πH j : H j ⟶ S`, `j ∈ J`, for a small index type `J` in any universe.
Closed subschemes `D j ⊆ Z ×_S H j` glue to a closed subscheme of `Z ×_S ∐_j H j`:

* `Scheme.IdealSheafData.sigmaGlue πZ πH D`, glued (`IdealSheafData.glueOfDisjoint`,
  `IdealSheaf/GlueDisjoint`) along the pairwise disjoint open cover of `Z ×_S ∐ H` by the
  `Z ×_S H j` (`Scheme.pullbackSigmaι`, `Limits/CoproductPullback`), with
  `comap_sigmaGlue : (sigmaGlue πZ πH D).comap (pullbackSigmaι πZ πH j) = D j`, uniqueness
  `eq_sigmaGlue_iff`, and `comap_sigmaGlue_pullbackMap`: the pullback of the glued family along a
  morphism `T ⟶ ∐ H` through the `j`-th component `b : T ⟶ H j` is the pullback of `D j` along `b`.
* `Scheme.IdealSheafData.ext_of_comap_pullbackMap_eq`: closed subschemes of `Z ×_S T` are
  determined by their pullbacks to the `Z ×_S U i` for a jointly surjective family of open
  immersions `U i ⟶ T` (for instance the clopen decomposition of `T` by fibre Hilbert polynomial,
  `HilbertScheme/Coproduct/Decomposition`).

Present consumers: the flatness, properness and surjectivity of the glued family
(`HilbertScheme/Coproduct/Family`) and its fibre Hilbert polynomials
(`HilbertScheme/Coproduct/Decomposition`).
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Scheme.IdealSheafData

variable {S Z : Scheme.{u}} (πZ : Z ⟶ S)

/-- **Closed subschemes of `Z ×_S T` are determined over an open cover of `T`**: for a jointly
surjective family of open immersions `j i : U i ⟶ T`, two closed subschemes of `Z ×_S T` with the
same pullbacks to every `Z ×_S U i` (along the `pullback.map` of `j i`) are equal. -/
theorem ext_of_comap_pullbackMap_eq {T : Scheme.{u}} (g : T ⟶ S) {ι : Type*}
    {U : ι → Scheme.{u}} (j : ∀ i, U i ⟶ T) [∀ i, IsOpenImmersion (j i)]
    (hj : ∀ t, ∃ i y, j i y = t) {I I' : (pullback πZ g).IdealSheafData}
    (h : ∀ i, I.comap (pullback.map πZ (j i ≫ g) πZ g (𝟙 Z) (j i) (𝟙 S) (by simp) (by simp)) =
      I'.comap (pullback.map πZ (j i ≫ g) πZ g (𝟙 Z) (j i) (𝟙 S) (by simp) (by simp))) :
    I = I' := by
  refine ext_of_comap_eq
    (fun i => pullback.map πZ (j i ≫ g) πZ g (𝟙 Z) (j i) (𝟙 S) (by simp) (by simp)) ?_ h
  refine Set.eq_univ_of_forall fun x => Set.mem_iUnion.mpr ?_
  obtain ⟨i, y, hy⟩ := hj (pullback.snd πZ g x)
  refine ⟨i, ?_⟩
  rw [Scheme.Pullback.range_map]
  exact ⟨⟨pullback.fst πZ g x, rfl⟩, ⟨y, hy⟩⟩

variable {J : Type*} [Small.{u} J] {H : J → Scheme.{u}} (πH : ∀ j, H j ⟶ S)

/-- **The family on `Z ×_S ∐ H` glued from families on the `Z ×_S H j`** (Nitsure,
*Construction of Hilbert and Quot schemes*, arXiv:math/0504590v1, proof of Thm 6.8, p. 33, the
family `D ⊂ X ×_S H` over the finite disjoint union `H`): the closed subscheme of `Z ×_S ∐ H`
whose restriction to every `Z ×_S H j` is `D j`. -/
def sigmaGlue (D : ∀ j, (pullback πZ (πH j)).IdealSheafData) :
    (pullback πZ (Sigma.desc πH)).IdealSheafData :=
  glueOfDisjoint (Scheme.pullbackSigmaι πZ πH) (Scheme.exists_pullbackSigmaι_eq πZ πH)
    (Scheme.pairwise_disjoint_range_pullbackSigmaι πZ πH) D

variable (D : ∀ j, (pullback πZ (πH j)).IdealSheafData)

/-- The glued family restricts to `D j` on `Z ×_S H j`. -/
@[simp]
theorem comap_sigmaGlue (j : J) :
    (sigmaGlue πZ πH D).comap (Scheme.pullbackSigmaι πZ πH j) = D j :=
  comap_glueOfDisjoint _ _ _ D j

/-- The glued family is the only closed subscheme of `Z ×_S ∐ H` restricting to every `D j`. -/
theorem eq_sigmaGlue_iff (V : (pullback πZ (Sigma.desc πH)).IdealSheafData) :
    V = sigmaGlue πZ πH D ↔ ∀ j, V.comap (Scheme.pullbackSigmaι πZ πH j) = D j :=
  eq_glueOfDisjoint_iff _ _ _ D V

/-- **Pulling back the glued family along a morphism into one component**: for `b : T ⟶ H j`
over `S`, the pullback of the glued family along `Z ×_S T ⟶ Z ×_S ∐ H` (induced by
`b ≫ Sigma.ι H j`) is the pullback of `D j` along `Z ×_S T ⟶ Z ×_S H j` (induced by `b`). -/
theorem comap_sigmaGlue_pullbackMap {T : Scheme.{u}} (gT : T ⟶ S) (j : J) (b : T ⟶ H j)
    (hb : b ≫ πH j = gT) :
    (sigmaGlue πZ πH D).comap (pullback.map πZ gT πZ (Sigma.desc πH) (𝟙 Z) (b ≫ Sigma.ι H j)
        (𝟙 S) (by simp) (by simp [hb])) =
      (D j).comap (pullback.map πZ gT πZ (πH j) (𝟙 Z) b (𝟙 S) (by simp) (by simp [hb])) := by
  have h : pullback.map πZ gT πZ (Sigma.desc πH) (𝟙 Z) (b ≫ Sigma.ι H j) (𝟙 S) (by simp)
      (by simp [hb]) = pullback.map πZ gT πZ (πH j) (𝟙 Z) b (𝟙 S) (by simp) (by simp [hb]) ≫
        Scheme.pullbackSigmaι πZ πH j := by
    rw [Scheme.pullbackSigmaι, pullback.map_comp]
    simp only [Category.comp_id]
  rw [h, comap_comp, comap_sigmaGlue]

end AlgebraicGeometry.Scheme.IdealSheafData
