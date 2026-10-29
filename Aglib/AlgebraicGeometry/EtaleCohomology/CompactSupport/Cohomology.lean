/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Open.AbelianAdjunction
public import Mathlib.CategoryTheory.Sites.SheafCohomology.ExactSequences

/-!
# Étale cohomology with compact supports along an open immersion

For an open immersion `j : U ⟶ X` and an abelian sheaf `F` on the small étale site of `U`,
`CompactSupport.H j F r` is the original cohomology `Sheaf.H ((etaleLowerShriek j).obj F) r`
of the actual extension by zero of `F` (Stacks, Tag 03S3). This is the definition
`H^r_c(U, F) = H^r(X, j_! F)` of Milne, *Lectures on Étale Cohomology* v2.21, p. 92, where
`X` is the complete regular curve containing `U`. Here `X` is an arbitrary scheme containing
`U` through `j`; no independence of `X` is asserted.

The groups are functorial in `F` through `Sheaf.H.map`. Since the lower shriek is exact
(Stacks, Tag 03S5), a short exact sequence of abelian sheaves on `U` has a long exact
sequence of compactly supported cohomology, whose connecting map is the original
`Sheaf.H.δ` of the extended sequence (Milne, loc. cit.). The map
`H^r_c(U, j^* G) → H^r(X, G)` is the original counit `j_! j^* G ⟶ G` on cohomology.

Coefficients are abelian sheaves with values in `AddCommGrpCat.{u + 1}` for schemes in
universe `u`; the Ext universe `w` is arbitrary.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe w u

namespace AlgebraicGeometry.Scheme.EtaleCohomology.CompactSupport

attribute [local instance] hasSheafifyLarge

variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
  [HasExt.{w} (AbelianSheaf.{u, u + 1} X)]

/-- Étale cohomology with compact supports along an open immersion `j : U ⟶ X`:
the original cohomology `H^r(X, j_! F)` of the extension by zero of `F`. -/
abbrev H (F : AbelianSheaf.{u, u + 1} U) (r : ℕ) : Type w :=
  Sheaf.H.{w} ((etaleLowerShriek j).obj F) r

namespace H

/-- Covariant functoriality of compactly supported cohomology in the coefficient sheaf. -/
def map {F G : AbelianSheaf.{u, u + 1} U} (φ : F ⟶ G) (r : ℕ) : H j F r →+ H j G r :=
  Sheaf.H.map ((etaleLowerShriek j).map φ) r

theorem map_apply {F G : AbelianSheaf.{u, u + 1} U} (φ : F ⟶ G) (r : ℕ) (x : H j F r) :
    map j φ r x = Sheaf.H.map ((etaleLowerShriek j).map φ) r x :=
  rfl

@[simp]
theorem map_id_apply (F : AbelianSheaf.{u, u + 1} U) (r : ℕ) (x : H j F r) :
    map j (𝟙 F) r x = x := by
  rw [map_apply, CategoryTheory.Functor.map_id]
  exact Sheaf.H.map_id_apply x

theorem map_comp_apply {F G K : AbelianSheaf.{u, u + 1} U} (φ : F ⟶ G) (ψ : G ⟶ K) (r : ℕ)
    (x : H j F r) : map j (φ ≫ ψ) r x = map j ψ r (map j φ r x) := by
  rw [map_apply, CategoryTheory.Functor.map_comp]
  exact Sheaf.H.map_comp_apply _ _ x

/-- Cohomology of an isomorphic coefficient is mapped bijectively. -/
theorem map_bijective_of_isIso {F G : AbelianSheaf.{u, u + 1} U} (φ : F ⟶ G) [IsIso φ]
    (r : ℕ) : Function.Bijective (map j φ r) := by
  refine Function.bijective_iff_has_inverse.mpr ⟨map j (inv φ) r, fun x => ?_, fun x => ?_⟩
  · rw [← map_comp_apply, IsIso.hom_inv_id, map_id_apply]
  · rw [← map_comp_apply, IsIso.inv_hom_id, map_id_apply]

end H

/-- Compactly supported cohomology in degree `r` as an additive functor of the coefficient. -/
abbrev functor (r : ℕ) : AbelianSheaf.{u, u + 1} U ⥤ AddCommGrpCat.{w} :=
  etaleLowerShriek j ⋙ Sheaf.functorH (Scheme.smallEtaleTopology X) r

/-- The map `H^r_c(U, j^* G) → H^r(X, G)` induced by the original counit `j_! j^* G ⟶ G`. -/
def counitMap (G : AbelianSheaf.{u, u + 1} X) (r : ℕ) :
    H j ((inverseImage j).obj G) r →+ Sheaf.H.{w} G r :=
  Sheaf.H.map ((etaleLowerShriekAdjunction j).counit.app G) r

theorem counitMap_apply (G : AbelianSheaf.{u, u + 1} X) (r : ℕ)
    (x : H j ((inverseImage j).obj G) r) :
    counitMap j G r x = Sheaf.H.map ((etaleLowerShriekAdjunction j).counit.app G) r x :=
  rfl

section ShortExact

variable {S : ShortComplex (AbelianSheaf.{u, u + 1} U)} (hS : S.ShortExact)

/-- The connecting map of compactly supported cohomology for a short exact sequence on `U`:
the original connecting map of the extended short exact sequence on `X`. -/
def δ (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁) : H j S.X₃ n₀ →+ H j S.X₁ n₁ :=
  Sheaf.H.δ (shortExact_etaleLowerShriek j hS) n₀ n₁ h

/-- The long exact sequence
`H^{n₀}_c(U, S.X₁) → H^{n₀}_c(U, S.X₂) → H^{n₀}_c(U, S.X₃) → H^{n₁}_c(U, S.X₁) → …`. -/
abbrev longSequence (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁) : ComposableArrows AddCommGrpCat.{w} 5 :=
  Sheaf.H.longSequence (shortExact_etaleLowerShriek j hS) n₀ n₁ h

theorem longSequence_exact (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁) :
    (longSequence j hS n₀ n₁ h).Exact :=
  Sheaf.H.longSequence_exact _ n₀ n₁ h

include hS in
/-- Exactness at the middle coefficient. -/
theorem exact_map_f_map_g (n : ℕ) : Function.Exact (H.map j S.f n) (H.map j S.g n) :=
  (ShortComplex.ab_exact_iff_function_exact _).mp
    (Sheaf.H.longSequence_exact₂' (shortExact_etaleLowerShriek j hS) n)

/-- Exactness at the third coefficient. -/
theorem exact_map_g_δ (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁) :
    Function.Exact (H.map j S.g n₀) (δ j hS n₀ n₁ h) :=
  (ShortComplex.ab_exact_iff_function_exact _).mp
    (Sheaf.H.longSequence_exact₃' (shortExact_etaleLowerShriek j hS) n₀ n₁ h)

/-- Exactness at the first coefficient in the next degree. -/
theorem exact_δ_map_f (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁) :
    Function.Exact (δ j hS n₀ n₁ h) (H.map j S.f n₁) :=
  (ShortComplex.ab_exact_iff_function_exact _).mp
    (Sheaf.H.longSequence_exact₁' (shortExact_etaleLowerShriek j hS) n₀ n₁ h)

end ShortExact

end AlgebraicGeometry.Scheme.EtaleCohomology.CompactSupport
