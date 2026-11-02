/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.CompactSupport.Cohomology
public import Aglib.AlgebraicGeometry.EtaleCohomology.Localization.AbelianShortExact

/-!
# The open-closed long exact sequence of compactly supported cohomology

Let `j : U ⟶ X` be an open immersion and `i : Z ⟶ X` a closed immersion with
`Set.range j = (Set.range i)ᶜ`. For every abelian sheaf `G` on `X`, the original sequence
`0 → j_! j^* G → G → i_* i^* G → 0` (Stacks, Tag 095L) is short exact by
`abelianLocalization_shortExact`; its arrows are the counit of `etaleLowerShriekAdjunction j`
and the unit of `inverseImageAdjunction i`. Its long exact cohomology sequence is

`… → H^r_c(U, j^* G) → H^r(X, G) → H^r(X, i_* i^* G) → H^{r+1}_c(U, j^* G) → …`

(Milne, *Lectures on Étale Cohomology* v2.21, proof of Prop. 14.5, p. 92), with the original
maps and the original connecting map `Sheaf.H.δ`. The first map is injective in degree zero.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe w u

namespace AlgebraicGeometry.Scheme.EtaleCohomology.CompactSupport

attribute [local instance] hasSheafifyLarge

variable {U Z X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
  (i : Z ⟶ X) [IsClosedImmersion i] (hcomp : Set.range j = (Set.range i)ᶜ)
  [HasExt.{w} (AbelianSheaf.{u, u + 1} X)] (G : AbelianSheaf.{u, u + 1} X)

/-- The connecting map `H^{n₀}(X, i_* i^* G) → H^{n₁}_c(U, j^* G)` of the original
open-closed localization sequence. -/
def localizationδ (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁) :
    Sheaf.H.{w} ((directImage i).obj ((inverseImage i).obj G)) n₀ →+
      H j ((inverseImage j).obj G) n₁ :=
  Sheaf.H.δ (abelianLocalization_shortExact j i hcomp G) n₀ n₁ h

/-- The long exact sequence `H^{n₀}_c(U, j^* G) → H^{n₀}(X, G) → H^{n₀}(X, i_* i^* G) →
H^{n₁}_c(U, j^* G) → H^{n₁}(X, G) → H^{n₁}(X, i_* i^* G)` of the original sequence. -/
abbrev localizationSequence (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁) :
    ComposableArrows AddCommGrpCat.{w} 5 :=
  Sheaf.H.longSequence (abelianLocalization_shortExact j i hcomp G) n₀ n₁ h

theorem localizationSequence_exact (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁) :
    (localizationSequence j i hcomp G n₀ n₁ h).Exact :=
  Sheaf.H.longSequence_exact _ n₀ n₁ h

include hcomp in
/-- Exactness at `H^r(X, G)`: the kernel of the original unit map is the image of the counit
map. -/
theorem exact_counitMap_unitMap (r : ℕ) :
    Function.Exact (counitMap j G r)
      (Sheaf.H.map ((inverseImageAdjunction i).unit.app G) r) :=
  (ShortComplex.ab_exact_iff_function_exact _).mp
    (Sheaf.H.longSequence_exact₂' (abelianLocalization_shortExact j i hcomp G) r)

/-- Exactness at `H^{n₀}(X, i_* i^* G)`. -/
theorem exact_unitMap_localizationδ (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁) :
    Function.Exact (Sheaf.H.map ((inverseImageAdjunction i).unit.app G) n₀)
      (localizationδ j i hcomp G n₀ n₁ h) :=
  (ShortComplex.ab_exact_iff_function_exact _).mp
    (Sheaf.H.longSequence_exact₃' (abelianLocalization_shortExact j i hcomp G) n₀ n₁ h)

/-- Exactness at `H^{n₁}_c(U, j^* G)`. -/
theorem exact_localizationδ_counitMap (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁) :
    Function.Exact (localizationδ j i hcomp G n₀ n₁ h) (counitMap j G n₁) :=
  (ShortComplex.ab_exact_iff_function_exact _).mp
    (Sheaf.H.longSequence_exact₁' (abelianLocalization_shortExact j i hcomp G) n₀ n₁ h)

include hcomp in
/-- The counit map is injective in degree zero, since the original counit is a monomorphism. -/
theorem counitMap_zero_injective : Function.Injective (counitMap j G 0) := by
  have : Mono ((etaleLowerShriekAdjunction j).counit.app G) :=
    (abelianLocalization_shortExact j i hcomp G).mono_f
  exact Abelian.Ext.postcomp_mk₀_injective_of_mono _ _

end AlgebraicGeometry.Scheme.EtaleCohomology.CompactSupport
