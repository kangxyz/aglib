/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.DerivedCategory.Ext.CogeneratorComparison
public import Aglib.AlgebraicGeometry.EtaleCohomology.Proper.Local.FiniteCogenerators
public import Aglib.AlgebraicGeometry.EtaleCohomology.Torsion.ZModCohomology

/-! # Original local comparison from geometric finite cogenerators

The actual comparison on genuine module coefficients reduces to original
finite constant annihilator tests. The coefficient stages are geometrically
constructible and ambient finitely presentable, including on the original
affine opens. Their finite constant product embeddings remain an explicit
geometric input. No comparison property occurs in the definition of a stage
or of its geometric test target.

The proof supplies genuine module injectives and their original underlying
abelian cohomological acyclicity. The original cocones and preservation of
their source/target cohomology remain explicit. This is a local criterion,
not an unconditional projective-line or proper-base-change theorem.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open AlgebraicGeometry.Scheme.EtaleCohomology.Constructible.FiniteCogenerators

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Proper

universe u e e' v w

attribute [local instance] hasSheafifyLarge TorsionZMod.hasSheafifyStandard

variable (X : Scheme.{u}) (n : ℕ)

/-- The geometric and ambient finite conditions used by the original
positive presentation, independent of any desired cohomology comparison. -/
def IsConstructibleFiniteStage (M : Reduction.ZModSheaf X n) : Prop :=
  Constructible.IsConstructible ((Reduction.zmodUnderlying X n).obj M) ∧
    IsFinitelyPresentable.{u + 1} ((Reduction.zmodUnderlying X n).obj M) ∧
      ∀ V : X.affineOpens, IsFinitelyPresentable.{u + 1}
        ((inverseImage V.1.ι).obj ((Reduction.zmodUnderlying X n).obj M))

/-- The native constant integer coefficient representing original cohomology. -/
abbrev cohomologySource : AbelianSheaf.{u, u + 1} X :=
  (constantSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
    (AddCommGrpCat.of (ULift.{u + 1} ℤ))

variable {X} {S : Scheme.{u}} (i : S ⟶ X)
  [HasExt.{e} (AbelianSheaf.{u, u + 1} X)]
  [HasExt.{e'} (AbelianSheaf.{u, u + 1} S)]

/-- Actual geometric finite cogenerators and original coefficient colimits
reduce bijectivity of the original pullback to the finite annihilator tests.
The source and target Ext universes are independently supplied. -/
theorem cohomologyPullback_bijective_of_finiteConstantAnnihilator_tests
    {J : Reduction.ZModSheaf X n → Type v}
    [∀ M, Category.{w} (J M)]
    [∀ M, HasColimitsOfShape (J M) AddCommGrpCat.{max e e'}]
    [∀ M, (colim : (J M ⥤ AddCommGrpCat.{max e e'}) ⥤
      AddCommGrpCat.{max e e'}).PreservesMonomorphisms]
    (K : ∀ M, J M ⥤ Reduction.ZModSheaf X n)
    (κ : ∀ M, K M ⟶ (Functor.const (J M)).obj M)
    (hc : ∀ M, IsColimit (Cocone.mk M (κ M)))
    (hstage : ∀ M j, IsConstructibleFiniteStage X n ((K M).obj j))
    (hfinite : ∀ M, IsConstructibleFiniteStage X n M →
      Nonempty (FiniteConstantProductEmbedding ((Reduction.zmodUnderlying X n).obj M)))
    (hsource : ∀ M, PreservesColimit (K M)
      (Reduction.zmodUnderlying X n ⋙ extFunctorObj (cohomologySource X) 0))
    (hcoh : ∀ M q, PreservesColimit (K M)
      (Reduction.zmodUnderlying X n ⋙ inverseImage i ⋙
        extFunctorObj (cohomologySource S) q))
    (hzero : ∀ N, IsFiniteConstantAnnihilator X n N →
      Function.Injective (cohomologyPullback i ((Reduction.zmodUnderlying X n).obj N) 0))
    (htest : ∀ N, IsFiniteConstantAnnihilator X n N → ∀ q,
      Function.Surjective (cohomologyPullback i ((Reduction.zmodUnderlying X n).obj N) q))
    (M : Reduction.ZModSheaf X n) (q : ℕ) :
    Function.Bijective (cohomologyPullback i ((Reduction.zmodUnderlying X n).obj M) q) := by
  let : EnoughInjectives (Reduction.ZModSheaf X n) :=
    TorsionZMod.enoughInjectivesStandard X.smallEtaleTopology n
  have : (Reduction.zmodUnderlying X n).Additive :=
    { map_add := by
        intro A B a b
        apply Sheaf.hom_ext
        apply NatTrans.ext
        funext V
        rfl }
  let : PreservesFiniteLimits (Reduction.zmodUnderlying X n) :=
    zmodUnderlying_preservesFiniteLimits X n
  let : PreservesFiniteColimits (Reduction.zmodUnderlying X n) :=
    zmodUnderlying_preservesFiniteColimits X n
  apply (inverseImage i).extPrecompMap_bijective_on_image_of_cogenerator_tests
    (Reduction.zmodUnderlying X n)
    (((inverseImageConstantIso i).app (AddCommGrpCat.of (ULift.{u + 1} ℤ))).inv)
    (IsConstructibleFiniteStage X n) (IsFiniteConstantAnnihilator X n)
    K κ hc hstage ?_ hsource hcoh ?_ hzero htest M q
  · intro N hN
    obtain ⟨t⟩ := hfinite N hN
    exact exists_mono_finiteConstantAnnihilator X n N t
  · intro I _ k
    exact zmodUnderlying_injective_cohomology_subsingleton X n I k

end AlgebraicGeometry.Scheme.EtaleCohomology.Proper
