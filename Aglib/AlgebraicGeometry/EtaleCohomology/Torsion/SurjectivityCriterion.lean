/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.DerivedCategory.Ext.EffacementComparison
public import Aglib.AlgebraicGeometry.EtaleCohomology.Torsion.QcqsComparison
public import Aglib.AlgebraicGeometry.EtaleCohomology.Torsion.ZModCohomology

/-!
# Surjectivity tests for original torsion cohomology pullback

Genuine `ZMod n`-module injectives have acyclic original underlying abelian
coefficients. Consequently, degree-zero injectivity and lower-degree
surjectivity force injectivity in the next degree for the actual pullback.
On qcqs schemes, all-degree surjectivity for genuine prime-module
coefficients, together with degree-zero injectivity, suffices for every
internally torsion coefficient. The geometric surjectivity tests remain
explicit; no proper-base-change or pulled-back injective acyclicity theorem
is assumed or asserted here.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.EtaleCohomology

universe u e e'

attribute [local instance] hasSheafifyLarge

variable {X S : Scheme.{u}}
  [HasExt.{e} (AbelianSheaf.{u, u + 1} X)]
  [HasExt.{e'} (AbelianSheaf.{u, u + 1} S)]

/-- Original prime-power or general-modulus pullback is injective in degree `q`
when it is injective in degree zero and surjective below `q`. -/
theorem zmodCohomologyPullback_injective_of_surjective_below (f : S ⟶ X) (n q : ℕ)
    (h₀ : ∀ M : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (ZMod n)),
      Function.Injective (cohomologyPullback.{u, e, e'} f
        ((sheafCompose X.smallEtaleTopology
          (forget₂ (ModuleCat.{u + 1} (ZMod n)) AddCommGrpCat.{u + 1})).obj M) 0))
    (hs : ∀ (M : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (ZMod n))) (k : ℕ),
      k < q → Function.Surjective (cohomologyPullback.{u, e, e'} f
        ((sheafCompose X.smallEtaleTopology
          (forget₂ (ModuleCat.{u + 1} (ZMod n)) AddCommGrpCat.{u + 1})).obj M) k))
    (M : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (ZMod n))) :
    Function.Injective (cohomologyPullback.{u, e, e'} f
      ((sheafCompose X.smallEtaleTopology
        (forget₂ (ModuleCat.{u + 1} (ZMod n)) AddCommGrpCat.{u + 1})).obj M) q) := by
  let : HasSheafify X.smallEtaleTopology (ModuleCat.{u + 1} (ZMod n)) :=
    TorsionZMod.hasSheafifyStandard.{u + 1, u} X.smallEtaleTopology n
  let U := sheafCompose X.smallEtaleTopology
    (forget₂ (ModuleCat.{u + 1} (ZMod n)) AddCommGrpCat.{u + 1})
  let : PreservesFiniteLimits U := zmodUnderlying_preservesFiniteLimits X n
  let : PreservesFiniteColimits U := zmodUnderlying_preservesFiniteColimits X n
  let : U.Additive := { map_add := by intro Y Z a b; ext W x; rfl }
  let : EnoughInjectives (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (ZMod n))) :=
    TorsionZMod.enoughInjectivesStandard.{u + 1, u} X.smallEtaleTopology n
  exact (inverseImage f).extPrecompMap_injective_on_image_of_surjective_below U
    (((inverseImageConstantIso f).app (AddCommGrpCat.of (ULift.{u + 1} ℤ))).inv)
    (fun I _ k => zmodUnderlying_injective_cohomology_subsingleton X n I k)
    h₀ q hs M

/-- Surjectivity alone supplies higher injectivity for genuine module coefficients,
provided the original degree-zero map is injective. -/
theorem zmodCohomologyPullback_bijective_of_surjective (f : S ⟶ X) (n : ℕ)
    (h₀ : ∀ M : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (ZMod n)),
      Function.Injective (cohomologyPullback.{u, e, e'} f
        ((sheafCompose X.smallEtaleTopology
          (forget₂ (ModuleCat.{u + 1} (ZMod n)) AddCommGrpCat.{u + 1})).obj M) 0))
    (hs : ∀ (M : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (ZMod n))) (q : ℕ),
      Function.Surjective (cohomologyPullback.{u, e, e'} f
        ((sheafCompose X.smallEtaleTopology
          (forget₂ (ModuleCat.{u + 1} (ZMod n)) AddCommGrpCat.{u + 1})).obj M) q))
    (M : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (ZMod n))) (q : ℕ) :
    Function.Bijective (cohomologyPullback.{u, e, e'} f
      ((sheafCompose X.smallEtaleTopology
        (forget₂ (ModuleCat.{u + 1} (ZMod n)) AddCommGrpCat.{u + 1})).obj M) q) :=
  ⟨zmodCohomologyPullback_injective_of_surjective_below f n q h₀
      (fun N k _ => hs N k) M,
    hs M q⟩

/-- On qcqs schemes, degree-zero injectivity and all-degree genuine prime-module
surjectivity suffice for original comparison of every internally torsion coefficient. -/
theorem cohomologyPullback_bijective_of_prime_modules_surjective_qcqs
    [CompactSpace X] [QuasiSeparatedSpace X] [CompactSpace S] [QuasiSeparatedSpace S]
    (f : S ⟶ X)
    (h₀ : ∀ (p : ℕ), p.Prime →
      ∀ M : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (ZMod p)),
      Function.Injective (cohomologyPullback.{u, e, e'} f
        ((sheafCompose X.smallEtaleTopology
          (forget₂ (ModuleCat.{u + 1} (ZMod p)) AddCommGrpCat.{u + 1})).obj M) 0))
    (hs : ∀ (p : ℕ), p.Prime →
      ∀ (M : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (ZMod p))) (q : ℕ),
      Function.Surjective (cohomologyPullback.{u, e, e'} f
        ((sheafCompose X.smallEtaleTopology
          (forget₂ (ModuleCat.{u + 1} (ZMod p)) AddCommGrpCat.{u + 1})).obj M) q))
    (F : AbelianSheaf.{u, u + 1} X) (hF : IsTorsion X F) :
    ∀ q, Function.Bijective (cohomologyPullback.{u, e, e'} f F q) :=
  cohomologyPullback_bijective_of_prime_modules_qcqs f
    (fun p hp M q => zmodCohomologyPullback_bijective_of_surjective
      f p (h₀ p hp) (hs p hp) M q) F hF

end AlgebraicGeometry.Scheme.EtaleCohomology
