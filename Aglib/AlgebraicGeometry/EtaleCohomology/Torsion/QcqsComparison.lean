/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Continuity.QcqsCoefficientContinuity
public import Aglib.AlgebraicGeometry.EtaleCohomology.Torsion.Comparison
public import Mathlib.CategoryTheory.Category.ULift

/-!
# Torsion comparison on qcqs schemes

Fixed-scheme coefficient continuity supplies preservation of sequential colimits
by the original cohomology functors. The indexing category is resized through
the native equivalence with `AsSmall`, so the result keeps independent Ext
universes without assuming larger colimits in the cohomology value category.

For a morphism between qcqs schemes, all-degree comparison for genuine prime
module coefficients therefore implies the original pullback comparison for
every torsion coefficient. Prime comparison remains the application hypothesis.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.EtaleCohomology

universe u e e'

attribute [local instance] hasSheafifyLarge

/-- The original cohomology functor preserves a filtered coefficient colimit
of the site universe whenever its value category has that colimit shape. -/
theorem qcqsCohomologyFunctor_preservesColimitsOfShape
    (X : Scheme.{u}) [CompactSpace X] [QuasiSeparatedSpace X]
    [HasExt.{e} (AbelianSheaf.{u, u + 1} X)]
    {I : Type (u + 1)} [SmallCategory I] [IsFiltered I]
    [HasColimitsOfShape I AddCommGrpCat.{e}] (n : ℕ) :
    PreservesColimitsOfShape I (cohomologyFunctor.{u, e} X n) where
  preservesColimit {G} := by
    let : IsIso (colimit.post G (cohomologyFunctor.{u, e} X n)) :=
      Continuity.isIso_qcqsCoefficientColimitComparison.{u, e} G n
    exact preservesColimit_of_isIso_post (cohomologyFunctor.{u, e} X n) G

/-- Sequential coefficient continuity keeps an arbitrary independent Ext universe.
The larger indexing category has colimits by equivalence with the original ℕ. -/
theorem qcqsCohomologyFunctor_preservesSequentialColimits
    (X : Scheme.{u}) [CompactSpace X] [QuasiSeparatedSpace X]
    [HasExt.{e} (AbelianSheaf.{u, u + 1} X)] (n : ℕ) :
    PreservesColimitsOfShape ℕ (cohomologyFunctor.{u, e} X n) := by
  let E : ℕ ≌ AsSmall.{u + 1} ℕ := AsSmall.equiv (C := ℕ)
  let : HasColimitsOfShape (AsSmall.{u + 1} ℕ) AddCommGrpCat.{e} :=
    hasColimitsOfShape_of_equivalence E
  let : PreservesColimitsOfShape (AsSmall.{u + 1} ℕ)
      (cohomologyFunctor.{u, e} X n) :=
    qcqsCohomologyFunctor_preservesColimitsOfShape X n
  exact preservesColimitsOfShape_of_equiv E.symm (cohomologyFunctor.{u, e} X n)

/-- On qcqs schemes, actual prime module comparison suffices for every torsion sheaf. -/
theorem cohomologyPullback_bijective_of_prime_modules_qcqs
    {X S : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
    [CompactSpace S] [QuasiSeparatedSpace S]
    [HasExt.{e} (AbelianSheaf.{u, u + 1} X)]
    [HasExt.{e'} (AbelianSheaf.{u, u + 1} S)] (f : S ⟶ X)
    (hprime : ∀ (p : ℕ), p.Prime →
      ∀ M : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (ZMod p)),
      ∀ n, Function.Bijective (cohomologyPullback.{u, e, e'} f
        ((sheafCompose X.smallEtaleTopology
          (forget₂ (ModuleCat.{u + 1} (ZMod p)) AddCommGrpCat.{u + 1})).obj M) n))
    (F : AbelianSheaf.{u, u + 1} X) (hF : IsTorsion X F) :
    ∀ n, Function.Bijective (cohomologyPullback.{u, e, e'} f F n) := by
  let (n : ℕ) : PreservesColimitsOfShape ℕ (cohomologyFunctor.{u, e} X n) :=
    qcqsCohomologyFunctor_preservesSequentialColimits X n
  let (n : ℕ) : PreservesColimitsOfShape ℕ (cohomologyFunctor.{u, e'} S n) :=
    qcqsCohomologyFunctor_preservesSequentialColimits S n
  exact cohomologyPullback_bijective_of_prime_modules f hprime F hF

end AlgebraicGeometry.Scheme.EtaleCohomology
