/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.SingleHomology
public import Aglib.Algebra.Homology.DerivedCategory.Plus.SingleTriangle
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor

/-!
# Original right-derived maps in a short exact sequence

The actual short-exact single triangle and its mapped homology sequence give
exactness for the native natural-degree right-derived maps, even after an
exact, not necessarily faithful, postfunctor. An epimorphism in the preceding
degree kills the connecting map and identifies the next original coefficient
with the actual kernel. Degree zero uses the native left-exact normalization.
-/

@[expose] public noncomputable section

universe u v u' v' u'' v'' w w'

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

namespace CategoryTheory.Functor

variable {A : Type u} [Category.{v} A] [Abelian A] [EnoughInjectives A]
  [HasDerivedCategory.{w} A]
  {B : Type u'} [Category.{v'} B] [Abelian B] [HasDerivedCategory.{w'} B]
  {D : Type u''} [Category.{v''} D] [Abelian D]
  (F : A ⥤ B) [F.Additive] (E : B ⥤ D) [E.Additive]
  [PreservesFiniteLimits E] [PreservesFiniteColimits E]
  (S : ShortComplex A) (hS : S.ShortExact)

/-- The original right-derived functor is additive through its canonical
single-homology normalization. -/
instance rightDerived_additive (n : ℕ) : (F.rightDerived n).Additive :=
  additive_of_iso (F.rightDerivedSingleHomologyIso n).symm

include hS in
/-- Exactness for the original two mapped coefficient arrows. -/
theorem rightDerivedMap_exact (n : ℕ) :
    ((S.map (F.rightDerived n)).map E).Exact := by
  let T := DerivedCategory.Plus.ι.mapTriangle.obj
    (F.rightDerivedFunctorPlus.mapTriangle.obj hS.singleTrianglePlus)
  have hT : T ∈ distTriang (DerivedCategory B) :=
    DerivedCategory.Plus.ι.map_distinguished _
      (F.rightDerivedFunctorPlus.map_distinguished _ hS.singleTrianglePlus_distinguished)
  let e := isoWhiskerRight (F.rightDerivedSingleHomologyIso n) E
  have h := (DerivedCategory.HomologySequence.exact₂ T hT (n : ℤ)).map E
  exact ShortComplex.exact_of_iso (S.mapNatIso e).symm h

include hS in
/-- An epimorphism in the preceding degree annihilates the actual connecting
map, so the next original coefficient inclusion is a monomorphism. -/
theorem rightDerivedMap_mono_succ_of_epi (n : ℕ)
    [Epi (E.map ((F.rightDerived n).map S.g))] :
    Mono (E.map ((F.rightDerived (n + 1)).map S.f)) := by
  let T := DerivedCategory.Plus.ι.mapTriangle.obj
    (F.rightDerivedFunctorPlus.mapTriangle.obj hS.singleTrianglePlus)
  have hT : T ∈ distTriang (DerivedCategory B) :=
    DerivedCategory.Plus.ι.map_distinguished _
      (F.rightDerivedFunctorPlus.map_distinguished _ hS.singleTrianglePlus_distinguished)
  let e := isoWhiskerRight (F.rightDerivedSingleHomologyIso n) E
  have : Epi (E.map ((DerivedCategory.homologyFunctor B (n : ℤ)).map T.mor₂)) := by
    change Epi (((DerivedCategory.Plus.singleFunctor A 0 ⋙ F.rightDerivedFunctorPlus ⋙
      DerivedCategory.Plus.homologyFunctor B (n : ℤ)) ⋙ E).map S.g)
    have : Epi ((F.rightDerived n ⋙ E).map S.g) :=
      inferInstanceAs (Epi (E.map ((F.rightDerived n).map S.g)))
    exact epi_of_epi_fac (e.hom.naturality S.g).symm
  have hδ : E.map (DerivedCategory.HomologySequence.δ T (n : ℤ) (n + 1 : ℕ) (by omega)) = 0 := by
    apply (cancel_epi (E.map ((DerivedCategory.homologyFunctor B (n : ℤ)).map T.mor₂))).mp
    rw [← E.map_comp,
      DerivedCategory.HomologySequence.comp_δ T hT (n : ℤ) (n + 1 : ℕ) (by omega),
      E.map_zero, comp_zero]
  have h₁ := (DerivedCategory.HomologySequence.exact₁ T hT
    (n : ℤ) (n + 1 : ℕ) (by omega)).map E
  have : Mono (E.map ((DerivedCategory.homologyFunctor B (n + 1 : ℕ)).map T.mor₁)) :=
    h₁.mono_g_iff.mpr hδ
  let e' := isoWhiskerRight (F.rightDerivedSingleHomologyIso (n + 1)) E
  have : Mono (((DerivedCategory.Plus.singleFunctor A 0 ⋙ F.rightDerivedFunctorPlus ⋙
      DerivedCategory.Plus.homologyFunctor B (n + 1 : ℕ)) ⋙ E).map S.f) :=
    inferInstanceAs (Mono (E.map
      ((DerivedCategory.homologyFunctor B (n + 1 : ℕ)).map T.mor₁)))
  exact mono_of_mono_fac (e'.hom.naturality S.f)

/-- The next original coefficient is the native kernel, after an exact
postfunctor, whenever the preceding original quotient map is epi. -/
def rightDerivedKernelIsoOfEpi (n : ℕ)
    [Epi (E.map ((F.rightDerived n).map S.g))] :
    E.obj ((F.rightDerived (n + 1)).obj S.X₁) ≅
      Limits.kernel (E.map ((F.rightDerived (n + 1)).map S.g)) := by
  let : Mono ((S.map (F.rightDerived (n + 1))).map E).f :=
    rightDerivedMap_mono_succ_of_epi F E S hS n
  exact (rightDerivedMap_exact F E S hS (n + 1)).fIsKernel.conePointUniqueUpToIso
    (limit.isLimit _)

/-- The isomorphism retains the literal original coefficient inclusion. -/
@[reassoc]
theorem rightDerivedKernelIsoOfEpi_hom_ι (n : ℕ)
    [Epi (E.map ((F.rightDerived n).map S.g))] :
    (rightDerivedKernelIsoOfEpi F E S hS n).hom ≫
      Limits.kernel.ι (E.map ((F.rightDerived (n + 1)).map S.g)) =
        E.map ((F.rightDerived (n + 1)).map S.f) :=
  by
    dsimp only [rightDerivedKernelIsoOfEpi]
    exact IsLimit.conePointUniqueUpToIso_hom_comp _ _ WalkingParallelPair.zero

/-- In degree zero, left exactness supplies the kernel without any preceding
degree or epimorphism assumption. -/
def rightDerivedZeroKernelIso [PreservesFiniteLimits F] :
    E.obj ((F.rightDerived 0).obj S.X₁) ≅ Limits.kernel (E.map ((F.rightDerived 0).map S.g)) := by
  let e := isoWhiskerRight F.rightDerivedZeroIsoSelf E
  let := hS.mono_f
  have : Mono ((F ⋙ E).map S.f) := inferInstance
  let : Mono ((S.map (F.rightDerived 0)).map E).f :=
    mono_of_mono_fac (e.hom.naturality S.f)
  exact (rightDerivedMap_exact F E S hS 0).fIsKernel.conePointUniqueUpToIso (limit.isLimit _)

/-- The degree-zero normalization retains the same original inclusion. -/
@[reassoc]
theorem rightDerivedZeroKernelIso_hom_ι [PreservesFiniteLimits F] :
    (rightDerivedZeroKernelIso F E S hS).hom ≫
      Limits.kernel.ι (E.map ((F.rightDerived 0).map S.g)) = E.map ((F.rightDerived 0).map S.f) :=
  by
    dsimp only [rightDerivedZeroKernelIso]
    exact IsLimit.conePointUniqueUpToIso_hom_comp _ _ WalkingParallelPair.zero

end CategoryTheory.Functor
