/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.GrothendieckExistence.OpenOverlapCoordinates

/-! # Original ambient overlap equations in native restriction coordinates -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.Modules.Coherent

universe u

/-- Converting an actual local inclusion to restriction coordinates commutes
with the original iterated restriction comparison. -/
@[reassoc]
theorem reconstructionInclusion_iteratedComparison {X Y Z : Scheme.{u}}
    (q : Z ⟶ Y) (p : Y ⟶ X) [IsOpenImmersion q] [IsOpenImmersion p]
    {G : Y.Modules} {M : X.Modules} (s : G ⟶ (pullback p).obj M) :
    (restrictFunctor q).map (s ≫ (restrictFunctorIsoPullback p).inv.app M) ≫
        (iteratedRestrictIsoPullback q p).hom.app M =
      (restrictFunctorIsoPullback q).hom.app G ≫ (pullback q).map s := by
  change (restrictFunctor q).map (s ≫ _) ≫
    ((restrictFunctor q).map ((restrictFunctorIsoPullback p).hom.app M) ≫
      (restrictFunctorIsoPullback q).hom.app ((pullback p).obj M)) = _
  rw [← Functor.map_comp_assoc]
  simp only [Category.assoc, Iso.inv_hom_id_app, Category.comp_id]
  exact (restrictFunctorIsoPullback q).hom.naturality s

/-- The pullback overlap comparison is conjugate to the exact native gluer's
restriction comparison on every ambient module, without quasicoherence. -/
@[reassoc]
theorem reconstructionOverlapPullbackIso_comparison {X U V : Scheme.{u}}
    (p : U ⟶ X) (q : V ⟶ X) [IsOpenImmersion p] [IsOpenImmersion q]
    (M : X.Modules) :
    (overlapRestrictIso p q).hom.app M ≫
        (iteratedRestrictIsoPullback (pullback.snd p q) q).hom.app M =
      (iteratedRestrictIsoPullback (pullback.fst p q) p).hom.app M ≫
        (reconstructionOverlapPullbackIso p q).hom.app M := by
  simp only [reconstructionOverlapPullbackIso, Iso.trans_hom, Iso.symm_hom,
    NatTrans.comp_app, Iso.hom_inv_id_app_assoc]

/-- An actual overlap equation in geometric pullback coordinates gives exactly
the overlap equation consumed by finite-cover coherent subobject gluing. -/
theorem reconstructionOverlap_restrict_compatible {X U V : Scheme.{u}}
    (p : U ⟶ X) (q : V ⟶ X) [IsOpenImmersion p] [IsOpenImmersion q]
    {G₁ : U.Modules} {G₂ : V.Modules} {M : X.Modules}
    (s₁ : G₁ ⟶ (pullback p).obj M) (s₂ : G₂ ⟶ (pullback q).obj M)
    (e : (pullback (pullback.fst p q)).obj G₁ ≅
      (pullback (pullback.snd p q)).obj G₂)
    (he : (pullback (pullback.fst p q)).map s₁ ≫
        (reconstructionOverlapPullbackIso p q).hom.app M =
      e.hom ≫ (pullback (pullback.snd p q)).map s₂) :
    (restrictFunctor (pullback.fst p q)).map
        (s₁ ≫ (restrictFunctorIsoPullback p).inv.app M) ≫
      (overlapRestrictIso p q).hom.app M =
    ((restrictFunctorIsoPullback (pullback.fst p q)).app G₁ ≪≫ e ≪≫
      ((restrictFunctorIsoPullback (pullback.snd p q)).app G₂).symm).hom ≫
        (restrictFunctor (pullback.snd p q)).map
          (s₂ ≫ (restrictFunctorIsoPullback q).inv.app M) := by
  apply (cancel_mono
    ((iteratedRestrictIsoPullback (pullback.snd p q) q).hom.app M)).mp
  rw [Category.assoc, reconstructionOverlapPullbackIso_comparison,
    ← Category.assoc, reconstructionInclusion_iteratedComparison,
    Category.assoc, he]
  rw [Category.assoc, reconstructionInclusion_iteratedComparison]
  simp only [Iso.trans_hom, Iso.symm_hom, Iso.app_hom, Iso.app_inv,
    Category.assoc, Iso.inv_hom_id_app_assoc]

end AlgebraicGeometry.Scheme.Modules.Coherent
