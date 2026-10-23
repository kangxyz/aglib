/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Finite.LocalDecomposition

/-! # The actual disjoint open cover by local components -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Finite

universe u v

variable (A : Type v) [CommRing A] (R : Type u) [CommRing R]
  [HenselianLocalRing R] [Algebra R A] [Module.Finite R A]

include R in
/-- The literal localization inclusions are open immersions. -/
theorem localComponentInclusion_isOpenImmersion (p : MaximalSpectrum A) :
    IsOpenImmersion (localComponentInclusion A p) := by
  let := localDecompositionMap_isIso A R
  rw [← ι_localDecompositionMap]
  infer_instance

/-- The actual local-component cover, retaining literal localization maps. -/
abbrev localComponentOpenCover : (Spec (.of A)).OpenCover := by
  let := localDecompositionMap_isIso A R
  exact ((sigmaOpenCover (localComponents A)).pushforwardIso
    (localDecompositionMap A)).copy (MaximalSpectrum A) (localComponents A)
      (localComponentInclusion A) (Equiv.refl _) (fun _ => Iso.refl _)
      (fun p => by
        change localComponentInclusion A p =
          𝟙 _ ≫ (Sigma.ι (localComponents A) p ≫ localDecompositionMap A)
        exact (ι_localDecompositionMap A p).symm.trans (Category.id_comp _).symm)

@[simp]
lemma localComponentOpenCover_f (p : MaximalSpectrum A) :
    (localComponentOpenCover A R).f p = localComponentInclusion A p := rfl

include R in
/-- Any test scheme mapping to two different components is empty. -/
theorem isEmpty_of_commSq_localComponentInclusion {p q : MaximalSpectrum A}
    {Z : Scheme.{v}} {a : Z ⟶ localComponents A p} {b : Z ⟶ localComponents A q}
    (h : CommSq a b (localComponentInclusion A p) (localComponentInclusion A q))
    (hpq : p ≠ q) : IsEmpty Z := by
  let := localDecompositionMap_isIso A R
  apply isEmpty_of_commSq_sigmaι_of_ne (g := localComponents A) (a := a) (b := b) _ hpq
  refine ⟨(cancel_mono (localDecompositionMap A)).mp ?_⟩
  simpa only [Category.assoc, ι_localDecompositionMap] using h.w

include R in
/-- Different local components have empty actual intersection. -/
theorem isEmpty_pullback_localComponentInclusion {p q : MaximalSpectrum A} (hpq : p ≠ q) :
    IsEmpty (pullback (localComponentInclusion A p) (localComponentInclusion A q) : Scheme.{v}) :=
  isEmpty_of_commSq_localComponentInclusion A R ⟨pullback.condition⟩ hpq

end AlgebraicGeometry.Scheme.EtaleCohomology.Finite
