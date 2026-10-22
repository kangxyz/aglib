/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.GrothendieckExistence.AffineCandidateMonicity

/-! # Uniqueness relative to both original affine bounded projections

Maps into a bounded candidate are determined by their algebraic target map
and all original formal-stage maps. This applies with varying source and target
coefficients, so the uniqueness can enforce both overlap cocycles and original
adic transitions. No completion conservativity is assumed.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.Modules.Coherent

universe u
variable {B : CommRingCat.{u}} [IsNoetherianRing B]
  {K : (Spec B).IdealSheafData} {F : AdicSystem (Spec B) K}
  {H G A : (Spec B).CoherentSheaf}
  (a : G ⟶ H) (β : (completionFunctor (Spec B) K).obj G ≅ F)

/-- A bounded candidate's two original projections determine all maps into it. -/
theorem affineBoundedCandidate_hom_ext (t : ℕ)
    (hk : killedByIdealSheaf (K ^ t) (kernel a.hom))
    (f g : A ⟶ G) (ha : f ≫ a = g ≫ a)
    (hs : ∀ n : ℕ,
      f.hom ≫ (idealSheafQuotientUnit (Spec B) (K ^ n)).app G.obj ≫
        β.hom.hom.app (op n) =
      g.hom ≫ (idealSheafQuotientUnit (Spec B) (K ^ n)).app G.obj ≫
        β.hom.hom.app (op n)) : f = g := by
  obtain ⟨n, hn⟩ := affineCandidateStages_jointly_monic a β t hk
  have := hn
  apply ObjectProperty.hom_ext
  apply (cancel_mono (prod.lift a.hom
    ((idealSheafQuotientUnit (Spec B) (K ^ n)).app G.obj ≫
      β.hom.hom.app (op n)))).mp
  apply prod.hom_ext
  · simpa only [Category.assoc, prod.lift_fst, ObjectProperty.FullSubcategory.comp_hom] using
      congrArg (fun q => q.hom) ha
  · simpa only [Category.assoc, prod.lift_snd] using hs n

end AlgebraicGeometry.Scheme.Modules.Coherent
