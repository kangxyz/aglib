/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.GrothendieckExistence.BoundedReconstructionEffectivity

/-! # Bounded coherent reconstruction on a quasi-compact locally Noetherian scheme

A bounded original formal comparison to an actual coherent target is sufficient
for global coherent reconstruction. The finite affine cover, all overlap
isomorphisms, and the coherent gluing are constructed. No realization, gluing,
separatedness, or faithful-completion premise is imposed.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.Modules.Coherent

universe u
variable {X : Scheme.{u}} [IsLocallyNoetherian X] [CompactSpace X]
  {K : X.IdealSheafData} {F : AdicSystem X K} {H : X.CoherentSheaf}

/-- Global bounded coherent reconstruction retains the specified original
formal map and exactly the same bound on both ordinary algebraic defects. -/
theorem exists_boundedCoherentReconstruction
    (α : F ⟶ (completionFunctor X K).obj H)
    (t : ℕ) (h : AdicSystem.DefectsKilled K t α) :
    ∃ (G : X.CoherentSheaf) (a : G ⟶ H)
      (β : (completionFunctor X K).obj G ≅ F),
      β.hom ≫ α = (completionFunctor X K).map a ∧
        killedByIdealSheaf (K ^ t) (kernel a.hom) ∧
          killedByIdealSheaf (K ^ t) (cokernel a.hom) := by
  let U := X.affineOpenCover
  let V := U.openCover.finiteSubcover
  let B (i : V.I₀) : CommRingCat.{u} := U.X (U.openCover.idx i.val)
  let p (i : V.I₀) : Spec (B i) ⟶ X := V.f i
  let (i : V.I₀) : IsOpenImmersion (p i) := inferInstanceAs (IsOpenImmersion (V.f i))
  let (i : V.I₀) : IsNoetherianRing (B i) :=
    isLocallyNoetherian_Spec.mp (isLocallyNoetherian_of_isOpenImmersion (p i))
  exact exists_boundedCoherentReconstruction_on_cover B p V.exists_eq α t h

end AlgebraicGeometry.Scheme.Modules.Coherent
