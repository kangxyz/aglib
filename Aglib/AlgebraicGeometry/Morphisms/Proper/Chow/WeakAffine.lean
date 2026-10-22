/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Morphisms.Proper.Chow.Weak

/-!
# Weak Chow over an original affine base

Transport the actual projective-product modification along the affine
base's canonical spectrum isomorphism, retaining the original over object.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Scheme.Chow

/-- A separated finite-type object over a Noetherian affine scheme admits
an actual proper surjective modification immersive in a proper object. -/
theorem exists_immersion_proper_modification {S : Scheme.{u}}
    [IsAffine S] [IsLocallyNoetherian S] (X : Over S)
    [IsSeparated X.hom] [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] :
    ∃ (Y P : Over S) (p : Y ⟶ X) (q : Y ⟶ P),
      IsProper p.left ∧ Surjective p.left ∧ IsImmersion q.left ∧ IsProper P.hom := by
  let : IsNoetherianRing Γ(S, ⊤) :=
    IsLocallyNoetherian.component_noetherian ⟨⊤, isAffineOpen_top S⟩
  obtain ⟨m, σ, hσ, Y, p, q, V, h, hp, hs, hq, -, -, -⟩ :=
    exists_immersion_projective_product_modification Γ(S, ⊤) (X.hom ≫ S.isoSpec.hom)
  let (k : Fin m) : Fintype (σ k) := hσ k
  have (k : Fin m) : IsProper (Over.mk (ProjectiveSpace.toSpec Γ(S, ⊤) (Option (σ k)))).hom := by
    dsimp only [Over.mk_hom]
    infer_instance
  have : IsProper (projectiveProductOver Γ(S, ⊤) σ).hom := isProper_finiteProductOver _
  let P : Over S := Over.mk ((projectiveProductOver Γ(S, ⊤) σ).hom ≫ S.isoSpec.inv)
  have h' : p ≫ X.hom = q ≫ P.hom := by
    apply (cancel_mono S.isoSpec.hom).mp
    simpa only [P, Over.mk_hom, Category.assoc, Iso.inv_hom_id, Category.comp_id] using h
  refine ⟨Over.mk (p ≫ X.hom), P, Over.homMk p, Over.homMk q h'.symm, hp, hs, hq, ?_⟩
  dsimp only [P, Over.mk_hom]
  infer_instance

end AlgebraicGeometry.Scheme.Chow
