/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.GrothendieckExistence.UniformTwistBaseChange
public import Aglib.AlgebraicGeometry.Modules.Coherent.AdicSystem.AssociatedGraded

/-! # One natural-number H¹ bound from an actual realized coproduct -/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.ProjectiveSpace
open AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Modules.QuasiCoherent

namespace AlgebraicGeometry.Scheme.Cohomology

universe u v

/-- A coherent realization of a native coproduct on the actual projective
base change supplies the one uniform H¹ bound needed by compatible generator
lifting. The component splittings are the native coproduct splittings. -/
theorem projective_uniform_h1_of_realized_coproduct
    {A B : Type u} [CommRing A] [CommRing B] [IsNoetherianRing B]
    (φ : A →+* B) (ι : Type u) (n : ℕ) (e : ι ≃ Fin (n + 1))
    {J : Type v} (M : J → (ProjectiveSpace A ι).Modules) [HasCoproduct M]
    (G : (pullback (toSpec A ι) (Spec.map (CommRingCat.ofHom φ))).Modules)
    (hG : affineLocallyFiniteType _ G)
    (eG : (pushforward (pullback.fst (toSpec A ι)
      (Spec.map (CommRingCat.ofHom φ)))).obj G ≅ ∐ M) :
    ∃ C : ℕ, ∀ d : ℕ, C ≤ d → ∀ j : J,
      Subsingleton (Sheaf.H.{u + 1} (moduleAddSheaf (ProjectiveSpace A ι)
        ((moduleTensorLeftFunctor (ProjectiveSpace A ι) (twistingSheaf A ι (d : ℤ))).obj
          (M j))) 1) := by
  let b := Bicone.ofColimitCocone (colimit.isColimit (Discrete.functor M))
  have hb (j : J) : Sigma.ι M j ≫ b.π j = 𝟙 (M j) := bicone_ι_π_self b j
  obtain ⟨C, hC⟩ := projectiveSerreVanishing_baseChange_retracts φ ι n e G hG M
    (fun j => Sigma.ι M j ≫ eG.inv) (fun j => eG.hom ≫ b.π j) (by
      intro j
      rw [Category.assoc, Iso.inv_hom_id_assoc, hb])
  refine ⟨C, fun d hd j => ?_⟩
  exact hC (d : ℤ) (by exact_mod_cast hd) j 1 (by decide)

end AlgebraicGeometry.Scheme.Cohomology
