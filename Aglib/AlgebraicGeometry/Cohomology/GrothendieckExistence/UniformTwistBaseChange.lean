/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.GrothendieckExistence.UniformTwist
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.FiniteType.Pushforward

/-!
# Uniform vanishing on the actual projective base-change space

A coherent coefficient constructed on the native fibre product is transferred
along the actual projective base-change isomorphism. Its direct image agrees
with the original projection direct image, via native pushforward composition.
Thus the uniform Serre bound applies without requiring a geometric realization
to be definitionally a module on polynomial projective space.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.ProjectiveSpace
open AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Modules.QuasiCoherent

universe u v

namespace AlgebraicGeometry.Scheme.Cohomology

variable {A B : Type u} [CommRing A] [CommRing B]
  (φ : A →+* B) (ι : Type u)

/-- The original inverse base-change comparison intertwines the original
projective map and the actual pullback projection. -/
@[reassoc (attr := simp)]
theorem projectiveBaseChange_inv_map :
    (baseChangeIso φ ι).inv ≫ ProjectiveSpace.map φ ι =
      pullback.fst (toSpec A ι) (Spec.map (CommRingCat.ofHom φ)) := by
  rw [← baseChangeIso_hom_fst φ ι, Iso.inv_hom_id_assoc]

/-- Native pushforward along the inverse geometric comparison transfers a
coefficient without changing its original direct image to the old base. -/
def projectiveBaseChangePushforwardIso
    (G : (pullback (toSpec A ι) (Spec.map (CommRingCat.ofHom φ))).Modules) :
    (pushforward (ProjectiveSpace.map φ ι)).obj
        ((pushforward (baseChangeIso φ ι).inv).obj G) ≅
      (pushforward (pullback.fst (toSpec A ι) (Spec.map (CommRingCat.ofHom φ)))).obj G :=
  (pushforwardComp (baseChangeIso φ ι).inv (ProjectiveSpace.map φ ι)).app G ≪≫
    (pushforwardCongr (projectiveBaseChange_inv_map φ ι)).app G

/-- One coherent coefficient on the actual fibre product supplies the same
single Serre bound for every retract of its original projection direct image.
No flatness of the coefficient-ring map is assumed. -/
theorem projectiveSerreVanishing_baseChange_retracts [IsNoetherianRing B]
    (n : ℕ) (e : ι ≃ Fin (n + 1))
    (G : (pullback (toSpec A ι) (Spec.map (CommRingCat.ofHom φ))).Modules)
    (hG : affineLocallyFiniteType _ G)
    {J : Type v} (M : J → (ProjectiveSpace A ι).Modules)
    (inc : ∀ j, M j ⟶
      (pushforward (pullback.fst (toSpec A ι) (Spec.map (CommRingCat.ofHom φ)))).obj G)
    (pr : ∀ j,
      (pushforward (pullback.fst (toSpec A ι) (Spec.map (CommRingCat.ofHom φ)))).obj G ⟶ M j)
    (h : ∀ j, inc j ≫ pr j = 𝟙 (M j)) :
    ∃ C : ℕ, ∀ d : ℤ, (C : ℤ) ≤ d → ∀ j : J, ∀ q : ℕ, q ≠ 0 →
      Subsingleton (Sheaf.H.{u + 1} (moduleAddSheaf (ProjectiveSpace A ι)
        ((moduleTensorLeftFunctor (ProjectiveSpace A ι) (twistingSheaf A ι d)).obj
          (M j))) q) := by
  let N := (pushforward (baseChangeIso φ ι).inv).obj G
  have hN : affineLocallyFiniteType (ProjectiveSpace B ι) N :=
    FiniteMorphism.affineLocallyFiniteType_pushforward (baseChangeIso φ ι).inv hG
  let a := projectiveBaseChangePushforwardIso φ ι G
  exact projectiveSerreVanishing_retracts φ ι n e N hN M
    (fun j => inc j ≫ a.inv) (fun j => a.hom ≫ pr j) (by
      intro j
      rw [Category.assoc, Iso.inv_hom_id_assoc, h])

end AlgebraicGeometry.Scheme.Cohomology
