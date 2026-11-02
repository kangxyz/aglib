/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Cech.Coproduct
public import Aglib.AlgebraicGeometry.Cohomology.FormalFunctions.ReesCohomologyAffine
public import Aglib.AlgebraicGeometry.Cohomology.FormalFunctions.ReesCohomologySections

/-!
# The original affine coproduct cohomology comparison

The complete comparison retains the three original linear equivalences, including
both their forward and inverse maps. In particular, specializing it does not
choose another inverse or another transported scalar action. The homogeneous
value law is proved before inserting a geometric graded coefficient.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
open CategoryTheory Limits Opposite TopologicalSpace DirectSum

namespace AlgebraicGeometry.Scheme.Cohomology

variable {A : Type u} [CommRing A] {X Y : Scheme.{u}}
  (p : Y ⟶ X) [IsAffineHom p] [CompactSpace X] [X.IsSeparated]
  (G : Y.Modules) [G.IsQuasicoherent] (α : A →+* Γ(X, ⊤))
  {δ : Type} (M : δ → X.Modules) [∀ i, (M i).IsQuasicoherent]
  (e : moduleSectionsPresheaf X α (∐ M) ≅
    moduleSectionsPresheaf X α ((Scheme.Modules.pushforward p).obj G))
  (q : ℕ)

/-- The same three original equivalences, with their original inverse choices. -/
def moduleCohomologyAffineCoproductEquiv :
    letI : ∀ i, Module A (Sheaf.H.{u + 1} (moduleAddSheaf X (M i)) q) :=
      fun i => moduleCohomologyModuleOfHom X α (M i) q
    letI := moduleCohomologyModuleOfHom X α (∐ M) q
    letI := moduleCohomologyModuleOfHom X α ((Scheme.Modules.pushforward p).obj G) q
    letI := moduleCohomologyModuleOfHom Y (p.appTop.hom.comp α) G q
    (⨁ i, Sheaf.H.{u + 1} (moduleAddSheaf X (M i)) q) ≃ₗ[A]
      Sheaf.H.{u + 1} (moduleAddSheaf Y G) q := by
  letI : ∀ i, Module A (Sheaf.H.{u + 1} (moduleAddSheaf X (M i)) q) :=
    fun i => moduleCohomologyModuleOfHom X α (M i) q
  letI := moduleCohomologyModuleOfHom X α (∐ M) q
  letI := moduleCohomologyModuleOfHom X α ((Scheme.Modules.pushforward p).obj G) q
  letI := moduleCohomologyModuleOfHom Y (p.appTop.hom.comp α) G q
  exact
    (moduleCohomologyCoproductEquiv.{u, 0} X α M q).trans
      ((moduleSectionsCohomologyEquiv X α e q).trans
        (moduleCohomologyAffinePushforwardEquiv p G α q))

/-- The whole original forward map, including the scalar-section comparison. -/
theorem moduleCohomologyAffineCoproductEquiv_apply
    (x : ⨁ i, Sheaf.H.{u + 1} (moduleAddSheaf X (M i)) q) :
    letI : ∀ i, Module A (Sheaf.H.{u + 1} (moduleAddSheaf X (M i)) q) :=
      fun i => moduleCohomologyModuleOfHom X α (M i) q
    letI := moduleCohomologyModuleOfHom X α (∐ M) q
    letI := moduleCohomologyModuleOfHom X α ((Scheme.Modules.pushforward p).obj G) q
    letI := moduleCohomologyModuleOfHom Y (p.appTop.hom.comp α) G q
    moduleCohomologyAffineCoproductEquiv p G α M e q x =
      moduleCohomologyMapAlong p (𝟙 ((Scheme.Modules.pushforward p).obj G)) q
        (Sheaf.H.map (moduleSectionsAddSheafMap X α e.hom) q
          (moduleCohomologyCoproductMap.{u, 0} X α M q x)) := rfl

/-- The inverse is literally the original reverse composite, not a new choice. -/
theorem moduleCohomologyAffineCoproductEquiv_symm_apply
    (x : Sheaf.H.{u + 1} (moduleAddSheaf Y G) q) :
    letI : ∀ i, Module A (Sheaf.H.{u + 1} (moduleAddSheaf X (M i)) q) :=
      fun i => moduleCohomologyModuleOfHom X α (M i) q
    letI := moduleCohomologyModuleOfHom X α (∐ M) q
    letI := moduleCohomologyModuleOfHom X α ((Scheme.Modules.pushforward p).obj G) q
    letI := moduleCohomologyModuleOfHom Y (p.appTop.hom.comp α) G q
    (moduleCohomologyAffineCoproductEquiv p G α M e q).symm x =
      (moduleCohomologyCoproductEquiv.{u, 0} X α M q).symm
        ((moduleSectionsCohomologyEquiv X α e q).symm
          ((moduleCohomologyAffinePushforwardEquiv p G α q).symm x)) := rfl

/-- The original summand generator has the original geometric image. -/
theorem moduleCohomologyAffineCoproductEquiv_lof [DecidableEq δ] (i : δ)
    (x : Sheaf.H.{u + 1} (moduleAddSheaf X (M i)) q) :
    letI : ∀ i, Module A (Sheaf.H.{u + 1} (moduleAddSheaf X (M i)) q) :=
      fun i => moduleCohomologyModuleOfHom X α (M i) q
    letI := moduleCohomologyModuleOfHom X α (∐ M) q
    letI := moduleCohomologyModuleOfHom X α ((Scheme.Modules.pushforward p).obj G) q
    letI := moduleCohomologyModuleOfHom Y (p.appTop.hom.comp α) G q
    moduleCohomologyAffineCoproductEquiv p G α M e q
      (DirectSum.lof A δ (fun j => Sheaf.H.{u + 1} (moduleAddSheaf X (M j)) q) i x) =
      moduleCohomologyMapAlong p (𝟙 ((Scheme.Modules.pushforward p).obj G)) q
        (Sheaf.H.map (moduleSectionsAddSheafMap X α e.hom) q
          (moduleCohomologyMapOfHom X α (Sigma.ι M i) q x)) := by
  let : ∀ i, Module A (Sheaf.H.{u + 1} (moduleAddSheaf X (M i)) q) :=
    fun i => moduleCohomologyModuleOfHom X α (M i) q
  let := moduleCohomologyModuleOfHom X α (∐ M) q
  let := moduleCohomologyModuleOfHom X α ((Scheme.Modules.pushforward p).obj G) q
  let := moduleCohomologyModuleOfHom Y (p.appTop.hom.comp α) G q
  exact (moduleCohomologyAffineCoproductEquiv_apply p G α M e q _).trans
    (congrArg (fun t =>
      moduleCohomologyMapAlong p (𝟙 ((Scheme.Modules.pushforward p).obj G)) q
        (Sheaf.H.map (moduleSectionsAddSheafMap X α e.hom) q t))
      (moduleCohomologyCoproductMap_lof.{u, 0} X α M q i x))

end AlgebraicGeometry.Scheme.Cohomology
