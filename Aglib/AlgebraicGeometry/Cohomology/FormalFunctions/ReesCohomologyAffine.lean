/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.FormalFunctions.ReesCohomologyPushforward
public import Aglib.AlgebraicGeometry.Cohomology.Cech.CoproductComputed
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.AffinePushforward

/-! # Cover-independent original affine-pushforward comparison -/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
open CategoryTheory Limits Opposite TopologicalSpace

namespace AlgebraicGeometry.Scheme.Cohomology

variable {X Y : Scheme.{u}} (p : Y ⟶ X) [IsAffineHom p]
  [CompactSpace X] [X.IsSeparated] (G : Y.Modules) [G.IsQuasicoherent]

/-- The unchanged direct-image cohomology map is bijective for affine morphisms
with quasi-compact separated target and quasicoherent coefficients. -/
theorem moduleCohomologyAffinePushforward_bijective (q : ℕ) :
    Function.Bijective
      (moduleCohomologyMapAlong p (𝟙 ((Scheme.Modules.pushforward p).obj G)) q) := by
  classical
  let := Scheme.Modules.isQuasicoherent_pushforward_of_isAffineHom p G
  let : Y.IsSeparated := ⟨by
    rw [← terminal.comp_from p]
    infer_instance⟩
  let C := X.affineCover.finiteSubcover
  let U : C.I₀ → X.Opens := fun i => (C.f i).opensRange
  have hU : ∀ i, IsAffineOpen (U i) := fun i => isAffineOpen_opensRange (C.f i)
  have hc : iSup U = ⊤ := C.iSup_opensRange
  exact moduleCohomologyPushforwardMap_bijective p G U hc
    (p.iSup_preimage_eq_top hc) (moduleCechIsAffineOpenIntersection X U hU)
    (moduleCechIsAffineOpenIntersection Y (fun i => p ⁻¹ᵁ U i)
      (fun i => (hU i).preimage p)) q

/-- Cover-independent linear equivalence with the original geometric forward map. -/
def moduleCohomologyAffinePushforwardEquiv {A : Type u} [CommRing A]
    (α : A →+* Γ(X, ⊤)) (q : ℕ) :
    letI := moduleCohomologyModuleOfHom X α ((Scheme.Modules.pushforward p).obj G) q
    letI := moduleCohomologyModuleOfHom Y (p.appTop.hom.comp α) G q
    Sheaf.H.{u + 1} (moduleAddSheaf X ((Scheme.Modules.pushforward p).obj G)) q ≃ₗ[A]
      Sheaf.H.{u + 1} (moduleAddSheaf Y G) q := by
  letI := moduleCohomologyModuleOfHom X α ((Scheme.Modules.pushforward p).obj G) q
  letI := moduleCohomologyModuleOfHom Y (p.appTop.hom.comp α) G q
  exact LinearEquiv.ofBijective
    (moduleCohomologyMapAlongLinear p α (𝟙 ((Scheme.Modules.pushforward p).obj G)) q)
    (moduleCohomologyAffinePushforward_bijective p G q)

/-- No cover choice changes the forward cohomology map. -/
theorem moduleCohomologyAffinePushforwardEquiv_apply {A : Type u} [CommRing A]
    (α : A →+* Γ(X, ⊤)) (q : ℕ)
    (x : Sheaf.H.{u + 1} (moduleAddSheaf X ((Scheme.Modules.pushforward p).obj G)) q) :
    moduleCohomologyAffinePushforwardEquiv p G α q x =
      moduleCohomologyMapAlong p (𝟙 ((Scheme.Modules.pushforward p).obj G)) q x := rfl

end AlgebraicGeometry.Scheme.Cohomology
