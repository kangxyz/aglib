/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.QuasiCoherent.SectionScalars
public import Aglib.AlgebraicGeometry.EtaleCohomology.QuasiCoherent.AffineSections
public import Aglib.AlgebraicGeometry.EtaleCohomology.QuasiCoherent.PullbackUnit

/-!
# Original affine tensor coordinates preserve section restrictions

The original geometric units compose through the native pullback comparison.
Consequently every affine over-map acts on tensor coordinates by its original
ring map on the first factor and the identity on the coefficient factor. This
is the coface normalization needed for the actual Amitsur comparison.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory Opposite
open AlgebraicGeometry.Scheme.Modules
open scoped TensorProduct ChangeOfRings

namespace AlgebraicGeometry.Scheme.EtaleCohomology.QuasiCoherent

variable (X : Scheme.{u}) (F : X.Modules) [F.IsQuasicoherent]

variable [IsAffine X]

/-- The native affine-section scalar action agrees with the original global-section action. -/
theorem affineΓFunctor_smul (M : X.Modules) (r : Γ(X, ⊤)) (s : (affineΓFunctor X).obj M) :
    (r • s : (affineΓFunctor X).obj M) =
      SMul.smul (M := Γ(X, ⊤)) (α := Γ(M, ⊤)) r s := by
  change SMul.smul (M := Γ(X, ⊤)) (α := Γ(M, ⊤))
    (X.toSpecΓ.app ⊤ ((Spec Γ(X, ⊤)).presheaf.map (𝟙 (op ⊤))
      ((Scheme.ΓSpecIso Γ(X, ⊤)).inv.hom r))) s = _
  rw [CategoryTheory.Functor.map_id]
  change SMul.smul (M := Γ(X, ⊤)) (α := Γ(M, ⊤))
    (X.toSpecΓ.appTop.hom ((Scheme.ΓSpecIso Γ(X, ⊤)).inv.hom r)) s = _
  rw [Scheme.toSpecΓ_appTop, Iso.inv_hom_id_apply]

/-- The canonical affine comparison on a pure tensor is scalar times the geometric unit. -/
theorem affinePullbackSectionsIso_tmul (T : Over X) [IsAffine T.left]
    (r : Γ(T.left, ⊤)) (s : (affineΓFunctor X).obj F) :
    (affinePullbackSectionsIso T.hom F).hom
        (r ⊗ₜ[Γ(X, ⊤),T.hom.appTop.hom] s) =
      SMul.smul (M := Γ(T.left, ⊤)) (α := Γ((pullback T.hom).obj F, ⊤))
        r ((((pullbackPushforwardAdjunction T.hom).unit.app F).app ⊤) s) := by
  have h : r ⊗ₜ[Γ(X, ⊤),T.hom.appTop.hom] s =
      SMul.smul (M := Γ(T.left, ⊤))
        (α := (ModuleCat.extendScalars T.hom.appTop.hom).obj ((affineΓFunctor X).obj F))
        r ((1 : Γ(T.left, ⊤)) ⊗ₜ[Γ(X, ⊤),T.hom.appTop.hom] s) := by
    exact (ModuleCat.ExtendScalars.smul_tmul T.hom.appTop.hom r 1 s).trans
      (by rw [mul_one]) |>.symm
  erw [h, _root_.map_smul, affinePullbackSectionsIso_one_tmul]
  exact affineΓFunctor_smul T.left ((pullback T.hom).obj F) r _

/-- Every affine over-map acts by its original ring map on the tensor factor. -/
theorem sectionsPresheaf_map_affine_tmul {T U : Over X}
    [IsAffine T.left] [IsAffine U.left] (f : U ⟶ T)
    (r : Γ(T.left, ⊤)) (s : (affineΓFunctor X).obj F) :
    (sectionsPresheaf X F).map f.op
        ((affinePullbackSectionsIso T.hom F).hom
          (r ⊗ₜ[Γ(X, ⊤),T.hom.appTop.hom] s)) =
      (affinePullbackSectionsIso U.hom F).hom
        (f.left.appTop.hom r ⊗ₜ[Γ(X, ⊤),U.hom.appTop.hom] s) := by
  exact (congrArg ((sectionsPresheaf X F).map f.op)
    (affinePullbackSectionsIso_tmul X F T r s)).trans
    ((sectionsPresheaf_map_smul X F f r
      ((((pullbackPushforwardAdjunction T.hom).unit.app F).app ⊤) s)).trans
      ((congrArg (fun z : Γ((pullback U.hom).obj F, ⊤) => f.left.appTop.hom r • z)
        (sectionsPresheaf_map_unit X F f s)).trans
          (affinePullbackSectionsIso_tmul X F U (f.left.appTop.hom r) s).symm))

end AlgebraicGeometry.Scheme.EtaleCohomology.QuasiCoherent
