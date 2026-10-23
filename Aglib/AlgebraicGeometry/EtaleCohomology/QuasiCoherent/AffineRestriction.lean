/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.QuasiCoherent.SectionScalars
public import Aglib.AlgebraicGeometry.EtaleCohomology.QuasiCoherent.AffineSections
public import Aglib.AlgebraicGeometry.Modules.Differentials.Diagonal.Affine

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
set_option backward.defeqAttrib.useBackward true

universe u

open CategoryTheory Opposite
open AlgebraicGeometry.Scheme.Modules
open scoped TensorProduct ChangeOfRings

namespace AlgebraicGeometry.Scheme.EtaleCohomology.QuasiCoherent

private theorem restriction_unit_calculation {A B C D E : Type*}
    (r : B → E) (ua : A → B) (ub : B → C) (i : C → D) (j : D → C)
    (k : D → E) (uc : A → D) (ud : A → E)
    (hr : ∀ b, r b = k (i (ub b)))
    (hc : ∀ a, j (uc a) = ub (ua a)) (hi : ∀ d, i (j d) = d)
    (hd : ∀ a, k (uc a) = ud a) (a : A) : r (ua a) = ud a := by
  rw [hr, ← hc, hi, hd]

private theorem iso_section_inv_hom {Y : Scheme.{u}} {M N : Y.Modules}
    (e : M ≅ N) (s : Γ(N, ⊤)) :
    Scheme.Modules.Hom.app e.hom ⊤ (Scheme.Modules.Hom.app e.inv ⊤ s) = s := by
  have h := congrArg (fun q : N ⟶ N => Scheme.Modules.Hom.app q ⊤ s) e.inv_hom_id
  exact h

private def literalSectionLinearMap {Y : Scheme.{u}} [IsAffine Y] (M : Y.Modules) :
    (affineΓFunctor Y).obj M ⟶
      (SheafOfModules.evaluation Y.ringCatSheaf (op ⊤)).obj M :=
  (Scheme.Modules.BaseChange.Affine.affineTildeΓRightIso Y).hom.app M

private theorem literalSectionLinearMap_apply {Y : Scheme.{u}} [IsAffine Y]
    (M : Y.Modules) (s : (affineΓFunctor Y).obj M) :
    literalSectionLinearMap M s = s := rfl

private theorem linear_tmul_of_unit {R S : Type*} [CommRing R] [CommRing S]
    (φ : R →+* S) (M : ModuleCat R) (N : ModuleCat S)
    (e : (ModuleCat.extendScalars φ).obj M ⟶ N) (η : M → N)
    (hη : ∀ m, e ((1 : S) ⊗ₜ[R,φ] m) = η m) (r : S) (m : M) :
    e (r ⊗ₜ[R,φ] m) = r • η m := by
  have h := (ModuleCat.ExtendScalars.smul_tmul φ r (1 : S) m).trans
    (by rw [mul_one])
  calc
    e (r ⊗ₜ[R,φ] m) = e (SMul.smul (M := S)
        (α := (ModuleCat.extendScalars φ).obj M) r ((1 : S) ⊗ₜ[R,φ] m)) :=
      congrArg e h.symm
    _ = r • e ((1 : S) ⊗ₜ[R,φ] m) := e.hom.map_smul r _
    _ = r • η m := congrArg (fun x : N => r • x) (hη m)

private theorem affine_tmul_of_unit {R : Type*} [CommRing R]
    {Y : Scheme.{u}} [IsAffine Y] (φ : R →+* Γ(Y, ⊤)) (M : ModuleCat R)
    (N : Y.Modules)
    (e : (ModuleCat.extendScalars φ).obj M ⟶ (affineΓFunctor Y).obj N)
    (η : M → Γ(N, ⊤)) (hη : ∀ m, e ((1 : Γ(Y, ⊤)) ⊗ₜ[R,φ] m) = η m)
    (r : Γ(Y, ⊤)) (m : M) :
    e (r ⊗ₜ[R,φ] m) = SMul.smul (M := Γ(Y, ⊤)) (α := Γ(N, ⊤)) r (η m) := by
  let P : ModuleCat Γ(Y, ⊤) :=
    (SheafOfModules.evaluation Y.ringCatSheaf (op ⊤)).obj N
  let e' : (ModuleCat.extendScalars φ).obj M ⟶ P := e ≫ literalSectionLinearMap N
  have he : ∀ t, e' t = e t := fun t => literalSectionLinearMap_apply N (e t)
  have h := linear_tmul_of_unit φ M P e' η (fun m => (he _).trans (hη m)) r m
  exact (he _).symm.trans h

private theorem restriction_tmul_calculation {R S A B C : Type*}
    [SMul R B] [SMul S C] (φ : R → S) (r : B → C) (a : A → B) (b : A → C)
    (t : R → A → B) (u : S → A → C)
    (ht : ∀ x s, t x s = x • a s) (hu : ∀ y s, u y s = y • b s)
    (hr : ∀ x z, r (x • z) = φ x • r z) (hab : ∀ s, r (a s) = b s)
    (x : R) (s : A) : r (t x s) = u (φ x) s := by
  rw [ht, hr, hab, hu]

variable (X : Scheme.{u}) (F : X.Modules) [F.IsQuasicoherent]

/-- Restriction retains the original global-section pullback unit. -/
theorem sectionsPresheaf_map_unit {T U : Over X} (f : U ⟶ T) (s : Γ(F, ⊤)) :
    (sectionsPresheaf X F).map f.op
        ((((pullbackPushforwardAdjunction T.hom).unit.app F).app ⊤) s) =
      (((pullbackPushforwardAdjunction U.hom).unit.app F).app ⊤) s := by
  exact restriction_unit_calculation
    (A := Γ(F, ⊤)) (B := Γ((pullback T.hom).obj F, ⊤))
    (C := Γ((pullback f.left).obj ((pullback T.hom).obj F), ⊤))
    (D := Γ((pullback (f.left ≫ T.hom)).obj F, ⊤))
    (E := Γ((pullback U.hom).obj F, ⊤))
    ((sectionsPresheaf X F).map f.op)
    (fun t => (((pullbackPushforwardAdjunction T.hom).unit.app F).app ⊤) t)
    (fun t => (((pullbackPushforwardAdjunction f.left).unit.app
      ((pullback T.hom).obj F)).app ⊤) t)
    (Scheme.Modules.Hom.app ((pullbackComp f.left T.hom).hom.app F) ⊤)
    (Scheme.Modules.Hom.app ((pullbackComp f.left T.hom).inv.app F) ⊤)
    (Scheme.Modules.Hom.app ((pullbackCongr (Over.w f)).hom.app F) ⊤)
    (fun t => (((pullbackPushforwardAdjunction (f.left ≫ T.hom)).unit.app F).app ⊤) t)
    (fun t => (((pullbackPushforwardAdjunction U.hom).unit.app F).app ⊤) t)
    (sectionsPresheaf_map_eq X F f)
    (Modules.Differentials.Diagonal.pullbackComp_inv_unit_top f.left T.hom F)
    (iso_section_inv_hom ((pullbackComp f.left T.hom).app F))
    (Modules.Differentials.Diagonal.pullbackCongr_unit_top (Over.w f) F) s

variable [IsAffine X]

/-- The canonical affine comparison on a pure tensor is scalar times the geometric unit. -/
theorem affinePullbackSectionsIso_tmul (T : Over X) [IsAffine T.left]
    (r : Γ(T.left, ⊤)) (s : (affineΓFunctor X).obj F) :
    (affinePullbackSectionsIso T.hom F).hom
        (r ⊗ₜ[Γ(X, ⊤),T.hom.appTop.hom] s) =
      SMul.smul (M := Γ(T.left, ⊤)) (α := Γ((pullback T.hom).obj F, ⊤))
        r ((((pullbackPushforwardAdjunction T.hom).unit.app F).app ⊤) s) := by
  exact affine_tmul_of_unit T.hom.appTop.hom ((affineΓFunctor X).obj F)
    ((pullback T.hom).obj F) (affinePullbackSectionsIso T.hom F).hom
    (fun m => (((pullbackPushforwardAdjunction T.hom).unit.app F).app ⊤) m)
    (affinePullbackSectionsIso_one_tmul T.hom F) r s

/-- Every affine over-map acts by its original ring map on the tensor factor. -/
theorem sectionsPresheaf_map_affine_tmul {T U : Over X}
    [IsAffine T.left] [IsAffine U.left] (f : U ⟶ T)
    (r : Γ(T.left, ⊤)) (s : (affineΓFunctor X).obj F) :
    (sectionsPresheaf X F).map f.op
        ((affinePullbackSectionsIso T.hom F).hom
          (r ⊗ₜ[Γ(X, ⊤),T.hom.appTop.hom] s)) =
      (affinePullbackSectionsIso U.hom F).hom
        (f.left.appTop.hom r ⊗ₜ[Γ(X, ⊤),U.hom.appTop.hom] s) := by
  exact restriction_tmul_calculation
    (R := Γ(T.left, ⊤)) (S := Γ(U.left, ⊤)) (A := (affineΓFunctor X).obj F)
    (B := Γ((pullback T.hom).obj F, ⊤)) (C := Γ((pullback U.hom).obj F, ⊤))
    f.left.appTop.hom ((sectionsPresheaf X F).map f.op)
    (fun m => (((pullbackPushforwardAdjunction T.hom).unit.app F).app ⊤) m)
    (fun m => (((pullbackPushforwardAdjunction U.hom).unit.app F).app ⊤) m)
    (fun r m => (affinePullbackSectionsIso T.hom F).hom
      (r ⊗ₜ[Γ(X, ⊤),T.hom.appTop.hom] m))
    (fun r m => (affinePullbackSectionsIso U.hom F).hom
      (r ⊗ₜ[Γ(X, ⊤),U.hom.appTop.hom] m))
    (affinePullbackSectionsIso_tmul X F T) (affinePullbackSectionsIso_tmul X F U)
    (sectionsPresheaf_map_smul X F f) (sectionsPresheaf_map_unit X F f) r s

end AlgebraicGeometry.Scheme.EtaleCohomology.QuasiCoherent
