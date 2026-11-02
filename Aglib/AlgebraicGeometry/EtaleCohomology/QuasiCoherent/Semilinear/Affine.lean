/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.QuasiCoherent.Semilinear.Sheaf
public import Aglib.AlgebraicGeometry.EtaleCohomology.QuasiCoherent.SpecSections
public import Aglib.LinearAlgebra.TensorProduct.Map

/-!
# The original affine semilinear additive coefficient endomorphism

The input module is the original `moduleSpecΓFunctor` value. Transport through
`ΓSpec` changes only its scalar spelling, and affine restriction constructs an
endomorphism of the same `additiveCoefficient`. Its affine-test formula and
uniqueness retain the actual geometric unit and section tensors. No finiteness,
flatness, domain or Noetherian assumption is used.
-/

@[expose] public noncomputable section

universe u

open CategoryTheory Opposite
open AlgebraicGeometry.Scheme.Modules
open scoped TensorProduct ChangeOfRings

namespace AlgebraicGeometry.Scheme.EtaleCohomology.QuasiCoherent

variable (A : CommRingCat.{u}) (F : (Spec A).Modules) [F.IsQuasicoherent]
  (p : ℕ) (hp : p.Prime) (hA : (p : A) = 0)
  (Φ : moduleSpecΓFunctor.obj F →ₛₗ[RingHom.frobeniusOfPrimeCastEqZero p hp hA]
    moduleSpecΓFunctor.obj F)

/-- The given prime-cast equation in the original global-section ring. -/
theorem primeCast_eq_zero_spec (h : (p : A) = 0) : (p : Γ(Spec A, ⊤)) = 0 := by
  simpa only [map_natCast, map_zero] using congrArg (Scheme.ΓSpecIso A).inv.hom h

omit [F.IsQuasicoherent] in
/-- The original two scalar actions agree through the actual `ΓSpec` isomorphism. -/
theorem specGammaScalar_smul (r : Γ(Spec A, ⊤)) (s : moduleSpecΓFunctor.obj F) :
    @Eq Γ(F, ⊤)
      (SMul.smul (M := A) (α := moduleSpecΓFunctor.obj F) ((Scheme.ΓSpecIso A).hom.hom r) s)
      (SMul.smul (M := Γ(Spec A, ⊤)) (α := (affineΓFunctor (Spec A)).obj F) r s) := by
  have h₁ := congrArg (β := Γ(F, ⊤))
    (fun z : moduleSpecΓFunctor.obj F => z)
    (specSections_smul A F ((Scheme.ΓSpecIso A).hom.hom r) s)
  have h₂ := congrArg (β := Γ(F, ⊤))
    (fun a : Γ(Spec A, ⊤) => SMul.smul (M := Γ(Spec A, ⊤)) (α := Γ(F, ⊤)) a s)
    (Iso.hom_inv_id_apply (Scheme.ΓSpecIso A) r)
  have h₃ := congrArg (β := Γ(F, ⊤))
    (fun z : (affineΓFunctor (Spec A)).obj F => z)
    (affineΓFunctor_smul (Spec A) F r s)
  exact h₁.trans (h₂.trans h₃.symm)

omit [F.IsQuasicoherent] in
/-- The same additive operator, with its actual global-section scalar action. -/
def specGlobalFrobenius :
    (affineΓFunctor (Spec A)).obj F →ₛₗ[
      RingHom.frobeniusOfPrimeCastEqZero p hp (primeCast_eq_zero_spec A p hA)]
      (affineΓFunctor (Spec A)).obj F where
  toFun := Φ
  map_add' := Φ.map_add
  map_smul' r s := by
    have hL := congrArg (β := Γ(F, ⊤)) (fun z : Γ(F, ⊤) => Φ z)
      (specGammaScalar_smul A F r s).symm
    have hΦ := Φ.map_smulₛₗ ((Scheme.ΓSpecIso A).hom.hom r) s
    have hpow := congrArg (β := Γ(F, ⊤))
      (fun a : A => SMul.smul (M := A) (α := moduleSpecΓFunctor.obj F) a (Φ s))
      (map_pow (Scheme.ΓSpecIso A).hom.hom r p).symm
    have hR := specGammaScalar_smul A F (r ^ p) (Φ s)
    exact hL.trans (hΦ.trans (hpow.trans hR))

omit [F.IsQuasicoherent] in
@[simp]
theorem specGlobalFrobenius_apply (s : moduleSpecΓFunctor.obj F) :
    specGlobalFrobenius A F p hp hA Φ s = Φ s := rfl

/-- The original semilinear map defines an additive endomorphism of the same
quasi-coherent étale coefficient, without claiming O-linearity. -/
def affineFrobenius : additiveCoefficient (Spec A) F ⟶ additiveCoefficient (Spec A) F :=
  affineGammaFrobenius (Spec A) F p hp (primeCast_eq_zero_spec A p hA)
    (specGlobalFrobenius A F p hp hA Φ)

local instance (U : (Spec A).AffineEtale) :
    IsAffine ((Scheme.AffineEtale.Spec (Spec A)).obj U).left := by
  change IsAffine (Spec U.left.unop)
  infer_instance

local instance (U : (Spec A).AffineEtale) :
    IsAffine ((Scheme.Etale.forget (Spec A)).obj
      ((Scheme.AffineEtale.Spec (Spec A)).obj U)).left := by
  change IsAffine (Spec U.left.unop)
  infer_instance

/-- On every native affine test the scalar and geometric unit are unchanged. -/
theorem affineFrobenius_scalar_unit (U : (Spec A).AffineEtale)
    (r : Γ(((Scheme.Etale.forget (Spec A)).obj
          ((Scheme.AffineEtale.Spec (Spec A)).obj U)).left, ⊤))
    (s : moduleSpecΓFunctor.obj F) :
    @Eq Γ((pullback ((Scheme.Etale.forget (Spec A)).obj
      ((Scheme.AffineEtale.Spec (Spec A)).obj U)).hom).obj F, ⊤)
    (((affineFrobenius A F p hp hA Φ).hom.app
      (op ((Scheme.AffineEtale.Spec (Spec A)).obj U))
      (ULift.up (SMul.smul (M := Γ(((Scheme.Etale.forget (Spec A)).obj
          ((Scheme.AffineEtale.Spec (Spec A)).obj U)).left, ⊤))
        (α := Γ((pullback ((Scheme.Etale.forget (Spec A)).obj
          ((Scheme.AffineEtale.Spec (Spec A)).obj U)).hom).obj F, ⊤))
        r ((((pullbackPushforwardAdjunction
          ((Scheme.Etale.forget (Spec A)).obj
          ((Scheme.AffineEtale.Spec (Spec A)).obj U)).hom).unit.app F).app ⊤) s)))).down)
      (SMul.smul (M := Γ(((Scheme.Etale.forget (Spec A)).obj
          ((Scheme.AffineEtale.Spec (Spec A)).obj U)).left, ⊤))
        (α := Γ((pullback ((Scheme.Etale.forget (Spec A)).obj
          ((Scheme.AffineEtale.Spec (Spec A)).obj U)).hom).obj F, ⊤))
        (r ^ p) ((((pullbackPushforwardAdjunction
          ((Scheme.Etale.forget (Spec A)).obj
          ((Scheme.AffineEtale.Spec (Spec A)).obj U)).hom).unit.app F).app ⊤) (Φ s))) := by
  let T : Over (Spec A) := (Scheme.Etale.forget (Spec A)).obj
    ((Scheme.AffineEtale.Spec (Spec A)).obj U)
  let : IsAffine T.left := by
    change IsAffine (Spec U.left.unop)
    infer_instance
  have h := affineGammaFrobenius_tmul (Spec A) F p hp (primeCast_eq_zero_spec A p hA)
    (specGlobalFrobenius A F p hp hA Φ) U r s
  have h₀ := affinePullbackSectionsIso_tmul (Spec A) F T r s
  have h₁ := affinePullbackSectionsIso_tmul (Spec A) F T (r ^ p)
    (specGlobalFrobenius A F p hp hA Φ s)
  have hi := congrArg (β := Γ((pullback T.hom).obj F, ⊤))
    (fun z : Γ((pullback T.hom).obj F, ⊤) =>
      ((affineFrobenius A F p hp hA Φ).hom.app
        (op ((Scheme.AffineEtale.Spec (Spec A)).obj U)) (ULift.up z)).down) h₀.symm
  have he := hi.trans (h.trans h₁)
  exact he

/-- On an actual algebra spectrum the forward formula is the original tensor
comparison, not a replacement coordinate module. -/
theorem affineFrobenius_specTensor (B : CommAlgCat.{u} A)
    [Etale (Spec.map (CommRingCat.ofHom (algebraMap A B)))]
    (r : B) (s : moduleSpecΓFunctor.obj F) :
    @Eq Γ((pullback (Spec.map (CommRingCat.ofHom (algebraMap A B)))).obj F, ⊤)
    (((affineFrobenius A F p hp hA Φ).hom.app
      (op (Scheme.Etale.mk (Spec.map (CommRingCat.ofHom (algebraMap A B)))))
      (ULift.up ((specTensorSectionsIso A F B).hom (r ⊗ₜ[A] s)))).down)
      ((specTensorSectionsIso A F B).hom ((r ^ p) ⊗ₜ[A] Φ s)) := by
  let f := Spec.map (CommRingCat.ofHom (algebraMap A B))
  have h := affineFrobenius_scalar_unit A F p hp hA Φ
    (Scheme.AffineEtale.mk f) ((Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom r) s
  have h₀ := specTensorSectionsIso_tmul A F B r s
  have h₁ := specTensorSectionsIso_tmul A F B (r ^ p) (Φ s)
  have hi := congrArg (β := Γ((pullback f).obj F, ⊤))
    (fun z : Γ((pullback f).obj F, ⊤) =>
      ((affineFrobenius A F p hp hA Φ).hom.app (op (Scheme.Etale.mk f))
        (ULift.up z)).down) h₀
  have hpow := congrArg (β := Γ((pullback f).obj F, ⊤))
    (fun a : Γ(Spec (CommRingCat.of B), ⊤) =>
      SMul.smul (M := Γ(Spec (CommRingCat.of B), ⊤)) (α := Γ((pullback f).obj F, ⊤)) a
        ((((pullbackPushforwardAdjunction f).unit.app F).app ⊤) (Φ s)))
    (map_pow (Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom r p).symm
  have he := hi.trans (h.trans (hpow.trans h₁.symm))
  exact he

/-- The original additive endomorphism is uniquely determined by its affine
scalar-unit formula. No O-linear structure on it is assumed. -/
theorem affineFrobenius_unique
    (Ψ : additiveCoefficient (Spec A) F ⟶ additiveCoefficient (Spec A) F)
    (hΨ : ∀ (U : (Spec A).AffineEtale)
      (r : Γ(((Scheme.Etale.forget (Spec A)).obj
          ((Scheme.AffineEtale.Spec (Spec A)).obj U)).left, ⊤))
      (s : moduleSpecΓFunctor.obj F),
      @Eq Γ((pullback ((Scheme.Etale.forget (Spec A)).obj
        ((Scheme.AffineEtale.Spec (Spec A)).obj U)).hom).obj F, ⊤)
      ((Ψ.hom.app (op ((Scheme.AffineEtale.Spec (Spec A)).obj U))
        (ULift.up (SMul.smul (M := Γ(((Scheme.Etale.forget (Spec A)).obj
          ((Scheme.AffineEtale.Spec (Spec A)).obj U)).left, ⊤))
        (α := Γ((pullback ((Scheme.Etale.forget (Spec A)).obj
          ((Scheme.AffineEtale.Spec (Spec A)).obj U)).hom).obj F, ⊤))
        r ((((pullbackPushforwardAdjunction
          ((Scheme.Etale.forget (Spec A)).obj
          ((Scheme.AffineEtale.Spec (Spec A)).obj U)).hom).unit.app F).app ⊤) s)))).down)
        (SMul.smul (M := Γ(((Scheme.Etale.forget (Spec A)).obj
          ((Scheme.AffineEtale.Spec (Spec A)).obj U)).left, ⊤))
        (α := Γ((pullback ((Scheme.Etale.forget (Spec A)).obj
          ((Scheme.AffineEtale.Spec (Spec A)).obj U)).hom).obj F, ⊤))
        (r ^ p) ((((pullbackPushforwardAdjunction
          ((Scheme.Etale.forget (Spec A)).obj
          ((Scheme.AffineEtale.Spec (Spec A)).obj U)).hom).unit.app F).app ⊤) (Φ s)))) :
    Ψ = affineFrobenius A F p hp hA Φ := by
  apply affineGammaFrobenius_unique
  intro U s
  let T : Over (Spec A) := (Scheme.Etale.forget (Spec A)).obj
    ((Scheme.AffineEtale.Spec (Spec A)).obj U)
  let : IsAffine T.left := by
    change IsAffine (Spec U.left.unop)
    infer_instance
  let k : Γ((pullback T.hom).obj F, ⊤) →+ Γ((pullback T.hom).obj F, ⊤) :=
    AddEquiv.ulift.toAddMonoidHom.comp
      ((Ψ.hom.app (op ((Scheme.AffineEtale.Spec (Spec A)).obj U))).hom.comp
        AddEquiv.ulift.symm.toAddMonoidHom)
  let e : (ModuleCat.extendScalars T.hom.appTop.hom).obj
      ((affineΓFunctor (Spec A)).obj F) →+ Γ((pullback T.hom).obj F, ⊤) :=
    (affinePullbackSectionsIso T.hom F).hom.hom.toAddMonoidHom
  let φ := affineSectionFrobenius (Spec A) F p hp (primeCast_eq_zero_spec A p hA)
    (specGlobalFrobenius A F p hp hA Φ) T
  have hk (z) : k z =
      (Ψ.hom.app (op ((Scheme.AffineEtale.Spec (Spec A)).obj U)) (ULift.up z)).down := rfl
  have heval (z) : e z = (affinePullbackSectionsIso T.hom F).hom z := rfl
  have hke (z) : (k.comp e) z = k ((affinePullbackSectionsIso T.hom F).hom z) := by
    simp only [AddMonoidHom.comp_apply, heval]
  have hφe (z) : (φ.comp e) z = affineSectionFrobenius (Spec A) F p hp
      (primeCast_eq_zero_spec A p hA) (specGlobalFrobenius A F p hp hA Φ) T
      ((affinePullbackSectionsIso T.hom F).hom z) := by
    simp only [φ, AddMonoidHom.comp_apply, heval]
  have hgen (r : Γ(T.left, ⊤)) (m : (affineΓFunctor (Spec A)).obj F) :
      (k.comp e) (r ⊗ₜ[Γ(Spec A, ⊤),T.hom.appTop.hom] m) =
        (φ.comp e) (r ⊗ₜ[Γ(Spec A, ⊤),T.hom.appTop.hom] m) := by
    have h₀ := affinePullbackSectionsIso_tmul (Spec A) F T r m
    have h₁ := affinePullbackSectionsIso_tmul (Spec A) F T (r ^ p)
      (specGlobalFrobenius A F p hp hA Φ m)
    have hφ := affineSectionFrobenius_tmul (Spec A) F p hp
      (primeCast_eq_zero_spec A p hA) (specGlobalFrobenius A F p hp hA Φ) T r m
    have ha := hΨ U r m
    have hc := (congrArg k h₀).trans ((hk _).trans (ha.trans (h₁.symm.trans hφ.symm)))
    let z : (ModuleCat.extendScalars T.hom.appTop.hom).obj
        ((affineΓFunctor (Spec A)).obj F) := r ⊗ₜ[Γ(Spec A, ⊤),T.hom.appTop.hom] m
    have hfirst := hke z
    have hlast := hφe z
    dsimp only [z] at hfirst hlast
    have hz := hfirst.trans (hc.trans hlast.symm)
    exact hz
  have he : k.comp e = φ.comp e :=
    TensorProduct.addHom_ext _ _ (fun r m => hgen r m)
  have hes : Function.Surjective e := by
    intro t
    obtain ⟨z, hz⟩ :=
      (ConcreteCategory.bijective_of_isIso (affinePullbackSectionsIso T.hom F).hom).2 t
    exact ⟨z, (heval z).trans hz⟩
  have hc : k = φ := (AddMonoidHom.cancel_right hes).mp he
  have hv := DFunLike.congr_fun hc s
  exact (hk s).symm.trans hv

end AlgebraicGeometry.Scheme.EtaleCohomology.QuasiCoherent
