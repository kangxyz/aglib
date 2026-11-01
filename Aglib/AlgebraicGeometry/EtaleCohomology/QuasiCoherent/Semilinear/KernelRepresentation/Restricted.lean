/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.QuasiCoherent.Semilinear.KernelRepresentation
public import Aglib.AlgebraicGeometry.Sites.EtaleAffineBasis.AffineAlgebras
public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.Descent.AffineEffectiveDescent
public import Aglib.AlgebraicGeometry.EtaleCohomology.H1.FiniteTorsorRepresentation
public import Mathlib.CategoryTheory.HomCongr

/-!
# The original restricted kernel and its actual finite algebra representative

The affine comparison uses the original rings of the native tests. The scalar
tower comes from their actual composed structural arrows. Its target is the
literal restriction of the original categorical kernel, not a new fixed-point
sheaf or an independently transported semilinear operator.
-/

@[expose] public noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry.Scheme.Modules
open scoped TensorProduct

namespace AlgebraicGeometry.Scheme.EtaleCohomology.QuasiCoherent

variable (A : CommRingCat.{u}) (F : (Spec A).Modules) [F.IsQuasicoherent]
  (p : ℕ) (hp : p.Prime) (hA : (p : A) = 0)
  (Φ : moduleSpecΓFunctor.obj F →ₛₗ[RingHom.frobeniusOfPrimeCastEqZero p hp hA]
    moduleSpecΓFunctor.obj F)
  (R : Type u) [CommRing R] [Algebra A R]
  [Etale (Spec.map (CommRingCat.ofHom (algebraMap A R)))]
  (C : Type u) [CommRing C] [Algebra R C] [Module.Finite R C] [Algebra.Etale R C]
  (e : ∀ (S : Type u) [CommRing S] [Algebra A S] [Algebra R S] [IsScalarTower A R S],
    (C →ₐ[R] S) ≃ {z : S ⊗[A] moduleSpecΓFunctor.obj F //
      LinearMap.frobeniusBaseChange p hp hA Φ S z = z})

/-- On each original affine test, the actual algebraic representative evaluates
to the literal restriction of the original categorical kernel. -/
def restrictedKernelAffineEquiv (U : (Spec (CommRingCat.of R)).AffineEtale) :
    (finiteRepresentedSetSheaf (Scheme.FiniteEtale.AffineDescent.specCover R C)).obj.obj
        (op ((Scheme.AffineEtale.Spec (Spec (CommRingCat.of R))).obj U)) ≃
      ((etaleRestriction (Spec.map (CommRingCat.ofHom (algebraMap A R)))).obj
        (kernel (affineFrobenius A F p hp hA Φ -
          𝟙 (additiveCoefficient (Spec A) F)))).obj.obj
        (op ((Scheme.AffineEtale.Spec (Spec (CommRingCat.of R))).obj U)) := by
  let j := Spec.map (CommRingCat.ofHom (algebraMap A R))
  let : Etale U.hom := U.prop
  let UA : (Spec A).AffineEtale := Scheme.AffineEtale.mk (U.hom ≫ j)
  let S := U.left.unop
  letI : Algebra R S := (Spec.preimage U.hom).hom.toAlgebra
  letI : Algebra A S := (Spec.preimage (U.hom ≫ j)).hom.toAlgebra
  let SA := Scheme.EtaleAffineBasis.affineAlgebra A UA
  let : IsScalarTower A R S := IsScalarTower.of_algebraMap_eq fun a => by
    have h := Spec.preimage_comp U.hom j
    rw [Spec.preimage_map] at h
    exact congrArg (fun g => g.hom a) h
  let eH := Scheme.EtaleAffineBasis.affineAlgebraHomEquiv
    (CommRingCat.of R) (CommAlgCat.of R C) U
  let K := kernel (affineFrobenius A F p hp hA Φ - 𝟙 (additiveCoefficient (Spec A) F))
  let eK := (K.obj.mapIso
    (Scheme.EtaleAffineBasis.affineAlgebraEtaleIso A UA).symm.op).addCommGroupIsoToAddEquiv
  exact Equiv.ulift.trans (eH.trans ((e S).trans
    ((affineFrobeniusKernelTensorEquiv A F p hp hA Φ SA).trans eK.toEquiv)))

variable (he : ∀ (S T : Type u) [CommRing S] [CommRing T]
    [Algebra A S] [Algebra A T] [Algebra R S] [Algebra R T]
    [IsScalarTower A R S] [IsScalarTower A R T] (f : S →ₐ[R] T) (h : C →ₐ[R] S),
    (e T (f.comp h)).val =
      TensorProduct.map (f.restrictScalars A).toLinearMap LinearMap.id (e S h).val)

include he in
/-- The complete affine comparison preserves original restrictions. Algebraic
naturality is used on the original scalar tower before evaluating kernel maps. -/
theorem restrictedKernelAffineEquiv_naturality
    {U V : (Spec (CommRingCat.of R)).AffineEtale} (f : U ⟶ V)
    (t : (finiteRepresentedSetSheaf (Scheme.FiniteEtale.AffineDescent.specCover R C)).obj.obj
      (op ((Scheme.AffineEtale.Spec (Spec (CommRingCat.of R))).obj V))) :
    restrictedKernelAffineEquiv A F p hp hA Φ R C e U
        ((finiteRepresentedSetSheaf (Scheme.FiniteEtale.AffineDescent.specCover R C)).obj.map
          ((Scheme.AffineEtale.Spec (Spec (CommRingCat.of R))).map f).op t) =
      ((etaleRestriction (Spec.map (CommRingCat.ofHom (algebraMap A R)))).obj
        (kernel (affineFrobenius A F p hp hA Φ -
          𝟙 (additiveCoefficient (Spec A) F)))).obj.map
          ((Scheme.AffineEtale.Spec (Spec (CommRingCat.of R))).map f).op
          (restrictedKernelAffineEquiv A F p hp hA Φ R C e V t) := by
  rcases t with ⟨g⟩
  let j := Spec.map (CommRingCat.ofHom (algebraMap A R))
  let : Etale U.hom := U.prop
  let : Etale V.hom := V.prop
  let UA : (Spec A).AffineEtale := Scheme.AffineEtale.mk (U.hom ≫ j)
  let VA : (Spec A).AffineEtale := Scheme.AffineEtale.mk (V.hom ≫ j)
  let SU := U.left.unop
  let SV := V.left.unop
  let : Algebra R SU := (Spec.preimage U.hom).hom.toAlgebra
  let : Algebra R SV := (Spec.preimage V.hom).hom.toAlgebra
  let : Algebra A SU := (Spec.preimage (U.hom ≫ j)).hom.toAlgebra
  let : Algebra A SV := (Spec.preimage (V.hom ≫ j)).hom.toAlgebra
  let : IsScalarTower A R SU := IsScalarTower.of_algebraMap_eq fun a => by
    have h := Spec.preimage_comp U.hom j
    rw [Spec.preimage_map] at h
    exact congrArg (fun k => k.hom a) h
  let : IsScalarTower A R SV := IsScalarTower.of_algebraMap_eq fun a => by
    have h := Spec.preimage_comp V.hom j
    rw [Spec.preimage_map] at h
    exact congrArg (fun k => k.hom a) h
  let SAU := Scheme.EtaleAffineBasis.affineAlgebra A UA
  let SAV := Scheme.EtaleAffineBasis.affineAlgebra A VA
  let fA : UA ⟶ VA := MorphismProperty.CostructuredArrow.homMk f.left trivial (by
    have h := MorphismProperty.Over.w
      ((Scheme.AffineEtale.Spec (Spec (CommRingCat.of R))).map f)
    change Spec.map f.left.unop ≫ V.hom = U.hom at h
    change Spec.map f.left.unop ≫ (V.hom ≫ j) = U.hom ≫ j
    rw [← Category.assoc, h])
  let fR : SV →ₐ[R] SU := (Scheme.EtaleAffineBasis.affineAlgebraMap (CommRingCat.of R) f).hom
  let fAb : SAV ⟶ SAU := Scheme.EtaleAffineBasis.affineAlgebraMap A fA
  have hf : fR.restrictScalars A = fAb.hom := by ext x; rfl
  let hV := Scheme.EtaleAffineBasis.affineAlgebraHomEquiv
    (CommRingCat.of R) (CommAlgCat.of R C) V g
  have hHom := Scheme.EtaleAffineBasis.affineAlgebraHomEquiv_naturality
    (CommRingCat.of R) (CommAlgCat.of R C) f g
  have hmap : TensorProduct.map (fR.restrictScalars A).toLinearMap LinearMap.id =
      fAb.hom.toLinearMap.rTensor (moduleSpecΓFunctor.obj F) := by
    rw [LinearMap.rTensor_def, hf]
    rfl
  have hw := (he SV SU fR hV).trans (congrArg
    (fun k : SV ⊗[A] moduleSpecΓFunctor.obj F →ₗ[A] SU ⊗[A] moduleSpecΓFunctor.obj F =>
      k (e SV hV).val) hmap)
  let K := kernel (affineFrobenius A F p hp hA Φ - 𝟙 (additiveCoefficient (Spec A) F))
  let iU := Scheme.EtaleAffineBasis.affineAlgebraEtaleIso A UA
  let iV := Scheme.EtaleAffineBasis.affineAlgebraEtaleIso A VA
  let q : Scheme.Etale.mk (Spec.map (CommRingCat.ofHom (algebraMap A SAU))) ⟶
      Scheme.Etale.mk (Spec.map (CommRingCat.ofHom (algebraMap A SAV))) :=
    MorphismProperty.Over.homMk ((algSpec A).map fAb.op).left ((algSpec A).map fAb.op).w
  let n := (Scheme.AffineEtale.Spec (Spec A)).map fA
  have hq : q = Scheme.EtaleAffineBasis.affineAlgebraEtaleMap A fA := by
    apply (Scheme.Etale.forget (Spec A)).map_injective
    exact (Scheme.EtaleAffineBasis.affineAlgebraEtaleMap_forget A fA).symm
  have hi := Scheme.EtaleAffineBasis.affineAlgebraEtaleIso_naturality A fA
  rw [← hq] at hi
  change q ≫ iV.hom = iU.hom ≫ n at hi
  have hiInv : iU.inv ≫ q = n ≫ iV.inv := by
    rw [Iso.inv_comp_eq, ← Category.assoc, Iso.eq_comp_inv]
    exact hi
  have hK : K.obj.map iV.inv.op ≫ K.obj.map n.op =
      K.obj.map q.op ≫ K.obj.map iU.inv.op :=
    (K.obj.map_comp iV.inv.op n.op).symm.trans
      ((congrArg (fun k => K.obj.map k.op) hiInv.symm).trans
        (K.obj.map_comp q.op iU.inv.op))
  have hcoord := affineFrobeniusKernelTensorEquiv_naturality A F p hp hA Φ SAV SAU fAb
    (e SV hV) (e SU (fR.comp hV)) hw
  change K.obj.map iU.inv.op
      (affineFrobeniusKernelTensorEquiv A F p hp hA Φ SAU
        (e SU (Scheme.EtaleAffineBasis.affineAlgebraHomEquiv (CommRingCat.of R)
          (CommAlgCat.of R C) U ((Scheme.Etale.forget (Spec (CommRingCat.of R))).map
            ((Scheme.AffineEtale.Spec (Spec (CommRingCat.of R))).map f) ≫ g)))) =
    K.obj.map n.op (K.obj.map iV.inv.op
      (affineFrobeniusKernelTensorEquiv A F p hp hA Φ SAV (e SV hV)))
  rw [hHom]
  exact (congrArg (K.obj.map iU.inv.op) hcoord.symm).trans
    (ConcreteCategory.congr_hom hK
      (affineFrobeniusKernelTensorEquiv A F p hp hA Φ SAV (e SV hV))).symm

/-- The actual finite algebra represents the literal restriction of the
original categorical kernel. Density glues the original affine equivalence. -/
def restrictedKernelSheafIso :
    finiteRepresentedSetSheaf (Scheme.FiniteEtale.AffineDescent.specCover R C) ≅
      underlyingSetSheaf
        ((etaleRestriction (Spec.map (CommRingCat.ofHom (algebraMap A R)))).obj
          (kernel (affineFrobenius A F p hp hA Φ -
            𝟙 (additiveCoefficient (Spec A) F)))) :=
  Functor.IsCoverDense.Types.sheafIso
    (G := Scheme.AffineEtale.Spec (Spec (CommRingCat.of R)))
    (NatIso.ofComponents
      (fun U => (restrictedKernelAffineEquiv A F p hp hA Φ R C e U.unop).toIso)
      (by
        intro U V f
        ext t
        exact restrictedKernelAffineEquiv_naturality A F p hp hA Φ R C e he f.unop t))

end AlgebraicGeometry.Scheme.EtaleCohomology.QuasiCoherent
