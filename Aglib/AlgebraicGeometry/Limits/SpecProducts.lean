/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.AlgebraicGeometry.Limits
public import Aglib.AlgebraicGeometry.AffineScheme.StructureMap

/-!
# Spectrum comparisons for finite products

General declarations relocated from R5 revision
`e6d63abca2403f50b6b413101ad7f6a7f2e0e2c7`.
Original namespaces, objects, maps, hypotheses and source boundaries are retained.
-/


/-!
Native migration from `R5Lab.Aglib.AlgebraicGeometry.Limits.SpecProducts` at R5 revision
`f8a3314ddecffcada2ec721d26d56a937bed9690`, SHA-256
`01120e4aea0ca3c12afd0ded493083339777e7412a24117c0a183a6303ce9be8`.
Original objects, maps, universes and explicit hypotheses are retained.
Native providers replace duplicate implementations.
-/

@[expose] public section

noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Limits AlgebraicGeometry
universe u

namespace AlgebraicGeometry.Scheme.Pullback.SpecProducts

/-- The Spec of a product is an actual coproduct of schemes. -/
def specProductIso (A B : Type u) [CommRing A] [CommRing B] :
    Spec (.of (A × B)) ≅ (Spec (.of A) ⨿ Spec (.of B)) :=
  (asIso (coprodSpec A B)).symm

@[reassoc, simp] theorem specProductIso_inl (A B : Type u) [CommRing A] [CommRing B] :
    coprod.inl ≫ (specProductIso A B).inv =
      Spec.map (CommRingCat.ofHom (RingHom.fst A B)) := coprodSpec_inl A B

@[reassoc, simp] theorem specProductIso_inr (A B : Type u) [CommRing A] [CommRing B] :
    coprod.inr ≫ (specProductIso A B).inv =
      Spec.map (CommRingCat.ofHom (RingHom.snd A B)) := coprodSpec_inr A B

variable {A B : Type u} [CommRing A] [CommRing B]
theorem specProductIso_naturality (f : A →+* B) :
    Spec.map (CommRingCat.ofHom (f.prodMap f)) ≫ (specProductIso A A).hom =
      (specProductIso B B).hom ≫ coprod.map (Spec.map (CommRingCat.ofHom f))
        (Spec.map (CommRingCat.ofHom f)) := by
  apply (cancel_mono (specProductIso A A).inv).mp
  apply (cancel_epi (specProductIso B B).inv).mp
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id, Iso.inv_hom_id_assoc]
  apply coprod.hom_ext
  · simp only [specProductIso_inl_assoc, specProductIso_inl, coprod.inl_map_assoc,
      ← Spec.map_comp]
    rfl
  · simp only [specProductIso_inr_assoc, specProductIso_inr, coprod.inr_map_assoc,
      ← Spec.map_comp]
    rfl

theorem specProductIso_over (k A : Type u) [Field k] [CommRing A] [Algebra k A] :
    (specProductIso A A).hom ≫
      coprod.desc (Spec.algebraMap k A)
          (Spec.algebraMap k A) =
        Spec.algebraMap k (A × A) := by
  apply (cancel_epi (specProductIso A A).inv).mp
  simp only [Iso.inv_hom_id_assoc]
  apply coprod.hom_ext
  · simp only [coprod.inl_desc, specProductIso_inl_assoc]
    unfold Spec.algebraMap
    rw [← Spec.map_comp]
    rfl
  · simp only [coprod.inr_desc, specProductIso_inr_assoc]
    unfold Spec.algebraMap
    rw [← Spec.map_comp]
    rfl

end AlgebraicGeometry.Scheme.Pullback.SpecProducts

namespace AlgebraicGeometry.Scheme.Pullback.OpenIntersection

/-- The concrete finite product cone, allowing a smaller index universe. -/
def finitePiFan {n : ℕ} (R : Fin n → CommRingCat.{u}) : Fan R :=
  Fan.mk (.of (∀ i, R i)) (fun i => CommRingCat.ofHom (Pi.evalRingHom (fun j => R j) i))

def finitePiFanIsLimit {n : ℕ} (R : Fin n → CommRingCat.{u}) : IsLimit (finitePiFan R) where
  lift s := CommRingCat.ofHom (RingHom.pi fun i => (s.π.app ⟨i⟩).hom)
  fac s j := by
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro x
    rfl
  uniq s m hm := by
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro x
    funext i
    exact congrArg (fun f : s.pt ⟶ R i => f x) (hm ⟨i⟩)

/-- Universe-flexible specialization of mathlib's finite-product spectrum theorem. -/
instance sigmaSpec_fin_isIso {n : ℕ} (R : Fin n → CommRingCat.{u}) : IsIso (sigmaSpec R) := by
  have he : sigmaSpec R =
      (colimit.isoColimitCocone ⟨_,
        (IsColimit.precomposeHomEquiv Discrete.natIsoFunctor.symm _).symm (isColimitOfPreserves
          Scheme.Spec (Fan.IsLimit.op (finitePiFanIsLimit R)))⟩).hom := by
    ext1
    simp
    rfl
  rw [he]
  infer_instance

/-- The literal spectrum of a finite product is the coproduct of the spectra. -/
def piSpecIso (R : Type u) [CommRing R] (n : ℕ) :
    Spec (.of (Fin n → R)) ≅ ∐ (fun _ : Fin n => Spec (.of R)) :=
  (asIso (sigmaSpec (fun _ : Fin n => CommRingCat.of R))).symm

@[reassoc, simp] theorem piSpecIso_component (R : Type u) [CommRing R] (n : ℕ) (i : Fin n) :
    Spec.map (CommRingCat.ofHom (Pi.evalRingHom (fun _ : Fin n => R) i)) ≫
      (piSpecIso R n).hom = Sigma.ι (fun _ : Fin n => Spec (.of R)) i := by
  have h := ι_sigmaSpec (fun _ : Fin n => CommRingCat.of R) i
  rw [← h]
  simp [piSpecIso]

end AlgebraicGeometry.Scheme.Pullback.OpenIntersection
