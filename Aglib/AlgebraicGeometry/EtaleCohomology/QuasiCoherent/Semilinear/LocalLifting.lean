/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.QuasiCoherent.Semilinear.Tensor
public import Aglib.AlgebraicGeometry.Morphisms.Etale.FrobeniusEquation
public import Mathlib.CategoryTheory.Sites.LocallySurjective

/-!
# Actual etale local lifts of original semilinear sections

The inhomogeneous polynomial cover supplies roots of the original section
operator. This does not deduce surjectivity from the finite fixed kernel, and
uses no higher-direct-image identification.
-/

@[expose] public noncomputable section

universe u

open CategoryTheory Opposite
open AlgebraicGeometry.Scheme.Modules
open scoped TensorProduct

namespace AlgebraicGeometry.Scheme.EtaleCohomology.QuasiCoherent

variable (A : CommRingCat.{u}) (F : (Spec A).Modules) [F.IsQuasicoherent]
  (p : ℕ) (hp : p.Prime) (hA : (p : A) = 0)
  (Φ : moduleSpecΓFunctor.obj F →ₛₗ[RingHom.frobeniusOfPrimeCastEqZero p hp hA]
    moduleSpecΓFunctor.obj F)
  [Module.Free A (moduleSpecΓFunctor.obj F)]
  [Module.Finite A (moduleSpecΓFunctor.obj F)]

section AlgebraTest

variable (B : CommAlgCat.{u} A)
  [Etale (Spec.map (CommRingCat.ofHom (algebraMap A B)))]

/-- Every original algebra-spectrum section lifts on a literal etale-surjective
root spectrum, retaining the original scalar map and section restriction. -/
theorem exists_etale_surjective_section_solution
    (s : Γ((pullback (Spec.map (CommRingCat.ofHom (algebraMap A B)))).obj F, ⊤)) :
    ∃ (C : CommAlgCat.{u} A) (f : B ⟶ C),
      Etale (Spec.map (CommRingCat.ofHom f.hom.toRingHom)) ∧
      Surjective (Spec.map (CommRingCat.ofHom f.hom.toRingHom)) ∧
      ∃ hC : Etale (Spec.map (CommRingCat.ofHom (algebraMap A C))),
      let := hC
      ∃ t : Γ((pullback (Spec.map (CommRingCat.ofHom (algebraMap A C)))).obj F, ⊤),
        @Eq Γ((pullback (Spec.map (CommRingCat.ofHom (algebraMap A C)))).obj F, ⊤)
          (affineFrobeniusSectionsAddHom A F p hp hA Φ C t - t)
          (sectionsAddHom (Spec A) F ((algSpec A).map f.op) s) := by
  obtain ⟨y, hy⟩ := (specTensorSectionsIso A F B).toLinearEquiv.surjective s
  subst s
  obtain ⟨C, f, hcov, hsurj, hC, z, hz⟩ :=
    Scheme.exists_etale_surjective_frobenius_solution A p hp hA Φ B y
  let := hC
  refine ⟨C, f, hcov, hsurj, hC, (tensorSectionsAddHom A F C) z, ?_⟩
  exact affineFrobenius_solution_specTensor A F p hp hA Φ B C f y z hz

/-- The original image sieve on an algebra-spectrum test contains its actual
inhomogeneous root cover. -/
theorem affineFrobenius_sub_id_imageSieve_spec
    (s : (additiveCoefficient (Spec A) F).obj.obj
      (op (Scheme.Etale.mk (Spec.map (CommRingCat.ofHom (algebraMap A B)))))) :
    Presheaf.imageSieve ((affineFrobenius A F p hp hA Φ) - 𝟙 _).hom s ∈
      (Spec A).smallEtaleTopology
        (Scheme.Etale.mk (Spec.map (CommRingCat.ofHom (algebraMap A B)))) := by
  obtain ⟨C, f, hcov, hsurj, hC, t, ht⟩ :=
    exists_etale_surjective_section_solution A F p hp hA Φ B s.down
  let := hcov
  let := hC
  let V := Scheme.Etale.mk (Spec.map (CommRingCat.ofHom (algebraMap A C)))
  let q₀ := (algSpec A).map f.op
  let q : V ⟶ Scheme.Etale.mk (Spec.map (CommRingCat.ofHom (algebraMap A B))) :=
    MorphismProperty.Over.homMk q₀.left q₀.w
  have hc : Sieve.ofArrows (fun _ : PUnit.{1} => V) (fun _ => q) ∈
      (Spec A).smallEtaleTopology _ := by
    rw [Scheme.ofArrows_mem_smallEtaleTopology_iff]
    change (⋃ _ : PUnit.{1}, Set.range
      (Spec.map (CommRingCat.ofHom f.hom.toRingHom))) = Set.univ
    simp only [Set.iUnion_const]
    exact Set.range_eq_univ.mpr hsurj.surj
  apply (Spec A).smallEtaleTopology.superset_covering ?_ hc
  rw [Sieve.ofArrows, Sieve.generate_le_iff, Presieve.ofArrows_le_iff]
  intro _
  refine ⟨ULift.up t, ?_⟩
  apply ULift.ext
  exact ht

end AlgebraTest

/-- An arbitrary original affine structural arrow is normalized by the actual
fully faithful spectrum map, before choosing its scalar action. -/
theorem affineFrobenius_sub_id_imageSieve_affine {R : CommRingCat.{u}}
    (f : Spec R ⟶ Spec A) [Etale f]
    (s : (additiveCoefficient (Spec A) F).obj.obj (op (Scheme.Etale.mk f))) :
    Presheaf.imageSieve ((affineFrobenius A F p hp hA Φ) - 𝟙 _).hom s ∈
      (Spec A).smallEtaleTopology (Scheme.Etale.mk f) := by
  obtain ⟨g, hg⟩ : ∃ g : A ⟶ R, Spec.map g = f :=
    ⟨Spec.preimage f, Spec.map_preimage f⟩
  subst f
  let : Algebra A R := g.hom.toAlgebra
  exact affineFrobenius_sub_id_imageSieve_spec A F p hp hA Φ (CommAlgCat.of A R) s

/-- The original semilinear difference is etale-locally surjective. Affine root
covers extend to all tests by the native cover-dense affine site. -/
theorem affineFrobenius_sub_id_isLocallySurjective :
    Presheaf.IsLocallySurjective (Spec A).smallEtaleTopology
      ((affineFrobenius A F p hp hA Φ) - 𝟙 _).hom := by
  constructor
  intro U s
  let H := Scheme.AffineEtale.Spec (Spec A)
  apply (Spec A).smallEtaleTopology.transitive
    (H.is_cover_of_isCoverDense (Spec A).smallEtaleTopology U)
  intro V g ⟨⟨Z, lift, m, fac⟩⟩
  rw [← fac, Sieve.pullback_comp]
  apply (Spec A).smallEtaleTopology.pullback_stable
  rw [Presheaf.pullback_imageSieve]
  let : Etale Z.hom := Z.prop
  exact affineFrobenius_sub_id_imageSieve_affine A F p hp hA Φ Z.hom
    ((additiveCoefficient (Spec A) F).obj.map m.op s)

/-- The actual additive coefficient difference is an epimorphism, independently
of any fixed-kernel finiteness or higher-direct-image comparison. -/
theorem affineFrobenius_sub_id_epi : Epi ((affineFrobenius A F p hp hA Φ) - 𝟙 _) := by
  let := affineFrobenius_sub_id_isLocallySurjective A F p hp hA Φ
  infer_instance

end AlgebraicGeometry.Scheme.EtaleCohomology.QuasiCoherent
