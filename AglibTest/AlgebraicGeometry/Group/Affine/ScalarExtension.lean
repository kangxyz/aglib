/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.Group.Affine.ScalarExtension

/-! The native Hopf Spec comparison retains arbitrary commutative bases and original maps. -/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry Scheme
open MonoidalCategory MonObj
open scoped TensorProduct

universe u

variable (k R : Type u) [CommRing k] [CommRing R] [Algebra k R]
  (A B : CommHopfAlgCat.{u} k)

example :
    (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap k R)))).mapGrp.obj
        ((hopfSpec (CommRingCat.of k)).obj (op A)) ≅
      (hopfSpec (CommRingCat.of R)).obj (op (CommHopfAlgCat.of R (R ⊗[k] A))) :=
  hopfSpecScalarExtensionIso k R A

example :
    (hopfSpecScalarExtensionIso k R A).inv.hom.hom.left ≫ pullback.fst _ _ =
      Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeRight : A →ₐ[k] R ⊗[k] A).toRingHom) :=
  hopfSpecScalarExtensionIso_inv_fst k R A

example :
    η ≫ (hopfSpecScalarExtensionIso k R A).hom.hom.hom = η :=
  hopfSpecScalarExtensionIso_one k R A

example :
    μ ≫ (hopfSpecScalarExtensionIso k R A).hom.hom.hom =
      ((hopfSpecScalarExtensionIso k R A).hom.hom.hom ⊗ₘ
        (hopfSpecScalarExtensionIso k R A).hom.hom.hom) ≫ μ :=
  hopfSpecScalarExtensionIso_mul k R A

example (f : A ⟶ B) :
    (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap k R)))).mapGrp.map
        ((hopfSpec (CommRingCat.of k)).map f.op) ≫
        (hopfSpecScalarExtensionIso k R A).hom =
      (hopfSpecScalarExtensionIso k R B).hom ≫
        (hopfSpec (CommRingCat.of R)).map ((hopfScalarExtension k R).map f).op :=
  hopfSpecScalarExtensionIso_hom_naturality k R f

example (f : A ⟶ B) (r : R) (a : A) :
    (hopfScalarExtension k R).map f (r ⊗ₜ[k] a) = r ⊗ₜ[k] f.hom a :=
  hopfScalarExtension_map_tmul k R f r a

example :
    hopfSpec (CommRingCat.of k) ⋙
        (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap k R)))).mapGrp ≅
      (hopfScalarExtension k R).op ⋙ hopfSpec (CommRingCat.of R) :=
  hopfSpecScalarExtensionNatIso k R

variable {S : Type u} [CommRing S] [Algebra k S]

example (g : R →ₐ[k] S) :
    (hopfSpecScalarExtensionIso k S A).inv.hom.hom.left ≫
        pullback.map
          (Spec (CommRingCat.of A) ↘ Spec (CommRingCat.of k))
          (Spec (CommRingCat.of S) ↘ Spec (CommRingCat.of k))
          (Spec (CommRingCat.of A) ↘ Spec (CommRingCat.of k))
          (Spec (CommRingCat.of R) ↘ Spec (CommRingCat.of k))
          (𝟙 _) (Spec.map (CommRingCat.ofHom g.toRingHom)) (𝟙 _) (by simp)
          (by
            change Spec.map (CommRingCat.ofHom (algebraMap k S)) ≫ 𝟙 _ =
              Spec.map (CommRingCat.ofHom g.toRingHom) ≫
                Spec.map (CommRingCat.ofHom (algebraMap k R))
            rw [Category.comp_id, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
            congr 1
            ext r
            exact (g.commutes r).symm) =
      Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.map g (AlgHom.id k A)).toRingHom) ≫
        (hopfSpecScalarExtensionIso k R A).inv.hom.hom.left :=
  hopfSpecScalarExtensionIso_base_naturality k R A g
