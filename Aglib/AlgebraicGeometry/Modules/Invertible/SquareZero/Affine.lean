/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Invertible.Affine
public import Aglib.RingTheory.PicardGroup.SquareZero

/-!
# Actual affine line-bundle lifting across a square-zero extension

The lifted object is the associated sheaf of an actual lifted invertible
module. The comparison uses the original affine pullback isomorphism and
the original global-section reconstruction of the specified line bundle.
The rings are arbitrary commutative rings.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory

namespace AlgebraicGeometry.Scheme.Modules.Invertible

universe u
variable {R S : CommRingCat.{u}}

/-- An actual line bundle on an affine square-zero closed subscheme lifts
with a specified actual pullback isomorphism. -/
theorem exists_lineBundle_lift_of_square_zero (φ : R ⟶ S)
    (hsurj : Function.Surjective φ.hom) (hf : RingHom.ker φ.hom ^ 2 = ⊥)
    (L : LineBundle (Spec S)) :
    ∃ L' : LineBundle (Spec R),
      Nonempty ((pullback (Spec.map φ)).obj L'.val ≅ L.val) := by
  obtain ⟨N, hN, ⟨e⟩⟩ := ModuleCat.exists_invertible_lift_of_square_zero φ.hom hsurj hf
    (moduleSpecΓFunctor.obj L.val)
  let := hN
  exact ⟨tildeLineBundle N, ⟨(tildePullbackIso φ).app N ≪≫
    (tilde.functor S).mapIso e ≪≫ tildeGlobalSectionsIso L⟩⟩

/-- A prescribed pullback isomorphism between two affine line bundles lifts
to an actual isomorphism, with the original geometric forward map retained. -/
theorem exists_lineBundle_iso_lift_of_square_zero (φ : R ⟶ S)
    (hsurj : Function.Surjective φ.hom) (hf : RingHom.ker φ.hom ^ 2 = ⊥)
    (L M : LineBundle (Spec R))
    (e : (pullback (Spec.map φ)).obj L.val ≅ (pullback (Spec.map φ)).obj M.val) :
    ∃ e' : L.val ≅ M.val, (pullback (Spec.map φ)).map e'.hom = e.hom := by
  let N := moduleSpecΓFunctor.obj L.val
  let N' := moduleSpecΓFunctor.obj M.val
  let b : (tilde.functor R).obj N ≅ L.val := tildeGlobalSectionsIso L
  let b' : (tilde.functor R).obj N' ≅ M.val := tildeGlobalSectionsIso M
  let P := pullback (Spec.map φ)
  let F := ModuleCat.extendScalars φ.hom
  let t := tildePullbackIso φ
  let c : (tilde.functor S).obj (F.obj N) ≅ (tilde.functor S).obj (F.obj N') :=
    (t.app N).symm ≪≫ P.mapIso b ≪≫ e ≪≫ P.mapIso b'.symm ≪≫ t.app N'
  let c' := (tilde.fullyFaithfulFunctor (R := S)).preimageIso c
  obtain ⟨d, hd⟩ := ModuleCat.exists_iso_lift_of_square_zero φ.hom hsurj hf N N' c'
  let d' : L.val ≅ M.val := b.symm ≪≫ (tilde.functor R).mapIso d ≪≫ b'
  have hc : (tilde.functor S).map c'.hom = c.hom :=
    (tilde.fullyFaithfulFunctor (R := S)).map_preimage c.hom
  have hmap : P.map ((tilde.functor R).map d.hom) =
      P.map b.hom ≫ e.hom ≫ P.map b'.inv := by
    have h := (NatIso.naturality_2 t d.hom).symm
    change P.map ((tilde.functor R).map d.hom) =
      (t.app N).hom ≫ (tilde.functor S).map (F.map d.hom) ≫ (t.app N').inv at h
    rw [hd, hc] at h
    simpa only [c, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom,
      Functor.mapIso_inv, Category.assoc, Iso.hom_inv_id_assoc,
      Iso.hom_inv_id, Category.comp_id] using h
  refine ⟨d', ?_⟩
  change P.map (b.inv ≫ (tilde.functor R).map d.hom ≫ b'.hom) = e.hom
  rw [P.map_comp, P.map_comp, hmap]
  simp only [Category.assoc, Iso.map_inv_hom_id_assoc, Iso.map_inv_hom_id]
  exact CategoryTheory.Category.comp_id e.hom

end AlgebraicGeometry.Scheme.Modules.Invertible
