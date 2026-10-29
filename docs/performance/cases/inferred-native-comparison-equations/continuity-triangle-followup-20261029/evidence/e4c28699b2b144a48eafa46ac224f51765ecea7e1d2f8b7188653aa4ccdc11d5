/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Continuity.DiagramDirectImageTriangleComp
public import Aglib.AlgebraicGeometry.EtaleCohomology.Stalk.BaseChangeHorizontalUnit

/-! # Native right-adjoint square compatibility with cone triangles -/

@[expose] public noncomputable section
open CategoryTheory
namespace AlgebraicGeometry.Scheme.EtaleCohomology.Continuity
universe u
attribute [local instance] hasSheafifyLarge

lemma directImageTriangleIso_transport {X Y T : Scheme.{u}}
    (f g : Y ⟶ X) (e : f = g) (p : T ⟶ X) (q : T ⟶ Y)
    (hf : q ≫ f = p) (hg : q ≫ g = p) (K : AbelianSheaf.{u, u + 1} T) :
    eqToHom (congrArg (fun s => (directImage s).obj ((directImage q).obj K)) e) ≫
        (directImageTriangleIso g p q hg).hom.app K =
      (directImageTriangleIso f p q hf).hom.app K := by
  subst g
  simp only [eqToHom_refl, Category.id_comp]

/-- Contract the square's last native composition before inserting a cone triangle. -/
lemma directImageSquareIso_comp_hom {X₀ X₁ Y₀ Y₁ : Scheme.{u}}
    (f : X₁ ⟶ X₀) (h : Y₁ ⟶ Y₀) (v₀ : Y₀ ⟶ X₀) (v₁ : Y₁ ⟶ X₁)
    (he : v₁ ≫ f = h ≫ v₀) (M : AbelianSheaf.{u, u + 1} Y₁)
    {N : AbelianSheaf.{u, u + 1} X₀}
    (r : (directImage (v₁ ≫ f)).obj M ⟶ N) :
    (directImageSquareIso v₀ v₁ f h he).hom.app M ≫
        (directImageCompIso f v₁).hom.app M ≫ r =
      (directImageCompIso v₀ h).hom.app M ≫
        eqToHom (congrArg (fun s : Y₁ ⟶ X₀ => (directImage s).obj M) he.symm) ≫ r := by
  simp only [directImageSquareIso, Iso.trans_hom, Iso.symm_hom,
    NatTrans.comp_app, eqToIso.hom, eqToHom_app, Category.assoc,
    Iso.inv_hom_id_app_assoc]

/-- All right-adjoint square paths into the same cone point agree by native composition. -/
lemma directImageSquareTriangle {X₀ X₁ Y₀ Y₁ T : Scheme.{u}}
    (f : X₁ ⟶ X₀) (h : Y₁ ⟶ Y₀) (v₀ : Y₀ ⟶ X₀) (v₁ : Y₁ ⟶ X₁)
    (p₀ : T ⟶ X₀) (p₁ : T ⟶ X₁) (q₀ : T ⟶ Y₀) (q₁ : T ⟶ Y₁)
    (he : v₁ ≫ f = h ≫ v₀) (hp : p₁ ≫ f = p₀) (hq : q₁ ≫ h = q₀)
    (hi : q₀ ≫ v₀ = p₀) (hj : q₁ ≫ v₁ = p₁)
    (K : AbelianSheaf.{u, u + 1} T) :
    (directImage v₀).map ((directImageTriangleIso h q₀ q₁ hq).hom.app K) ≫
        (directImageTriangleIso v₀ p₀ q₀ hi).hom.app K =
      (directImageSquareIso v₀ v₁ f h he).hom.app ((directImage q₁).obj K) ≫
        (directImage f).map ((directImageTriangleIso v₁ p₁ q₁ hj).hom.app K) ≫
          (directImageTriangleIso f p₀ p₁ hp).hom.app K := by
  have hright := directImageTriangleIso_comp f v₁ p₀ p₁ q₁ hp hj K
  have htransport := directImageTriangleIso_comp_transport v₀ h (v₁ ≫ f) he
    p₀ q₀ q₁ hi hq (by rw [← Category.assoc, hj, hp]) K
  rw [← hright]
  exact ((directImageSquareIso_comp_hom f h v₀ v₁ he ((directImage q₁).obj K)
    ((directImageTriangleIso (v₁ ≫ f) p₀ q₁
      (by rw [← Category.assoc, hj, hp])).hom.app K)).trans htransport).symm

end AlgebraicGeometry.Scheme.EtaleCohomology.Continuity
