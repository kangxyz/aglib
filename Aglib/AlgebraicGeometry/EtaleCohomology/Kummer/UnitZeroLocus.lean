/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Kummer.Coefficients
public import Aglib.AlgebraicGeometry.Sites.EtaleOpenRestriction
public import Aglib.AlgebraicGeometry.Sites.EtaleSectionZeroLocus

/-! # Trivial structure germs give actual etale-local zero neighborhoods for Gm -/

@[expose] public noncomputable section

open CategoryTheory Opposite AlgebraicGeometry
open GroupCohomology.Kummer.Coefficients

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Kummer

universe u

private theorem open_restriction_appTop {Y : Scheme.{u}} (W : Y.Opens)
    (i : W ⟶ ⊤) :
    Y.presheaf.map i.op ≫ W.ι.appLE W ⊤ (fun x _ => x.property) = W.ι.appTop := by
  have h := Hom.map_appLE W.ι (fun x (_ : x ∈ (⊤ : W.toScheme.Opens)) => x.property) i.op
  have ht : W.ι.appLE ⊤ ⊤ le_rfl = W.ι.appTop := by
    change W.ι.appTop ≫ W.toScheme.presheaf.map (𝟙 (op ⊤)) = W.ι.appTop
    rw [CategoryTheory.Functor.map_id, Category.comp_id]
  exact h.trans ht

/-- Triviality in the actual structure stalk implies local zero for the original Gm sheaf. -/
theorem mem_gm_sectionZeroLocus_of_germ_eq_one {X : Scheme.{u}} (U : X.Etale)
    (a : (gm X).obj.obj (op U)) (x : U.left)
    (hx : U.left.presheaf.germ ⊤ x trivial
      ((unitsSections X (op U) a).toMul : Γ(U.left, ⊤)) = 1) :
    x ∈ Etale.sectionZeroLocus (gm X).obj a := by
  let s : Γ(U.left, ⊤) := (unitsSections X (op U) a).toMul
  have hs : U.left.presheaf.germ ⊤ x trivial (s - 1) = 0 := by
    rw [map_sub, map_one, hx, sub_self]
  obtain ⟨W, i, hxW, hres⟩ :=
    U.left.toRingedSpace.exists_res_eq_zero_of_germ_eq_zero ⊤ (s - 1) ⟨x, trivial⟩ hs
  change U.left.Opens at W
  have hres' : U.left.presheaf.map i.op s = 1 := by
    simpa only [map_sub, map_one, sub_eq_zero] using hres
  have htop : W.ι.appTop s = 1 := by
    have h := ConcreteCategory.congr_hom (open_restriction_appTop W i) s
    exact h.symm.trans ((congrArg (W.ι.appLE W ⊤ (fun y _ => y.property)) hres').trans
      (map_one _))
  refine ⟨Etale.openChart U W, Etale.openChartHom U W, ⟨x, hxW⟩, rfl, ?_⟩
  apply (unitsSections X (op (Etale.openChart U W))).injective
  rw [map_zero]
  apply Additive.toMul.injective
  rw [unitsSections_naturality]
  apply Units.ext
  exact htop

end AlgebraicGeometry.Scheme.EtaleCohomology.Kummer
