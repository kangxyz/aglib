/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.CategoryTheory.Adjunction.Triple
public import Aglib.CategoryTheory.Adjunction.MateHomEquiv

/-! # Original identity normalization of the canonical outer-adjoint comparison -/

@[expose] public noncomputable section
namespace CategoryTheory.Adjunction
variable {A : Type*} [Category* A] {J Q S : A ⥤ A}
  (t : Triple J Q S) [J.Full] [J.Faithful]

/-- Two original conjugate identity comparisons normalize the canonical triple map. -/
theorem Triple.leftToRight_identity (eJ : J ≅ 𝟭 A) (eQ : Q ≅ 𝟭 A) (eS : S ≅ 𝟭 A)
    (hJ : conjugateEquiv Adjunction.id t.adj₁ eJ.hom = eQ.inv)
    (hQ : conjugateEquiv Adjunction.id t.adj₂ eQ.hom = eS.inv) :
    t.leftToRight = eJ.hom ≫ eS.inv := by
  ext K
  have h₁ := homEquiv_to_identity t.adj₁ eJ.hom K
  rw [hJ, Adjunction.homEquiv_apply] at h₁
  have h₂ := homEquiv_to_identity t.adj₂ eQ.hom (J.obj K)
  rw [hQ, Adjunction.homEquiv_apply] at h₂
  have hi : inv (t.adj₁.unit.app K) = Q.map (eJ.hom.app K) ≫ eQ.hom.app K := by
    apply (cancel_epi (t.adj₁.unit.app K)).mp
    rw [IsIso.hom_inv_id, ← Category.assoc, h₁, Iso.inv_hom_id_app]
  have hn := eQ.hom.naturality (eJ.hom.app K)
  change Q.map (eJ.hom.app K) ≫ eQ.hom.app K =
    eQ.hom.app (J.obj K) ≫ eJ.hom.app K at hn
  rw [Triple.leftToRight_app, ← S.map_inv, hi, hn, S.map_comp, ← Category.assoc, h₂]
  exact (eS.inv.naturality (eJ.hom.app K)).symm

end CategoryTheory.Adjunction
