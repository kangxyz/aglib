/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.BaseChange.HigherDirectImage.Nonflat.ChartCoefficient

/-! # Original coefficient sections under chart refinement -/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory Opposite TopologicalSpace
namespace AlgebraicGeometry.Scheme.Modules.Nonflat
universe u
variable {X Y U V U' V' : Scheme.{u}}
  (p : Y ⟶ X) (a : U ⟶ X) (c : V ⟶ Y) (q : V ⟶ U)
  (a' : U' ⟶ X) (c' : V' ⟶ Y) (q' : V' ⟶ U')
  [IsOpenImmersion a] [IsOpenImmersion c]
  [IsOpenImmersion a'] [IsOpenImmersion c']
  (w : q ≫ a = c ≫ p) (w' : q' ≫ a' = c' ≫ p)
  (ha : a' ''ᵁ (⊤ : U'.Opens) ≤ a ''ᵁ (⊤ : U.Opens))
  (hc : c' ''ᵁ (⊤ : V'.Opens) ≤ c ''ᵁ (⊤ : V.Opens))
  {M : X.Modules} {N : Y.Modules} (ψ : M ⟶ (pushforward p).obj N)

/-- Refining both charts restricts the original coefficient section, independently
of the coordinate presentation of either chart. -/
theorem chartCoefficient_top_restrict
    (x : Γ(M, a ''ᵁ (⊤ : U.Opens))) :
    N.presheaf.map (homOfLE hc).op ((chartCoefficient p a c q w ψ).app ⊤ x) =
      (chartCoefficient p a' c' q' w' ψ).app ⊤
        (M.presheaf.map (homOfLE ha).op x) := by
  have hn : ψ.app (a' ''ᵁ ⊤) (M.presheaf.map (homOfLE ha).op x) =
      N.presheaf.map (homOfLE (show p ⁻¹ᵁ (a' ''ᵁ ⊤) ≤ p ⁻¹ᵁ (a ''ᵁ ⊤) from
        fun _ hx => ha hx)).op (ψ.app (a ''ᵁ ⊤) x) :=
    CategoryTheory.congr_fun (ψ.mapPresheaf.naturality (homOfLE ha).op) x
  let u : c ''ᵁ (⊤ : V.Opens) ⟶ p ⁻¹ᵁ (a ''ᵁ (⊤ : U.Opens)) :=
    homOfLE (chartCoefficient_image_le p a c q w ⊤)
  let v : c' ''ᵁ (⊤ : V'.Opens) ⟶ p ⁻¹ᵁ (a' ''ᵁ (⊤ : U'.Opens)) :=
    homOfLE (chartCoefficient_image_le p a' c' q' w' ⊤)
  let d : p ⁻¹ᵁ (a' ''ᵁ (⊤ : U'.Opens)) ⟶ p ⁻¹ᵁ (a ''ᵁ (⊤ : U.Opens)) :=
    homOfLE (fun _ hx => ha hx)
  simp only [chartCoefficient_app, AddCommGrpCat.comp_apply]
  change N.presheaf.map (homOfLE hc).op
      (N.presheaf.map u.op (ψ.app (a ''ᵁ ⊤) x)) =
    N.presheaf.map v.op (ψ.app (a' ''ᵁ ⊤) (M.presheaf.map (homOfLE ha).op x))
  have hm : N.presheaf.map (homOfLE hc).op
      (N.presheaf.map u.op (ψ.app (a ''ᵁ ⊤) x)) =
    N.presheaf.map v.op (N.presheaf.map d.op (ψ.app (a ''ᵁ ⊤) x)) := by
    rw [← N.presheaf.map_comp_apply, ← N.presheaf.map_comp_apply]
    congr 1
  exact hm.trans (congrArg (fun z : Γ(N, p ⁻¹ᵁ (a' ''ᵁ ⊤)) =>
    N.presheaf.map v.op z) hn.symm)

end AlgebraicGeometry.Scheme.Modules.Nonflat
