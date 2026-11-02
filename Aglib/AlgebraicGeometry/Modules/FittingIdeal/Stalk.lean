/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.FittingIdeal.Pullback
public import Aglib.AlgebraicGeometry.Modules.Pullback.LocalSpectrum
public import Aglib.AlgebraicGeometry.IdealSheaf.Colon

/-!
# Fitting ideals at the original module stalk

For an actual finitely presented module sheaf, the stalk ideal of its
Fitting ideal sheaf is the Fitting ideal of its original module stalk.
The proof uses the original pullback to the local spectrum, its existing
section/stalk comparison, and the original structure-sheaf germ map.
No Noetherian hypothesis or replacement stalk module is used.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory Opposite TopologicalSpace

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}} (M : X.Modules)

/-- Fitting ideal sheaves retain the actual module stalk and its original
local-ring action. Finite presentation supplies finite type after pullback. -/
theorem fittingIdealSheaf_stalkIdeal [M.IsFinitePresentation]
    (hM : QuasiCoherent.affineLocallyFiniteType X M) (k : ℕ) (x : X) :
    (fittingIdealSheaf M hM k).stalkIdeal x =
      Module.fittingIdeal (X.presheaf.stalk x) ((moduleStalk X x).obj M) k := by
  let A : CommRingCat.{u} := X.presheaf.stalk x
  let g := X.fromSpecStalk x
  let N : (Spec A).Modules := (pullback g).obj M
  have hN : QuasiCoherent.affineLocallyFiniteType (Spec A) N :=
    QuasiCoherent.affineLocallyFiniteType_pullback_of_finitePresentation g M
  have : Module.Finite Γ(Spec A, ⊤) Γ(N, ⊤) :=
    QuasiCoherent.finite_sections_of_affineLocallyFiniteType N hN ⟨⊤, isAffineOpen_top _⟩
  have hscalar : Module.fittingIdeal A (moduleSpecΓFunctor.obj N) k =
      (Module.fittingIdeal Γ(Spec A, ⊤) Γ(N, ⊤) k).map (Scheme.ΓSpecIso A).hom.hom := by
    have h := Module.fittingIdeal_compHom_of_bijective (M := Γ(N, ⊤))
      (Scheme.ΓSpecIso A).inv.hom (ConcreteCategory.bijective_of_isIso _) k
    exact h.trans (Ideal.map_comap_of_equiv
      (Scheme.ΓSpecIso A).commRingCatIsoToRingEquiv).symm
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  have hpre : (⊤ : (Spec A).Opens) ≤ g ⁻¹ᵁ U := by
    intro z _
    exact (Scheme.range_fromSpecStalk.le ⟨z, rfl⟩).mem_open U.isOpen hxU
  have happ : g.appLE U ⊤ hpre ≫ (Scheme.ΓSpecIso A).hom =
      X.presheaf.germ U x hxU := by
    rw [Scheme.Hom.appLE, Scheme.fromSpecStalk_app hxU]
    have hcomp : (homOfLE (show g ⁻¹ᵁ U ≤ ⊤ from le_top)).op ≫
        (homOfLE hpre).op = 𝟙 (op (⊤ : (Spec A).Opens)) := Subsingleton.elim _ _
    simp only [Category.assoc, ← Functor.map_comp, hcomp]
    rw [CategoryTheory.Functor.map_id, Category.id_comp, Iso.inv_hom_id, Category.comp_id]
  calc
    (fittingIdealSheaf M hM k).stalkIdeal x =
        (Module.fittingIdeal Γ(X, U) Γ(M, U) k).map (X.presheaf.germ U x hxU).hom :=
      (fittingIdealSheaf M hM k).stalkIdeal_eq_map ⟨U, hU⟩ x hxU
    _ = ((Module.fittingIdeal Γ(X, U) Γ(M, U) k).map (g.appLE U ⊤ hpre).hom).map
        (Scheme.ΓSpecIso A).hom.hom := by
      rw [Ideal.map_map, ← CommRingCat.hom_comp, happ]
    _ = (Module.fittingIdeal Γ(Spec A, ⊤) Γ(N, ⊤) k).map
        (Scheme.ΓSpecIso A).hom.hom :=
      congrArg (fun J => J.map (Scheme.ΓSpecIso A).hom.hom)
        (fittingIdeal_sections_pullback g M hM ⟨U, hU⟩
          ⟨⊤, isAffineOpen_top _⟩ hpre k).symm
    _ = Module.fittingIdeal A (moduleSpecΓFunctor.obj N) k := hscalar.symm
    _ = Module.fittingIdeal (X.presheaf.stalk x) ((moduleStalk X x).obj M) k :=
      (Module.fittingIdeal_congr (stalkFromSpecStalkSectionsIso X x M).toLinearEquiv k).symm

end AlgebraicGeometry.Scheme.Modules
