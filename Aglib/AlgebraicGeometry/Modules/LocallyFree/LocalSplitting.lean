/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.Modules.Epimorphisms
public import Aglib.AlgebraicGeometry.Modules.Generators.LocalLifting
public import Aglib.AlgebraicGeometry.Modules.LocallyFree.LocalBases
public import Aglib.AlgebraicGeometry.Modules.Exact
/-!
# Local splitting of epimorphisms onto finite locally free sheaves

A finite basis of the target has simultaneous local lifts. The free-sheaf
universal property turns those lifts into a right inverse after shrinking the
open. The resulting splitting is local; no assertion of global projectivity
or a globally split exact structure is made.
-/
@[expose] public section


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

namespace AlgebraicGeometry.Scheme.Modules
variable {X : Scheme.{u}} {M N : X.Modules}

/-- A surjection to a sheaf with a finite basis on `U` has a section on a
neighborhood of each point of `U`. -/
theorem exists_local_section_of_finite_basis (p : M ⟶ N) [Epi p]
    (U : X.Opens) (G : (N.over U).GeneratingSections) [G.IsFiniteType] [IsIso G.π]
    (x : X) (hx : x ∈ U) :
    ∃ (V : X.Opens) (_hVU : V ≤ U), x ∈ V ∧
      ∃ s : N.over V ⟶ M.over V, s ≫ p.over V = 𝟙 _ := by
  obtain ⟨V, hVU, hxV, t, ht⟩ := exists_finite_local_lifts p U
    (fun i : G.I => (G.s i).val (op (Over.mk (𝟙 U)))) x hx
  let GV := restrictLocalBasis hVU G
  let l : SheafOfModules.free G.I ⟶ M.over V :=
    (M.over V).freeHomEquiv.symm (fun i => sectionOver M V (t i))
  have hl : l ≫ p.over V = GV.π := by
    apply (N.over V).freeHomEquiv.injective
    funext i
    rw [SheafOfModules.freeHomEquiv_comp_apply]
    dsimp only [l]
    rw [Equiv.apply_symm_apply, sectionsMap_over_sectionOver]
    refine Eq.trans ?_ (congrFun ((N.over V).freeHomEquiv.apply_symm_apply GV.s) i).symm
    apply over_sections_ext V
    rw [sectionOver_top, ht i]
    exact (restrictLocalBasis_s_top hVU G i).symm
  refine ⟨V, hVU, hxV, inv GV.π ≫ l, ?_⟩
  rw [Category.assoc, hl, IsIso.inv_hom_id]

/-- Restriction to the site over an open, with `X.Modules` as source. -/
def overRestriction (U : X.Opens) :
    X.Modules ⥤ SheafOfModules.{u} (X.ringCatSheaf.over U) :=
  SheafOfModules.overFunctor.{u} X.ringCatSheaf U

/-- Restriction to the site over an open is a right adjoint as well as the
left adjoint supplied by its extension-by-direct-image description. -/
instance overRestriction_isRightAdjoint (U : X.Opens) :
    (overRestriction U).IsRightAdjoint := by
  dsimp [overRestriction, SheafOfModules.overFunctor]
  exact (SheafOfModules.PullbackConstruction.adjunction
    (F := Over.forget U) (J := (Opens.grothendieckTopology X).over U)
    (K := Opens.grothendieckTopology X) (R := X.ringCatSheaf)
    (S := X.ringCatSheaf.over U) (𝟙 _)).isRightAdjoint

instance overRestriction_isLeftAdjoint (U : X.Opens) :
    (overRestriction U).IsLeftAdjoint := by
  exact (SheafOfModules.overPushforwardOverAdj (R := X.ringCatSheaf) U).isLeftAdjoint

instance overRestriction_additive (U : X.Opens) :
    (overRestriction U).Additive where
  map_add := by intros; rfl

/-- Short exact sequences remain short exact on the site over an open. -/
theorem shortExact_over {S : ShortComplex X.Modules} (hS : S.ShortExact) (U : X.Opens) :
    (S.map (overRestriction U)).ShortExact := by
  exact hS.map_of_exact _

/-- A short exact sequence whose quotient is finite locally free splits on
a neighborhood of every point. -/
theorem exists_local_splitting {S : ShortComplex X.Modules} (hS : S.ShortExact)
    [IsFiniteLocallyFree X S.X₃] (x : X) :
    ∃ (U : X.Opens), x ∈ U ∧
      Nonempty (S.map (overRestriction U)).Splitting := by
  obtain ⟨U, hxU, G, hG, hfin⟩ :=
    finiteLocallyFree_iff_pointwise.mp (inferInstance : IsFiniteLocallyFree X S.X₃) x
  let := hS.epi_g
  obtain ⟨V, _, hxV, s, hs⟩ := exists_local_section_of_finite_basis S.g U G x hxU
  let hV := shortExact_over hS V
  exact ⟨V, hxV, ⟨ShortComplex.Splitting.ofExactOfSection _ hV.exact s hs hV.mono_f⟩⟩

end AlgebraicGeometry.Scheme.Modules
