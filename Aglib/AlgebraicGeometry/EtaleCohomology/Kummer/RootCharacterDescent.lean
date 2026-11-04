/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.H1.RepresentedCharacterDescent
public import Aglib.AlgebraicGeometry.EtaleCohomology.H1.MarkedCoefficients
public import Aglib.AlgebraicGeometry.EtaleCohomology.Kummer.BoundaryNaturality

/-! Original roots-character descent along a connected scheme. -/

open CategoryTheory CategoryTheory.Limits MonoidalCategory MonObj
open GroupCohomology.Kummer.Coefficients GroupCohomology.Kummer.CoefficientBaseChange

@[expose] public noncomputable section

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Kummer

open Scheme.Group

universe u

attribute [local instance] hasSheafifyLarge Over.cartesianMonoidalCategory

/-- Positive annihilation makes the original global section group torsion. -/
theorem isAddTorsion_globalSections_of_killed {S : Scheme.{u}}
    (L : AbelianSheaf.{u, u + 1} S) (n : ℕ) (hn : 0 < n)
    (h : n • 𝟙 L = 0) : IsAddTorsion ((globalSections S).obj L) := by
  let F := globalSections S
  intro x
  refine isOfFinAddOrder_iff_nsmul_eq_zero.mpr ⟨n, hn, ?_⟩
  have hm := congrArg F.map h
  rw [F.map_nsmul, F.map_id, F.map_zero] at hm
  have hx := congrArg (fun g : F.obj L ⟶ F.obj L => g x) hm
  exact hx

variable (k : Type u) [Field k] [IsSepClosed k] {X : Scheme.{u}}
  [ConnectedSpace X] [CompactSpace X] [QuasiSeparatedSpace X]
  (p : X ⟶ Spec (.of k)) (H : Grp (Over (Spec (.of k))))
  [IsCommMonObj H.X] [IsFinite H.X.hom] [Etale H.X.hom]
  (n : ℕ) (hn : 0 < n) (hi : IsUnit (n : Γ(Spec (.of k), ⊤)))
  (hh : (𝟙 H.X : H.X ⟶ H.X) ^ n = 1)

set_option hygiene false in
local notation "K" => MultiplicativeGroup.rootsGroupScheme (Spec (.of k)) n

/-- All original roots coefficient morphisms after pullback are original field
root characters, via the same represented sheaf and roots base-change iso. -/
def rootsCharacterPullbackEquiv :
    (H ⟶ K) ≃ (representedSheaf (baseChangedGroup p H) ⟶ mu X n) :=
  letI : Etale (K).X.hom := RootsFiniteEtale.rootsScheme_etale (Spec (.of k)) n hn hi
  let hH := isAddTorsion_globalSections_of_killed (representedSheaf H) n hn
    (representedSheaf_killedBy_of_identity_pow H n hh)
  let hK := isAddTorsion_globalSections_of_killed (mu (Spec (.of k)) n) n hn
    (mu_killedBy (Spec (.of k)) n)
  let E := representedPullbackHomEquiv k p H K hH hK
  let r := MarkedCoefficients.representedSheafIso (MultiplicativeBaseChange.rootsBaseChangeIso p n)
  E.trans ((Iso.refl _).homCongr r)

/-- The forward map is the represented map of the original pulled-back character. -/
theorem rootsCharacterPullbackEquiv_apply (χ : H ⟶ K) :
    rootsCharacterPullbackEquiv k p H n hn hi hh χ =
      representedSheafMap ((Over.pullback p).mapGrp.map χ ≫
        (MultiplicativeBaseChange.rootsBaseChangeIso p n).hom) := by
  let : Etale (K).X.hom := RootsFiniteEtale.rootsScheme_etale (Spec (.of k)) n hn hi
  let hH := isAddTorsion_globalSections_of_killed (representedSheaf H) n hn
    (representedSheaf_killedBy_of_identity_pow H n hh)
  let hK := isAddTorsion_globalSections_of_killed (mu (Spec (.of k)) n) n hn
    (mu_killedBy (Spec (.of k)) n)
  let E := representedPullbackHomEquiv k p H K hH hK
  let r := representedSheafMap (MultiplicativeBaseChange.rootsBaseChangeIso p n).hom
  let g := (Over.pullback p).mapGrp.map χ
  change (𝟙 _ ≫ E χ ≫ r) =
    representedSheafMap (g ≫ (MultiplicativeBaseChange.rootsBaseChangeIso p n).hom)
  have h := representedPullbackHomEquiv_apply k p H K hH hK χ
  exact (Category.id_comp _).trans ((congrArg (fun f => f ≫ r) h).trans
    (representedSheafMap_comp g (MultiplicativeBaseChange.rootsBaseChangeIso p n).hom).symm)

end AlgebraicGeometry.Scheme.EtaleCohomology.Kummer
