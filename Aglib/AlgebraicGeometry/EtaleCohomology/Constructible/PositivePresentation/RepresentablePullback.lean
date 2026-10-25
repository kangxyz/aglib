/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.PositivePresentation.FreeSet
public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.FiniteColimits.Partitions

/-! # Original free representables under actual scheme inverse image

The original section universal property and native inverse-image adjunction
identify the pullback of an original free scalar-quotient representable with
the original free representable of the actual base-changed etale object.
The construction holds at every modulus. A genuine finite-etale partition
therefore suffices for positive-modulus geometric constructibility; the
existence of that geometric partition is not assumed silently.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.Sheaf.TorsionFinitePresentation

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Constructible.PositivePresentation

universe u

attribute [local instance] hasSheafifyLarge

section Pullback

variable {X S : Scheme.{u}} (f : S ⟶ X) (n : ℕ) (U : X.Etale)

/-- The native inverse-image adjunction and the original killed-section
universal properties give the actual pullback Hom equivalence. -/
def freeZModPullbackHomEquiv (F : AbelianSheaf.{u, u + 1} S) :
    ((inverseImage f).obj (freeZModRepresentable.{u + 1} X.smallEtaleTopology n U) ⟶ F) ≃
      (freeZModRepresentable.{u + 1} S.smallEtaleTopology n ((siteBaseChange f).obj U) ⟶ F) :=
  ((inverseImageAdjunction f).homEquiv _ F).trans
    ((freeZModSectionsEquiv X.smallEtaleTopology n U ((directImage f).obj F)).trans
      (freeZModSectionsEquiv S.smallEtaleTopology n ((siteBaseChange f).obj U) F).symm)

/-- This equivalence retains the identical original evaluated section. -/
theorem freeZModPullbackHomEquiv_val (F : AbelianSheaf.{u, u + 1} S)
    (b : (inverseImage f).obj
      (freeZModRepresentable.{u + 1} X.smallEtaleTopology n U) ⟶ F) :
    (freeZModSectionsEquiv S.smallEtaleTopology n ((siteBaseChange f).obj U) F
      (freeZModPullbackHomEquiv f n U F b)).val =
    (freeZModSectionsEquiv X.smallEtaleTopology n U ((directImage f).obj F)
      ((inverseImageAdjunction f).homEquiv _ F b)).val :=
  congrArg Subtype.val
    ((freeZModSectionsEquiv S.smallEtaleTopology n ((siteBaseChange f).obj U) F).apply_symm_apply _)

/-- Original coefficient maps are preserved before exposing any concrete
free-cokernel carrier. -/
theorem freeZModPullbackHomEquiv_naturality {F G : AbelianSheaf.{u, u + 1} S}
    (b : (inverseImage f).obj
      (freeZModRepresentable.{u + 1} X.smallEtaleTopology n U) ⟶ F) (q : F ⟶ G) :
    freeZModPullbackHomEquiv f n U G (b ≫ q) = freeZModPullbackHomEquiv f n U F b ≫ q := by
  apply (freeZModSectionsEquiv S.smallEtaleTopology n ((siteBaseChange f).obj U) G).injective
  apply Subtype.ext
  calc
    _ = (freeZModSectionsEquiv X.smallEtaleTopology n U ((directImage f).obj G)
        ((inverseImageAdjunction f).homEquiv _ G (b ≫ q))).val :=
      freeZModPullbackHomEquiv_val f n U G (b ≫ q)
    _ = q.hom.app (op ((siteBaseChange f).obj U))
        ((freeZModSectionsEquiv X.smallEtaleTopology n U ((directImage f).obj F)
          ((inverseImageAdjunction f).homEquiv _ F b)).val) := by
      rw [(inverseImageAdjunction f).homEquiv_naturality_right]
      exact freeZModSectionsEquiv_naturality X.smallEtaleTopology n U _
        ((directImage f).map q)
    _ = q.hom.app (op ((siteBaseChange f).obj U))
        ((freeZModSectionsEquiv S.smallEtaleTopology n ((siteBaseChange f).obj U) F
          (freeZModPullbackHomEquiv f n U F b)).val) := by
      rw [freeZModPullbackHomEquiv_val]
    _ = _ := (freeZModSectionsEquiv_naturality S.smallEtaleTopology n
      ((siteBaseChange f).obj U) _ q).symm

/-- Actual inverse image takes the original free scalar-quotient generator
to the original free generator of the actual base-changed etale test. -/
def freeZModRepresentableInverseImageIso :
    (inverseImage f).obj (freeZModRepresentable.{u + 1} X.smallEtaleTopology n U) ≅
      freeZModRepresentable.{u + 1} S.smallEtaleTopology n ((siteBaseChange f).obj U) := by
  let e : coyoneda.obj (op ((inverseImage f).obj
      (freeZModRepresentable.{u + 1} X.smallEtaleTopology n U))) ≅
      coyoneda.obj (op (freeZModRepresentable.{u + 1} S.smallEtaleTopology n
        ((siteBaseChange f).obj U))) :=
    NatIso.ofComponents (fun F => (freeZModPullbackHomEquiv f n U F).toIso) (by
      intro F G q
      ext b
      exact freeZModPullbackHomEquiv_naturality f n U b q)
  exact (Coyoneda.fullyFaithful.preimageIso e).unop.symm

end Pullback

/-- Actual finite-etale partitions of the original base-changed test objects
prove positive-modulus constructibility. The geometric input here consists
of genuine finite structural maps on actual locally closed strata. -/
theorem freeZModRepresentable_isConstructible_of_finiteEtalePartitions
    {X : Scheme.{u}} (U : X.Etale) (n : ℕ) (hn : n ≠ 0)
    (hparts : ∀ V : X.affineOpens, ∃ p : FiniteLocallyClosedPartition V.1.toScheme,
      ∀ i, IsFinite ((siteBaseChange (p.inclusion i ≫ V.1.ι)).obj U).hom) :
    IsConstructible (freeZModRepresentable.{u + 1} X.smallEtaleTopology n U) := by
  intro V
  obtain ⟨p, hp⟩ := hparts V
  refine ⟨{ toFiniteLocallyClosedPartition := p, locally_constant := ?_ }⟩
  intro i
  have := hp i
  let e := ((inverseImageComp V.1.ι (p.inclusion i)).app
      (freeZModRepresentable.{u + 1} X.smallEtaleTopology n U)).symm ≪≫
    freeZModRepresentableInverseImageIso (p.inclusion i ≫ V.1.ι) n U
  exact (isFiniteLocallyConstant_iff_of_iso e).mpr
    (freeZModRepresentable_isFiniteLocallyConstant_of_isFinite
      ((siteBaseChange (p.inclusion i ≫ V.1.ι)).obj U) n hn)

end AlgebraicGeometry.Scheme.EtaleCohomology.Constructible.PositivePresentation
