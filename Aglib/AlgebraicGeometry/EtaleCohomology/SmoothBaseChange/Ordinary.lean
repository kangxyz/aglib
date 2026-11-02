/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.SmoothBaseChange.OrdinaryConnectedCharts
public import Aglib.AlgebraicGeometry.Morphisms.Smooth.ConnectedLocalFactorization
public import Aglib.AlgebraicGeometry.Morphisms.Smooth.RelativeDimension
public import Aglib.AlgebraicGeometry.Sites.EtaleLocalIsomorphism

/-! # Canonical ordinary smooth base change for bounded coefficients

Every original etale test is refined around each of its points by the actual
connected local factorization of its smooth structural map. The original
canonical mate is invertible on that refinement. The native locally-bijective
sheaf criterion then detects the original exchange, without a conservative
direct-image assertion or any global quasi-compactness hypothesis.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.EtaleCohomology.SmoothBaseChange
open Continuity
universe u
attribute [local instance] hasSheafifyLarge

/-- The literal ordinary Cartesian exchange is invertible under arbitrary
smooth base change for every original abelian coefficient annihilated by a
specified nonzero natural number. No finite-LCC or global qcqs hypothesis occurs. -/
theorem baseChangeMap_smooth_bounded_isIso
    {X S S' : Scheme.{u}} (f : X ⟶ S) (g : S' ⟶ S) [Smooth g]
    (F : AbelianSheaf.{u, u + 1} X) (n : ℕ) (hn : 0 < n) (hF : n • 𝟙 F = 0) :
    IsIso ((baseChangeMap f (pullback.fst g f) g (pullback.snd g f)
      pullback.condition).app F) := by
  apply Scheme.Etale.isIso_of_pointed_refinement_bijective
  intro T t
  let : Smooth (T.hom ≫ g) := inferInstance
  obtain ⟨O, d, ht, hd⟩ := Scheme.exists_smoothOfRelativeDimension_open (T.hom ≫ g) t
  let : SmoothOfRelativeDimension d (O.ι ≫ (T.hom ≫ g)) := hd
  obtain ⟨V, W, w, _, hw, _, hqc, hqs, hgc, hopen, het, htriangle⟩ :=
    Scheme.exists_connected_local_factorization (O.ι ≫ (T.hom ≫ g)) d ⟨t, ht⟩
  let k := W.ι ≫ pullback.snd V.hom (O.ι ≫ (T.hom ≫ g))
  let p := W.ι ≫ pullback.fst V.hom (O.ι ≫ (T.hom ≫ g))
  let : Etale k := het
  let U : S'.Etale := Scheme.Etale.mk ((k ≫ O.ι) ≫ T.hom)
  let r : U ⟶ T := MorphismProperty.Over.homMk (k ≫ O.ι) rfl (by trivial)
  have hmap : p ≫ V.hom = U.hom ≫ g := by
    change p ≫ V.hom = ((k ≫ O.ι) ≫ T.hom) ≫ g
    exact htriangle.trans
      ((Category.assoc k O.ι (T.hom ≫ g)).symm.trans
        (Category.assoc (k ≫ O.ι) T.hom g).symm)
  let a : U ⟶ (siteBaseChange g).obj V :=
    MorphismProperty.Over.homMk (pullback.lift p U.hom hmap)
      (pullback.lift_snd _ _ _) (by trivial)
  have hp : (unitRepresentativeArrow g a).left = p := by
    change pullback.lift p U.hom hmap ≫ pullback.fst V.hom g = p
    exact pullback.lift_fst _ _ _
  let : QuasiCompact (unitRepresentativeArrow g a).left := hp.symm ▸ hqc
  let : QuasiSeparated (unitRepresentativeArrow g a).left := hp.symm ▸ hqs
  let : GeometricallyConnected (unitRepresentativeArrow g a).left := hp.symm ▸ hgc
  let : UniversallyOpen (unitRepresentativeArrow g a).left := hp.symm ▸ hopen
  refine ⟨U, r, w, ?_, ?_⟩
  · change O.ι (k w) = t
    exact congrArg O.ι hw
  · let : IsIso (((baseChangeMap f (pullback.fst g f) g (pullback.snd g f)
        pullback.condition).app F).hom.app (op U)) :=
      ordinaryChart_component_isIso f g F a n hn hF
    exact (ConcreteCategory.isIso_iff_bijective _).mp inferInstance

end AlgebraicGeometry.Scheme.EtaleCohomology.SmoothBaseChange
