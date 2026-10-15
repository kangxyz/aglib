/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Pullback.Free
public import Aglib.AlgebraicGeometry.Modules.Pullback.FlatMorphism
public import Aglib.AlgebraicGeometry.Modules.BaseChange.OpenImmersion.Cartesian
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import Mathlib.Topology.Sheaves.Flasque

/-! # Ordinary module-sheaf complexes and geometric restriction

Source:
`Quillen/AlgebraicGeometry/PerfectComplexes/Restriction.lean`
at LOCAL Quillen
`189a8e779f0c68b2dfc6f8195daebb3e684a5905`.
Source SHA-256:
`00896057a7423474dc1d4f8b6743337ce31c9f93490cbf5d11989649ccf1d3f3`.
Selected declarations: restrict, restrict_additive, restrict_preservesFiniteLimits,
  restrict_preservesFiniteColimits, restrictFunctor_preservesHomology, restrict_quasiIso.
Source:
`Quillen/AlgebraicGeometry/PerfectComplexes/Pullback.lean`
at LOCAL Quillen
`189a8e779f0c68b2dfc6f8195daebb3e684a5905`.
Source SHA-256:
`2e5ce5b94f6bdf7b63190c25514b058ee2d10ff210bee636504ca723df0028e2`.
Selected declarations: pullbackComplex, pullbackComplex_additive, pullbackComplexRestrictIso.
Source:
`Quillen/AlgebraicGeometry/PerfectComplexes/FlatPullback.lean`
at LOCAL Quillen
`189a8e779f0c68b2dfc6f8195daebb3e684a5905`.
Source SHA-256:
`e68368b05013e5642baabac948a30e7d7493acd660ace47346b774827295bc33`.
Selected declarations: pullbackComplex_preservesFiniteLimits, pullbackFunctor_preservesHomology,
  pullbackComplex_quasiIso.
Source:
`Quillen/AlgebraicGeometry/PerfectComplexes/ProjectiveLine/P5NativeCoefficientsSupport.lean`
at LOCAL Quillen
`189a8e779f0c68b2dfc6f8195daebb3e684a5905`.
Source SHA-256:
`f960093218542cb3dc2e13439cc03be9268b0cb50607f10d119b08f3d24a31dd`.
Selected declarations: restrictModule_isFlasque, restrict_isStrictlyGE,
  ordinaryOpenRestrictionIso, ordinaryOpenRestrictionIso_hom_f.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry HomologicalComplex
namespace AlgebraicGeometry.Scheme.Modules

instance restrictModule_isFlasque {U P : Scheme.{u}} (j : U ⟶ P) [IsOpenImmersion j]
    (M : P.Modules) [TopCat.Presheaf.IsFlasque M.presheaf] :
    TopCat.Presheaf.IsFlasque (M.restrict j).presheaf where
  epi {V W} k := by
    change Epi (M.presheaf.map (j.opensFunctor.map k.unop).op)
    infer_instance

namespace Complex
variable {U X : Scheme.{u}}

/-- Degreewise restriction of integer-indexed cochain complexes along the open immersion `j`. -/
def restrict (j : U ⟶ X) [IsOpenImmersion j] : CochainComplex X.Modules ℤ ⥤ CochainComplex
  U.Modules ℤ :=
  (Scheme.Modules.restrictFunctor j).mapHomologicalComplex (ComplexShape.up ℤ)

instance restrict_additive (j : U ⟶ X) [IsOpenImmersion j] : (restrict j).Additive := by
  unfold restrict
  infer_instance

instance restrict_preservesFiniteLimits (j : U ⟶ X) [IsOpenImmersion j] : PreservesFiniteLimits
  (restrict j) := by
  unfold restrict
  infer_instance

instance restrict_preservesFiniteColimits (j : U ⟶ X) [IsOpenImmersion j] :
  PreservesFiniteColimits (restrict j) := by
  unfold restrict
  infer_instance

instance restrictFunctor_preservesHomology (j : U ⟶ X) [IsOpenImmersion j] :
  (Scheme.Modules.restrictFunctor j).PreservesHomology :=
  Functor.preservesHomology_of_preservesMonos_and_cokernels _

instance restrict_quasiIso (j : U ⟶ X) [IsOpenImmersion j] {K L : CochainComplex X.Modules ℤ} (f :
  K ⟶ L) [QuasiIso f] :
    QuasiIso ((restrict j).map f) := by
  unfold restrict
  infer_instance

/-- Degreewise pullback of integer-indexed cochain complexes along `f`. -/
def pullback {X Y : Scheme.{u}} (f : X ⟶ Y) : CochainComplex Y.Modules ℤ ⥤ CochainComplex
  X.Modules ℤ :=
  (Scheme.Modules.pullback f).mapHomologicalComplex (ComplexShape.up ℤ)

instance pullback_additive {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (pullback f).Additive := by unfold pullback; infer_instance

/-- The comparison between pullback followed by restriction to `f ⁻¹ᵁ U` and restriction to `U`
followed by pullback along `f ∣_ U`. -/
def pullbackRestrictIso {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens) :
    pullback f ⋙ restrict (f ⁻¹ᵁ U).ι ≅
      restrict U.ι ⋙ pullback (f ∣_ U) :=
  NatIso.mapHomologicalComplex (Scheme.Modules.pullbackRestrictIso f U) (ComplexShape.up ℤ)

instance pullback_preservesFiniteLimits {X Y : Scheme.{u}} (f : X ⟶ Y) [Flat f] :
    PreservesFiniteLimits (pullback f) := by unfold pullback; infer_instance

instance pullbackFunctor_preservesHomology {X Y : Scheme.{u}} (f : X ⟶ Y) [Flat f] :
    (Scheme.Modules.pullback f).PreservesHomology :=
  Functor.preservesHomology_of_preservesMonos_and_cokernels _

instance pullback_quasiIso {X Y : Scheme.{u}} (f : X ⟶ Y) [Flat f]
    {K L : CochainComplex Y.Modules ℤ} (s : K ⟶ L) [QuasiIso s] : QuasiIso ((pullback f).map s) :=
      by
  unfold pullback
  infer_instance

lemma restrict_isStrictlyGE {U P : Scheme.{u}} (j : U ⟶ P) [IsOpenImmersion j]
    (K : CochainComplex P.Modules ℤ) (a : ℤ) [K.IsStrictlyGE a] :
    ((restrict j).obj K).IsStrictlyGE a := by
  dsimp [restrict]
  infer_instance

/-- Direct image followed by open restriction, identified with restriction to the inverse-image
open followed by direct image along the restricted morphism, on cochain complexes. -/
def ordinaryOpenRestrictionIso {P Y : Scheme.{u}} (f : P ⟶ Y) (Z : Y.Opens) :
    (Scheme.Modules.pushforward f).mapHomologicalComplex (.up ℤ) ⋙ restrict Z.ι ≅
      restrict (f ⁻¹ᵁ Z).ι ⋙
        (Scheme.Modules.pushforward (f ∣_ Z)).mapHomologicalComplex (.up ℤ) :=
  Functor.mapHomologicalComplexCompIso
    (cartesianOpenBaseChange (f ⁻¹ᵁ Z).ι (f ∣_ Z) f Z.ι
      (isPullback_morphismRestrict f Z).flip) _

lemma ordinaryOpenRestrictionIso_hom_f {P Y : Scheme.{u}} (f : P ⟶ Y) (Z : Y.Opens)
    (K : CochainComplex P.Modules ℤ) (n : ℤ) :
    ((ordinaryOpenRestrictionIso f Z).hom.app K).f n =
      (cartesianOpenBaseChange (f ⁻¹ᵁ Z).ι (f ∣_ Z) f Z.ι
        (isPullback_morphismRestrict f Z).flip).hom.app (K.X n) := rfl

end Complex
end AlgebraicGeometry.Scheme.Modules
