/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Descent.Modules.ZariskiStack
public import Aglib.AlgebraicGeometry.Descent.Modules.Fppf.CompTransCoherence
public import Aglib.CategoryTheory.Sites.Descent.OverSigma
public import Aglib.CategoryTheory.Sites.Descent.Composition
public import Mathlib.AlgebraicGeometry.Sites.SheafQuasiCompact
public import Mathlib.AlgebraicGeometry.Sites.Fpqc

/-!
# Quasi-coherent sheaves form an fpqc prestack

`Scheme.isPrestack_fpqcTopology_of_isPrestackFor_specMap`: a pseudofunctor
`F : LocallyDiscrete Scheme.{u}ᵒᵖ ⥤ᵖ Cat` which is a prestack for the Zariski topology and for the
singleton presieve of `Spec.map f` for every faithfully flat ring map `f` is a prestack for the
fpqc topology. For `S`, `M`, `N`, the presheaf `F.presheafHom M N` on `Over S` is turned into the
presheaf `Presieve.overSigma (F.presheafHom M N)` on schemes (pairs of a morphism `g : Y ⟶ S` and
a morphism `g^* M ⟶ g^* N`, [OverSigma](../../../../CategoryTheory/Sites/Descent/OverSigma.lean)).
Since the fpqc and Zariski topologies are subcanonical, the sheaf conditions of the two presheaves
correspond, and Mathlib's `isSheaf_type_propQCTopology_iff`
(`Mathlib/AlgebraicGeometry/Sites/SheafQuasiCompact.lean`, Stacks, Tag 022H) reduces the fpqc sheaf
condition to the Zariski topology and to single faithfully flat morphisms of affine schemes.

`Scheme.Modules.isPrestack_quasicoherentPseudofunctor_fpqcTopology` (instance): the instance for
`quasicoherentPseudofunctor`, from the Zariski stack instance and
`isStackFor_quasicoherentPseudofunctor_singleton_specMap`. This is the descent of morphisms of
quasi-coherent sheaves along fpqc coverings (Stacks Project, Tag 023T: for an fpqc covering, every
descent datum on quasi-coherent sheaves is effective and the functor from quasi-coherent sheaves
to descent data is fully faithful; the full faithfulness is this prestack statement for fpqc
coverings).
-/

@[expose] public section

universe u' v' u

open CategoryTheory Opposite Bicategory Pseudofunctor Presieve

namespace AlgebraicGeometry.Scheme

-- Mathlib's instances for `IsZariskiLocalAtSource P` and the like, stated for a variable `P`, apply
-- at `P := @Flat` only when types are compared without the transparency restriction, as in
-- Mathlib's own use of `isSheaf_type_propQCTopology_iff` (`Sites/Fpqc.lean`).
set_option backward.isDefEq.respectTransparency.types false in
/-- A pseudofunctor on schemes which is a Zariski prestack and a prestack for the singleton
presieve of `Spec.map f` for every faithfully flat ring map `f` is an fpqc prestack. -/
theorem isPrestack_fpqcTopology_of_isPrestackFor_specMap
    (F : LocallyDiscrete Scheme.{u}ᵒᵖ ⥤ᵖ Cat.{v', u'}) [F.IsPrestack Scheme.zariskiTopology]
    (hF : ∀ ⦃A B : CommRingCat.{u}⦄ (f : A ⟶ B), f.hom.FaithfullyFlat →
      F.IsPrestackFor (Presieve.singleton (Spec.map f))) :
    F.IsPrestack Scheme.fpqcTopology := by
  refine IsPrestack.of_isPrestackFor fun S R hR ↦ ?_
  rw [isPrestackFor_iff_isSheafFor]
  intro M N
  have hY : Presieve.IsSheaf Scheme.fpqcTopology (yoneda.obj S) :=
    GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable _
  have hG : Presieve.IsSheaf Scheme.fpqcTopology (overSigma (F.presheafHom M N)) := by
    refine (isSheaf_type_propQCTopology_iff (P := @Flat) _).2
      ⟨fun Y R' hR' ↦ ?_, fun {A B} f hf hs ↦ ?_⟩
    · refine isSheafFor_overSigma _
        (GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable
          (J := Scheme.zariskiTopology) (yoneda.obj S) R' hR') (fun g ↦ ?_)
      exact ((isSheaf_iff_isSheaf_of_type _ _).1
        (IsPrestack.isSheaf Scheme.zariskiTopology M N)) _
          (Scheme.zariskiTopology.overEquiv_symm_mem_over (Over.mk g) R' hR')
    · rw [Presieve.isSheafFor_iff_generate]
      have : Flat (Spec.map f) := hf
      have hff : f.hom.FaithfullyFlat := (flat_and_surjective_SpecMap_iff f).1 ⟨hf, hs⟩
      have hmem : Sieve.generate (Presieve.singleton (Spec.map f)) ∈
          Scheme.fpqcTopology (Spec A) :=
        Precoverage.generate_mem_toGrothendieck (Hom.singleton_mem_fpqcPrecoverage (Spec.map f))
      refine isSheafFor_overSigma _ (hY _ hmem) (fun g ↦ ?_)
      exact (F.isPrestackFor_iff_isSheafFor' _).1 ((F.IsPrestackFor_generate_iff _).2 (hF f hff))
        M N g
  exact isSheafFor_of_isSheafFor_overSigma _ (hG _ hR) (hY _ hR).isSeparatedFor

namespace Modules

/-- **Quasi-coherent sheaves form an fpqc prestack** (descent of morphisms along fpqc
coverings). -/
instance isPrestack_quasicoherentPseudofunctor_fpqcTopology :
    quasicoherentPseudofunctor.{u}.IsPrestack Scheme.fpqcTopology :=
  isPrestack_fpqcTopology_of_isPrestackFor_specMap _ fun _ _ f hf ↦
    (isStackFor_quasicoherentPseudofunctor_singleton_specMap f hf).isPrestackFor

/-- Quasi-coherent sheaves form an fppf prestack. -/
instance isPrestack_quasicoherentPseudofunctor_fppfTopology :
    quasicoherentPseudofunctor.{u}.IsPrestack Scheme.fppfTopology :=
  IsPrestack.of_le _ fppfTopology_le_fpqcTopology

end Modules

end AlgebraicGeometry.Scheme
