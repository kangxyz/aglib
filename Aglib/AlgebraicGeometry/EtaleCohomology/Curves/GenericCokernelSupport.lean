/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Curves.GenericCokernelLocalLifting
public import Aglib.AlgebraicGeometry.EtaleCohomology.Curves.GenericEtalePointLifting
public import Aglib.AlgebraicGeometry.Sites.EtaleLocalPreimage
public import Aglib.AlgebraicGeometry.Sites.EtaleSectionZeroLocus
public import Aglib.Topology.NoetherianCurveSupport
public import Mathlib.CategoryTheory.Sites.EpiMono

/-!
# Actual finite support of arbitrary generic-unit cokernel sections

Sections of the original sheaf cokernel are lifted through its original
epimorphism on actual etale charts. Affine refinements handle non-quasi-compact
charts. The resulting etale-local zero locus contains every generic point;
its complement is finite on a Noetherian curve test.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry TopologicalSpace Set
open GroupCohomology.Kummer.Coefficients

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Curves

universe u

variable {X : Scheme.{u}} [IsNoetherian X]

private theorem represented_mem_zeroLocus (U : X.Etale) [QuasiCompact U.hom]
    (a : ((directImage (genericArtinMap X)).obj (gm (genericArtinLocus X))).obj.obj (op U))
    (η : genericPoints U.left) :
    η.val ∈ Etale.sectionZeroLocus (cokernel (genericArtinUnit X)).obj
      ((cokernel.π (genericArtinUnit X)).hom.app (op U) a) := by
  let e := genericArtinBaseChangeIndexEquiv (X := X) (U := U.left) U.hom
  obtain ⟨W, _, hpW, b, hb⟩ := exists_genericUnit_local_lift U a (e.symm η)
  have he : (pullback.fst U.hom (genericArtinMap X)) (e.symm η) = η.val :=
    (genericArtinBaseChangeIndexEquiv_val (X := X) (U := U.left) U.hom (e.symm η)).symm.trans
      (congrArg Subtype.val (e.apply_symm_apply η))
  refine ⟨Etale.openChart U W, Etale.openChartHom U W, ⟨η.val, he ▸ hpW⟩, rfl, ?_⟩
  have hn := ConcreteCategory.congr_hom
    ((cokernel.π (genericArtinUnit X)).hom.naturality (Etale.openChartHom U W).op) a
  have hz := congrArg (fun k : gm X ⟶ cokernel (genericArtinUnit X) =>
    k.hom.app (op (Etale.openChart U W))) (cokernel.condition (genericArtinUnit X))
  have hzv := ConcreteCategory.congr_hom hz b
  change (cokernel.π (genericArtinUnit X)).hom.app _
    ((genericArtinUnit X).hom.app _ b) = 0 at hzv
  exact hn.symm.trans ((congrArg (fun c =>
    (cokernel.π (genericArtinUnit X)).hom.app _ c) hb.symm).trans hzv)

/-- Every generic point belongs to the actual etale-local zero locus of any cokernel section. -/
theorem genericCokernel_generic_mem_zeroLocus (U : X.Etale)
    (a : (cokernel (genericArtinUnit X)).obj.obj (op U)) (η : genericPoints U.left) :
    η.val ∈ Etale.sectionZeroLocus (cokernel (genericArtinUnit X)).obj a := by
  let π := cokernel.π (genericArtinUnit X)
  let : Sheaf.IsLocallySurjective π :=
    (Sheaf.isLocallySurjective_iff_epi' Ab.{u + 1} π).mpr inferInstance
  obtain ⟨V, f, y, b, hy, hb⟩ := Etale.exists_localPreimage_at_point π.hom a η.val
  let : IsLocallyNoetherian U.left :=
    LocallyOfFiniteType.isLocallyNoetherian (X := U.left) (Y := X) U.hom
  have hyg : y ∈ genericPoints V.left :=
    mem_genericPoints_of_etale_image f.left y (hy.symm ▸ η.property)
  let : IsLocallyNoetherian V.left :=
    LocallyOfFiniteType.isLocallyNoetherian (X := V.left) (Y := X) V.hom
  obtain ⟨W, hW, hyW, _⟩ :=
    exists_isAffineOpen_mem_and_subset (X := V.left) (U := ⊤) (x := y) (by trivial)
  let : IsAffine W.toScheme := hW
  let : CompactSpace W.toScheme := isCompact_iff_compactSpace.mp hW.isCompact
  let : IsNoetherian W.toScheme := {
    toIsLocallyNoetherian := inferInstance
    toCompactSpace := inferInstance }
  let T := Etale.openChart V W
  let : QuasiCompact T.hom :=
    quasiCompact_of_noetherianSpace_source (X := W.toScheme) (Y := X) (W.ι ≫ V.hom)
  let g : T ⟶ V := Etale.openChartHom V W
  let z : T.left := ⟨y, hyW⟩
  have hzg : z ∈ genericPoints T.left := mem_genericPoints_of_etale_image W.ι z hyg
  have hz := represented_mem_zeroLocus T
    (((directImage (genericArtinMap X)).obj (gm (genericArtinLocus X))).obj.map g.op b) ⟨z, hzg⟩
  have he := ConcreteCategory.congr_hom (π.hom.naturality g.op) b
  change π.hom.app (op T)
      (((directImage (genericArtinMap X)).obj (gm (genericArtinLocus X))).obj.map g.op b) =
    (cokernel (genericArtinUnit X)).obj.map g.op (π.hom.app (op V) b) at he
  rw [he, hb] at hz
  have hV := Etale.mem_sectionZeroLocus_of_restriction
    (cokernel (genericArtinUnit X)).obj g
    ((cokernel (genericArtinUnit X)).obj.map f.op a) hz
  exact hy ▸ Etale.mem_sectionZeroLocus_of_restriction
    (cokernel (genericArtinUnit X)).obj f a hV

/-- The genuine etale-local support of any original cokernel section is finite on a curve test. -/
theorem genericCokernel_finite_support (U : X.Etale) [QuasiCompact U.hom]
    (hdim : topologicalKrullDim U.left ≤ 1)
    (a : (cokernel (genericArtinUnit X)).obj.obj (op U)) :
    ((Etale.sectionZeroLocus (cokernel (genericArtinUnit X)).obj a)ᶜ).Finite := by
  let : IsNoetherian U.left := {
    toIsLocallyNoetherian := LocallyOfFiniteType.isLocallyNoetherian (X := U.left) (Y := X) U.hom
    toCompactSpace := QuasiCompact.compactSpace_of_compactSpace (X := U.left) (Y := X) U.hom }
  exact finite_compl_open_of_contains_genericPoints hdim
    (Etale.isOpen_sectionZeroLocus _ a)
    (fun x hx => genericCokernel_generic_mem_zeroLocus U a ⟨x, hx⟩)

end AlgebraicGeometry.Scheme.EtaleCohomology.Curves
