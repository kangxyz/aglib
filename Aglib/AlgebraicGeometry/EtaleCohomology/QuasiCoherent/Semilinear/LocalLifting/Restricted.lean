/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.QuasiCoherent.Semilinear.KernelRepresentation
public import Aglib.AlgebraicGeometry.Sites.EtaleAffineBasis.AffineAlgebras
public import Aglib.RingTheory.Etale.FrobeniusEquation.Tower
public import Aglib.AlgebraicGeometry.EtaleCohomology.H1.EtaleRestriction
public import Mathlib.CategoryTheory.Sites.LocallySurjective

/-!
# Local lifts for the original restricted semilinear map

Freeness is required only after the given etale scalar extension. The actual
inhomogeneous root cover and native affine structural comparisons give local
lifts for the literal restriction of the original additive sheaf map. No new
semilinear operator or coefficient sheaf is introduced.
-/

@[expose] public noncomputable section

universe u

open CategoryTheory Opposite
open AlgebraicGeometry.Scheme.Modules
open scoped TensorProduct

namespace AlgebraicGeometry.Scheme.EtaleCohomology.QuasiCoherent

private theorem section_solution_transport {C : Type*} [Category C]
    (L : Cᵒᵖ ⥤ AddCommGrpCat.{u + 1}) (δ : L ⟶ L)
    {U V U' V' : C} (iU : U' ≅ U) (iV : V' ≅ V)
    (q : V' ⟶ U') (n : V ⟶ U) (h : q ≫ iU.hom = iV.hom ≫ n)
    (s : L.obj (op U)) (t : L.obj (op V'))
    (ht : δ.app (op V') t = L.map q.op (L.map iU.hom.op s)) :
    δ.app (op V) (L.map iV.inv.op t) = L.map n.op s := by
  have hn := ConcreteCategory.congr_hom (δ.naturality iV.inv.op) t
  have hc : iV.inv ≫ q ≫ iU.hom = n := by
    rw [h]
    simp
  have hm : L.map iU.hom.op ≫ L.map q.op ≫ L.map iV.inv.op = L.map n.op := by
    rw [← L.map_comp, ← L.map_comp]
    simpa only [op_comp, Category.assoc] using congrArg (fun f => L.map f.op) hc
  exact hn.trans ((congrArg (L.map iV.inv.op) ht).trans (ConcreteCategory.congr_hom hm s))

private theorem imageSieve_mem_of_solution {C D : Type*} [Category C] [Category D]
    (H : D ⥤ C) (L : Cᵒᵖ ⥤ AddCommGrpCat.{u + 1}) (δ : L ⟶ L)
    {U V : D} {U' V' : C} (iU : U' ≅ H.obj U) (iV : V' ≅ H.obj V)
    (q : V' ⟶ U') (n : V ⟶ U) (h : q ≫ iU.hom = iV.hom ≫ H.map n)
    (s : (H.op ⋙ L).obj (op U))
    (ht : ∃ t : L.obj (op V'), δ.app (op V') t = L.map q.op (L.map iU.hom.op s)) :
    (Presheaf.imageSieve (Functor.whiskerLeft H.op δ) s) n := by
  obtain ⟨t, ht⟩ := ht
  exact ⟨L.map iV.inv.op t, section_solution_transport L δ iU iV q (H.map n) h s t ht⟩

private theorem algSpec_map_left_ringHom (A : CommRingCat.{u})
    {B C : CommAlgCat.{u} A} (f : B ⟶ C) :
    ((algSpec A).map f.op).left = Spec.map (CommRingCat.ofHom f.hom.toRingHom) := rfl

private theorem coefficient_solution
    (A : CommRingCat.{u}) (F : (Spec A).Modules) [F.IsQuasicoherent]
    (p : ℕ) (hp : p.Prime) (hA : (p : A) = 0)
    (Φ : moduleSpecΓFunctor.obj F →ₛₗ[RingHom.frobeniusOfPrimeCastEqZero p hp hA]
      moduleSpecΓFunctor.obj F)
    (B C : CommAlgCat.{u} A)
    [Etale (Spec.map (CommRingCat.ofHom (algebraMap A B)))]
    [Etale (Spec.map (CommRingCat.ofHom (algebraMap A C)))]
    (f : B ⟶ C) (c : Spec (CommRingCat.of C) ⟶ Spec (CommRingCat.of B))
    (hc : ((algSpec A).map f.op).left = c)
    (hw : c ≫ Spec.map (CommRingCat.ofHom (algebraMap A B)) =
      Spec.map (CommRingCat.ofHom (algebraMap A C)))
    (y : B ⊗[A] moduleSpecΓFunctor.obj F)
    (z : C ⊗[A] moduleSpecΓFunctor.obj F)
    (hz : LinearMap.frobeniusBaseChange p hp hA Φ C z - z =
      f.hom.toLinearMap.rTensor (moduleSpecΓFunctor.obj F) y) :
    let q : Scheme.Etale.mk (Spec.map (CommRingCat.ofHom (algebraMap A C))) ⟶
        Scheme.Etale.mk (Spec.map (CommRingCat.ofHom (algebraMap A B))) :=
      MorphismProperty.Over.homMk c hw
    ((affineFrobenius A F p hp hA Φ - 𝟙 (additiveCoefficient (Spec A) F)).hom.app
      (op (Scheme.Etale.mk (Spec.map (CommRingCat.ofHom (algebraMap A C))))))
        (tensorCoefficientAddEquiv A F C z) =
      (additiveCoefficient (Spec A) F).obj.map q.op (tensorCoefficientAddEquiv A F B y) := by
  subst c
  intro q
  have hd : ((affineFrobenius A F p hp hA Φ -
      𝟙 (additiveCoefficient (Spec A) F)).hom.app
        (op (Scheme.Etale.mk (Spec.map (CommRingCat.ofHom (algebraMap A C))))))
      (tensorCoefficientAddEquiv A F C z) =
        tensorCoefficientAddEquiv A F C (LinearMap.frobeniusBaseChange p hp hA Φ C z - z) := by
    apply ULift.ext
    exact affineFrobenius_sub_id_specTensor A F p hp hA Φ C z
  exact hd.trans ((congrArg (tensorCoefficientAddEquiv A F C) hz).trans
    (tensorCoefficientAddEquiv_naturality A F B C f y).symm)

variable (A : CommRingCat.{u}) (F : (Spec A).Modules) [F.IsQuasicoherent]
  (p : ℕ) (hp : p.Prime) (hA : (p : A) = 0)
  (Φ : moduleSpecΓFunctor.obj F →ₛₗ[RingHom.frobeniusOfPrimeCastEqZero p hp hA]
    moduleSpecΓFunctor.obj F)
  [Module.Finite A (moduleSpecΓFunctor.obj F)]
  (R : Type u) [CommRing R] [Algebra A R]
  [Etale (Spec.map (CommRingCat.ofHom (algebraMap A R)))]
  [Module.Free R (R ⊗[A] moduleSpecΓFunctor.obj F)]

/-- Every original restricted affine-test section lifts on its actual
inhomogeneous etale-surjective spectrum cover. -/
theorem restricted_affineFrobenius_imageSieve_affine
    (U : (Spec (CommRingCat.of R)).AffineEtale)
    (s : ((etaleRestriction (Spec.map (CommRingCat.ofHom (algebraMap A R)))).obj
      (additiveCoefficient (Spec A) F)).obj.obj
        (op ((Scheme.AffineEtale.Spec (Spec (CommRingCat.of R))).obj U))) :
    Presheaf.imageSieve
        ((etaleRestriction (Spec.map (CommRingCat.ofHom (algebraMap A R)))).map
          (affineFrobenius A F p hp hA Φ - 𝟙 (additiveCoefficient (Spec A) F))).hom s ∈
      (Spec (CommRingCat.of R)).smallEtaleTopology
        ((Scheme.AffineEtale.Spec (Spec (CommRingCat.of R))).obj U) := by
  let j := Spec.map (CommRingCat.ofHom (algebraMap A R))
  let L := additiveCoefficient (Spec A) F
  let δ := affineFrobenius A F p hp hA Φ - 𝟙 L
  let : Etale U.hom := U.prop
  let UA : (Spec A).AffineEtale := Scheme.AffineEtale.mk (U.hom ≫ j)
  let S := U.left.unop
  obtain ⟨r, hr⟩ : ∃ r : CommRingCat.of R ⟶ S, Spec.map r = U.hom :=
    ⟨Spec.preimage U.hom, Spec.map_preimage U.hom⟩
  obtain ⟨g, hg⟩ : ∃ g : A ⟶ S, Spec.map g = U.hom ≫ j :=
    ⟨Spec.preimage (U.hom ≫ j), Spec.map_preimage (U.hom ≫ j)⟩
  let : Algebra R S := r.hom.toAlgebra
  let : Algebra A S := g.hom.toAlgebra
  have hgcomp : g = CommRingCat.ofHom (algebraMap A R) ≫ r := by
    apply Spec.map_injective
    rw [Spec.map_comp, hr, hg]
  let : IsScalarTower A R S := IsScalarTower.of_algebraMap_eq fun a =>
    congrArg (fun k => k.hom a) hgcomp
  let SA := CommAlgCat.of A S
  have hSA : Etale (Spec.map (CommRingCat.ofHom (algebraMap A SA))) := by
    change Etale (Spec.map g)
    rw [hg]
    infer_instance
  let := hSA
  obtain ⟨iU, hiU⟩ : ∃ iU : Scheme.Etale.mk (Spec.map (CommRingCat.ofHom (algebraMap A SA))) ≅
      (siteEtalePostcompose j).obj
        ((Scheme.AffineEtale.Spec (Spec (CommRingCat.of R))).obj U),
      iU.hom.left = 𝟙 (Spec (CommRingCat.of SA)) :=
    ⟨MorphismProperty.Over.isoMk (Iso.refl _) (by
      change 𝟙 _ ≫ (U.hom ≫ j) = Spec.map g
      rw [Category.id_comp, hg]), rfl⟩
  obtain ⟨y, hy⟩ := (tensorCoefficientAddEquiv A F SA).surjective (L.obj.map iU.hom.op s)
  have hroots := Algebra.FrobeniusEquation.exists_etale_surjective_solution_of_free_baseChange
    p hp hA Φ R S
  obtain ⟨C, hC, hSC, hRC, hAC, hRSC, hARC, hASC, het, hsurj, z, hz⟩ := hroots y
  let CA := CommAlgCat.of A C
  obtain ⟨fA, hfA⟩ : ∃ fA : SA ⟶ CA,
      fA.hom = IsScalarTower.toAlgHom A S C :=
    ⟨(ConcreteCategory.homEquiv (C := CommAlgCat.{u} A) (X := SA) (Y := CA)).symm
      (IsScalarTower.toAlgHom A S C), rfl⟩
  let c := Spec.map (CommRingCat.ofHom (algebraMap S C))
  have hleft : ((algSpec A).map fA.op).left = c := by
    rw [algSpec_map_left_ringHom, hfA]
    rfl
  have hstr := ((algSpec A).map fA.op).w
  rw [hleft, algSpec_obj_hom, algSpec_obj_hom] at hstr
  have hc : Etale c := by
    rw [HasRingHomProperty.Spec_iff (P := @Etale)]
    change (algebraMap S C).Etale
    rw [RingHom.etale_algebraMap]
    exact het
  let := hc
  have hcomp : c ≫ (U.hom ≫ j) =
      Spec.map (CommRingCat.ofHom (algebraMap A C)) := by
    change c ≫ UA.hom = _
    change c ≫ (U.hom ≫ j) = _
    rw [← hg]
    exact hstr
  let : Etale (Spec.map (CommRingCat.ofHom (algebraMap A C))) := by
    rw [← hcomp]
    infer_instance
  let V := Scheme.Etale.mk (c ≫ U.hom)
  let qR : V ⟶ (Scheme.AffineEtale.Spec (Spec (CommRingCat.of R))).obj U :=
    MorphismProperty.Over.homMk c rfl
  let qA : Scheme.Etale.mk (Spec.map (CommRingCat.ofHom (algebraMap A CA))) ⟶
      Scheme.Etale.mk (Spec.map (CommRingCat.ofHom (algebraMap A SA))) :=
    MorphismProperty.Over.homMk c hstr
  obtain ⟨iV, hiV⟩ : ∃ iV : Scheme.Etale.mk (Spec.map (CommRingCat.ofHom (algebraMap A CA))) ≅
      (siteEtalePostcompose j).obj V, iV.hom.left = 𝟙 (Spec (CommRingCat.of CA)) :=
    ⟨MorphismProperty.Over.isoMk (Iso.refl _) (by
      change 𝟙 _ ≫ ((c ≫ U.hom) ≫ j) =
        Spec.map (CommRingCat.ofHom (algebraMap A C))
      simpa only [Category.id_comp, Category.assoc] using hcomp), rfl⟩
  have hi : qA ≫ iU.hom = iV.hom ≫ (siteEtalePostcompose j).map qR := by
    apply MorphismProperty.Over.Hom.ext
    change c ≫ iU.hom.left = iV.hom.left ≫ c
    rw [hiU, hiV]
    exact (Category.comp_id c).trans (Category.id_comp c).symm
  have hz' : LinearMap.frobeniusBaseChange p hp hA Φ CA z - z =
      fA.hom.toLinearMap.rTensor (moduleSpecΓFunctor.obj F) y := by
    rw [LinearMap.rTensor_def, hfA]
    exact hz
  have hroot := coefficient_solution A F p hp hA Φ SA CA fA c hleft hstr y z hz'
  change @Eq (L.obj.obj (op (Scheme.Etale.mk
      (Spec.map (CommRingCat.ofHom (algebraMap A CA))))))
    (δ.hom.app _ (tensorCoefficientAddEquiv A F CA z))
    (L.obj.map qA.op (tensorCoefficientAddEquiv A F SA y)) at hroot
  rw [hy] at hroot
  obtain ⟨t, ht⟩ : ∃ t : L.obj.obj (op (Scheme.Etale.mk
      (Spec.map (CommRingCat.ofHom (algebraMap A CA))))),
      δ.hom.app _ t = L.obj.map qA.op (L.obj.map iU.hom.op s) :=
    ⟨tensorCoefficientAddEquiv A F CA z, hroot⟩
  have hcover : Sieve.ofArrows (fun _ : PUnit.{1} => V) (fun _ => qR) ∈
      (Spec (CommRingCat.of R)).smallEtaleTopology _ := by
    rw [Scheme.ofArrows_mem_smallEtaleTopology_iff]
    change (⋃ _ : PUnit.{1}, Set.range c) = Set.univ
    simp only [Set.iUnion_const]
    exact Set.range_eq_univ.mpr hsurj
  apply (Spec (CommRingCat.of R)).smallEtaleTopology.superset_covering ?_ hcover
  rw [Sieve.ofArrows, Sieve.generate_le_iff, Presieve.ofArrows_le_iff]
  intro _
  exact imageSieve_mem_of_solution (siteEtalePostcompose j) L.obj δ.hom iU iV qA qR
    hi s ⟨t, ht⟩

/-- The literal restricted original difference is locally surjective on every
test, by the cover-dense affine site and its actual root covers. -/
theorem restricted_affineFrobenius_isLocallySurjective :
    Presheaf.IsLocallySurjective (Spec (CommRingCat.of R)).smallEtaleTopology
      ((etaleRestriction (Spec.map (CommRingCat.ofHom (algebraMap A R)))).map
        (affineFrobenius A F p hp hA Φ - 𝟙 (additiveCoefficient (Spec A) F))).hom := by
  constructor
  intro U s
  let H := Scheme.AffineEtale.Spec (Spec (CommRingCat.of R))
  apply (Spec (CommRingCat.of R)).smallEtaleTopology.transitive
    (H.is_cover_of_isCoverDense (Spec (CommRingCat.of R)).smallEtaleTopology U)
  intro V g ⟨⟨Z, lift, m, fac⟩⟩
  rw [← fac, Sieve.pullback_comp]
  apply (Spec (CommRingCat.of R)).smallEtaleTopology.pullback_stable
  rw [Presheaf.pullback_imageSieve]
  exact restricted_affineFrobenius_imageSieve_affine A F p hp hA Φ R Z _

/-- Freeness of the actual localized tensor module makes the same original
restricted additive difference an epimorphism. -/
theorem restricted_affineFrobenius_epi :
    Epi ((etaleRestriction (Spec.map (CommRingCat.ofHom (algebraMap A R)))).map
      (affineFrobenius A F p hp hA Φ - 𝟙 (additiveCoefficient (Spec A) F))) := by
  let := restricted_affineFrobenius_isLocallySurjective A F p hp hA Φ R
  infer_instance

end AlgebraicGeometry.Scheme.EtaleCohomology.QuasiCoherent
