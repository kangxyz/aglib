/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Surfaces.RationalSingularities.Blowup
public import Aglib.AlgebraicGeometry.Blowup.ProjectivePresentation.AffineRow
public import Aglib.AlgebraicGeometry.Modules.LocallyFree.Coherent
public import Aglib.AlgebraicGeometry.Modules.Invertible.GeneratingKernel
public import Aglib.AlgebraicGeometry.Modules.Generators.GlobalSections
public import Aglib.AlgebraicGeometry.Modules.Tensor.Monoidal.Sections
public import Aglib.AlgebraicGeometry.Surfaces.Contraction.FormalNeighborhood.Powers
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-!
# Original ideal-power sections on the normalized rational surface blowup

Finite generators of the original maximal ideal produce their actual normalized
exceptional sections. Their literal tensor products generate all original ideal
powers. Rational structure-H1 and the derived local cohomological-dimension
bound give H1 vanishing for these powers.

The original ordered cross relations generate the positive twists of the actual
row kernel. Their H1 vanishing gives surjectivity of the original power rows on
global sections. Through the original proper-birational coefficient map, the
actual nth ideal-power section image is exactly the original maximal ideal to
power n. Native Cartier multiplication retains every original ideal inclusion.

This is the normalized section-algebra step of Stacks 0B4Y. Descent of normality
to the ordinary blowup and the exceptional-fibre quotient comparison are further
consumers; neither is assumed here.
-/

@[expose] public noncomputable section
set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Hom
open AlgebraicGeometry.Scheme.Modules.QuasiCoherent
open AlgebraicGeometry.Scheme.Modules.Invertible
open AlgebraicGeometry.ProjectiveSpace.FromSections
open AlgebraicGeometry.Scheme.Blowup
open AlgebraicGeometry.Scheme.Blowup.ProjectivePresentation

universe u

namespace AlgebraicGeometry.Scheme.RationalSingularities

/-- The existing unit object, with the scheme module category fixed before specializing maps. -/
abbrev originalUnit (X : Scheme.{u}) : X.Modules :=
  SheafOfModules.unit X.ringCatSheaf

section CategoryBoundaries

variable {C D : Type*} [Category* C] [Category* D]

private theorem original_iso_hom_epi {M N : C} (e : M ≅ N) : Epi e.hom := inferInstance

private theorem original_iso_inv_isIso {M N : C} (e : M ≅ N) : IsIso e.inv := inferInstance

private theorem original_iso_hom_isIso {M N : C} (e : M ≅ N) : IsIso e.hom := inferInstance

private theorem original_comp_epi {M N P : C} (f : M ⟶ N) (g : N ⟶ P)
    (hf : Epi f) (hg : Epi g) : Epi (f ≫ g) := by
  let := hf
  let := hg
  exact epi_comp f g

private theorem original_map_epi (T : C ⥤ D) {M N : C} (f : M ⟶ N)
    [PreservesColimit (span f f) T] (hf : Epi f) : Epi (T.map f) := by
  let := hf
  exact preserves_epi_of_preservesColimit T f

private theorem original_map_epi_of_preserves (T : C ⥤ D) [T.PreservesEpimorphisms]
    {M N : C} (f : M ⟶ N) (hf : Epi f) : Epi (T.map f) := by
  let := hf
  infer_instance

private theorem original_comp_isIso {M N P : C} (f : M ⟶ N) (g : N ⟶ P)
    (hf : IsIso f) (hg : IsIso g) : IsIso (f ≫ g) := by
  let := hf
  let := hg
  infer_instance

private theorem original_inv_factor {O M N : C} (f : M ⟶ N) (hf : IsIso f) (s : O ⟶ N) :
    (s ≫ inv f) ≫ f = s := by
  let := hf
  simp only [Category.assoc, IsIso.inv_hom_id, Category.comp_id]

private theorem original_row_comp_eq {ι : Type*} {O M N : C}
    [HasCoproductsOfShape ι C] (s : ι → (O ⟶ M)) (f : M ⟶ N) :
    Sigma.desc (fun i => s i ≫ f) = Sigma.desc s ≫ f := by
  apply Sigma.hom_ext
  intro i
  rw [Sigma.ι_comp_desc, Sigma.ι_comp_desc_assoc]

private theorem original_row_comp_epi {ι : Type*} {O M N : C}
    [HasCoproductsOfShape ι C] (s : ι → (O ⟶ M)) (f : M ⟶ N)
    (hs : Epi (Sigma.desc s)) (hf : Epi f) :
    Epi (Sigma.desc fun i => s i ≫ f) :=
  (original_row_comp_eq s f).symm ▸ original_comp_epi (Sigma.desc s) f hs hf

private theorem original_row_equation {ι : Type*} [HasCoproductsOfShape ι C]
    {O M N V : C} (e : M ≅ N) (eF : V ≅ ∐ fun _ : ι => O)
    (f : V ⟶ N) (s : ι → (O ⟶ M))
    (h : ∀ i, s i ≫ e.hom = (Sigma.ι (fun _ : ι => O) i ≫ eF.inv) ≫ f) :
    Sigma.desc s ≫ e.hom = eF.inv ≫ f := by
  apply Sigma.hom_ext
  intro i
  rw [Sigma.ι_comp_desc_assoc]
  exact (h i).trans (Category.assoc _ _ _)

private theorem original_tensor_rows_epi {ι κ : Type*}
    [HasCoproductsOfShape ι C] [HasCoproductsOfShape κ C]
    [HasCoproductsOfShape (ι × κ) C] (T : C ⥤ C) {O M N : C}
    (e : T.obj O ≅ N) (s : ι → (O ⟶ M)) (t : κ → (O ⟶ N))
    (ht : Epi (Sigma.desc t)) (hs : Epi (T.map (Sigma.desc s)))
    (hσ : Epi (sigmaComparison T (fun _ : ι => O))) :
    Epi (Sigma.desc fun ij : ι × κ => t ij.2 ≫ e.inv ≫ T.map (s ij.1)) := by
  let := ht
  let := hs
  let := hσ
  constructor
  intro Z f g h
  have hi (i : ι) : T.map (s i) ≫ f = T.map (s i) ≫ g := by
    apply (cancel_epi e.inv).mp
    apply (cancel_epi (Sigma.desc t)).mp
    apply Sigma.hom_ext
    intro j
    have hij := congrArg (fun k => Sigma.ι (fun _ : ι × κ => O) (i, j) ≫ k) h
    simpa only [Sigma.ι_comp_desc_assoc, Category.assoc] using hij
  apply (cancel_epi (T.map (Sigma.desc s))).mp
  apply (cancel_epi (sigmaComparison T (fun _ : ι => O))).mp
  apply Sigma.hom_ext
  intro i
  simpa only [Category.assoc, ι_comp_sigmaComparison_assoc, ← T.map_comp_assoc,
    Sigma.ι_comp_desc] using hi i

private theorem original_iso_cancel {O M N P : C} (s : O ⟶ N) (e : M ≅ N) (i : N ⟶ P) :
    (s ≫ e.inv) ≫ e.hom ≫ i = s ≫ i := by
  simp only [Category.assoc, Iso.inv_hom_id_assoc]

private theorem original_iso_hom_cancel {M N P : C} (e : M ≅ N) (f : M ⟶ P) :
    e.hom ≫ e.inv ≫ f = f := Iso.hom_inv_id_assoc e f

private theorem original_move_iso {O M N : C} (e : M ≅ N) (f : O ⟶ M) (g : O ⟶ N)
    (h : f ≫ e.hom = g) : g ≫ e.inv = f := by
  rw [← h, Category.assoc, Iso.hom_inv_id, Category.comp_id]

private theorem original_conjugate_eq {M N : C} (e : M ≅ N) (f : M ⟶ M) (g : N ⟶ N)
    (h : f ≫ e.hom = e.hom ≫ g) : e.inv ≫ f ≫ e.hom = g := by
  rw [h, Iso.inv_hom_id_assoc]

private theorem original_pullback_paste (F : C ⥤ D) {O M : C} {U N : D}
    (u : F.obj O ≅ U) (s : O ⟶ M) (i : M ⟶ O)
    (e : F.obj M ⟶ N) (j : N ⟶ U) (h : e ≫ j = F.map i ≫ u.hom) :
    ((u.inv ≫ F.map s) ≫ e) ≫ j = u.inv ≫ F.map (s ≫ i) ≫ u.hom := by
  simp only [Category.assoc]
  rw [h, ← F.map_comp_assoc]

private theorem original_tensor_row_comparison {ι : Type*} [HasCoproductsOfShape ι C]
    (T : C ⥤ C) {O M P : C} [PreservesColimit (Discrete.functor (fun _ : ι => O)) T]
    (e : T.obj O ≅ P) (s : ι → (O ⟶ M)) :
    Sigma.desc (fun i => e.inv ≫ T.map (s i)) =
      (PreservesCoproduct.iso T (fun _ : ι => O) ≪≫ Sigma.mapIso (fun _ : ι => e)).inv ≫
        T.map (Sigma.desc s) := by
  apply Sigma.hom_ext
  intro i
  simp only [Iso.trans_inv, PreservesCoproduct.inv_hom, Category.assoc]
  rw [Sigma.ι_comp_desc, Sigma.ι_mapIso_inv_assoc, ι_comp_sigmaComparison_assoc,
    ← T.map_comp, Sigma.ι_comp_desc]

private theorem original_kernel_shortExact [Abelian C] {M N : C} (f : M ⟶ N) (hf : Epi f) :
    (ShortComplex.kernelSequence f).ShortExact := by
  let := hf
  exact { exact := ShortComplex.kernelSequence_exact f, epi_g := hf }

private theorem original_row_sum_decomposition [Preadditive C] {ι : Type*} [Fintype ι]
    [HasCoproductsOfShape ι C] {O M N : C} (r : ι → (M ⟶ N))
    (t : O ⟶ ∐ fun _ : ι => M) :
    ∃ c : ι → (O ⟶ M), t ≫ Sigma.desc r = ∑ i, c i ≫ r i := by
  obtain ⟨c, hc⟩ := exists_eq_sum_sigma_ι t
  refine ⟨c, ?_⟩
  rw [hc, Preadditive.sum_comp]
  apply Finset.sum_congr rfl
  intro i _
  rw [Category.assoc, Sigma.ι_comp_desc]

end CategoryBoundaries

/-- Original epimorphic rows of sections stay epimorphic under the actual pullback. -/
private theorem pullback_sections_epi {X Y : Scheme.{u}} (f : X ⟶ Y)
    {M : Y.Modules} {ι : Type u}
    (s : ι → ((originalUnit Y) ⟶ M)) [Epi (Sigma.desc s)] :
    Epi (Sigma.desc fun i => pullbackSection f (s i)) := by
  exact @pulledFamily_epi (I := ι) (X := Y) (T := X) (g := f) (M := M) (s := s)
    (inferInstance : Epi (Sigma.desc s))

/-- Postcomposition retains the same original indexed row. -/
private theorem section_row_comp_epi {X : Scheme.{u}} {M N : X.Modules} {ι : Type u}
    (s : ι → ((originalUnit X) ⟶ M)) [Epi (Sigma.desc s)]
    (f : M ⟶ N) [Epi f] : Epi (Sigma.desc fun i => s i ≫ f) := by
  exact original_row_comp_epi (C := X.Modules) s f inferInstance inferInstance

/-- The affine row equation is proved before the concrete generation witnesses are inserted. -/
private theorem affine_idealSection_row_equation
    (A : Type u) [CommRing A] (I : Ideal A) {ι : Type u} (g : ι → I) :
    Sigma.desc (fun i => AffineCoordinates.idealSection A I (g i)) ≫
        (AffineRow.originalIdealIso I).hom =
      (tildeFinsupp (R := CommRingCat.of A) ι).inv ≫
        tilde.map (ModuleCat.ofHom (Finsupp.linearCombination A g)) := by
  let X := Spec (.of A)
  let T := tilde.functor (.of A)
  let lc : ModuleCat.of A (ι →₀ A) ⟶ ModuleCat.of A I :=
    ModuleCat.ofHom (Finsupp.linearCombination A g)
  let e : idealModule (affineCenter A I).subschemeι ≅ T.obj (ModuleCat.of A I) :=
    AffineRow.originalIdealIso I
  let eF : T.obj (ModuleCat.of A (ι →₀ A)) ≅ (∐ fun _ : ι => originalUnit X) :=
    tildeFinsupp (R := CommRingCat.of A) ι
  apply original_row_equation (C := X.Modules) e eF (T.map lc)
    (fun i => AffineCoordinates.idealSection A I (g i))
  intro i
  let l : ModuleCat.of A A ⟶ ModuleCat.of A (ι →₀ A) := ModuleCat.ofHom (Finsupp.lsingle i)
  let v : ModuleCat.of A A ⟶ ModuleCat.of A I :=
    ModuleCat.ofHom (LinearMap.toSpanSingleton A I (g i))
  have hv : v = l ≫ lc := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro a
    change a • g i = Finsupp.linearCombination A g (Finsupp.single i a)
    exact (Finsupp.linearCombination_single A (v := g) a i).symm
  have hi : Sigma.ι (fun _ : ι => originalUnit X) i ≫ eF.inv = T.map l :=
    original_move_iso eF _ _ (tildeFinsupp_hom_ιFree (R := CommRingCat.of A) i)
  exact (AffineRow.idealSection_originalIdealIso I (g i)).trans
    (((congrArg T.map hv).trans (T.map_comp l lc)).trans
      (congrArg (fun k => k ≫ T.map lc) hi.symm))

/-- Actual original ideal generators give an epimorphic row of their original ideal sections. -/
private theorem affine_idealSection_row_epi
    (A : Type u) [CommRing A] (I : Ideal A) {ι : Type u} (g : ι → I)
    (hg : Submodule.span A (Set.range g) = ⊤) :
    Epi (Sigma.desc fun i => AffineCoordinates.idealSection A I (g i)) := by
  let X := Spec (.of A)
  let T := tilde.functor (.of A)
  let lc : ModuleCat.of A (ι →₀ A) ⟶ ModuleCat.of A I :=
    ModuleCat.ofHom (Finsupp.linearCombination A g)
  have hlc : Epi lc := (ModuleCat.epi_iff_surjective lc).mpr
    ((_root_.span_range_eq_top_iff_surjective_finsuppLinearCombination A).mp hg)
  let e : idealModule (affineCenter A I).subschemeι ≅ T.obj (ModuleCat.of A I) :=
    AffineRow.originalIdealIso I
  let eF : T.obj (ModuleCat.of A (ι →₀ A)) ≅ (∐ fun _ : ι => originalUnit X) :=
    tildeFinsupp (R := CommRingCat.of A) ι
  let : T.PreservesEpimorphisms := CategoryTheory.Functor.preservesEpimorphisms_of_adjunction
    (tilde.adjunction (R := CommRingCat.of A))
  have hp : Epi (eF.inv ≫ T.map lc) := original_comp_epi eF.inv (T.map lc)
    (original_iso_hom_epi (C := X.Modules) eF.symm)
      (original_map_epi_of_preserves T lc hlc)
  have hr : Epi ((Sigma.desc fun i => AffineCoordinates.idealSection A I (g i)) ≫ e.hom) :=
    (affine_idealSection_row_equation A I g).symm ▸ hp
  let : IsIso e.hom := original_iso_hom_isIso (C := X.Modules) e
  exact (epi_comp_iff_of_isIso _ e.hom).mp hr

/-- The actual products of two finite section rows generate the actual tensor module.
Only the tensor coefficient is required to be finite locally free. -/
private theorem tensor_section_row_epi {X : Scheme.{u}} {M N : X.Modules}
    [IsFiniteLocallyFree X N] {ι κ : Type u} [Finite ι]
    (s : ι → ((originalUnit X) ⟶ M)) [Epi (Sigma.desc s)]
    (t : κ → ((originalUnit X) ⟶ N)) [Epi (Sigma.desc t)] :
    Epi (Sigma.desc fun ij : ι × κ => t ij.2 ≫
      (tensorSheafLeftUnit X N).inv ≫ (moduleTensorRightFunctor X N).map (s ij.1)) := by
  let O : X.Modules := (originalUnit X)
  let T := moduleTensorRightFunctor X N
  let : T.Additive := moduleTensorRightFunctor_additive _ _
  let : T.PreservesHomology := moduleTensorRight_preservesHomology N
  let : PreservesFiniteColimits T :=
    CategoryTheory.Functor.preservesFiniteColimits_of_preservesHomology T
  let e : T.obj O ≅ N := tensorSheafLeftUnit X N
  have hs : Epi (T.map (Sigma.desc s)) := original_map_epi T _ inferInstance
  exact original_tensor_rows_epi T e s t inferInstance hs inferInstance

/-- All actual tensor powers have finite rows, constructed from the original row. -/
private theorem tensorPower_finite_row {X : Scheme.{u}} (L : LineBundle X)
    {ι : Type u} [Finite ι]
    (s : ι → ((originalUnit X) ⟶ L.val)) (hs : Epi (Sigma.desc s)) (n : ℕ) :
    ∃ (κ : Type u) (_ : Finite κ)
      (t : κ → ((originalUnit X) ⟶
        ((tensorPowerLineBundle X L n).val : X.Modules))),
      Epi (Sigma.desc t) := by
  let : Epi (Sigma.desc s) := hs
  induction n with
  | zero =>
    let O : X.Modules := (originalUnit X)
    let e : O ≅ ((tensorPowerLineBundle X L 0).val : X.Modules) :=
      (coproductUniqueIso (fun _ : PUnit.{u + 1} => O)).symm
    let : Epi e.hom := original_iso_hom_epi (C := X.Modules) e
    let t : PUnit.{u + 1} → (O ⟶ ((tensorPowerLineBundle X L 0).val : X.Modules)) := fun _ => e.hom
    have ht : Epi (Sigma.desc t) :=
      epi_of_epi_fac (show Sigma.ι (fun _ : PUnit.{u + 1} => O) PUnit.unit ≫
        Sigma.desc t = e.hom from Sigma.ι_comp_desc t PUnit.unit)
    exact ⟨PUnit.{u + 1}, inferInstance, t, ht⟩
  | succ n ih =>
    obtain ⟨κ, hκ, t, ht⟩ := ih
    let := hκ
    let := ht
    let P := tensorPowerLineBundle X L n
    let : IsFiniteLocallyFree X P.val := isFiniteLocallyFree_of_isLocallyRankOne P.property
    let v := fun ij : ι × κ => t ij.2 ≫
      (tensorSheafLeftUnit X P.val).inv ≫ (moduleTensorRightFunctor X P.val).map (s ij.1)
    exact ⟨ι × κ, inferInstance, v, tensor_section_row_epi s t⟩

/-- Original ordered cross relations, tensored with the previous original power,
give the finite row of the actual positive kernel twist. -/
private theorem kernelTensorPower_finite_row {X : Scheme.{u}} (L : LineBundle X)
    {ι : Type u} [Finite ι]
    (s : ι → ((originalUnit X) ⟶ L.val)) (hs : Epi (Sigma.desc s)) (n : ℕ) :
    ∃ (κ : Type u) (_ : Finite κ)
      (t : κ → ((originalUnit X) ⟶
        (moduleTensorRightFunctor X ((tensorPowerLineBundle X L (n + 1)).val : X.Modules)).obj
          (kernel (Sigma.desc s)))), Epi (Sigma.desc t) := by
  let π : (∐ fun _ : ι => originalUnit X) ⟶ (L.val : X.Modules) := Sigma.desc s
  let : Epi π := hs
  let : Epi (Sigma.desc s) := hs
  let K := kernel π
  let P := tensorPowerLineBundle X L n
  let : IsFiniteLocallyFree X P.val := isFiniteLocallyFree_of_isLocallyRankOne P.property
  let r := fun ij : ι × ι => generatingKernelSection L π ij.1 ij.2
  have hr : Epi (Sigma.desc r) := @generatingKernelMap_epi X ι inferInstance L π hs
  let : Epi (Sigma.desc r) := hr
  obtain ⟨κ, hκ, t, ht⟩ := tensorPower_finite_row L s hs n
  let := hκ
  let := ht
  let v := fun ij : (ι × ι) × κ => t ij.2 ≫
    (tensorSheafLeftUnit X P.val).inv ≫ (moduleTensorRightFunctor X P.val).map (r ij.1)
  have hv : Epi (Sigma.desc v) :=
    @tensor_section_row_epi X ((moduleTensorRightFunctor X L.val).obj K) P.val
      (isFiniteLocallyFree_of_isLocallyRankOne P.property) (ι × ι) κ inferInstance r hr t ht
  let : Epi (Sigma.desc v) := hv
  let e : tensorSheaf X (tensorSheaf X K L.val) P.val ≅
      (moduleTensorRightFunctor X (tensorPowerLineBundle X L (n + 1)).val).obj K :=
    tensorSheafAssociator X K L.val P.val
  have he : Epi e.hom := original_iso_hom_epi (C := X.Modules) e
  exact ⟨(ι × ι) × κ, inferInstance, fun ij => v ij ≫ e.hom,
    original_row_comp_epi (C := X.Modules) v e.hom hv he⟩

/-- Coherence of the actual tensor kernel follows from its original finite row.
It is not an additional acyclicity or presentation input. -/
private theorem kernelTensorPower_coherent {X : Scheme.{u}} [IsLocallyNoetherian X]
    (L : LineBundle X) {ι : Type u} [Finite ι]
    (π : (∐ fun _ : ι => originalUnit X) ⟶ (L.val : X.Modules)) (n : ℕ) :
    affineLocallyFiniteType X
      ((moduleTensorRightFunctor X ((tensorPowerLineBundle X L n).val : X.Modules)).obj
        (kernel π)) := by
  let O : X.Modules := (originalUnit X)
  let P := tensorPowerLineBundle X L n
  let T := moduleTensorRightFunctor X P.val
  let : IsFiniteLocallyFree X P.val := isFiniteLocallyFree_of_isLocallyRankOne P.property
  let : T.Additive := moduleTensorRightFunctor_additive _ _
  let : T.PreservesHomology := moduleTensorRight_preservesHomology P.val
  let : PreservesFiniteLimits T :=
    CategoryTheory.Functor.preservesFiniteLimits_of_preservesHomology T
  let : PreservesFiniteColimits T :=
    CategoryTheory.Functor.preservesFiniteColimits_of_preservesHomology T
  let e : T.obj (∐ fun _ : ι => originalUnit X) ≅
      ∐ fun _ : ι => P.val :=
    PreservesCoproduct.iso T (fun _ : ι => O) ≪≫
      Sigma.mapIso (fun _ : ι => tensorSheafLeftUnit X P.val)
  have hfree : affineLocallyFiniteType X
      (T.obj (∐ fun _ : ι => originalUnit X)) :=
    (affineLocallyFiniteType X).prop_of_iso e.symm
      ((affineLocallyFiniteType X).prop_coproduct
        (fun _ : ι => coherent_of_finiteLocallyFree P.val))
  let : IsFiniteLocallyFree X (T.obj L.val) :=
    isFiniteLocallyFree_of_isLocallyRankOne
      (tensorSheaf_locallyRankOne X L.val P.val L.property P.property)
  have htarget : affineLocallyFiniteType X (T.obj L.val) :=
    coherent_of_finiteLocallyFree (T.obj L.val)
  exact (affineLocallyFiniteType X).prop_of_iso (PreservesKernel.iso T π).symm
    ((affineLocallyFiniteType X).prop_kernel (T.map π) hfree htarget)

/-- The original section-kernel equivalence with only its underlying bijection exposed. -/
private def originalIdealSections {X Z : Scheme.{u}} (i : Z ⟶ X) (U : X.Opens) :
    Γ(idealModule i, U) ≃ RingHom.ker (i.app U).hom :=
  (idealSectionsEquiv i U).toEquiv

private theorem originalIdealSections_val {X Z : Scheme.{u}} (i : Z ⟶ X) (U : X.Opens)
    (s : Γ(idealModule i, U)) :
    (originalIdealSections i U s : Γ(X, U)) =
      (show Γ(X, U) from (idealInclusion i).val.app (op U) s) :=
  idealSectionsEquiv_val i U s

/-- Evaluation uses the original global structure ring as its literal target. -/
private def originalScalarEndEquiv (X : Scheme.{u}) :
    ((originalUnit X) ⟶
      (originalUnit X)) ≃ Γ(X, ⊤) :=
  unitHomGlobalSectionsEquiv X (originalUnit X)

private def originalScalarEndAddEquiv (X : Scheme.{u}) :
    ((originalUnit X) ⟶
      (originalUnit X)) ≃+ Γ(X, ⊤) :=
  unitHomGlobalSectionsAddEquiv X (originalUnit X)

private theorem originalScalarEnd_comp {X : Scheme.{u}} {M : X.Modules}
    (s : (originalUnit X) ⟶ M)
    (f : M ⟶ (originalUnit X)) :
    originalScalarEndEquiv X (s ≫ f) =
      (show Γ(X, ⊤) from f.val.app (op ⊤) (unitHomGlobalSectionsEquiv X M s)) := rfl

private theorem unitMul_value (X : Scheme.{u}) (a : Γ(X, ⊤)) :
    originalScalarEndEquiv X (unitMul X a) = a := by
  change 1 * X.presheaf.map (𝟙 (op (⊤ : X.Opens))) a = a
  rw [CategoryTheory.Functor.map_id]
  exact one_mul a

private theorem original_pullback_unitMul {X Y : Scheme.{u}} (f : X ⟶ Y) (a : Γ(Y, ⊤)) :
    pullbackUnitEnd f (unitMul Y a) = unitMul X (f.appTop a) :=
  original_conjugate_eq (C := X.Modules) (pullbackUnitIso f)
    ((Modules.pullback f).map (unitMul Y a)) (unitMul X (f.appTop a)) (unitMul_pullback f a)

private theorem original_tensor_kernel_global_surjective {X : Scheme.{u}}
    {R : Type u} [CommRing R] (α : R →+* Γ(X, ⊤))
    (T : X.Modules ⥤ X.Modules) [T.Additive] [T.PreservesHomology]
    {M N : X.Modules} (f : M ⟶ N) (hf : Epi f)
    (hH : Subsingleton (Sheaf.H.{u + 1} (Cohomology.moduleAddSheaf X (T.obj (kernel f))) 1)) :
    Function.Surjective ((T.map f).val.app (op ⊤)) := by
  let : Epi f := hf
  let : PreservesFiniteLimits T :=
    CategoryTheory.Functor.preservesFiniteLimits_of_preservesHomology T
  let : PreservesFiniteColimits T :=
    CategoryTheory.Functor.preservesFiniteColimits_of_preservesHomology T
  let : Epi (T.map (ShortComplex.kernelSequence f).g) := original_map_epi T f hf
  let S : ShortComplex X.Modules := (ShortComplex.kernelSequence f).map T
  have hS : S.ShortExact := (original_kernel_shortExact f hf).map T
  let : Subsingleton (Sheaf.H.{u + 1} (Cohomology.moduleAddSheaf X S.X₁) 1) := hH
  let := Cohomology.moduleCohomologyModuleOfHom X α S.X₃ 0
  let := Cohomology.moduleCohomologyModuleOfHom X α S.X₁ (0 + 1)
  apply Cohomology.surjective_of_moduleCohomologyConnectingOfHom_zero_eq_zero (X := X) α S hS
  apply LinearMap.ext
  intro x
  exact Subsingleton.elim _ _

/-- Scalar membership in the actual closed ideal is exactly factorization of the
original multiplication endomorphism through its original inclusion. -/
private theorem idealCoefficient_mem_iff_unitHom {X Z : Scheme.{u}} (i : Z ⟶ X)
    (a : Γ(X, ⊤)) :
    a ∈ RingHom.ker i.appTop.hom ↔
      ∃ s : (originalUnit X) ⟶ idealModule i,
        s ≫ idealInclusion i = unitMul X a := by
  constructor
  · intro ha
    let E := unitHomGlobalSectionsEquiv X (idealModule i)
    let K := originalIdealSections i ⊤
    let v : Γ(idealModule i, ⊤) := K.symm ⟨a, ha⟩
    let s := E.symm v
    refine ⟨s, (originalScalarEndEquiv X).injective ?_⟩
    exact (originalScalarEnd_comp s (idealInclusion i)).trans
      ((congrArg (fun z : Γ(idealModule i, ⊤) =>
        (show Γ(X, ⊤) from (idealInclusion i).val.app (op ⊤) z))
        (E.apply_symm_apply v)).trans
        ((originalIdealSections_val i ⊤ v).symm.trans
          ((congrArg Subtype.val (K.apply_symm_apply ⟨a, ha⟩)).trans (unitMul_value X a).symm)))
  · rintro ⟨s, hs⟩
    let v := unitHomGlobalSectionsEquiv X (idealModule i) s
    have hv : (originalIdealSections i ⊤ v : Γ(X, ⊤)) = a :=
      (originalIdealSections_val i ⊤ v).trans
        ((originalScalarEnd_comp s (idealInclusion i)).symm.trans
          ((congrArg (originalScalarEndEquiv X) hs).trans (unitMul_value X a)))
    exact hv ▸ (originalIdealSections i ⊤ v).property

namespace MaximalIdealBlowup

variable (A : Type u) [CommRing A] [IsDomain A] [IsLocalRing A]
  (hd : ringKrullDim A = 2)

/-- The original ideal element gives its actual normalized exceptional section. -/
def normalizedIdealSection (a : IsLocalRing.maximalIdeal A) :
    (originalUnit (normalization A hd)) ⟶
      idealModule (normalizedExceptionalIdeal A hd).subschemeι :=
  pullbackSection (nu A hd)
    (AffineCoordinates.tautologicalSection (datum A)
      (AffineCoordinates.idealSection A (IsLocalRing.maximalIdeal A) a)) ≫
    (normalizedIdealPullbackIso A hd).hom

/-- The original generator row with its native coproduct fixed once for all kernel consumers. -/
def normalizedIdealRow (hd : ringKrullDim A = 2) {ι : Type u}
    (g : ι → IsLocalRing.maximalIdeal A) :
    (∐ fun _ : ι => originalUnit (normalization A hd)) ⟶
      idealModule (normalizedExceptionalIdeal A hd).subschemeι :=
  Sigma.desc fun j => normalizedIdealSection A hd (g j)

/-- The finite row on the actual normalized ideal is derived from the original ideal generators. -/
theorem normalizedIdealSection_row_epi {ι : Type u} (g : ι → IsLocalRing.maximalIdeal A)
    (hg : Submodule.span A (Set.range g) = ⊤) :
    Epi (Sigma.desc fun i => normalizedIdealSection A hd (g i)) := by
  let s : ι → (originalUnit (Spec (.of A)) ⟶
      idealModule (affineCenter A (IsLocalRing.maximalIdeal A)).subschemeι) :=
    fun i => AffineCoordinates.idealSection A (IsLocalRing.maximalIdeal A) (g i)
  have hs : Epi (Sigma.desc s) := affine_idealSection_row_epi A (IsLocalRing.maximalIdeal A) g hg
  have hp : Epi (Sigma.desc fun i => pullbackSection (map A hd) (s i)) :=
    @pullback_sections_epi (X := source A hd) (Y := Spec (.of A)) (f := map A hd)
      (M := idealModule (affineCenter A (IsLocalRing.maximalIdeal A)).subschemeι)
      (ι := ι) (s := s) hs
  let t : ι → (originalUnit (source A hd) ⟶
      idealModule (exceptionalIdeal A hd).subschemeι) :=
    fun i => AffineCoordinates.tautologicalSection (datum A) (s i)
  have ht : Epi (Sigma.desc t) :=
    original_row_comp_epi (C := (source A hd).Modules)
      (fun i => pullbackSection (map A hd) (s i)) (tautologicalQuotient (datum A)) hp
        (tautologicalQuotient_epi (datum A))
  have hn : Epi (Sigma.desc fun i => pullbackSection (nu A hd) (t i)) :=
    @pullback_sections_epi (X := normalization A hd) (Y := source A hd) (f := nu A hd)
      (M := idealModule (exceptionalIdeal A hd).subschemeι) (ι := ι) (s := t) ht
  exact original_row_comp_epi (C := (normalization A hd).Modules)
    (fun i => pullbackSection (nu A hd) (t i)) (normalizedIdealPullbackIso A hd).hom hn
      (original_iso_hom_epi (C := (normalization A hd).Modules) (normalizedIdealPullbackIso A hd))

/-- The actual normalized section keeps the original scalar through its actual ideal inclusion. -/
theorem normalizedIdealSection_inclusion (hd : ringKrullDim A = 2)
    (a : IsLocalRing.maximalIdeal A) :
    normalizedIdealSection A hd a ≫ idealInclusion (normalizedExceptionalIdeal A hd).subschemeι =
      pullbackUnitEnd (nu A hd)
        (pullbackUnitEnd (map A hd) (IdealFrames.affineMultiplication A (a : A))) := by
  let t := AffineCoordinates.tautologicalSection (datum A)
    (AffineCoordinates.idealSection A (IsLocalRing.maximalIdeal A) a)
  have hp := original_pullback_paste (Modules.pullback (nu A hd)) (pullbackUnitIso (nu A hd))
    t (idealInclusion (exceptionalIdeal A hd).subschemeι) (normalizedIdealPullbackIso A hd).hom
    (idealInclusion (normalizedExceptionalIdeal A hd).subschemeι)
    (normalizedIdealPullbackIso_inclusion A hd)
  have ht : t ≫ idealInclusion (exceptionalIdeal A hd).subschemeι =
      pullbackUnitEnd (map A hd) (IdealFrames.affineMultiplication A (a : A)) :=
    (AffineCoordinates.tautologicalSection_inclusion (datum A)
      (AffineCoordinates.idealSection A (IsLocalRing.maximalIdeal A) a)).trans
        (congrArg (pullbackUnitEnd (map A hd))
          (AffineCoordinates.idealSection_inclusion A (IsLocalRing.maximalIdeal A) a))
  exact hp.trans (congrArg (pullbackUnitEnd (nu A hd)) ht)

/-- The inclusion is multiplication by the original structural coefficient. -/
theorem normalizedIdealSection_scalar (hd : ringKrullDim A = 2)
    (a : IsLocalRing.maximalIdeal A) :
    normalizedIdealSection A hd a ≫ idealInclusion (normalizedExceptionalIdeal A hd).subschemeι =
      unitMul (normalization A hd) (coefficients A hd (a : A)) := by
  exact (normalizedIdealSection_inclusion A hd a).trans
    ((pullbackUnitEnd_comp (nu A hd) (map A hd)
      (IdealFrames.affineMultiplication A (a : A))).symm.trans
      ((congrArg (pullbackUnitEnd (nu A hd ≫ map A hd))
        (IdealFrames.affineMultiplication_eq_unitMul A (a : A))).trans
        (original_pullback_unitMul (nu A hd ≫ map A hd) ((Scheme.ΓSpecIso (.of A)).inv (a : A)))))

/-- The actual ideal of original scalars whose structural sections vanish on the full
normalized exceptional subscheme. -/
def normalizedSectionIdeal : Ideal A :=
  (RingHom.ker (normalizedExceptionalIdeal A hd).subschemeι.appTop.hom).comap
    (coefficients A hd)

/-- Original maximal-ideal scalars are actual sections of the normalized image ideal. -/
theorem maximalIdeal_le_normalizedSectionIdeal :
    IsLocalRing.maximalIdeal A ≤ normalizedSectionIdeal A hd := by
  intro a ha
  let Y := normalization A hd
  let i := (normalizedExceptionalIdeal A hd).subschemeι
  let s : originalUnit Y ⟶ idealModule i := normalizedIdealSection A hd ⟨a, ha⟩
  let v : Γ(idealModule i, ⊤) := unitHomGlobalSectionsEquiv Y (idealModule i) s
  have hv : (originalIdealSections i ⊤ v : Γ(Y, ⊤)) = coefficients A hd a :=
    (originalIdealSections_val i ⊤ v).trans
      ((originalScalarEnd_comp s (idealInclusion i)).symm.trans
        ((congrArg (originalScalarEndEquiv Y) (normalizedIdealSection_scalar A hd ⟨a, ha⟩)).trans
          (unitMul_value Y (coefficients A hd a))))
  change coefficients A hd a ∈ RingHom.ker i.appTop.hom
  exact hv ▸ (originalIdealSections i ⊤ v).property

/-- The scalar section ideal is exactly the original maximal ideal. Nonemptiness of the
actual exceptional subscheme rules out the unit ideal; normality of A is not needed here. -/
theorem normalizedSectionIdeal_eq [IsNoetherianRing A]
    (hA : IsNagataRing.{u, 0} A) :
    normalizedSectionIdeal A hd = IsLocalRing.maximalIdeal A := by
  let i := (normalizedExceptionalIdeal A hd).subschemeι
  obtain ⟨y, hy⟩ := normalizedExceptional_nonempty A hd hA
  have hy' : y ∈ Set.range i := by
    rw [Scheme.IdealSheafData.range_subschemeι]
    exact hy
  obtain ⟨z, _⟩ := hy'
  let : Nonempty (⊤ : (normalizedExceptionalIdeal A hd).subscheme.Opens) :=
    ⟨⟨z, trivial⟩⟩
  have hproper : normalizedSectionIdeal A hd ≠ ⊤ := by
    intro ht
    have h1 : (1 : A) ∈ normalizedSectionIdeal A hd := by rw [ht]; trivial
    change i.appTop (coefficients A hd 1) = 0 at h1
    rw [map_one, map_one] at h1
    exact one_ne_zero h1
  exact (Ideal.IsMaximal.eq_of_le (inferInstance : (IsLocalRing.maximalIdeal A).IsMaximal)
    hproper (maximalIdeal_le_normalizedSectionIdeal A hd)).symm

/-- Membership retains the literal inclusion of original global sections. -/
theorem normalizedIdealSection_exists_iff [IsNoetherianRing A]
    (hA : IsNagataRing.{u, 0} A) (a : A) :
    (∃ s : Γ(idealModule (normalizedExceptionalIdeal A hd).subschemeι, ⊤),
      (idealInclusion (normalizedExceptionalIdeal A hd).subschemeι).val.app (op ⊤) s =
        coefficients A hd a) ↔ a ∈ IsLocalRing.maximalIdeal A := by
  let i := (normalizedExceptionalIdeal A hd).subschemeι
  rw [← normalizedSectionIdeal_eq A hd hA]
  change (∃ s : Γ(idealModule i, ⊤),
    (idealInclusion i).val.app (op ⊤) s = coefficients A hd a) ↔
      coefficients A hd a ∈ RingHom.ker i.appTop.hom
  constructor
  · rintro ⟨s, hs⟩
    have h := (originalIdealSections_val i ⊤ s).trans hs
    exact h ▸ (originalIdealSections i ⊤ s).property
  · intro ha
    let v := (originalIdealSections i ⊤).symm ⟨coefficients A hd a, ha⟩
    refine ⟨v, ?_⟩
    exact (originalIdealSections_val i ⊤ v).symm.trans
      (congrArg Subtype.val ((originalIdealSections i ⊤).apply_symm_apply
        ⟨coefficients A hd a, ha⟩))

/-- Finite original maximal-ideal generators produce the actual finite normalized ideal row. -/
theorem exists_finite_normalizedIdealSection_row [IsNoetherianRing A] :
    ∃ (n : ℕ) (g : ULift.{u} (Fin n) → IsLocalRing.maximalIdeal A),
      Submodule.span A (Set.range g) = ⊤ ∧
      Epi (Sigma.desc fun i => normalizedIdealSection A hd (g i)) := by
  obtain ⟨n, g₀, hg₀⟩ := Module.Finite.exists_fin (R := A) (M := IsLocalRing.maximalIdeal A)
  let g : ULift.{u} (Fin n) → IsLocalRing.maximalIdeal A := fun i => g₀ i.down
  have hrange : Set.range g = Set.range g₀ := by
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨i.down, rfl⟩
    · rintro ⟨i, rfl⟩
      exact ⟨ULift.up i, rfl⟩
  have hg : Submodule.span A (Set.range g) = ⊤ :=
    (congrArg (Submodule.span A) hrange).trans hg₀
  exact ⟨n, g, hg, normalizedIdealSection_row_epi A hd g hg⟩

/-- The actual normalized exceptional ideal has H1 zero, with its finite row derived. -/
theorem normalizedExceptionalIdeal_H1 [IsNoetherianRing A]
    (hA : IsNagataRing.{u, 0} A) (hRat : NormalModificationH1Vanishing A) :
    Subsingleton (Sheaf.H.{u + 1}
      (Cohomology.moduleAddSheaf (normalization A hd)
        (idealModule (normalizedExceptionalIdeal A hd).subschemeι)) 1) := by
  let M := idealModule (normalizedExceptionalIdeal A hd).subschemeι
  let : IsFiniteLocallyFree (normalization A hd) M :=
    Invertible.isFiniteLocallyFree_of_isLocallyRankOne (normalizedExceptional_isLocallyRankOne A hd)
  obtain ⟨n, g, _, hepi⟩ := exists_finite_normalizedIdealSection_row A hd
  let := hepi
  exact @normalization_finiteRow_H1 A _ _ _ _ hd hA hRat (ULift.{u} (Fin n)) inferInstance
    M (coherent_of_finiteLocallyFree M) (fun i => normalizedIdealSection A hd (g i)) hepi

/-- The actual normalized exceptional ideal, bundled with its derived invertibility. -/
def normalizedIdealLineBundle : LineBundle (normalization A hd) :=
  ⟨idealModule (normalizedExceptionalIdeal A hd).subschemeι,
    normalizedExceptional_isLocallyRankOne A hd⟩

/-- The native tensor power of the actual normalized ideal, in its native module category. -/
abbrev normalizedIdealTensorPower (n : ℕ) : (normalization A hd).Modules :=
  (tensorPowerLineBundle (normalization A hd) (normalizedIdealLineBundle A hd) n).val

/-- The original sheaf of the nth power of the literal normalized exceptional ideal. -/
def normalizedIdealPower (n : ℕ) : (normalization A hd).Modules :=
  idealModule ((normalizedExceptionalIdeal A hd) ^ n).subschemeι

/-- Native Cartier multiplication compares the actual tensor power with the same ideal power. -/
def normalizedIdealPowerIso (n : ℕ) :
    (normalizedIdealTensorPower A hd n) ≅
      normalizedIdealPower A hd n := by
  let i := (normalizedExceptionalIdeal A hd).subschemeι
  let e := Surfaces.Contraction.FormalNeighborhood.cartierIdealPowerIso i
    (normalizedExceptional_isLocallyRankOne A hd) n
  have hi : i.ker ^ n = (normalizedExceptionalIdeal A hd) ^ n := by
    simp only [i, Scheme.IdealSheafData.ker_subschemeι]
  exact e ≪≫ eqToIso (congrArg
    (fun J : (normalization A hd).IdealSheafData => idealModule J.subschemeι) hi)

/-- The original tensor-power inclusion, through the native Cartier power comparison. -/
def normalizedTensorPowerInclusion (n : ℕ) :
    (normalizedIdealTensorPower A hd n) ⟶
      (originalUnit (normalization A hd)) :=
  (Surfaces.Contraction.FormalNeighborhood.cartierIdealPowerIso
    (normalizedExceptionalIdeal A hd).subschemeι
    (normalizedExceptional_isLocallyRankOne A hd) n).hom ≫
      idealInclusion ((normalizedExceptionalIdeal A hd).subschemeι.ker ^ n).subschemeι

/-- The original scalar preimage of the literal closed ideal-power section kernel. -/
def normalizedPowerSectionIdeal (n : ℕ) : Ideal A :=
  (RingHom.ker (((normalizedExceptionalIdeal A hd).subschemeι.ker ^ n).subschemeι.appTop).hom).comap
    (coefficients A hd)

/-- This displayed power ideal is exactly the original normalized exceptional ideal power. -/
theorem normalizedPowerSectionIdeal_eq_original (n : ℕ) :
    normalizedPowerSectionIdeal A hd n =
      (RingHom.ker (((normalizedExceptionalIdeal A hd) ^ n).subschemeι.appTop).hom).comap
        (coefficients A hd) := by
  exact congrArg (fun J : (normalization A hd).IdealSheafData =>
    (RingHom.ker ((J ^ n).subschemeι.appTop).hom).comap (coefficients A hd))
      (Scheme.IdealSheafData.ker_subschemeι (normalizedExceptionalIdeal A hd))

/-- Original scalar membership is equivalent to an original tensor-power section
with the displayed original ideal inclusion. -/
theorem normalizedPowerSectionIdeal_mem_iff (n : ℕ) (a : A) :
    a ∈ normalizedPowerSectionIdeal A hd n ↔
      ∃ s : (originalUnit (normalization A hd)) ⟶
        (normalizedIdealTensorPower A hd n),
        s ≫ normalizedTensorPowerInclusion A hd n =
          unitMul (normalization A hd) (coefficients A hd a) := by
  let i := (normalizedExceptionalIdeal A hd).subschemeι
  let e := Surfaces.Contraction.FormalNeighborhood.cartierIdealPowerIso i
    (normalizedExceptional_isLocallyRankOne A hd) n
  change coefficients A hd a ∈ RingHom.ker (i.ker ^ n).subschemeι.appTop.hom ↔ _
  rw [idealCoefficient_mem_iff_unitHom]
  constructor
  · rintro ⟨s, hs⟩
    refine ⟨s ≫ e.inv, ?_⟩
    change (s ≫ e.inv) ≫ e.hom ≫ idealInclusion (i.ker ^ n).subschemeι = _
    exact (original_iso_cancel (C := (normalization A hd).Modules) s e
      (idealInclusion (i.ker ^ n).subschemeι)).trans hs
  · rintro ⟨s, hs⟩
    exact ⟨s ≫ e.hom, (Category.assoc _ _ _).trans hs⟩

/-- Degree one retains the same original exceptional section ideal. -/
theorem normalizedPowerSectionIdeal_one :
    normalizedPowerSectionIdeal A hd 1 = normalizedSectionIdeal A hd := by
  have h : (normalizedExceptionalIdeal A hd).subschemeι.ker ^ 1 =
      normalizedExceptionalIdeal A hd :=
    (pow_one _).trans (Scheme.IdealSheafData.ker_subschemeι (normalizedExceptionalIdeal A hd))
  exact congrArg (fun J : (normalization A hd).IdealSheafData =>
    (RingHom.ker J.subschemeι.appTop.hom).comap (coefficients A hd)) h

/-- The zeroth original ideal-power section image is the original base ring. -/
theorem normalizedPowerSectionIdeal_zero : normalizedPowerSectionIdeal A hd 0 = ⊤ := by
  let Y := normalization A hd
  have htop : IsIso (idealInclusion (⊤ : Y.IdealSheafData).subschemeι) :=
    original_iso_inv_isIso (C := Y.Modules)
      (Surfaces.Contraction.FormalNeighborhood.topIdealModuleIso (X := Y))
  have hpow : (normalizedExceptionalIdeal A hd).subschemeι.ker ^ 0 =
      (⊤ : Y.IdealSheafData) := pow_zero _
  have hi : IsIso (idealInclusion
      ((normalizedExceptionalIdeal A hd).subschemeι.ker ^ 0).subschemeι) := by
    exact (congrArg (fun J : Y.IdealSheafData => IsIso (idealInclusion J.subschemeι)) hpow).mpr htop
  let e : ((tensorPowerLineBundle Y (normalizedIdealLineBundle A hd) 0).val : Y.Modules) ≅
      idealModule ((normalizedExceptionalIdeal A hd).subschemeι.ker ^ 0).subschemeι :=
    Surfaces.Contraction.FormalNeighborhood.cartierIdealPowerIso
      (normalizedExceptionalIdeal A hd).subschemeι (normalizedExceptional_isLocallyRankOne A hd) 0
  let : IsIso (normalizedTensorPowerInclusion A hd 0) :=
    original_comp_isIso (C := Y.Modules) e.hom
      (idealInclusion ((normalizedExceptionalIdeal A hd).subschemeι.ker ^ 0).subschemeι)
      (original_iso_hom_isIso (C := Y.Modules) e) hi
  apply top_unique
  intro a _
  apply (normalizedPowerSectionIdeal_mem_iff A hd 0 a).mpr
  refine ⟨unitMul (normalization A hd) (coefficients A hd a) ≫
    inv (normalizedTensorPowerInclusion A hd 0), ?_⟩
  exact original_inv_factor (C := (normalization A hd).Modules)
    (normalizedTensorPowerInclusion A hd 0) inferInstance
    (unitMul (normalization A hd) (coefficients A hd a))

/-- Native Cartier multiplication gives the product of the original ideal inclusions
on every original pure tensor section. -/
theorem normalizedTensorPowerInclusion_succ_section (n : ℕ)
    (U : (normalization A hd).Opens)
    (m : Γ(idealModule (normalizedExceptionalIdeal A hd).subschemeι, U))
    (p : Γ((normalizedIdealTensorPower A hd n), U)) :
    (normalizedTensorPowerInclusion A hd (n + 1)).val.app (op U)
      (moduleTensorSection (normalization A hd)
        (idealModule (normalizedExceptionalIdeal A hd).subschemeι)
        (normalizedIdealTensorPower A hd n) U m p) =
      (show Γ(normalization A hd, U) from
        (idealInclusion (normalizedExceptionalIdeal A hd).subschemeι).val.app (op U) m) *
      (show Γ(normalization A hd, U) from
        (normalizedTensorPowerInclusion A hd n).val.app (op U) p) := by
  let Y := normalization A hd
  let i := (normalizedExceptionalIdeal A hd).subschemeι
  let P : Y.Modules := normalizedIdealTensorPower A hd n
  let e : P ≅ idealModule (i.ker ^ n).subschemeι :=
    Surfaces.Contraction.FormalNeighborhood.cartierIdealPowerIso i
      (normalizedExceptional_isLocallyRankOne A hd) n
  let z := moduleTensorSection Y (idealModule i) P U m p
  let k := Cartier.idealMultiplication i (i.ker ^ n).subschemeι
  have hcat := Surfaces.Contraction.FormalNeighborhood.cartierIdealPowerIso_succ_inclusion
    i (normalizedExceptional_isLocallyRankOne A hd) n
  have h₀ := congrArg (fun f : tensorSheaf Y (idealModule i) P ⟶ originalUnit Y =>
    (show Γ(Y, U) from f.val.app (op U) z)) hcat
  have h₁ := congrArg (fun w => (show Γ(Y, U) from k.val.app (op U) w))
    (moduleTensorLeftFunctor_map_section (idealModule i) e.hom U m p)
  exact h₀.trans (h₁.trans
    (idealMultiplication_section i (i.ker ^ n).subschemeι U m (e.hom.val.app (op U) p)))

/-- Every original normalized exceptional ideal power has vanishing H1.
The finite rows, coherence and higher-kernel vanishing are all derived. -/
theorem normalizedIdealPower_H1 [IsNoetherianRing A]
    (hA : IsNagataRing.{u, 0} A) (hRat : NormalModificationH1Vanishing A) (n : ℕ) :
    Subsingleton (Sheaf.H.{u + 1}
      (Cohomology.moduleAddSheaf (normalization A hd) (normalizedIdealPower A hd n)) 1) := by
  obtain ⟨d, g, _, hepi⟩ := exists_finite_normalizedIdealSection_row A hd
  let := hepi
  let L := normalizedIdealLineBundle A hd
  let P := tensorPowerLineBundle (normalization A hd) L n
  obtain ⟨κ, hκ, t, ht⟩ := tensorPower_finite_row L
    (fun j => normalizedIdealSection A hd (g j)) hepi n
  let := hκ
  let := ht
  let : IsFiniteLocallyFree (normalization A hd) P.val :=
    isFiniteLocallyFree_of_isLocallyRankOne P.property
  have hH := @normalization_finiteRow_H1 A _ _ _ _ hd hA hRat κ hκ P.val
    (coherent_of_finiteLocallyFree P.val) t ht
  exact Cohomology.moduleCohomology_subsingleton_of_iso (normalizedIdealPowerIso A hd n) 1 hH

/-- The actual kernel of the original generator row, tensored with the original ideal power. -/
def normalizedIdealKernelPower {ι : Type u} (g : ι → IsLocalRing.maximalIdeal A) (n : ℕ) :
    (normalization A hd).Modules :=
  (moduleTensorRightFunctor (normalization A hd)
    (normalizedIdealTensorPower A hd n)).obj
      (kernel (normalizedIdealRow A hd g))

/-- Positive twists of the actual original row kernel have H1 zero.
The cross-relation row and its coherence are constructed from the original generator row. -/
theorem normalizedIdealKernelPower_H1 [IsNoetherianRing A]
    (hA : IsNagataRing.{u, 0} A) (hRat : NormalModificationH1Vanishing A)
    {ι : Type u} [Finite ι] (g : ι → IsLocalRing.maximalIdeal A)
    (hg : Submodule.span A (Set.range g) = ⊤) (n : ℕ) :
    Subsingleton (Sheaf.H.{u + 1} (Cohomology.moduleAddSheaf (normalization A hd)
      (normalizedIdealKernelPower A hd g (n + 1))) 1) := by
  let Y := normalization A hd
  let : IsLocallyNoetherian Y := normalization_isLocallyNoetherian A hd hA
  let L := normalizedIdealLineBundle A hd
  let s := fun j => normalizedIdealSection A hd (g j)
  let : Epi (Sigma.desc s) := normalizedIdealSection_row_epi A hd g hg
  obtain ⟨κ, hκ, t, ht⟩ := kernelTensorPower_finite_row L s
    (normalizedIdealSection_row_epi A hd g hg) n
  let := hκ
  let := ht
  exact @normalization_finiteRow_H1 A _ _ _ _ hd hA hRat κ hκ
    (normalizedIdealKernelPower A hd g (n + 1))
    (kernelTensorPower_coherent L (Sigma.desc s) (n + 1)) t ht

/-- The actual positive tensor twist of the original generator row is surjective
on global sections, by its derived kernel H1 vanishing. -/
theorem normalizedIdealTensorRow_global_surjective [IsNoetherianRing A]
    (hA : IsNagataRing.{u, 0} A) (hRat : NormalModificationH1Vanishing A)
    {ι : Type u} [Finite ι] (g : ι → IsLocalRing.maximalIdeal A)
    (hg : Submodule.span A (Set.range g) = ⊤) (n : ℕ) :
    Function.Surjective
      (((moduleTensorRightFunctor (normalization A hd)
        (normalizedIdealTensorPower A hd (n + 1))).map
            (normalizedIdealRow A hd g)).val.app (op ⊤)) := by
  let Y := normalization A hd
  let L := normalizedIdealLineBundle A hd
  let P := tensorPowerLineBundle Y L (n + 1)
  let π := normalizedIdealRow A hd g
  have hπ : Epi π := normalizedIdealSection_row_epi A hd g hg
  let : IsFiniteLocallyFree Y P.val := isFiniteLocallyFree_of_isLocallyRankOne P.property
  let T := moduleTensorRightFunctor Y P.val
  let : T.Additive := moduleTensorRightFunctor_additive Y P.val
  let : T.PreservesHomology := moduleTensorRight_preservesHomology P.val
  exact original_tensor_kernel_global_surjective (coefficients A hd) T π hπ
    (normalizedIdealKernelPower_H1 A hd hA hRat g hg n)

/-- The original ideal element acts from the nth tensor power to the next power. -/
def normalizedTensorPowerRowSection (a : IsLocalRing.maximalIdeal A) (n : ℕ) :
    (normalizedIdealTensorPower A hd n) ⟶
      (normalizedIdealTensorPower A hd (n + 1)) :=
  (tensorSheafLeftUnit (normalization A hd)
    (normalizedIdealTensorPower A hd n)).inv ≫
      (moduleTensorRightFunctor (normalization A hd)
        (normalizedIdealTensorPower A hd n)).map
          (normalizedIdealSection A hd a)

/-- This same power-row component multiplies by the original base-ring element. -/
theorem normalizedTensorPowerRowSection_value (a : IsLocalRing.maximalIdeal A) (n : ℕ)
    (p : Γ((normalizedIdealTensorPower A hd n), ⊤)) :
    (normalizedTensorPowerInclusion A hd (n + 1)).val.app (op ⊤)
      ((normalizedTensorPowerRowSection A hd a n).val.app (op ⊤) p) =
        coefficients A hd (a : A) * (show Γ(normalization A hd, ⊤) from
          (normalizedTensorPowerInclusion A hd n).val.app (op ⊤) p) := by
  let Y := normalization A hd
  let P : Y.Modules := normalizedIdealTensorPower A hd n
  let i := (normalizedExceptionalIdeal A hd).subschemeι
  let s := normalizedIdealSection A hd a
  let L := fun z : Γ(normalizedIdealTensorPower A hd (n + 1), ⊤) =>
    (show Γ(Y, ⊤) from (normalizedTensorPowerInclusion A hd (n + 1)).val.app (op ⊤) z)
  let T := (moduleTensorCoefficientMap Y s).app P
  have hs : (show Γ(Y, ⊤) from (idealInclusion i).val.app (op ⊤)
      (s.val.app (op ⊤) (1 : Γ(Y, ⊤)))) = coefficients A hd (a : A) :=
    (congrArg (originalScalarEndEquiv Y) (normalizedIdealSection_scalar A hd a)).trans
      (unitMul_value Y (coefficients A hd (a : A)))
  have hu : (tensorSheafLeftUnit Y P).inv.val.app (op ⊤) p =
      moduleTensorSection Y (originalUnit Y) P ⊤ (1 : Γ(Y, ⊤)) p :=
    leftUnitor_inv_moduleTensorSection (X := Y) P ⊤ p
  have h₀ := congrArg (fun z => L (T.val.app (op ⊤) z)) hu
  have h₁ := congrArg L
    (moduleTensorCoefficientMap_section s P ⊤ (1 : Γ(Y, ⊤)) p)
  have h₂ := normalizedTensorPowerInclusion_succ_section A hd n ⊤
    (s.val.app (op ⊤) (1 : Γ(Y, ⊤))) p
  exact h₀.trans (h₁.trans (h₂.trans
    (congrArg (fun c : Γ(Y, ⊤) => c *
      (show Γ(Y, ⊤) from (normalizedTensorPowerInclusion A hd n).val.app (op ⊤) p)) hs)))

/-- Positive original power rows are surjective on global sections in their finite
coproduct presentation, retaining every original generator component. -/
theorem normalizedTensorPowerRow_global_surjective [IsNoetherianRing A]
    (hA : IsNagataRing.{u, 0} A) (hRat : NormalModificationH1Vanishing A)
    {ι : Type u} [Finite ι] (g : ι → IsLocalRing.maximalIdeal A)
    (hg : Submodule.span A (Set.range g) = ⊤) (n : ℕ) :
    Function.Surjective ((Sigma.desc fun j =>
      normalizedTensorPowerRowSection A hd (g j) (n + 1)).val.app (op ⊤)) := by
  let Y := normalization A hd
  let O : Y.Modules := (originalUnit Y)
  let P := tensorPowerLineBundle Y (normalizedIdealLineBundle A hd) (n + 1)
  let T := moduleTensorRightFunctor Y P.val
  let : IsFiniteLocallyFree Y P.val := isFiniteLocallyFree_of_isLocallyRankOne P.property
  let : T.Additive := moduleTensorRightFunctor_additive _ _
  let : T.PreservesHomology := moduleTensorRight_preservesHomology P.val
  let : PreservesFiniteColimits T :=
    CategoryTheory.Functor.preservesFiniteColimits_of_preservesHomology T
  let π := normalizedIdealRow A hd g
  let e : T.obj (∐ fun _ : ι => originalUnit Y) ≅
      ∐ fun _ : ι => P.val :=
    PreservesCoproduct.iso T (fun _ : ι => O) ≪≫
      Sigma.mapIso (fun _ : ι => tensorSheafLeftUnit Y P.val)
  let r := Sigma.desc fun j => normalizedTensorPowerRowSection A hd (g j) (n + 1)
  have hr : r = e.inv ≫ T.map π :=
    original_tensor_row_comparison T (tensorSheafLeftUnit Y P.val)
      (fun j => normalizedIdealSection A hd (g j))
  have hfac : e.hom ≫ r = T.map π :=
    (congrArg (fun k => e.hom ≫ k) hr).trans
      (original_iso_hom_cancel (C := Y.Modules) e (T.map π))
  intro y
  obtain ⟨x, hx⟩ := normalizedIdealTensorRow_global_surjective A hd hA hRat g hg n y
  refine ⟨e.hom.val.app (op ⊤) x, ?_⟩
  change (e.hom ≫ r).val.app (op ⊤) x = y
  exact (congrArg (fun k : T.obj (∐ fun _ : ι => originalUnit Y) ⟶
    T.obj (normalizedIdealLineBundle A hd).val => k.val.app (op ⊤) x) hfac).trans hx

/-- Each original section of a positive ideal power is a finite sum of the
original generator components applied to sections of the previous power. -/
theorem normalizedTensorPowerRow_decomposition [IsNoetherianRing A]
    (hA : IsNagataRing.{u, 0} A) (hRat : NormalModificationH1Vanishing A)
    {ι : Type u} [Fintype ι] (g : ι → IsLocalRing.maximalIdeal A)
    (hg : Submodule.span A (Set.range g) = ⊤) (n : ℕ)
    (s : (originalUnit (normalization A hd)) ⟶
      (normalizedIdealTensorPower A hd (n + 2))) :
    ∃ c : ι → ((originalUnit (normalization A hd)) ⟶
      (normalizedIdealTensorPower A hd (n + 1))),
      s = ∑ j, c j ≫ normalizedTensorPowerRowSection A hd (g j) (n + 1) := by
  let Y := normalization A hd
  let P := normalizedIdealTensorPower A hd (n + 1)
  let Q := normalizedIdealTensorPower A hd (n + 2)
  let r := Sigma.desc fun j => normalizedTensorPowerRowSection A hd (g j) (n + 1)
  obtain ⟨t, ht⟩ := exists_unitHom_factor_of_surjective r
    (normalizedTensorPowerRow_global_surjective A hd hA hRat g hg n) s
  let t' : originalUnit Y ⟶ (∐ fun _ : ι => P) := t
  have ht' : t' ≫ r = s := ht
  obtain ⟨c, hc⟩ := original_row_sum_decomposition (C := Y.Modules)
    (O := originalUnit Y) (M := P) (N := Q)
    (fun j => normalizedTensorPowerRowSection A hd (g j) (n + 1)) t'
  exact ⟨c, ht'.symm.trans hc⟩

/-- Products of original ideal scalars and original power sections land in the
same next original power, by actual Cartier multiplication. -/
theorem maximalIdeal_mul_normalizedPowerSectionIdeal_le (n : ℕ) :
    IsLocalRing.maximalIdeal A * normalizedPowerSectionIdeal A hd n ≤
      normalizedPowerSectionIdeal A hd (n + 1) := by
  apply Ideal.mul_le.mpr
  intro a ha b hb
  obtain ⟨s, hs⟩ := (normalizedPowerSectionIdeal_mem_iff A hd n b).mp hb
  apply (normalizedPowerSectionIdeal_mem_iff A hd (n + 1) (a * b)).mpr
  refine ⟨s ≫ normalizedTensorPowerRowSection A hd ⟨a, ha⟩ n, ?_⟩
  let Y := normalization A hd
  let p := unitHomGlobalSectionsEquiv Y (normalizedIdealTensorPower A hd n) s
  have hs' : (show Γ(Y, ⊤) from
      (normalizedTensorPowerInclusion A hd n).val.app (op ⊤) p) = coefficients A hd b :=
    (congrArg (originalScalarEndEquiv Y) hs).trans (unitMul_value Y (coefficients A hd b))
  apply (originalScalarEndEquiv Y).injective
  exact (normalizedTensorPowerRowSection_value A hd ⟨a, ha⟩ n p).trans
    ((congrArg (fun z : Γ(Y, ⊤) => coefficients A hd a * z) hs').trans
      ((map_mul (coefficients A hd) a b).symm.trans
        (unitMul_value Y (coefficients A hd (a * b))).symm))

/-- The original positive power-section ideals satisfy the actual multiplication
recurrence. Normality is used only for the original coefficient bijection. -/
theorem normalizedPowerSectionIdeal_succ_eq [IsNoetherianRing A] [IsIntegrallyClosed A]
    (hA : IsNagataRing.{u, 0} A) (hRat : NormalModificationH1Vanishing A) (n : ℕ) :
    normalizedPowerSectionIdeal A hd (n + 2) =
      IsLocalRing.maximalIdeal A * normalizedPowerSectionIdeal A hd (n + 1) := by
  classical
  apply le_antisymm
  · intro a ha
    obtain ⟨d, g, hg, _⟩ := exists_finite_normalizedIdealSection_row A hd
    obtain ⟨s, hs⟩ := (normalizedPowerSectionIdeal_mem_iff A hd (n + 2) a).mp ha
    obtain ⟨c, hc⟩ := normalizedTensorPowerRow_decomposition A hd hA hRat g hg n s
    let Y := normalization A hd
    let ρ := normalizedTensorPowerInclusion A hd (n + 1)
    let ev := originalScalarEndEquiv Y
    choose b hb using fun j : ULift.{u} (Fin d) =>
      (coefficients_bijective A hd hA).2 (ev (c j ≫ ρ))
    have hbmem (j : ULift.{u} (Fin d)) : b j ∈ normalizedPowerSectionIdeal A hd (n + 1) := by
      apply (normalizedPowerSectionIdeal_mem_iff A hd (n + 1) (b j)).mpr
      refine ⟨c j, ?_⟩
      apply ev.injective
      rw [unitMul_value]
      exact (hb j).symm
    have hscalar : coefficients A hd a =
        ∑ j : ULift.{u} (Fin d), coefficients A hd (g j : A) * coefficients A hd (b j) := by
      have hs' := congrArg ev hs
      rw [unitMul_value] at hs'
      rw [← hs', hc, Preadditive.sum_comp]
      change (originalScalarEndAddEquiv Y)
        (∑ j, (c j ≫ normalizedTensorPowerRowSection A hd (g j) (n + 1)) ≫
          normalizedTensorPowerInclusion A hd (n + 2)) = _
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro j _
      change (normalizedTensorPowerInclusion A hd (n + 2)).val.app (op ⊤)
        ((normalizedTensorPowerRowSection A hd (g j) (n + 1)).val.app (op ⊤)
          ((c j).val.app (op ⊤) (1 : Γ(Y, ⊤)))) = _
      exact (normalizedTensorPowerRowSection_value A hd (g j) (n + 1)
        ((c j).val.app (op ⊤) (1 : Γ(Y, ⊤)))).trans
          (congrArg (fun z : Γ(Y, ⊤) => coefficients A hd (g j : A) * z) (hb j).symm)
    have haeq : a = ∑ j : ULift.{u} (Fin d), (g j : A) * b j := by
      apply (coefficients_bijective A hd hA).1
      simpa only [map_sum, map_mul] using hscalar
    rw [haeq]
    exact Ideal.sum_mem _ (fun j _ => Ideal.mul_mem_mul (g j).property (hbmem j))
  · exact maximalIdeal_mul_normalizedPowerSectionIdeal_le A hd (n + 1)

/-- The actual original ideal-power section image is exactly the corresponding
power of the original maximal ideal. -/
theorem normalizedPowerSectionIdeal_eq [IsNoetherianRing A] [IsIntegrallyClosed A]
    (hA : IsNagataRing.{u, 0} A) (hRat : NormalModificationH1Vanishing A) (n : ℕ) :
    normalizedPowerSectionIdeal A hd n = IsLocalRing.maximalIdeal A ^ n := by
  cases n with
  | zero =>
    simpa only [pow_zero, Ideal.one_eq_top] using normalizedPowerSectionIdeal_zero A hd
  | succ n =>
    induction n with
    | zero => rw [normalizedPowerSectionIdeal_one, normalizedSectionIdeal_eq A hd hA, pow_one]
    | succ n ih =>
      exact (normalizedPowerSectionIdeal_succ_eq A hd hA hRat n).trans
        ((congrArg (fun J : Ideal A => IsLocalRing.maximalIdeal A * J) ih).trans
          (pow_succ' (IsLocalRing.maximalIdeal A) (n + 1)).symm)

/-- The section-image conclusion is stated on the literal original ideal powers,
not on a replacement tensor object or chosen copy of the global coefficient ring. -/
theorem normalizedIdealPower_sectionImage [IsNoetherianRing A] [IsIntegrallyClosed A]
    (hA : IsNagataRing.{u, 0} A) (hRat : NormalModificationH1Vanishing A) (n : ℕ) :
    (RingHom.ker (((normalizedExceptionalIdeal A hd) ^ n).subschemeι.appTop).hom).comap
      (coefficients A hd) = IsLocalRing.maximalIdeal A ^ n :=
  (normalizedPowerSectionIdeal_eq_original A hd n).symm.trans
    (normalizedPowerSectionIdeal_eq A hd hA hRat n)

end MaximalIdealBlowup

end AlgebraicGeometry.Scheme.RationalSingularities
