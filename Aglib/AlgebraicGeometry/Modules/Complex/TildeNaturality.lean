/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Complex.Tilde

/-!
# Naturality of the original tilde counit on homology

The original counit comparison commutes with every actual complex map.
The statement retains the native affine action and arbitrary complex shape.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits HomologicalComplex

universe u w

namespace AlgebraicGeometry.Scheme.Modules.Complex

/-- Exact tilde and the actual counit give a natural homology comparison. -/
@[reassoc]
theorem tildeGlobalSectionsHomologyIso_naturality (R : CommRingCat.{u})
    {ι : Type w} (d : ComplexShape ι) {K L : HomologicalComplex (Spec R).Modules d}
    [QuasiIso (tildeGlobalSectionsCounit R d K)]
    [QuasiIso (tildeGlobalSectionsCounit R d L)]
    (φ : K ⟶ L) (i : ι) :
    (tilde.functor R).map
        (homologyMap ((moduleSpecΓFunctor.mapHomologicalComplex d).map φ) i) ≫
        (tildeGlobalSectionsHomologyIso R d L i).hom =
      (tildeGlobalSectionsHomologyIso R d K i).hom ≫ homologyMap φ i := by
  let C := (moduleSpecΓFunctor.mapHomologicalComplex d).obj K
  let D := (moduleSpecΓFunctor.mapHomologicalComplex d).obj L
  let z := (moduleSpecΓFunctor.mapHomologicalComplex d).map φ
  let TC := ((tilde.functor R).mapHomologicalComplex d).obj C
  let TD := ((tilde.functor R).mapHomologicalComplex d).obj D
  let a : (tilde.functor R).obj (C.homology i) ⟶
      (tilde.functor R).obj (D.homology i) :=
    (tilde.functor R).map (homologyMap z i)
  let b : (tilde.functor R).obj (D.homology i) ⟶ TD.homology i :=
    ((D.sc i).mapHomologyIso (tilde.functor R)).inv
  let c : TD.homology i ⟶ L.homology i :=
    homologyMap (tildeGlobalSectionsCounit R d L) i
  let p : (tilde.functor R).obj (C.homology i) ⟶ TC.homology i :=
    ((C.sc i).mapHomologyIso (tilde.functor R)).inv
  let q : TC.homology i ⟶ TD.homology i :=
    homologyMap (((tilde.functor R).mapHomologicalComplex d).map z) i
  let r : TC.homology i ⟶ K.homology i :=
    homologyMap (tildeGlobalSectionsCounit R d K) i
  let s : K.homology i ⟶ L.homology i := homologyMap φ i
  have ht : a ≫ b = p ≫ q :=
    ShortComplex.mapHomologyIso_inv_naturality
      ((HomologicalComplex.shortComplexFunctor (ModuleCat.{u} R) d i).map z)
      (tilde.functor R)
  let H := homologyFunctor (Spec R).Modules d i
  have hc : q ≫ c = r ≫ s :=
    (H.map_comp (((tilde.functor R).mapHomologicalComplex d).map z)
      (tildeGlobalSectionsCounit R d L)).symm.trans
      ((congrArg H.map (tildeGlobalSectionsCounit_naturality R d φ)).trans
        (H.map_comp (tildeGlobalSectionsCounit R d K) φ))
  let k : (tilde.functor R).obj (C.homology i) ⟶ K.homology i :=
    (tildeGlobalSectionsHomologyIso R d K i).hom
  let l : (tilde.functor R).obj (D.homology i) ⟶ L.homology i :=
    (tildeGlobalSectionsHomologyIso R d L i).hom
  have hK : k = p ≫ r := tildeGlobalSectionsHomologyIso_hom R d K i
  have hL : l = b ≫ c := tildeGlobalSectionsHomologyIso_hom R d L i
  have h₁ : a ≫ l = a ≫ (b ≫ c) :=
    congrArg (fun v : (tilde.functor R).obj (D.homology i) ⟶ L.homology i => a ≫ v) hL
  have h₂ : a ≫ (b ≫ c) = (a ≫ b) ≫ c := (Category.assoc a b c).symm
  have h₃ : (a ≫ b) ≫ c = (p ≫ q) ≫ c :=
    congrArg (fun v : (tilde.functor R).obj (C.homology i) ⟶ TD.homology i => v ≫ c) ht
  have h₄ : (p ≫ q) ≫ c = p ≫ (q ≫ c) := Category.assoc p q c
  have h₅ : p ≫ (q ≫ c) = p ≫ (r ≫ s) :=
    congrArg (fun v : TC.homology i ⟶ L.homology i => p ≫ v) hc
  have h₆ : p ≫ (r ≫ s) = (p ≫ r) ≫ s := (Category.assoc p r s).symm
  have h₇ : (p ≫ r) ≫ s = k ≫ s :=
    congrArg (fun v : (tilde.functor R).obj (C.homology i) ⟶ K.homology i => v ≫ s) hK.symm
  exact Eq.trans h₁ (Eq.trans h₂ (Eq.trans h₃ (Eq.trans h₄
    (Eq.trans h₅ (Eq.trans h₆ h₇)))))

end AlgebraicGeometry.Scheme.Modules.Complex
