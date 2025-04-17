import Mathlib.AlgebraicTopology.SimplicialSet.Basic
import Mathlib.AlgebraicTopology.SingularSet
import Mathlib.AlgebraicTopology.SingularHomology.Basic
import Mathlib.Topology.Basic
import Mathlib.Topology.Category.TopCat.Basic
import Mathlib.Algebra.Homology.Homotopy
import Mathlib.AlgebraicTopology.TopologicalSimplex

/-
The singular chain complex of a topological space X is local on X.
Explicitly, if U (i:I), U i = X, then C(X,A) = ⊕ (i : I) C(U i).
-/

namespace AlgebraicTopology

open Topology CategoryTheory TopCat

noncomputable section

universe w v u

variable (C : Type u) [Category.{v} C] [Limits.HasCoproducts.{0} C]
variable [Preadditive C] [CategoryWithHomology C] (n : ℕ)
variable (R : C)
variable (X : TopCat.{0})


/-
Barycentric subdivision of the standard n simplex
Bary: Fin (n choose n-1) -> Cont(Δ_n, Δ_n)
Lemma: Diam Bary(k) < n/(n+1)
-/



/-
Define subdivision chain maps S: C(X) → C(X), by σ ↦ ∑ (-1)^k σ ∘ Bary(k)
Lemma: S ≃ id
More generally, S^m ≃ id
-/



/-
Lemma ∃m s.t. S^m factors through ⊕ (i : I) C(U i)
Conclude
-/


 variable (α : Type) (V : α → Set X) (ho : ∀ (i : α), IsOpen (V i)) (hU : ⋃ (i : α), V i = Set.univ) (i : α )



def f := fun i: α  => ((singularChainComplexFunctor C).obj R).obj (TopCat.of (V i))


def cop [Limits.HasCoproducts C] (h : α → ChainComplex C ℕ ) :ChainComplex C ℕ := h i




def g (C : Type u) [Category.{v, u} C] [Limits.HasCoproducts C] [Preadditive C] {R : C}
  {X : TopCat} {α : Type w} {V : α → Set ↑X} (i: α) : ChainComplex C ℕ :=
  ((singularChainComplexFunctor C).obj R).obj (TopCat.of (V i))


/-
def HomotopyEquiv_of_cover : HomotopyEquiv (((singularChainComplexFunctor C).obj R).obj X) (∐ g) where
  hom := sorry
  inv := sorry
  homotopyHomInvId := sorry
  homotopyInvHomId := sorry
-/

#check f
#check ∐ g C

--def F (i : α ) : ChainComplex C ℕ  := ((singularChainComplexFunctor C).obj R).obj
--(TopCat.of (V i))

--#check F

#check ((singularChainComplexFunctor C).obj R).obj X

/-
theorem singularChainComplex_of_openCover [Limits.HasCoproducts.{0} C]
    (C : Type u) [Category.{v, u} C] [Limits.HasCoproducts C] [Preadditive C] (R : C)
    (X : TopCat {α : Type w} {V : α → Set ↑X}  :
    (((singularChainComplexFunctor C).obj R).obj X) ≅  := by

    sorry
-/



--∐ (fun i: α  => ((singularChainComplexFunctor C).obj R).obj (TopCat.of (U i)))
