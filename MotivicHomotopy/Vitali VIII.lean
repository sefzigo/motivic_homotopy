import Mathlib.Analysis.RCLike.Basic
import Mathlib.Order.CompletePartialOrder

set_option warningAsError false

open Set Filter Real Function Rat Classical ENNReal
noncomputable section

structure naiveMeasure where
  μ : Set ℝ → ENNReal
  monotony {A B : Set ℝ} (h : A ⊆ B) : μ A ≤ μ B
  translation_invariance {A : Set ℝ} {x : ℝ} : μ ((fun a ↦ a + x)''A) = μ A
  normalised {l : ℝ} : μ (Icc 0 l) = ENNReal.ofReal l
  sigma_additivity {A : ℕ → Set ℝ} (h : Pairwise (Disjoint on A)): μ (⋃ n, A n) = ∑' n, μ (A n)

instance : CoeFun naiveMeasure (λ _ => Set ℝ → ENNReal) where
  coe := naiveMeasure.μ

def I : Set ℝ := Icc 0 1
def J : Set ℝ := Icc (-1) 2
def J' : Set ℝ := Icc 0 3

variable (μ : naiveMeasure)

#check μ.sigma_additivity

instance equiv : Setoid I where
  r := fun x y ↦ (x.val - y.val) ∈ range ((↑) : ℚ → ℝ)
  iseqv := {
    refl := by
      intro x
      use 0
      simp

    symm := by
      rintro x y ⟨q, hxy⟩
      use (-q)
      have h₁ : y.val - x.val = -(x.val - y.val) := by ring
      rw [h₁]
      rw [← hxy]
      norm_cast

    trans := by
      rintro x y z ⟨q₁, hxy⟩ ⟨q₂, hyz⟩
      use q₁ + q₂
      simp at hxy hyz ⊢
      rw [hxy]
      rw [hyz]
      simp
  }

-- def quot := Quotient equiv

-- lemma surj : ∀ t : quot, ∃ x : { x : ℝ // x ∈ Icc 0 1 }, ⟦x⟧ = t := Quot.exists_rep

-- def rep : quot → { x : ℝ // x ∈ Icc 0 1 } :=
  -- fun t ↦ Classical.choose (Quot.exists_rep t)

-- def vitaliSet : Set ℝ := { x : ℝ | ∃ t : quot, ↑(rep t) = x }

def vitaliSet : Set ℝ := { x : ℝ | ∃ y : I, Quot.mk equiv y = ⟦y⟧ ∧ x = y.val}

def shiftRange : Set ℝ := Icc (-1) 1 ∩ range ((↑) : ℚ → ℝ)

def vitaliSet' (j : ℝ) : Set ℝ := (fun x ↦ x + j)'' vitaliSet

def vitaliUnion : Set ℝ := ⋃ i ∈ shiftRange, vitaliSet' i


lemma welldef : vitaliSet = vitaliSet' 0 := by
  unfold vitaliSet'
  ext x
  simp

lemma distinct {j k : ℕ} (h : j≠k) : vitaliSet' j ∩ vitaliSet' k = ∅ := by
  unfold vitaliSet'
  ext x
  constructor
  simp
  · by_contra c
    push_neg at c
    rcases c with ⟨⟨x1, h1⟩, ⟨x2, h2⟩⟩
    have diff : ((x1: ℝ) - (x2 : ℝ) ) = (↑k - ↑j : ℝ) := by
      ring_nf
      rw [←h2.2]
      rw [←h1.2]
      linarith
    have rat : (x1 - x2 : ℝ) ∈ range ((↑) : ℚ → ℝ) := by
      use (k - j : ℚ)
      rw [diff]
      simp
    have equiv_x1_x2 : x1 ≈ x2 := rat
    have qeq : ⟦x1⟧ = ⟦x2⟧ := Quot.sound equiv_x1_x2
    have q_eq : (↑k : ℝ) - ↑j ∈ range (Rat.cast : ℚ → ℝ) := by
      rw [←diff]
      exact rat
    have int_diff : (↑k - ↑j : ℝ) ∈ range Int.cast := by
      use (k : ℤ) - (j : ℤ)
      norm_cast
    have : k = j := by
      rcases q_eq with ⟨q, hq⟩
      have hk : (↑k : ℝ) = ↑j + q := by linarith
      have h_diff : (↑k : ℝ) - ↑j = q := by linarith
      sorry
    have contra := h this.symm
    exact contra
  · simp

lemma superset' (μ : naiveMeasure): vitaliSet ⊆ I := by
  rintro x ⟨t, ht⟩
  simp_all only [Subtype.coe_prop]

lemma bound (μ : naiveMeasure): μ vitaliSet ≤ ENNReal.ofReal 1 := by
  have h' : μ I = ENNReal.ofReal 1 := by
    exact μ.normalised
  rw[← h']
  apply μ.monotony (superset' μ)

lemma vitaliTranslations (μ : naiveMeasure) {r : ℝ} : μ vitaliSet = μ (vitaliSet' r) := by
  unfold vitaliSet'
  symm
  apply μ.translation_invariance


lemma sigma (μ : naiveMeasure) : μ vitaliUnion = ∑' r : ℝ, if r ∈ shiftRange then μ (vitaliSet' r) else 0 := by
  unfold vitaliUnion
  unfold vitaliSet'
  -- vitaliDisjoint and μ.sigma_additivity
  sorry


lemma superset (μ : naiveMeasure) : I ⊆ vitaliUnion := by
  -- surely the smallest/biggest element of vitaliUnion is smaller/bigger (or equal to) than 0/1.
  -- the hard part is to show that for any element in I, there is an element in vitaliUnion
  sorry

lemma subset (μ : naiveMeasure) : vitaliUnion ⊆ J := by
  unfold vitaliUnion
  intro x
  simp
  intro r hr hx
  unfold vitaliSet' at hx
  simp at hx
  rcases hx with ⟨v, hv, hx⟩

  have r_bounds : r ∈ Icc (-1) 1 := by
    unfold shiftRange at hr
    simp at hr
    exact hr.1

  unfold J
  simp
  constructor
  · sorry
  sorry

lemma threeJ (μ : naiveMeasure) : μ J = ENNReal.ofReal 3 := by
  have eqJ (μ : naiveMeasure) : μ J = μ J' := by
    have h_translate : J' = (fun a ↦ a + 1)''J := by
      ext x
      simp [J, J']
      intro h
      constructor
      · intro h'
        linarith
      intro h''
      linarith
    rw [h_translate]
    exact Eq.symm μ.translation_invariance
  rw[eqJ]
  exact μ.normalised


theorem vitali (μ : naiveMeasure) (t : ENNReal): μ vitaliSet = t → False := by
  by_contra h
  by_cases h₀ : t = 0

  · have contra : ENNReal.ofReal 1 ≤ 0 := by
      calc
        ENNReal.ofReal 1 = μ I := by symm; apply μ.normalised
        _ ≤ μ vitaliUnion := by apply μ.monotony (superset μ)
        _ = tsum (fun r => if r ∈ shiftRange then μ (vitaliSet' r) else 0) := by exact sigma μ
        _ = tsum (fun r => if r ∈ shiftRange then μ vitaliSet else 0) := by sorry -- vitaliTranslations
        _ = tsum (fun r => if r ∈ shiftRange then 0 else 0) := by rw [h, h₀]
        _ = 0 := by simp
    have one_pos : ENNReal.ofReal 1 > 0 := by simp
    exact absurd contra (not_le_of_gt one_pos)

  have contra' : ENNReal.ofReal 3 ≥ ⊤ := by
      calc
        ENNReal.ofReal 3 = μ J := by symm; apply threeJ
        _ ≥ μ vitaliUnion := by apply μ.monotony (subset μ)
        _ = tsum (fun r => if r ∈ shiftRange then μ (vitaliSet' r) else 0) := by exact sigma μ
        _ = tsum (fun r => if r ∈ shiftRange then μ vitaliSet else 0) := by sorry -- vitaliTranslations
        _ = tsum (fun r => if r ∈ shiftRange then t else 0) := by exact tsum_congr fun b => congrFun (congrArg (ite (b ∈ shiftRange)) h) 0
        _ = t * tsum (fun r => if r ∈ shiftRange then 1 else 0) := by hint
        _ = t * ⊤ := by apply sorry -- an infinite sum of ones is infinite
        _ = ⊤ := by exact ENNReal.mul_top h₀
  have three_finite : ENNReal.ofReal 3 < ⊤ := by simp
  exact absurd contra' (not_le_of_gt three_finite)

end

#min_imports
