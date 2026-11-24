import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_3362 : ∀ (x1 x2 x3 : ℕ) (x4 : Fin x1 → Fin x1 → Prop) [x5 : DecidableRel x4], (∀ (x6 : Fin x1), Fintype.card { x7 : Fin x1 // x4 x7 x6 } = x2) → (∀ (x7 x8 : Fin x1), x7 ≠ x8 → ∃! x10 : Fin x1, x4 x7 x10 ∧ x4 x8 x10) → ∀ (x8 x9 : Fin x3 → Finset (Fin x1)), (∀ (x10 : Fin x3), ∀ x11 ∈ x8 x10, ∀ x13 ∈ x9 x10, x4 x11 x13) → (∀ (x11 x12 : Fin x1), x4 x11 x12 → ∃ (x14 : Fin x3), x11 ∈ x8 x14 ∧ x12 ∈ x9 x14) → x1 * x2 ≤ ∑ x12 : Fin x3, ((x8 x12).card + (x9 x12).card) := by
  intro N k m I _ hk hu A B hrect hcov
  have star : ∀ i, (A i).card * (B i).card ≤ (A i).card + (B i).card := by
    intro i
    by_cases hA : (A i).card ≤ 1
    · rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hA with h | h
      · simp [h]
      · rw [h]; omega
    · by_cases hB : (B i).card ≤ 1
      · rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hB with h | h
        · simp [h]
        · rw [h]; omega
      · exfalso
        simp only [not_le] at hA hB
        obtain ⟨p, hp, p', hp', hpp'⟩ := Finset.one_lt_card.mp hA
        obtain ⟨l, hl, l', hl', hll'⟩ := Finset.one_lt_card.mp hB
        obtain ⟨c, _, huniq⟩ := hu p p' hpp'
        have e1 := huniq l ⟨hrect i p hp l hl, hrect i p' hp' l hl⟩
        have e2 := huniq l' ⟨hrect i p hp l' hl', hrect i p' hp' l' hl'⟩
        exact hll' (e1.trans e2.symm)
  have hline : ∀ l : Fin N, (∑ p : Fin N, if I p l then 1 else 0) = k := by
    intro l
    rw [← Finset.card_filter, ← hk l, Fintype.card_subtype]
  have hS : ((Finset.univ : Finset (Fin N × Fin N)).filter (fun q => I q.1 q.2)).card = N * k := by
    rw [Finset.card_filter, Fintype.sum_prod_type_right]
    simp only [hline, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  have hsub : (Finset.univ : Finset (Fin N × Fin N)).filter (fun q => I q.1 q.2) ⊆
      Finset.univ.biUnion (fun i => A i ×ˢ B i) := by
    intro q hq
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hq
    obtain ⟨i, h1, h2⟩ := hcov q.1 q.2 hq
    simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_product]
    exact ⟨i, h1, h2⟩
  calc N * k = ((Finset.univ : Finset (Fin N × Fin N)).filter (fun q => I q.1 q.2)).card := hS.symm
    _ ≤ (Finset.univ.biUnion (fun i => A i ×ˢ B i)).card := Finset.card_le_card hsub
    _ ≤ ∑ i, (A i ×ˢ B i).card := Finset.card_biUnion_le
    _ = ∑ i, (A i).card * (B i).card := by simp only [Finset.card_product]
    _ ≤ ∑ i, ((A i).card + (B i).card) := Finset.sum_le_sum (fun i _ => star i)
