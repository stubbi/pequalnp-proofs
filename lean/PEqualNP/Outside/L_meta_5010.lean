import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_5010

open PEqualNP.CircuitLowerBounds

def E : List (Fin 9 × Fin 9) :=
  [((0 : Fin (9 : ℕ)), (1 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (2 : Fin (9 : ℕ))),
    ((2 : Fin (9 : ℕ)), (3 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (4 : Fin (9 : ℕ))),
    ((4 : Fin (9 : ℕ)), (0 : Fin (9 : ℕ))), ((0 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ))),
    ((1 : Fin (9 : ℕ)), (6 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))),
    ((3 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((5 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))),
    ((6 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((8 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ)))]

def fv (x : Fin 9 → Bool) : Bool := E.any fun p => x p.1 && x p.2

def L (k : ℕ) (x : Fin 9 → Bool) : List Bool :=
  (List.ofFn x ++ [x 0 || x 2]) ++ [!(List.ofFn x ++ [x 0 || x 2]).getD k false]

def ex (p : Fin 9 × Fin 9) : Fin 9 → Bool := fun i => decide (i = p.1) || decide (i = p.2)

lemma L_length (k : ℕ) (x : Fin 9 → Bool) : (L k x).length = 11 := by
  simp [L]

lemma getD_min (w : List Bool) (hw : w.length = 11) (a : ℕ) :
    w.getD a false = w.getD (min a 11) false := by
  rcases lt_or_ge a 11 with h | h
  · rw [min_eq_left h.le]
  · rw [min_eq_right h]
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none (show w.length ≤ a by omega),
      List.getElem?_eq_none (show w.length ≤ 11 by omega)]

lemma agree_fin : ∀ k : Fin 11, (k = 0 ∨ k = 3 ∨ k = 4) → ∀ a b : Fin 12, ∃ p ∈ E,
    (L k (fun _ => false)).getD a false = (L k (ex p)).getD a false ∧
    (L k (fun _ => false)).getD b false = (L k (ex p)).getD b false := by
  decide

lemma f_zero : fv (fun _ => false) = false := by decide

lemma f_edge : ∀ p ∈ E, fv (ex p) = true := by decide

lemma eval_form (C : Circuit) (hF : PEqualNP.MetaComplexity.FanInTwo C)
    (hlen : C.gates.length ≤ 1) : ∃ a b : ℕ, ∃ h : Bool → Bool → Bool,
      ∀ w : List Bool, w.length = 11 → C.eval w = h (w.getD a false) (w.getD b false) := by
  rcases hC : C.gates with _ | ⟨g, _ | ⟨g', gs⟩⟩
  · refine ⟨C.output, C.output, fun u _ => u, ?_⟩
    intro w _
    simp [Circuit.eval, Circuit.wires, hC]
  · have hg : g.inputs.length ≤ 2 := (hF g (by simp [hC])).2
    rcases lt_trichotomy C.output 11 with ho | ho | ho
    · refine ⟨C.output, C.output, fun u _ => u, ?_⟩
      intro w hw
      simp only [Circuit.eval, Circuit.wires, hC, List.foldl_cons, List.foldl_nil]
      simp [List.getD_eq_getElem?_getD, List.getElem?_append_left (show C.output < w.length by omega)]
    · rcases hi : g.inputs with _ | ⟨i, _ | ⟨j, _ | ⟨l, ls⟩⟩⟩
      · refine ⟨0, 0, fun _ _ => g.op.eval [], ?_⟩
        intro w hw
        simp only [Circuit.eval, Circuit.wires, hC, List.foldl_cons, List.foldl_nil, hi, ho]
        simp [List.getD_eq_getElem?_getD, hw]
      · refine ⟨i, i, fun u _ => g.op.eval [u], ?_⟩
        intro w hw
        simp only [Circuit.eval, Circuit.wires, hC, List.foldl_cons, List.foldl_nil, hi, ho]
        simp [List.getD_eq_getElem?_getD, hw]
      · refine ⟨i, j, fun u v => g.op.eval [u, v], ?_⟩
        intro w hw
        simp only [Circuit.eval, Circuit.wires, hC, List.foldl_cons, List.foldl_nil, hi, ho]
        simp [List.getD_eq_getElem?_getD, hw]
      · rw [hi] at hg; simp at hg
    · refine ⟨0, 0, fun _ _ => false, ?_⟩
      intro w hw
      simp only [Circuit.eval, Circuit.wires, hC, List.foldl_cons, List.foldl_nil]
      simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none (show (w ++ [_]).length ≤ C.output by simp; omega)]
  · rw [hC] at hlen; simp at hlen

end PEqualNP.Outside.L_meta_5010

theorem PEqualNP.Outside.L_meta_5010 : ∀ (x1 : Fin (11 : ℕ)),   x1 = (0 : Fin (11 : ℕ)) ∨ x1 = (3 : Fin (11 : ℕ)) ∨ x1 = (4 : Fin (11 : ℕ)) →     ∀ (x3 : PEqualNP.CircuitLowerBounds.Circuit),       PEqualNP.MetaComplexity.FanInTwo x3 →         x3.size ≤ (13 : ℕ) →           (¬∃ (x6 : PEqualNP.CircuitLowerBounds.Gate), x3.gates[(1 : ℕ)]? = Option.some x6) →             ∃ (x7 : Fin (9 : ℕ) → Bool),               have x8 : List Bool := List.ofFn x7 ++ [x7 (0 : Fin (9 : ℕ)) || x7 (2 : Fin (9 : ℕ))];               x3.eval (x8 ++ [!x8.getD (↑x1) Bool.false]) ≠ [((0 : Fin (9 : ℕ)), (1 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (2 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (3 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (4 : Fin (9 : ℕ))), ((4 : Fin (9 : ℕ)), (0 : Fin (9 : ℕ))), ((0 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (6 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((5 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((6 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((8 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ)))].any fun (x9 : Fin (9 : ℕ) × Fin (9 : ℕ)) => x7 x9.1 && x7 x9.2 := by
  intro k hk C hF _ hno
  have hlen : C.gates.length ≤ 1 := by
    by_contra h
    simp only [not_le] at h
    exact hno ⟨C.gates[1], List.getElem?_eq_getElem h⟩
  obtain ⟨a, b, h, hev⟩ := PEqualNP.Outside.L_meta_5010.eval_form C hF hlen
  have hk' : k = 0 ∨ k = 3 ∨ k = 4 := hk
  obtain ⟨p, hpE, ha, hb⟩ := PEqualNP.Outside.L_meta_5010.agree_fin k hk'
    ⟨min a 11, by omega⟩ ⟨min b 11, by omega⟩
  have l0 := PEqualNP.Outside.L_meta_5010.L_length k (fun _ => false)
  have l1 := PEqualNP.Outside.L_meta_5010.L_length k (PEqualNP.Outside.L_meta_5010.ex p)
  by_cases h0 : C.eval (PEqualNP.Outside.L_meta_5010.L k (fun _ => false)) =
      PEqualNP.Outside.L_meta_5010.fv (fun _ => false)
  · refine ⟨PEqualNP.Outside.L_meta_5010.ex p, ?_⟩
    show C.eval (PEqualNP.Outside.L_meta_5010.L k (PEqualNP.Outside.L_meta_5010.ex p)) ≠
      PEqualNP.Outside.L_meta_5010.fv (PEqualNP.Outside.L_meta_5010.ex p)
    rw [PEqualNP.Outside.L_meta_5010.f_edge p hpE, hev _ l1,
      PEqualNP.Outside.L_meta_5010.getD_min _ l1 a, PEqualNP.Outside.L_meta_5010.getD_min _ l1 b]
    rw [hev _ l0, PEqualNP.Outside.L_meta_5010.f_zero,
      PEqualNP.Outside.L_meta_5010.getD_min _ l0 a, PEqualNP.Outside.L_meta_5010.getD_min _ l0 b] at h0
    simp only at ha hb
    rw [← ha, ← hb, h0]
    decide
  · exact ⟨fun _ => false, h0⟩
