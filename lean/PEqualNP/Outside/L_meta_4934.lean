import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_4934

open PEqualNP.CircuitLowerBounds

lemma getD_out (a : List Bool) (r : ℕ) (h : a.length ≤ r) : a.getD r false = false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none h]

lemma getD_snoc (a : List Bool) (v : Bool) (r : ℕ) :
    (a ++ [v]).getD r false =
      if r < a.length then a.getD r false else if r = a.length then v else false := by
  rcases lt_trichotomy r a.length with h | h | h
  · simp [h, List.getD_eq_getElem?_getD, List.getElem?_append_left h]
  · subst h; simp [List.getD_eq_getElem?_getD]
  · have h1 : ¬ r < a.length := by omega
    have h2 : r ≠ a.length := by omega
    simp only [h1, h2, if_false]
    exact getD_out _ _ (by simp; omega)

def mp (σ : Fin 10 → Fin 10) (r : ℕ) : ℕ :=
  if h : r < 10 then ((σ ⟨r, h⟩ : Fin 10) : ℕ) else if r < 29 then r else 29

lemma mp_le (σ : Fin 10 → Fin 10) (r : ℕ) : mp σ r ≤ 29 := by
  unfold mp
  split_ifs with h1 h2
  · have := (σ ⟨r, h1⟩).isLt; omega
  · omega
  · exact le_refl _

def relabel (σ : Fin 10 → Fin 10) (C : Circuit) : Circuit :=
  ⟨C.gates.map (fun g => (⟨g.op, g.inputs.map (mp σ)⟩ : Gate)), mp σ C.output⟩

def Inv (σ : Fin 10 → Fin 10) (a b : List Bool) : Prop :=
  a.length = b.length ∧ 11 ≤ a.length ∧ a.length ≤ 29 ∧
    (∀ r, 10 ≤ r → a.getD r false = b.getD r false) ∧
    (∀ i : Fin 10, a.getD (σ i : ℕ) false = b.getD (i : ℕ) false)

lemma inv_mp (σ : Fin 10 → Fin 10) (a b : List Bool) (h : Inv σ a b) (r : ℕ) :
    a.getD (mp σ r) false = b.getD r false := by
  obtain ⟨hl, _, h29, hA, hB⟩ := h
  unfold mp
  split_ifs with h1 h2
  · exact hB ⟨r, h1⟩
  · exact hA r (by omega)
  · rw [getD_out a 29 h29, getD_out b r (by omega)]

lemma inv_step (σ : Fin 10 → Fin 10) (a b : List Bool) (h : Inv σ a b)
    (hlen : a.length + 1 ≤ 29) (g : Gate) :
    Inv σ (a ++ [g.op.eval ((g.inputs.map (mp σ)).map fun i => a.getD i false)])
      (b ++ [g.op.eval (g.inputs.map fun i => b.getD i false)]) := by
  have hv : ((g.inputs.map (mp σ)).map fun i => a.getD i false) =
      g.inputs.map fun i => b.getD i false := by
    rw [List.map_map]
    apply List.map_congr_left
    intro r _
    exact inv_mp σ a b h r
  rw [hv]
  obtain ⟨hl, h11, h29, hA, hB⟩ := h
  refine ⟨by simp [hl], by simp; omega, by simp; omega, ?_, ?_⟩
  · intro r hr
    rw [getD_snoc, getD_snoc, hl]
    split_ifs with h1 h2
    · exact hA r hr
    · rfl
    · rfl
  · intro i
    have hi1 : ((σ i : Fin 10) : ℕ) < a.length := by have := (σ i).isLt; omega
    have hi2 : ((i : Fin 10) : ℕ) < b.length := by have := i.isLt; omega
    rw [getD_snoc, getD_snoc, if_pos hi1, if_pos hi2]
    exact hB i

lemma inv_fold (σ : Fin 10 → Fin 10) : ∀ (gs : List Gate) (a b : List Bool), Inv σ a b →
    a.length + gs.length ≤ 29 →
    Inv σ ((gs.map (fun g => (⟨g.op, g.inputs.map (mp σ)⟩ : Gate))).foldl
        (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) a)
      (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) b)
  | [], a, b, h, _ => by simpa using h
  | g :: gs, a, b, h, hlen => by
    simp only [List.map_cons, List.foldl_cons]
    apply inv_fold σ gs
    · exact inv_step σ a b h (by simp at hlen; omega) g
    · simp at hlen ⊢; omega

lemma inv_init (σ : Fin 10 → Fin 10) (x : Fin 10 → Bool) (c : Bool) :
    Inv σ (List.ofFn x ++ [c]) (List.ofFn (x ∘ σ) ++ [c]) := by
  refine ⟨by simp, by simp, by simp, ?_, ?_⟩
  · intro r hr
    rw [getD_snoc, getD_snoc]
    simp only [List.length_ofFn]
    have : ¬ r < 10 := by omega
    simp only [this, if_false]
  · intro i
    have h1 : ((σ i : Fin 10) : ℕ) < (List.ofFn x).length := by simp
    have h2 : ((i : Fin 10) : ℕ) < (List.ofFn (x ∘ σ)).length := by simp
    rw [getD_snoc, getD_snoc, if_pos h1, if_pos h2, List.getD_eq_getElem _ _ h1,
      List.getD_eq_getElem _ _ h2, List.getElem_ofFn, List.getElem_ofFn]
    rfl

end PEqualNP.Outside.L_meta_4934

theorem PEqualNP.Outside.L_meta_4934 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : Fin (10 : ℕ) → Fin (10 : ℕ)), PEqualNP.MetaComplexity.FanInTwo x1 → x1.size ≤ (18 : ℕ) → ∃ (x5 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x5 ∧ x5.size = x1.size ∧ x5.output ≤ (29 : ℕ) ∧ (∀ x6 ∈ x5.gates, ∀ x8 ∈ x6.inputs, x8 ≤ (29 : ℕ)) ∧ ∀ (x6 : Fin (10 : ℕ) → Bool) (x7 : Bool), x5.eval (List.ofFn x6 ++ [x7]) = x1.eval (List.ofFn (x6 ∘ x2) ++ [x7]) := by
  intro C σ hF hs
  refine ⟨PEqualNP.Outside.L_meta_4934.relabel σ C, ?_, ?_, ?_, ?_, ?_⟩
  · intro g hg
    simp only [PEqualNP.Outside.L_meta_4934.relabel, List.mem_map] at hg
    obtain ⟨g0, hg0, rfl⟩ := hg
    obtain ⟨h1, h2⟩ := hF g0 hg0
    exact ⟨h1, by simpa using h2⟩
  · simp [PEqualNP.Outside.L_meta_4934.relabel, PEqualNP.CircuitLowerBounds.Circuit.size]
  · exact PEqualNP.Outside.L_meta_4934.mp_le σ C.output
  · intro g hg i hi
    simp only [PEqualNP.Outside.L_meta_4934.relabel, List.mem_map] at hg
    obtain ⟨g0, _, rfl⟩ := hg
    simp only [List.mem_map] at hi
    obtain ⟨r, _, rfl⟩ := hi
    exact PEqualNP.Outside.L_meta_4934.mp_le σ r
  · intro x c
    have hs' : C.gates.length ≤ 18 := hs
    have hinv := PEqualNP.Outside.L_meta_4934.inv_fold σ C.gates (List.ofFn x ++ [c])
      (List.ofFn (x ∘ σ) ++ [c]) (PEqualNP.Outside.L_meta_4934.inv_init σ x c) (by simp; omega)
    exact PEqualNP.Outside.L_meta_4934.inv_mp σ _ _ hinv C.output
