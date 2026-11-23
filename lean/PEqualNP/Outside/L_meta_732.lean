import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_732_aux

def eL : List (ℕ × ℕ) := [(0, 1), (0, 3), (0, 4), (0, 5), (0, 6), (1, 3), (1, 4), (1, 6), (2, 4),
  (2, 6), (2, 7), (3, 4), (3, 5), (3, 7), (4, 5), (4, 6), (4, 7), (5, 7)]

def dL : List (ℕ × ℕ) := [(0, 3), (0, 4), (1, 0), (1, 6), (2, 4), (2, 6), (3, 1), (3, 5), (3, 7),
  (4, 1), (4, 3), (5, 0), (5, 4), (5, 7), (6, 0), (6, 4), (7, 2), (7, 4)]

def eB (u v : Fin 8) : Bool := decide ((u.val, v.val) ∈ eL ∨ (v.val, u.val) ∈ eL)

def dB (u v : Fin 8) : Bool := decide ((u.val, v.val) ∈ dL)

def mis (j : Fin 9) : List (Fin 8) :=
  ![[4], [0, 2], [0, 7], [1, 7], [2, 3], [3, 6], [5, 6], [6, 7], [1, 2, 5]] j

def wa (j : Fin 9) : Fin 8 := ![1, 3, 2, 0, 1, 5, 0, 0, 0] j

def wb (j : Fin 9) : Fin 8 := ![3, 4, 4, 6, 6, 7, 4, 4, 6] j

def bv (b0 b1 b2 b3 b4 b5 b6 b7 : Bool) : Fin 8 → Bool := ![b0, b1, b2, b3, b4, b5, b6, b7]

theorem s1 : ∀ j : Fin 9, eB (wa j) (wb j) = true ∧ wa j ∉ mis j ∧ wb j ∉ mis j ∧
    ∀ k ∈ mis j, dB (wa j) k = false ∧ dB (wb j) k = false := by
  decide

theorem cover8 : ∀ b0 b1 b2 b3 b4 b5 b6 b7 : Bool,
    (∀ u v : Fin 8, bv b0 b1 b2 b3 b4 b5 b6 b7 u = true → bv b0 b1 b2 b3 b4 b5 b6 b7 v = true →
      eB u v = false) →
    ∃ j : Fin 9, ∀ i : Fin 8, bv b0 b1 b2 b3 b4 b5 b6 b7 i = true → i ∈ mis j := by
  decide

theorem orient : ∀ u v : Fin 8, (eB u v = true ↔ (dB u v = true ∨ dB v u = true)) ∧
    (dB u v = true → ¬ dB v u = true) := by
  decide

end PEqualNP.Outside.L_meta_732_aux

open PEqualNP.Outside.L_meta_732_aux in
theorem PEqualNP.Outside.L_meta_732 :
    ∀ (E D : Fin 8 → Fin 8 → Prop),
  (∀ u v, E u v ↔ ((u.val, v.val) ∈ [(0, 1), (0, 3), (0, 4), (0, 5), (0, 6), (1, 3), (1, 4), (1, 6), (2, 4),
      (2, 6), (2, 7), (3, 4), (3, 5), (3, 7), (4, 5), (4, 6), (4, 7), (5, 7)] ∨
    (v.val, u.val) ∈ [(0, 1), (0, 3), (0, 4), (0, 5), (0, 6), (1, 3), (1, 4), (1, 6), (2, 4),
      (2, 6), (2, 7), (3, 4), (3, 5), (3, 7), (4, 5), (4, 6), (4, 7), (5, 7)])) →
  (∀ u v, D u v ↔ (u.val, v.val) ∈ [(0, 3), (0, 4), (1, 0), (1, 6), (2, 4), (2, 6), (3, 1), (3, 5), (3, 7),
      (4, 1), (4, 3), (5, 0), (5, 4), (5, 7), (6, 0), (6, 4), (7, 2), (7, 4)]) →
  (∀ u v, E u v ↔ (D u v ∨ D v u)) ∧ (∀ u v, D u v → ¬ D v u) ∧
  ∀ W K : Set (Fin 8),
    (∀ u ∈ W, ∀ v ∈ W, ¬ E u v) → Disjoint K W → (∀ u ∈ K, ∀ v ∈ K, ¬ E u v) →
    ∃ v, v ∉ W ∧ v ∉ K ∧ ∀ k ∈ K, ¬ D v k := by
  intro E D hE hD
  have hE' : ∀ u v, E u v ↔ eB u v = true := by
    intro u v
    rw [hE u v, eB, decide_eq_true_iff]
    exact Iff.rfl
  have hD' : ∀ u v, D u v ↔ dB u v = true := by
    intro u v
    rw [hD u v, dB, decide_eq_true_iff]
    exact Iff.rfl
  refine ⟨?_, ?_, ?_⟩
  · intro u v
    rw [hE', hD', hD']
    exact (orient u v).1
  · intro u v
    rw [hD', hD']
    exact (orient u v).2
  · intro W K hW _ hK
    classical
    let b : Fin 8 → Bool := fun i => decide (i ∈ K)
    have hb : ∀ i, b i = true ↔ i ∈ K := fun i => by simp [b]
    have hbv : ∀ i, bv (b 0) (b 1) (b 2) (b 3) (b 4) (b 5) (b 6) (b 7) i = b i := by
      intro i
      fin_cases i <;> rfl
    have hind : ∀ u v : Fin 8, bv (b 0) (b 1) (b 2) (b 3) (b 4) (b 5) (b 6) (b 7) u = true →
        bv (b 0) (b 1) (b 2) (b 3) (b 4) (b 5) (b 6) (b 7) v = true → eB u v = false := by
      intro u v hu hv
      rw [hbv, hb] at hu hv
      have h := hK u hu v hv
      rw [hE'] at h
      simpa using h
    obtain ⟨j, hj⟩ := cover8 _ _ _ _ _ _ _ _ hind
    have hsub : ∀ k ∈ K, k ∈ mis j := fun k hk => hj k (by rw [hbv, hb]; exact hk)
    obtain ⟨he, ha, hbb, hd⟩ := s1 j
    by_cases haW : wa j ∈ W
    · refine ⟨wb j, ?_, ?_, ?_⟩
      · intro hbW
        exact hW _ haW _ hbW ((hE' _ _).2 he)
      · intro hbK
        exact hbb (hsub _ hbK)
      · intro k hk hdk
        rw [hD'] at hdk
        have h2 := (hd k (hsub k hk)).2
        rw [h2] at hdk
        exact Bool.false_ne_true hdk
    · refine ⟨wa j, haW, ?_, ?_⟩
      · intro haK
        exact ha (hsub _ haK)
      · intro k hk hdk
        rw [hD'] at hdk
        have h1 := (hd k (hsub k hk)).1
        rw [h1] at hdk
        exact Bool.false_ne_true hdk
