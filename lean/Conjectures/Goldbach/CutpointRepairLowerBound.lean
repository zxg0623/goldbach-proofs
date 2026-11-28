import Mathlib

namespace CutpointRepairBound

private def originals : List ℕ := [25787, 23073, 28121, 30291, 29519, 51747, 29183, 30693, 46539, 27299, 55077, 35117, 58401, 48851, 29673, 44813, 22041, 52193, 40623, 35561, 59667, 54623, 31341, 41939, 42603, 49467, 57963, 12377, 33269, 18117, 18191, 42833, 46341, 38403, 48893, 1821, 8307, 14831, 15039, 60269, 71799, 73059, 66447]
private def witnesses (g : Fin 2) : List ℕ := if g=0 then [5214, 9666, 13272, 13956, 17796, 18552, 21624, 26238, 36786, 38154, 41496, 43002, 50832, 51534, 58338, 63942, 69588, 114714, 116892, 132486, 168534, 191778, 208128, 326688] else [5674, 19948, 25792, 32062, 45142, 47488, 68692, 85624, 87268, 90202, 111334, 117676, 147508, 147886, 171424, 175936, 227788, 231196, 235174, 335428, 370522, 402064, 551056, 637246]
private def row (g : Fin 2) (i : Fin 24) : ℕ := (witnesses g).getD i.val 0
private def factors : List ℕ := [3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137, 139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193, 197, 199, 211, 223, 227, 229, 233, 239, 241, 251, 257, 263, 269, 271, 277, 281, 283, 307, 311, 313, 317, 347, 353, 359, 367, 379, 397, 401, 409, 419, 443, 457, 467, 479, 523, 541, 557, 673]
private def properFactor (q : ℕ) : Bool := factors.any (fun d => decide (1 < d ∧ d < q ∧ d ∣ q))
private def eligible (d t : ℕ) : Prop := (t+d)%5 ≠ 0 ∧ (t+d)%7 ≠ 0
private instance (d t : ℕ) : Decidable (eligible d t) := inferInstanceAs (Decidable (_ ∧ _))
private def side (g : Fin 2) : ℕ := if g=0 then 2 else 0

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem table : ∀ (g : Fin 2) (i : Fin 24),
    7 < row g i ∧ row g i < 2097152 ∧ row g i % 2=0 ∧ row g i % 3=g.val ∧
    originals.all (fun t => properFactor (t+row g i)) = true := by decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem capacities : ∀ (g : Fin 2) (j : Fin 105),
    j.val % 5≠0 → j.val % 7≠4 →
    ((Finset.univ : Finset (Fin 24)).filter (fun i => eligible (row g i) j.val)).card ≤ 15 := by decide +kernel

private theorem avoids (x p : ℕ) (hx : x.Prime) (hp : 1 < p) (lt : p<x) : x % p≠0 := by
  intro h
  rcases (Nat.dvd_prime hx).mp (Nat.dvd_of_mod_eq_zero h) with h | h <;> omega

private theorem total (S : Finset ℕ) (prime : ∀ t ∈ S, t ≤ 2712663 ∧ (10^316-t).Prime)
    (covered : ∀ k : ℕ, k < 1048576 → 2 ≤ ((originals.toFinset ∪ S).filter (fun t => (t+2*k).Prime)).card)
    (g : Fin 2) : 4 ≤ (S.filter (fun t => t % 3=side g)).card := by
  let X := S.filter fun t => t % 3=side g
  have cert (t : ℕ) (ht : t ∈ S) : t % 3≠1 ∧ t % 5≠0 ∧ t % 7≠4 := by
    obtain ⟨le,large⟩ := prime t ht
    change (10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000-t).Prime at large
    have h₃ := avoids _ 3 large (by decide) (by omega)
    have h₅ := avoids _ 5 large (by decide) (by omega)
    have h₇ := avoids _ 7 large (by decide) (by omega)
    omega
  have byRow (i : Fin 24) : 2 ≤ (X.filter (fun t => eligible (row g i) t)).card := by
    obtain ⟨large,cap,even,modThree,miss⟩ := table g i
    have h := covered (row g i/2) (by omega)
    rw [show 2*(row g i/2)=row g i by omega] at h
    refine h.trans (Finset.card_le_card ?_)
    intro t ht
    obtain ⟨union,p⟩ := Finset.mem_filter.mp ht
    have fresh : t ∈ S := by
      rcases Finset.mem_union.mp union with old | fresh
      · have composite := (List.all_eq_true.mp miss) t (List.mem_toFinset.mp old)
        obtain ⟨v,_,hv⟩ := List.any_eq_true.mp composite
        obtain ⟨lo,hi,div⟩ := of_decide_eq_true hv
        rcases (Nat.dvd_prime p).mp div with one | eq <;> omega
      · exact fresh
    obtain ⟨ht₃,_,_⟩ := cert t fresh
    have h₃ := avoids _ 3 p (by decide) (by omega)
    have h₅ := avoids _ 5 p (by decide) (by omega)
    have h₇ := avoids _ 7 p (by decide) (by omega)
    have same : t % 3=side g := by
      by_cases h0 : g=0
      · rw [side,if_pos h0]
        have hg : g.val=0 := by simp [h0]
        omega
      · rw [side,if_neg h0]
        have hg : g.val≠0 := by simpa using h0
        have hsmall := g.isLt
        omega
    exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨fresh,same⟩,h₅,h₇⟩
  have byCol (t : ℕ) (ht : t ∈ X) : ((Finset.univ : Finset (Fin 24)).filter (fun i => eligible (row g i) t)).card ≤ 15 := by
    obtain ⟨_,h5,h7⟩ := cert t (Finset.mem_filter.mp ht).1
    let j : Fin 105 := ⟨t % 105,Nat.mod_lt _ (by decide)⟩
    have le := capacities g j (by dsimp [j]; omega) (by dsimp [j]; omega)
    have eq : ((Finset.univ : Finset (Fin 24)).filter (fun i => eligible (row g i) t)) =
        (Finset.univ.filter (fun i => eligible (row g i) j.val)) := by
      apply Finset.filter_congr
      intro i _
      unfold eligible
      dsimp [j]
      omega
    rw [eq]
    exact le
  have count : 48 ≤ 15*X.card := calc
    48 = ∑ _i : Fin 24, (2:ℕ) := by simp
    _ ≤ ∑ i : Fin 24, (X.filter (fun t => eligible (row g i) t)).card := Finset.sum_le_sum (fun i _ => byRow i)
    _ = ∑ t ∈ X, ((Finset.univ : Finset (Fin 24)).filter (fun i => eligible (row g i) t)).card := by
      simp only [Finset.card_filter]
      rw [Finset.sum_comm]
    _ ≤ ∑ _t ∈ X, 15 := Finset.sum_le_sum byCol
    _ = 15*X.card := by simp [Nat.mul_comm]
  change 4 ≤ X.card
  omega

theorem result : ∀ S : Finset ℕ, (∀ t ∈ S, t ≤ 2712663 ∧ (10^316-t).Prime) → (∀ k : ℕ, k < 1048576 → 2 ≤ ((([25787, 23073, 28121, 30291, 29519, 51747, 29183, 30693, 46539, 27299, 55077, 35117, 58401, 48851, 29673, 44813, 22041, 52193, 40623, 35561, 59667, 54623, 31341, 41939, 42603, 49467, 57963, 12377, 33269, 18117, 18191, 42833, 46341, 38403, 48893, 1821, 8307, 14831, 15039, 60269, 71799, 73059, 66447] : List ℕ).toFinset ∪ S).filter (fun t => (t+2*k).Prime)).card) → 8 ≤ S.card := by
  intro S prime cover
  have a := total S prime cover 0
  have b := total S prime cover 1
  let X := S.filter (fun t => t % 3=2)
  let Y := S.filter (fun t => t % 3=0)
  change 4 ≤ X.card at a
  change 4 ≤ Y.card at b
  have dis : Disjoint X Y := by
    apply Finset.disjoint_left.mpr
    intro t hx hy
    have := (Finset.mem_filter.mp hx).2
    have := (Finset.mem_filter.mp hy).2
    omega
  have sub : X ∪ Y ⊆ S := Finset.union_subset (Finset.filter_subset _ _) (Finset.filter_subset _ _)
  have h := Finset.card_le_card sub
  rw [Finset.card_union_of_disjoint dis] at h
  omega

end CutpointRepairBound

theorem Conjectures.Goldbach.CutpointRepairLowerBound : ∀ S : Finset ℕ, (∀ t ∈ S, t ≤ 2712663 ∧ (10^316-t).Prime) → (∀ k : ℕ, k < 1048576 → 2 ≤ ((([25787, 23073, 28121, 30291, 29519, 51747, 29183, 30693, 46539, 27299, 55077, 35117, 58401, 48851, 29673, 44813, 22041, 52193, 40623, 35561, 59667, 54623, 31341, 41939, 42603, 49467, 57963, 12377, 33269, 18117, 18191, 42833, 46341, 38403, 48893, 1821, 8307, 14831, 15039, 60269, 71799, 73059, 66447] : List ℕ).toFinset ∪ S).filter (fun t => (t+2*k).Prime)).card) → 8 ≤ S.card := CutpointRepairBound.result
