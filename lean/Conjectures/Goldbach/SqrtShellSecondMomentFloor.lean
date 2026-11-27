import Conjectures.Goldbach.SqrtArcSecondMomentFloor

/-!
Squarefree denominators between the cube-root and five-twelfths powers give a
logarithmic sum of reciprocals. Their reduced-fraction windows stay outside
the cube-root arcs while lying inside the square-root arcs. Integrating the
prime energy on those disjoint windows localizes the lower bound to the shell.
The disjoint-window argument adapts the square-root exterior proof in PR 3727.
-/

namespace Conjectures.Goldbach.SqrtShellSecondMomentFloor

open Finset Filter
open scoped BigOperators Topology
open Conjectures.Goldbach.SqrtArcSecondMomentFloor.GoldbachCount

/-- Reciprocal mass on squarefree denominators between the cube and intermediate cutoffs. -/
theorem denominatorMass :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ n : ℕ in atTop,
      c * Real.log n ≤
        ∑ q ∈ (Ioc ⌊(n : ℝ) ^ (1/3 : ℝ)⌋₊ ⌊(n : ℝ)^(5/12 : ℝ)⌋₊).filter Squarefree,
          1 / (q : ℝ) := by
  classical
  have h8 : 0 < Real.log 8 := Real.log_pos (by norm_num)
  refine ⟨1/(384*Real.log 8), by positivity, ?_⟩
  filter_upwards [eventually_ge_atTop (8^48 : ℕ)] with n hn
  have h1n : (1:ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  have hnp : (0:ℝ) < n := by linarith
  have hlg : 48 * Real.log 8 ≤ Real.log n := by
    have hn' : (8:ℝ)^48 ≤ n := by exact_mod_cast hn
    simpa [Real.log_pow] using Real.log_le_log (by positivity) hn'
  let y := Real.log n / (24 * Real.log 8)
  let J := ⌊y⌋₊
  let D := ⌊(n:ℝ)^(1/3:ℝ)⌋₊
  have hy : 2 ≤ y := by
    dsimp [y]
    apply (le_div_iff₀ (by positivity)).2
    linarith
  have hjlo : y/2 ≤ (J:ℝ) := by
    have := Nat.lt_floor_add_one y
    dsimp [J]
    linarith
  have hjhi : (J:ℝ)*Real.log 8 ≤ Real.log n / 24 := by
    have h := Nat.floor_le (show 0 ≤ y by linarith)
    change (J:ℝ) ≤ Real.log n/(24*Real.log 8) at h
    have := (le_div_iff₀ (by positivity : 0 < 24*Real.log 8)).1 h
    linarith
  have hJpow : (8:ℝ)^J ≤ (n:ℝ)^(1/24:ℝ) := by
    rw [← Real.rpow_natCast, Real.rpow_def_of_pos (by norm_num : (0:ℝ)<8),
      Real.rpow_def_of_pos hnp, Real.exp_le_exp]
    linarith
  have hd : 0 < D := Nat.floor_pos.mpr (Real.one_le_rpow h1n (by norm_num))
  have hfit : 8^J*D ≤ ⌊(n : ℝ)^(5/12 : ℝ)⌋₊ := by
    apply Nat.le_floor
    push_cast
    calc
      (8:ℝ) ^ J * (D:ℝ) ≤ (n:ℝ)^(1/24:ℝ) * (n:ℝ)^(1/3:ℝ) := by
        gcongr
        exact Nat.floor_le (by positivity : 0 ≤ (n:ℝ) ^ (1/3:ℝ))
      _ ≤ (n:ℝ)^(5/12:ℝ) := by
        rw [← Real.rpow_add hnp]
        exact Real.rpow_le_rpow_of_exponent_le h1n (by norm_num)
  have he : (1/(384*Real.log 8)) * Real.log n ≤ (J:ℝ)/8 := by
    calc
      _ = y/2/8 := by dsimp [y]; ring
      _ ≤ _ := by linarith
  refine (he.trans (mass_blocks D J hd)).trans ?_
  apply sum_le_sum_of_subset_of_nonneg
  · exact filter_subset_filter _ (Ioc_subset_Ioc le_rfl hfit)
  · intro q _ _
    positivity


/-- Intermediate denominators eventually lie below both cutoffs needed for the windows. -/
theorem denominatorLimits : ∀ᶠ n : ℕ in atTop,
    ⌊(n:ℝ)^(5/12:ℝ)⌋₊ ≤ sqrtCutoff n ∧
    ⌊(n:ℝ)^(5/12:ℝ)⌋₊ ≤ ⌊Real.sqrt n / 4⌋₊ := by
  have bound := ((isLittleO_log_rpow_atTop (show (0:ℝ) < 1/48 by norm_num)).comp_tendsto
    (tendsto_natCast_atTop_atTop (R := ℝ))).bound (show (0:ℝ) < 1/4 by norm_num)
  filter_upwards [eventually_ge_atTop (4^12 : ℕ), bound] with n hn hb
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast (show 2 ≤ n by omega)
  have hp : (0:ℝ) < n := by linarith
  have hlog : Real.log n ≤ (1/4:ℝ)*(n:ℝ)^(1/48:ℝ) := by
    simpa [Function.comp_def, Real.norm_eq_abs, abs_of_nonneg (Real.log_natCast_nonneg n),
      abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) _)] using hb
  have he := Real.natLog_le_logb (n+2) 2
  have htwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hhalf : (1:ℝ)/2 ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hsum : Real.log ((n:ℝ)+2) ≤ 2 * Real.log n := by
    calc
      _ ≤ Real.log ((n:ℝ)^2) :=
        Real.log_le_log (by positivity) (by nlinarith [sq_nonneg ((n:ℝ)-2)])
      _ = _ := by simp [Real.log_pow]
  have hell : (Nat.log 2 (n+2) : ℝ) ≤ (n:ℝ) ^ (1/48 : ℝ) := by
    simp only [Real.logb, Nat.cast_add, Nat.cast_ofNat] at he
    have hh := (le_div_iff₀ htwo).mp he
    have hp' := mul_le_mul_of_nonneg_left hhalf (Nat.cast_nonneg (Nat.log 2 (n+2)) : 0 ≤ (_:ℝ))
    linarith
  have hlpos : 0 < Nat.log 2 (n+2) := Nat.log_pos (by decide) (by omega)
  have h4 : (4:ℝ) ≤ (n:ℝ)^(1/12:ℝ) := by
    calc
      (4:ℝ) = ((4:ℝ)^12)^(1/12:ℝ) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
        norm_num
      _ ≤ _ := Real.rpow_le_rpow (by positivity) (by exact_mod_cast hn) (by norm_num)
  constructor
  · apply Nat.floor_le_floor
    apply (le_div_iff₀ (by positivity)).2
    calc
      _ ≤ (n:ℝ)^(5/12:ℝ)*((n:ℝ)^(1/48:ℝ))^4 := by gcongr
      _ = Real.sqrt n := by
        rw [← Real.rpow_mul_natCast hp.le, ← Real.rpow_add hp, Real.sqrt_eq_rpow]
        norm_num
  · apply Nat.floor_le_floor
    apply (le_div_iff₀ (by norm_num : (0:ℝ)<4)).2
    calc
      _ ≤ (n:ℝ)^(5/12:ℝ)*(n:ℝ)^(1/12:ℝ) := by gcongr
      _ = Real.sqrt n := by rw [← Real.rpow_add hp, Real.sqrt_eq_rpow]; norm_num

end Conjectures.Goldbach.SqrtShellSecondMomentFloor

open Conjectures.Goldbach.SqrtArcSecondMomentFloor
open Conjectures.Goldbach.SqrtArcSecondMomentFloor.GoldbachSupport
open MeasureTheory Set Filter
open scoped BigOperators Interval Topology

namespace Conjectures.Goldbach.SqrtShellSecondMomentFloor

private theorem reduced_centers_unique {q r a b : ℕ} (hq : 0 < q)
    (ha : Nat.Coprime a q) (hb : Nat.Coprime b r) (he : a * r = b * q) :
    q = r ∧ a = b := by
  have hdq : q ∣ a * r := he ▸ Nat.dvd_mul_left q b
  have hdr : r ∣ b * q := he.symm ▸ Nat.dvd_mul_left r a
  have hqr := Nat.dvd_antisymm (ha.symm.dvd_of_dvd_mul_left hdq) (hb.symm.dvd_of_dvd_mul_left hdr)
  subst r
  exact ⟨rfl, Nat.eq_of_mul_eq_mul_right hq he⟩

/-- Sum the disjoint shifted intervals at reduced fractions and keep only their
contribution to the integral over the newly included square-root arc band. -/
theorem assembleShellWindows (s : Finset ℕ) (D H D₂ H₂ n : ℕ) (S : ℝ → ℂ) (hS : Continuous S)
    (hn : 0 < n)
    (hden : ∀ q ∈ s, D < q)
    (houter : ∀ q ∈ s, q ≤ D₂ ∧ q ≤ H₂)
    (hend : ∀ q ∈ s, (q : ℝ) ≤ 6 * n)
    (hmask : ∀ q ∈ s, (q : ℝ) * H + (q : ℝ) * D / 6 < n)
    (hpair : ∀ q ∈ s, ∀ r ∈ s, (q : ℝ) * r < 6 * n)
    (hamp : ∀ q ∈ s, ∀ h ∈ Icc (0 : ℝ) (1 / (6 * n)),
      (n : ℝ) / 8 ≤ ‖∑ a ∈ (Finset.range q).filter (fun a => Nat.Coprime a q),
          S ((a : ℝ) / q + h)‖) :
    ∑ q ∈ s, (n : ℝ) / (384 * (q : ℝ)) ≤
      ∫ t in (0 : ℝ)..1, (publishedWideArcs D₂ H₂ n \ publishedWideArcs D H n).indicator (fun x => ‖S x‖ ^ 2) t := by
  classical
  let A := fun q : ℕ => (Finset.range q).filter (fun a => Nat.Coprime a q)
  let indices := s.sigma A
  let w : ℝ := 1 / (6 * (n : ℝ))
  let f : ℝ → ℝ := fun t => ‖S t‖ ^ 2
  let c : (Σ _ : ℕ, ℕ) → ℝ := fun i => (i.2 : ℝ) / i.1
  let W := fun i => Ioc (c i) (c i + w)
  let target := Ioc (0 : ℝ) 1 ∩ (publishedWideArcs D₂ H₂ n \ publishedWideArcs D H n)
  have hn' : 0 < (n : ℝ) := by exact_mod_cast hn
  have hw : 0 ≤ w := by dsimp [w]; positivity
  have hc : Continuous f := hS.norm.pow 2
  have hindex {i : Σ _ : ℕ, ℕ} (hi : i ∈ indices) :
      i.1 ∈ s ∧ i.2 < i.1 ∧ Nat.Coprime i.2 i.1 := by
    simpa [indices, A] using hi
  have hqpos {q : ℕ} (hq : q ∈ s) : 0 < q := Nat.zero_lt_of_lt (hden q hq)
  have hge {q : ℕ} (hq : q ∈ s) : 0 < (q : ℝ) := by exact_mod_cast hqpos hq
  have hsubset {i : Σ _ : ℕ, ℕ} (hi : i ∈ indices) : W i ⊆ target := by
    rcases hindex hi with ⟨hq, ha, hcop⟩
    intro t ht
    change c i < t ∧ t ≤ c i + w at ht
    have hfirst : 0 ≤ c i := by dsimp [c]; positivity
    have hq := hge hq
    have ha1 : (i.2 : ℝ) + 1 ≤ i.1 := by exact_mod_cast ha
    have hsmall : w ≤ 1 / (i.1 : ℝ) := one_div_le_one_div_of_le hq (hend _ (hindex hi).1)
    have hlast : t ≤ 1 := calc
      t ≤ (i.2 : ℝ) / i.1 + 1 / i.1 := by change t ≤ c i + 1 / i.1; linarith only [ht.2, hsmall]
      _ = ((i.2 : ℝ) + 1) / i.1 := by ring
      _ ≤ 1 := (div_le_one hq).2 ha1
    refine ⟨⟨hfirst.trans_lt ht.1, hlast⟩, ?_, ?_⟩
    · refine ⟨i.1, i.2, hqpos (hindex hi).1, (houter _ (hindex hi).1).1, ha.le, hcop, ?_⟩
      change |t - c i| ≤ (H₂ : ℝ) / ((i.1 : ℝ) * n)
      rw [abs_of_nonneg (sub_nonneg.mpr ht.1.le)]
      apply (show t - c i ≤ w by linarith only [ht.2]).trans
      dsimp [w]
      apply (div_le_div_iff₀ (by positivity : (0 : ℝ) < 6*n) (mul_pos hq hn')).2
      have hz : (i.1 : ℝ) ≤ H₂ := by exact_mod_cast (houter _ (hindex hi).1).2
      nlinarith only [mul_le_mul_of_nonneg_right hz hn'.le,
        mul_nonneg (Nat.cast_nonneg H₂ : (0 : ℝ) ≤ H₂) hn'.le]
    · have hout := outsideWideArcs i.2 i.1 D H n (t - c i) hcop
        (hden _ (hindex hi).1) hn (sub_nonneg.mpr ht.1.le)
        (by change t - c i ≤ w; linarith only [ht.2]) (hmask _ (hindex hi).1)
      change t ∉ publishedWideArcs D H n
      change c i + (t - c i) ∉ publishedWideArcs D H n at hout
      rwa [add_sub_cancel] at hout
  have hdisj : Set.Pairwise (↑indices) (fun i j => Disjoint (W i) (W j)) := by
    intro i hi j hj hne
    rcases hindex hi with ⟨hqi, hai, hci⟩
    rcases hindex hj with ⟨hqj, haj, hcj⟩
    have hcross : i.2 * j.1 ≠ j.2 * i.1 := by
      intro he
      obtain ⟨h₁,h₂⟩ := reduced_centers_unique (hqpos hqi) hci hcj he
      apply hne
      cases i
      cases j
      simp_all
    apply Set.disjoint_left.mpr
    intro t ht hu
    change c i < t ∧ t ≤ c i + w at ht
    change c j < t ∧ t ≤ c j + w at hu
    have h := deepArcWindowsDisjoint i.2 j.2 i.1 j.1 n (t - c i) (t - c j)
      (hge hqi) (hge hqj) hn' hcross (hpair _ hqi _ hqj)
      (sub_nonneg.mpr ht.1.le) (by change t - c i ≤ w; linarith only [ht.2])
      (sub_nonneg.mpr hu.1.le) (by change t - c j ≤ w; linarith only [hu.2])
    apply h
    change c i + (t - c i) = c j + (t - c j)
    abel
  have hint {a b : ℝ} : IntegrableOn f (Ioc a b) volume := by
    exact (hc.integrableOn_Icc (a := a) (b := b)).mono_set Ioc_subset_Icc_self
  have htarget : IntegrableOn f target volume := hint.mono_set (Set.inter_subset_left ..)
  have hshift (i : Σ _ : ℕ, ℕ) : (∫ h in (0 : ℝ)..w, f (c i + h)) = ∫ x in W i, f x := by
    rw [intervalIntegral.integral_comp_add_left, add_zero, intervalIntegral.integral_of_le]
    exact le_add_of_nonneg_right hw
  calc
    ∑ q ∈ s, (n : ℝ) / (384 * (q : ℝ)) ≤
        ∑ q ∈ s, ∑ a ∈ A q, ∫ h in (0 : ℝ)..w, f ((a : ℝ) / q + h) := by
      apply Finset.sum_le_sum
      intro q hq
      have hcard : (A q).card ≤ q :=
        (Finset.card_filter_le ..).trans_eq (Finset.card_range q)
      exact residueWindowEnergy (A q) (fun a h => S ((a : ℝ) / q + h))
        hn' (hqpos hq) hcard (fun a _ => hS.comp (continuous_const.add continuous_id)) (hamp q hq)
    _ = ∑ i ∈ indices, ∫ h in (0 : ℝ)..w, f (c i + h) :=
      Finset.sum_sigma' s A _
    _ = ∑ i ∈ indices, ∫ x in W i, f x := Finset.sum_congr rfl fun i _ => hshift i
    _ = ∫ x in ⋃ i ∈ indices, W i, f x :=
      (integral_biUnion_finset indices (fun _ _ => measurableSet_Ioc) hdisj (fun _ _ => hint)).symm
    _ ≤ ∫ x in target, f x := by
      apply setIntegral_mono_set htarget (Filter.Eventually.of_forall fun x => sq_nonneg ‖S x‖)
      exact Filter.Eventually.of_forall fun _ hx => by
        rcases Set.mem_iUnion₂.mp hx with ⟨i,hi,ht⟩
        exact hsubset hi ht
    _ = ∫ t in (0 : ℝ)..1, (publishedWideArcs D₂ H₂ n \ publishedWideArcs D H n).indicator (fun x => ‖S x‖ ^ 2) t := by
      rw [intervalIntegral.integral_of_le (by norm_num), setIntegral_indicator ((measurable_publishedWideArcs ..).diff (measurable_publishedWideArcs ..))]


end Conjectures.Goldbach.SqrtShellSecondMomentFloor

open Conjectures.Goldbach.SqrtShellSecondMomentFloor in
/-- The square-root arc shell carries a second moment of order at least `n * log n`. -/
theorem Conjectures.Goldbach.SqrtShellSecondMomentFloor :
    let w := fun k : ℕ => if Nat.Prime k then Real.log (k:ℝ) else 0; let E := fun x : ℝ => Complex.exp (((2*Real.pi*x:ℝ):ℂ)*Complex.I); let S := fun (n : ℕ) (u : ℕ → ℝ) (t : ℝ) => Finset.sum (Finset.range (n+1)) (fun k => (u k:ℂ)*E ((k:ℝ)*t)); let Q := fun n : ℕ => (Nat.log 2 (n+2))^2; let Q₁ := fun n : ℕ => ⌊(n:ℝ)^(1/3:ℝ)⌋₊; let H := fun n : ℕ => 256 * Q₁ n * Q n; let wideArcs := fun n : ℕ => {t : ℝ | ∃ q a : ℕ, 1≤q ∧ q≤Q₁ n ∧ a≤q ∧ Nat.Coprime a q ∧ |t-(a:ℝ)/(q:ℝ)| ≤ (H n:ℝ)/((q:ℝ)*(n:ℝ))}; let Q₂ := fun n : ℕ => ⌊Real.sqrt (n : ℝ) / ((Nat.log 2 (n + 2) : ℝ) ^ 4)⌋₊; let sqrtArcs := fun n : ℕ => {t : ℝ | ∃ q a : ℕ, 1 ≤ q ∧ q ≤ Q₂ n ∧ a ≤ q ∧ Nat.Coprime a q ∧ |t - (a : ℝ) / (q : ℝ)| ≤ ((256 * Q₂ n * Q n : ℕ) : ℝ) / ((q : ℝ) * (n : ℝ))}; ∃ c : ℝ, 0 < c ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n → c * (n : ℝ) * Real.log (n : ℝ) ≤ intervalIntegral (fun t => (sqrtArcs n \ wideArcs n).indicator (fun u => ‖S n w u‖ ^ 2) t) (0 : ℝ) 1 MeasureTheory.volume := by
  classical
  let D (n : ℕ) := ⌊(n : ℝ) ^ (1/3 : ℝ)⌋₊
  let L (n : ℕ) := ⌊(n : ℝ) ^ (5/12 : ℝ)⌋₊
  let Q (n : ℕ) := (Nat.log 2 (n+2))^2
  let H (n : ℕ) := 256 * D n * Q n
  let D₂ := GoldbachCount.sqrtCutoff
  let H₂ (n : ℕ) := 256 * D₂ n * Q n
  obtain ⟨d, hd, hm⟩ := denominatorMass
  refine ⟨d/384, by positivity, Filter.eventually_atTop.1 ?_⟩
  filter_upwards [hm, denominatorLimits, primeAmplitudeBounds, GoldbachCount.sqrtMaskScales] with
    n hmass ⟨hLouter, hLsmall⟩ ⟨hn, hθ, hql⟩ ⟨hD₂, hH₂⟩
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  have hDL : D n ≤ L n := Nat.floor_mono
    (Real.rpow_le_rpow_of_exponent_le hn1 (show (1/3 : ℝ) ≤ 5/12 by norm_num))
  have hDD : D n ≤ D₂ n := hDL.trans hLouter
  have hHH : H n ≤ H₂ n := Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hDD)
  have hD : (D n : ℝ) ≤ Real.sqrt n := (by exact_mod_cast hDD : (D n : ℝ) ≤ D₂ n).trans hD₂
  have hH : (H n : ℝ) ≤ Real.sqrt n := (by exact_mod_cast hHH : (H n : ℝ) ≤ H₂ n).trans hH₂
  have hlog : 0 < Nat.log 2 (n+2) := Nat.log_pos (by decide) (by omega)
  have hDQ : D₂ n ≤ H₂ n := by
    dsimp [H₂, Q]
    calc
      D₂ n ≤ 256 * D₂ n := by omega
      _ ≤ 256 * D₂ n * (Nat.log 2 (n+2))^2 := Nat.le_mul_of_pos_right _ (pow_pos hlog 2)
  let s := (Finset.Ioc (D n) (L n)).filter Squarefree
  have hs {q : ℕ} (hq : q ∈ s) : (D n < q ∧ q ≤ L n) ∧ Squarefree q := by
    simpa [s] using hq
  have hl {q : ℕ} (hq : q ∈ s) : q ≤ ⌊Real.sqrt n / 4⌋₊ := (hs hq).1.2.trans hLsmall
  obtain ⟨hend, hmask, hpair⟩ := denominatorWindowLimits n (D n) (H n) hn hD hH
  have hc : Continuous (GoldbachL2Arithmetic.primeSum n) := by
    unfold GoldbachL2Arithmetic.primeSum GoldbachL2Arithmetic.primeTerm GoldbachL2Arithmetic.E
    fun_prop
  have hw := assembleShellWindows s (D n) (H n) (D₂ n) (H₂ n) n _ hc (by omega)
    (fun _ hq => (hs hq).1.1)
    (fun _ hq => ⟨(hs hq).1.2.trans hLouter, ((hs hq).1.2.trans hLouter).trans hDQ⟩)
    (fun q hq => hend q (hl hq)) (fun q hq => hmask q (hl hq))
    (fun q hq r hr => hpair q r (hl hq) (hl hr))
    (fun q hq h hh => GoldbachL2Arithmetic.reduced_amplitude n q (by omega) (hs hq).2
      hθ (hql q (hl hq)) h hh.1 hh.2)
  simpa only [D, Q, H, D₂, H₂, GoldbachCount.sqrtCutoff, GoldbachL2Arithmetic.primeSum_eq_catalogue,
    GoldbachL2Arithmetic.E, publishedWideArcs] using (scaleDenominatorMass s n d (Real.log n) hmass).trans hw
