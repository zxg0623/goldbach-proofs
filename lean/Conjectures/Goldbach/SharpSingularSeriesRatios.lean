import Conjectures.Goldbach.B13BilateralVaughanReduction
import Conjectures.Goldbach.DeepThreeQuartersExceptionalZeroCriterion
import Mathlib
import Conjectures.Goldbach.BinaryShiftOrderTail

private abbrev isEvenGoldbachTarget (m : ℕ) : Prop := Even m

/-! Sharp singular-series ratios for Goldbach. The final theorem gives the
optimal general factor, prime-level extremizers, the inverse-pair
factor, and a one-character exceptional-count bound. Auxiliary results
are grouped under SharpSingularSeriesRatiosProof. -/

/-! The generalized Goldbach singular series for two primitive Dirichlet
characters. Grouping finite Fourier frequencies by reduced denominator gives
the totient-normalized residue density. A uniform bound for the three Gauss
sums gives absolute convergence at every positive target. Taking finite
levels divisible by every fixed denominator proves the first inequality in
Pintz, “A new explicit formula in the additive theory of primes with
applications I”, §7, (7.7), https://arxiv.org/abs/1804.05561.

The Gauss sums here use the positive additive phase, so the target frequency
in the third Gauss sum is negative. -/

namespace Conjectures.Goldbach.SharpSingularSeriesRatiosProof.TwistedGoldbachSingularSeries

open Finset DirichletCharacter
open scoped BigOperators Classical
open B13BilateralVaughanReductionProof

private theorem group_average {G H : Type*} [Group G] [Group H] [Fintype G] [Fintype H]
    (π : G →* H) (onto : Function.Surjective π) (F : H → ℂ) :
    (Fintype.card H : ℂ) * ∑ x : G, F (π x) = (Fintype.card G : ℂ) * ∑ y : H, F y := by
  have left (y : H) : (∑ x : G, F (y*π x)) = ∑ x : G, F (π x) := by
    obtain ⟨z,rfl⟩ := onto y
    simp_rw [← map_mul]
    exact Equiv.sum_comp (Equiv.mulLeft z) (fun x => F (π x))
  have right (x : G) : (∑ y : H, F (y*π x)) = ∑ y : H, F y :=
    Equiv.sum_comp (Equiv.mulRight (π x)) F
  calc
    _ = ∑ _y : H, ∑ x : G, F (π x) := by simp
    _ = ∑ y : H, ∑ x : G, F (y*π x) := sum_congr rfl (fun y _ => (left y).symm)
    _ = ∑ x : G, ∑ y : H, F (y*π x) := sum_comm
    _ = ∑ _x : G, ∑ y : H, F y := sum_congr rfl (fun x _ => right x)
    _ = _ := by simp

/-- Pushing a lifted character through the reduction of residues preserves
the totient-normalized weighted sum against every function on the divisor. -/
theorem induced_average {q d : ℕ} [NeZero q] [NeZero d] (h : d ∣ q)
    (θ : DirichletCharacter ℂ d) (F : ZMod d → ℂ) :
    (d.totient:ℂ)*(∑ x : ZMod q, changeLevel h θ x * F (ZMod.castHom h (ZMod d) x)) =
      (q.totient:ℂ)*(∑ y : ZMod d, θ y * F y) := by
  let _ : Fintype (ZMod q)ˣ := BombieriVinogradov.LargeSieve.characterReductionUnitFintype q
  let _ : Fintype (ZMod d)ˣ := BombieriVinogradov.LargeSieve.characterReductionUnitFintype d
  rw [← BombieriVinogradov.LargeSieve.sum_units_eq_sum_residues,
    ← BombieriVinogradov.LargeSieve.sum_units_eq_sum_residues θ]
  simp only [changeLevel_eq_cast_of_dvd, ZMod.castHom_apply]
  simpa only [ZMod.card_units_eq_totient, ZMod.unitsMap_val] using
    group_average (ZMod.unitsMap h) (ZMod.unitsMap_surjective h)
      (fun u : (ZMod d)ˣ => θ (u : ZMod d) * F u)

/-- When a character does not factor through the divisor, its whole
pushforward measure vanishes, even before choosing a Fourier phase. -/
theorem absent_average {q d : ℕ} [NeZero q] (h : d ∣ q) (χ : DirichletCharacter ℂ q)
    (hn : ¬χ.FactorsThrough d) (F : ZMod d → ℂ) :
    (∑ x : ZMod q, χ x * F (ZMod.castHom h (ZMod d) x)) = 0 := by
  classical
  have hk := mt (factorsThrough_iff_ker_unitsMap h).mpr hn
  obtain ⟨u,hu,hχ⟩ := Set.not_subset.mp hk
  have hmem : ZMod.unitsMap h u = 1 := hu
  have hne : χ (u : ZMod q) ≠ 1 := by
    intro he
    apply hχ
    apply Units.ext
    exact he
  have hu' : ZMod.castHom h (ZMod d) (u : ZMod q) = 1 := congrArg Units.val hmem
  apply eq_zero_of_mul_eq_self_left hne
  let G (x : ZMod q) := χ x * F (ZMod.castHom h (ZMod d) x)
  calc
    _ = ∑ x : ZMod q, G (u*x) := by
      rw [mul_sum]
      apply sum_congr rfl
      intro x _
      simp only [G,map_mul,hu',one_mul,mul_assoc]
    _ = _ := u.mulLeft_bijective.sum_comp G

private theorem phase_descent {q d : ℕ} [NeZero q] [NeZero d] (h : d ∣ q)
    (k : ℕ) (x : ZMod q) :
    ZMod.stdAddChar (((q/d*k : ℕ) : ZMod q)*x) =
      ZMod.stdAddChar ((k : ZMod d)*ZMod.castHom h (ZMod d) x) := by
  obtain ⟨f,rfl⟩ := h
  obtain ⟨n,rfl⟩ : ∃ n : ℕ, (n : ZMod (d*f)) = x := ⟨x.val,ZMod.natCast_zmod_val x⟩
  rw [Nat.mul_div_cancel_left f (NeZero.pos d), map_natCast, ← Nat.cast_mul, ← Nat.cast_mul,
    DyadicMixedB4GaussLift.stdAddChar_nat_fraction, DyadicMixedB4GaussLift.stdAddChar_nat_fraction]
  congr 1
  have hf : f ≠ 0 := fun e => NeZero.ne (d*f) (by simp [e])
  push_cast
  field_simp [NeZero.ne d,hf]

noncomputable def amplitude {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (k : ℕ) : ℂ :=
  gaussSum χ (ZMod.stdAddChar.mulShift (k : ZMod q)) / (q.totient:ℂ)

theorem amplitude_at_divisor {q d : ℕ} [NeZero q] [NeZero d] (h : d ∣ q)
    (χ : DirichletCharacter ℂ q) (k : ℕ) :
    amplitude χ (q/d*k) = if H : χ.FactorsThrough d then amplitude H.χ₀ k else 0 := by
  classical
  unfold amplitude gaussSum
  simp only [AddChar.mulShift_apply,phase_descent h]
  split_ifs with H
  · apply (div_eq_div_iff (Nat.cast_ne_zero.mpr (NeZero.ne q.totient))
        (Nat.cast_ne_zero.mpr (NeZero.ne d.totient))).mpr
    calc
      _ = (d.totient:ℂ)*(∑ x : ZMod q, changeLevel h H.χ₀ x *
        ZMod.stdAddChar ((k : ZMod d)*ZMod.castHom h (ZMod d) x)) := by
          conv_lhs => rw [H.eq_changeLevel]
          ring
      _ = _ := (induced_average h H.χ₀ (fun y => ZMod.stdAddChar ((k : ZMod d)*y))).trans (mul_comm ..)
  · rw [absent_average h χ H (fun y => ZMod.stdAddChar ((k : ZMod d)*y)),zero_div]

/-- Sort the frequencies at level q by their reduced denominator.
The zero frequency is the unique reduced numerator at denominator one. -/
theorem reduced_denominators (q : ℕ) [NeZero q] (F : ℕ → ℂ) :
    ∑ k ∈ range q, F k =
      ∑ d ∈ q.divisors, ∑ a ∈ (range d).filter (fun a => d.Coprime a), F (q/d*a) := by
  classical
  let T (g : ℕ) := ∑ k ∈ (range q).filter (fun k => q.gcd k=g), F k
  have part : ∑ k ∈ range q, F k = ∑ g ∈ q.divisors, T g :=
    (sum_fiberwise_of_maps_to (fun k (_ : k ∈ range q) =>
      Nat.mem_divisors.mpr ⟨q.gcd_dvd_left k,NeZero.ne q⟩) F).symm
  rw [part, ← Nat.sum_div_divisors q T]
  apply sum_congr rfl
  intro d hd
  obtain ⟨g,hg⟩ := Nat.dvd_of_mem_divisors hd
  have hdpos := Nat.pos_of_mem_divisors hd
  have hgpos : 0 < g := by
    by_contra! hg0
    exact NeZero.ne q (by simp [hg,show g=0 by omega])
  have hquot : q/d=g := by rw [hg,Nat.mul_div_cancel_left g hdpos]
  rw [hquot]
  unfold T
  symm
  apply sum_bij (fun a _ => g*a)
  · intro a ha
    obtain ⟨ha,hc⟩ := mem_filter.mp ha
    have hq : q=g*d := hg.trans (mul_comm d g)
    exact mem_filter.mpr ⟨mem_range.mpr (hq ▸ Nat.mul_lt_mul_of_pos_left (mem_range.mp ha) hgpos),
      by rw [hq,Nat.gcd_mul_left,hc.gcd_eq_one,mul_one]⟩
  · intro a _ b _ hab
    exact Nat.eq_of_mul_eq_mul_left hgpos hab
  · intro k hk
    obtain ⟨hk,hc⟩ := mem_filter.mp hk
    obtain ⟨a,rfl⟩ : g ∣ k := hc ▸ q.gcd_dvd_right k
    have hq : q=g*d := hg.trans (mul_comm d g)
    rw [hq,Nat.gcd_mul_left] at hc
    have ha : a<d := (Nat.mul_lt_mul_left hgpos).mp (hq ▸ mem_range.mp hk)
    exact ⟨a,mem_filter.mpr ⟨mem_range.mpr ha, (mul_eq_left₀ hgpos.ne').mp hc⟩,rfl⟩
  · intro _ _
    rfl

noncomputable def normalized {q : ℕ} [NeZero q] (χ ψ : DirichletCharacter ℂ q) (m : ℕ) : ℂ :=
  ((q:ℂ)*∑ x : ZMod q, χ x * ψ ((m : ZMod q)-x)) / (q.totient:ℂ)^2

/-- The contribution of the reduced fractions of denominator d. It is zero
unless both characters descend. Its phases and Gauss sums are all at d. -/
noncomputable def denominatorTerm {q : ℕ} (χ ψ : DirichletCharacter ℂ q) (m d : ℕ) : ℂ := by
  classical
  exact if hd : d ≠ 0 then
    let _ : NeZero d := ⟨hd⟩
    if H : χ.FactorsThrough d then
      if K : ψ.FactorsThrough d then
        ∑ a ∈ (range d).filter (fun a => d.Coprime a),
          ZMod.stdAddChar ((a : ZMod d)*(-(m : ZMod d))) * amplitude H.χ₀ a * amplitude K.χ₀ a
      else 0
    else 0
  else 0

private theorem synthesis {q : ℕ} [NeZero q] (χ ψ : DirichletCharacter ℂ q) (m : ZMod q) :
    (∑ t : ZMod q, ZMod.stdAddChar (t*(-m)) * (gaussSum χ (ZMod.stdAddChar.mulShift t) *
      gaussSum ψ (ZMod.stdAddChar.mulShift t))) = (q:ℂ) * ∑ x : ZMod q, χ x * ψ (m-x) := by
  let J (s : ZMod q) := ∑ x : ZMod q, χ x * ψ (s-x)
  have h (t : ZMod q) : ZMod.dft J (-t) =
      gaussSum χ (ZMod.stdAddChar.mulShift t) * gaussSum ψ (ZMod.stdAddChar.mulShift t) := by
    rw [gaussSum_mul,ZMod.dft_apply]
    apply sum_congr rfl
    intro s _
    rw [← sum_mul]
    simp only [J,smul_eq_mul,mul_neg,neg_neg,AddChar.mulShift_apply,mul_comm]
  calc
    _ = ZMod.dft (fun t => ZMod.dft J (-t)) m := by
      rw [ZMod.dft_apply]
      apply sum_congr rfl
      intro t _
      rw [h,smul_eq_mul,mul_neg]
    _ = _ := by rw [ZMod.dft_comp_neg,ZMod.dft_dft]; simp only [J,neg_neg,smul_eq_mul]

theorem finite_expansion {q : ℕ} [NeZero q] (χ ψ : DirichletCharacter ℂ q) (m : ℕ) :
    normalized χ ψ m = ∑ d ∈ q.divisors, denominatorTerm χ ψ m d := by
  let F (k : ℕ) := ZMod.stdAddChar ((k : ZMod q)*(-(m : ZMod q))) * amplitude χ k * amplitude ψ k
  have H : normalized χ ψ m = ∑ k ∈ range q, F k := by
    unfold normalized
    rw [← synthesis, ← DyadicMixedB4DualCharacter.sum_natCast_range_eq_zmod, sum_div]
    apply sum_congr rfl
    intro k _
    dsimp only [F,amplitude]
    ring
  rw [H,reduced_denominators q F]
  apply sum_congr rfl
  intro d hd
  have hd0 := (Nat.pos_of_mem_divisors hd).ne'
  let _ : NeZero d := ⟨hd0⟩
  have divides := Nat.dvd_of_mem_divisors hd
  unfold denominatorTerm
  simp only [dite_eq_left hd0]
  by_cases Hχ : χ.FactorsThrough d <;> by_cases Hψ : ψ.FactorsThrough d <;>
    simp only [F,amplitude_at_divisor divides,phase_descent divides,map_neg,map_natCast,Hχ,Hψ,
      dite_true,dite_false,mul_zero,zero_mul,sum_const_zero]

theorem conductor_support {q : ℕ} [NeZero q] (χ ψ : DirichletCharacter ℂ q) (m d : ℕ)
    (h : ¬Nat.lcm χ.conductor ψ.conductor ∣ d) : denominatorTerm χ ψ m d = 0 := by
  unfold denominatorTerm
  split_ifs with hd hχ hψ
  · exact False.elim (h (Nat.lcm_dvd (conductor_dvd_of_mem_conductorSet χ hχ)
      (conductor_dvd_of_mem_conductorSet ψ hψ)))
  all_goals rfl

private theorem principal_count {q : ℕ} [NeZero q] (m : ZMod q) :
    (∑ x : ZMod q, (1 : DirichletCharacter ℂ q) x * (1 : DirichletCharacter ℂ q) (m-x)) =
      (((univ : Finset (ZMod q)).filter (fun x => IsUnit x ∧ IsUnit (m-x))).card:ℂ) := by
  calc
    _ = ∑ x : ZMod q, if IsUnit x ∧ IsUnit (m-x) then (1:ℂ) else 0 := by
      apply sum_congr rfl
      intro x _
      by_cases hu : IsUnit x <;> by_cases hv : IsUnit (m-x) <;>
        simp [hu,hv,MulChar.one_apply,MulChar.map_nonunit]
    _ = _ := by simp

/-- Absolute values of the finite twisted residue counts are bounded by the
ordinary count on the same modulus, including composite moduli. -/
theorem chars_le_units {q : ℕ} [NeZero q] (χ ψ : DirichletCharacter ℂ q)
    (m : ZMod q) : ‖∑ x : ZMod q, χ x * ψ (m-x)‖ ≤
      ‖∑ x : ZMod q, (1 : DirichletCharacter ℂ q) x * (1 : DirichletCharacter ℂ q) (m-x)‖ := by
  rw [principal_count,Complex.norm_natCast]
  calc
    _ ≤ ∑ x : ZMod q, ‖χ x * ψ (m-x)‖ := norm_sum_le _ _
    _ ≤ ∑ x : ZMod q, if IsUnit x ∧ IsUnit (m-x) then (1:ℝ) else 0 := by
      apply sum_le_sum
      intro x _
      by_cases hu : IsUnit x
      · by_cases hv : IsUnit (m-x)
        · rw [ite_eq_left ⟨hu,hv⟩,norm_mul]
          simpa only [one_mul] using mul_le_mul (χ.norm_le_one x) (ψ.norm_le_one (m-x))
            (norm_nonneg _) zero_le_one
        · simp [hv,ψ.map_nonunit hv]
      · simp [hu,χ.map_nonunit hu]
    _ = _ := by simp

/-- Every complete divisor sum is dominated by the ordinary singular-series
sum at the same level and target, without any primitivity assumption. -/
theorem domination {q : ℕ} [NeZero q] (χ ψ : DirichletCharacter ℂ q) (m : ℕ) :
    ‖∑ d ∈ q.divisors, denominatorTerm χ ψ m d‖ ≤
      ‖∑ d ∈ q.divisors, denominatorTerm (1 : DirichletCharacter ℂ q) 1 m d‖ := by
  rw [← finite_expansion,← finite_expansion]
  simp only [normalized,norm_div,norm_mul]
  exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (chars_le_units χ ψ _) (norm_nonneg _))
    (norm_nonneg _)

/-- The numerator sum at a reduced denominator is a product of three Gauss
sums. The first two use frequency one, the third uses the actual target. -/
noncomputable def gaussCoefficient {d : ℕ} [NeZero d] (χ ψ : DirichletCharacter ℂ d) (m : ℕ) : ℂ :=
  (gaussSum χ ZMod.stdAddChar * gaussSum ψ ZMod.stdAddChar *
    gaussSum (χ*ψ)⁻¹ (ZMod.stdAddChar.mulShift (-(m : ZMod d)))) / (d.totient:ℂ)^2

theorem reduced_numerators {d : ℕ} [NeZero d] (χ ψ : DirichletCharacter ℂ d) (m : ℕ) :
    (∑ a ∈ (range d).filter (fun a => d.Coprime a), ZMod.stdAddChar ((a : ZMod d)*(-(m : ZMod d))) *
      amplitude χ a * amplitude ψ a) = gaussCoefficient χ ψ m := by
  let A := gaussSum χ ZMod.stdAddChar * gaussSum ψ ZMod.stdAddChar / (d.totient:ℂ)^2
  let F (z : ZMod d) := (χ*ψ)⁻¹ z * ZMod.stdAddChar ((-(m : ZMod d))*z)
  have shift (θ : DirichletCharacter ℂ d) (a : ℕ) (hc : a.Coprime d) :
      gaussSum θ (ZMod.stdAddChar.mulShift (a : ZMod d)) =
        θ⁻¹ (a : ZMod d) * gaussSum θ ZMod.stdAddChar :=
    gaussSum_mulShift_eq θ ZMod.stdAddChar (ZMod.unitOfCoprime a hc)
  rw [sum_filter]
  calc
    _ = ∑ a ∈ range d, A * F (a : ZMod d) := by
      apply sum_congr rfl
      intro a _
      by_cases hc : d.Coprime a
      · simp only [ite_eq_left hc,A,F,amplitude,shift _ _ hc.symm,mul_inv,MulChar.mul_apply]
        rw [mul_comm (a : ZMod d) (-(m : ZMod d))]
        ring
      · have hnu : ¬IsUnit (a : ZMod d) := fun hu => hc ((ZMod.isUnit_iff_coprime a d).mp hu).symm
        simp only [ite_eq_right hc,F,MulChar.map_nonunit _ hnu,zero_mul,mul_zero]
    _ = A * ∑ z : ZMod d, F z := by
      rw [← mul_sum,DyadicMixedB4DualCharacter.sum_natCast_range_eq_zmod F]
    _ = _ := by unfold A F gaussCoefficient gaussSum; simp only [AddChar.mulShift_apply]; ring

/-- Denominator coefficient for two primitive source characters. It is
defined independently of the finite ambient modulus used in the expansion. -/
noncomputable def coefficient {r s : ℕ} (α : DirichletCharacter ℂ r) (β : DirichletCharacter ℂ s)
    (m d : ℕ) : ℂ := by
  classical
  exact if hd : d ≠ 0 then
    let _ : NeZero d := ⟨hd⟩
    if h : r ∣ d ∧ s ∣ d then gaussCoefficient (changeLevel h.1 α) (changeLevel h.2 β) m else 0
  else 0

private theorem factors_iff_source {r q d : ℕ} [NeZero q] {α : DirichletCharacter ℂ r}
    (hα : α.IsPrimitive) (hr : r ∣ q) (hd : d ∣ q) :
    (changeLevel hr α).FactorsThrough d ↔ r ∣ d := by
  constructor
  · intro H
    simpa only [conductor_changeLevel,show α.conductor=r from hα] using
      conductor_dvd_of_mem_conductorSet (changeLevel hr α) H
  · intro h
    exact ⟨hd,changeLevel h α,changeLevel_trans α h hd⟩

private theorem descended_character {r q d : ℕ} [NeZero q] (α : DirichletCharacter ℂ r)
    (hr : r ∣ q) (hd : d ∣ q) (h : r ∣ d) (H : (changeLevel hr α).FactorsThrough d) :
    H.χ₀ = changeLevel h α :=
  changeLevel_injective hd (H.eq_changeLevel.symm.trans (changeLevel_trans α h hd))

theorem stable_denominator {r s q : ℕ} [NeZero q] {α : DirichletCharacter ℂ r}
    {β : DirichletCharacter ℂ s} (hα : α.IsPrimitive) (hβ : β.IsPrimitive)
    (hr : r ∣ q) (hs : s ∣ q) (m d : ℕ) (hd : d ∣ q) :
    denominatorTerm (changeLevel hr α) (changeLevel hs β) m d = coefficient α β m d := by
  have hd0 : d ≠ 0 := fun e => NeZero.ne q (Nat.eq_zero_of_zero_dvd (e ▸ hd))
  let _ : NeZero d := ⟨hd0⟩
  simp only [denominatorTerm,coefficient,dite_eq_left hd0]
  by_cases H : r ∣ d
  · have H' := (factors_iff_source hα hr hd).mpr H
    by_cases K : s ∣ d
    · have K' := (factors_iff_source hβ hs hd).mpr K
      simp only [dite_eq_left H',dite_eq_left K',dite_eq_left (And.intro H K),reduced_numerators,
        descended_character α hr hd H H',descended_character β hs hd K K']
    · have K' := mt (factors_iff_source hβ hs hd).mp K
      simp only [dite_eq_left H',dite_eq_right K',dite_eq_right (not_and_of_not_right _ K)]
  · have H' := mt (factors_iff_source hα hr hd).mp H
    simp only [dite_eq_right H',dite_eq_right (not_and_of_not_left _ H)]

private theorem estimate_at_multiple {r s d : ℕ} [NeZero r] [NeZero s] [NeZero d]
    (α : DirichletCharacter ℂ r) (β : DirichletCharacter ℂ s) (hr : r ∣ d) (hs : s ∣ d)
    (m : ℕ) (hm : 0 < m) :
    let R := Real.sqrt ((r*s:ℕ):ℝ)
    let M := ∑ f ∈ m.divisors, (f:ℝ)
    ‖gaussCoefficient (changeLevel hr α) (changeLevel hs β) m‖ ≤ R*R*(R*M)/(d.totient:ℝ)^2 := by
  intro R M
  let A := changeLevel hr α
  let B := changeLevel hs β
  let Z := (A*B)⁻¹
  have hrpos := Nat.mul_pos (NeZero.pos r) (NeZero.pos s)
  have cA : A.conductor ∣ r*s := by
    dsimp only [A]
    rw [conductor_changeLevel]
    exact α.conductor_dvd_level.trans (dvd_mul_right r s)
  have cB : B.conductor ∣ r*s := by
    dsimp only [B]
    rw [conductor_changeLevel]
    exact β.conductor_dvd_level.trans (dvd_mul_left s r)
  have cZ : Z.conductor ∣ r*s := by
    rw [show Z.conductor=(A*B).conductor from conductor_inv _]
    exact (conductor_mul_dvd_lcm_conductor A B).trans (Nat.lcm_dvd cA cB)
  have root {t : ℕ} (h : t ∣ r*s) : Real.sqrt t ≤ R :=
    Real.sqrt_le_sqrt (by exact_mod_cast Nat.le_of_dvd hrpos h)
  have hA := (DyadicMixedB4CharacterFactorBound.norm_dirichlet_gauss_standard A).trans (root cA)
  have hB := (DyadicMixedB4CharacterFactorBound.norm_dirichlet_gauss_standard B).trans (root cB)
  have mass : (∑ f ∈ m.divisors.filter (fun f => Z.conductor*f ∣ d), (f:ℝ)) ≤ M :=
    sum_le_sum_of_subset_of_nonneg (filter_subset ..) (fun i _ _ => Nat.cast_nonneg i)
  have hsft := DyadicMixedB4CharacterFactorBound.norm_dirichlet_gauss_induced (dvd_refl d) Z m hm
  rw [changeLevel_self] at hsft
  have hZ := (DyadicMixedB4CharacterFactorBound.norm_gauss_neg_shift_le Z (m : ZMod d)).trans
    (hsft.trans (mul_le_mul (root cZ) mass (by positivity) (Real.sqrt_nonneg _)))
  change ‖(gaussSum A ZMod.stdAddChar * gaussSum B ZMod.stdAddChar *
    gaussSum Z (ZMod.stdAddChar.mulShift (-(m : ZMod d))))/(d.totient:ℂ)^2‖ ≤ _
  rw [norm_div,norm_pow,Complex.norm_natCast,norm_mul,norm_mul]
  exact div_le_div_of_nonneg_right (mul_le_mul
    (mul_le_mul hA hB (norm_nonneg _) (Real.sqrt_nonneg _)) hZ (norm_nonneg _)
    (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))) (sq_nonneg _)

private theorem totient_weight {d : ℕ} (hd : 0 < d) :
    1/(d.totient:ℝ)^2 ≤ 576 * (d:ℝ)^(-(3/2):ℝ) := by
  have h := DeepThreeQuarters.totient_ratio_le_rpow (show (0:ℝ)<1/4 by norm_num) d hd
  norm_num at h
  have dp : (0:ℝ)<d := by exact_mod_cast hd
  have hp : (0:ℝ)<d.totient := by exact_mod_cast Nat.totient_pos.mpr hd
  have invbound : 1/(d.totient:ℝ) ≤ 24*(d:ℝ)^(-(3/4):ℝ) := by
    calc
      _ = ((d:ℝ)/d.totient)/d := by field_simp
      _ ≤ (24*(d:ℝ)^(1/4:ℝ))/d := div_le_div_of_nonneg_right h dp.le
      _ = _ := by
        rw [show (-(3/4):ℝ)=1/4-1 by norm_num,Real.rpow_sub dp,Real.rpow_one]
        ring
  have square := pow_le_pow_left₀ (by positivity : (0:ℝ) ≤ 1/d.totient) invbound 2
  rw [div_pow,one_pow,mul_pow,← Real.rpow_mul_natCast dp.le] at square
  norm_num at square ⊢
  exact square

/-- Absolute convergence holds at every positive target. The divisor sum of
m controls the third Gauss sum uniformly as the reduced denominator varies. -/
theorem summable_coefficients {r s : ℕ} [NeZero r] [NeZero s]
    (α : DirichletCharacter ℂ r) (β : DirichletCharacter ℂ s) (m : ℕ) (hm : 0 < m) :
    Summable (fun d : ℕ => ‖coefficient α β m d‖) := by
  let R := Real.sqrt ((r*s:ℕ):ℝ)
  let M := ∑ f ∈ m.divisors, (f:ℝ)
  let C := R*R*(R*M)
  have hC : 0≤C := by dsimp [C,M,R]; positivity
  have summable : Summable (fun d : ℕ => (d:ℝ)^(-(3/2):ℝ)) :=
    Real.summable_nat_rpow.mpr (by norm_num)
  apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _) _ (summable.mul_left (C*576))
  intro d
  by_cases hd : d=0
  · simp [coefficient,hd,Real.zero_rpow (by norm_num : (-(3/2):ℝ) ≠ 0)]
  have bound0 : 0 ≤ C*576*(d:ℝ)^(-(3/2):ℝ) := by positivity
  let _ : NeZero d := ⟨hd⟩
  by_cases h : r ∣ d ∧ s ∣ d
  · simp only [coefficient,dite_eq_left hd,dite_eq_left h]
    calc
      _ ≤ C/(d.totient:ℝ)^2 := estimate_at_multiple α β h.1 h.2 m hm
      _ = C*(1/(d.totient:ℝ)^2) := by ring
      _ ≤ C*(576*(d:ℝ)^(-(3/2):ℝ)) := mul_le_mul_of_nonneg_left (totient_weight (Nat.pos_of_ne_zero hd)) hC
      _ = _ := by ring
  · simpa only [coefficient,dite_eq_left hd,dite_eq_right h,norm_zero] using bound0

theorem ambient_sum {r s q : ℕ} [NeZero q] {α : DirichletCharacter ℂ r} {β : DirichletCharacter ℂ s}
    (hα : α.IsPrimitive) (hβ : β.IsPrimitive) (hr : r ∣ q) (hs : s ∣ q) (m : ℕ) :
    normalized (changeLevel hr α) (changeLevel hs β) m =
      ∑ d ∈ q.divisors, coefficient α β m d :=
  (finite_expansion _ _ m).trans (sum_congr rfl (fun d hd =>
    stable_denominator hα hβ hr hs m d (Nat.dvd_of_mem_divisors hd)))

open Filter Topology

private theorem cofinal_divisors (L : ℕ) (hL : L ≠ 0) :
    Tendsto (fun n : ℕ => insert 0 (L*n.factorial).divisors) atTop atTop := by
  apply tendsto_atTop.2
  intro S
  filter_upwards [eventually_ge_atTop (S.sup id)] with n hn
  intro d hd
  by_cases h : d=0
  · simp [h]
  apply mem_insert_of_mem
  have hdn : d≤n := (S.le_sup (f := id) hd).trans hn
  exact Nat.mem_divisors.mpr ⟨(Nat.dvd_factorial (Nat.pos_of_ne_zero h) hdn).trans
    (dvd_mul_left n.factorial L),mul_ne_zero hL n.factorial_ne_zero⟩

/-- Complete divisor sums at L times n! exhaust the absolutely convergent
series, starting from any positive base level L. -/
theorem partial_limit {r s : ℕ} [NeZero r] [NeZero s]
    (α : DirichletCharacter ℂ r) (β : DirichletCharacter ℂ s) (m : ℕ) (hm : 0 < m)
    (L : ℕ) (hL : L ≠ 0) :
    Tendsto (fun n : ℕ => ∑ d ∈ (L*n.factorial).divisors, coefficient α β m d)
      atTop (𝓝 (∑' d : ℕ, coefficient α β m d)) := by
  have h := (summable_coefficients α β m hm).of_norm.hasSum
  have hl := h.comp (cofinal_divisors L hL)
  apply hl.congr'
  filter_upwards with n
  simp [coefficient]

private theorem principal_real (q : ℕ) [NeZero q] (m : ℕ) :
    ‖normalized (1 : DirichletCharacter ℂ q) 1 m‖ = (normalized (1 : DirichletCharacter ℂ q) 1 m).re := by
  let N := ((univ : Finset (ZMod q)).filter (fun x => IsUnit x ∧ IsUnit ((m:ZMod q)-x))).card
  let v : ℝ := q*N/(q.totient:ℝ)^2
  have hv : 0≤v := by dsimp [v]; positivity
  have e : normalized (1 : DirichletCharacter ℂ q) 1 m = (v:ℂ) := by
    unfold normalized v
    rw [principal_count]
    push_cast
    rfl
  rw [e,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hv,Complex.ofReal_re]

/-- The absolute value of the full twisted singular series is at most the
ordinary singular series at each positive target. Both series converge
absolutely, with no zero-free hypothesis. -/
theorem infinite_domination {r s : ℕ} [NeZero r] [NeZero s]
    {α : DirichletCharacter ℂ r} {β : DirichletCharacter ℂ s}
    (hα : α.IsPrimitive) (hβ : β.IsPrimitive) (m : ℕ) (hm : 0 < m) :
    ‖∑' d : ℕ, coefficient α β m d‖ ≤
      (∑' d : ℕ, coefficient (1 : DirichletCharacter ℂ 1) (1 : DirichletCharacter ℂ 1) m d).re := by
  let L := r*s
  have hL : L ≠ 0 := mul_ne_zero (NeZero.ne r) (NeZero.ne s)
  let oneχ : DirichletCharacter ℂ 1 := 1
  have main := partial_limit oneχ oneχ m hm L hL
  apply le_of_tendsto_of_tendsto' (partial_limit α β m hm L hL).norm (Complex.continuous_re.tendsto _ |>.comp main)
  intro n
  let q := L*n.factorial
  let _ : NeZero q := ⟨mul_ne_zero hL n.factorial_ne_zero⟩
  have hr : r ∣ q := (dvd_mul_right r s).trans (dvd_mul_right L n.factorial)
  have hs : s ∣ q := (dvd_mul_left s r).trans (dvd_mul_right L n.factorial)
  have ordinary := ambient_sum (α := oneχ) (β := oneχ) isPrimitive_one_level_one
    isPrimitive_one_level_one (one_dvd q) (one_dvd q) m
  simp only [oneχ,map_one] at ordinary
  change ‖∑ d ∈ q.divisors, coefficient α β m d‖ ≤
    (∑ d ∈ q.divisors, coefficient oneχ oneχ m d).re
  rw [← ambient_sum hα hβ hr hs m,← ordinary,← principal_real]
  simpa only [← finite_expansion] using domination (changeLevel hr α) (changeLevel hs β) m

end Conjectures.Goldbach.SharpSingularSeriesRatiosProof.TwistedGoldbachSingularSeries

/-! Reduction of an admissible binary residue pair through any divisor has
uniform fibers. This lets one recover the ratio of the full twisted and
ordinary singular series from a single modulus containing both conductors. -/

namespace Conjectures.Goldbach.SharpSingularSeriesRatiosProof.TwistedGoldbachConductorRatio

open Finset DirichletCharacter
open scoped BigOperators Classical

def admissible {n : ℕ} (m x : ZMod n) : Prop := IsUnit x ∧ IsUnit (m-x)

noncomputable def fiber {q L : ℕ} [NeZero q] (h : L ∣ q) (m : ZMod q) (u : ZMod L) :
    Finset (ZMod q) := univ.filter (fun x => admissible m x ∧ ZMod.castHom h (ZMod L) x=u)

private theorem unit_criterion {q : ℕ} [NeZero q] (x : ZMod q) :
    IsUnit x ↔ ∀ (p : ℕ), p.Prime → ∀ h : p ∣ q, ZMod.castHom h (ZMod p) x ≠ 0 := by
  constructor
  · intro hx p hp h
    let _ : Fact p.Prime := ⟨hp⟩
    exact (hx.map (ZMod.castHom h (ZMod p))).ne_zero
  · obtain ⟨n,rfl⟩ : ∃ n : ℕ, (n : ZMod q)=x := ⟨x.val,ZMod.natCast_zmod_val x⟩
    intro H
    apply (ZMod.isUnit_iff_coprime n q).mpr
    apply Nat.coprime_of_dvd
    intro p hp hn hq
    exact H p hp hq (by rw [map_natCast,ZMod.natCast_eq_zero_iff]; exact hn)

private theorem reduce_twice {p q L : ℕ} [NeZero q] (h : L ∣ q) (g : p ∣ L) (x : ZMod q) :
    ZMod.castHom g (ZMod p) (ZMod.castHom h (ZMod L) x) = ZMod.castHom (g.trans h) (ZMod p) x := by
  obtain ⟨n,rfl⟩ : ∃ n : ℕ, (n : ZMod q)=x := ⟨x.val,ZMod.natCast_zmod_val x⟩
  simp only [map_natCast]

private theorem preserving_shift {q L : ℕ} [NeZero q] [NeZero L] (h : L ∣ q) (b : ZMod L) :
    ∃ c : ZMod q, ZMod.castHom h (ZMod L) c=b ∧
      ∀ p : ℕ, p.Prime → ∀ hp : p ∣ q, ¬p ∣ L → ZMod.castHom hp (ZMod p) c=0 := by
  let S := q.primeFactors.filter (fun p => ¬p ∣ L)
  let D := ∏ p ∈ S, p
  have hc : D.Coprime L := Nat.coprime_prod_left_iff.mpr (fun p hp =>
    (Nat.prime_of_mem_primeFactors (mem_filter.mp hp).1).coprime_iff_not_dvd.mpr (mem_filter.mp hp).2)
  let u := ZMod.unitOfCoprime D hc
  let n := ((↑u⁻¹ : ZMod L)*b).val
  refine ⟨((D*n:ℕ):ZMod q),?_,?_⟩
  · rw [map_natCast,Nat.cast_mul,show (n : ZMod L) = (↑u⁻¹ : ZMod L)*b from ZMod.natCast_zmod_val _]
    change (↑u : ZMod L)*(↑u⁻¹*b)=b
    simp
  · intro p hp hq hL
    have hpS : p ∈ S := mem_filter.mpr ⟨Nat.mem_primeFactors.mpr ⟨hp,hq,NeZero.ne q⟩,hL⟩
    rw [map_natCast,ZMod.natCast_eq_zero_iff]
    exact (dvd_prod_of_mem (fun z : ℕ => z) hpS).trans (dvd_mul_right D n)

private theorem patch_unit {q L : ℕ} [NeZero q] (h : L ∣ q) (x c : ZMod q) (hx : IsUnit x)
    (hl : IsUnit (ZMod.castHom h (ZMod L) (x+c)))
    (away : ∀ p : ℕ, p.Prime → ∀ hp : p ∣ q, ¬p ∣ L → ZMod.castHom hp (ZMod p) c=0) :
    IsUnit (x+c) := by
  apply (unit_criterion _).mpr
  intro p hprime hp
  by_cases hL : p ∣ L
  · let _ : Fact p.Prime := ⟨hprime⟩
    rw [← reduce_twice h hL]
    exact (hl.map (ZMod.castHom hL (ZMod p))).ne_zero
  · rw [map_add,away p hprime hp hL,add_zero]
    exact (unit_criterion x).mp hx p hprime hp

private theorem fiber_card_le {q L : ℕ} [NeZero q] [NeZero L] (h : L ∣ q)
    (m : ZMod q) (u v : ZMod L) (hv : admissible (ZMod.castHom h (ZMod L) m) v) :
    (fiber h m u).card ≤ (fiber h m v).card := by
  let π := ZMod.castHom h (ZMod L)
  obtain ⟨c,hc,away⟩ := preserving_shift h (v-u)
  apply card_le_card_of_injOn (fun x : ZMod q => x+c)
  · intro x hx
    obtain ⟨⟨hxunit,hother⟩,hπ⟩ := (mem_filter.mp hx).2
    have image : π (x+c)=v := by rw [map_add,hπ,hc]; abel
    refine mem_filter.mpr ⟨mem_univ _,⟨⟨?_,?_⟩,image⟩⟩
    · apply patch_unit h x c hxunit _ away
      exact image ▸ hv.1
    · rw [show m-(x+c)=(m-x)+(-c) by ring]
      apply patch_unit h (m-x) (-c) hother
      · change IsUnit (π ((m-x)+(-c)))
        rw [show (m-x)+(-c)=m-(x+c) by ring,map_sub,image]
        exact hv.2
      · intro p hprime hp hL
        rw [map_neg,away p hprime hp hL,neg_zero]
  · intro x _ y _ e
    exact add_right_cancel e

/-- Every lower admissible pair has the same number of admissible lifts,
including when q has prime factors absent from L. -/
theorem uniform_fibers {q L : ℕ} [NeZero q] [NeZero L] (h : L ∣ q) (m : ZMod q) :
    ∃ K : ℕ, ∀ u : ZMod L, (fiber h m u).card =
      if admissible (ZMod.castHom h (ZMod L) m) u then K else 0 := by
  let π := ZMod.castHom h (ZMod L)
  have empty (u : ZMod L) (hu : ¬admissible (π m) u) : fiber h m u=∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    intro x hx
    obtain ⟨⟨h₁,h₂⟩,e⟩ := (mem_filter.mp hx).2
    apply hu
    rw [← e]
    exact ⟨h₁.map π,by simpa only [map_sub] using h₂.map π⟩
  by_cases H : ∃ u : ZMod L, admissible (π m) u
  · obtain ⟨u,hu⟩ := H
    refine ⟨(fiber h m u).card,fun v => ?_⟩
    by_cases hv : admissible (π m) v
    · rw [ite_eq_left hv]
      exact le_antisymm (fiber_card_le h m v u hu) (fiber_card_le h m u v hv)
    · rw [ite_eq_right hv,empty v hv,card_empty]
  · refine ⟨0,fun u => ?_⟩
    have hu : ¬admissible (π m) u := fun h => H ⟨u,h⟩
    rw [ite_eq_right hu,empty u hu,card_empty]

private theorem reduce_admissible {q L : ℕ} (h : L ∣ q) {m x : ZMod q} (hx : admissible m x) :
    admissible (ZMod.castHom h (ZMod L) m) (ZMod.castHom h (ZMod L) x) :=
  ⟨hx.1.map _,by simpa only [map_sub] using hx.2.map (ZMod.castHom h (ZMod L))⟩

theorem fiber_weight {q L : ℕ} [NeZero q] [NeZero L] (h : L ∣ q) (m : ZMod q) :
    ∃ K : ℕ, ∀ F : ZMod L → ℂ,
      (∑ x ∈ univ.filter (admissible m), F (ZMod.castHom h (ZMod L) x)) =
        (K:ℂ)*∑ y ∈ univ.filter (admissible (ZMod.castHom h (ZMod L) m)), F y := by
  let π := ZMod.castHom h (ZMod L)
  let H := univ.filter (admissible m)
  let T := univ.filter (admissible (π m))
  obtain ⟨K,hK⟩ := uniform_fibers h m
  refine ⟨K, fun F => ?_⟩
  have maps : ∀ x ∈ H, π x ∈ T := fun x hx =>
    mem_filter.mpr ⟨mem_univ _,reduce_admissible h (mem_filter.mp hx).2⟩
  have group (u : ZMod L) : H.filter (fun x => π x=u) = fiber h m u := by
    ext x
    simp only [H,π,fiber,mem_filter,mem_univ,true_and]
  change (∑ x ∈ H, F (π x)) = (K:ℂ)*∑ u ∈ T, F u
  rw [← sum_fiberwise_of_maps_to' maps F,mul_sum]
  apply sum_congr rfl
  intro u hu
  have hu' : admissible (ZMod.castHom h (ZMod L) m) u := (mem_filter.mp hu).2
  rw [group,sum_const,nsmul_eq_mul,hK u,ite_eq_left hu']

noncomputable def J {q : ℕ} [NeZero q] (χ ψ : DirichletCharacter ℂ q) (m : ZMod q) : ℂ :=
  ∑ x : ZMod q, χ x * ψ (m-x)

private theorem restricted_eq {q : ℕ} [NeZero q] (χ ψ : DirichletCharacter ℂ q) (m : ZMod q) :
    (∑ x ∈ univ.filter (admissible m), χ x * ψ (m-x)) = J χ ψ m := by
  apply sum_subset (filter_subset ..)
  intro x _ hx
  by_cases hu : IsUnit x
  · have hv : ¬IsUnit (m-x) := fun hv => hx (mem_filter.mpr ⟨mem_univ _,hu,hv⟩)
    simp [ψ.map_nonunit hv]
  · simp [χ.map_nonunit hu]

/-- The same lift multiplicity works for all pairs of characters at L. -/
theorem jacobi_lift {q L : ℕ} [NeZero q] [NeZero L] (h : L ∣ q) (m : ZMod q) :
    ∃ K : ℕ, ∀ χ ψ : DirichletCharacter ℂ L,
      J (changeLevel h χ) (changeLevel h ψ) m = (K:ℂ)*J χ ψ (ZMod.castHom h (ZMod L) m) := by
  let π := ZMod.castHom h (ZMod L)
  obtain ⟨K,hK⟩ := fiber_weight h m
  refine ⟨K,fun χ ψ => ?_⟩
  have reduce (θ : DirichletCharacter ℂ L) (x : ZMod q) (hx : IsUnit x) :
      changeLevel h θ x = θ (π x) := by
    simpa only [π,IsUnit.unit_spec,ZMod.castHom_apply] using changeLevel_eq_cast_of_dvd θ h hx.unit
  rw [← restricted_eq,← restricted_eq χ ψ]
  calc
    _ = ∑ x ∈ univ.filter (admissible m), χ (π x)*ψ (π m-π x) := by
      apply sum_congr rfl
      intro x hx
      have h' := (mem_filter.mp hx).2
      rw [reduce χ x h'.1,reduce ψ (m-x) h'.2,map_sub]
    _ = _ := hK (fun x => χ x*ψ (π m-x))

open TwistedGoldbachSingularSeries

private theorem finite_cross {q L : ℕ} [NeZero q] [NeZero L] (h : L ∣ q)
    (χ ψ : DirichletCharacter ℂ L) (m : ℕ) :
    normalized (changeLevel h χ) (changeLevel h ψ) m * J (1 : DirichletCharacter ℂ L) 1 (m : ZMod L) =
      normalized (1 : DirichletCharacter ℂ q) 1 m * J χ ψ (m : ZMod L) := by
  obtain ⟨K,hK⟩ := jacobi_lift h (m : ZMod q)
  have weighted := hK χ ψ
  have ordinary := hK 1 1
  simp only [map_natCast,map_one] at weighted ordinary
  change ((q:ℂ)*J (changeLevel h χ) (changeLevel h ψ) (m : ZMod q)/(q.totient:ℂ)^2)*_ =
    ((q:ℂ)*J (1 : DirichletCharacter ℂ q) 1 (m : ZMod q)/(q.totient:ℂ)^2)*_
  rw [weighted,ordinary]
  ring

open Filter Topology

/-- The ratio of the two singular series is determined at any single common
multiple of the conductors. The identity also holds at targets for which the
principal residue count vanishes. -/
theorem conductor_identity {r s L : ℕ} [NeZero r] [NeZero s] [NeZero L]
    {α : DirichletCharacter ℂ r} {β : DirichletCharacter ℂ s}
    (hα : α.IsPrimitive) (hβ : β.IsPrimitive) (hr : r ∣ L) (hs : s ∣ L) (m : ℕ) (hm : 0 < m) :
    (∑' d : ℕ, coefficient α β m d) * J (1 : DirichletCharacter ℂ L) 1 (m : ZMod L) =
      (∑' d : ℕ, coefficient (1 : DirichletCharacter ℂ 1) (1 : DirichletCharacter ℂ 1) m d) *
        J (changeLevel hr α) (changeLevel hs β) (m : ZMod L) := by
  let oneχ : DirichletCharacter ℂ 1 := 1
  have left := (partial_limit α β m hm L (NeZero.ne L)).mul_const (J (1 : DirichletCharacter ℂ L) 1 (m : ZMod L))
  have right := (partial_limit oneχ oneχ m hm L (NeZero.ne L)).mul_const
    (J (changeLevel hr α) (changeLevel hs β) (m : ZMod L))
  apply tendsto_nhds_unique_of_eventuallyEq left right
  filter_upwards with n
  let q := L*n.factorial
  let _ : NeZero q := ⟨mul_ne_zero (NeZero.ne L) n.factorial_ne_zero⟩
  have h : L ∣ q := dvd_mul_right L n.factorial
  have ordinary := ambient_sum (α := oneχ) (β := oneχ) isPrimitive_one_level_one
    isPrimitive_one_level_one (one_dvd q) (one_dvd q) m
  simp only [oneχ,map_one] at ordinary
  change ((∑ d ∈ q.divisors, coefficient α β m d)*_) =
    ((∑ d ∈ q.divisors, coefficient oneχ oneχ m d)*_)
  rw [← ambient_sum hα hβ (hr.trans h) (hs.trans h) m, ← ordinary,
    changeLevel_trans α hr h, changeLevel_trans β hs h]
  exact finite_cross h (changeLevel hr α) (changeLevel hs β) m

/-- The principal-character convolution counts admissible residues. -/
theorem principal_card {L : ℕ} [NeZero L] (m : ZMod L) :
    J (1 : DirichletCharacter ℂ L) 1 m = ((univ.filter (admissible m)).card:ℂ) := by
  rw [← restricted_eq]
  calc
    _ = ∑ _x ∈ univ.filter (admissible m), (1:ℂ) := by
      apply sum_congr rfl
      intro x hx
      have H := (mem_filter.mp hx).2
      rw [MulChar.one_apply H.1,MulChar.one_apply H.2,one_mul]
    _ = _ := by simp

/-- An explicit admissible residue for every even target and every positive
modulus. At a prime where the target is one the polynomial selects minus one,
and otherwise it selects one. -/
theorem admissible_even (L : ℕ) [NeZero L] (m : ℕ) (he : Even m) :
    ∃ x : ZMod L, admissible (m : ZMod L) x := by
  let x : ZMod L := 2*((m:ZMod L)-1)^L.factorial-1
  have both (p : ℕ) (hp : p.Prime) (h : p ∣ L) :
      ZMod.castHom h (ZMod p) x ≠ 0 ∧ ZMod.castHom h (ZMod p) ((m:ZMod L)-x) ≠ 0 := by
    let _ : Fact p.Prime := ⟨hp⟩
    have red : ZMod.castHom h (ZMod p) x = 2*((m:ZMod p)-1)^L.factorial-1 := by
      simp only [x,map_sub,map_mul,map_ofNat,map_pow,map_natCast,map_one]
    have red' : ZMod.castHom h (ZMod p) ((m:ZMod L)-x) =
        (m:ZMod p) - (2*((m:ZMod p)-1)^L.factorial-1) := by
      rw [map_sub,map_natCast,red]
    rw [red,red']
    by_cases h1 : (m:ZMod p)=1
    · have p2 : p≠2 := by
        rintro rfl
        have hz : (m : ZMod 2)=0 := (ZMod.natCast_eq_zero_iff m 2).mpr (even_iff_two_dvd.mp he)
        exact one_ne_zero (h1.symm.trans hz)
      have nz : (2 : ZMod p) ≠ 0 := fun hz =>
        p2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp ((ZMod.natCast_eq_zero_iff 2 p).mp hz))
      simp only [h1,sub_self,zero_pow L.factorial_ne_zero,mul_zero,zero_sub,sub_neg_eq_add]
      exact ⟨neg_ne_zero.mpr one_ne_zero,by simpa only [one_add_one_eq_two] using nz⟩
    · have hpL : p≤L := Nat.le_of_dvd (NeZero.pos L) h
      obtain ⟨t,ht⟩ := Nat.dvd_factorial (Nat.sub_pos_of_lt hp.one_lt) ((Nat.sub_le p 1).trans hpL)
      have u : ((m:ZMod p)-1)^L.factorial = 1 := by
        rw [ht,pow_mul,ZMod.pow_card_sub_one_eq_one (sub_ne_zero.mpr h1),one_pow]
      rw [u,mul_one,show (2:ZMod p)-1=1 by ring]
      exact ⟨one_ne_zero,sub_ne_zero.mpr h1⟩
  exact ⟨x,(unit_criterion x).mpr (fun p hp h => (both p hp h).1),
    (unit_criterion _).mpr (fun p hp h => (both p hp h).2)⟩

/-- At even targets the ordinary count in the denominator is positive, so the
finite conductor-level correction can be used as a literal complex ratio. -/
theorem exact_ratio {r s L : ℕ} [NeZero r] [NeZero s] [NeZero L]
    {α : DirichletCharacter ℂ r} {β : DirichletCharacter ℂ s}
    (hα : α.IsPrimitive) (hβ : β.IsPrimitive) (hr : r ∣ L) (hs : s ∣ L) (m : ℕ)
    (hm : 0 < m) (he : Even m) :
    (∑' d : ℕ, coefficient α β m d) =
      (∑' d : ℕ, coefficient (1 : DirichletCharacter ℂ 1) (1 : DirichletCharacter ℂ 1) m d) *
        (J (changeLevel hr α) (changeLevel hs β) (m : ZMod L) /
          ((univ.filter (admissible (m : ZMod L))).card:ℂ)) := by
  obtain ⟨x,hx⟩ := admissible_even L m he
  have positive := card_pos.mpr (show (univ.filter (admissible (m : ZMod L))).Nonempty from
    ⟨x,mem_filter.mpr ⟨mem_univ _,hx⟩⟩)
  rw [← mul_div_assoc,eq_div_iff (Nat.cast_ne_zero.mpr positive.ne')]
  rw [← principal_card]
  exact conductor_identity hα hβ hr hs m hm

/-- At zero, orthogonality selects the inverse pair of characters. -/
theorem zero_jacobi {L : ℕ} [NeZero L] (A B : DirichletCharacter ℂ L) :
    J A B 0 = if A*B=1 then B (-1)*(L.totient:ℂ) else 0 := by
  have eqn (x : ZMod L) : A x * B (0-x) = B (-1)*(A*B) x := by
    rw [zero_sub,← neg_one_mul x,map_mul,MulChar.mul_apply]
    ring
  simp only [J,eqn,← mul_sum]
  by_cases h : A*B=1
  · rw [ite_eq_left h,h,MulChar.sum_one_eq_card_units,ZMod.card_units_eq_totient]
  · rw [ite_eq_right h,MulChar.sum_eq_zero_of_ne_one h,mul_zero]

/-- On a multiple of both conductors, all off-diagonal character pairs
vanish. The surviving inverse pair retains its parity at minus one. -/
theorem at_conductor_multiple {r s L : ℕ} [NeZero r] [NeZero s] [NeZero L]
    {α : DirichletCharacter ℂ r} {β : DirichletCharacter ℂ s} (hα : α.IsPrimitive) (hβ : β.IsPrimitive)
    (hr : r ∣ L) (hs : s ∣ L) (m : ℕ) (hm : 0 < m) (divides : L ∣ m) :
    (∑' d : ℕ, coefficient α β m d) = if changeLevel hr α * changeLevel hs β = 1 then
      (∑' d : ℕ, coefficient (1 : DirichletCharacter ℂ 1) (1 : DirichletCharacter ℂ 1) m d) *
      changeLevel hs β (-1) else 0 := by
  have ident := conductor_identity hα hβ hr hs m hm
  have hz := (ZMod.natCast_eq_zero_iff m L).mpr divides
  have principal : J (1 : DirichletCharacter ℂ L) 1 0 = (L.totient:ℂ) := by
    rw [zero_jacobi]
    simp [MulChar.one_apply (isUnit_neg_one : IsUnit (-1 : ZMod L))]
  rw [hz,principal,zero_jacobi] at ident
  apply mul_right_cancel₀ (Nat.cast_ne_zero.mpr (NeZero.ne L.totient) : (L.totient:ℂ) ≠ 0)
  split_ifs at ident ⊢ with h
  · simpa only [mul_assoc] using ident
  · simpa only [zero_mul,mul_zero] using ident

theorem unequal_conductors_vanish {r s L : ℕ} [NeZero r] [NeZero s] [NeZero L]
    {α : DirichletCharacter ℂ r} {β : DirichletCharacter ℂ s} (hα : α.IsPrimitive) (hβ : β.IsPrimitive)
    (hr : r ∣ L) (hs : s ∣ L) (hne : r≠s) (m : ℕ) (hm : 0 < m) (divides : L ∣ m) :
    (∑' d : ℕ, coefficient α β m d) = 0 := by
  rw [at_conductor_multiple hα hβ hr hs m hm divides]
  apply ite_eq_right
  intro hab
  have hinv : changeLevel hs β = (changeLevel hr α)⁻¹ := eq_inv_of_mul_eq_one_right hab
  have e := congrArg DirichletCharacter.conductor hinv
  simp only [conductor_inv,conductor_changeLevel,show α.conductor=r from hα,
    show β.conductor=s from hβ] at e
  exact hne e.symm

end Conjectures.Goldbach.SharpSingularSeriesRatiosProof.TwistedGoldbachConductorRatio

/-! Finite character-twisted Goldbach densities at squarefree levels.
The sum is over all residues, with the two Dirichlet characters extended
by zero on nonunits. No primitivity or reality hypothesis is needed.
The comparison is with the untwisted density at the same level and target. -/

namespace Conjectures.Goldbach.SharpSingularSeriesRatiosProof.SquarefreeTwistedGoldbachDensity

open Finset
open scoped BigOperators Classical

noncomputable def localSum {p : ℕ} [Fact p.Prime] (χ ψ : DirichletCharacter ℂ p)
    (m : ZMod p) : ℂ := ∑ a : ZMod p, χ a * ψ (m-a)

private theorem norm_jacobi {p : ℕ} [hp : Fact p.Prime] {χ ψ : DirichletCharacter ℂ p}
    (hχ : χ ≠ 1) (hψ : ψ ≠ 1) (hχψ : χ*ψ ≠ 1) :
    ‖jacobiSum χ ψ‖ = Real.sqrt p := by
  have hc : star (jacobiSum χ ψ) = jacobiSum χ⁻¹ ψ⁻¹ := by
    simp only [jacobiSum, star_sum, star_mul', MulChar.star_apply']
  have hchar : ringChar ℂ ≠ ringChar (ZMod p) := by
    rw [ZMod.ringChar_zmod_n, ringChar.eq ℂ 0]
    exact hp.out.ne_zero.symm
  have h := congrArg (fun z : ℂ => ‖z‖) (jacobiSum_mul_jacobiSum_inv hchar hχ hψ hχψ)
  simp only [← hc, norm_mul, norm_star, ZMod.card, Complex.norm_natCast] at h
  nlinarith [Real.sq_sqrt (Nat.cast_nonneg p), Real.sqrt_nonneg (p:ℝ), norm_nonneg (jacobiSum χ ψ)]

private theorem localSum_nonzero {p : ℕ} [Fact p.Prime] (χ ψ : DirichletCharacter ℂ p)
    {m : ZMod p} (hm : m ≠ 0) : localSum χ ψ m = (χ m*ψ m)*jacobiSum χ ψ := by
  have h := Equiv.sum_comp (Equiv.mulLeft₀ m hm) (fun a : ZMod p => χ a * ψ (m-a))
  calc
    _ = ∑ a : ZMod p, χ (m*a) * ψ (m-m*a) := h.symm
    _ = ∑ a : ZMod p, (χ m*ψ m)*(χ a*ψ (1-a)) := by
      apply sum_congr rfl
      intro a _
      rw [← mul_one_sub, map_mul, map_mul]
      ring
    _ = _ := (mul_sum ..).symm

private theorem localSum_zero {p : ℕ} [hp : Fact p.Prime] (χ ψ : DirichletCharacter ℂ p) :
    localSum χ ψ 0 = ψ (-1)*(if χ*ψ = 1 then ((p-1 : ℕ) : ℂ) else 0) := by
  classical
  have h : localSum χ ψ 0 = ψ (-1)*∑ a : ZMod p, (χ*ψ) a := by
    unfold localSum
    rw [mul_sum]
    apply sum_congr rfl
    intro a _
    rw [zero_sub, ← neg_one_mul a, map_mul, MulChar.mul_apply]
    ring
  rw [h]
  by_cases hprod : χ*ψ = 1
  · simp only [hprod, ite_true, MulChar.sum_one_eq_card_units, ZMod.card_units_eq_totient,
      Nat.totient_prime hp.out]
  · rw [ite_eq_right hprod, MulChar.sum_eq_zero_of_ne_one hprod]

/-- Complete table, including the primes 2 and 3 and imprimitive local factors. -/
theorem local_norm {p : ℕ} [hp : Fact p.Prime] (χ ψ : DirichletCharacter ℂ p) (m : ZMod p) :
    ‖localSum χ ψ m‖ =
      if m=0 then (if χ*ψ=1 then (p:ℝ)-1 else 0)
      else if χ=1 ∧ ψ=1 then (p:ℝ)-2
      else if χ=1 ∨ ψ=1 ∨ χ*ψ=1 then 1 else Real.sqrt p := by
  classical
  by_cases hm : m=0
  · subst m
    rw [ite_eq_left rfl,localSum_zero,norm_mul,ψ.norm_neg_one,one_mul]
    by_cases h : χ*ψ=1
    · rw [ite_eq_left h,ite_eq_left h,Complex.norm_natCast,Nat.cast_sub hp.out.one_le,Nat.cast_one]
    · simp [h]
  have hu := isUnit_iff_ne_zero.mpr hm
  have v (θ : DirichletCharacter ℂ p) : ‖θ m‖=1 := θ.unit_norm_eq_one hu.unit
  rw [ite_eq_right hm,localSum_nonzero χ ψ hm,norm_mul,norm_mul,
    v χ,v ψ,one_mul,one_mul]
  by_cases hχ : χ=1
  · subst χ
    by_cases hψ : ψ=1
    · subst ψ
      have hpos : (0:ℝ) ≤ p-2 := sub_nonneg.mpr (by exact_mod_cast hp.out.two_le)
      simp only [and_self,ite_true,jacobiSum_one_one,ZMod.card]
      rw [← Complex.ofReal_natCast, ← Complex.ofReal_ofNat 2, ← Complex.ofReal_sub,
        Complex.norm_real, Real.norm_of_nonneg hpos]
    · simp [hψ,jacobiSum_one_nontrivial hψ]
  by_cases hψ : ψ=1
  · subst ψ
    rw [jacobiSum_comm,jacobiSum_one_nontrivial hχ]
    simp [hχ]
  by_cases hprod : χ*ψ=1
  · have hinv : ψ=χ⁻¹ := eq_inv_of_mul_eq_one_right hprod
    simp only [hχ,hψ,hprod,false_and,ite_false,false_or,ite_true]
    rw [hinv,jacobiSum_nontrivial_inv hχ,norm_neg,χ.norm_neg_one]
  · simp [hχ,hψ,hprod,norm_jacobi hχ hψ hprod]

private theorem local_le_principal {p : ℕ} [Fact p.Prime] (χ ψ : DirichletCharacter ℂ p)
    (m : ZMod p) : ‖localSum χ ψ m‖ ≤ ‖localSum (1 : DirichletCharacter ℂ p) 1 m‖ := by
  classical
  let U := univ.filter (fun a : ZMod p => IsUnit a ∧ IsUnit (m-a))
  have restrict (α β : DirichletCharacter ℂ p) :
      (∑ a ∈ U, α a * β (m-a)) = localSum α β m := by
    apply sum_subset (filter_subset _ _)
    intro a _ ha
    by_cases hu : IsUnit a
    · have hv : ¬IsUnit (m-a) := fun hv => ha (mem_filter.mpr ⟨mem_univ _,hu,hv⟩)
      simp [β.map_nonunit hv]
    · simp [α.map_nonunit hu]
  have triv : localSum (1 : DirichletCharacter ℂ p) 1 m = (U.card:ℂ) := by
    rw [← restrict]
    calc
      _ = ∑ _a ∈ U, (1:ℂ) := by
        apply sum_congr rfl
        intro a ha
        obtain ⟨_, hu, hv⟩ := mem_filter.mp ha
        rw [MulChar.one_apply hu,MulChar.one_apply hv,one_mul]
      _ = _ := by simp
  rw [triv,Complex.norm_natCast,← restrict]
  calc
    _ ≤ ∑ a ∈ U, ‖χ a * ψ (m-a)‖ := norm_sum_le _ _
    _ ≤ ∑ _a ∈ U, (1:ℝ) := by
      apply sum_le_sum
      intro a _
      rw [norm_mul]
      exact (mul_le_mul_of_nonneg_right (χ.norm_le_one _) (norm_nonneg _)).trans
        (by simpa only [one_mul] using ψ.norm_le_one (m-a))
    _ = _ := by simp

section Squarefree
variable {k : ℕ} (p : Fin k → ℕ) [∀ i, Fact (p i).Prime] [NeZero (∏ i, p i)]
    (cop : Pairwise (fun i j => (p i).Coprime (p j)))
    (χ ψ : (i : Fin k) → DirichletCharacter ℂ (p i))

/-- The complete sum over one actual residue ring, with both characters
assembled from their components by the Chinese remainder isomorphism. -/
noncomputable def twisted (m : ZMod (∏ i, p i)) : ℂ :=
  let e := ZMod.prodEquivPi p cop
  ∑ a : ZMod (∏ i, p i), (∏ i, χ i (e a i)) * (∏ i, ψ i (e (m-a) i))

theorem factorization (m : ZMod (∏ i, p i)) :
    twisted p cop χ ψ m = ∏ i, localSum (χ i) (ψ i) (ZMod.prodEquivPi p cop m i) := by
  classical
  let e := ZMod.prodEquivPi p cop
  let f (i : Fin k) (a : ZMod (p i)) := χ i a * ψ i (e m i-a)
  have hstep (a : ZMod (∏ i, p i)) :
      (∏ i, χ i (e a i)) * (∏ i, ψ i (e (m-a) i)) = ∏ i, f i (e a i) := by
    rw [← prod_mul_distrib,map_sub]
    rfl
  calc
    _ = ∑ a : ZMod (∏ i, p i), ∏ i, f i (e a i) := sum_congr rfl (fun a _ => hstep a)
    _ = ∑ a : (i : Fin k) → ZMod (p i), ∏ i, f i (a i) :=
      Equiv.sum_comp e.toEquiv (fun a => ∏ i, f i (a i))
    _ = _ := (Fintype.prod_sum f).symm

/-- A nonprincipal component at a prime away from the target costs a factor
of at least two for p ≥ 11. At every other prime the cost is at most one.
The saving therefore multiplies across the *distinct* offending primes. -/
theorem suppression (m : ZMod (∏ i, p i)) :
    let e := ZMod.prodEquivPi p cop
    let B := univ.filter (fun i => 11 ≤ p i ∧ e m i ≠ 0 ∧ (χ i ≠ 1 ∨ ψ i ≠ 1))
    (2:ℝ)^B.card * ‖twisted p cop χ ψ m‖ ≤
      ‖twisted p cop (fun _ => 1) (fun _ => 1) m‖ := by
  classical
  intro e B
  let w (i : Fin k) : ℝ := if i ∈ B then 2 else 1
  have hweight : (∏ i, w i) = (2:ℝ)^B.card := by
    simp [w, Finset.prod_ite_mem]
  rw [← hweight, factorization, factorization, norm_prod, norm_prod, ← prod_mul_distrib]
  apply prod_le_prod₀
  · intro i _
    exact mul_nonneg (by dsimp [w]; split <;> norm_num) (norm_nonneg _)
  · intro i _
    by_cases hi : i ∈ B
    · have ⟨hp,hm,hχψ⟩ := (mem_filter.mp hi).2
      change (ZMod.prodEquivPi p cop) m i ≠ 0 at hm
      have hn : ¬(χ i=1 ∧ ψ i=1) := by tauto
      have hpR : (11:ℝ) ≤ p i := by exact_mod_cast hp
      have hs := Real.sq_sqrt (Nat.cast_nonneg (p i))
      have hroot : 3 ≤ Real.sqrt (p i) := by nlinarith [Real.sqrt_nonneg (p i)]
      have hsmall : 2*Real.sqrt (p i) ≤ p i-2 := by nlinarith [sq_nonneg (Real.sqrt (p i)-3)]
      rw [show w i = 2 by simp [w,hi],local_norm,local_norm]
      simp only [hm,ite_false,hn,ite_true,and_self]
      split <;> linarith
    · rw [show w i = 1 by simp [w,hi],one_mul]
      exact local_le_principal _ _ _

/-- A prime dividing the target kills the entire sum when the two local
characters do not cancel one another on its units. -/
theorem vanishing (m : ZMod (∏ i, p i)) (i : Fin k)
    (hm : ZMod.prodEquivPi p cop m i = 0) (h : χ i * ψ i ≠ 1) :
    twisted p cop χ ψ m = 0 := by
  rw [factorization]
  apply prod_eq_zero (mem_univ i)
  apply norm_eq_zero.mp
  rw [local_norm,ite_eq_left hm,ite_eq_right h]

private theorem dft_convolution {N : ℕ} [NeZero N] (f g : ZMod N → ℂ) :
    ZMod.dft (fun m => ∑ a, f a * g (m-a)) =
      fun t => ZMod.dft f t * ZMod.dft g t := by
  classical
  funext t
  simp only [ZMod.dft_apply,smul_eq_mul]
  calc
    _ = ∑ a, ∑ m : ZMod N, ZMod.stdAddChar (-(m*t)) * (f a*g (m-a)) := by
      simp only [mul_sum]
      rw [sum_comm]
    _ = ∑ a, ∑ b : ZMod N, (ZMod.stdAddChar (-(a*t))*f a) *
        (ZMod.stdAddChar (-(b*t))*g b) := by
      apply sum_congr rfl
      intro a _
      let F (m : ZMod N) := ZMod.stdAddChar (-(m*t)) * (f a*g (m-a))
      calc
        _ = ∑ b : ZMod N, F (a+b) := (Equiv.sum_comp (Equiv.addLeft a) F).symm
        _ = _ := by
          apply sum_congr rfl
          intro b _
          simp only [F,add_sub_cancel_left,add_mul,neg_add_rev,AddChar.map_add_eq_mul]
          ring
    _ = _ := by simp only [sum_mul,mul_sum]; rw [sum_comm]

omit [∀ i, Fact (p i).Prime] in
/-- Normalized inverse Fourier synthesis of the product of the two complete
character sums gives the same finite local density. -/
theorem synthesis (m : ZMod (∏ i, p i)) :
    let e := ZMod.prodEquivPi p cop
    let f := fun a => ∏ i, χ i (e a i)
    let g := fun a => ∏ i, ψ i (e a i)
    ZMod.dft (fun t => ZMod.dft f t * ZMod.dft g t) (-m) =
      ((∏ i, p i : ℕ) : ℂ) * twisted p cop χ ψ m := by
  intro e f g
  rw [← dft_convolution f g,ZMod.dft_dft]
  simp only [neg_neg,smul_eq_mul]
  rfl

end Squarefree
end Conjectures.Goldbach.SharpSingularSeriesRatiosProof.SquarefreeTwistedGoldbachDensity

/-! Complete twisted binary densities on arbitrary residue rings. For a pair of
primitive characters their convolution has exactly the norm of the Fourier
transform of the inverse product character. This also covers imprimitive
products, where the conductor can be much smaller than either input level. -/

namespace Conjectures.Goldbach.SharpSingularSeriesRatiosProof.PrimePowerTwistedGoldbachDensity

open Finset DirichletCharacter
open scoped BigOperators Classical

noncomputable def density {q : ℕ} [NeZero q] (χ ψ : DirichletCharacter ℂ q) (m : ZMod q) :
    ℂ := ∑ a : ZMod q, χ a * ψ (m-a)

private theorem transform {q : ℕ} [NeZero q] (χ ψ : DirichletCharacter ℂ q) :
    ZMod.dft (density χ ψ) = fun t => ZMod.dft χ t * ZMod.dft ψ t := by
  funext t
  rw [fourierTransform_eq_gaussSum_mulShift,fourierTransform_eq_gaussSum_mulShift,gaussSum_mul,
    ZMod.dft_apply]
  apply sum_congr rfl
  intro m _
  rw [← sum_mul,smul_eq_mul,AddChar.mulShift_apply]
  simp only [density,mul_neg,mul_comm]

theorem phase_relation {q : ℕ} [NeZero q] {χ ψ : DirichletCharacter ℂ q}
    (hχ : χ.IsPrimitive) (hψ : ψ.IsPrimitive) (m : ZMod q) :
    (q:ℂ)*density χ ψ m =
      (gaussSum χ ZMod.stdAddChar * gaussSum ψ ZMod.stdAddChar) *
      ZMod.dft (fun t => (χ*ψ)⁻¹ t) m := by
  let G := gaussSum χ ZMod.stdAddChar * gaussSum ψ ZMod.stdAddChar
  have ht : ZMod.dft (density χ ψ) = fun t => G*(χ*ψ)⁻¹ (-t) := by
    rw [transform]
    funext t
    rw [hχ.fourierTransform_eq_inv_mul_gaussSum,hψ.fourierTransform_eq_inv_mul_gaussSum]
    simp only [G,mul_inv,MulChar.mul_apply]
    ring
  have hi := congrFun (ZMod.dft_dft (density χ ψ)) (-m)
  rw [ht,ZMod.dft_const_mul G] at hi
  change G * ZMod.dft (fun t => (χ*ψ)⁻¹ (-t)) (-m) = (q:ℂ) • density χ ψ (- -m) at hi
  rw [ZMod.dft_comp_neg (fun t => (χ*ψ)⁻¹ t)] at hi
  simpa only [neg_neg,smul_eq_mul] using hi.symm

theorem primitive_norm {q : ℕ} [NeZero q] {χ ψ : DirichletCharacter ℂ q}
    (hχ : χ.IsPrimitive) (hψ : ψ.IsPrimitive) (m : ZMod q) :
    ‖density χ ψ m‖ = ‖ZMod.dft (fun t => (χ*ψ)⁻¹ t) m‖ := by
  have h := congrArg (fun z : ℂ => ‖z‖) (phase_relation hχ hψ m)
  simp only [norm_mul,Complex.norm_natCast,norm_gaussSum_stdAddChar hχ,
    norm_gaussSum_stdAddChar hψ,Real.mul_self_sqrt (Nat.cast_nonneg q)] at h
  exact mul_left_cancel₀ (by exact_mod_cast NeZero.ne q : (q:ℝ)≠0) h

theorem primitive_product {q : ℕ} [NeZero q] {χ ψ : DirichletCharacter ℂ q}
    (hχ : χ.IsPrimitive) (hψ : ψ.IsPrimitive) (hprod : (χ*ψ).IsPrimitive) (m : ZMod q) :
    ‖density χ ψ m‖ = if IsUnit m then Real.sqrt q else 0 := by
  rw [primitive_norm hχ hψ]
  change ‖ZMod.dft (⇑((χ*ψ)⁻¹)) m‖ = _
  rw [hprod.inv.fourierTransform_eq_inv_mul_gaussSum,norm_mul,norm_gaussSum_stdAddChar hprod.inv,
    inv_inv]
  by_cases hm : IsUnit m
  · have h : ‖(χ*ψ) (-m)‖ = 1 := (χ*ψ).unit_norm_eq_one hm.neg.unit
    rw [ite_eq_left hm,h,one_mul]
  · rw [ite_eq_right hm,MulChar.map_nonunit _ (by simpa using hm : ¬ IsUnit (-m)),norm_zero,zero_mul]

open B13BilateralVaughanReductionProof

private theorem lifted_character {d f : ℕ} [NeZero d] [NeZero f]
    (support : ∀ a : ℕ, a.Coprime d → a.Coprime f) (θ : DirichletCharacter ℂ d) (a : ℕ) :
    changeLevel (dvd_mul_right d f) θ (a : ZMod (d*f)) = θ (a : ZMod d) := by
  rw [DyadicMixedB4MoebiusGauss.changeLevel_nat_indicator]
  by_cases h : a.Coprime d
  · rw [ite_eq_left (Nat.coprime_mul_iff_right.mpr ⟨h,support a h⟩),one_mul]
  · have hz : θ (a : ZMod d)=0 := θ.map_nonunit (fun hu => h ((ZMod.isUnit_iff_coprime a d).mp hu))
    simp only [hz,mul_zero]

/-- Exact Fourier support of a lifted character whenever the larger modulus
has the same prime support. Lifting introduces a divisibility condition on the
frequency and multiplies the surviving lower-level Gauss sum by the fiber size. -/
theorem lifted_gauss {d f : ℕ} [NeZero d] [NeZero f] [NeZero (d*f)]
    (support : ∀ a : ℕ, a.Coprime d → a.Coprime f) (θ : DirichletCharacter ℂ d) (k : ℕ) :
    gaussSum (changeLevel (dvd_mul_right d f) θ) (ZMod.stdAddChar.mulShift (k : ZMod (d*f))) =
      if f ∣ k then (f:ℂ)*gaussSum θ (ZMod.stdAddChar.mulShift ((k/f : ℕ) : ZMod d)) else 0 := by
  rw [DyadicMixedB4GaussLift.gaussSum_as_fraction_sum]
  simp only [lifted_character support,Nat.cast_mul]
  exact DyadicMixedB4GaussLift.lift_gaussSum θ k

private theorem neg_frequency {q : ℕ} [NeZero q] {χ ψ : DirichletCharacter ℂ q}
    (hχ : χ.IsPrimitive) (hψ : ψ.IsPrimitive) (k : ℕ) :
    ‖density χ ψ (-(k : ZMod q))‖ =
      ‖gaussSum (χ*ψ)⁻¹ (ZMod.stdAddChar.mulShift (k : ZMod q))‖ := by
  rw [primitive_norm hχ hψ]
  simp only [fourierTransform_eq_gaussSum_mulShift,neg_neg]

private theorem primitive_gauss {d : ℕ} [NeZero d] {θ : DirichletCharacter ℂ d}
    (hθ : θ.IsPrimitive) (a : ℕ) :
    ‖gaussSum θ (ZMod.stdAddChar.mulShift (a : ZMod d))‖ =
      if a.Coprime d then Real.sqrt d else 0 := by
  rw [gaussSum_mulShift_of_isPrimitive ZMod.stdAddChar hθ,norm_mul,norm_gaussSum_stdAddChar hθ]
  by_cases ha : a.Coprime d
  · rw [ite_eq_left ha]
    have v : ‖θ⁻¹ (a : ZMod d)‖=1 := θ⁻¹.unit_norm_eq_one (ZMod.unitOfCoprime a ha)
    rw [v,one_mul]
  · rw [ite_eq_right ha,MulChar.map_nonunit _ (fun hu => ha ((ZMod.isUnit_iff_coprime a d).mp hu)),
      norm_zero,zero_mul]

/-- Thin-shell support for a primitive pair whose product is induced from a
primitive character of positive level with the same prime factors. -/
theorem conductor_shell {d f : ℕ} [NeZero d] [NeZero f] [NeZero (d*f)]
    (support : ∀ a : ℕ, a.Coprime d → a.Coprime f)
    {χ ψ : DirichletCharacter ℂ (d*f)} (hχ : χ.IsPrimitive) (hψ : ψ.IsPrimitive)
    {θ : DirichletCharacter ℂ d} (hθ : θ.IsPrimitive)
    (lift : (χ*ψ)⁻¹ = changeLevel (dvd_mul_right d f) θ) (k : ℕ) :
    ‖density χ ψ (-(k : ZMod (d*f)))‖ =
      if f ∣ k ∧ (k/f).Coprime d then (f:ℝ)*Real.sqrt d else 0 := by
  rw [neg_frequency hχ hψ,lift,lifted_gauss support]
  by_cases h : f ∣ k
  · rw [ite_eq_left h,norm_mul,Complex.norm_natCast,primitive_gauss hθ]
    by_cases hc : (k/f).Coprime d <;> simp [h,hc]
  · simp [h]

/-- Primitive and properly lifted characters have disjoint Fourier supports if
no new prime divides the larger level. Their convolution vanishes at every
target, even the zero target. -/
theorem mixed_vanishes {d f : ℕ} [NeZero d] [NeZero f] [NeZero (d*f)]
    (hf : 1 < f) (support : ∀ a : ℕ, a.Coprime d → a.Coprime f)
    {χ : DirichletCharacter ℂ (d*f)} (hχ : χ.IsPrimitive) (ψ : DirichletCharacter ℂ d)
    (m : ZMod (d*f)) : density χ (changeLevel (dvd_mul_right d f) ψ) m = 0 := by
  have ht : ZMod.dft (density χ (changeLevel (dvd_mul_right d f) ψ)) = 0 := by
    rw [transform]
    funext t
    rw [hχ.fourierTransform_eq_inv_mul_gaussSum,fourierTransform_eq_gaussSum_mulShift]
    by_cases hu : IsUnit (-t)
    · let a := (-t).val
      have ha : (a : ZMod (d*f)) = -t := ZMod.natCast_zmod_val _
      have hc : a.Coprime (d*f) := (ZMod.isUnit_iff_coprime a (d*f)).mp (ha.symm ▸ hu)
      have hn : ¬ f ∣ a := fun hd => hf.ne' (Nat.eq_one_of_dvd_coprimes hc hd (dvd_mul_left f d))
      rw [← ha,lifted_gauss support,ite_eq_right hn,mul_zero]
      rfl
    · rw [MulChar.map_nonunit _ hu,zero_mul,zero_mul]
      rfl
  have h := ZMod.dft.injective (ht.trans ZMod.dft.map_zero.symm)
  exact congrFun h m

private theorem prime_gauss_one {p : ℕ} [hp : Fact p.Prime] (a : ℕ) :
    gaussSum (1 : DirichletCharacter ℂ p) (ZMod.stdAddChar.mulShift (a : ZMod p)) =
      if p ∣ a then ((p-1 : ℕ):ℂ) else -1 := by
  by_cases h : p ∣ a
  · rw [ite_eq_left h,(ZMod.natCast_eq_zero_iff a p).mpr h,AddChar.mulShift_zero,gaussSum_one_one,
      Nat.card_eq_fintype_card,ZMod.card_units_eq_totient,Nat.totient_prime hp.out]
  · rw [ite_eq_right h]
    exact gaussSum_one_left (ZMod.isPrimitive_stdAddChar p (fun z => h ((ZMod.natCast_eq_zero_iff a p).mp z)))

/-- The remaining (principal product) case gives the exact prime-power
Ramanujan magnitude, including at multiples of the whole modulus. -/
theorem principal_product_power {p : ℕ} [hp : Fact p.Prime] (j : ℕ)
    {χ ψ : DirichletCharacter ℂ (p*p^j)} (hχ : χ.IsPrimitive) (hψ : ψ.IsPrimitive)
    (invpair : χ*ψ=1) (k : ℕ) :
    ‖density χ ψ (-(k : ZMod (p*p^j)))‖ =
      if p^j ∣ k then ((p^j:ℕ):ℝ) * (if p ∣ k/p^j then (p:ℝ)-1 else 1) else 0 := by
  rw [neg_frequency hχ hψ,invpair,inv_one]
  have lift : (1 : DirichletCharacter ℂ (p*p^j)) =
      changeLevel (dvd_mul_right p (p^j)) (1 : DirichletCharacter ℂ p) := (map_one _).symm
  rw [lift,lifted_gauss (fun a (h : a.Coprime p) => h.pow_right j)]
  by_cases h : p^j ∣ k
  · rw [ite_eq_left h,ite_eq_left h,norm_mul,Complex.norm_natCast,prime_gauss_one]
    by_cases hq : p ∣ k/p^j
    · rw [ite_eq_left hq,ite_eq_left hq,Complex.norm_natCast,Nat.cast_sub hp.out.one_le,Nat.cast_one]
    · simp [hq]
  · simp [h]

/-- Reflection of the target changes only the phase, for arbitrary characters. -/
theorem reflected {q : ℕ} [NeZero q] (χ ψ : DirichletCharacter ℂ q) (m : ZMod q) :
    ‖density χ ψ (-m)‖ = ‖density χ ψ m‖ := by
  have h : density χ ψ (-m) = (χ (-1)*ψ (-1))*density χ ψ m := by
    let F (a : ZMod q) := χ a * ψ (-m-a)
    calc
      _ = ∑ a : ZMod q, F (-a) := (Equiv.sum_comp (Equiv.neg _) F).symm
      _ = ∑ a : ZMod q, (χ (-1)*ψ (-1))*(χ a*ψ (m-a)) := by
        apply sum_congr rfl
        intro a _
        change χ (-a) * ψ (-m - -a) = _
        rw [show -m - -a = (-1)*(m-a) by ring,← neg_one_mul a,map_mul,map_mul]
        ring
      _ = _ := (mul_sum ..).symm
  rw [h,norm_mul,norm_mul,χ.norm_neg_one,ψ.norm_neg_one,one_mul,one_mul]

private theorem shell_at_level {d q : ℕ} [NeZero d] [NeZero q] (hd : d ∣ q)
    (support : ∀ a : ℕ, a.Coprime d → a.Coprime (q/d))
    {χ ψ : DirichletCharacter ℂ q} (hχ : χ.IsPrimitive) (hψ : ψ.IsPrimitive)
    {θ : DirichletCharacter ℂ d} (hθ : θ.IsPrimitive) (lift : (χ*ψ)⁻¹=changeLevel hd θ) (k : ℕ) :
    ‖density χ ψ (k : ZMod q)‖ =
      if q/d ∣ k ∧ (k/(q/d)).Coprime d then ((q/d:ℕ):ℝ)*Real.sqrt d else 0 := by
  obtain ⟨f,rfl⟩ := hd
  have hf : NeZero f := ⟨fun h => NeZero.ne (d*f) (by simp [h])⟩
  have hr : d*f/d=f := Nat.mul_div_cancel_left f (NeZero.pos d)
  rw [hr,← reflected]
  exact conductor_shell (by simpa only [hr] using support) hχ hψ hθ lift k

private theorem conductor_coprime {p d : ℕ} [hp : Fact p.Prime] (j : ℕ)
    (hd : d ∣ p*p^j) (hne : d≠1) {a : ℕ} (ha : a.Coprime d) : a.Coprime ((p*p^j)/d) := by
  have he : p*p^j=p^(j+1) := by ring
  rw [he] at hd ⊢
  obtain ⟨b,_,hb⟩ := (Nat.dvd_prime_pow hp.out).mp hd
  have hbpos : 0<b := by by_contra! hh; simp [hb, show b=0 by omega] at hne
  have hpa : a.Coprime p := (Nat.coprime_pow_right_iff hbpos _ _).mp (hb ▸ ha)
  exact (hpa.pow_right (j+1)).of_dvd_right (Nat.div_dvd_of_dvd hd)

/-- Complete prime-power norm when both characters are primitive.
The exceptional shell is determined by the conductor of their inverse product. -/
theorem prime_power_table {p : ℕ} [hp : Fact p.Prime] (j : ℕ)
    (χ ψ : DirichletCharacter ℂ (p*p^j)) (hχ : χ.IsPrimitive) (hψ : ψ.IsPrimitive) (k : ℕ) :
    let d := ((χ*ψ)⁻¹).conductor
    let f := (p*p^j)/d
    ‖density χ ψ (k : ZMod (p*p^j))‖ = if χ*ψ=1 then
      (if p^j ∣ k then ((p^j:ℕ):ℝ)*(if p ∣ k/p^j then (p:ℝ)-1 else 1) else 0)
      else if f ∣ k ∧ (k/f).Coprime d then (f:ℝ)*Real.sqrt d else 0 := by
  intro d f
  by_cases h : χ*ψ=1
  · rw [ite_eq_left h,← reflected]
    exact principal_product_power j hχ hψ h k
  rw [ite_eq_right h]
  let θ := (χ*ψ)⁻¹
  let _ : NeZero d := ⟨fun hzero => NeZero.ne (p*p^j) (conductor_eq_zero_iff_level_eq_zero.mp hzero)⟩
  have hd : d ∣ p*p^j := θ.conductor_dvd_level
  have hd1 : d≠1 := by
    intro h1
    have hθ : θ=1 := (eq_one_iff_conductor_eq_one (χ := θ)).mpr h1
    exact h (inv_eq_one.mp hθ)
  exact shell_at_level hd (fun _ ha => conductor_coprime j hd hd1 ha) hχ hψ
    θ.primitiveCharacter_isPrimitive θ.changeLevel_primitiveCharacter.symm k

private theorem lift_residue {d f : ℕ} [NeZero d] [NeZero f] [NeZero (d*f)]
    (support : ∀ a : ℕ, a.Coprime d → a.Coprime f) (θ : DirichletCharacter ℂ d)
    (z : ZMod (d*f)) : changeLevel (dvd_mul_right d f) θ z =
      θ (ZMod.castHom (dvd_mul_right d f) (ZMod d) z) := by
  have h := lifted_character support θ z.val
  simpa only [← map_natCast (ZMod.castHom (dvd_mul_right d f) (ZMod d)), ZMod.natCast_zmod_val] using h

/-- When both characters descend, the density at the higher level is exactly
the fiber size times the lower-level density, with the target reduced as well. -/
theorem both_lifted {d f : ℕ} [NeZero d] [NeZero f] [NeZero (d*f)]
    (support : ∀ a : ℕ, a.Coprime d → a.Coprime f) (χ ψ : DirichletCharacter ℂ d)
    (m : ZMod (d*f)) :
    density (changeLevel (dvd_mul_right d f) χ) (changeLevel (dvd_mul_right d f) ψ) m =
      (f:ℂ)*density χ ψ (ZMod.castHom (dvd_mul_right d f) (ZMod d) m) := by
  let π := ZMod.castHom (dvd_mul_right d f) (ZMod d)
  unfold density
  rw [← DyadicMixedB4DualCharacter.sum_natCast_range_eq_zmod]
  simp only [lift_residue support,map_natCast,map_sub]
  rw [DyadicMixedB4GaussLift.sum_range_blocks]
  simp only [Nat.cast_add,Nat.cast_mul,ZMod.natCast_self,zero_mul,zero_add,sum_const,card_range,
    nsmul_eq_mul]
  exact congrArg (fun z : ℂ => (f:ℂ)*z) (DyadicMixedB4DualCharacter.sum_natCast_range_eq_zmod
    (fun a : ZMod d => χ a * ψ (π m - a)))

end Conjectures.Goldbach.SharpSingularSeriesRatiosProof.PrimePowerTwistedGoldbachDensity

/-! Factor the full complex singular series of two primitive source characters
through the local components of their actual common-level characters. -/

namespace Conjectures.Goldbach.SharpSingularSeriesRatiosProof.TwistedGoldbachLocalProduct

open Finset DirichletCharacter TwistedGoldbachConductorRatio
open scoped BigOperators Classical

noncomputable def series {r s : ℕ} (α : DirichletCharacter ℂ r)
    (β : DirichletCharacter ℂ s) (m : ℕ) : ℂ :=
  ∑' d : ℕ, TwistedGoldbachSingularSeries.coefficient α β m d

section Coordinates
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {q : ι → ℕ} [∀ i, NeZero (q i)]
  {L : ℕ} [NeZero L] (e : ZMod L ≃+* ∀ i, ZMod (q i))

/-- Restrict a common-level character to the units at one CRT coordinate.
The same formula extends it by zero on nonunits. -/
noncomputable def component (χ : DirichletCharacter ℂ L) (i : ι) : DirichletCharacter ℂ (q i) where
  toFun x := χ (e.symm (Pi.mulSingle i x))
  map_one' := by simp
  map_mul' x y := by simp only [Pi.mulSingle_mul,map_mul]
  map_nonunit' x hx := χ.map_nonunit (by
    intro hu
    have h := (hu.map e).map (Pi.evalRingHom (fun j => ZMod (q j)) i)
    exact hx (by simpa using h))

omit [Fintype ι] [∀ i, NeZero (q i)] [NeZero L] in
theorem component_one (i : ι) : component e (1 : DirichletCharacter ℂ L) i = 1 := by
  apply MulChar.ext
  intro u
  have hu := (u.isUnit.map (MonoidHom.mulSingle (fun j => ZMod (q j)) i)).map e.symm
  simp only [MonoidHom.mulSingle_apply] at hu
  change (1 : DirichletCharacter ℂ L) (e.symm (Pi.mulSingle i (u:ZMod (q i)))) = _
  rw [MulChar.one_apply hu,MulChar.one_apply u.isUnit]

omit [∀ i, NeZero (q i)] [NeZero L] in
theorem reassemble (χ : DirichletCharacter ℂ L) (x : ZMod L) :
    χ x = ∏ i, component e χ i (e x i) := by
  change χ x = ∏ i, χ (e.symm (Pi.mulSingle i (e x i)))
  rw [← map_prod,← map_prod,Finset.univ_prod_mulSingle,e.symm_apply_apply]

/-- Factor the convolution itself, including every phase. -/
theorem local_factors (A B : DirichletCharacter ℂ L) (m : ℕ) :
    J A B (m:ZMod L) = ∏ i, J (component e A i) (component e B i) (m:ZMod (q i)) := by
  let f (i : ι) (x : ZMod (q i)) := component e A i x * component e B i ((m:ZMod (q i))-x)
  have step (x : ZMod L) : A x * B ((m:ZMod L)-x) = ∏ i, f i (e x i) := by
    rw [reassemble e A x,reassemble e B ((m:ZMod L)-x),← prod_mul_distrib,map_sub,map_natCast]
    rfl
  calc
    _ = ∑ x : ZMod L, ∏ i, f i (e x i) := sum_congr rfl (fun x _ => step x)
    _ = ∑ x : ∀ i, ZMod (q i), ∏ i, f i (x i) :=
      Equiv.sum_comp e.toEquiv (fun x => ∏ i, f i (x i))
    _ = _ := (Fintype.prod_sum f).symm

theorem principal_ne_zero (d m : ℕ) [NeZero d] (he : Even m) :
    J (1 : DirichletCharacter ℂ d) 1 (m:ZMod d) ≠ 0 := by
  obtain ⟨x,hx⟩ := admissible_even d m he
  rw [principal_card]
  exact Nat.cast_ne_zero.mpr (card_pos.mpr ⟨x,mem_filter.mpr ⟨mem_univ _,hx⟩⟩).ne'

/-- Exact Euler product for the correction to the ordinary singular series,
over any CRT decomposition, including prime powers with unequal conductors. -/
theorem full_product {r s : ℕ} [NeZero r] [NeZero s] {α : DirichletCharacter ℂ r}
    {β : DirichletCharacter ℂ s} (hα : α.IsPrimitive) (hβ : β.IsPrimitive)
    (hr : r ∣ L) (hs : s ∣ L) (m : ℕ) (hm : 0 < m) (he : Even m) :
    series α β m = series (1 : DirichletCharacter ℂ 1) (1 : DirichletCharacter ℂ 1) m *
      ∏ i, (J (component e (changeLevel hr α) i) (component e (changeLevel hs β) i) (m:ZMod (q i)) /
        J (1 : DirichletCharacter ℂ (q i)) 1 (m:ZMod (q i))) := by
  have h := conductor_identity hα hβ hr hs m hm
  rw [local_factors e (1 : DirichletCharacter ℂ L) 1,local_factors e (changeLevel hr α) (changeLevel hs β)] at h
  simp only [component_one] at h
  rw [prod_div_distrib,← mul_div_assoc,eq_div_iff (prod_ne_zero_iff.mpr (fun i _ => principal_ne_zero (q i) m he))]
  exact h

/-- A noninverse pair at any single CRT factor dividing the target kills the
entire series, even if all the other conductor factors are coprime to it. -/
theorem vanished_factor {r s : ℕ} [NeZero r] [NeZero s] {α : DirichletCharacter ℂ r}
    {β : DirichletCharacter ℂ s} (hα : α.IsPrimitive) (hβ : β.IsPrimitive)
    (hr : r ∣ L) (hs : s ∣ L) (m : ℕ) (hm : 0 < m) (he : Even m) (i : ι)
    (hdiv : q i ∣ m)
    (hne : component e (changeLevel hr α) i * component e (changeLevel hs β) i ≠ 1) :
    series α β m = 0 := by
  rw [full_product e hα hβ hr hs m hm he]
  apply mul_eq_zero_of_right
  apply prod_eq_zero (mem_univ i)
  rw [(ZMod.natCast_eq_zero_iff m (q i)).mpr hdiv,zero_jacobi,ite_eq_right hne,zero_div]

private theorem ratio_le_one {d : ℕ} [NeZero d] (A B : DirichletCharacter ℂ d)
    (m : ℕ) (he : Even m) :
    ‖J A B (m:ZMod d) / J (1 : DirichletCharacter ℂ d) 1 (m:ZMod d)‖ ≤ 1 := by
  rw [norm_div,div_le_one (norm_pos_iff.mpr (principal_ne_zero d m he))]
  exact TwistedGoldbachSingularSeries.chars_le_units A B _

private theorem simple_saving {p : ℕ} [hp : Fact p.Prime] (A B : DirichletCharacter ℂ p)
    (m : ℕ) (hmp : ¬ p ∣ m) (hab : A ≠ 1 ∨ B ≠ 1) :
    ‖J A B (m:ZMod p) / J (1 : DirichletCharacter ℂ p) 1 (m:ZMod p)‖ ≤
      Real.sqrt p / ((p:ℝ)-2) := by
  have hm0 : (m:ZMod p) ≠ 0 := fun h => hmp ((ZMod.natCast_eq_zero_iff m p).mp h)
  have hn : ¬(A=1 ∧ B=1) := by tauto
  have ht := SquarefreeTwistedGoldbachDensity.local_norm A B (m:ZMod p)
  have ht0 := SquarefreeTwistedGoldbachDensity.local_norm (1 : DirichletCharacter ℂ p) 1 (m:ZMod p)
  simp only [hm0,ite_false,hn] at ht
  simp only [hm0,ite_false,and_self,ite_true] at ht0
  change ‖SquarefreeTwistedGoldbachDensity.localSum A B (m:ZMod p) /
    SquarefreeTwistedGoldbachDensity.localSum (1 : DirichletCharacter ℂ p) 1 (m:ZMod p)‖ ≤ _
  rw [norm_div,ht,ht0]
  apply div_le_div_of_nonneg_right _ (sub_nonneg.mpr (by exact_mod_cast hp.out.two_le))
  split_ifs
  · exact (Real.one_le_sqrt.mpr (by exact_mod_cast hp.out.one_le))
  · exact le_rfl

/-- Multiplicative saving from any collection of distinct prime CRT
coordinates away from the target with a nontrivial character component. The
complementary factors may be prime powers or arbitrary composite factors. -/
theorem prime_suppression {r s : ℕ} [NeZero r] [NeZero s] {α : DirichletCharacter ℂ r}
    {β : DirichletCharacter ℂ s} (hα : α.IsPrimitive) (hβ : β.IsPrimitive)
    (hr : r ∣ L) (hs : s ∣ L) (m : ℕ) (hm : 0 < m) (he : Even m)
    (T : Finset ι) (good : ∀ i ∈ T, (q i).Prime ∧ 5 ≤ q i ∧ ¬q i ∣ m ∧
      (component e (changeLevel hr α) i ≠ 1 ∨ component e (changeLevel hs β) i ≠ 1)) :
    ‖series α β m‖ ≤ ‖series (1 : DirichletCharacter ℂ 1) (1 : DirichletCharacter ℂ 1) m‖ *
      ∏ i ∈ T, Real.sqrt (q i) / ((q i:ℝ)-2) := by
  let w (i : ι) : ℝ := if i ∈ T then Real.sqrt (q i) / ((q i:ℝ)-2) else 1
  have weights : (∏ i, w i) = ∏ i ∈ T, Real.sqrt (q i) / ((q i:ℝ)-2) := by
    simp [w,prod_ite_mem]
  rw [full_product e hα hβ hr hs m hm he,norm_mul,norm_prod,← weights]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  apply prod_le_prod₀ (fun _ _ => norm_nonneg _)
  intro i _
  by_cases hi : i ∈ T
  · obtain ⟨hp,_,hd,hn⟩ := good i hi
    let _ : Fact (q i).Prime := ⟨hp⟩
    rw [show w i = _ from ite_eq_left hi]
    exact simple_saving _ _ m hd hn
  · rw [show w i = 1 from ite_eq_right hi]
    exact ratio_le_one _ _ m he

end Coordinates

theorem ordinary_prime_power {p : ℕ} [hp : Fact p.Prime] (j m : ℕ) :
    ‖J (1 : DirichletCharacter ℂ (p*p^j)) 1 (m:ZMod (p*p^j))‖ =
      ((p^j:ℕ):ℝ) * (if p ∣ m then (p:ℝ)-1 else (p:ℝ)-2) := by
  have h := PrimePowerTwistedGoldbachDensity.both_lifted (d := p) (f := p^j)
    (fun a (ha : a.Coprime p) => ha.pow_right j) (1 : DirichletCharacter ℂ p) 1 (m:ZMod (p*p^j))
  simp only [map_one,map_natCast] at h
  have here := SquarefreeTwistedGoldbachDensity.local_norm (1 : DirichletCharacter ℂ p) 1 (m:ZMod p)
  simp only [one_mul,and_self,ite_true,ZMod.natCast_eq_zero_iff] at here
  change ‖PrimePowerTwistedGoldbachDensity.density (1 : DirichletCharacter ℂ p) 1 (m:ZMod p)‖ = _ at here
  change ‖PrimePowerTwistedGoldbachDensity.density (1 : DirichletCharacter ℂ (p*p^j)) 1 (m:ZMod (p*p^j))‖ = _
  rw [h,norm_mul,Complex.norm_natCast,here]

/-- Complete norm table for the infinite twisted series at a pair of
primitive prime-power conductors. Clearing the ordinary local count makes
the formula valid even at odd targets and at the prime two. -/
theorem prime_power_shell {p : ℕ} [hp : Fact p.Prime] (j : ℕ)
    (A B : DirichletCharacter ℂ (p*p^j)) (hA : A.IsPrimitive) (hB : B.IsPrimitive)
    (m : ℕ) (hm : 0 < m) :
    let d := ((A*B)⁻¹).conductor
    let f := (p*p^j)/d
    ‖series A B m‖ * (((p^j:ℕ):ℝ) * (if p ∣ m then (p:ℝ)-1 else (p:ℝ)-2)) =
      ‖series (1 : DirichletCharacter ℂ 1) (1 : DirichletCharacter ℂ 1) m‖ *
        (if A*B=1 then
          (if p^j ∣ m then ((p^j:ℕ):ℝ) * (if p ∣ m/p^j then (p:ℝ)-1 else 1) else 0)
         else if f ∣ m ∧ (m/f).Coprime d then (f:ℝ)*Real.sqrt d else 0) := by
  have h := congrArg (fun z : ℂ => ‖z‖)
    (conductor_identity hA hB (dvd_refl _) (dvd_refl _) m hm)
  simp only [norm_mul,changeLevel_self,ordinary_prime_power] at h
  have table := PrimePowerTwistedGoldbachDensity.prime_power_table j A B hA hB m
  change ‖J A B (m:ZMod (p*p^j))‖ = _ at table
  rw [table] at h
  exact h

/-- At a unit target and a repeated prime, only a primitive product can
survive. Its magnitude has an extra square-root saving with each level. -/
theorem unit_prime_power {p : ℕ} [hp : Fact p.Prime] (j : ℕ) (hj : 0 < j)
    (A B : DirichletCharacter ℂ (p*p^j)) (hA : A.IsPrimitive) (hB : B.IsPrimitive)
    (m : ℕ) (hm : 0 < m) (hmp : ¬p ∣ m) :
    ‖series A B m‖ * (((p^j:ℕ):ℝ) * ((p:ℝ)-2)) =
      ‖series (1 : DirichletCharacter ℂ 1) (1 : DirichletCharacter ℂ 1) m‖ *
        (if ((A*B)⁻¹).conductor = p*p^j then Real.sqrt (p*p^j:ℕ) else 0) := by
  let Q := p*p^j
  let d := ((A*B)⁻¹).conductor
  have hd : d ∣ Q := ((A*B)⁻¹).conductor_dvd_level
  have hpQ : p ∣ Q := dvd_mul_right p (p^j)
  have hQ : 0 < Q := Nat.mul_pos hp.out.pos (pow_pos hp.out.pos _)
  have mp : m.Coprime p := (hp.out.coprime_iff_not_dvd.mpr hmp).symm
  have mQ := mp.mul_right (mp.pow_right j)
  have nf : Q/d ∣ m → d=Q := by
    intro h
    have one := Nat.eq_one_of_dvd_coprimes mQ h (Nat.div_dvd_of_dvd hd)
    have cancel := Nat.div_mul_cancel hd
    simpa only [one,one_mul] using cancel
  have table := prime_power_shell j A B hA hB m hm
  dsimp only at table
  rw [ite_eq_right hmp] at table
  rw [table]
  congr 1
  change (if A*B=1 then _ else if Q/d ∣ m ∧ (m/(Q/d)).Coprime d then _ else 0) =
    (if d=Q then _ else 0)
  by_cases invpair : A*B=1
  · have d1 : d=1 := (eq_one_iff_conductor_eq_one (χ := (A*B)⁻¹)).mp (by rw [invpair,inv_one])
    have neq : d ≠ Q := by
      intro h
      have h1 : p ∣ 1 := by simpa only [← h,d1] using hpQ
      exact hp.out.not_dvd_one h1
    have nopow : ¬p^j ∣ m := fun h => hmp ((dvd_pow_self p hj.ne').trans h)
    simp only [invpair,ite_true,neq,ite_false,nopow]
  rw [ite_eq_right invpair]
  by_cases same : d=Q
  · have red : Q/d=1 := by rw [same,Nat.div_self hQ]
    have hc : m.Coprime d := by rw [same]; exact mQ
    have hs : Q/d ∣ m ∧ (m/(Q/d)).Coprime d := by simpa only [red,one_dvd,Nat.div_one,true_and] using hc
    rw [ite_eq_left hs,ite_eq_left same,red,Nat.cast_one,one_mul]
    exact congrArg (fun a : ℕ => Real.sqrt a) same
  · have cannot : ¬(Q/d ∣ m ∧ (m/(Q/d)).Coprime d) := fun h => same (nf h.1)
    simp only [cannot,ite_false,same]

end Conjectures.Goldbach.SharpSingularSeriesRatiosProof.TwistedGoldbachLocalProduct

/-! The primitive/principal pair contributing to the exceptional-zero
formula has an elementary exact numerator, including its phase. -/

namespace Conjectures.Goldbach.SharpSingularSeriesRatiosProof.TwistedGoldbachMixedPrincipal

open Finset DirichletCharacter TwistedGoldbachConductorRatio TwistedGoldbachLocalProduct
open scoped BigOperators Classical
open B13BilateralVaughanReductionProof

private theorem principal_gauss (r : ℕ) [NeZero r] :
    gaussSum (1 : DirichletCharacter ℂ r) ZMod.stdAddChar = (ArithmeticFunction.moebius r : ℂ) := by
  by_cases one : r=1
  · subst r
    have trivial : (ZMod.stdAddChar : AddChar (ZMod 1) ℂ) = 1 := by
      ext x
      rw [show x=0 from Subsingleton.elim _ _]
      simp
    rw [trivial,gaussSum_one_one,Nat.card_eq_fintype_card,ZMod.card_units_eq_totient]
    norm_num
  have lower : 1 < r := by have := NeZero.pos r; omega
  have h := DyadicMixedB4Ramanujan.ramanujan_moebius lower 1
  rw [DyadicMixedB4Ramanujan.ramanujan_natural_gauss lower] at h
  simp only [Nat.cast_one,AddChar.mulShift_one] at h
  rw [h,sum_eq_single_of_mem r (Nat.mem_divisors_self _ (NeZero.ne r))]
  · simp [DyadicMixedB4MoebiusGauss.moebiusComplex,Nat.div_self (NeZero.pos r)]
  · intro d hd hne
    have h : ¬r/d ∣ 1 := by
      intro hone
      have he := Nat.eq_one_of_dvd_one hone
      apply hne
      simpa only [he,one_mul] using Nat.div_mul_cancel (Nat.mem_divisors.mp hd).1
    simp [h]

/-- The binary convolution of a primitive character with the principal
character equals the original character multiplied by the Möbius function of
its conductor. This identity holds on every residue, including nonunits. -/
theorem mixed_jacobi {r : ℕ} [NeZero r] (χ : DirichletCharacter ℂ r) (hχ : χ.IsPrimitive)
    (m : ZMod r) : J χ 1 m = (ArithmeticFunction.moebius r:ℂ)*χ m := by
  have conv : ZMod.dft (J χ 1) = fun t => ZMod.dft χ t * ZMod.dft (1 : DirichletCharacter ℂ r) t := by
    funext t
    rw [fourierTransform_eq_gaussSum_mulShift,fourierTransform_eq_gaussSum_mulShift,gaussSum_mul,
      ZMod.dft_apply]
    apply sum_congr rfl
    intro y _
    rw [← sum_mul,smul_eq_mul,AddChar.mulShift_apply]
    simp only [J,mul_neg,mul_comm]
  have eqn : J χ 1 = fun y => (ArithmeticFunction.moebius r:ℂ)*χ y := by
    apply ZMod.dft.injective
    rw [conv,ZMod.dft_const_mul]
    funext t
    by_cases hu : IsUnit (-t)
    · have shift := gaussSum_mulShift_eq (1 : DirichletCharacter ℂ r) ZMod.stdAddChar hu.unit
      simp only [hu.unit_spec,inv_one,MulChar.one_apply hu,one_mul,principal_gauss] at shift
      rw [fourierTransform_eq_gaussSum_mulShift (1 : DirichletCharacter ℂ r),shift,mul_comm]
    · rw [hχ.fourierTransform_eq_inv_mul_gaussSum,(χ⁻¹).map_nonunit hu,zero_mul,zero_mul,mul_zero]
  exact congrFun eqn m

/-- The full mixed series, with no unsummed denominator terms. -/
theorem mixed_exact {r : ℕ} [NeZero r] (χ : DirichletCharacter ℂ r) (hχ : χ.IsPrimitive)
    (m : ℕ) (hm : 0 < m) :
    series χ (1 : DirichletCharacter ℂ 1) m * J (1 : DirichletCharacter ℂ r) 1 (m:ZMod r) =
      series (1 : DirichletCharacter ℂ 1) (1 : DirichletCharacter ℂ 1) m *
        ((ArithmeticFunction.moebius r:ℂ)*χ (m:ZMod r)) := by
  have h := conductor_identity (β := (1 : DirichletCharacter ℂ 1)) hχ isPrimitive_one_level_one
    (dvd_refl r) (one_dvd r) m hm
  simpa only [series,changeLevel_self,map_one,mixed_jacobi χ hχ] using h

noncomputable def localWeight (m p : ℕ) : ℝ :=
  if p ∣ m then (p:ℝ)/((p:ℝ)-1) else (p:ℝ)*((p:ℝ)-2)/((p:ℝ)-1)^2

noncomputable def ordinaryWeight (q m : ℕ) [NeZero q] : ℝ :=
  (q:ℝ) * ‖J (1 : DirichletCharacter ℂ q) 1 (m:ZMod q)‖ / (q.totient:ℝ)^2

private theorem weight_prime_power {p : ℕ} [hp : Fact p.Prime] (a m : ℕ) (ha : 0 < a) :
    ordinaryWeight (p^a) m = localWeight m p := by
  obtain ⟨j,rfl⟩ := Nat.exists_eq_succ_of_ne_zero ha.ne'
  have fpos : (0:ℝ) < ((p^j:ℕ):ℝ) := by exact_mod_cast pow_pos hp.out.pos j
  have ppos : (0:ℝ) < (p:ℝ)-1 := sub_pos.mpr (by exact_mod_cast hp.out.one_lt)
  have form (q : ℕ) [NeZero q] (hq : q=p*p^j) : ordinaryWeight q m = localWeight m p := by
    subst q
    have tot : (p*p^j).totient = p^j*(p-1) := by rw [← pow_succ',Nat.totient_prime_pow_succ hp.out]
    unfold ordinaryWeight
    rw [tot,ordinary_prime_power,Nat.cast_mul,Nat.cast_mul,Nat.cast_sub hp.out.one_le,Nat.cast_one]
    unfold localWeight
    split_ifs <;> field_simp [fpos.ne',ppos.ne']
  exact form _ (pow_succ' p j)

/-- The finite ordinary count has exactly the usual Euler factor at every
prime dividing the modulus, independent of its exponent. -/
theorem ordinary_product (q m : ℕ) [NeZero q] :
    ordinaryWeight q m = ∏ p ∈ q.primeFactors, localWeight m p := by
  let F (p : q.primeFactors) := (p:ℕ)^(q.factorization p)
  have pp (p : q.primeFactors) : (p:ℕ).Prime := Nat.prime_of_mem_primeFactors p.property
  let _ : ∀ p : q.primeFactors, Fact (p:ℕ).Prime := fun p => ⟨pp p⟩
  let _ : ∀ p : q.primeFactors, NeZero (F p) := fun p => ⟨pow_ne_zero _ (pp p).ne_zero⟩
  have expo (p : q.primeFactors) : 0 < q.factorization (p:ℕ) :=
    (pp p).factorization_pos_of_dvd (NeZero.ne q) (Nat.dvd_of_mem_primeFactors p.property)
  let e : ZMod q ≃+* ∀ p : q.primeFactors, ZMod (F p) := ZMod.equivPi q (NeZero.ne q)
  have hJ := local_factors e (1 : DirichletCharacter ℂ q) 1 m
  simp only [component_one] at hJ
  have hr : (q:ℝ) = ∏ p : q.primeFactors, (F p:ℝ) := by
    exact_mod_cast Nat.prod_primeFactors_coe_pow_factorization (NeZero.ne q)
  have hφ : q.totient = ∏ p : q.primeFactors, (F p).totient := by
    rw [Nat.totient_eq_prod_factorization (NeZero.ne q),Nat.prod_factorization_eq_prod_primeFactors]
    simp only [F,Nat.totient_prime_pow (pp _) (expo _)]
    exact (Finset.prod_coe_sort q.primeFactors (fun p : ℕ => p^(q.factorization p-1)*(p-1))).symm
  have hφr : (q.totient:ℝ) = ∏ p : q.primeFactors, ((F p).totient:ℝ) := by exact_mod_cast hφ
  unfold ordinaryWeight
  rw [hr,hφr,hJ,norm_prod,← prod_mul_distrib,← prod_pow,← prod_div_distrib]
  rw [← Finset.prod_coe_sort q.primeFactors (localWeight m)]
  apply prod_congr rfl
  intro p _
  exact weight_prime_power _ m (expo p)

private theorem local_minimum {p : ℕ} (hp : 2 ≤ p) (m : ℕ) :
    1-1/((p:ℝ)-1)^2 ≤ localWeight m p := by
  have hpos : (0:ℝ) < (p:ℝ)-1 := sub_pos.mpr (by exact_mod_cast (by omega : 1 < p))
  unfold localWeight
  split_ifs
  · apply (sub_le_self (1:ℝ) (by positivity)).trans
    exact (le_div_iff₀ hpos).mpr (by linarith)
  · apply le_of_eq
    field_simp [hpos.ne']
    ring

private theorem truncated_lower (S : Finset ℕ) (hp : ∀ p ∈ S, p.Prime) (m : ℕ) (he : Even m) :
    ∀ P : ℕ, 2 ≤ P →
      (if 2 ∈ S then (2:ℝ) else 1) * P / (2*((P:ℝ)-1)) ≤
        ∏ p ∈ range (P+1), (if p ∈ S then localWeight m p else 1) := by
  let a : ℝ := if 2 ∈ S then 2 else 1
  have ha : 0 < a := by dsimp [a]; split <;> norm_num
  intro P hP
  induction P,hP using Nat.le_induction with
  | base =>
    have h0 : 0 ∉ S := fun h => Nat.not_prime_zero (hp 0 h)
    have h1 : 1 ∉ S := fun h => Nat.not_prime_one (hp 1 h)
    have h2 : 2 ∣ m := even_iff_two_dvd.mp he
    rw [show range (2+1) = {0,1,2} by decide]
    by_cases ht : 2 ∈ S <;> norm_num [h0,h1,ht,localWeight,h2]
  | succ k hk ih =>
    have hk' : (2:ℝ) ≤ k := by exact_mod_cast hk
    let b : ℝ := 1-1/(k:ℝ)^2
    have hb : 0 ≤ b := by
      apply sub_nonneg.mpr
      apply (div_le_one (by positivity : 0 < (k:ℝ)^2)).mpr
      nlinarith [sq_nonneg ((k:ℝ)-2)]
    have hf : b ≤ (if k+1 ∈ S then localWeight m (k+1) else 1) := by
      split_ifs
      · simpa [b] using local_minimum (p := k+1) (by omega) m
      · exact sub_le_self _ (by positivity)
    change a*(k:ℝ)/(2*((k:ℝ)-1)) ≤ _ at ih
    have left : 0 ≤ a*(k:ℝ)/(2*((k:ℝ)-1)) :=
      div_nonneg (mul_nonneg ha.le (Nat.cast_nonneg k)) (by linarith)
    rw [prod_range_succ]
    refine le_trans ?_ (mul_le_mul ih hf hb (left.trans ih))
    change a*((k+1:ℕ):ℝ)/(2*(((k+1:ℕ):ℝ)-1)) ≤ (a*(k:ℝ)/(2*((k:ℝ)-1))) * b
    apply le_of_eq
    push_cast
    dsimp [b]
    field_simp [show (k:ℝ)-1 ≠ 0 by linarith,show (k:ℝ) ≠ 0 by linarith]
    ring

theorem uniform_weight (q m : ℕ) [NeZero q] (he : Even m) :
    (if 2 ∣ q then (1:ℝ) else 1/2) ≤ ordinaryWeight q m := by
  let P := max 2 q
  have hP : 2 ≤ P := le_max_left ..
  have hr : (2:ℝ) ≤ P := by exact_mod_cast hP
  have cover : q.primeFactors ⊆ range (P+1) := fun p hp =>
    mem_range.mpr (Nat.lt_succ_of_le ((Nat.le_of_mem_primeFactors hp).trans (le_max_right ..)))
  have h := truncated_lower q.primeFactors (fun _ hp => Nat.prime_of_mem_primeFactors hp) m he P hP
  simp only [prod_ite_mem,inter_eq_right.mpr cover] at h
  rw [ordinary_product]
  apply le_trans _ h
  have two : 2 ∈ q.primeFactors ↔ 2 ∣ q :=
    ⟨Nat.dvd_of_mem_primeFactors,fun h => Nat.mem_primeFactors.mpr ⟨Nat.prime_two,h,NeZero.ne q⟩⟩
  by_cases ht : 2 ∣ q <;> simp only [two,ht,ite_true,ite_false,one_mul]
  all_goals apply (le_div_iff₀ (by linarith : (0:ℝ) < 2*((P:ℝ)-1))).mpr; linarith

/-- The ordinary infinite series at a positive even target has real part
at least one. -/
theorem ordinary_at_least_one (m : ℕ) (hm : 0 < m) (he : Even m) :
    1 ≤ (series (1 : DirichletCharacter ℂ 1) (1 : DirichletCharacter ℂ 1) m).re := by
  let O : DirichletCharacter ℂ 1 := 1
  have lim := (TwistedGoldbachSingularSeries.partial_limit O O m hm 2 (by decide)).norm
  have lower : 1 ≤ ‖series O O m‖ := by
    apply ge_of_tendsto' lim
    intro n
    let q := 2*n.factorial
    let _ : NeZero q := ⟨mul_ne_zero (by decide) n.factorial_ne_zero⟩
    have hf := uniform_weight q m he
    rw [ite_eq_left (dvd_mul_right 2 n.factorial)] at hf
    have amb := TwistedGoldbachSingularSeries.ambient_sum (α := O) (β := O)
      isPrimitive_one_level_one isPrimitive_one_level_one (one_dvd q) (one_dvd q) m
    simp only [O,map_one] at amb
    change 1 ≤ ‖∑ d ∈ q.divisors, TwistedGoldbachSingularSeries.coefficient O O m d‖
    rw [← amb]
    simpa only [TwistedGoldbachSingularSeries.normalized,norm_div,norm_mul,norm_pow,
      Complex.norm_natCast,ordinaryWeight,J] using hf
  exact lower.trans (TwistedGoldbachSingularSeries.infinite_domination (α := O) (β := O)
    isPrimitive_one_level_one isPrimitive_one_level_one m hm)

/-- A mixed contribution vanishes at a nonsquarefree conductor or a nonunit
target. -/
theorem mixed_zero {r : ℕ} [NeZero r] (χ : DirichletCharacter ℂ r) (hχ : χ.IsPrimitive)
    (m : ℕ) (hm : 0 < m) (he : Even m) (bad : ¬Squarefree r ∨ ¬m.Coprime r) :
    series χ (1 : DirichletCharacter ℂ 1) m = 0 := by
  have h := mixed_exact χ hχ m hm
  apply (mul_eq_zero.mp (show series χ (1 : DirichletCharacter ℂ 1) m *
      J (1 : DirichletCharacter ℂ r) 1 (m:ZMod r) = 0 from ?_)).resolve_right (principal_ne_zero r m he)
  rw [h]
  rcases bad with hs | hc
  · simp [ArithmeticFunction.moebius_eq_zero_of_not_squarefree hs]
  · simp [χ.map_nonunit (fun hu => hc ((ZMod.isUnit_iff_coprime m r).mp hu))]

/-- Explicit constant in the uniform mixed-pair bound used in (11.10) of
Pintz I and (8.1) of Bhowmik--Grimmelt. -/
theorem mixed_bound {r : ℕ} [NeZero r] (χ : DirichletCharacter ℂ r) (hχ : χ.IsPrimitive)
    (m : ℕ) (hm : 0 < m) (he : Even m) :
    ‖series χ (1 : DirichletCharacter ℂ 1) m‖ ≤
      (2*(r:ℝ)/(r.totient:ℝ)^2) * ‖series (1 : DirichletCharacter ℂ 1) (1 : DirichletCharacter ℂ 1) m‖ := by
  have h := congrArg (fun z : ℂ => ‖z‖) (mixed_exact χ hχ m hm)
  simp only [norm_mul] at h
  have small : ‖(ArithmeticFunction.moebius r:ℂ)‖ * ‖χ (m:ZMod r)‖ ≤ 1 :=
    (mul_le_mul (DyadicMixedB4MoebiusGauss.norm_moebiusComplex_le_one r)
      (χ.norm_le_one _) (norm_nonneg _) zero_le_one).trans_eq (one_mul _)
  have hφ : (0:ℝ) < (r.totient:ℝ)^2 := sq_pos_of_pos (by exact_mod_cast Nat.totient_pos.mpr (NeZero.pos r))
  have base : 1/2 ≤ ordinaryWeight r m := by
    apply le_trans _ (uniform_weight r m he)
    split <;> norm_num
  have total := (le_div_iff₀ hφ).mp base
  let O : ℝ := ‖series (1 : DirichletCharacter ℂ 1) (1 : DirichletCharacter ℂ 1) m‖
  let T : ℝ := ‖series χ (1 : DirichletCharacter ℂ 1) m‖
  let D : ℝ := ‖J (1 : DirichletCharacter ℂ r) 1 (m:ZMod r)‖
  have a : T*D ≤ O := h.le.trans ((mul_le_mul_of_nonneg_left small (norm_nonneg _)).trans_eq (mul_one _))
  have b : (r.totient:ℝ)^2 ≤ 2*(r:ℝ)*D := by change 1/2*(r.totient:ℝ)^2 ≤ (r:ℝ)*D at total; linarith
  change T ≤ (2*(r:ℝ)/(r.totient:ℝ)^2)*O
  rw [div_mul_eq_mul_div,le_div_iff₀ hφ]
  calc
    T*(r.totient:ℝ)^2 ≤ T*(2*(r:ℝ)*D) := mul_le_mul_of_nonneg_left b (norm_nonneg _)
    _ = 2*(r:ℝ)*(T*D) := by ring
    _ ≤ 2*(r:ℝ)*O := mul_le_mul_of_nonneg_left a (by positivity)

end Conjectures.Goldbach.SharpSingularSeriesRatiosProof.TwistedGoldbachMixedPrincipal

/-! Möbius inversion of the finite conductor quotient. At denominators
divisible by the least common multiple of the conductors, the remaining
Euler factors are real and multiplicative away from that common level. -/

namespace Conjectures.Goldbach.SharpSingularSeriesRatiosProof.TwistedGoldbachCoefficientProduct

open Finset DirichletCharacter TwistedGoldbachConductorRatio
open TwistedGoldbachSingularSeries TwistedGoldbachLocalProduct TwistedGoldbachMixedPrincipal
open scoped BigOperators Classical

noncomputable def atom (L t : ℕ) (g : ℕ → ℝ) : ℝ :=
  if Squarefree t ∧ t.Coprime L then ∏ p ∈ t.primeFactors, g p else 0

theorem sum_atoms (L n : ℕ) (hL : L ≠ 0) (hn : n ≠ 0) (g : ℕ → ℝ) :
    ∑ t ∈ n.divisors, atom L t g = ∏ p ∈ n.primeFactors \ L.primeFactors, (1+g p) := by
  rw [prod_one_add]
  unfold atom
  rw [← sum_filter]
  apply sum_bij (fun d _ => d.primeFactors)
  · intro d hd
    obtain ⟨hm,_,hc⟩ := mem_filter.mp hd
    apply mem_powerset.mpr
    intro p hp
    exact mem_sdiff.mpr ⟨Nat.primeFactors_mono (Nat.dvd_of_mem_divisors hm) hn hp,
      fun h => disjoint_left.mp hc.disjoint_primeFactors hp h⟩
  · intro a ha b hb hab
    rw [← Nat.prod_primeFactors_of_squarefree (mem_filter.mp ha).2.1,
      ← Nat.prod_primeFactors_of_squarefree (mem_filter.mp hb).2.1,hab]
  · intro U hU
    have sub := mem_powerset.mp hU
    have prime (p : ℕ) (hp : p ∈ U) := Nat.prime_of_mem_primeFactors (mem_sdiff.mp (sub hp)).1
    let d := ∏ p ∈ U, p
    have factors : d.primeFactors=U := Nat.primeFactors_prod prime
    have hd : d ≠ 0 := (prod_pos (fun p hp => (prime p hp).pos)).ne'
    have square := Nat.squarefree_prod_primeFactors d
    rw [factors] at square
    have divides : d ∣ n := by
      have h := (Nat.prod_primeFactors_dvd_iff (n := d) hn).mpr
        (by rw [factors]; exact fun p hp => (mem_sdiff.mp (sub hp)).1)
      rwa [factors] at h
    have cop : d.Coprime L := (Nat.disjoint_primeFactors hd hL).mp (by
      rw [factors,disjoint_left]
      exact fun p hp => (mem_sdiff.mp (sub hp)).2)
    exact ⟨d,mem_filter.mpr ⟨Nat.mem_divisors.mpr ⟨divides,hn⟩,square,cop⟩,factors⟩
  · intro _ _
    rfl

private theorem eq_of_divisor_sums (f g : ℕ → ℂ)
    (h : ∀ n : ℕ, n ≠ 0 → ∑ d ∈ n.divisors, f d = ∑ d ∈ n.divisors, g d) :
    ∀ n : ℕ, n ≠ 0 → f n=g n := by
  intro n
  induction n using Nat.strong_induction_on with
  | ind n ih =>
    intro hn
    have ne := Nat.mem_divisors_self n hn
    have rest : ∑ d ∈ n.divisors.erase n, f d = ∑ d ∈ n.divisors.erase n, g d := by
      apply sum_congr rfl
      intro d hd
      have ⟨hneq,hmem⟩ := mem_erase.mp hd
      exact ih d (lt_of_le_of_ne (Nat.le_of_dvd (Nat.pos_of_ne_zero hn) (Nat.dvd_of_mem_divisors hmem)) hneq)
        (Nat.pos_of_mem_divisors hmem).ne'
    have H := h n hn
    rw [← sum_erase_add _ _ ne,← sum_erase_add _ _ ne,rest] at H
    exact add_left_cancel H

private theorem multiples {M : Type*} [AddCommMonoid M] {L n : ℕ} (hL : L ≠ 0) (hn : n ≠ 0) (f : ℕ → M)
    (outside : ∀ d : ℕ, ¬L ∣ d → f d=0) :
    ∑ d ∈ n.divisors, f (L*d) = ∑ d ∈ (L*n).divisors, f d := by
  let S := (L*n).divisors.filter (fun d => L ∣ d)
  calc
    _ = ∑ d ∈ S, f d := by
      apply sum_bij (fun d _ => L*d)
      · intro d hd
        exact mem_filter.mpr ⟨Nat.mem_divisors.mpr ⟨Nat.mul_dvd_mul_left L (Nat.dvd_of_mem_divisors hd),
          mul_ne_zero hL hn⟩,dvd_mul_right L d⟩
      · intro a _ b _ h
        exact Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hL) h
      · intro d hd
        obtain ⟨hm,k,rfl⟩ := mem_filter.mp hd
        exact ⟨k,Nat.mem_divisors.mpr ⟨Nat.dvd_of_mul_dvd_mul_left (Nat.pos_of_ne_zero hL)
          (Nat.dvd_of_mem_divisors hm),hn⟩,rfl⟩
      · intro _ _
        rfl
    _ = _ := sum_subset (filter_subset _ _) (fun d hd hnot =>
      outside d (fun h => hnot (mem_filter.mpr ⟨hd,h⟩)))

private theorem complex_ordinary (q m : ℕ) [NeZero q] :
    normalized (1 : DirichletCharacter ℂ q) 1 m = (ordinaryWeight q m:ℂ) := by
  change (q:ℂ)*J (1 : DirichletCharacter ℂ q) 1 (m:ZMod q)/(q.totient:ℂ)^2 = _
  simp only [ordinaryWeight,principal_card,Complex.norm_natCast,Complex.ofReal_div,Complex.ofReal_mul,
    Complex.ofReal_natCast,Complex.ofReal_pow]

private theorem partial_sums {r s q : ℕ} [NeZero r] [NeZero s] [NeZero q]
    {α : DirichletCharacter ℂ r} {β : DirichletCharacter ℂ s} (hα : α.IsPrimitive) (hβ : β.IsPrimitive)
    (hr : r ∣ q) (hs : s ∣ q) (m : ℕ) (hm : 0 < m) (he : Even m) :
    ∑ d ∈ q.divisors, coefficient α β m d =
      (series α β m / series (1 : DirichletCharacter ℂ 1) (1 : DirichletCharacter ℂ 1) m) *
        (ordinaryWeight q m:ℂ) := by
  let O := series (1 : DirichletCharacter ℂ 1) (1 : DirichletCharacter ℂ 1) m
  have nz : O ≠ 0 := by
    intro hz
    have h := ordinary_at_least_one m hm he
    change 1 ≤ O.re at h
    rw [hz,Complex.zero_re] at h
    norm_num at h
  have id := conductor_identity hα hβ hr hs m hm
  change series α β m * J (1 : DirichletCharacter ℂ q) 1 (m:ZMod q) = O * _ at id
  rw [← ambient_sum hα hβ hr hs m,← complex_ordinary]
  change (q:ℂ)*J _ _ (m:ZMod q)/(q.totient:ℂ)^2 =
    (series α β m/O)*((q:ℂ)*J (1 : DirichletCharacter ℂ q) 1 (m:ZMod q)/(q.totient:ℂ)^2)
  have eqn : J (changeLevel hr α) (changeLevel hs β) (m:ZMod q) =
      (series α β m/O)*J (1 : DirichletCharacter ℂ q) 1 (m:ZMod q) := by
    rw [div_mul_eq_mul_div,eq_div_iff nz,mul_comm]
    exact id.symm
  rw [eqn]
  ring

theorem off_level {r s : ℕ} (α : DirichletCharacter ℂ r) (β : DirichletCharacter ℂ s)
    (m d : ℕ) (h : ¬Nat.lcm r s ∣ d) : coefficient α β m d = 0 := by
  unfold coefficient
  split_ifs with hd hdiv
  · exact False.elim (h (Nat.lcm_dvd hdiv.1 hdiv.2))
  all_goals rfl

private theorem new_weights {L t : ℕ} [NeZero L] [NeZero t] (m : ℕ) :
    ordinaryWeight (L*t) m = ordinaryWeight L m *
      ∏ p ∈ t.primeFactors \ L.primeFactors, localWeight m p := by
  rw [ordinary_product,ordinary_product,Nat.primeFactors_mul (NeZero.ne L) (NeZero.ne t)]
  have seteq : L.primeFactors ∪ t.primeFactors = L.primeFactors ∪ (t.primeFactors \ L.primeFactors) := by
    ext p
    simp only [mem_union,mem_sdiff]
    tauto
  rw [seteq,prod_union]
  exact disjoint_left.mpr (fun p hp h => (mem_sdiff.mp h).2 hp)

section Conductors
variable {r s : ℕ} [NeZero r] [NeZero s] {α : DirichletCharacter ℂ r} {β : DirichletCharacter ℂ s}
  (hα : α.IsPrimitive) (hβ : β.IsPrimitive) (m : ℕ) (hm : 0 < m) (he : Even m)
include hα hβ hm he

/-- At multiples of the least common conductor level, finite sums acquire
exactly the ordinary Euler factors for the newly introduced primes. -/
theorem partial_extension (t : ℕ) (ht : t ≠ 0) :
    let L := Nat.lcm r s
    ∑ d ∈ (L*t).divisors, coefficient α β m d =
      coefficient α β m L * ((∏ p ∈ t.primeFactors \ L.primeFactors, localWeight m p : ℝ):ℂ) := by
  intro L
  let _ : NeZero t := ⟨ht⟩
  let _ : NeZero L := ⟨(Nat.lcm_pos (NeZero.pos r) (NeZero.pos s)).ne'⟩
  have hr : r ∣ L := Nat.dvd_lcm_left ..
  have hs : s ∣ L := Nat.dvd_lcm_right ..
  have base := partial_sums hα hβ hr hs m hm he
  rw [sum_eq_single_of_mem L (Nat.mem_divisors_self L (NeZero.ne L))] at base
  · have h := partial_sums hα hβ (hr.trans (dvd_mul_right L t)) (hs.trans (dvd_mul_right L t)) m hm he
    rw [h,new_weights,Complex.ofReal_mul,← mul_assoc,← base]
  · intro d hd ne
    apply off_level
    intro h
    exact ne (Nat.dvd_antisymm (Nat.dvd_of_mem_divisors hd) h)

/-- Formula for every single coefficient, including every ramified or
nonsquarefree zero. No primitivity condition is imposed on the product of
the two source characters. -/
theorem coefficient_extension (t : ℕ) (ht : t ≠ 0) :
    let L := Nat.lcm r s
    coefficient α β m (L*t) =
      coefficient α β m L * (atom L t (fun p => localWeight m p-1):ℂ) := by
  intro L
  let c := coefficient α β m
  let g (p : ℕ) := localWeight m p-1
  have hL : L ≠ 0 := (Nat.lcm_pos (NeZero.pos r) (NeZero.pos s)).ne'
  apply eq_of_divisor_sums (fun d => c (L*d)) (fun d => c L * (atom L d g:ℂ)) _ t ht
  intro n hn
  rw [multiples hL hn c (fun d h => off_level α β m d h)]
  have H := partial_extension hα hβ m hm he n hn
  change ∑ d ∈ (L*n).divisors, c d = _ at H
  rw [H,← mul_sum,← Complex.ofReal_sum,sum_atoms _ _ hL hn]
  have eqn : (fun p => 1+g p) = localWeight m := funext (fun p => by dsimp [g]; ring)
  simp only [eqn]
  rfl

theorem absolute_partial (t : ℕ) (ht : t ≠ 0) :
    let L := Nat.lcm r s
    ∑ d ∈ (L*t).divisors, ‖coefficient α β m d‖ =
      ‖coefficient α β m L‖ * ∏ p ∈ t.primeFactors \ L.primeFactors, (1+|localWeight m p-1|) := by
  intro L
  let c := coefficient α β m
  let g (p : ℕ) := localWeight m p-1
  have hL : L ≠ 0 := (Nat.lcm_pos (NeZero.pos r) (NeZero.pos s)).ne'
  have absatom (d : ℕ) : |atom L d g| = atom L d (fun p => |g p|) := by
    unfold atom
    split_ifs <;> simp [Finset.abs_prod]
  rw [← multiples hL ht (fun d => ‖c d‖) (fun d h => by change ‖coefficient α β m d‖ = 0; rw [off_level α β m d h,norm_zero])]
  change ∑ d ∈ t.divisors, ‖c (L*d)‖ = ‖c L‖*_
  rw [← sum_atoms L t hL ht (fun p => |g p|),mul_sum]
  apply sum_congr rfl
  intro d hd
  have H := coefficient_extension hα hβ m hm he d (Nat.pos_of_mem_divisors hd).ne'
  change c (L*d) = c L * (atom L d g:ℂ) at H
  rw [H,norm_mul,Complex.norm_real,Real.norm_eq_abs,absatom]

end Conductors

open Filter Topology

/-- The ratio of the absolute Euler factor to the signed factor. A prime
dividing the conductor level or the even target contributes one. -/
noncomputable def correction (K p : ℕ) : ℝ :=
  if p.Prime ∧ 2 < p ∧ ¬p ∣ K then 1+2/((p:ℝ)*((p:ℝ)-2)) else 1

theorem correction_one_le (K p : ℕ) : 1 ≤ correction K p := by
  unfold correction
  split_ifs with h
  · have hp : (2:ℝ)<p := by exact_mod_cast h.2.1
    exact le_add_of_nonneg_right (by positivity)
  · rfl

private theorem factor_ratio {L p m : ℕ} (hp : p.Prime) (he : Even m) (hL : ¬p ∣ L) :
    1+|localWeight m p-1| = |localWeight m p| * correction (L*m) p := by
  have hp1 : (1:ℝ)<p := by exact_mod_cast hp.one_lt
  have h1 : 0 < (p:ℝ)-1 := by linarith
  by_cases hm : p ∣ m
  · have hm' : p ∣ L*m := hm.trans (dvd_mul_left m L)
    simp only [localWeight,ite_eq_left hm,correction,hm',not_true_eq_false,and_false,ite_false,mul_one]
    have hw : 1 ≤ (p:ℝ)/((p:ℝ)-1) := (le_div_iff₀ h1).mpr (by linarith)
    rw [abs_of_nonneg (sub_nonneg.mpr hw),abs_of_nonneg (by linarith : 0 ≤ (p:ℝ)/((p:ℝ)-1))]
    ring
  · have pn : 2 < p := by
      have := hp.two_le
      by_contra! bad
      exact hm (show p ∣ m by simpa [show p=2 by omega] using even_iff_two_dvd.mp he)
    have hp2 : (2:ℝ)<p := by exact_mod_cast pn
    have h2 : 0 < (p:ℝ)-2 := by linarith
    have h0 : 0 < (p:ℝ) := by linarith
    have hk : ¬p ∣ L*m := fun H => (hp.dvd_mul.mp H).elim hL hm
    simp only [localWeight,ite_eq_right hm,correction,ite_eq_left (And.intro hp (And.intro pn hk))]
    have hw : (p:ℝ)*((p:ℝ)-2)/((p:ℝ)-1)^2 ≤ 1 :=
      (div_le_one (sq_pos_of_pos h1)).mpr (by nlinarith)
    rw [abs_of_nonpos (sub_nonpos.mpr hw),abs_of_nonneg (div_nonneg (mul_nonneg h0.le h2.le) (sq_nonneg _))]
    field_simp [h0.ne',h1.ne',h2.ne']
    ring

theorem finite_ratio {r s : ℕ} [NeZero r] [NeZero s] {α : DirichletCharacter ℂ r}
    {β : DirichletCharacter ℂ s} (hα : α.IsPrimitive) (hβ : β.IsPrimitive)
    (m : ℕ) (hm : 0 < m) (he : Even m) (t : ℕ) (ht : t ≠ 0) :
    let L := Nat.lcm r s
    ∑ d ∈ (L*t).divisors, ‖coefficient α β m d‖ =
      ‖∑ d ∈ (L*t).divisors, coefficient α β m d‖ *
        ∏ p ∈ t.primeFactors, correction (L*m) p := by
  intro L
  have hL : L ≠ 0 := (Nat.lcm_pos (NeZero.pos r) (NeZero.pos s)).ne'
  have rest : ∏ p ∈ t.primeFactors \ L.primeFactors, correction (L*m) p =
      ∏ p ∈ t.primeFactors, correction (L*m) p := by
    apply prod_subset sdiff_subset
    intro p hp hnot
    have hpL : p ∈ L.primeFactors := by
      by_contra H
      exact hnot (mem_sdiff.mpr ⟨hp,H⟩)
    have hd := (Nat.dvd_of_mem_primeFactors hpL).trans (dvd_mul_right L m)
    simp [correction,hd]
  rw [absolute_partial hα hβ m hm he t ht,partial_extension hα hβ m hm he t ht,
    norm_mul,Complex.norm_real,Real.norm_eq_abs,Finset.abs_prod,← rest,mul_assoc,← prod_mul_distrib]
  congr 1
  apply prod_congr rfl
  intro p hp
  have prime := Nat.prime_of_mem_primeFactors (mem_sdiff.mp hp).1
  exact factor_ratio prime he (fun hd => (mem_sdiff.mp hp).2 (Nat.mem_primeFactors.mpr ⟨prime,hd,hL⟩))

private theorem correction_multipliable (K : ℕ) : Multipliable (correction K) := by
  let g (p : ℕ) := correction K p-1
  have base := (Real.summable_one_div_nat_pow.mpr (by decide : 1<2)).mul_left (6:ℝ)
  have hs : Summable g := base.of_norm_bounded (fun p => by
    have hg : 0 ≤ g p := sub_nonneg.mpr (correction_one_le K p)
    rw [Real.norm_eq_abs,abs_of_nonneg hg]
    dsimp [g,correction]
    split_ifs with h
    · have hp : (3:ℝ) ≤ p := by exact_mod_cast h.2.1
      have hp0 : 0 < (p:ℝ) := by linarith
      have hp2 : 0 < (p:ℝ)-2 := by linarith
      field_simp [hp0.ne',hp2.ne']
      nlinarith [mul_nonneg hp0.le (show 0 ≤ (p:ℝ)-3 by linarith)]
    · rw [sub_self]
      positivity)
  exact (Real.multipliable_one_add_of_summable hs).congr (fun p => by dsimp [g]; ring)

private theorem correction_bound_step {p : ℕ} (hp : 2<p) (K : ℕ) :
    correction K p ≤ (((p:ℝ)-1)^2/((p:ℝ)*((p:ℝ)-2)))^2 := by
  have h : (2:ℝ)<p := by exact_mod_cast hp
  have hd : 0 < (p:ℝ)*((p:ℝ)-2) := mul_pos (by linarith) (by linarith)
  have algebra : ((p:ℝ)-1)^2/((p:ℝ)*((p:ℝ)-2)) = 1+1/((p:ℝ)*((p:ℝ)-2)) := by
    field_simp [hd.ne']
    ring
  rw [algebra]
  have hinv : 0 ≤ 1/((p:ℝ)*((p:ℝ)-2)) := by positivity
  unfold correction
  split_ifs <;> nlinarith [sq_nonneg (1/((p:ℝ)*((p:ℝ)-2))),show 2/((p:ℝ)*((p:ℝ)-2))=2*(1/((p:ℝ)*((p:ℝ)-2))) by ring]

private theorem initial_product (K : ℕ) : ∀ n : ℕ, 2 ≤ n →
    ∏ p ∈ range (n+1), correction K p ≤ (2*((n:ℝ)-1)/(n:ℝ))^2 := by
  intro n hn
  induction n,hn using Nat.le_induction with
  | base => norm_num [prod_range_succ,correction]
  | succ k hk ih =>
    have h : (2:ℝ)≤k := by exact_mod_cast hk
    have hk0 : (k:ℝ) ≠ 0 := by linarith
    have hk1 : (k:ℝ)-1 ≠ 0 := by linarith
    have hks : (k:ℝ)+1 ≠ 0 := by linarith
    rw [prod_range_succ]
    refine (mul_le_mul ih (correction_bound_step (by omega : 2<k+1) K)
      (zero_le_one.trans (correction_one_le K _)) (sq_nonneg _)).trans_eq ?_
    push_cast
    field_simp [hk0,hk1,hks,show (k:ℝ)+1-2 ≠ 0 by linarith]
    ring

theorem correction_product_le_four (K : ℕ) : ∏' p : ℕ, correction K p ≤ 4 := by
  apply le_of_tendsto ((correction_multipliable K).hasProd.tendsto_prod_nat.comp (tendsto_add_atTop_nat 1))
  filter_upwards [eventually_ge_atTop 2] with n hn
  apply (initial_product K n hn).trans
  have h : (2:ℝ)≤n := by exact_mod_cast hn
  have hn0 : 0 < (n:ℝ) := by linarith
  have ht : 2*((n:ℝ)-1)/(n:ℝ) ≤ 2 := (div_le_iff₀ hn0).mpr (by linarith)
  have hb : 0 ≤ 2*((n:ℝ)-1)/(n:ℝ) := div_nonneg (by linarith) hn0.le
  nlinarith [mul_nonneg (sub_nonneg.mpr ht) (show 0 ≤ 2+2*((n:ℝ)-1)/(n:ℝ) by linarith)]

private theorem abs_limit {r s : ℕ} [NeZero r] [NeZero s] (α : DirichletCharacter ℂ r)
    (β : DirichletCharacter ℂ s) (m : ℕ) (hm : 0 < m) (L : ℕ) (hL : L ≠ 0) :
    Tendsto (fun n : ℕ => ∑ d ∈ (L*n.factorial).divisors, ‖coefficient α β m d‖)
      atTop (𝓝 (∑' d : ℕ, ‖coefficient α β m d‖)) := by
  have hf : Tendsto (fun n : ℕ => insert 0 (L*n.factorial).divisors) atTop atTop := by
    apply tendsto_atTop.2
    intro S
    filter_upwards [eventually_ge_atTop (S.sup id)] with n hn
    intro d hd
    by_cases h : d=0
    · simp [h]
    exact mem_insert_of_mem (Nat.mem_divisors.mpr ⟨(Nat.dvd_factorial (Nat.pos_of_ne_zero h)
      ((S.le_sup (f := id) hd).trans hn)).trans (dvd_mul_left n.factorial L),
      mul_ne_zero hL n.factorial_ne_zero⟩)
  apply ((summable_coefficients α β m hm).hasSum.comp hf).congr'
  filter_upwards with n
  simp [coefficient]

/-- Equality keeps precisely the odd primes outside the two conductors
and the target. It includes singular series which vanish. -/
theorem absolute_euler_product {r s : ℕ} [NeZero r] [NeZero s]
    {α : DirichletCharacter ℂ r} {β : DirichletCharacter ℂ s}
    (hα : α.IsPrimitive) (hβ : β.IsPrimitive) (m : ℕ) (hm : 0 < m) (he : Even m) :
    ∑' d : ℕ, ‖coefficient α β m d‖ =
      ‖∑' d : ℕ, coefficient α β m d‖ * ∏' p : ℕ, correction (Nat.lcm r s*m) p := by
  let L := Nat.lcm r s
  have hL : L ≠ 0 := (Nat.lcm_pos (NeZero.pos r) (NeZero.pos s)).ne'
  let K := L*m
  have h := (partial_limit α β m hm L hL).norm.mul
    ((correction_multipliable K).hasProd.tendsto_prod_nat.comp (tendsto_add_atTop_nat 1))
  refine tendsto_nhds_unique (abs_limit α β m hm L hL) (h.congr' ?_)
  filter_upwards with n
  change ‖∑ d ∈ (L*n.factorial).divisors, coefficient α β m d‖ * (∏ p ∈ range (n+1), correction K p) = _
  rw [finite_ratio hα hβ m hm he n.factorial n.factorial_ne_zero]
  congr 1
  symm
  apply prod_subset
  · intro p hp
    exact mem_range.mpr (Nat.lt_succ_of_le ((Nat.prime_of_mem_primeFactors hp).dvd_factorial.mp
      (Nat.dvd_of_mem_primeFactors hp)))
  · intro p hp hnot
    by_cases prime : p.Prime
    · exact False.elim (hnot (Nat.mem_primeFactors.mpr ⟨prime,prime.dvd_factorial.mpr
        (Nat.le_of_lt_succ (mem_range.mp hp)),n.factorial_ne_zero⟩))
    · simp [correction,prime]

theorem correction_le_universal (K : ℕ) : ∏' p : ℕ, correction K p ≤ ∏' p : ℕ, correction 1 p := by
  apply le_of_tendsto_of_tendsto' (correction_multipliable K).hasProd.tendsto_prod_nat
    (correction_multipliable 1).hasProd.tendsto_prod_nat
  intro n
  apply Finset.prod_le_prod₀ (fun p _ => zero_le_one.trans (correction_one_le K p))
  intro p _
  by_cases h : p.Prime ∧ 2<p ∧ ¬p ∣ K
  · have h1 : p.Prime ∧ 2<p ∧ ¬p ∣ 1 := ⟨h.1,h.2.1,h.1.not_dvd_one⟩
    simp only [correction,ite_eq_left h,ite_eq_left h1,le_refl]
  · rw [show correction K p = 1 by simp [correction,h]]
    exact correction_one_le 1 p

end Conjectures.Goldbach.SharpSingularSeriesRatiosProof.TwistedGoldbachCoefficientProduct

/-! Exact arithmetic support and size of the common-conductor coefficient in
the generalized Goldbach singular series. The additive frequency need not
be a unit. Its reduced denominator selects the primitive character and the
remaining Möbius factor. See Pintz I, (7.3)–(7.5).
https://arxiv.org/abs/1804.05561 -/

namespace Conjectures.Goldbach.SharpSingularSeriesRatiosProof.TwistedGoldbachConductorValue

open Finset DirichletCharacter TwistedGoldbachSingularSeries TwistedGoldbachCoefficientProduct
open TwistedGoldbachLocalProduct
open B13BilateralVaughanReductionProof
open DyadicMixedB4MoebiusGauss DyadicMixedB4GaussLift DyadicMixedB4ImprimitiveBound
open scoped BigOperators Classical

/-- The exact phase of an induced Gauss sum at an unramified additive
frequency. A shared prime or a square in the conductor quotient kills it. -/
theorem induced_standard {r q : ℕ} [NeZero r] [NeZero q] (hr : r ∣ q)
    (χ : DirichletCharacter ℂ r) (hχ : χ.IsPrimitive) :
    gaussSum (changeLevel hr χ) ZMod.stdAddChar =
      (ArithmeticFunction.moebius (q/r):ℂ) * χ (↑(q/r):ZMod r) * gaussSum χ ZMod.stdAddChar := by
  have h := sum_inducedGauss_moebius hr χ 1
  simp only [Nat.cast_one,AddChar.mulShift_one] at h
  rw [h,sum_eq_single_of_mem (q/r) (Nat.mem_divisors.mpr ⟨Nat.div_dvd_of_dvd hr,NeZero.ne q⟩)]
  · rw [Nat.div_div_self hr (NeZero.ne q)]
    have a := gaussSum_as_fraction_sum χ 1
    simpa only [Nat.cast_one,AddChar.mulShift_one,one_mul,moebiusComplex] using
      congrArg (fun z : ℂ => (ArithmeticFunction.moebius (q/r):ℂ)*χ (↑(q/r):ZMod r)*z) a.symm
  · intro e he hne
    have bad : ¬(e.Coprime r ∧ (q/e/r) ∣ 1) := by
      intro ⟨hc,hf⟩
      have one := Nat.eq_one_of_dvd_one hf
      obtain ⟨_,_,eqn⟩ := conductor_cofactor hr he hc
      rw [one,mul_one] at eqn
      exact hne (by rw [← eqn,Nat.mul_div_cancel _ (NeZero.pos r)])
    have zero := norm_induced_gauss_term hr he 1 hχ
    rw [ite_eq_right bad] at zero
    exact norm_le_zero_iff.mp zero

def admissible (r q : ℕ) : Prop := Squarefree (q/r) ∧ (q/r).Coprime r

theorem induced_standard_norm {r q : ℕ} [NeZero r] [NeZero q] (hr : r ∣ q)
    (χ : DirichletCharacter ℂ r) (hχ : χ.IsPrimitive) :
    ‖gaussSum (changeLevel hr χ) ZMod.stdAddChar‖ =
      if admissible r q then Real.sqrt r else 0 := by
  rw [induced_standard hr χ hχ,norm_mul,norm_mul,DirichletCharacter.norm_gaussSum_stdAddChar hχ]
  by_cases hs : Squarefree (q/r)
  · have mu : ‖(ArithmeticFunction.moebius (q/r):ℂ)‖ = 1 := by
      rcases ArithmeticFunction.moebius_ne_zero_iff_eq_or.mp (ArithmeticFunction.moebius_ne_zero_iff_squarefree.mpr hs) with H | H <;> rw [H] <;> norm_num
    rw [mu,one_mul]
    by_cases hc : (q/r).Coprime r
    · have hu := (ZMod.isUnit_iff_coprime (q/r) r).mpr hc
      have hn := χ.unit_norm_eq_one hu.unit
      rw [ite_eq_left (show admissible r q from ⟨hs,hc⟩)]
      simpa only [hu.unit_spec,one_mul] using congrArg (fun z : ℝ => z*Real.sqrt r) hn
    · rw [χ.map_nonunit (fun h => hc ((ZMod.isUnit_iff_coprime _ _).mp h)),norm_zero,zero_mul]
      simp [admissible,hc]
  · simp [ArithmeticFunction.moebius_eq_zero_of_not_squarefree hs,admissible,hs]

/-- The Fourier frequency g*k has reduced denominator j, where g=q/j and
k is a unit modulo j. This gives its exact norm at the original level. -/
theorem amplitude_norm {q j : ℕ} [NeZero q] [NeZero j] (hj : j ∣ q)
    (χ : DirichletCharacter ℂ q) (k : ℕ) (hk : k.Coprime j) :
    ‖amplitude χ (q/j*k)‖ = if χ.conductor ∣ j ∧ admissible χ.conductor j then
      Real.sqrt χ.conductor/(j.totient:ℝ) else 0 := by
  let d := χ.conductor
  let _ : NeZero d := ⟨fun h => NeZero.ne q (conductor_eq_zero_iff_level_eq_zero.mp h)⟩
  rw [amplitude_at_divisor hj]
  by_cases hd : d ∣ j
  · let θ := χ.primitiveCharacter
    let θj := changeLevel hd θ
    have eqn : χ = changeLevel hj θj := by
      dsimp only [θj,θ]
      rw [← changeLevel_trans,changeLevel_primitiveCharacter]
    have H : χ.FactorsThrough j := ⟨hj,θj,eqn⟩
    have eqj : H.χ₀=θj := changeLevel_injective hj (H.eq_changeLevel.symm.trans eqn)
    rw [dite_eq_left H,eqj]
    let hu : (ZMod j)ˣ := ZMod.unitOfCoprime k hk
    have HS := gaussSum_mulShift_eq θj ZMod.stdAddChar hu
    have val : (hu:ZMod j)=(k:ZMod j) := ZMod.coe_unitOfCoprime k hk
    unfold amplitude
    rw [← val,HS,norm_div,norm_mul,(θj⁻¹).unit_norm_eq_one hu,one_mul,Complex.norm_natCast,
      induced_standard_norm hd θ χ.primitiveCharacter_isPrimitive]
    change (if admissible d j then Real.sqrt d else 0)/(j.totient:ℝ) = _
    change (if admissible d j then Real.sqrt d else 0)/(j.totient:ℝ) =
      (if d ∣ j ∧ admissible d j then Real.sqrt d/(j.totient:ℝ) else 0)
    by_cases good : admissible d j <;> simp [good,hd]
  · have H : ¬χ.FactorsThrough j := fun h => hd (χ.conductor_dvd_of_mem_conductorSet h)
    rw [dite_eq_right H,norm_zero,ite_eq_right (not_and_of_not_left _ hd)]

theorem shifted_norm {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (m : ℕ) :
    let j := q/(m.gcd q)
    ‖gaussSum χ (ZMod.stdAddChar.mulShift (m:ZMod q))‖ =
      if χ.conductor ∣ j ∧ admissible χ.conductor j then
        (q.totient:ℝ)/j.totient * Real.sqrt χ.conductor else 0 := by
  intro j
  let g := m.gcd q
  have hg : 0 < g := Nat.gcd_pos_of_pos_right m (NeZero.pos q)
  have hd : g ∣ q := Nat.gcd_dvd_right m q
  have hj : j ∣ q := Nat.div_dvd_of_dvd hd
  let _ : NeZero j := ⟨(Nat.div_pos (Nat.le_of_dvd (NeZero.pos q) hd) hg).ne'⟩
  have eqn : q/j*(m/g)=m := by
    dsimp [j,g]
    rw [Nat.div_div_self hd (NeZero.ne q),Nat.mul_div_cancel' (Nat.gcd_dvd_left m q)]
  have A := amplitude_norm hj χ (m/g) (Nat.coprime_div_gcd_div_gcd hg)
  rw [eqn,amplitude,norm_div,Complex.norm_natCast] at A
  have hφ : (q.totient:ℝ) ≠ 0 := by exact_mod_cast NeZero.ne q.totient
  have val := (div_eq_iff hφ).mp A
  rw [val]
  split_ifs <;> ring

noncomputable def inversePair {r s : ℕ} (α : DirichletCharacter ℂ r) (β : DirichletCharacter ℂ s) :
    DirichletCharacter ℂ (Nat.lcm r s) :=
  ((changeLevel (Nat.dvd_lcm_left r s) α)*(changeLevel (Nat.dvd_lcm_right r s) β))⁻¹

def supported (r s L d j : ℕ) : Prop :=
  admissible r L ∧ admissible s L ∧ d ∣ j ∧ admissible d j

/-- The three primitive conductors determine the exact magnitude at the
base denominator, without factoring either of the source moduli. -/
theorem base_norm {r s : ℕ} [NeZero r] [NeZero s] {α : DirichletCharacter ℂ r}
    {β : DirichletCharacter ℂ s} (hα : α.IsPrimitive) (hβ : β.IsPrimitive) (m : ℕ) :
    let L := Nat.lcm r s
    let d := (inversePair α β).conductor
    let j := L/(m.gcd L)
    ‖coefficient α β m L‖ = if supported r s L d j then
      Real.sqrt r * Real.sqrt s * Real.sqrt d / ((L.totient:ℝ)*(j.totient:ℝ)) else 0 := by
  intro L d j
  have hL : L ≠ 0 := (Nat.lcm_pos (NeZero.pos r) (NeZero.pos s)).ne'
  let _ : NeZero L := ⟨hL⟩
  have hr : r ∣ L := Nat.dvd_lcm_left ..
  have hs : s ∣ L := Nat.dvd_lcm_right ..
  let θ := inversePair α β
  have neg_eq : ‖gaussSum θ (ZMod.stdAddChar.mulShift (-(m:ZMod L)))‖ =
      ‖gaussSum θ (ZMod.stdAddChar.mulShift (m:ZMod L))‖ := by
    exact le_antisymm (DyadicMixedB4CharacterFactorBound.norm_gauss_neg_shift_le _ _)
      (by simpa using DyadicMixedB4CharacterFactorBound.norm_gauss_neg_shift_le θ (-(m:ZMod L)))
  rw [coefficient,dite_eq_left hL,dite_eq_left (And.intro hr hs)]
  unfold gaussCoefficient
  rw [norm_div,norm_pow,Complex.norm_natCast,norm_mul,norm_mul,
    induced_standard_norm hr α hα,induced_standard_norm hs β hβ]
  change (if admissible r L then _ else 0)*(if admissible s L then _ else 0)*
    ‖gaussSum θ (ZMod.stdAddChar.mulShift (-(m:ZMod L)))‖/(L.totient:ℝ)^2 = _
  rw [neg_eq,shifted_norm]
  change _ * _ * (if d ∣ j ∧ admissible d j then (L.totient:ℝ)/j.totient*Real.sqrt d else 0)/(L.totient:ℝ)^2 = _
  have hφ : (L.totient:ℝ) ≠ 0 := by exact_mod_cast NeZero.ne L.totient
  unfold supported
  by_cases h1 : admissible r L <;> by_cases h2 : admissible s L <;> by_cases h3 : d ∣ j ∧ admissible d j <;>
    simp only [h1,h2,h3,and_true,and_false,ite_true,ite_false,mul_zero,zero_mul,zero_div]
  field_simp [hφ]

theorem full_base {r s : ℕ} [NeZero r] [NeZero s] {α : DirichletCharacter ℂ r}
    {β : DirichletCharacter ℂ s} (hα : α.IsPrimitive) (hβ : β.IsPrimitive) (m : ℕ) (hm : 0 < m) :
    let L := Nat.lcm r s
    let _ : NeZero L := ⟨(Nat.lcm_pos (NeZero.pos r) (NeZero.pos s)).ne'⟩
    ‖series α β m‖ * TwistedGoldbachMixedPrincipal.ordinaryWeight L m =
      ‖series (1 : DirichletCharacter ℂ 1) (1 : DirichletCharacter ℂ 1) m‖ * ‖coefficient α β m L‖ := by
  intro L inst
  let _ : NeZero L := inst
  have hr : r ∣ L := Nat.dvd_lcm_left ..
  have hs : s ∣ L := Nat.dvd_lcm_right ..
  have E := ambient_sum hα hβ hr hs m
  rw [sum_eq_single_of_mem L (Nat.mem_divisors_self L (NeZero.ne L))] at E
  · have N := congrArg (fun z : ℂ => ‖z‖) E
    simp only [normalized,norm_div,norm_mul,norm_pow,Complex.norm_natCast] at N
    have J := congrArg (fun z : ℂ => ‖z‖) (TwistedGoldbachConductorRatio.conductor_identity hα hβ hr hs m hm)
    simp only [norm_mul] at J
    rw [← N]
    unfold TwistedGoldbachMixedPrincipal.ordinaryWeight
    change ‖series α β m‖*((L:ℝ)*_/(L.totient:ℝ)^2)=_ * ((L:ℝ)*_/(L.totient:ℝ)^2)
    simp only [series,TwistedGoldbachConductorRatio.J] at J ⊢
    linear_combination ((L:ℝ)/(L.totient:ℝ)^2)*J
  · intro d hd ne
    exact off_level α β m d (fun h => ne (Nat.dvd_antisymm (Nat.dvd_of_mem_divisors hd) h))

/-- Nonvanishing of the infinite series is equivalent to four finite
arithmetic conditions on the conductors and the reduced denominator. -/
theorem full_support {r s : ℕ} [NeZero r] [NeZero s] {α : DirichletCharacter ℂ r}
    {β : DirichletCharacter ℂ s} (hα : α.IsPrimitive) (hβ : β.IsPrimitive)
    (m : ℕ) (hm : 0 < m) (he : Even m) :
    let L := Nat.lcm r s
    let d := (inversePair α β).conductor
    series α β m ≠ 0 ↔ supported r s L d (L/(m.gcd L)) := by
  intro L d
  let j := L/(m.gcd L)
  let _ : NeZero L := ⟨(Nat.lcm_pos (NeZero.pos r) (NeZero.pos s)).ne'⟩
  let _ : NeZero j := ⟨(Nat.div_pos (Nat.le_of_dvd (NeZero.pos L) (Nat.gcd_dvd_right m L))
    (Nat.gcd_pos_of_pos_right m (NeZero.pos L))).ne'⟩
  have hd : 0 < d := Nat.pos_of_ne_zero (fun h => NeZero.ne L (conductor_eq_zero_iff_level_eq_zero.mp h))
  let O := series (1 : DirichletCharacter ℂ 1) (1 : DirichletCharacter ℂ 1) m
  have hO : 0 < ‖O‖ := lt_of_lt_of_le (by norm_num : (0:ℝ)<1)
    ((TwistedGoldbachMixedPrincipal.ordinary_at_least_one m hm he).trans (Complex.re_le_norm O))
  have W := TwistedGoldbachMixedPrincipal.uniform_weight L m he
  have hw : 0 < TwistedGoldbachMixedPrincipal.ordinaryWeight L m := lt_of_lt_of_le (by split <;> norm_num) W
  have H := full_base hα hβ m hm
  dsimp only at H
  rw [base_norm hα hβ m] at H
  change ‖series α β m‖ * TwistedGoldbachMixedPrincipal.ordinaryWeight L m = ‖O‖ *
    (if supported r s L d j then Real.sqrt r * Real.sqrt s * Real.sqrt d/((L.totient:ℝ)*(j.totient:ℝ)) else 0) at H
  by_cases good : supported r s L d j
  · rw [ite_eq_left good] at H
    refine ⟨fun _ => good, fun _ hzero => ?_⟩
    rw [hzero,norm_zero,zero_mul] at H
    have hrp : (0:ℝ)<r := by exact_mod_cast NeZero.pos r
    have hsp : (0:ℝ)<s := by exact_mod_cast NeZero.pos s
    have hdp : (0:ℝ)<d := by exact_mod_cast hd
    have hLφ : 0 < (L.totient:ℝ) := by exact_mod_cast Nat.totient_pos.mpr (NeZero.pos L)
    have hjφ : 0 < (j.totient:ℝ) := by exact_mod_cast Nat.totient_pos.mpr (NeZero.pos j)
    exact (ne_of_lt (mul_pos hO (div_pos (mul_pos (mul_pos (Real.sqrt_pos.mpr hrp)
      (Real.sqrt_pos.mpr hsp)) (Real.sqrt_pos.mpr hdp)) (mul_pos hLφ hjφ)))) H
  · rw [ite_eq_right good,mul_zero] at H
    have zero := norm_eq_zero.mp ((mul_eq_zero.mp H).resolve_right hw.ne')
    exact ⟨fun hn => False.elim (hn zero),fun h => False.elim (good h)⟩

end Conjectures.Goldbach.SharpSingularSeriesRatiosProof.TwistedGoldbachConductorValue

/-! Recover the conductor of every actual CRT component directly from
the original global conductor. This lets a bound obtained from one
prime-power factor control the full singular series independently of all
complementary factors. -/

namespace Conjectures.Goldbach.SharpSingularSeriesRatiosProof.TwistedGoldbachConductorComponents

open Finset DirichletCharacter TwistedGoldbachLocalProduct TwistedGoldbachConductorRatio
open scoped BigOperators Classical

theorem conductor_mul_coprime {L : ℕ} [NeZero L] (A B : DirichletCharacter ℂ L)
    (h : A.conductor.Coprime B.conductor) : (A*B).conductor=A.conductor*B.conductor := by
  let Z := A*B
  have Aeq : Z*B⁻¹=A := by change A*B*B⁻¹=A; group
  have Beq : Z*A⁻¹=B := by change A*B*A⁻¹=B; rw [mul_comm A B]; group
  have dA := conductor_mul_dvd_lcm_conductor Z B⁻¹
  have dB := conductor_mul_dvd_lcm_conductor Z A⁻¹
  rw [Aeq,conductor_inv] at dA
  rw [Beq,conductor_inv] at dB
  have one := h.dvd_of_dvd_mul_right (dA.trans (Nat.lcm_dvd_mul ..))
  have two := h.symm.dvd_of_dvd_mul_right (dB.trans (Nat.lcm_dvd_mul ..))
  exact Nat.dvd_antisymm ((conductor_mul_dvd_lcm_conductor A B).trans (Nat.lcm_dvd_mul ..))
    (h.mul_dvd_of_dvd_of_dvd one two)

private theorem conductor_prod {ι : Type*} [DecidableEq ι] {L : ℕ} [NeZero L]
    (f : ι → DirichletCharacter ℂ L) (S : Finset ι)
    (hc : ∀ i ∈ S, ∀ k ∈ S, i ≠ k → (f i).conductor.Coprime (f k).conductor) :
    (∏ i ∈ S, f i).conductor=∏ i ∈ S, (f i).conductor := by
  induction S using Finset.induction_on with
  | empty => simp [conductor_one]
  | @insert i S hi ih =>
    have hc' : ∀ j ∈ S, ∀ k ∈ S, j ≠ k → (f j).conductor.Coprime (f k).conductor :=
      fun j hj k hk => hc j (mem_insert_of_mem hj) k (mem_insert_of_mem hk)
    have hp : (f i).conductor.Coprime ((∏ j ∈ S, f j).conductor) := by
      rw [ih hc']
      exact Nat.Coprime.prod_right (fun k hk => hc i (mem_insert_self ..) k (mem_insert_of_mem hk) (fun e => hi (e ▸ hk)))
    rw [prod_insert hi,prod_insert hi,conductor_mul_coprime _ _ hp,ih hc']

section Coordinates
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {q : ι → ℕ} [∀ i, NeZero (q i)]
  {L : ℕ} [NeZero L] (e : ZMod L ≃+* ∀ i, ZMod (q i))

omit [Fintype ι] [∀ i, NeZero (q i)] [NeZero L] in
theorem component_mul (A B : DirichletCharacter ℂ L) (i : ι) :
    component e (A*B) i = component e A i * component e B i := by
  apply MulChar.ext
  intro _
  rfl

omit [∀ i, NeZero (q i)] in
theorem recovered (hd : ∀ i, q i ∣ L) (A : DirichletCharacter ℂ L) :
    A = ∏ i, changeLevel (hd i) (component e A i) := by
  apply MulChar.ext
  intro u
  rw [reassemble e A u]
  let ev : DirichletCharacter ℂ L →* ℂ :=
    { toFun := fun χ => χ u, map_one' := MulChar.one_apply_coe u, map_mul' := fun _ _ => rfl }
  change _ = ev (∏ i, changeLevel (hd i) (component e A i))
  rw [map_prod]
  apply prod_congr rfl
  intro i _
  change _ = changeLevel (hd i) (component e A i) u
  rw [changeLevel_eq_cast_of_dvd]
  congr 1
  suffices eqCast : ∀ x : ZMod L, e x i = ZMod.cast x from eqCast u
  intro x
  obtain ⟨n,rfl⟩ : ∃ n : ℕ, (n : ZMod L)=x := ⟨x.val,ZMod.natCast_zmod_val x⟩
  rw [map_natCast,ZMod.cast_natCast (hd i)]
  rfl

omit [∀ i, NeZero (q i)] in
theorem global_conductor (hd : ∀ i, q i ∣ L) (hc : Pairwise (fun i k => (q i).Coprime (q k)))
    (A : DirichletCharacter ℂ L) :
    A.conductor = ∏ i, (component e A i).conductor := by
  let f (i : ι) := changeLevel (hd i) (component e A i)
  have val (i : ι) : (f i).conductor = (component e A i).conductor := conductor_changeLevel ..
  have cop : ∀ i ∈ univ, ∀ k ∈ univ, i ≠ k → (f i).conductor.Coprime (f k).conductor := by
    intro i _ k _ h
    rw [val,val]
    exact (hc h).of_dvd ((component e A i).conductor_dvd_level) ((component e A k).conductor_dvd_level)
  calc
    _ = (∏ i, f i).conductor := congrArg conductor (recovered e hd A)
    _ = ∏ i, (f i).conductor := conductor_prod f _ cop
    _ = _ := prod_congr rfl (fun i _ => val i)

omit [∀ i, NeZero (q i)] in
theorem component_conductor (hd : ∀ i, q i ∣ L) (hc : Pairwise (fun i k => (q i).Coprime (q k)))
    (A : DirichletCharacter ℂ L) (i : ι) :
    (component e A i).conductor=(q i).gcd A.conductor := by
  let f (k : ι) := (component e A k).conductor
  have cop : (q i).Coprime (∏ k ∈ (univ.erase i), f k) := Nat.Coprime.prod_right
    (fun k hk => (hc (mem_erase.mp hk).1.symm).of_dvd_right ((component e A k).conductor_dvd_level))
  rw [global_conductor e hd hc A]
  change f i = (q i).gcd (∏ k, f k)
  rw [← prod_erase_mul _ _ (mem_univ i),cop.symm.gcd_mul_left_cancel_right,
    Nat.gcd_eq_right ((component e A i).conductor_dvd_level)]

/-- Each individual CRT factor bounds the norm of the global correction.
This form retains the unnormalized local counts and also covers zero
local sums. -/
theorem single_factor {r s : ℕ} [NeZero r] [NeZero s]
    {α : DirichletCharacter ℂ r} {β : DirichletCharacter ℂ s}
    (hα : α.IsPrimitive) (hβ : β.IsPrimitive) (hr : r ∣ L) (hs : s ∣ L)
    (m : ℕ) (hm : 0 < m) (he : Even m) (i : ι) :
    ‖series α β m‖ * ‖J (1 : DirichletCharacter ℂ (q i)) 1 (m:ZMod (q i))‖ ≤
      ‖series (1 : DirichletCharacter ℂ 1) (1 : DirichletCharacter ℂ 1) m‖ *
      ‖J (component e (changeLevel hr α) i) (component e (changeLevel hs β) i) (m:ZMod (q i))‖ := by
  let U (k : ι) := J (1 : DirichletCharacter ℂ (q k)) 1 (m:ZMod (q k))
  let V (k : ι) := J (component e (changeLevel hr α) k) (component e (changeLevel hs β) k) (m:ZMod (q k))
  let W (k : ι) := ‖V k/U k‖
  have hU (k : ι) : 0 < ‖U k‖ := norm_pos_iff.mpr (principal_ne_zero (q k) m he)
  have small (k : ι) : W k ≤ 1 := by
    dsimp [W]
    rw [norm_div,div_le_one (hU k)]
    exact TwistedGoldbachSingularSeries.chars_le_units _ _ _
  have all : (∏ k, W k) ≤ W i := by
    rw [← prod_erase_mul _ _ (mem_univ i)]
    exact mul_le_of_le_one_left (norm_nonneg _) (prod_le_one₀ (fun k _ => norm_nonneg _) (fun k _ => small k))
  have H := congrArg (fun z : ℂ => ‖z‖) (full_product e hα hβ hr hs m hm he)
  rw [norm_mul,norm_prod] at H
  let O := ‖series (1 : DirichletCharacter ℂ 1) (1 : DirichletCharacter ℂ 1) m‖
  change ‖series α β m‖=O*(∏ k, W k) at H
  have bound : ‖series α β m‖ ≤ O*W i := H.le.trans (mul_le_mul_of_nonneg_left all (norm_nonneg _))
  dsimp only [W] at bound
  rw [norm_div,← mul_div_assoc] at bound
  exact (le_div_iff₀ (hU i)).mp bound

end Coordinates

theorem prime_part_gcd {L d p : ℕ} (hp : p.Prime) (hL : L ≠ 0) (hd : d ∣ L) :
    (p^L.factorization p).gcd d = p^d.factorization p := by
  have dn : d ≠ 0 := ne_zero_of_dvd_ne_zero hL hd
  apply Nat.dvd_antisymm
  · obtain ⟨k,_,hk⟩ := (Nat.dvd_prime_pow hp).mp (Nat.gcd_dvd_left (p^L.factorization p) d)
    rw [hk]
    exact (hp.pow_dvd_iff_dvd_ordProj dn).mp (hk ▸ Nat.gcd_dvd_right (p^L.factorization p) d)
  · exact Nat.dvd_gcd (Nat.ordProj_dvd_ordProj_of_dvd hL hd p) (Nat.ordProj_dvd d p)

/-- At the prime-power CRT coordinate, the conductor keeps exactly the
valuation of the global conductor. -/
theorem prime_component_conductor {L : ℕ} [NeZero L] (A : DirichletCharacter ℂ L)
    (i : L.primeFactors) :
    (component (ZMod.equivPi L (NeZero.ne L)) A i).conductor=(i:ℕ)^A.conductor.factorization i := by
  rw [component_conductor _ (fun k : L.primeFactors => Nat.ordProj_dvd L k)
    L.pairwise_coprime_pow_primeFactors_factorization A i]
  exact prime_part_gcd (Nat.prime_of_mem_primeFactors i.property) (NeZero.ne L) A.conductor_dvd_level

end Conjectures.Goldbach.SharpSingularSeriesRatiosProof.TwistedGoldbachConductorComponents

/-! A modulus-uniform off-diagonal estimate. The loss depends only on
the reduced additive denominator and is of double logarithmic size.
The Mertens estimate is imported from the existing Goldbach order-tail
module. See Pintz I, (1.21)–(1.22). -/

namespace Conjectures.Goldbach.SharpSingularSeriesRatiosProof.TwistedGoldbachConductorSuppression

open Finset Real DirichletCharacter ErdosStraus.PrimeEstimates.Mertens
open TwistedGoldbachConductorValue TwistedGoldbachMixedPrincipal TwistedGoldbachLocalProduct
open scoped BigOperators Classical

noncomputable def totRatio (q : ℕ) : ℝ := (q:ℝ)/q.totient
noncomputable def primeRatio (p : ℕ) : ℝ := (p:ℝ)/((p:ℝ)-1)
noncomputable def doubleLog (q : ℕ) : ℝ := 1+Real.log (1+Real.log q)

theorem totient_euler (q : ℕ) (hq : 0 < q) :
    totRatio q = ∏ p ∈ q.primeFactors, primeRatio p := by
  have pos : 0 < ∏ p ∈ q.primeFactors, ((p:ℝ)-1) := prod_pos (fun p hp =>
    sub_pos.mpr (by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).one_lt))
  have H := congrArg (fun n : ℕ => (n:ℝ)) (Nat.totient_mul_prod_primeFactors q)
  simp only [Nat.cast_mul,Nat.cast_prod] at H
  have each : ∏ p ∈ q.primeFactors, ((p-1:ℕ):ℝ) = ∏ p ∈ q.primeFactors, ((p:ℝ)-1) :=
    prod_congr rfl (fun p hp => by rw [Nat.cast_sub (Nat.prime_of_mem_primeFactors hp).one_le]; norm_num)
  rw [each] at H
  unfold totRatio primeRatio
  rw [prod_div_distrib,div_eq_div_iff (by exact_mod_cast (Nat.totient_pos.mpr hq).ne') pos.ne']
  linarith

private theorem count_factors (q : ℕ) (hq : 0 < q) : (q.primeFactors.card:ℝ) ≤ 2*log q := by
  have bound : 2^q.primeFactors.card ≤ q := (Finset.pow_card_le_prod _ _ _
    (fun p hp => (Nat.prime_of_mem_primeFactors hp).two_le)).trans (Nat.le_of_dvd hq (Nat.prod_primeFactors_dvd q))
  have logs : (q.primeFactors.card:ℝ)*log 2 ≤ log q := by
    rw [← log_pow]
    apply log_le_log (by positivity)
    exact_mod_cast bound
  have half := Real.one_sub_inv_le_log_of_pos (x := 2) (by norm_num)
  norm_num at half
  nlinarith [mul_nonneg (Nat.cast_nonneg (α:=ℝ) q.primeFactors.card) (show 0 ≤ log 2-1/2 by linarith)]

theorem doubleLog_one_le (q : ℕ) (hq : 0 < q) : 1 ≤ doubleLog q := by
  have hlog : 0 ≤ log q := log_nonneg (by exact_mod_cast hq)
  exact le_add_of_nonneg_right (log_nonneg (by linarith))

theorem totient_double_log :
    ∃ C : ℝ, 0 < C ∧ ∀ q : ℕ, 0 < q → totRatio q ≤ C * doubleLog q := by
  obtain ⟨A,hA,HM⟩ := mertensSecond
  let z := ∑' n : ℕ, (1:ℝ)/(n:ℝ)^2
  let K := mertensSecondConstant+A/log 2+1+2*z
  refine ⟨exp K,exp_pos K,?_⟩
  intro q hq
  let S := q.primeFactors
  let x := 2*(1+log q)
  have hlog : 0 ≤ log q := log_nonneg (by exact_mod_cast hq)
  have hx : 2 ≤ x := by dsimp [x]; linarith
  have hp (p : ℕ) (h : p ∈ S) : p.Prime := Nat.prime_of_mem_primeFactors h
  have small : ∑ p ∈ S.filter (fun p : ℕ => (p:ℝ) ≤ x), 1/(p:ℝ) ≤ primeReciprocalSum ⌊x⌋₊ := by
    apply sum_le_sum_of_subset_of_nonneg
    · intro p hh
      exact mem_primesUpTo.mpr ⟨hp p (mem_filter.mp hh).1,Nat.le_floor (mem_filter.mp hh).2⟩
    · intro _ _ _; positivity
  have large : ∑ p ∈ S.filter (fun p : ℕ => ¬(p:ℝ) ≤ x), 1/(p:ℝ) ≤ 1 := by
    let B := S.filter (fun p : ℕ => ¬(p:ℝ) ≤ x)
    have hc : (B.card:ℝ) ≤ x := by
      have bnd : (B.card:ℝ) ≤ S.card := by exact_mod_cast card_filter_le S (fun p : ℕ => ¬(p:ℝ) ≤ x)
      dsimp [x]
      linarith [count_factors q hq]
    calc
      _ ≤ ∑ _p ∈ B, 1/x := sum_le_sum (fun p hh =>
        one_div_le_one_div_of_le (by linarith) (le_of_not_ge (mem_filter.mp hh).2))
      _ ≤ 1 := by simpa only [sum_const,nsmul_eq_mul,mul_one_div] using (div_le_one (by linarith : 0<x)).mpr hc
  have recip : ∑ p ∈ S, 1/(p:ℝ) ≤ log (log x)+mertensSecondConstant+A/log 2+1 := by
    have H := (abs_le.mp (HM x hx)).2
    have Adiv := div_le_div_of_nonneg_left hA.le (log_pos (by norm_num : (1:ℝ)<2)) (log_le_log (by norm_num) hx)
    linarith [sum_filter_add_sum_filter_not S (fun p => (p:ℝ)≤x) (fun p => 1/(p:ℝ))]
  have zbound : ∑ p ∈ S, 1/(p:ℝ)^2 ≤ z :=
    (Real.summable_one_div_nat_pow.mpr (by decide : 1<2)).sum_le_tsum S (fun _ _ => by positivity)
  have terms : ∑ p ∈ S, 1/((p:ℝ)-1) ≤ log (log x)+K := by
    have point (p : ℕ) (hh : p ∈ S) : 1/((p:ℝ)-1) ≤ 1/(p:ℝ) + 2*(1/(p:ℝ)^2) := by
      have h : (2:ℝ)≤p := by exact_mod_cast (hp p hh).two_le
      have h0 : 0 < (p:ℝ) := by linarith
      have h1 : 0 < (p:ℝ)-1 := by linarith
      field_simp [h0.ne',h1.ne']
      nlinarith
    have sum := sum_le_sum point
    rw [sum_add_distrib,← mul_sum] at sum
    dsimp only [K]
    linarith
  rw [totient_euler q hq]
  calc
    _ ≤ ∏ p ∈ S, exp (1/((p:ℝ)-1)) := by
      apply prod_le_prod₀
      · intro p h
        have h1 : 1 < (p:ℝ) := by exact_mod_cast (hp p h).one_lt
        exact div_nonneg (Nat.cast_nonneg p) (by linarith)
      · intro p h
        have h1 : 1 < (p:ℝ) := by exact_mod_cast (hp p h).one_lt
        have eqn : primeRatio p = 1/((p:ℝ)-1)+1 := by unfold primeRatio; field_simp; ring
        rw [eqn]
        exact add_one_le_exp _
    _ = exp (∑ p ∈ S, 1/((p:ℝ)-1)) := (exp_sum ..).symm
    _ ≤ exp (log (log x)+K) := exp_le_exp.mpr terms
    _ ≤ _ := by
      rw [exp_add,exp_log (log_pos (by linarith : 1<x)),mul_comm]
      apply mul_le_mul_of_nonneg_left _ (exp_pos K).le
      dsimp [x,doubleLog]
      rw [log_mul (by norm_num) (by positivity)]
      linarith [log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)]

private theorem primeRatio_ge_one {p : ℕ} (hp : p.Prime) : 1 ≤ primeRatio p := by
  have h : (1:ℝ)<p := by exact_mod_cast hp.one_lt
  exact (le_div_iff₀ (by linarith : 0 < (p:ℝ)-1)).mpr (by linarith)

/-- The large ordinary Euler factors at primes shared with the target
cancel before any bound on the totient is used. -/
theorem cancel_common_primes (L m : ℕ) [NeZero L] (he : Even m) :
    totRatio L ≤ 2*ordinaryWeight L m * totRatio (L/(m.gcd L)) := by
  let g := m.gcd L
  let j := L/g
  have hg : g ∣ L := Nat.gcd_dvd_right m L
  have hj : 0 < j := Nat.div_pos (Nat.le_of_dvd (NeZero.pos L) hg) (Nat.gcd_pos_of_pos_right m (NeZero.pos L))
  let A := L.primeFactors.filter (fun p => p ∣ m)
  let B := L.primeFactors.filter (fun p => ¬p ∣ m)
  have primeB (p : ℕ) (hp : p ∈ B) := Nat.prime_of_mem_primeFactors (mem_filter.mp hp).1
  have primeA (p : ℕ) (hp : p ∈ A) := Nat.prime_of_mem_primeFactors (mem_filter.mp hp).1
  have splitφ : (∏ p ∈ A, primeRatio p)*(∏ p ∈ B, primeRatio p) = totRatio L := by
    rw [totient_euler L (NeZero.pos L)]
    exact prod_filter_mul_prod_filter_not L.primeFactors _ primeRatio
  have splitW : (∏ p ∈ A, primeRatio p)*(∏ p ∈ B, localWeight m p) = ordinaryWeight L m := by
    rw [ordinary_product]
    have same : ∏ p ∈ A, primeRatio p = ∏ p ∈ A, localWeight m p := by
      exact prod_congr rfl (fun p hp => by simp only [localWeight,ite_eq_left (mem_filter.mp hp).2,primeRatio])
    rw [same]
    exact prod_filter_mul_prod_filter_not L.primeFactors _ _
  let Q := ∏ p ∈ B, p
  let _ : NeZero Q := ⟨(prod_pos (fun p hp => (primeB p hp).pos)).ne'⟩
  have lower := uniform_weight Q m he
  have half : (1/2:ℝ) ≤ ∏ p ∈ B, localWeight m p := by
    have factors : Q.primeFactors=B := Nat.primeFactors_prod primeB
    rw [ordinary_product,factors] at lower
    apply le_trans _ lower
    split <;> norm_num
  have cover : B ⊆ j.primeFactors := by
    intro p hp
    obtain ⟨mem,off⟩ := mem_filter.mp hp
    have hprod : p ∣ g*j := (Nat.mul_div_cancel' hg).symm ▸ Nat.dvd_of_mem_primeFactors mem
    have hd : p ∣ j := ((primeB p hp).dvd_mul.mp hprod).resolve_left
      (fun h => off (h.trans (Nat.gcd_dvd_left m L)))
    exact Nat.mem_primeFactors.mpr ⟨primeB p hp,hd,hj.ne'⟩
  have more : (∏ p ∈ B, primeRatio p) ≤ totRatio j := by
    rw [totient_euler j hj]
    exact prod_le_prod_of_subset_of_one_le₀ cover (fun p h => zero_le_one.trans (primeRatio_ge_one (primeB p h)))
      (fun p hp _ => primeRatio_ge_one (Nat.prime_of_mem_primeFactors hp))
  have a0 : 0 ≤ ∏ p ∈ A, primeRatio p := prod_nonneg (fun p h => zero_le_one.trans (primeRatio_ge_one (primeA p h)))
  have b0 : 0 ≤ ∏ p ∈ B, primeRatio p := prod_nonneg (fun p h => zero_le_one.trans (primeRatio_ge_one (primeB p h)))
  have agrow : (∏ p ∈ A, primeRatio p) ≤ 2*ordinaryWeight L m := by
    rw [← splitW]
    nlinarith [mul_nonneg a0 (sub_nonneg.mpr half)]
  rw [← splitφ]
  exact mul_le_mul agrow more b0 (a0.trans agrow)

theorem conductor_triangle {r s : ℕ} [NeZero r] [NeZero s] {α : DirichletCharacter ℂ r}
    {β : DirichletCharacter ℂ s} (hα : α.IsPrimitive) (hβ : β.IsPrimitive) :
    let d := (inversePair α β).conductor
    r ∣ Nat.lcm d s ∧ s ∣ Nat.lcm d r := by
  intro d
  let L := Nat.lcm r s
  let _ : NeZero L := ⟨(Nat.lcm_pos (NeZero.pos r) (NeZero.pos s)).ne'⟩
  let A := changeLevel (Nat.dvd_lcm_left r s) α
  let B := changeLevel (Nat.dvd_lcm_right r s) β
  let Z := inversePair α β
  have a : A.conductor=r := (conductor_changeLevel ..).trans hα
  have b : B.conductor=s := (conductor_changeLevel ..).trans hβ
  have az : Z*B=A⁻¹ := by
    change (A*B)⁻¹*B=A⁻¹
    rw [mul_comm A B]
    group
  have bz : Z*A=B⁻¹ := by change (A*B)⁻¹*A=B⁻¹; group
  have ar := conductor_mul_dvd_lcm_conductor Z B
  have br := conductor_mul_dvd_lcm_conductor Z A
  rw [az,conductor_inv,a,b] at ar
  rw [bz,conductor_inv,b,a] at br
  exact ⟨ar,br⟩

theorem conductor_saving {r s : ℕ} [NeZero r] [NeZero s] {α : DirichletCharacter ℂ r}
    {β : DirichletCharacter ℂ s} (hα : α.IsPrimitive) (hβ : β.IsPrimitive)
    (m : ℕ) (hm : 0 < m) (he : Even m) :
    let L := Nat.lcm r s
    let j := L/(m.gcd L)
    ‖series α β m‖ * sqrt (((L/r)*(L/s)*j:ℕ):ℝ) ≤
      2*‖series (1 : DirichletCharacter ℂ 1) (1 : DirichletCharacter ℂ 1) m‖*(totRatio j)^2 := by
  intro L j
  let _ : NeZero L := ⟨(Nat.lcm_pos (NeZero.pos r) (NeZero.pos s)).ne'⟩
  let a := L/r
  let b := L/s
  let d := (inversePair α β).conductor
  let O := ‖series (1 : DirichletCharacter ℂ 1) (1 : DirichletCharacter ℂ 1) m‖
  let T := ‖series α β m‖
  let W := ordinaryWeight L m
  have hw : 0 < W := lt_of_lt_of_le (by split <;> norm_num) (uniform_weight L m he)
  have hj : 0 < j := Nat.div_pos (Nat.le_of_dvd (NeZero.pos L) (Nat.gcd_dvd_right m L))
    (Nat.gcd_pos_of_pos_right m (NeZero.pos L))
  have hO : 0 ≤ O := norm_nonneg _
  have hjφ : 0 < (j.totient:ℝ) := by exact_mod_cast Nat.totient_pos.mpr hj
  have hLφ : 0 < (L.totient:ℝ) := by exact_mod_cast Nat.totient_pos.mpr (NeZero.pos L)
  by_cases good : supported r s L d j
  · have H := full_base hα hβ m hm
    dsimp only at H
    rw [base_norm hα hβ m] at H
    change T*W=O*(if supported r s L d j then _ else 0) at H
    rw [ite_eq_left good] at H
    have ra : sqrt r * sqrt a = sqrt L := by
      rw [← sqrt_mul (Nat.cast_nonneg r),← Nat.cast_mul,Nat.mul_div_cancel' (Nat.dvd_lcm_left r s)]
    have sb : sqrt s * sqrt b = sqrt L := by
      rw [← sqrt_mul (Nat.cast_nonneg s),← Nat.cast_mul,Nat.mul_div_cancel' (Nat.dvd_lcm_right r s)]
    have dj : sqrt d*sqrt j ≤ (j:ℝ) := by
      have h : d ≤ j := Nat.le_of_dvd hj good.2.2.1
      calc
        _ ≤ sqrt j*sqrt j := mul_le_mul_of_nonneg_right (sqrt_le_sqrt (by exact_mod_cast h)) (sqrt_nonneg _)
        _ = _ := Real.mul_self_sqrt (Nat.cast_nonneg _)
    have size : (sqrt r*sqrt s*sqrt d)*sqrt ((a*b*j:ℕ):ℝ) ≤ (L:ℝ)*j := by
      push_cast
      rw [sqrt_mul (mul_nonneg (Nat.cast_nonneg a) (Nat.cast_nonneg b)),sqrt_mul (Nat.cast_nonneg a)]
      calc
        _ = (sqrt r*sqrt a)*(sqrt s*sqrt b)*(sqrt d*sqrt j) := by ring
        _ ≤ _ := by rw [ra,sb,Real.mul_self_sqrt (Nat.cast_nonneg L)]; exact mul_le_mul_of_nonneg_left dj (Nat.cast_nonneg _)
    have clean := cancel_common_primes L m he
    change totRatio L ≤ 2*W*totRatio j at clean
    change T*sqrt ((a*b*j:ℕ):ℝ) ≤ 2*O*(totRatio j)^2
    apply (le_of_mul_le_mul_left _ hw)
    calc
      W*(T*sqrt ((a*b*j:ℕ):ℝ)) = (T*W)*sqrt ((a*b*j:ℕ):ℝ) := by ring
      _ = O*((sqrt r*sqrt s*sqrt d)*sqrt ((a*b*j:ℕ):ℝ)/((L.totient:ℝ)*j.totient)) := by rw [H]; ring
      _ ≤ O*((L:ℝ)*j/((L.totient:ℝ)*j.totient)) := mul_le_mul_of_nonneg_left
        (div_le_div_of_nonneg_right size (mul_pos hLφ hjφ).le) hO
      _ = O*(totRatio L*totRatio j) := by unfold totRatio; ring
      _ ≤ O*((2*W*totRatio j)*totRatio j) := mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right clean (div_nonneg (Nat.cast_nonneg j) hjφ.le)) hO
      _ = _ := by ring
  · have zero := not_ne_iff.mp (mt (full_support hα hβ m hm he).mp good)
    rw [zero,norm_zero,zero_mul]
    positivity

private theorem reduced_dvd (m k t : ℕ) (hk : 0 < k) : k/(m.gcd k) ∣ t ↔ k ∣ m*t := by
  let g := m.gcd k
  let v := k/g
  let u := m/g
  have hg : 0 < g := Nat.gcd_pos_of_pos_right m hk
  have gm : g*u=m := Nat.mul_div_cancel' (Nat.gcd_dvd_left m k)
  have gk : g*v=k := Nat.mul_div_cancel' (Nat.gcd_dvd_right m k)
  have cop : u.Coprime v := Nat.coprime_div_gcd_div_gcd hg
  change v ∣ t ↔ k ∣ m*t
  rw [← gk,← gm,mul_assoc,Nat.mul_dvd_mul_iff_left hg]
  exact ⟨fun h => h.trans (dvd_mul_left t u),cop.symm.dvd_of_dvd_mul_left⟩

theorem reduced_lcm {r s : ℕ} [NeZero r] [NeZero s] (m : ℕ) :
    (Nat.lcm r s)/(m.gcd (Nat.lcm r s)) = Nat.lcm (r/(m.gcd r)) (s/(m.gcd s)) := by
  let L := Nat.lcm r s
  have equiv (t : ℕ) : L/(m.gcd L) ∣ t ↔ Nat.lcm (r/(m.gcd r)) (s/(m.gcd s)) ∣ t := by
    rw [reduced_dvd m L t (Nat.lcm_pos (NeZero.pos r) (NeZero.pos s)),Nat.lcm_dvd_iff,Nat.lcm_dvd_iff,
      reduced_dvd m r t (NeZero.pos r),reduced_dvd m s t (NeZero.pos s)]
  exact Nat.dvd_antisymm ((equiv _).mpr (dvd_refl _)) ((equiv _).mp (dvd_refl _))

theorem complementary_dvd {r s : ℕ} [NeZero r] [NeZero s] {α : DirichletCharacter ℂ r}
    {β : DirichletCharacter ℂ s} (hα : α.IsPrimitive) (hβ : β.IsPrimitive) {m : ℕ}
    (good : supported r s (Nat.lcm r s) (inversePair α β).conductor (Nat.lcm r s / (m.gcd (Nat.lcm r s)))) :
    let L := Nat.lcm r s
    let d := (inversePair α β).conductor
    L/r ∣ d ∧ L/s ∣ d := by
  intro L d
  have hr : r ∣ L := Nat.dvd_lcm_left ..
  have hs : s ∣ L := Nat.dvd_lcm_right ..
  have ar : L/r ∣ s := Nat.dvd_of_mul_dvd_mul_left (NeZero.pos r) (by rw [Nat.mul_div_cancel' hr]; exact Nat.lcm_dvd_mul r s)
  have bs : L/s ∣ r := Nat.dvd_of_mul_dvd_mul_left (NeZero.pos s) (by rw [Nat.mul_div_cancel' hs,mul_comm]; exact Nat.lcm_dvd_mul r s)
  obtain ⟨A,B⟩ := conductor_triangle hα hβ
  exact ⟨good.1.2.dvd_of_dvd_mul_right (ar.trans (B.trans (Nat.lcm_dvd_mul d r))),
    good.2.1.2.dvd_of_dvd_mul_right (bs.trans (A.trans (Nat.lcm_dvd_mul d s)))⟩

/-- The five quantities in Pintz I (1.22). The denominator of each of
the first two quotients is the gcd of the source conductors. -/
def complexity (r s d m : ℕ) : ℕ :=
  max (max ((s/(r.gcd s))^2) ((r/(r.gcd s))^2)) (max (max (r/(m.gcd r)) (s/(m.gcd s))) d)

private theorem doubleLog_compare {j U : ℕ} (hj : 0 < j) (hU : 0 < U) (upper : j ≤ U^2) :
    doubleLog j ≤ 2 * doubleLog U := by
  have logU : 0 ≤ log U := log_nonneg (by exact_mod_cast hU)
  have lelog : log j ≤ 2*log U := by
    have H := log_le_log (by exact_mod_cast hj : (0:ℝ)<j) (by exact_mod_cast upper : (j:ℝ)≤(U:ℝ)^2)
    simpa only [log_pow,Nat.cast_ofNat] using H
  have le' : log (1+log j) ≤ log (2*(1+log U)) := log_le_log
    (by linarith [log_nonneg (by exact_mod_cast hj : (1:ℝ)≤j)]) (by linarith)
  rw [log_mul (by norm_num) (by positivity)] at le'
  unfold doubleLog
  linarith [log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2),log_nonneg (by linarith : (1:ℝ)≤1+log U)]

/-- The off-diagonal comparison, with its double logarithmic loss and one
constant uniform in every conductor and positive even target. -/
theorem pintz_comparison :
    ∃ C : ℝ, 0 < C ∧ ∀ (r s : ℕ) [NeZero r] [NeZero s] (α : DirichletCharacter ℂ r)
    (β : DirichletCharacter ℂ s), α.IsPrimitive → β.IsPrimitive → ∀ m : ℕ, 0 < m → Even m →
    let U := complexity r s (inversePair α β).conductor m
    ‖series α β m‖ * sqrt U ≤ C * ‖series (1 : DirichletCharacter ℂ 1) (1 : DirichletCharacter ℂ 1) m‖*(doubleLog U)^2 := by
  obtain ⟨C,hC,phi⟩ := totient_double_log
  refine ⟨8*C^2,by positivity,?_⟩
  intro r s _ _ α β hα hβ m hm he U
  let L := Nat.lcm r s
  let k := r.gcd s
  let a := L/r
  let b := L/s
  let v := r/(m.gcd r)
  let w := s/(m.gcd s)
  let j := L/(m.gcd L)
  let d := (inversePair α β).conductor
  let T := ‖series α β m‖
  let O := ‖series (1 : DirichletCharacter ℂ 1) (1 : DirichletCharacter ℂ 1) m‖
  have Lp : 0 < L := Nat.lcm_pos (NeZero.pos r) (NeZero.pos s)
  have hj : 0 < j := Nat.div_pos (Nat.le_of_dvd Lp (Nat.gcd_dvd_right m L)) (Nat.gcd_pos_of_pos_right m Lp)
  have ap : 0 < a := Nat.div_pos (Nat.le_of_dvd Lp (Nat.dvd_lcm_left ..)) (NeZero.pos r)
  have bp : 0 < b := Nat.div_pos (Nat.le_of_dvd Lp (Nat.dvd_lcm_right ..)) (NeZero.pos s)
  have aeq : a=s/k := by
    change Nat.lcm r s/r=s/r.gcd s
    rw [Nat.lcm_eq_mul_div,Nat.mul_div_assoc _ (Nat.gcd_dvd_right r s),Nat.mul_div_cancel_left _ (NeZero.pos r)]
  have beq : b=r/k := by
    change Nat.lcm r s/s=r/r.gcd s
    rw [Nat.lcm_comm,Nat.lcm_eq_mul_div,Nat.mul_div_assoc _ (Nat.gcd_dvd_right s r),Nat.mul_div_cancel_left _ (NeZero.pos s),Nat.gcd_comm]
  have Ueq : U=max (max (a^2) (b^2)) (max (max v w) d) := by rw [aeq,beq]; rfl
  have vu : v ≤ U := Ueq ▸ (le_max_left v w).trans ((le_max_left _ d).trans (le_max_right ..))
  have wu : w ≤ U := Ueq ▸ (le_max_right v w).trans ((le_max_left _ d).trans (le_max_right ..))
  have au : a^2 ≤ U := Ueq ▸ (le_max_left _ _).trans (le_max_left ..)
  have up : 0 < U := (pow_pos ap 2).trans_le au
  have jeq : j = Nat.lcm v w := reduced_lcm m
  have ju : j ≤ U^2 := by
    rw [jeq,pow_two]
    exact (Nat.le_of_dvd (Nat.mul_pos (Nat.div_pos (Nat.le_of_dvd (NeZero.pos r) (Nat.gcd_dvd_right m r))
        (Nat.gcd_pos_of_pos_right m (NeZero.pos r))) (Nat.div_pos (Nat.le_of_dvd (NeZero.pos s) (Nat.gcd_dvd_right m s))
        (Nat.gcd_pos_of_pos_right m (NeZero.pos s)))) (Nat.lcm_dvd_mul v w)).trans (Nat.mul_le_mul vu wu)
  by_cases good : supported r s L d j
  · obtain ⟨ad,bd⟩ := complementary_dvd hα hβ (m := m) good
    have dj := Nat.le_of_dvd hj good.2.2.1
    have aj := Nat.le_of_dvd hj (ad.trans good.2.2.1)
    have bj := Nat.le_of_dvd hj (bd.trans good.2.2.1)
    have top : U ≤ a*b*j := by
      rw [Ueq,max_le_iff,max_le_iff,max_le_iff,max_le_iff]
      have jtop : j ≤ a*b*j := Nat.le_mul_of_pos_left j (Nat.mul_pos ap bp)
      have vj : v ≤ j := Nat.le_of_dvd hj (jeq ▸ Nat.dvd_lcm_left v w)
      have wj : w ≤ j := Nat.le_of_dvd hj (jeq ▸ Nat.dvd_lcm_right v w)
      refine ⟨⟨?_,?_⟩,⟨⟨vj.trans jtop,wj.trans jtop⟩,dj.trans jtop⟩⟩
      · rw [pow_two]
        exact Nat.mul_le_mul (Nat.le_mul_of_pos_right a bp) aj
      · rw [pow_two]
        exact Nat.mul_le_mul (Nat.le_mul_of_pos_left b ap) bj
    have upper := (phi j hj).trans (mul_le_mul_of_nonneg_left (doubleLog_compare hj up ju) hC.le)
    have nonneg : 0 ≤ totRatio j := div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    have hO : 0 ≤ O := norm_nonneg _
    calc
      T*sqrt U ≤ T*sqrt ((a*b*j:ℕ):ℝ) := mul_le_mul_of_nonneg_left (sqrt_le_sqrt (by exact_mod_cast top)) (norm_nonneg _)
      _ ≤ 2*O*(totRatio j)^2 := conductor_saving hα hβ m hm he
      _ ≤ 2*O*(C*(2*doubleLog U))^2 := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ nonneg upper 2) (by positivity)
      _ = _ := by ring
  · have zero := not_ne_iff.mp (mt (full_support hα hβ m hm he).mp good)
    rw [zero,norm_zero,zero_mul]
    positivity

end Conjectures.Goldbach.SharpSingularSeriesRatiosProof.TwistedGoldbachConductorSuppression

/-! An explicit separation between the twisted and ordinary singular
series outside the five divisibility conditions in Pintz I, (7.8).
We use the exact local Fourier norms to obtain the sharp constant sqrt(5)/3. -/

namespace Conjectures.Goldbach.SharpSingularSeriesRatiosProof.TwistedGoldbachExceptionalGap

open Finset DirichletCharacter Real TwistedGoldbachLocalProduct TwistedGoldbachConductorRatio
open TwistedGoldbachConductorValue TwistedGoldbachConductorComponents
open B13BilateralVaughanReductionProof
open scoped BigOperators Classical

/-- A primitive pair on a prime power has Jacobi norm at most the
modulus divided by the square root of the reduced additive denominator. -/
theorem prime_power_bound {p : ℕ} [hp : Fact p.Prime] (n m : ℕ)
    {A B : DirichletCharacter ℂ (p*p^n)} (hA : A.IsPrimitive) (hB : B.IsPrimitive) :
    let q := p*p^n
    let j := q/(m.gcd q)
    1 < j → ‖J A B (m:ZMod q)‖*sqrt j ≤ q := by
  intro q j hj
  have qp : 0 < q := Nat.mul_pos hp.out.pos (pow_pos hp.out.pos n)
  have jd : j ∣ q := Nat.div_dvd_of_dvd (Nat.gcd_dvd_right m q)
  have eqQ : q=p^(n+1) := by rw [pow_succ']
  obtain ⟨k,_,jpk⟩ := (Nat.dvd_prime_pow hp.out).mp (eqQ ▸ jd)
  cases k with
  | zero => simp [jpk] at hj
  | succ k =>
    let θ := (A*B)⁻¹
    have F := PrimePowerTwistedGoldbachDensity.primitive_norm hA hB (m:ZMod q)
    change ‖J A B (m:ZMod q)‖ = ‖ZMod.dft (⇑θ) (m:ZMod q)‖ at F
    rw [fourierTransform_eq_gaussSum_mulShift] at F
    have G := (DyadicMixedB4CharacterFactorBound.norm_gauss_neg_shift_le θ (m:ZMod q)).trans_eq (shifted_norm θ m)
    change _ ≤ (if θ.conductor ∣ j ∧ TwistedGoldbachConductorValue.admissible θ.conductor j then
      (q.totient:ℝ)/j.totient * sqrt θ.conductor else 0) at G
    rw [← F] at G
    have top : ‖J A B (m:ZMod q)‖ ≤ (q.totient:ℝ)/j.totient * sqrt j := by
      split_ifs at G with h
      · exact G.trans (mul_le_mul_of_nonneg_left (sqrt_le_sqrt (by exact_mod_cast Nat.le_of_dvd (by omega : 0 < j) h.1)) (by positivity))
      · exact G.trans (by positivity)
    calc
      _ ≤ ((q.totient:ℝ)/j.totient * sqrt j)*sqrt j := mul_le_mul_of_nonneg_right top (sqrt_nonneg _)
      _ = (q.totient:ℝ)/j.totient * j := by rw [mul_assoc,mul_self_sqrt (Nat.cast_nonneg _)]
      _ = q := by
        rw [eqQ,jpk,Nat.totient_prime_pow_succ hp.out,Nat.totient_prime_pow_succ hp.out]
        push_cast
        have hp0 : (p:ℝ) ≠ 0 := by exact_mod_cast hp.out.ne_zero
        have hsub : ((p-1:ℕ):ℝ) ≠ 0 := by exact_mod_cast (Nat.sub_pos_of_lt hp.out.one_lt).ne'
        field_simp
        ring

private theorem prime_sqrt_bound {p : ℕ} (hp : 5 ≤ p) :
    3*sqrt p ≤ sqrt 5*((p:ℝ)-2) := by
  have h : (5:ℝ) ≤ p := by exact_mod_cast hp
  apply (sq_le_sq₀ (by positivity) (mul_nonneg (sqrt_nonneg _) (by linarith))).mp
  rw [mul_pow,mul_pow,sq_sqrt (Nat.cast_nonneg p),sq_sqrt (by norm_num : (0:ℝ) ≤ 5)]
  nlinarith [mul_nonneg (sub_nonneg.mpr h) (show 0 ≤ 5*(p:ℝ)-4 by linarith)]

private theorem arithmetic_gap {p j m : ℕ} (pj : p ≤ j) (he : Even m)
    (out : (p=2 ∧ 8 ≤ j) ∨ (p=3 ∧ 27 ≤ j) ∨ 5 ≤ p) :
    3*(p:ℝ) ≤ sqrt 5*(if p ∣ m then (p:ℝ)-1 else (p:ℝ)-2)*sqrt j := by
  rcases out with ⟨rfl,hj⟩ | ⟨rfl,hj⟩ | hp
  · rw [ite_eq_left (even_iff_two_dvd.mp he)]
    have h : (8:ℝ) ≤ j := by exact_mod_cast hj
    have z : (11/4:ℝ) ≤ sqrt j := le_sqrt_of_sq_le (by linarith)
    have v : (11/5:ℝ) ≤ sqrt 5 := le_sqrt_of_sq_le (by norm_num)
    have both := mul_le_mul v z (by norm_num) (sqrt_nonneg _)
    norm_num at *
    linarith
  · have h : (27:ℝ) ≤ j := by exact_mod_cast hj
    have z : 5 ≤ sqrt j := le_sqrt_of_sq_le (by linarith)
    have v : 2 ≤ sqrt 5 := le_sqrt_of_sq_le (by norm_num)
    have both := mul_le_mul v z (by norm_num) (sqrt_nonneg _)
    split_ifs <;> norm_num <;> nlinarith only [both]
  · have sp := prime_sqrt_bound hp
    have sj := sqrt_le_sqrt (by exact_mod_cast pj : (p:ℝ) ≤ j)
    have h : (5:ℝ) ≤ p := by exact_mod_cast hp
    have scaled := mul_le_mul sp sj (sqrt_nonneg _)
      (mul_nonneg (sqrt_nonneg _) (show 0 ≤ (p:ℝ)-2 by linarith))
    rw [mul_assoc,mul_self_sqrt (Nat.cast_nonneg p)] at scaled
    split_ifs
    · exact scaled.trans (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (by linarith) (sqrt_nonneg _)) (sqrt_nonneg _))
    · exact scaled

theorem local_power_gap_sharp {p : ℕ} [hp : Fact p.Prime] (n m : ℕ) (he : Even m)
    {A B : DirichletCharacter ℂ (p*p^n)} (hA : A.IsPrimitive) (hB : B.IsPrimitive) :
    let q := p*p^n
    let j := q/(m.gcd q)
    p ≤ j → ((p=2 ∧ 8 ≤ j) ∨ (p=3 ∧ 27 ≤ j) ∨ 5 ≤ p) →
    3*‖J A B (m:ZMod q)‖ ≤ sqrt 5*‖J (1 : DirichletCharacter ℂ q) 1 (m:ZMod q)‖ := by
  intro q j pj out
  have bound := prime_power_bound n m hA hB (hp.out.one_lt.trans_le pj)
  have G := arithmetic_gap (m := m) pj he out
  have P : 0 < sqrt (j:ℝ) := sqrt_pos.mpr (by exact_mod_cast hp.out.pos.trans_le pj)
  apply le_of_mul_le_mul_right (a := sqrt (j:ℝ)) <;> try assumption
  rw [ordinary_prime_power n m]
  have G' := mul_le_mul_of_nonneg_left G (by positivity : 0 ≤ ((p^n:ℕ):ℝ))
  change ‖J A B (m:ZMod q)‖*sqrt j ≤ (↑(p*p^n):ℝ) at bound
  push_cast at bound G' ⊢
  linarith only [show 3*(‖J A B (m:ZMod q)‖*sqrt j) ≤ 3*((p:ℝ)*(p:ℝ)^n) by linarith,
    show (p:ℝ)^n*(3*p) ≤ _ from G']

private theorem prime_local_gap {p : ℕ} [hp : Fact p.Prime] (m : ℕ)
    (A B : DirichletCharacter ℂ p) (mp : ¬p ∣ m) (hab : A ≠ 1 ∨ B ≠ 1) (big : 5 ≤ p) :
    3*‖J A B (m:ZMod p)‖ ≤ sqrt 5*‖J (1 : DirichletCharacter ℂ p) 1 (m:ZMod p)‖ := by
  have nonzero : (m:ZMod p) ≠ 0 := mt (ZMod.natCast_eq_zero_iff m p).mp mp
  have top := SquarefreeTwistedGoldbachDensity.local_norm A B (m:ZMod p)
  have ordinary := SquarefreeTwistedGoldbachDensity.local_norm (1 : DirichletCharacter ℂ p) 1 (m:ZMod p)
  have pair : ¬(A=1 ∧ B=1) := by tauto
  simp only [nonzero,ite_false,pair] at top
  simp only [nonzero,ite_false,and_self,ite_true] at ordinary
  change 3*‖SquarefreeTwistedGoldbachDensity.localSum A B (m:ZMod p)‖ ≤
    sqrt 5*‖SquarefreeTwistedGoldbachDensity.localSum (1 : DirichletCharacter ℂ p) 1 (m:ZMod p)‖
  rw [top,ordinary]
  split_ifs
  · have : (5:ℝ) ≤ p := by exact_mod_cast big
    have hh : 2 ≤ sqrt 5 := le_sqrt_of_sq_le (by norm_num)
    nlinarith [mul_nonneg (sub_nonneg.mpr hh) (show 0 ≤ (p:ℝ)-2 by linarith)]
  · exact prime_sqrt_bound big

private theorem reduced_prime_part {L p : ℕ} (hp : p.Prime) (hL : L ≠ 0) (m : ℕ) :
    let q := p^L.factorization p
    q/(m.gcd q) = p^(L/(m.gcd L)).factorization p := by
  intro q
  let g := m.gcd L
  have gd : g ∣ L := Nat.gcd_dvd_right ..
  have Q : q ∣ L := Nat.ordProj_dvd L p
  have same : m.gcd q = q.gcd g := by
    change m.gcd q = q.gcd (m.gcd L)
    rw [Nat.gcd_left_comm,Nat.gcd_eq_left Q]
  have gq := prime_part_gcd hp hL gd
  change q.gcd g = p^g.factorization p at gq
  have le := (Nat.factorization_le_iff_dvd (Nat.gcd_pos_of_pos_right m (Nat.pos_of_ne_zero hL)).ne' hL).mpr gd p
  rw [same,gq,Nat.factorization_div gd]
  exact Nat.pow_div le hp.pos

private theorem offending_prime {j : ℕ} (hj : 0 < j) (out : ¬ j ∣ 36) :
    ∃ p : ℕ, p.Prime ∧ p ∣ j ∧ ((p=2 ∧ 8 ∣ j) ∨ (p=3 ∧ 27 ∣ j) ∨ 5 ≤ p) := by
  by_contra absent
  apply out
  apply (Nat.factorization_le_iff_dvd hj.ne' (by decide : (36:ℕ) ≠ 0)).mp
  intro p
  by_cases hp : p.Prime
  · by_cases d : p ∣ j
    · have H (u : (p=2 ∧ 8 ∣ j) ∨ (p=3 ∧ 27 ∣ j) ∨ 5 ≤ p) := absent ⟨p,hp,d,u⟩
      have small : p < 5 := by by_contra! h; exact H (.inr (.inr h))
      have which : p=2 ∨ p=3 := by interval_cases p <;> norm_num at *
      rcases which with rfl | rfl
      · apply le_trans (b := 2) _ ((Nat.prime_two.pow_dvd_iff_le_factorization (by decide : (36:ℕ) ≠ 0)).mp (by decide : 2^2 ∣ 36))
        have h : ¬ 3 ≤ j.factorization 2 := fun e => H (.inl ⟨rfl,(Nat.prime_two.pow_dvd_iff_le_factorization hj.ne').mpr e⟩)
        omega
      · apply le_trans (b := 2) _ ((Nat.prime_three.pow_dvd_iff_le_factorization (by decide : (36:ℕ) ≠ 0)).mp (by decide : 3^2 ∣ 36))
        have h : ¬ 3 ≤ j.factorization 3 := fun e => H (.inr (.inl ⟨rfl,(Nat.prime_three.pow_dvd_iff_le_factorization hj.ne').mpr e⟩))
        omega
    · simp [Nat.factorization_eq_zero_of_not_dvd d]
  · simp [Nat.factorization_eq_zero_of_not_prime _ hp]

private theorem primitive_source_dvd {p L r n : ℕ} (hp : p.Prime)
    (hr : r ∣ L) (good : TwistedGoldbachConductorValue.admissible r L)
    (hd : p^(n+2) ∣ L) : p^(n+2) ∣ r := by
  let a := L/r
  have eqn : r*a=L := Nat.mul_div_cancel' hr
  have hpow : p^(n+2) ∣ r*a := eqn ▸ hd
  by_cases hdpa : p ∣ a
  · have cop : p.Coprime r := good.2.of_dvd_left hdpa
    have all : p^(n+2) ∣ a := (cop.pow_left _).dvd_of_dvd_mul_left hpow
    have bad : p*p ∣ a := (show p*p ∣ p^(n+2) by rw [← pow_two]; exact pow_dvd_pow _ (by omega)).trans all
    exact False.elim (Nat.squarefree_iff_prime_squarefree.mp good.1 p hp bad)
  · exact ((hp.coprime_iff_not_dvd.mpr hdpa).pow_left _).dvd_of_dvd_mul_right hpow

private theorem complementary_odd {L r m : ℕ} (rL : r ∣ L) (he : Even m)
    (good : TwistedGoldbachConductorValue.admissible r L)
    (div : L/r ∣ L/(m.gcd L)) : ¬2 ∣ L/r := by
  let a := L/r
  let g := m.gcd L
  let j := L/g
  have ra : r*a=L := Nat.mul_div_cancel' rL
  have gj : g*j=L := Nat.mul_div_cancel' (Nat.gcd_dvd_right m L)
  intro ha
  have cp : Nat.Coprime 2 r := good.2.of_dvd_left ha
  have twoL : 2 ∣ L := ra ▸ ha.trans (dvd_mul_left a r)
  have hdg : 2 ∣ g := Nat.dvd_gcd (even_iff_two_dvd.mp he) twoL
  have bad : 2*2 ∣ L := gj ▸ Nat.mul_dvd_mul hdg (ha.trans div)
  have badA : 2*2 ∣ a := (cp.pow_left 2).dvd_of_dvd_mul_left (ra ▸ bad)
  exact Nat.squarefree_iff_prime_squarefree.mp good.1 2 Nat.prime_two badA

private theorem small_complement {a : ℕ} (h : a ∣ 36) (hs : Squarefree a)
    (odd : ¬2 ∣ a) : a ∣ 3 := by
  have le := Nat.le_of_dvd (by decide : 0 < 36) h
  have hn : ¬ 9 ∣ a := Nat.squarefree_iff_prime_squarefree.mp hs 3 Nat.prime_three
  interval_cases a <;> norm_num at *

private theorem power_gap_of_eq {p q : ℕ} [Fact p.Prime] [NeZero q] (n : ℕ)
    (eqn : q=p*p^n) (m : ℕ) (he : Even m) (A B : DirichletCharacter ℂ q)
    (hA : A.IsPrimitive) (hB : B.IsPrimitive) :
    let j := q/(m.gcd q)
    p ≤ j → ((p=2 ∧ 8 ≤ j) ∨ (p=3 ∧ 27 ≤ j) ∨ 5 ≤ p) →
    3*‖J A B (m:ZMod q)‖ ≤ sqrt 5*‖J (1 : DirichletCharacter ℂ q) 1 (m:ZMod q)‖ := by
  subst q
  exact local_power_gap_sharp n m he hA hB

/-- A single prime-power factor already gives a uniform gap unless the
reduced additive denominator divides 36. -/
theorem reduced_gap_sharp {r s : ℕ} [NeZero r] [NeZero s] {α : DirichletCharacter ℂ r}
    {β : DirichletCharacter ℂ s} (hα : α.IsPrimitive) (hβ : β.IsPrimitive)
    (m : ℕ) (hm : 0 < m) (he : Even m) :
    let L := Nat.lcm r s
    ¬ L/(m.gcd L) ∣ 36 →
    3*‖series α β m‖ ≤ sqrt 5*‖series (1 : DirichletCharacter ℂ 1) (1 : DirichletCharacter ℂ 1) m‖ := by
  classical
  intro L outside
  let j := L/(m.gcd L)
  let hr : r ∣ L := Nat.dvd_lcm_left ..
  let hs : s ∣ L := Nat.dvd_lcm_right ..
  let d := (inversePair α β).conductor
  by_cases good : supported r s L d j
  swap
  · have zero := not_ne_iff.mp (mt (full_support hα hβ m hm he).mp good)
    rw [zero,norm_zero,mul_zero]
    positivity
  have lp : 0 < L := Nat.lcm_pos (NeZero.pos r) (NeZero.pos s)
  let _ : NeZero L := ⟨lp.ne'⟩
  have jd : j ∣ L := Nat.div_dvd_of_dvd (Nat.gcd_dvd_right m L)
  have jp : 0 < j := Nat.pos_of_dvd_of_pos jd lp
  obtain ⟨p,hp,pj,bad⟩ := offending_prime jp outside
  let _ : Fact p.Prime := ⟨hp⟩
  have pl : p ∣ L := pj.trans jd
  let i : L.primeFactors := ⟨p,Nat.mem_primeFactors.mpr ⟨hp,pl,lp.ne'⟩⟩
  let (k : L.primeFactors) : NeZero ((k:ℕ)^L.factorization k) := ⟨(Nat.ordProj_pos L k).ne'⟩
  let e := ZMod.equivPi L lp.ne'
  let Q := p^L.factorization p
  let _ : NeZero Q := ⟨(Nat.ordProj_pos L p).ne'⟩
  let A := component e (changeLevel hr α) i
  let B := component e (changeLevel hs β) i
  let t := Q/(m.gcd Q)
  have qpos : 0 < Q := Nat.ordProj_pos ..
  have tpos : 0 < t := Nat.pos_of_dvd_of_pos (Nat.div_dvd_of_dvd (Nat.gcd_dvd_right m Q)) qpos
  have eqt : t=p^j.factorization p := reduced_prime_part hp lp.ne' m
  have lift (k : ℕ) (H : p^k ∣ j) : p^k ∣ t := eqt ▸ (hp.pow_dvd_iff_dvd_ordProj jp.ne').mp H
  have pt : p ≤ t := Nat.le_of_dvd tpos (by simpa using lift 1 (by simpa using pj))
  have out : (p=2 ∧ 8 ≤ t) ∨ (p=3 ∧ 27 ≤ t) ∨ 5 ≤ p := by
    rcases bad with ⟨ep,h8⟩ | ⟨ep,h27⟩ | big
    · left; refine ⟨ep,?_⟩
      have h : p^3 ∣ t := lift 3 (by simpa [ep] using h8)
      simpa [ep] using Nat.le_of_dvd tpos h
    · right; left; refine ⟨ep,?_⟩
      have h : p^3 ∣ t := lift 3 (by simpa [ep] using h27)
      simpa [ep] using Nat.le_of_dvd tpos h
    · exact .inr (.inr big)
  have ha : A.conductor=Q.gcd r := by
    dsimp only [A]
    rw [component_conductor e (fun k : L.primeFactors => Nat.ordProj_dvd L k)
      L.pairwise_coprime_pow_primeFactors_factorization,conductor_changeLevel,hα]
  have hb : B.conductor=Q.gcd s := by
    dsimp only [B]
    rw [component_conductor e (fun k : L.primeFactors => Nat.ordProj_dvd L k)
      L.pairwise_coprime_pow_primeFactors_factorization,conductor_changeLevel,hβ]
  have vpos := (hp.dvd_iff_one_le_factorization lp.ne').mp pl
  have loc : 3*‖J A B (m:ZMod Q)‖ ≤ sqrt 5*‖J (1 : DirichletCharacter ℂ Q) 1 (m:ZMod Q)‖ := by
    by_cases v : L.factorization p=1
    · have Qp : Q=p := by simp [Q,v]
      let _ : Fact Q.Prime := ⟨Qp ▸ hp⟩
      have tl : t ≤ p := Qp ▸ Nat.div_le_self Q (m.gcd Q)
      have mp : ¬Q ∣ m := by
        intro H
        have te : t=1 := by dsimp only [t]; rw [Nat.gcd_eq_right H,Nat.div_self qpos]
        have := hp.one_lt
        omega
      have large : 5 ≤ Q := by
        rw [Qp]
        rcases out with ⟨hp2,ht⟩ | ⟨hp3,ht⟩ | b <;> omega
      have neq (χ : DirichletCharacter ℂ Q) (H : χ.conductor=Q) : χ ≠ 1 := by
        intro E
        rw [E,conductor_one] at H
        omega
      apply prime_local_gap m A B mp _ large
      rcases hp.dvd_mul.mp (pl.trans (Nat.lcm_dvd_mul r s)) with pr | ps
      · exact .inl (neq A (ha.trans (Nat.gcd_eq_left (Qp ▸ pr))))
      · exact .inr (neq B (hb.trans (Nat.gcd_eq_left (Qp ▸ ps))))
    · obtain ⟨n,hn⟩ : ∃ n : ℕ, L.factorization p=n+2 := ⟨L.factorization p-2,by omega⟩
      have Qd : p^(n+2) ∣ L := by simpa [hn] using Nat.ordProj_dvd L p
      have Qr : Q ∣ r := by simpa [Q,hn] using primitive_source_dvd hp hr good.1 Qd
      have Qs : Q ∣ s := by simpa [Q,hn] using primitive_source_dvd hp hs good.2.1 Qd
      have eqQ : Q = p*p^(n+1) := by dsimp only [Q]; rw [hn,pow_succ' p (n+1)]
      exact power_gap_of_eq (n+1) eqQ m he A B (ha.trans (Nat.gcd_eq_left Qr))
        (hb.trans (Nat.gcd_eq_left Qs)) pt out
  have full := single_factor e hα hβ hr hs m hm he i
  let O := ‖series (1 : DirichletCharacter ℂ 1) (1 : DirichletCharacter ℂ 1) m‖
  let V := ‖J A B (m:ZMod Q)‖
  let W := ‖J (1 : DirichletCharacter ℂ Q) 1 (m:ZMod Q)‖
  have wp : 0 < W := norm_pos_iff.mpr (principal_ne_zero Q m he)
  change ‖series α β m‖*W ≤ O*V at full
  change 3*V ≤ sqrt 5*W at loc
  apply le_of_mul_le_mul_right (a := W) <;> try assumption
  change 3*‖series α β m‖*W ≤ sqrt 5*O*W
  linarith only [mul_le_mul_of_nonneg_left full (by norm_num : (0:ℝ) ≤ 3),
    mul_le_mul_of_nonneg_left loc (show 0 ≤ O from norm_nonneg _)]

/-- The exceptions in Pintz I (7.8). The exact local estimates give
sqrt(5)/3 in place of the stated sqrt(3)/2. -/
theorem pintz_gap_sharp {r s : ℕ} [NeZero r] [NeZero s] {α : DirichletCharacter ℂ r}
    {β : DirichletCharacter ℂ s} (hα : α.IsPrimitive) (hβ : β.IsPrimitive)
    (m : ℕ) (hm : 0 < m) (he : Even m)
    (out : ¬(r/(m.gcd r) ∣ 36 ∧ s/(m.gcd s) ∣ 36 ∧ r/(r.gcd s) ∣ 3 ∧
      s/(r.gcd s) ∣ 3 ∧ (inversePair α β).conductor ∣ 36)) :
    3*‖series α β m‖ ≤ sqrt 5*‖series (1 : DirichletCharacter ℂ 1) (1 : DirichletCharacter ℂ 1) m‖ := by
  let L := Nat.lcm r s
  let j := L/(m.gcd L)
  let d := (inversePair α β).conductor
  by_cases h36 : j ∣ 36
  swap
  · exact reduced_gap_sharp hα hβ m hm he h36
  by_cases good : supported r s L d j
  swap
  · have zero := not_ne_iff.mp (mt (full_support hα hβ m hm he).mp good)
    rw [zero,norm_zero,mul_zero]
    positivity
  have hr : r ∣ L := Nat.dvd_lcm_left ..
  have hs : s ∣ L := Nat.dvd_lcm_right ..
  obtain ⟨ra,sa⟩ := TwistedGoldbachConductorSuppression.complementary_dvd hα hβ (m := m) good
  have rj := ra.trans good.2.2.1
  have sj := sa.trans good.2.2.1
  have rsmall := small_complement (rj.trans h36) good.1.1 (complementary_odd hr he good.1 rj)
  have ssmall := small_complement (sj.trans h36) good.2.1.1 (complementary_odd hs he good.2.1 sj)
  have eqr : L/r=s/(r.gcd s) := by
    change (Nat.lcm r s)/r=s/(r.gcd s)
    rw [Nat.lcm_eq_mul_div,Nat.mul_div_assoc _ (Nat.gcd_dvd_right r s),Nat.mul_div_cancel_left _ (NeZero.pos r)]
  have eqs : L/s=r/(r.gcd s) := by
    change (Nat.lcm r s)/s=r/(r.gcd s)
    rw [Nat.lcm_comm,Nat.lcm_eq_mul_div,Nat.mul_div_assoc _ (Nat.gcd_dvd_right s r),
      Nat.mul_div_cancel_left _ (NeZero.pos s),Nat.gcd_comm]
  have splitj : j=Nat.lcm (r/(m.gcd r)) (s/(m.gcd s)) := TwistedGoldbachConductorSuppression.reduced_lcm m
  exact False.elim (out ⟨(splitj ▸ Nat.dvd_lcm_left ..).trans h36,
    (splitj ▸ Nat.dvd_lcm_right ..).trans h36,eqs ▸ ssmall,eqr ▸ rsmall,good.2.2.1.trans h36⟩)

private theorem three_quarters {A B : ℝ} (hB : 0 ≤ B) (h : 3*A ≤ sqrt 5*B) :
    4*A ≤ 3*B := by
  have h5 : sqrt 5 ≤ 9/4 := (sqrt_le_iff).mpr ⟨by norm_num,by norm_num⟩
  linarith only [h, mul_le_mul_of_nonneg_right h5 hB]

theorem local_power_gap {p : ℕ} [hp : Fact p.Prime] (n m : ℕ) (he : Even m)
    {A B : DirichletCharacter ℂ (p*p^n)} (hA : A.IsPrimitive) (hB : B.IsPrimitive) :
    let q := p*p^n
    let j := q/(m.gcd q)
    p ≤ j → ((p=2 ∧ 8 ≤ j) ∨ (p=3 ∧ 27 ≤ j) ∨ 5 ≤ p) →
    4*‖J A B (m:ZMod q)‖ ≤ 3*‖J (1 : DirichletCharacter ℂ q) 1 (m:ZMod q)‖ := by
  intro q j pj out
  exact three_quarters (norm_nonneg _) (local_power_gap_sharp n m he hA hB pj out)

theorem reduced_gap {r s : ℕ} [NeZero r] [NeZero s] {α : DirichletCharacter ℂ r}
    {β : DirichletCharacter ℂ s} (hα : α.IsPrimitive) (hβ : β.IsPrimitive)
    (m : ℕ) (hm : 0 < m) (he : Even m) :
    let L := Nat.lcm r s
    ¬ L/(m.gcd L) ∣ 36 →
    4*‖series α β m‖ ≤ 3*‖series (1 : DirichletCharacter ℂ 1) (1 : DirichletCharacter ℂ 1) m‖ := by
  intro L out
  exact three_quarters (norm_nonneg _) (reduced_gap_sharp hα hβ m hm he out)

theorem pintz_gap {r s : ℕ} [NeZero r] [NeZero s] {α : DirichletCharacter ℂ r}
    {β : DirichletCharacter ℂ s} (hα : α.IsPrimitive) (hβ : β.IsPrimitive)
    (m : ℕ) (hm : 0 < m) (he : Even m)
    (out : ¬(r/(m.gcd r) ∣ 36 ∧ s/(m.gcd s) ∣ 36 ∧ r/(r.gcd s) ∣ 3 ∧
      s/(r.gcd s) ∣ 3 ∧ (inversePair α β).conductor ∣ 36)) :
    4*‖series α β m‖ ≤ 3*‖series (1 : DirichletCharacter ℂ 1) (1 : DirichletCharacter ℂ 1) m‖ := by
  exact three_quarters (norm_nonneg _) (pintz_gap_sharp hα hβ m hm he out)

/-- Away from multiples of the conductor in 36m, any pair of primitive
characters at that level has a strict gap, including the diagonal pair
that supplies the exceptional-real-zero term. -/
theorem same_level_gap {r : ℕ} [NeZero r] {α β : DirichletCharacter ℂ r}
    (hα : α.IsPrimitive) (hβ : β.IsPrimitive) (m : ℕ) (hm : 0 < m) (he : Even m)
    (out : ¬r ∣ 36*m) :
    4*‖series α β m‖ ≤ 3*‖series (1 : DirichletCharacter ℂ 1) (1 : DirichletCharacter ℂ 1) m‖ := by
  apply pintz_gap hα hβ m hm he
  intro H
  apply out
  have D := Nat.mul_dvd_mul H.1 (Nat.gcd_dvd_left m r)
  rwa [Nat.div_mul_cancel (Nat.gcd_dvd_right m r)] at D

end Conjectures.Goldbach.SharpSingularSeriesRatiosProof.TwistedGoldbachExceptionalGap

/-! Optimal contraction of the twisted Goldbach singular series off the
five exceptional divisibilities of Pintz I, (7.8). A primitive quartic
character modulo 5 realizes the bound for every positive even target
prime to 5. -/

namespace Conjectures.Goldbach.SharpSingularSeriesRatiosProof.SharpTwistedGoldbachGap

open DirichletCharacter TwistedGoldbachLocalProduct TwistedGoldbachConductorRatio
open TwistedGoldbachExceptionalGap SquarefreeTwistedGoldbachDensity
open scoped Classical

local instance : Fact (Nat.Prime 5) := ⟨by decide⟩

private def quarticValue (x : ZMod 5) : ℂ :=
  match x.val with
  | 0 => 0
  | 1 => 1
  | 2 => Complex.I
  | 3 => -Complex.I
  | _ => -1

/-- The generator taking the value i at 2 modulo 5. -/
noncomputable def quartic : DirichletCharacter ℂ 5 where
  toFun := quarticValue
  map_one' := rfl
  map_mul' a b := by
    fin_cases a <;> fin_cases b
    all_goals first | change (0:ℂ) = _ | change (1:ℂ) = _ | change Complex.I = _
                    | change -Complex.I = _ | change (-1:ℂ) = _
    all_goals norm_num [quarticValue, ZMod.val, Complex.ext_iff, Complex.mul_re, Complex.mul_im]
  map_nonunit' a h := by
    have eq0 : a=0 := by simpa only [isUnit_iff_ne_zero,not_not] using h
    subst a
    rfl

theorem quartic_props : quartic ≠ 1 ∧ quartic*quartic ≠ 1 ∧ quartic.IsPrimitive := by
  have V : quartic 2 = Complex.I := rfl
  have U : IsUnit (2:ZMod 5) := isUnit_iff_ne_zero.mpr (by decide : (2:ZMod 5) ≠ 0)
  have P : (1 : DirichletCharacter ℂ 5) 2 = 1 := MulChar.one_apply U
  have nontrivial : quartic ≠ 1 := by
    intro h
    have H := congrArg (fun χ : DirichletCharacter ℂ 5 => (χ 2).re) h
    change (quartic 2).re=((1 : DirichletCharacter ℂ 5) 2).re at H
    norm_num [V,P] at H
  have square : quartic*quartic ≠ 1 := by
    intro h
    have H := congrArg (fun χ : DirichletCharacter ℂ 5 => (χ 2).re) h
    change (quartic 2*quartic 2).re=((1 : DirichletCharacter ℂ 5) 2).re at H
    norm_num [V,P] at H
  refine ⟨nontrivial,square,?_⟩
  rcases (Nat.dvd_prime (by decide : Nat.Prime 5)).mp quartic.conductor_dvd_level with H | H
  · exact False.elim (nontrivial (eq_one_iff_conductor_eq_one.mpr H))
  · exact H

theorem quartic_fourth : quartic^4=1 := by
  have H := quartic.pow_card_eq_one
  rw [ZMod.card_units_eq_totient,show (5:ℕ).totient=4 by decide] at H
  exact H

theorem quartic_extremizer (m : ℕ) (hm : 0 < m) (he : Even m) (h5 : ¬5 ∣ m) :
    3*‖series quartic quartic m‖ =
      Real.sqrt 5*‖series (1 : DirichletCharacter ℂ 1) (1 : DirichletCharacter ℂ 1) m‖ := by
  obtain ⟨N,NN,P⟩ := quartic_props
  have hm5 : (m:ZMod 5) ≠ 0 := mt (ZMod.natCast_eq_zero_iff m 5).mp h5
  have F := exact_ratio P P (dvd_refl 5) (dvd_refl 5) m hm he
  rw [changeLevel_self,← principal_card] at F
  change series quartic quartic m = series (1 : DirichletCharacter ℂ 1) (1 : DirichletCharacter ℂ 1) m *
    (J quartic quartic (m:ZMod 5) / J 1 1 (m:ZMod 5)) at F
  have T := local_norm quartic quartic (m:ZMod 5)
  have O := local_norm (1 : DirichletCharacter ℂ 5) 1 (m:ZMod 5)
  simp [hm5,N,NN] at T
  norm_num [hm5] at O
  change ‖J quartic quartic (m:ZMod 5)‖=Real.sqrt 5 at T
  change ‖J (1 : DirichletCharacter ℂ 5) 1 (m:ZMod 5)‖=3 at O
  rw [F,norm_mul,norm_div,T,O]
  ring

def exceptional {r s : ℕ} (α : DirichletCharacter ℂ r) (β : DirichletCharacter ℂ s)
    (m : ℕ) : Prop :=
  r/(m.gcd r) ∣ 36 ∧ s/(m.gcd s) ∣ 36 ∧ r/(r.gcd s) ∣ 3 ∧ s/(r.gcd s) ∣ 3 ∧
    ((changeLevel (Nat.dvd_lcm_left r s) α)*(changeLevel (Nat.dvd_lcm_right r s) β)).conductor ∣ 36

theorem sharp_bound {r s : ℕ} [NeZero r] [NeZero s] {α : DirichletCharacter ℂ r}
    {β : DirichletCharacter ℂ s} (hα : α.IsPrimitive) (hβ : β.IsPrimitive)
    (m : ℕ) (hm : 0 < m) (he : Even m) (out : ¬exceptional α β m) :
    3*‖series α β m‖ ≤ Real.sqrt 5*‖series (1 : DirichletCharacter ℂ 1) (1 : DirichletCharacter ℂ 1) m‖ := by
  apply pintz_gap_sharp hα hβ m hm he
  simpa only [exceptional,TwistedGoldbachConductorValue.inversePair,conductor_inv] using out

theorem quartic_outside (m : ℕ) (h5 : ¬5 ∣ m) : ¬exceptional quartic quartic m := by
  intro h
  have g : m.gcd 5 = 1 := (Nat.Prime.coprime_iff_not_dvd (by decide : Nat.Prime 5)).mpr h5 |>.symm
  have d := h.1
  simp [g] at d

theorem optimum (K : ℝ) :
    (∀ (r s : ℕ) [NeZero r] [NeZero s] (α : DirichletCharacter ℂ r) (β : DirichletCharacter ℂ s),
      α.IsPrimitive → β.IsPrimitive → ∀ m : ℕ, 0 < m → Even m → ¬exceptional α β m →
        ‖series α β m‖ ≤ K*‖series (1 : DirichletCharacter ℂ 1) (1 : DirichletCharacter ℂ 1) m‖) ↔
    Real.sqrt 5/3 ≤ K := by
  constructor
  · intro h
    have H := h 5 5 quartic quartic quartic_props.2.2 quartic_props.2.2 2 (by decide)
      (by decide) (quartic_outside 2 (by decide))
    have E := quartic_extremizer 2 (by decide) (by decide) (by decide)
    let O := ‖series (1 : DirichletCharacter ℂ 1) (1 : DirichletCharacter ℂ 1) 2‖
    have Opos : 0 < O := lt_of_lt_of_le (by norm_num : (0:ℝ)<1)
      ((TwistedGoldbachMixedPrincipal.ordinary_at_least_one 2 (by decide) (by decide)).trans (Complex.re_le_norm _))
    apply le_of_mul_le_mul_right (a := O) _ Opos
    dsimp only [O]
    linarith only [H,E]
  · intro lower r s _ _ α β hα hβ m hm he out
    have H := sharp_bound hα hβ m hm he out
    have Kbound := mul_le_mul_of_nonneg_right lower
      (norm_nonneg (series (1 : DirichletCharacter ℂ 1) (1 : DirichletCharacter ℂ 1) m))
    linarith only [H,Kbound]

end Conjectures.Goldbach.SharpSingularSeriesRatiosProof.SharpTwistedGoldbachGap

open Conjectures.Goldbach.SharpSingularSeriesRatiosProof.SharpTwistedGoldbachGap in
theorem Conjectures.Goldbach.SharpSingularSeriesRatiosProof.SharpTwistedGoldbachGap :
by
  classical
  let S := fun {r s : ℕ} (α : DirichletCharacter ℂ r) (β : DirichletCharacter ℂ s) (m : ℕ) =>
    ∑' q : ℕ, if hq : q ≠ 0 then
      let _ : NeZero q := ⟨hq⟩
      if h : r ∣ q ∧ s ∣ q then
        let A := DirichletCharacter.changeLevel h.1 α
        let B := DirichletCharacter.changeLevel h.2 β
        gaussSum A ZMod.stdAddChar * gaussSum B ZMod.stdAddChar *
          gaussSum (A*B)⁻¹ (ZMod.stdAddChar.mulShift (-(m:ZMod q))) / (q.totient:ℂ)^2
      else 0
    else 0
  let O := S (1 : DirichletCharacter ℂ 1) (1 : DirichletCharacter ℂ 1)
  let X := fun {r s : ℕ} (α : DirichletCharacter ℂ r) (β : DirichletCharacter ℂ s) (m : ℕ) =>
    r/(m.gcd r) ∣ 36 ∧ s/(m.gcd s) ∣ 36 ∧ r/(r.gcd s) ∣ 3 ∧ s/(r.gcd s) ∣ 3 ∧
      ((DirichletCharacter.changeLevel (Nat.dvd_lcm_left r s) α)*
       (DirichletCharacter.changeLevel (Nat.dvd_lcm_right r s) β)).conductor ∣ 36
  exact
    (∀ K : ℝ, (∀ (r s : ℕ) [NeZero r] [NeZero s] (α : DirichletCharacter ℂ r) (β : DirichletCharacter ℂ s),
      α.IsPrimitive → β.IsPrimitive → ∀ m : ℕ, 0 < m → Even m → ¬X α β m →
      ‖S α β m‖ ≤ K*‖O m‖) ↔ Real.sqrt 5/3 ≤ K) ∧
    (∃ χ : DirichletCharacter ℂ 5, χ.IsPrimitive ∧ χ^4=1 ∧ χ*χ ≠ 1 ∧
      ∀ m : ℕ, 0 < m → Even m → ¬5 ∣ m → ¬X χ χ m ∧ 3*‖S χ χ m‖=Real.sqrt 5*‖O m‖) := by
  refine ⟨optimum,quartic,quartic_props.2.2,quartic_fourth,quartic_props.2.1,?_⟩
  intro m hm he h5
  exact ⟨quartic_outside m h5,quartic_extremizer m hm he h5⟩

/-! The inverse-character diagonal of the Goldbach explicit formula.
Away from the multiples of the conductor in 6m, one local Ramanujan
sum either vanishes or contracts the full series by at least three. -/

namespace Conjectures.Goldbach.SharpSingularSeriesRatiosProof.InverseGoldbachSingularGap

open Finset DirichletCharacter TwistedGoldbachLocalProduct TwistedGoldbachConductorRatio
open TwistedGoldbachConductorComponents PrimePowerTwistedGoldbachDensity
open scoped Classical

theorem large_coordinate {r k : ℕ} [NeZero r] (hk : 0 < k) (out : ¬r ∣ k) :
    ∃ p ∈ r.primeFactors, ¬p^r.factorization p ∣ k := by
  by_contra! h
  apply out
  have nz := hk.ne'
  apply (Nat.factorization_le_iff_dvd (NeZero.ne r) nz).mp
  intro p
  by_cases hp : p.Prime
  · by_cases d : p ∣ r
    · exact (hp.pow_dvd_iff_le_factorization nz).mp (h p (Nat.mem_primeFactors.mpr ⟨hp,d,NeZero.ne r⟩))
    · simp [Nat.factorization_eq_zero_of_not_dvd d]
  · simp [Nat.factorization_eq_zero_of_not_prime _ hp]

private theorem inverse_local {p : ℕ} [hp : Fact p.Prime] (n m : ℕ)
    {A B : DirichletCharacter ℂ (p*p^n)} (hA : A.IsPrimitive) (hB : B.IsPrimitive)
    (pair : A*B=1) (out : ¬p*p^n ∣ 6*m) :
    3*‖J A B (m:ZMod (p*p^n))‖ ≤ ‖J (1 : DirichletCharacter ℂ (p*p^n)) 1 (m:ZMod (p*p^n))‖ := by
  have T := principal_product_power n hA hB pair m
  rw [reflected] at T
  change ‖J A B (m:ZMod (p*p^n))‖=_ at T
  rw [T,ordinary_prime_power n m]
  by_cases d : p^n ∣ m
  · have big : 5 ≤ p := by
      by_contra! small
      have p6 : p ∣ 6 := by have := hp.out; interval_cases p <;> norm_num at *
      exact out (Nat.mul_dvd_mul p6 d)
    have nd : ¬p ∣ m/p^n := by
      intro e
      apply out
      have h := Nat.mul_dvd_mul e (dvd_refl (p^n))
      rw [Nat.div_mul_cancel d] at h
      exact h.trans (dvd_mul_left m 6)
    rw [ite_eq_left d,ite_eq_right nd,mul_one]
    have pr : (5:ℝ) ≤ p := by exact_mod_cast big
    rw [mul_comm (3:ℝ)]
    apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
    split_ifs <;> linarith
  · rw [ite_eq_right d,mul_zero]
    have pr : (2:ℝ) ≤ p := by exact_mod_cast hp.out.two_le
    apply mul_nonneg (Nat.cast_nonneg _)
    split_ifs <;> linarith

private theorem inverse_local_cast {p q : ℕ} [Fact p.Prime] [NeZero q] (n m : ℕ)
    (eqn : q=p*p^n) {A B : DirichletCharacter ℂ q} (hA : A.IsPrimitive) (hB : B.IsPrimitive)
    (pair : A*B=1) (out : ¬q ∣ 6*m) :
    3*‖J A B (m:ZMod q)‖ ≤ ‖J (1 : DirichletCharacter ℂ q) 1 (m:ZMod q)‖ := by
  subst q
  exact inverse_local n m hA hB pair out

theorem inverse_gap {r : ℕ} [NeZero r] {A B : DirichletCharacter ℂ r}
    (hA : A.IsPrimitive) (hB : B.IsPrimitive) (pair : A*B=1)
    (m : ℕ) (hm : 0 < m) (he : Even m) (out : ¬r ∣ 6*m) :
    3*‖series A B m‖ ≤ ‖series (1 : DirichletCharacter ℂ 1) (1 : DirichletCharacter ℂ 1) m‖ := by
  obtain ⟨p,member,bad⟩ := large_coordinate (by positivity : 0 < 6*m) out
  obtain ⟨hp,pr,_⟩ := Nat.mem_primeFactors.mp member
  let _ : Fact p.Prime := ⟨hp⟩
  let i : r.primeFactors := ⟨p,member⟩
  let Q := p^r.factorization p
  let e := ZMod.equivPi r (NeZero.ne r)
  let (k : r.primeFactors) : NeZero ((k:ℕ)^r.factorization k) := ⟨(Nat.ordProj_pos r k).ne'⟩
  let _ : NeZero Q := ⟨(Nat.ordProj_pos r p).ne'⟩
  have prim (χ : DirichletCharacter ℂ r) (hχ : χ.IsPrimitive) : (component e χ i).IsPrimitive := by
    rw [isPrimitive_def,component_conductor e (fun k : r.primeFactors => Nat.ordProj_dvd r k)
      r.pairwise_coprime_pow_primeFactors_factorization,hχ,Nat.gcd_eq_left (Nat.ordProj_dvd ..)]
  have pp : component e A i * component e B i=1 := by
    rw [← component_mul,pair,component_one]
  have va := (hp.dvd_iff_one_le_factorization (NeZero.ne r)).mp pr
  obtain ⟨n,hn⟩ : ∃ n, r.factorization p = n+1 := ⟨r.factorization p-1,by omega⟩
  have eqn : Q=p*p^n := by rw [show Q=p^r.factorization p from rfl,hn,pow_succ']
  have loc := inverse_local_cast n m eqn (prim A hA) (prim B hB) pp bad
  have full := single_factor e hA hB (dvd_refl r) (dvd_refl r) m hm he i
  simp only [changeLevel_self] at full
  let O := ‖series (1 : DirichletCharacter ℂ 1) (1 : DirichletCharacter ℂ 1) m‖
  let W := ‖J (1 : DirichletCharacter ℂ Q) 1 (m:ZMod Q)‖
  let V := ‖J (component e A i) (component e B i) (m:ZMod Q)‖
  change 3*V ≤ W at loc
  change ‖series A B m‖*W ≤ O*V at full
  have wp : 0 < W := norm_pos_iff.mpr (principal_ne_zero Q m he)
  apply le_of_mul_le_mul_right (a := W) _ wp
  change 3*‖series A B m‖*W ≤ O*W
  linarith only [mul_le_mul_of_nonneg_left loc (show 0 ≤ O from norm_nonneg _),full]

theorem quadratic_gap {r : ℕ} [NeZero r] {χ : DirichletCharacter ℂ r}
    (hχ : χ.IsPrimitive) (realχ : χ.IsQuadratic) (m : ℕ) (hm : 0 < m)
    (he : Even m) (out : ¬r ∣ 6*m) :
    3*‖series χ χ m‖ ≤ ‖series (1 : DirichletCharacter ℂ 1) (1 : DirichletCharacter ℂ 1) m‖ := by
  apply inverse_gap hχ hχ _ m hm he out
  simpa only [realχ.inv] using mul_inv_cancel χ

end Conjectures.Goldbach.SharpSingularSeriesRatiosProof.InverseGoldbachSingularGap

open Conjectures.Goldbach.SharpSingularSeriesRatiosProof.InverseGoldbachSingularGap in
theorem Conjectures.Goldbach.SharpSingularSeriesRatiosProof.InverseGoldbachSingularGap :
by
  classical
  let S := fun {r s : ℕ} (α : DirichletCharacter ℂ r) (β : DirichletCharacter ℂ s) (m : ℕ) =>
    ∑' q : ℕ, if hq : q ≠ 0 then
      let _ : NeZero q := ⟨hq⟩
      if h : r ∣ q ∧ s ∣ q then
        let A := DirichletCharacter.changeLevel h.1 α
        let B := DirichletCharacter.changeLevel h.2 β
        gaussSum A ZMod.stdAddChar * gaussSum B ZMod.stdAddChar *
          gaussSum (A*B)⁻¹ (ZMod.stdAddChar.mulShift (-(m:ZMod q))) / (q.totient:ℂ)^2
      else 0
    else 0
  let O := S (1 : DirichletCharacter ℂ 1) (1 : DirichletCharacter ℂ 1)
  exact ∀ (r : ℕ) [NeZero r] (χ ψ : DirichletCharacter ℂ r),
    χ.IsPrimitive → ψ.IsPrimitive → χ*ψ=1 → ∀ m : ℕ, 0 < m → Even m →
    ¬r ∣ 6*m → 3*‖S χ ψ m‖ ≤ ‖O m‖ := fun _ _ _ _ hχ hψ pair m hm he out => inverse_gap hχ hψ pair m hm he out

/-! The beta factor in Pintz's explicit formula for Goldbach numbers,
arXiv:1804.09084, equations (2.19)–(2.21). Interpolation between the
constant density and the arcsine density makes the error explicit and
uniform in both imaginary parts. -/

namespace Conjectures.Goldbach.SharpSingularSeriesRatiosProof.ExceptionalZeroBetaBound

open Complex MeasureTheory Filter
open scoped Topology

noncomputable section

private def kernel (z w : ℂ) (x : ℝ) : ℂ := (x : ℂ)^(z-1)*(1-(x : ℂ))^(w-1)
private def half : ℂ := 1/2
private def arcsine (x : ℝ) := x^(-(1/2 : ℝ))*(1-x)^(-(1/2 : ℝ))

private theorem kernel_half {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ 1) :
    kernel half half x = (arcsine x : ℂ) := by
  have h : half-1 = ((-(1/2 : ℝ) : ℝ) : ℂ) := by norm_num [half]
  dsimp only [kernel,arcsine]
  rw [Complex.ofReal_mul,Complex.ofReal_cpow h0,Complex.ofReal_cpow (sub_nonneg.mpr h1),
    Complex.ofReal_sub,Complex.ofReal_one,h]

private theorem norm_half {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ 1) :
    ‖kernel half half x‖ = arcsine x := by
  rw [kernel_half h0 h1,Complex.norm_real, Real.norm_eq_abs,abs_of_nonneg]
  exact mul_nonneg (Real.rpow_nonneg h0 _) (Real.rpow_nonneg (sub_nonneg.mpr h1) _)

private theorem half_integral : (∫ x in (0 : ℝ)..1, ‖kernel half half x‖) = Real.pi := by
  have hh : 0 < half.re := by norm_num [half,Complex.div_re]
  have hvalue : Complex.betaIntegral half half = (Real.pi : ℂ) := by
    rw [Complex.betaIntegral_eq_Gamma_mul_div _ _ hh hh,show half+half=1 by norm_num [half],
      Complex.Gamma_one,div_one]
    have hg : Complex.Gamma half = ((Real.sqrt Real.pi : ℝ) : ℂ) := by
      have he : half = ((1/2:ℝ) : ℂ) := by norm_num [half]
      rw [he,Complex.Gamma_ofReal,Real.Gamma_one_half_eq]
    rw [hg,← Complex.ofReal_mul,Real.mul_self_sqrt Real.pi_pos.le]
  apply Complex.ofReal_injective
  calc
    _ = ∫ x in (0:ℝ)..1, (‖kernel half half x‖ : ℂ) := intervalIntegral.integral_ofReal.symm
    _ = Complex.betaIntegral half half := by
      apply intervalIntegral.integral_congr
      intro x hx
      rw [Set.uIcc_of_le (by norm_num : (0:ℝ)≤1)] at hx
      change (‖kernel half half x‖ : ℂ) = kernel half half x
      rw [norm_half hx.1 hx.2,kernel_half hx.1 hx.2]
    _ = _ := hvalue

private theorem pointwise {δ x : ℝ} {z w : ℂ} (hδ : 0 ≤ δ) (hδ' : δ ≤ 1/2)
    (hz : 1-δ ≤ z.re) (hw : 1-δ ≤ w.re) (h0 : 0 < x) (h1 : x < 1) :
    ‖kernel z w x‖ ≤ 1-2*δ+2*δ*‖kernel half half x‖ := by
  have h0' : 0 < 1-x := sub_pos.mpr h1
  have h1' : 1-x ≤ 1 := by linarith
  have hk : 0 ≤ arcsine x := mul_nonneg (Real.rpow_nonneg h0.le _)
    (Real.rpow_nonneg h0'.le _)
  have hg := Real.geom_mean_le_arith_mean2_weighted (show 0 ≤ 1-2*δ by linarith)
    (show 0 ≤ 2*δ by linarith) (by norm_num : (0:ℝ) ≤ 1) hk (by ring)
  rw [Real.one_rpow,one_mul,mul_one] at hg
  rw [norm_half h0.le h1.le]
  refine le_trans ?_ hg
  rw [kernel,norm_mul,← Complex.ofReal_one,← Complex.ofReal_sub,
    Complex.norm_cpow_eq_rpow_re_of_pos h0,Complex.norm_cpow_eq_rpow_re_of_pos h0']
  simp only [Complex.sub_re]
  have hs : x^(z.re-1)*(1-x)^(w.re-1) ≤ x^(-δ)*(1-x)^(-δ) :=
    mul_le_mul (Real.rpow_le_rpow_of_exponent_ge h0 h1.le (by linarith only [hz]))
      (Real.rpow_le_rpow_of_exponent_ge h0' h1' (by linarith only [hw]))
      (Real.rpow_nonneg h0'.le _) (Real.rpow_nonneg h0.le _)
  refine hs.trans_eq ?_
  dsimp only [arcsine]
  rw [Real.mul_rpow (Real.rpow_nonneg h0.le _) (Real.rpow_nonneg h0'.le _),
    ← Real.rpow_mul h0.le, ← Real.rpow_mul h0'.le]
  ring_nf

/-- Explicit uniform replacement for the asymptotic beta-factor estimate. -/
theorem gamma_ratio {δ : ℝ} {z w : ℂ} (hδ : 0 ≤ δ) (hδ' : δ ≤ 1/2)
    (hz : 1-δ ≤ z.re) (hw : 1-δ ≤ w.re) :
    ‖Complex.Gamma z*Complex.Gamma w/Complex.Gamma (z+w)‖ ≤ 1+2*(Real.pi-1)*δ := by
  have hz' : 0 < z.re := by linarith
  have hw' : 0 < w.re := by linarith
  have hh : 0 < half.re := by norm_num [half,Complex.div_re]
  have hk : IntervalIntegrable (kernel half half) volume 0 1 := Complex.betaIntegral_convergent hh hh
  have hk' : IntervalIntegrable (kernel z w) volume 0 1 := Complex.betaIntegral_convergent hz' hw'
  rw [← Complex.betaIntegral_eq_Gamma_mul_div _ _ hz' hw']
  calc
    _ ≤ ∫ x in (0:ℝ)..1, ‖kernel z w x‖ := intervalIntegral.norm_integral_le_integral_norm zero_le_one
    _ ≤ ∫ x in (0:ℝ)..1, (1-2*δ+2*δ*‖kernel half half x‖) :=
      intervalIntegral.integral_mono_on_of_le_Ioo zero_le_one hk'.norm
        (intervalIntegrable_const.add (hk.norm.const_mul _)) (fun _ h =>
          pointwise hδ hδ' hz hw h.1 h.2)
    _ = _ := by
      rw [intervalIntegral.integral_add intervalIntegrable_const (hk.norm.const_mul _),
        intervalIntegral.integral_const,intervalIntegral.integral_const_mul,half_integral]
      simp only [sub_zero,one_smul]
      ring

/-- Apply the uniform gamma bound to the full complex secondary sum,
preserving each zero's individual horizontal distance from 1. -/
theorem secondary_floor (δ s m : ℝ) (P : Finset (ℕ×ℕ)) (z : ℕ → ℂ)
    (a : ℕ×ℕ → ℂ) (err : ℂ) (hδ : 0 ≤ δ) (hδ' : δ ≤ 1/2)
    (hs : 0 ≤ s) (hm : 0 < m)
    (hab : ∀ p ∈ P, ‖a p‖ ≤ s ∧ 1-δ ≤ (z p.1).re ∧ 1-δ ≤ (z p.2).re) :
    s*m*(1-(1+2*(Real.pi-1)*δ)*
      ∑ p ∈ P, m^((z p.1).re-1)*m^((z p.2).re-1))-‖err‖ ≤
    ((s*m : ℝ)+ (∑ p ∈ P, a p*(Complex.Gamma (z p.1)*Complex.Gamma (z p.2)/
      Complex.Gamma (z p.1+z p.2))*(m : ℂ)^(z p.1+z p.2-1))+err : ℂ).re := by
  let A := 1+2*(Real.pi-1)*δ
  have hA : 0 ≤ A := by
    dsimp [A]
    exact add_nonneg zero_le_one (mul_nonneg (mul_nonneg (by norm_num)
      (by linarith only [Real.pi_gt_three])) hδ)
  let d := fun i : ℕ => m^((z i).re-1)
  let c := fun p : ℕ×ℕ => a p*(Complex.Gamma (z p.1)*Complex.Gamma (z p.2)/
    Complex.Gamma (z p.1+z p.2))*(m : ℂ)^(z p.1+z p.2-1)
  have hz (p : ℕ×ℕ) : ‖(m:ℂ)^(z p.1+z p.2-1)‖ = m*(d p.1*d p.2) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hm,Complex.sub_re,Complex.add_re,Complex.one_re]
    dsimp [d]
    rw [← Real.rpow_add hm,show (z p.1).re+(z p.2).re-1 =
      1+(((z p.1).re-1)+((z p.2).re-1)) by ring,Real.rpow_add hm,Real.rpow_one]
  have hu : ‖∑ p ∈ P, c p‖ ≤ (s*m*A)*(∑ p ∈ P, d p.1*d p.2) := calc
    _ ≤ ∑ p ∈ P, ‖c p‖ := norm_sum_le _ _
    _ ≤ ∑ p ∈ P, (s*m*A)*(d p.1*d p.2) := by
      apply Finset.sum_le_sum
      intro p hp
      obtain ⟨ha,hz₁,hz₂⟩ := hab p hp
      dsimp only [c]
      rw [norm_mul,norm_mul,hz]
      have h := mul_le_mul ha (gamma_ratio hδ hδ' hz₁ hz₂) (norm_nonneg _) hs
      have hpos : 0 ≤ m*(d p.1*d p.2) := by dsimp [d]; positivity
      exact (mul_le_mul_of_nonneg_right h hpos).trans_eq (by dsimp [A];ring)
    _ = _ := (Finset.mul_sum _ _ _).symm
  have hr := (abs_le.mp (Complex.abs_re_le_norm (∑ p ∈ P,c p))).1
  have he := (abs_le.mp (Complex.abs_re_le_norm err)).1
  change s*m*(1-A*(∑ p ∈ P,d p.1*d p.2))-‖err‖ ≤
    (((s*m : ℝ) : ℂ)+(∑ p ∈ P,c p)+err).re
  simp only [Complex.add_re,Complex.ofReal_re]
  linarith only [hu,hr,he]

end
end Conjectures.Goldbach.SharpSingularSeriesRatiosProof.ExceptionalZeroBetaBound

/-! The exceptional conductor profiles in §2, equations (2.26)–(2.31), of
Pintz, arXiv:1804.09084. The divisibility argument is finite and independent
of how the primitive conductors and their zeros are produced. -/

namespace Conjectures.Goldbach.SharpSingularSeriesRatiosProof.ExceptionalConductorClasses

open Finset Filter
open scoped BigOperators Topology

def profile (R : Finset ℕ) (C m : ℕ) := R.filter (fun r => r ∣ C*m)
def modulus (S : Finset ℕ) : ℕ := S.lcm id
def moduli (R : Finset ℕ) := R.powerset.image modulus
noncomputable def bad (R : Finset ℕ) (C N : ℕ) (T : ℝ) :=
  (Ioc 0 N).filter (fun m => T < (modulus (profile R C m) : ℝ))

private theorem cancel_common (q C m : ℕ) (hq : 0 < q) :
    q ∣ C*m ↔ q/(q.gcd C) ∣ m := by
  let g := q.gcd C
  have hg : 0 < g := Nat.gcd_pos_of_pos_left C hq
  have hl : (q/g)*g=q := Nat.div_mul_cancel (Nat.gcd_dvd_left q C)
  have hr : (C/g)*g=C := Nat.div_mul_cancel (Nat.gcd_dvd_right q C)
  have he : ((C/g)*m)*g=C*m := by rw [Nat.mul_right_comm, hr]
  calc
    q ∣ C*m ↔ (q/g)*g ∣ ((C/g)*m)*g := by rw [hl,he]
    _ ↔ (q/g) ∣ (C/g)*m := Nat.mul_dvd_mul_iff_right hg
    _ ↔ _ := (Nat.coprime_div_gcd_div_gcd hg).dvd_mul_left

/-- Exact number of positive multiples after cancelling the common
part of a modulus with the integer attached to the target. -/
theorem multiples (q C N : ℕ) (hq : 0 < q) :
    ((Ioc 0 N).filter (fun m => q ∣ C*m)).card = N/(q/(q.gcd C)) := by
  simp_rw [cancel_common q C _ hq]
  exact Nat.Ioc_filter_dvd_card_eq_div N _

/-- Every target is divisible, after multiplication by C, by the least
common multiple of precisely the exceptional conductors it sees. -/
theorem profile_dvd (R : Finset ℕ) (C m : ℕ) :
    modulus (profile R C m) ∣ C*m := Finset.lcm_dvd (fun _ h => (mem_filter.mp h).2)

private theorem count_one {q C N : ℕ} (hq : 0 < q) (hC : 0 < C) :
    q*((Ioc 0 N).filter (fun m => q ∣ C*m)).card ≤ C*N := by
  rw [multiples q C N hq]
  let g := q.gcd C
  have hq' : (q/g)*g=q := Nat.div_mul_cancel (Nat.gcd_dvd_left q C)
  calc
    _ = ((q/g)*g)*(N/(q/g)) := congrArg (fun x : ℕ => x*(N/(q/g))) hq'.symm
    _ = g*((q/g)*(N/(q/g))) := by ring
    _ ≤ g*N := Nat.mul_le_mul_left _ (Nat.mul_div_le N _)
    _ ≤ C*N := Nat.mul_le_mul_right N (Nat.gcd_le_right q hC)

/-- Distinct lcms are counted once, even when different subsets give
the same modulus. There are at most two to the number of conductors. -/
theorem discard (R : Finset ℕ) (C N : ℕ) (T : ℝ) (hC : 0 < C) (hT : 0 < T) :
    T*((bad R C N T).card : ℝ) ≤ (2 : ℝ)^R.card*C*N := by
  classical
  let Q : Finset ℕ := (moduli R).filter (fun q : ℕ => T < (q : ℝ))
  let V := fun q : ℕ => (Ioc 0 N).filter (fun m => q ∣ C*m)
  have hs : bad R C N T ⊆ Q.biUnion V := by
    intro m hm
    obtain ⟨hI,ht⟩ := mem_filter.mp hm
    have hp : profile R C m ∈ R.powerset := mem_powerset.mpr (filter_subset _ _)
    exact mem_biUnion.mpr ⟨_,mem_filter.mpr ⟨mem_image_of_mem _ hp,ht⟩,
      mem_filter.mpr ⟨hI,profile_dvd R C m⟩⟩
  have hcard : ((bad R C N T).card : ℝ) ≤ ∑ q ∈ Q, ((V q).card : ℝ) := by
    exact_mod_cast (card_le_card hs).trans card_biUnion_le
  have hQ : Q.card ≤ 2^R.card := by
    calc Q.card ≤ (moduli R).card := card_filter_le _ _
         _ ≤ R.powerset.card := card_image_le
         _ = _ := card_powerset _
  calc
    _ ≤ T*(∑ q ∈ Q, ((V q).card : ℝ)) := mul_le_mul_of_nonneg_left hcard hT.le
    _ = ∑ q ∈ Q, T*((V q).card : ℝ) := mul_sum _ _ _
    _ ≤ ∑ _q ∈ Q, (C : ℝ)*N := by
      apply sum_le_sum
      intro q hq
      have hq' : T < (q : ℝ) := (mem_filter.mp hq).2
      have hq0 : 0 < q := by exact_mod_cast hT.trans hq'
      exact (mul_le_mul_of_nonneg_right hq'.le (Nat.cast_nonneg _)).trans
        (by exact_mod_cast count_one hq0 hC)
    _ = (Q.card : ℝ)*((C : ℝ)*N) := by simp
    _ ≤ _ := by
      have hc : (Q.card : ℝ) ≤ (2 : ℝ)^R.card := by exact_mod_cast hQ
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_right hc (by positivity : 0 ≤ (C : ℝ)*N)

noncomputable def shifted (R : Finset ℕ) (C X : ℕ) (T : ℝ) : Finset ℕ :=
  @Finset.filter ℕ (fun n => Even n ∧ ∃ e ∈ Icc 1 (Nat.log 2 X/2),
    T < (modulus (profile R C (n-2^e)) : ℝ)) (Classical.decPred _) (Ico X (2*X))

private theorem shifted_card {R : Finset ℕ} {C X : ℕ} {T : ℝ} (hX : 8 ≤ X) :
    (shifted R C X T).card ≤ (Nat.log 2 X/2)*(bad R C (2*X) T).card := by
  classical
  let B := bad R C (2*X) T
  let I := Icc 1 (Nat.log 2 X/2)
  have hs : shifted R C X T ⊆ I.biUnion (fun e => B.image (fun m => m+2^e)) := by
    intro n hn
    simp only [shifted, mem_filter] at hn
    obtain ⟨hI,_,e,he,hmod⟩ := hn
    have hlog : 2 ≤ Nat.log 2 X := (Nat.le_log_iff_pow_le (by decide) (by omega)).2 (by omega)
    have hbound := (mem_Icc.mp he).2
    have hpower := (Nat.pow_le_pow_right (by decide : 0 < 2)
      (show e+1 ≤ Nat.log 2 X by omega)).trans (Nat.pow_log_le_self 2 (by omega : X ≠ 0))
    rw [pow_succ] at hpower
    have hn' : X ≤ n ∧ n < 2*X := mem_Ico.mp hI
    refine mem_biUnion.mpr ⟨e,he,mem_image.mpr ⟨n-2^e,?_,by omega⟩⟩
    exact mem_filter.mpr ⟨mem_Ioc.mpr ⟨by omega,by omega⟩,hmod⟩
  calc _ ≤ _ := card_le_card hs
       _ ≤ ∑ e ∈ I, (B.image (fun m => m+2^e)).card := card_biUnion_le
       _ ≤ ∑ _e ∈ I, B.card := sum_le_sum (fun _ _ => card_image_le)
       _ = _ := by simp [I,B]

/-- A bounded number of exceptional conductors can vary with X. Those
with combined modulus above the quarter power, at any of the small
binary shifts, use at most the 31/40 power of the original block. -/
theorem shifted_power (K C : ℕ) (hC : 0 < C) :
    ∀ᶠ X : ℕ in atTop, ∀ R : Finset ℕ, R.card ≤ K →
      ((shifted R C X ((X : ℝ)^(1/4 : ℝ))).card : ℝ) ≤ (X : ℝ)^(31/40 : ℝ) := by
  let M := (2 : ℝ)^K*C*2/Real.log 2
  have h2 := Real.log_pos (by norm_num : (1 : ℝ)<2)
  have hCr : 0 < (C : ℝ) := Nat.cast_pos.mpr hC
  have hM : 0 < M := by dsimp [M]; positivity
  have hsmall := ((isLittleO_log_rpow_atTop (by norm_num : (0:ℝ)<1/40)).comp_tendsto
    (tendsto_natCast_atTop_atTop (R := ℝ))).bound (inv_pos.mpr hM)
  filter_upwards [eventually_ge_atTop (8 : ℕ),hsmall] with X hX hs
  intro R hR
  have hx : 0 < (X : ℝ) := by exact_mod_cast (show 0 < X by omega)
  have hl : 0 ≤ Real.log X := Real.log_natCast_nonneg X
  let T := (X : ℝ)^(1/4 : ℝ)
  have hT : 0 < T := Real.rpow_pos_of_pos hx _
  have hD := discard R C (2*X) T hC hT
  have hRK := pow_le_pow_right₀ (by norm_num : (1:ℝ)≤2) hR
  have hcard : T*((bad R C (2*X) T).card : ℝ) ≤ (2:ℝ)^K*C*(2*(X:ℝ)) := by
    push_cast at hD
    exact hD.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hRK hCr.le) (by positivity))
  have hL : ((Nat.log 2 X/2 : ℕ) : ℝ) ≤ Real.log X/Real.log 2 :=
    (Nat.cast_le.mpr (Nat.div_le_self _ _)).trans (Real.natLog_le_logb X 2)
  have hnat : ((shifted R C X T).card : ℝ) ≤
      ((Nat.log 2 X/2 : ℕ) : ℝ)*(bad R C (2*X) T).card := by
    exact_mod_cast shifted_card (R:=R) (C:=C) (T:=T) hX
  have hsum : T*((shifted R C X T).card : ℝ) ≤ Real.log X/Real.log 2 *
      ((2 : ℝ)^K*C*(2*(X : ℝ))) := calc
    _ ≤ T*(((Nat.log 2 X/2 : ℕ) : ℝ)*(bad R C (2*X) T).card) :=
      mul_le_mul_of_nonneg_left hnat hT.le
    _ = ((Nat.log 2 X/2 : ℕ) : ℝ)*(T*(bad R C (2*X) T).card) := by ring
    _ ≤ _ := mul_le_mul hL hcard (by positivity) (by positivity)
  have hs' : Real.log X ≤ M⁻¹*(X : ℝ)^(1/40 : ℝ) := by
    simpa only [Function.comp_apply,Real.norm_eq_abs,abs_of_nonneg hl,
      abs_of_nonneg (Real.rpow_nonneg hx.le _)] using hs
  have hml : M*Real.log X ≤ (X : ℝ)^(1/40 : ℝ) := by
    have hh := mul_le_mul_of_nonneg_left hs' hM.le
    rwa [← mul_assoc,mul_inv_cancel₀ hM.ne',one_mul] at hh
  apply le_of_mul_le_mul_left _ hT
  refine hsum.trans ?_
  calc
    _ = (M*Real.log X)*(X : ℝ) := by dsimp [M]; ring
    _ ≤ (X : ℝ)^(1/40 : ℝ)*(X : ℝ) := mul_le_mul_of_nonneg_right hml hx.le
    _ = T*(X : ℝ)^(31/40 : ℝ) := by
      dsimp [T]
      rw [← Real.rpow_add hx, ← Real.rpow_add_one hx.ne']
      norm_num

end Conjectures.Goldbach.SharpSingularSeriesRatiosProof.ExceptionalConductorClasses

/-! The pole and one exceptional zero in the generalized Goldbach
explicit formula. Estimate their actual singular series, beta factors
and powers together. Only multiples of r/(r,36) can lose the resulting
lower bound once the conductor is large. This estimates the displayed
terms of the formula; the analytic remainder stays explicit.
See Pintz I, (11.41)–(11.42), https://arxiv.org/abs/1804.05561. -/

namespace Conjectures.Goldbach.SharpSingularSeriesRatiosProof.SingleExceptionalZeroMajorFloor

open Finset Real DirichletCharacter TwistedGoldbachLocalProduct TwistedGoldbachConductorSuppression
open TwistedGoldbachMixedPrincipal
open scoped BigOperators Classical

private theorem prime_fourth {p : ℕ} (hp : p.Prime) :
    (primeRatio p)^4 ≤ (p:ℝ)*((if p=2 then 8 else 1)*(if p=3 then 2 else 1)) := by
  by_cases p2 : p=2
  · subst p; norm_num [primeRatio]
  by_cases p3 : p=3
  · subst p; norm_num [primeRatio]
  have p5 : 5 ≤ p := by by_contra! sm; interval_cases p <;> norm_num at *
  have pr : (5:ℝ) ≤ p := by exact_mod_cast p5
  have nonneg : 0 ≤ primeRatio p := div_nonneg (Nat.cast_nonneg p) (by linarith)
  have bound : primeRatio p ≤ 5/4 := (div_le_iff₀ (show 0 < (p:ℝ)-1 by linarith)).mpr (by linarith)
  simp only [p2,p3,ite_false,mul_one]
  exact (pow_le_pow_left₀ nonneg bound 4).trans (by linarith)

/-- A concrete totient bound without any asymptotic threshold. -/
theorem totient_fourth (r : ℕ) (hr : 0 < r) : (totRatio r)^4 ≤ 16*r := by
  classical
  let D (p : ℕ) : ℝ := (if p=2 then 8 else 1)*(if p=3 then 2 else 1)
  have sup : ∏ p ∈ r.primeFactors, D p ≤ 16 := by
    simp only [D,prod_mul_distrib,prod_ite_eq']
    split_ifs <;> norm_num
  have rad : (∏ p ∈ r.primeFactors, (p:ℝ)) ≤ r := by
    rw [← Nat.cast_prod]
    exact_mod_cast Nat.le_of_dvd hr (Nat.prod_primeFactors_dvd r)
  rw [totient_euler r hr,← prod_pow]
  calc
    _ ≤ ∏ p ∈ r.primeFactors, (p:ℝ)*D p := prod_le_prod₀
      (fun p h => by
        have hpr : 1 < (p:ℝ) := by exact_mod_cast (Nat.prime_of_mem_primeFactors h).one_lt
        exact pow_nonneg (div_nonneg (Nat.cast_nonneg p) (by linarith)) _)
      (fun _ h => prime_fourth (Nat.prime_of_mem_primeFactors h))
    _ = (∏ p ∈ r.primeFactors, (p:ℝ))*(∏ p ∈ r.primeFactors, D p) := prod_mul_distrib
    _ ≤ (r:ℝ)*16 := mul_le_mul rad sup (prod_nonneg fun p _ => by dsimp [D]; split_ifs <;> norm_num) (Nat.cast_nonneg _)
    _ = _ := mul_comm ..

theorem mixed_decay {r : ℕ} [NeZero r] (χ : DirichletCharacter ℂ r) (hχ : χ.IsPrimitive)
    (m : ℕ) (hm : 0 < m) (he : Even m) :
    ‖series χ (1 : DirichletCharacter ℂ 1) m‖*sqrt r ≤
      8*‖series (1 : DirichletCharacter ℂ 1) (1 : DirichletCharacter ℂ 1) m‖ := by
  let O := ‖series (1 : DirichletCharacter ℂ 1) (1 : DirichletCharacter ℂ 1) m‖
  have rpos : 0 < (r:ℝ) := by exact_mod_cast NeZero.pos r
  have phi : 0 < (r.totient:ℝ) := by exact_mod_cast Nat.totient_pos.mpr (NeZero.pos r)
  have H := sqrt_le_sqrt (totient_fourth r (NeZero.pos r))
  rw [show (totRatio r)^4=((totRatio r)^2)^2 by ring,sqrt_sq (sq_nonneg _),
    sqrt_mul (by norm_num : (0:ℝ) ≤ 16),show sqrt (16:ℝ)=4 by norm_num] at H
  have raw : (2*(r:ℝ)/(r.totient:ℝ)^2)*sqrt r ≤ 8 := by
    calc
      (2*(r:ℝ)/(r.totient:ℝ)^2)*sqrt r = ((totRatio r)^2)*(2*sqrt r)/r := by
        unfold totRatio
        field_simp
      _ ≤ (4*sqrt r)*(2*sqrt r)/r := div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right H (by positivity)) rpos.le
      _ = 8 := by
        rw [show (4*sqrt r)*(2*sqrt r)=8*(sqrt r*sqrt r) by ring,mul_self_sqrt rpos.le]
        field_simp
  have mixed := mul_le_mul_of_nonneg_right (mixed_bound χ hχ m hm he) (sqrt_nonneg (r:ℝ))
  change _ ≤ 8*O
  calc
    _ ≤ ((2*(r:ℝ)/(r.totient:ℝ)^2)*O)*sqrt r := mixed
    _ = ((2*(r:ℝ)/(r.totient:ℝ)^2)*sqrt r)*O := by ring
    _ ≤ 8*O := mul_le_mul_of_nonneg_right raw (norm_nonneg _)

noncomputable def kernel (m : ℕ) (z w : ℂ) : ℂ :=
  (Complex.Gamma z*Complex.Gamma w/Complex.Gamma (z+w))*(m:ℂ)^(z+w-1)

theorem kernel_bound {m : ℕ} (hm : 0 < m) {z w : ℂ}
    (hz : 1-1/128 ≤ z.re) (hz' : z.re ≤ 1) (hw : 1-1/128 ≤ w.re) (hw' : w.re ≤ 1) :
    ‖kernel m z w‖ ≤ (17/16:ℝ)*m := by
  have B := ExceptionalZeroBetaBound.gamma_ratio (δ := 1/128) (by norm_num) (by norm_num) hz hw
  have bound : ‖Complex.Gamma z*Complex.Gamma w/Complex.Gamma (z+w)‖ ≤ (17/16:ℝ) :=
    B.trans (by linarith [Real.pi_lt_four])
  have mp : (0:ℝ) < m := by exact_mod_cast hm
  have power : ‖(m:ℂ)^(z+w-1)‖ ≤ (m:ℝ) := by
    change ‖((m:ℝ):ℂ)^(z+w-1)‖ ≤ _
    rw [Complex.norm_cpow_eq_rpow_re_of_pos mp,Complex.sub_re,Complex.add_re,Complex.one_re]
    simpa using Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hm : (1:ℝ) ≤ m) (by linarith : z.re+w.re-1 ≤ 1)
  rw [kernel,norm_mul]
  exact mul_le_mul bound power (norm_nonneg _) (by norm_num)

noncomputable def mainTerms {r : ℕ} (χ : DirichletCharacter ℂ r) (z : ℂ) (m : ℕ) : ℂ :=
  let oneχ : DirichletCharacter ℂ 1 := 1
  (m:ℂ)*series oneχ oneχ m - 2*(series χ oneχ m*kernel m z 1) + series χ χ m*kernel m z z

/-- The pole and a single near-one zero leave a positive fraction of
the ordinary term off the exceptional congruence class. The error can
be any complex number. -/
theorem main_floor {r : ℕ} [NeZero r] (χ : DirichletCharacter ℂ r) (hχ : χ.IsPrimitive)
    (z : ℂ) (hz : 1-1/128 ≤ z.re) (hz' : z.re ≤ 1)
    (m : ℕ) (hm : 0 < m) (he : Even m) (off : ¬ r ∣ 36*m)
    (smallMixed : 262144 ≤ r ∨ ¬Squarefree r ∨ ¬m.Coprime r) (err : ℂ) :
    ‖series (1 : DirichletCharacter ℂ 1) (1 : DirichletCharacter ℂ 1) m‖*(m:ℝ)/6 - ‖err‖ ≤
      (mainTerms χ z m+err).re := by
  let P : DirichletCharacter ℂ 1 := 1
  let S := series P P m
  let O := ‖S‖
  let M := series χ P m*kernel m z 1
  let D := series χ χ m*kernel m z z
  have Op : 0 ≤ O := norm_nonneg _
  have mp : 0 ≤ (m:ℝ) := Nat.cast_nonneg _
  have Oeq : S.re=O := le_antisymm (Complex.re_le_norm S)
    (TwistedGoldbachSingularSeries.infinite_domination (α := P) (β := P)
      isPrimitive_one_level_one isPrimitive_one_level_one m hm)
  have msmall : ‖series χ P m‖ ≤ O/64 := by
    rcases smallMixed with big | vanish
    · have sr : 512 ≤ sqrt (r:ℝ) := le_sqrt_of_sq_le (by exact_mod_cast big)
      have a := (mul_le_mul_of_nonneg_left sr (norm_nonneg (series χ P m))).trans (mixed_decay χ hχ m hm he)
      change ‖series χ P m‖*512 ≤ 8*O at a
      linarith
    · rw [mixed_zero χ hχ m hm he vanish,norm_zero]
      positivity
  have diag : ‖series χ χ m‖ ≤ 3/4*O := by
    have H := TwistedGoldbachExceptionalGap.same_level_gap hχ hχ m hm he off
    change 4*‖series χ χ m‖ ≤ 3*O at H
    linarith
  have mlim : ‖M‖ ≤ (O/64)*((17/16:ℝ)*m) := by
    dsimp only [M]
    rw [norm_mul]
    exact mul_le_mul msmall (kernel_bound hm hz hz' (by norm_num) (by norm_num)) (norm_nonneg _) (by positivity)
  have dlim : ‖D‖ ≤ (3/4*O)*((17/16:ℝ)*m) := by
    dsimp only [D]
    rw [norm_mul]
    exact mul_le_mul diag (kernel_bound hm hz hz' hz hz') (norm_nonneg _) (by positivity)
  have Mre := (Complex.re_le_norm M).trans mlim
  have Dre := (abs_le.mp (Complex.abs_re_le_norm D)).1
  have E := (abs_le.mp (Complex.abs_re_le_norm err)).1
  change O*(m:ℝ)/6-‖err‖ ≤ ((m:ℂ)*S-2*M+D+err).re
  simp only [Complex.add_re,Complex.sub_re,Complex.mul_re,Complex.natCast_re,Complex.natCast_im,
    show (2:ℂ).re=2 by rfl,show (2:ℂ).im=0 by rfl,zero_mul,sub_zero,Oeq]
  nlinarith only [Mre,Dre,dlim,E,mul_nonneg Op mp]

/-- Positive even targets that violate the one-eighth floor are counted
by a single progression after cancelling the common divisor with 36. -/
theorem exceptional_count {r : ℕ} [NeZero r] (χ : DirichletCharacter ℂ r) (hχ : χ.IsPrimitive)
    (z : ℂ) (hz : 1-1/128 ≤ z.re) (hz' : z.re ≤ 1) (big : 262144 ≤ r)
    (N : ℕ) (err : ℕ → ℂ) (herr : ∀ m ∈ Ioc 0 N, Even m → ‖err m‖ ≤ (m:ℝ)/24) :
    ((Ioc 0 N).filter (fun m : ℕ => isEvenGoldbachTarget m ∧ (mainTerms χ z m+err m).re < (m:ℝ)/8)).card ≤
      N/(r/(r.gcd 36)) := by
  classical
  rw [← ExceptionalConductorClasses.multiples r 36 N (NeZero.pos r)]
  apply card_le_card
  intro m hmem
  obtain ⟨hi,he,low⟩ := mem_filter.mp hmem
  refine mem_filter.mpr ⟨hi,?_⟩
  by_contra gap
  have hm := (mem_Ioc.mp hi).1
  have bound := main_floor χ hχ z hz hz' m hm he gap (.inl big) (err m)
  let P : DirichletCharacter ℂ 1 := 1
  have O : 1 ≤ ‖series P P m‖ := (ordinary_at_least_one m hm he).trans (Complex.re_le_norm _)
  have lower := mul_le_mul_of_nonneg_right O (Nat.cast_nonneg (α := ℝ) m)
  change ‖series P P m‖*(m:ℝ)/6-‖err m‖ ≤ _ at bound
  linarith only [low,bound,lower,herr m hi he]

end Conjectures.Goldbach.SharpSingularSeriesRatiosProof.SingleExceptionalZeroMajorFloor

/-! Optimal uniform constants for the twisted Goldbach singular series
and a finite-conductor lower bound in the one-real-character case. -/

namespace Conjectures.Goldbach.SharpSingularSeriesRatiosProof.SharpSingularSeriesRatios

open Finset DirichletCharacter TwistedGoldbachLocalProduct TwistedGoldbachConductorRatio
open TwistedGoldbachConductorComponents SquarefreeTwistedGoldbachDensity
open SharpTwistedGoldbachGap InverseGoldbachSingularGap SingleExceptionalZeroMajorFloor
open TwistedGoldbachMixedPrincipal
open scoped Classical

/-- On the unit targets at a squarefree conductor with a prime above 5,
each of the mixed and quadratic Jacobi factors loses a factor of five. -/
theorem fifth_at_unit {r : ℕ} [NeZero r] {χ : DirichletCharacter ℂ r}
    (prim : χ.IsPrimitive) (realχ : χ.IsQuadratic) (sf : Squarefree r)
    (large : ¬r ∣ 30) (m : ℕ) (hm : 0 < m) (he : Even m) (cop : m.Coprime r) :
    let P : DirichletCharacter ℂ 1 := 1
    5*‖series χ P m‖ ≤ ‖series P P m‖ ∧ 5*‖series χ χ m‖ ≤ ‖series P P m‖ := by
  intro P
  obtain ⟨p,member,bad⟩ := large_coordinate (by decide : 0<30) large
  obtain ⟨hp,pr,_⟩ := Nat.mem_primeFactors.mp member
  have valp := Nat.factorization_eq_one_of_squarefree sf hp pr
  let i : r.primeFactors := ⟨p,member⟩
  let e := ZMod.equivPi r (NeZero.ne r)
  let (k : r.primeFactors) : NeZero ((k:ℕ)^r.factorization k) := ⟨(Nat.ordProj_pos r k).ne'⟩
  let Q := p^r.factorization p
  let _ : NeZero Q := ⟨(Nat.ordProj_pos r p).ne'⟩
  have Qp : Q=p := by simp [Q,valp]
  let _ : Fact Q.Prime := ⟨Qp ▸ hp⟩
  have largeQ : 7 ≤ Q := by
    rw [Qp]
    by_contra! small
    rw [valp,pow_one] at bad
    interval_cases p <;> norm_num at *
  have nz : (m:ZMod Q) ≠ 0 := by
    intro h
    have d := (ZMod.natCast_eq_zero_iff m Q).mp h
    rw [Qp] at d
    have t := Nat.dvd_gcd d pr
    rw [cop] at t
    exact hp.not_dvd_one t
  let A := component e χ i
  have cond : A.conductor=Q := by
    dsimp only [A]
    rw [component_conductor e (fun k : r.primeFactors => Nat.ordProj_dvd r k)
      r.pairwise_coprime_pow_primeFactors_factorization,prim,Nat.gcd_eq_left (Nat.ordProj_dvd ..)]
  have N : A ≠ 1 := by
    intro h
    rw [h,conductor_one] at cond
    omega
  have pair : χ*χ=1 := by simpa [realχ.inv] using mul_inv_cancel χ
  have AA : A*A=1 := by dsimp only [A]; rw [← component_mul,pair,component_one]
  have M := local_norm A (1 : DirichletCharacter ℂ Q) (m:ZMod Q)
  have D := local_norm A A (m:ZMod Q)
  have O := local_norm (1 : DirichletCharacter ℂ Q) 1 (m:ZMod Q)
  simp only [nz,ite_false,N,false_and,true_or,or_true,ite_true] at M
  simp [nz,N,AA] at D
  simp [nz] at O
  change ‖J A 1 (m:ZMod Q)‖=1 at M
  change ‖J A A (m:ZMod Q)‖=1 at D
  let W := ‖J (1 : DirichletCharacter ℂ Q) 1 (m:ZMod Q)‖
  change W=(Q:ℝ)-2 at O
  have lw : 5 ≤ W := by rw [O]; linarith only [show (7:ℝ) ≤ Q by exact_mod_cast largeQ]
  have F := single_factor e prim isPrimitive_one_level_one (dvd_refl r) (one_dvd r) m hm he i
  simp only [changeLevel_self,map_one,component_one] at F
  have G := single_factor e prim prim (dvd_refl r) (dvd_refl r) m hm he i
  simp only [changeLevel_self] at G
  change ‖series χ P m‖*W ≤ ‖series P P m‖*‖J A 1 (m:ZMod Q)‖ at F
  change ‖series χ χ m‖*W ≤ ‖series P P m‖*‖J A A (m:ZMod Q)‖ at G
  rw [M,mul_one] at F
  rw [D,mul_one] at G
  constructor
  · linarith only [F,mul_le_mul_of_nonneg_left lw (norm_nonneg (series χ P m))]
  · linarith only [G,mul_le_mul_of_nonneg_left lw (norm_nonneg (series χ χ m))]

/-- The combined relative size of the two mixed terms and the diagonal
is at most 3/5 when the conductor avoids the finite small divisors. -/
theorem combined_coefficients {r : ℕ} [NeZero r] {χ : DirichletCharacter ℂ r}
    (prim : χ.IsPrimitive) (realχ : χ.IsQuadratic) (large : ¬r ∣ 30)
    (m : ℕ) (hm : 0 < m) (he : Even m) (off : ¬r ∣ 6*m) :
    let P : DirichletCharacter ℂ 1 := 1
    2*‖series χ P m‖+‖series χ χ m‖ ≤ (3/5:ℝ)*‖series P P m‖ := by
  intro P
  by_cases h : Squarefree r ∧ m.Coprime r
  · obtain ⟨a,b⟩ := fifth_at_unit prim realχ h.1 large m hm he h.2
    linarith
  · rw [show series χ P m=0 from mixed_zero χ prim m hm he (not_and_or.mp h),norm_zero]
    have d := quadratic_gap prim realχ m hm he off
    linarith [norm_nonneg (series P P m)]

theorem one_zero_floor {r : ℕ} [NeZero r] {χ : DirichletCharacter ℂ r}
    (prim : χ.IsPrimitive) (realχ : χ.IsQuadratic) (large : ¬r ∣ 30)
    (z : ℂ) (hz : 1-1/128 ≤ z.re) (hz' : z.re ≤ 1)
    (m : ℕ) (hm : 0 < m) (he : Even m) (off : ¬r ∣ 6*m) (err : ℂ) :
    let P : DirichletCharacter ℂ 1 := 1
    (29/80:ℝ)*‖series P P m‖*m-‖err‖ ≤ (mainTerms χ z m+err).re := by
  intro P
  let S := series P P m
  let M := series χ P m*kernel m z 1
  let D := series χ χ m*kernel m z z
  have Oeq : S.re=‖S‖ := le_antisymm (Complex.re_le_norm S)
    (TwistedGoldbachSingularSeries.infinite_domination (α := P) (β := P)
      isPrimitive_one_level_one isPrimitive_one_level_one m hm)
  have ml : ‖M‖ ≤ ‖series χ P m‖*((17/16:ℝ)*m) := by
    dsimp only [M]; rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (kernel_bound hm hz hz' (by norm_num) (by norm_num)) (norm_nonneg _)
  have dl : ‖D‖ ≤ ‖series χ χ m‖*((17/16:ℝ)*m) := by
    dsimp only [D]; rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (kernel_bound hm hz hz' hz hz') (norm_nonneg _)
  have together := mul_le_mul_of_nonneg_right (combined_coefficients prim realχ large m hm he off)
    (by positivity : 0 ≤ (17/16:ℝ)*m)
  change (2*‖series χ P m‖+‖series χ χ m‖)*_ ≤ ((3/5:ℝ)*‖S‖)*_ at together
  have RM := (Complex.re_le_norm M).trans ml
  have RD := (abs_le.mp (Complex.abs_re_le_norm D)).1
  have RE := (abs_le.mp (Complex.abs_re_le_norm err)).1
  change (29/80:ℝ)*‖S‖*m-‖err‖ ≤ ((m:ℂ)*S-2*M+D+err).re
  simp only [Complex.add_re,Complex.sub_re,Complex.mul_re,Complex.natCast_re,Complex.natCast_im,
    show (2:ℂ).re=2 by rfl,show (2:ℂ).im=0 by rfl,zero_mul,sub_zero,Oeq]
  linarith only [RM,RD,dl,RE,together]

theorem count_below_quarter {r : ℕ} [NeZero r] {χ : DirichletCharacter ℂ r}
    (prim : χ.IsPrimitive) (realχ : χ.IsQuadratic) (large : ¬r ∣ 30)
    (z : ℂ) (hz : 1-1/128 ≤ z.re) (hz' : z.re ≤ 1) (N : ℕ) (err : ℕ → ℂ)
    (herr : ∀ m ∈ Ioc 0 N, Even m → ‖err m‖ ≤ (9/80:ℝ)*m) :
    ((Ioc 0 N).filter (fun m : ℕ => isEvenGoldbachTarget m ∧ (mainTerms χ z m+err m).re < (m:ℝ)/4)).card ≤
      N/(r/(r.gcd 6)) := by
  classical
  rw [← ExceptionalConductorClasses.multiples r 6 N (NeZero.pos r)]
  apply card_le_card
  intro m mem
  obtain ⟨hi,he,low⟩ := mem_filter.mp mem
  refine mem_filter.mpr ⟨hi,?_⟩
  by_contra off
  have hm := (mem_Ioc.mp hi).1
  let P : DirichletCharacter ℂ 1 := 1
  have O : 1 ≤ ‖series P P m‖ := (ordinary_at_least_one m hm he).trans (Complex.re_le_norm _)
  have lower := mul_le_mul_of_nonneg_right O (Nat.cast_nonneg (α := ℝ) m)
  have bound := one_zero_floor prim realχ large z hz hz' m hm he off (err m)
  change (29/80:ℝ)*‖series P P m‖*m-‖err m‖ ≤ _ at bound
  linarith only [low,bound,lower,herr m hi he]

/-- At every odd prime the quadratic character realizes both local
ratios on every unit target. The levels 5 and 7 give the extremizers
for the inverse diagonal and for the sum of the three coefficients. -/
theorem prime_quadratic_ratios (p : ℕ) (hp : p.Prime) (oddp : 3 ≤ p) :
    ∃ χ : DirichletCharacter ℂ p, χ.IsPrimitive ∧ χ.IsQuadratic ∧
      ∀ m : ℕ, 0 < m → Even m → ¬p ∣ m →
        let P : DirichletCharacter ℂ 1 := 1
        ((p:ℝ)-2)*‖series χ P m‖=‖series P P m‖ ∧
        ((p:ℝ)-2)*‖series χ χ m‖=‖series P P m‖ := by
  let _ : Fact p.Prime := ⟨hp⟩
  let _ : NeZero p := ⟨hp.ne_zero⟩
  let f := Int.castRingHom ℂ
  let χ : DirichletCharacter ℂ p := (quadraticChar (ZMod p)).ringHomComp f
  have realχ : χ.IsQuadratic := (quadraticChar_isQuadratic _).comp f
  have N : χ ≠ 1 := (MulChar.ringHomComp_ne_one_iff (show Function.Injective f from Int.cast_injective)).mpr
    (quadraticChar_ne_one (by rw [ZMod.ringChar_zmod_n]; omega))
  have prim : χ.IsPrimitive := by
    rcases (Nat.dvd_prime hp).mp χ.conductor_dvd_level with H|H
    · exact False.elim (N (eq_one_iff_conductor_eq_one.mpr H))
    · exact H
  refine ⟨χ,prim,realχ,?_⟩
  intro m hm he unit P
  have nz : (m:ZMod p) ≠ 0 := mt (ZMod.natCast_eq_zero_iff m p).mp unit
  have pair : χ*χ=1 := by simpa only [realχ.inv] using mul_inv_cancel χ
  have O := local_norm (1 : DirichletCharacter ℂ p) 1 (m:ZMod p)
  simp [nz] at O
  change ‖J (1 : DirichletCharacter ℂ p) 1 (m:ZMod p)‖=(p:ℝ)-2 at O
  have pos : (0:ℝ) < (p:ℝ)-2 := by linarith only [show (3:ℝ) ≤ p by exact_mod_cast oddp]
  have transfer {s : ℕ} [NeZero s] (β : DirichletCharacter ℂ s) (hβ : β.IsPrimitive)
      (d : s ∣ p) (v : ‖J χ (changeLevel d β) (m:ZMod p)‖=1) :
      ((p:ℝ)-2)*‖series χ β m‖=‖series P P m‖ := by
    have F := exact_ratio prim hβ (dvd_refl p) d m hm he
    rw [changeLevel_self,← principal_card] at F
    change series χ β m = series P P m * (J χ (changeLevel d β) (m:ZMod p) / J 1 1 (m:ZMod p)) at F
    rw [F,norm_mul,norm_div,v,O]
    field_simp
  constructor
  · apply transfer P isPrimitive_one_level_one (one_dvd p)
    dsimp only [P]
    rw [map_one]
    have T := local_norm χ (1 : DirichletCharacter ℂ p) (m:ZMod p)
    change ‖localSum χ 1 (m:ZMod p)‖=1
    simpa [nz,N] using T
  · apply transfer χ prim (dvd_refl p)
    rw [changeLevel_self]
    have T := local_norm χ χ (m:ZMod p)
    change ‖localSum χ χ (m:ZMod p)‖=1
    simpa [nz,N,pair] using T

end Conjectures.Goldbach.SharpSingularSeriesRatiosProof.SharpSingularSeriesRatios

open Conjectures.Goldbach.SharpSingularSeriesRatiosProof.SharpSingularSeriesRatios in
theorem Conjectures.Goldbach.SharpSingularSeriesRatios :
by
  classical
  let S := fun {r s : ℕ} (α : DirichletCharacter ℂ r) (β : DirichletCharacter ℂ s) (m : ℕ) =>
    ∑' q : ℕ, if hq : q ≠ 0 then
      let _ : NeZero q := ⟨hq⟩
      if h : r ∣ q ∧ s ∣ q then
        let A := DirichletCharacter.changeLevel h.1 α
        let B := DirichletCharacter.changeLevel h.2 β
        gaussSum A ZMod.stdAddChar * gaussSum B ZMod.stdAddChar *
          gaussSum (A*B)⁻¹ (ZMod.stdAddChar.mulShift (-(m:ZMod q))) / (q.totient:ℂ)^2
      else 0
    else 0
  let O := S (1 : DirichletCharacter ℂ 1) (1 : DirichletCharacter ℂ 1)
  let X := fun {r s : ℕ} (α : DirichletCharacter ℂ r) (β : DirichletCharacter ℂ s) (m : ℕ) =>
    r/(m.gcd r) ∣ 36 ∧ s/(m.gcd s) ∣ 36 ∧ r/(r.gcd s) ∣ 3 ∧ s/(r.gcd s) ∣ 3 ∧
      ((DirichletCharacter.changeLevel (Nat.dvd_lcm_left r s) α)*
       (DirichletCharacter.changeLevel (Nat.dvd_lcm_right r s) β)).conductor ∣ 36
  let P : DirichletCharacter ℂ 1 := 1
  let K := fun (m : ℕ) (z w : ℂ) =>
    (Complex.Gamma z*Complex.Gamma w/Complex.Gamma (z+w))*(m:ℂ)^(z+w-1)
  let F := fun {r : ℕ} (χ : DirichletCharacter ℂ r) (z : ℂ) (m : ℕ) =>
    (m:ℂ)*S P P m - 2*(S χ P m*K m z 1) + S χ χ m*K m z z
  exact
    (∀ K : ℝ, (∀ (r s : ℕ) [NeZero r] [NeZero s] (α : DirichletCharacter ℂ r) (β : DirichletCharacter ℂ s),
      α.IsPrimitive → β.IsPrimitive → ∀ m : ℕ, 0 < m → Even m → ¬X α β m →
      ‖S α β m‖ ≤ K*‖O m‖) ↔ Real.sqrt 5/3 ≤ K) ∧
    (∃ χ : DirichletCharacter ℂ 5, χ.IsPrimitive ∧ χ^4=1 ∧ χ*χ ≠ 1 ∧
      ∀ m : ℕ, 0 < m → Even m → ¬5 ∣ m → ¬X χ χ m ∧ 3*‖S χ χ m‖=Real.sqrt 5*‖O m‖) ∧
    (∀ (r : ℕ) [NeZero r] (χ ψ : DirichletCharacter ℂ r), χ.IsPrimitive → ψ.IsPrimitive →
      χ*ψ=1 → ∀ m : ℕ, 0 < m → Even m → ¬r ∣ 6*m → 3*‖S χ ψ m‖ ≤ ‖O m‖) ∧
    (∀ p : ℕ, p.Prime → 3 ≤ p → ∃ χ : DirichletCharacter ℂ p, χ.IsPrimitive ∧ χ.IsQuadratic ∧
      ∀ m : ℕ, 0 < m → Even m → ¬p ∣ m →
      ((p:ℝ)-2)*‖S χ P m‖=‖O m‖ ∧ ((p:ℝ)-2)*‖S χ χ m‖=‖O m‖) ∧
    (∀ (r : ℕ) [NeZero r] (χ : DirichletCharacter ℂ r), χ.IsPrimitive → χ.IsQuadratic → ¬r ∣ 30 →
      (∀ m : ℕ, 0 < m → Even m → ¬r ∣ 6*m →
        2*‖S χ P m‖+‖S χ χ m‖ ≤ (3/5:ℝ)*‖O m‖) ∧
      ∀ z : ℂ, 1-1/128 ≤ z.re → z.re ≤ 1 →
        (∀ m : ℕ, 0 < m → Even m → ¬r ∣ 6*m → ∀ err : ℂ,
          (29/80:ℝ)*‖O m‖*m-‖err‖ ≤ (F χ z m+err).re) ∧
        (∀ (N : ℕ) (err : ℕ → ℂ), (∀ m ∈ Finset.Ioc 0 N, Even m → ‖err m‖ ≤ (9/80:ℝ)*m) →
          ((Finset.Ioc 0 N).filter (fun m : ℕ => Even m ∧ (F χ z m+err m).re < (m:ℝ)/4)).card ≤
            N/(r/(r.gcd 6)))) := by
  refine ⟨Conjectures.Goldbach.SharpSingularSeriesRatiosProof.SharpTwistedGoldbachGap.1,Conjectures.Goldbach.SharpSingularSeriesRatiosProof.SharpTwistedGoldbachGap.2,
    Conjectures.Goldbach.SharpSingularSeriesRatiosProof.InverseGoldbachSingularGap,prime_quadratic_ratios,?_⟩
  intro r _ χ prim realχ large
  exact ⟨combined_coefficients prim realχ large,fun z hz hz' =>
    ⟨one_zero_floor prim realχ large z hz hz',count_below_quarter prim realχ large z hz hz'⟩⟩
