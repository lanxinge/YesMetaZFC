import YesMetaZFC.SetTheory.Descriptive.Game
import YesMetaZFC.SetTheory.Ord.NaturalPrime
import YesMetaZFC.Model.SetTheory.Internal.TypeGameNode

/-! # 原辅助博弈的三阶段时序

一轮依次为玩家 II 的辅助走法、玩家 I 的回答、原实数落子；第三步归属随轮号奇偶。
位置 i=3n+r 用对象模型的序数除法读取，有限历史不采用宿主列表。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal Descriptive
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

@[simp] theorem tg_division_closed_l (𝒞 : OrderedPairConvention) {d} (i c n r : Term d)
    (hi : i.freeSupport = []) (hc : c.freeSupport = []) (hn : n.freeSupport = []) (hr : r.freeSupport = []) :
    (Formula.isOrdinalDivision 𝒞 i c n r).FreeClosed := by
  simp -implicitDefEqProofs [Formula.isOrdinalDivision, Definitional.Formula.FreeClosed, hi, hc, hn, hr]

def Tg_event_d (J : kpair_convention_l.Interpretation M) (c n r h v : M.Domain) : Prop :=
  ∃ i, M.IsOrdinalDivision J i c n r ∧ Rd_entry_d i v h
def tg_event_m {d} (c n r h v : Term d) : Formula 1 d := set[d] ⟪∃ i,
  ⌜Formula.isOrdinalDivision kpair_convention_l⌝ₚ(i, ⌜c⌝ₛ, ⌜n⌝ₛ, ⌜r⌝ₛ) ∧ ⌜rd_entry0_m⌝ₚ(i, ⌜v⌝ₛ, ⌜h⌝ₛ)⟫
derive_free_closed tg_event_m

theorem tg_event_sat_l (J : kpair_convention_l.Interpretation M) (hE : Extensional M)
    {d} (ρ : Env M d) (c n r h v : Term d) :
    Formula.satisfies ρ (tg_event_m c n r h v) ↔
      Tg_event_d J (c.eval ρ) (n.eval ρ) (r.eval ρ) (h.eval ρ) (v.eval ρ) := by
  simp only [tg_event_m, Tg_event_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    Formula.satisfies_isOrdinalDivision_iff J hE, rd_entry0_sat_l hE, Definitional.Term.eval_weaken]
  rfl

theorem tg_index_unique_l {c n r i j : M.Domain} (hc : M.IsOrdinal c)
    (hi : M.IsOrdinalDivision I i c n r) (hj : M.IsOrdinalDivision I j c n r) : i = j := by
  obtain ⟨hn, hr, p, hp, ai⟩ := hi
  obtain ⟨_, _, q, hq, aj⟩ := hj
  obtain ⟨t, _, unique⟩ := ZF.ordinalMultiplication_existsUnique hZF I c hn
  have eq := (unique p hp).trans (unique q hq).symm
  subst q
  obtain ⟨s, _, unique⟩ := ZF.ordinalAddition_existsUnique hZF I p (hc.mem hr)
  exact (unique i ai).trans (unique j aj).symm

theorem Tg_event_d.unique_l {c n r h v w : M.Domain} (hc : M.IsOrdinal c) (fn : M.IsSetFunction I h)
    (a : Tg_event_d I c n r h v) (b : Tg_event_d I c n r h w) : v = w := by
  obtain ⟨i, hi, vi⟩ := a
  obtain ⟨j, hj, wj⟩ := b
  exact fn.2 i v w vi ((tg_index_unique_l hZF hc hi hj).symm ▸ wj)

/-- 同一轮内推进一个阶段；所有计数均为模型自身的序数。 -/
theorem tg_division_next_l {c n r s i j : M.Domain} (hc : M.IsOrdinal c)
    (div : M.IsOrdinalDivision I i c n r) (next : M.SuccessorOf s r)
    (step : M.SuccessorOf j i) (hs : M.mem s c) : M.IsOrdinalDivision I j c n s := by
  obtain ⟨hn, hr, p, mul, add⟩ := div
  exact ⟨hn, hs, p, mul, (ZF.ordinalAddition_successor_iff hZF I (hc.mem hr) next).mpr ⟨i, add, step⟩⟩

/-- 最后一阶段后进入下一轮，不依赖内部自然数的外部标准性。 -/
theorem tg_division_cycle_l {c n n' r i j e : M.Domain} (hc : M.IsOrdinal c)
    (div : M.IsOrdinalDivision I i c n r) (last : M.SuccessorOf c r)
    (next : M.SuccessorOf n' n) (step : M.SuccessorOf j i) (empty : ∀ x, ¬ M.mem x e) :
    M.IsOrdinalDivision I j c n' e := by
  obtain ⟨hn, hr, p, mul, add⟩ := div
  have sum := (ZF.ordinalAddition_successor_iff hZF I (hc.mem hr) last).mpr ⟨i, add, step⟩
  exact ⟨KP.successor_isOrdinal (ZF.modelsKP hZF) hn next,
    hc.empty_mem_of_nonempty (ZF.modelsKP hZF) ⟨r, last.predecessor_mem⟩ empty, j,
    (ZF.ordinalMultiplication_successor_iff hZF I hc hn next).mpr ⟨p, mul, sum⟩,
    (ZF.ordinalAddition_zero_iff hZF I empty).mpr rfl⟩

def Tg_owner_d (ω c a b J : M.Domain) : Prop := ∀ i,
  M.mem i J ↔ M.mem i ω ∧ ∃ n r, M.mem n ω ∧ M.IsOrdinalDivision I i c n r ∧ (r = a ∨ r = b ∧ Gm_even_d I ω n)

theorem tg_owner_l (ω c a b : M.Domain) : ∃ J, Tg_owner_d hZF ω c a b J := by
  let ρ : Env M 4 := (((⟨fun _ => ω, fun _ => ω⟩ : Env M 1).push c).push a).push b
  let φ : UnarySchema 4 := { body := .existsE (.conj (.mem .newest (.bound 5)) (.existsE (.conj
    (Formula.isOrdinalDivision kpair_convention_l (.bound 2) (.bound 5) (.bound 1) .newest)
    (.disj (Formula.extensionalEq .newest (.bound 4)) (.conj (Formula.extensionalEq .newest (.bound 3))
      (gm_even_m (𝒞 := kpair_convention_l) (.bound 6) (.bound 1))))))) }
  obtain ⟨J, sep⟩ := ZF.separation_exists_d hZF φ ρ ω
  refine ⟨J, fun i => (sep i).trans (and_congr Iff.rfl ?_)⟩
  simp only [φ, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff, Formula.satisfies_mem_iff,
    Formula.satisfies_disj_iff, Formula.satisfies_extensionalEq_iff_eq hZF.1,
    Formula.satisfies_isOrdinalDivision_iff I hZF.1, gm_even_sat_l I hZF.1]
  exact ⟨fun ⟨n, hn, r, div, own⟩ => ⟨n, r, hn, div, own⟩, fun ⟨n, r, hn, div, own⟩ => ⟨n, hn, r, div, own⟩⟩

theorem Tg_owner_d.read_l {ω c a b J i n r : M.Domain} (owner : Tg_owner_d hZF ω c a b J)
    (hω : M.IsOrdinal ω) (hc : M.IsOrdinal c) (nonzero : ∃ x, M.mem x c) (hi : M.mem i ω)
    (hn : M.mem n ω) (div : M.IsOrdinalDivision I i c n r) :
    M.mem i J ↔ r = a ∨ r = b ∧ Gm_even_d I ω n := by
  obtain ⟨q, s, _, unique⟩ := ZF.ordinalDivision_existsUnique_pair hZF I (hω.mem hi) hc nonzero
  obtain ⟨en, er⟩ := unique n r div
  refine (owner i).trans ⟨?_, fun own => ⟨hi, n, r, hn, div, own⟩⟩
  rintro ⟨_, n', r', _, d', own⟩
  obtain ⟨en', er'⟩ := unique n' r' d'
  exact (en'.trans en.symm) ▸ (er'.trans er.symm) ▸ own

/-- 每个内部时刻都有唯一商余分解，余数恰为原三阶段之一。 -/
theorem tg_clock_l {ω e a b c i : M.Domain} (hω : M.IsOmega ω) (he : ∀ x, ¬ M.mem x e)
    (ha : M.SuccessorOf a e) (hb : M.SuccessorOf b a) (hc : M.SuccessorOf c b) (hi : M.mem i ω) :
    M.mem c ω ∧ ∃ n r, M.mem n ω ∧ M.IsOrdinalDivision I i c n r ∧ (r = e ∨ r = a ∨ r = b) ∧
      ∀ n' r', M.IsOrdinalDivision I i c n' r' → n' = n ∧ r' = r := by
  have next {x y : M.Domain} (hx : M.mem x ω) (hy : M.SuccessorOf y x) : M.mem y ω := by
    obtain ⟨z, hz, hzω⟩ := hω.1.2 x hx
    exact hz.eq hZF.1 hy ▸ hzω
  have hcω := next (next (next (num_mem_l hZF.1 hω (show Num_d 0 e from he)) ha) hb) hc
  obtain ⟨n, r, div, unique⟩ := ZF.ordinalDivision_existsUnique_pair hZF I (hω.members_areOrdinals hZF i hi)
    (hω.members_areOrdinals hZF c hcω) ⟨b, hc.predecessor_mem⟩
  refine ⟨hcω, n, r, Structure.nat_div_quotient_mem_omega hZF I hω hi hcω ⟨b, hc.predecessor_mem⟩ div, div, ?_, unique⟩
  rcases (hc r).mp div.2.1 with hr | hr
  · rcases (hb r).mp hr with hr | hr
    · rcases (ha r).mp hr with hr | hr
      · exact (he r hr).elim
      · exact Or.inl (hZF.1.eq_of_same_members r e hr)
    · exact Or.inr (Or.inl (hZF.1.eq_of_same_members r a hr))
  · exact Or.inr (Or.inr (hZF.1.eq_of_same_members r b hr))

def Tg_digits_d (c r n A h x : M.Domain) : Prop := Fn0_d n A x ∧ ∀ i v, M.mem i n →
  (Rd_entry_d i v x ↔ Tg_event_d I c i r h v)
def tg_digits_m {d} (c r n A h x : Term d) : Formula 1 d := set[d] ⟪⌜fn0_m⌝ₚ(⌜n⌝ₛ, ⌜A⌝ₛ, ⌜x⌝ₛ) ∧
  (∀ i v, i ∈ ⌜n⌝ₛ → (⌜rd_entry0_m⌝ₚ(i, v, ⌜x⌝ₛ) ↔ ⌜tg_event_m⌝ₚ(⌜c⌝ₛ, i, ⌜r⌝ₛ, ⌜h⌝ₛ, v)))⟫
derive_free_closed tg_digits_m

theorem tg_digits_sat_l {d} (ρ : Env M d) (c r n A h x : Term d) :
    Formula.satisfies ρ (tg_digits_m c r n A h x) ↔
      Tg_digits_d hZF (c.eval ρ) (r.eval ρ) (n.eval ρ) (A.eval ρ) (h.eval ρ) (x.eval ρ) := by
  simp only [tg_digits_m, Tg_digits_d, Formula.satisfies_conj_iff, fn0_sat_l hZF.1,
    Formula.satisfies_forall_iff, Formula.satisfies_imp_iff, Formula.satisfies_mem_iff,
    Formula.satisfies_iff_iff, rd_entry0_sat_l hZF.1, tg_event_sat_l I hZF.1, Definitional.Term.eval_weaken]
  rfl

theorem tg_digits_exists_l {c r n A h : M.Domain} (hc : M.IsOrdinal c) (fn : M.IsSetFunction I h)
    (values : ∀ i, M.mem i n → ∃ v, M.mem v A ∧ Tg_event_d I c i r h v) :
    ∃ x, Tg_digits_d hZF c r n A h x := by
  let ρ : Env M 3 := ((⟨fun _ => c, fun _ => c⟩ : Env M 1).push r).push h
  let φ : BinarySchema 3 := { body := tg_event_m (.bound 4) (.bound 1) (.bound 3) (.bound 2) .newest }
  have sat i v : φ.denote ρ i v ↔ Tg_event_d I c i r h v := tg_event_sat_l I hZF.1 ..
  obtain ⟨x, fx, graph⟩ := ZF.exists_setFunctionFromTo_of_denote hZF I φ ρ (source := n) (target := A)
    (fun i hi => (values i hi).imp fun v hv => (sat i v).mpr hv.2)
    (fun i _ v w hv hw => ((sat i v).mp hv).unique_l hZF hc fn ((sat i w).mp hw))
    (fun i v hi hv => by
      obtain ⟨w, hw, event⟩ := values i hi
      exact (event.unique_l hZF hc fn ((sat i v).mp hv)) ▸ hw)
  exact ⟨x, fn0_of_function_l (ZF.modelsKP hZF) fx, fun i v hi =>
    (graph i v).trans ((and_iff_right hi).trans (sat i v))⟩

end YesMetaZFC.SetTheory.LargeCardinal
