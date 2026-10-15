import YesMetaZFC.SetTheory.Descriptive.Game
import YesMetaZFC.SetTheory.Ord.NaturalPrime

/-! # 内部回合在后继处换手

用模型自己的除二商余分解证明奇偶翻转，不对外部自然数作归纳。
-/
namespace YesMetaZFC.SetTheory.Descriptive
open Definitional.Project
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M) (hZF : M.Models ZF)
include hZF

theorem gm_even_zero_l {ω z : M.Domain} (hw : M.IsOmega ω) (hz : ∀ x, ¬ M.mem x z) : Gm_even_d I ω z := by
  obtain ⟨e, he, heω⟩ := hw.1.1
  have eq := hZF.1.eq_of_same_members e z fun x => iff_of_false (he x) (hz x)
  exact ⟨z, eq ▸ heω, (ZF.ordinalAddition_zero_iff hZF I hz).mpr rfl⟩

theorem gm_even_successor_l {ω n m : M.Domain} (hw : M.IsOmega ω) (hn : M.mem n ω)
    (sm : M.SuccessorOf m n) : Gm_even_d I ω m ↔ ¬ Gm_even_d I ω n := by
  obtain ⟨z, hz, hzω⟩ := hw.1.1
  obtain ⟨o, so, ho⟩ := hw.1.2 z hzω
  obtain ⟨t, st, ht⟩ := hw.1.2 o ho
  obtain ⟨m', sm', hm'⟩ := hw.1.2 n hn
  have hm := sm'.eq hZF.1 sm ▸ hm'
  have ot := hw.members_areOrdinals hZF t ht
  have oo := hw.members_areOrdinals hZF o ho
  have oz : o ≠ z := fun eq => hz z (eq ▸ so.predecessor_mem)
  have zt : M.mem z t := (st z).mpr (Or.inl so.predecessor_mem)
  -- 自然数乘法交换律把除二的乘积与博弈所用的 k+k 对齐。
  have twice {k v} (hk : M.mem k ω) : M.IsOrdinalMultiplication I v t k ↔ M.IsOrdinalAddition I v k k := by
    have read {v} (mul : M.IsOrdinalMultiplication I v t k) : M.IsOrdinalAddition I v k k := by
      obtain ⟨r, kr, _⟩ := ZF.ordinalMultiplication_existsUnique hZF I k ot
      have eq := Structure.natural_mul_comm hZF I hw ht hk mul kr; subst r
      obtain ⟨p, kp, add⟩ := (ZF.ordinalMultiplication_successor_iff hZF I (hw.members_areOrdinals hZF k hk) oo st).mp kr
      exact ZF.ordinalMultiplication_one_right hZF I (hw.members_areOrdinals hZF k hk) ⟨z, hz, so⟩ kp ▸ add
    refine ⟨read, fun add => ?_⟩
    obtain ⟨p, mul, _⟩ := ZF.ordinalMultiplication_existsUnique hZF I t (hw.members_areOrdinals hZF k hk)
    obtain ⟨_, _, unique⟩ := ZF.ordinalAddition_existsUnique hZF I k (hw.members_areOrdinals hZF k hk)
    exact (unique p (read mul)).trans (unique v add).symm ▸ mul
  -- 商余唯一性给出“偶数当且仅当余数为零”；后继只交换两个余数。
  have rem {i q r} (hi : M.mem i ω) (div : M.IsOrdinalDivision I i t q r) : Gm_even_d I ω i ↔ r = z := by
    constructor
    · rintro ⟨k, hk, add⟩
      have dz : M.IsOrdinalDivision I i t k z := ⟨hw.members_areOrdinals hZF k hk, zt, i,
        (twice hk).mpr add, (ZF.ordinalAddition_zero_iff hZF I hz).mpr rfl⟩
      obtain ⟨_, _, _, unique⟩ := ZF.ordinalDivision_existsUnique_pair hZF I (hw.members_areOrdinals hZF i hi) ot ⟨o, st.predecessor_mem⟩
      exact (unique q r div).2.trans (unique k z dz).2.symm
    · intro eq; subst r
      have hq := Structure.nat_div_quotient_mem_omega hZF I hw hi ht ⟨o, st.predecessor_mem⟩ div
      obtain ⟨_, _, p, mul, add⟩ := div
      exact ⟨q, hq, (ZF.ordinalAddition_zero_iff hZF I hz).mp add |>.symm ▸ (twice hq).mp mul⟩
  obtain ⟨q, r, div, _⟩ := ZF.ordinalDivision_existsUnique_pair hZF I (hw.members_areOrdinals hZF n hn) ot ⟨o, st.predecessor_mem⟩
  have cases : r = z ∨ r = o := ((st r).mp div.2.1).elim
    (fun h => ((so r).mp h).elim (fun h => (hz r h).elim) (fun h => Or.inl (hZF.1.eq_of_same_members r z h)))
    (fun h => Or.inr (hZF.1.eq_of_same_members r o h))
  rcases cases with rfl | rfl
  · have d := div
    obtain ⟨oq, _, p, mul, add⟩ := d
    have next : M.IsOrdinalDivision I m t q o := ⟨oq, st.predecessor_mem, p, mul,
      (ZF.ordinalAddition_successor_iff hZF I (Structure.IsOrdinal.of_no_members hz) so).mpr ⟨n, add, sm⟩⟩
    exact ⟨fun even => (oz ((rem hm next).mp even)).elim, fun no => (no ((rem hn div).mpr rfl)).elim⟩
  · have hq := Structure.nat_div_quotient_mem_omega hZF I hw hn ht ⟨_, st.predecessor_mem⟩ div
    obtain ⟨q', sq, hq'⟩ := hw.1.2 q hq
    have d := div
    obtain ⟨oq, _, p, mul, add⟩ := d
    have next : M.IsOrdinalDivision I m t q' z := ⟨hw.members_areOrdinals hZF q' hq', zt, m,
      (ZF.ordinalMultiplication_successor_iff hZF I ot oq sq).mpr ⟨p, mul,
        (ZF.ordinalAddition_successor_iff hZF I oo st).mpr ⟨n, add, sm⟩⟩,
      (ZF.ordinalAddition_zero_iff hZF I hz).mpr rfl⟩
    exact ⟨fun _ even => oz ((rem hn div).mp even), fun _ => (rem hm next).mpr rfl⟩

theorem gm_turn_successor_l (b : Bool) {ω n m : M.Domain} (hw : M.IsOmega ω) (hn : M.mem n ω)
    (sm : M.SuccessorOf m n) : Gm_turn_d I b ω m ↔ Gm_turn_d I (!b) ω n := by
  cases b
  · change (¬ Gm_even_d I ω m) ↔ Gm_even_d I ω n
    exact ⟨fun no => Classical.byContradiction (fun odd => no ((gm_even_successor_l I hZF hw hn sm).mpr odd)),
      fun even next => ((gm_even_successor_l I hZF hw hn sm).mp next) even⟩
  · exact gm_even_successor_l I hZF hw hn sm

end YesMetaZFC.SetTheory.Descriptive
