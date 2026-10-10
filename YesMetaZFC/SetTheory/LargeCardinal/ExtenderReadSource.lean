import YesMetaZFC.SetTheory.LargeCardinal.ExtenderRankClosure

/-! # 读取超幂证书所需的有限闭性

读取只用传递性、配对和全部内部有限函数及其空间。完整源与任意包含 ω
的拥有极限秩段均提供实际实例；后一实例不需要该高度正则。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

structure Fs_read_d (ω V : M.Domain) : Prop where
  transitive : M.TransitiveSet V
  omega_mem : M.mem ω V
  pair : ∀ a b, M.mem a V → M.mem b V → ∃ p, M.mem p V ∧ Pair_d M p a b
  functions : ∀ n A f, M.mem n ω → M.MemberSubset A V → Fn0_d n A f → M.mem f V
  spaces : ∀ A n, M.mem A V → M.mem n ω → ∃ D, M.mem D V ∧ Ep_space_d A n D

theorem Fs_read_d.kpair_l {ω V a b : M.Domain} (h : Fs_read_d ω V)
    (ha : M.mem a V) (hb : M.mem b V) : ∃ p, M.mem p V ∧ KPair_d M p a b := by
  obtain ⟨s, hs, singleton⟩ := h.pair a a ha ha
  obtain ⟨t, ht, both⟩ := h.pair a b ha hb
  obtain ⟨p, hp, outer⟩ := h.pair s t hs ht
  exact ⟨p, hp, s, t, (fun x => (singleton x).trans ⟨fun h => h.elim id id, Or.inl⟩), both, outer⟩

theorem Ep_source_d.read_source_l (hZF : M.Models ZF) {ω κ K V W : M.Domain}
    (source : Ep_source_d hZF ω κ K V W) : Fs_read_d ω V := by
  obtain ⟨c, code⟩ := source.code
  refine ⟨source.transitive, source.omega_mem, source.theory.algebra.pair,
    fun n A f hn hA hf => sc_finite_function_l hZF source.omega source.transitive code source.theory
      source.omega_mem hA hn hf, fun A n hA hn => ?_⟩
  obtain ⟨D, hD, space⟩ := source.finite_space_l hZF hA hn
  exact ⟨D, hD, fun f => (space f).trans ⟨fn0_of_function_l (ZF.modelsKP hZF), fn0_function_l (ZF.modelsKP hZF)⟩⟩

theorem Ep_source_d.rank_read_source_l (hZF : M.Models ZF) {ω κ K Z W α V : M.Domain}
    (source : Ep_source_d hZF ω κ K Z W) (hV : M.mem V Z) (rank : Vr_d Z α V)
    (hα : M.IsLimitOrdinal α) (hω : M.mem ω V) : Fs_read_d ω V := by
  have vt := rank.transitive_l hZF source.transitive hV
  obtain ⟨c, R, code⟩ := smdl_membership_l (kp_pair_l (ZF.modelsKP hZF)) hZF ⟨ω, hω⟩
  have theory := source.rank_theory_l hZF hV rank hα code
  refine ⟨vt, hω, theory.algebra.pair,
    fun n A f hn hA hf => sc_finite_function_l hZF source.omega vt code theory hω hA hn hf, fun A n hA hn => ?_⟩
  obtain ⟨D, hD, space⟩ := source.finite_space_l hZF (source.transitive V hV A hA) hn
  have hd : Ep_space_d A n D := fun f => (space f).trans
    ⟨fn0_of_function_l (ZF.modelsKP hZF), fn0_function_l (ZF.modelsKP hZF)⟩
  refine ⟨D, rank.relations_mem_l source.transitive hV hα hω hA hD (fun f hf p hp => ?_), hd⟩
  obtain ⟨i, hi, x, hx, pair⟩ := ((hd f).mp hf).1 p hp
  exact ⟨i, source.omega.transitive hZF n hn i hi, x, hx, pair⟩

end YesMetaZFC.SetTheory.LargeCardinal
