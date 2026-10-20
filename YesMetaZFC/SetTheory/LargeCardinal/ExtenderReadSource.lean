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
  refine ⟨source.transitive, source.omega_mem, source.theory.algebra.pair,
    fun n A f hn hA hf => sc_finite_function_l hZF source.omega source.transitive source.theory.algebra.pair source.theory.algebra.union
      source.omega_mem hA hn hf, fun A n hA hn => ?_⟩
  obtain ⟨D, hD, space⟩ := source.finite_space_l hZF hA hn
  exact ⟨D, hD, fun f => (space f).trans ⟨fn0_of_function_l (ZF.modelsKP hZF), fn0_function_l (ZF.modelsKP hZF)⟩⟩

theorem Fs_read_d.rank_l (hZF : M.Models ZF) {ω Z α V : M.Domain}
    (source : Fs_read_d ω Z) (hω₀ : M.IsOmega ω)
    (union : ∀ a, M.mem a Z → ∃ p, M.mem p Z ∧ M.IsUnionOf p a)
    (hV : M.mem V Z) (rank : Vr_d Z α V)
    (hα : M.IsLimitOrdinal α) (hω : M.mem ω V) : Fs_read_d ω V := by
  have vt := rank.transitive_l hZF source.transitive hV
  have pair a b (ha : M.mem a V) (hb : M.mem b V) : ∃ p, M.mem p V ∧ Pair_d M p a b := by
    obtain ⟨p, hp, code⟩ := source.pair a b (source.transitive V hV a ha) (source.transitive V hV b hb)
    exact ⟨p, rank.pair_mem_l hZF source.transitive hV hα ha hb hp code, code⟩
  have un a (ha : M.mem a V) : ∃ p, M.mem p V ∧ M.IsUnionOf p a := by
    obtain ⟨p, hp, code⟩ := union a (source.transitive V hV a ha)
    exact ⟨p, rank.union_mem_l hZF source.transitive hV ha hp code, code⟩
  refine ⟨vt, hω, pair, fun n A f hn hA hf => sc_finite_function_l hZF hω₀ vt pair un hω hA hn hf,
    fun A n hA hn => ?_⟩
  obtain ⟨D, hD, space⟩ := source.spaces A n (source.transitive V hV A hA) hn
  refine ⟨D, rank.relations_mem_l source.transitive hV hα hω hA hD (fun f hf p hp => ?_), space⟩
  obtain ⟨i, hi, x, hx, code⟩ := ((space f).mp hf).1 p hp
  exact ⟨i, hω₀.transitive hZF n hn i hi, x, hx, code⟩

theorem Ep_source_d.rank_read_source_l (hZF : M.Models ZF) {ω κ K Z W α V : M.Domain}
    (source : Ep_source_d hZF ω κ K Z W) (hV : M.mem V Z) (rank : Vr_d Z α V)
    (hα : M.IsLimitOrdinal α) (hω : M.mem ω V) : Fs_read_d ω V :=
  (source.read_source_l hZF).rank_l hZF source.omega source.theory.algebra.union hV rank hα hω

end YesMetaZFC.SetTheory.LargeCardinal
