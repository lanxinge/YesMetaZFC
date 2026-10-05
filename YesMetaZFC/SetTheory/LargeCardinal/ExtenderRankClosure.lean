import YesMetaZFC.SetTheory.LargeCardinal.ExtenderRankTheory

/-! # 相对秩段及初等回拉的完整源证书 -/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Ep_source_d.rank_sequences_l {ω κ K Z S α V : M.Domain}
    (source : Ep_source_d hZF ω κ K Z S) (hV : M.mem V Z) (rank : Vr_d Z α V)
    (hα : M.IsLimitOrdinal α) (hω : M.mem ω V) : Sc_sequences_d I ω V := by
  have hZ := source.transitive
  obtain ⟨c, hc⟩ := source.code
  refine ⟨fun A hA => ?_, fun A K μ e hA hK hμ he seq hw idx => ?_⟩
  · obtain ⟨K, hK, seq⟩ := source.sequences.space A (hZ V hV A hA)
    refine ⟨K, rank.relations_mem_l hZ hV hα hω hA hK (fun f hf p hp => ?_), seq⟩
    obtain ⟨n, hn, fn⟩ := (seq f).mp hf
    obtain ⟨i, hi, x, hx, pair⟩ := (fn0_of_function_l (ZF.modelsKP hZF) fn).1 p hp
    exact ⟨i, source.omega.transitive hZF n hn i hi, x, hx, pair⟩
  · have hkZ := hZ V hV K hK
    have hμZ := hZ V hV μ hμ
    obtain ⟨f, hf, bound⟩ := source.sequences.index A K μ e (hZ V hV A hA) hkZ hμZ (hZ V hV e he) seq hw idx
    obtain ⟨g, hg, inj⟩ := bound.restrict_l hZF source.omega hZ hc source.theory hkZ hμZ hf
    exact ⟨g, rank.relation_mem_l hZF hZ hV hα hK hμ hg (fn0_of_function_l (ZF.modelsKP hZF) inj.1).1,
      Sc_index_d.of_injection_l (ZF.modelsKP hZF) idx.ordinal inj⟩

/-- 内部正则严格秩段自动成为下一次超幂可直接消费的源。 -/
theorem Ep_source_d.rank_l {ω κ K Z S α V c R μ : M.Domain}
    (source : Ep_source_d hZF ω κ K Z S) (hV : M.mem V Z) (rank : Vr_d Z α V)
    (hα : M.IsLimitOrdinal α) (regular : Sc_regular_d Z α) (hω : M.mem ω V) (hm : Smem_d I c V R)
    (hμ : M.mem μ V) (ho : M.IsOrdinal μ) (hw : M.MemberSubset ω μ) : ∃ L, Ep_source_d hZF ω μ L V R := by
  have ht := rank.transitive_l hZF source.transitive hV
  have theory := source.rank_theory_l hZF hV rank hα hm
  have seq := source.rank_sequences_l hZF hV rank hα hω
  obtain ⟨L, hL, hs⟩ := seq.space μ hμ
  exact ⟨L, source.omega, hw, ht, hω, hμ, sc_ordinal_small_l hZF source.omega ht hm theory hμ ho,
    hL, hs, ⟨c, hm⟩, theory, source.rank_collection_l hZF hV rank hα regular hm, seq,
    source.rank_collapse_l hZF hV rank hα regular⟩

/-- 反塌缩的全初等图回拉全部源性质，不另给新模型的闭包证书。 -/
theorem Ep_source_d.pull_l {ω κ K Y S X c R d j μ : M.Domain}
    (target : Ep_source_d hZF ω κ K Y S) (hX : M.TransitiveSet X) (hωX : M.mem ω X)
    (hm : Smem_d I c X R) (hn : Smem_d I d Y S) (hj : Smap_d I ω c d X Y j)
    (hμ : M.mem μ X) (ho : M.IsOrdinal μ) (hw : M.MemberSubset ω μ) : ∃ L, Ep_source_d hZF ω μ L X R := by
  have theory := target.theory.pull_l I hZF target.omega hX target.transitive hm hn hj
  have seq := (sc_sequences_iff_l hZF target.omega hX target.transitive hm hn hj hωX theory target.theory).mpr target.sequences
  obtain ⟨L, hL, hs⟩ := seq.space μ hμ
  exact ⟨L, target.omega, hw, hX, hωX, hμ, sc_ordinal_small_l hZF target.omega hX hm theory hμ ho, hL, hs, ⟨c, hm⟩, theory,
    target.collection.pull_l hZF target.omega hX target.transitive hm hn hj, seq,
    (sc_collapse_iff_l hZF target.omega hX target.transitive hm hn hj).mpr target.collapse⟩

end YesMetaZFC.SetTheory.LargeCardinal
