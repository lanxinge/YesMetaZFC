import YesMetaZFC.SetTheory.LargeCardinal.ExtenderBoundedCollapse

/-! # 同一有界超幂在严格秩截断中的保持

有界函数池、节点和关系先由秩闭包回收。支撑层的实际枚举证明节点集小，
截断源的小关系塌缩遂回收原来的传递像及求值图；不预设它们已经属于截断。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)
include hZF

theorem Eb_pool_d.rank_l {ω κ K X α V L B J P G A : M.Domain}
    (hω : M.IsOmega ω) (hX : M.TransitiveSet X) (hV : M.mem V X) (rank : Vr_d X α V)
    (hα : M.IsLimitOrdinal α) (hw : M.mem ω V) (hK : M.mem K V) (hL : M.mem L V) (hB : M.mem B V)
    (indices : ∀ a, M.mem a J ↔ Ei_d ω L a) (pool : Eb_pool_d ω κ L X B J K P G A) :
    Eb_pool_d ω κ L V B J K P G A := by
  have ht := rank.transitive_l hZF hX hV
  have hJ := rank.relations_mem_l hX hV hα hw hL pool.indices (fun a ha p hp => by
    obtain ⟨n, hn, fn, _⟩ := (indices a).mp ha
    obtain ⟨i, hi, x, hx, pair⟩ := fn.1 p hp
    exact ⟨i, hω.transitive hZF n hn i hi, x, hx, pair⟩)
  have hP := rank.subsets_mem_l hX hV hα hK pool.powers
    (fun x hx => ((pool.subsets x).mp hx).2)
  have hG := rank.relations_mem_l hX hV hα hK hB pool.functions
    (fun f hf => ((pool.graphs f).mp hf).2)
  have hA := rank.relation_mem_l hZF hX hV hα hJ hG pool.carrier (fun u hu => by
    obtain ⟨a, ha, f, hf, pair, _⟩ := (pool.nodes u).mp hu
    exact ⟨a, ha, f, hf, pair⟩)
  exact ⟨hJ, hP, hG, hA, fun x =>
    ⟨fun hx => ⟨ht P hP x hx, ((pool.subsets x).mp hx).2⟩,
      fun ⟨hx, sub⟩ => (pool.subsets x).mpr ⟨hX V hV x hx, sub⟩⟩,
    fun f => ⟨fun hf => ⟨ht G hG f hf, ((pool.graphs f).mp hf).2⟩,
      fun ⟨hf, bound⟩ => (pool.graphs f).mpr ⟨hX V hV f hf, bound⟩⟩, pool.nodes⟩

/-- 截断保留全部原节点、原关系、同一个传递像及原求值图。 -/
theorem Eb_collapse_d.rank_l {ω κ K X α V R L B A Q Y e F W : M.Domain}
    (source : Ep_source_d hZF ω κ K V R) (hX : M.TransitiveSet X) (hV : M.mem V X)
    (rank : Vr_d X α V) (hα : M.IsLimitOrdinal α) (hL : M.mem L V) (hF : M.mem F V)
    (limit : M.IsLimitOrdinal L) (level : Er_level_d V L W) (hκ : M.mem κ W) (hB : M.mem B W)
    (collapse : Eb_collapse_d ω κ L K X B F A Q Y e) :
    M.mem Y V ∧ Eb_collapse_d ω κ L K V B F A Q Y e := by
  obtain ⟨J, P, G, U, T, pool, indices, _, hT, hQ, _, range, membership, shape, edges, wc, member⟩ := collapse
  have hBV := source.transitive W level.member B hB
  have pool' := pool.rank_l hZF source.omega hX hV rank hα source.omega_mem source.finite_mem hL hBV indices
  have hTV := rank.relation_mem_l hZF hX hV hα hBV hBV hT (fun p hp => by
    obtain ⟨x, y, hx, hy, _, pair⟩ := (membership p).mp hp
    exact ⟨x, hx, y, hy, pair⟩)
  have hQV := rank.relation_mem_l hZF hX hV hα pool'.carrier pool'.carrier hQ shape
  obtain ⟨c, hm⟩ := source.code
  obtain ⟨U', hU', range'⟩ := sc_range_source_l hZF source.omega source.transitive hm source.theory hF
  have eq := hZF.1.eq_of_same_members U' U (fun x => (range' x).trans (range x).symm)
  have hUV : M.mem U V := eq ▸ hU'
  have relation : M.IsSetRelationOn I Q A := by
    refine ⟨fun p hp => ?_, fun u v h => ⟨((edges u v).mp h).1, ((edges u v).mp h).2.1⟩⟩
    obtain ⟨u, _, v, _, pair⟩ := shape p hp
    exact ⟨u, v, pair⟩
  -- 用原求值图的完整关系反映在截断中塌缩，唯一性给出原像的所属判断。
  obtain ⟨hY, he⟩ := sc_presentation_l hZF source.omega source.transitive hm source.theory source.collapse
    pool'.carrier hQV (pool'.rank_small_l hZF source hL limit level hκ hB)
    relation wc.transitive wc.function wc.onto member
  exact ⟨hY, J, P, G, U, T, pool', indices, hUV, hTV, hQV, he, range, membership, shape, edges, wc, member⟩

/-- 原坐标界属于截断时，大源没有额外的有界代表或有限幂子集。 -/
theorem Eb_pool_d.of_rank_l {ω κ K X α V L B J P G A : M.Domain}
    (hX : M.TransitiveSet X) (hV : M.mem V X) (rank : Vr_d X α V) (hα : M.IsLimitOrdinal α)
    (hK : M.mem K V) (hB : M.mem B V) (pool : Eb_pool_d ω κ L V B J K P G A) :
    Eb_pool_d ω κ L X B J K P G A := by
  have inside := hX V hV
  refine ⟨inside J pool.indices, inside P pool.powers, inside G pool.functions, inside A pool.carrier,
    fun x => ?_, fun f => ?_, pool.nodes⟩
  · exact ⟨fun hx => ⟨inside x ((pool.subsets x).mp hx).1, ((pool.subsets x).mp hx).2⟩,
      fun ⟨hx, sub⟩ => (pool.subsets x).mpr ⟨rank.subset_mem_l hX hV hK hx sub, sub⟩⟩
  · exact ⟨fun hf => ⟨inside f ((pool.graphs f).mp hf).1, ((pool.graphs f).mp hf).2⟩,
      fun ⟨hf, bound⟩ => (pool.graphs f).mpr ⟨rank.relation_mem_l hZF hX hV hα hK hB hf bound, bound⟩⟩

/-- 同一个有界呈示及塌缩在大源中保持；无需再次构造商或选择新的求值图。 -/
theorem Eb_collapse_d.of_rank_l {ω κ K X α V L B A Q Y e F : M.Domain}
    (hX : M.TransitiveSet X) (hV : M.mem V X) (rank : Vr_d X α V) (hα : M.IsLimitOrdinal α)
    (hK : M.mem K V) (hB : M.mem B V) (collapse : Eb_collapse_d ω κ L K V B F A Q Y e) :
    Eb_collapse_d ω κ L K X B F A Q Y e := by
  obtain ⟨J, P, G, U, R, pool, indices, hU, hR, hQ, he, rest⟩ := collapse
  exact ⟨J, P, G, U, R, pool.of_rank_l hZF hX hV rank hα hK hB, indices,
    hX V hV U hU, hX V hV R hR, hX V hV Q hQ, hX V hV e he, rest⟩

end YesMetaZFC.SetTheory.LargeCardinal
