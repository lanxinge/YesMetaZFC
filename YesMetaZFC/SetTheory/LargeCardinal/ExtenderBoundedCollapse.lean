import YesMetaZFC.SetTheory.LargeCardinal.ExtenderBoundedConst
import YesMetaZFC.SetTheory.LargeCardinal.ExtenderRankClosure
import YesMetaZFC.SetTheory.LargeCardinal.RelativeRankSegment
import YesMetaZFC.SetTheory.LargeCardinal.IterationStep
import YesMetaZFC.Model.SetTheory.Internal.SourcePresentation
import YesMetaZFC.SetTheory.Collapse.RelationMap

/-! # 有界超幂的实际像在所属源中计算

若支撑 L 的相对秩段带有源内 L 枚举，全部有限支撑的低秩函数代表都落在
该秩段中，因而节点集在源内为小。原极限的有界代表恰好满射到 j(B)，
源内小关系塌缩遂将同一个 j(B) 及代表求值图放回源中。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

/-- 节点、关系与求值图保持显式，并记录重复代表对成员关系的完整反映。 -/
def Eb_collapse_d (ω κ L K X B F A Q Y e : M.Domain) : Prop := ∃ J P G U R,
  Eb_pool_d ω κ L X B J K P G A ∧ (∀ a, M.mem a J ↔ Ei_d ω L a) ∧
    M.mem U X ∧ M.mem R X ∧ M.mem Q X ∧ M.mem e X ∧
    (∀ x, M.mem x U ↔ ∃ a, Rd_entry_d a x F) ∧
    Rd_fun_d .mem B B B R ∧
    (∀ p, M.mem p Q → ∃ u, M.mem u A ∧ ∃ v, M.mem v A ∧ KPair_d M p u v) ∧
    (∀ u v, Rd_entry_d u v Q ↔ M.mem u A ∧ M.mem v A ∧ Eb_link_d ω κ L B J K U R F G u v) ∧
    Wc_map_d A Q Y e ∧
    ∀ u v x y, Rd_entry_d u x e → Rd_entry_d v y e → (Rd_entry_d u v Q ↔ M.mem x y)

theorem Eb_pool_d.rank_small_l {ω κ K X R L B J P G A V : M.Domain}
    (source : Ep_source_d hZF ω κ K X R) (pool : Eb_pool_d ω κ L X B J K P G A)
    (hL : M.mem L X) (limit : M.IsLimitOrdinal L) (level : Er_level_d X L V)
    (hκ : M.mem κ V) (hB : M.mem B V) : Sc_small_d X A := by
  have hω := level.hierarchy.subset_mem_l source.transitive level.member hκ source.omega_mem source.below
  obtain ⟨c, S, code⟩ := smdl_membership_l I hZF ⟨ω, hω⟩
  have theory := source.rank_theory_l hZF level.member level.hierarchy limit code
  have trans := level.hierarchy.transitive_l hZF source.transitive level.member
  have hK := level.hierarchy.relations_mem_l source.transitive level.member limit hω hκ source.finite_mem
    (fun f hf p hp => by
      obtain ⟨n, hn, fn⟩ := (source.finite f).mp hf
      obtain ⟨i, hi, x, hx, pair⟩ := (fn0_of_function_l (ZF.modelsKP hZF) fn).1 p hp
      exact ⟨i, source.omega.transitive hZF n hn i hi, x, hx, pair⟩)
  have sub u (hu : M.mem u A) : M.mem u V := by
    obtain ⟨n, a, D, f, hn, _, ha, hd, hf, fn, pair⟩ := pool.read_l hZF source hu
    have haV := sc_finite_function_l hZF source.omega trans theory.algebra.pair theory.algebra.union hω
      (level.hierarchy.ordinal_subset_l hZF source.transitive level.member) hn ha
    have hfV := level.hierarchy.relation_mem_l hZF source.transitive level.member limit hK hB hf (fun p hp => by
      obtain ⟨s, hs, x, hx, pair⟩ := fn.1 p hp
      exact ⟨s, (source.finite s).mpr ⟨n, hn, fn0_function_l (ZF.modelsKP hZF) ((hd s).mp hs)⟩, x, hx, pair⟩)
    obtain ⟨v, hv, vp⟩ := theory.algebra.kpair_l haV hfV
    exact kpair_unique_l M hZF.1 vp pair ▸ hv
  obtain ⟨c₀, hm⟩ := source.code
  obtain ⟨_, f, _, hf, iso⟩ := level.code
  have small := sc_small_image_l hZF source.omega source.transitive hm source.theory hL level.member hf
    (sc_ordinal_small_l hZF source.omega source.transitive hm source.theory hL limit.1) iso.function iso.onto
  exact small.mono_l sub

/-- 源拥有扩展器及支撑秩段枚举时，低秩传递集合的超幂像仍属于该源。 -/
theorem it_ultra_owned_image_l {ω κ K L X R F c d j N S V B B' : M.Domain}
    (source : Ep_source_d hZF ω κ K X R) (power : Sc_power_d X) (family : Em_source_d ω κ L X F)
    (hm : Smem_d I c X R) (hn : Smem_d I d N S) (ultra : It_ultra_d hZF ω κ L F c d j)
    (hL : M.mem L X) (hF : M.mem F X) (hl : M.IsLimitOrdinal L) (level : Er_level_d X L V)
    (hκ : M.mem κ V) (hB : M.mem B V) (transitive : M.TransitiveSet B) (hBB : Rd_entry_d B B' j) :
    M.mem B' X ∧ ∃ A Q e, Eb_collapse_d ω κ L K X B F A Q B' e := by
  have hN := ultra.transitive_l hZF hn.1
  obtain ⟨X₀, R₀, N₀, S₀, J, O, Z, A, p, T, U, q, b, C, W, i, e,
    mx, nx, system, limit, _, wc, bij, _, hi, constants, hj, js⟩ := ultra
  obtain ⟨ex, er⟩ := smdl_unique_l I mx.1 hm.1
  obtain ⟨en, es⟩ := smdl_unique_l I nx.1 hn.1
  subst X₀ R₀ N₀ S₀
  have hBX := source.transitive V level.member B hB
  have tr := smap_delta_l I hZF source.omega source.transitive hN hm hn hj (n := 1)
    (Formula.isTransitive .newest) (by simp -implicitDefEqProofs) (Formula.isTransitive_delta0 _)
    ⟨fun _ => B, fun _ => B⟩ ⟨fun _ => B', fun _ => B'⟩ (fun _ => hBB)
  simp only [Formula.satisfies_isTransitive_iff] at tr
  let membership : BinarySchema 0 := { body := .mem (.bound 1) .newest }
  obtain ⟨R₁, hR₁, shape, rel⟩ := sc_relation_source_l hZF source.omega source.transitive hm source.theory membership (.mem ..)
    ⟨Fin.elim0, fun _ => B⟩ (fun i => Fin.elim0 i) hBX hBX
  have relation₀ x y : Rd_entry_d x y R₁ ↔ M.mem x B ∧ M.mem y B ∧ M.mem x y :=
    (rel x y).trans (and_congr_right fun _ => and_congr_right fun _ => Formula.satisfies_mem_iff ..)
  have membership₀ : Rd_fun_d .mem B B B R₁ := by
    intro p
    refine ⟨fun hp => ?_, ?_⟩
    · obtain ⟨x, y, pair⟩ := shape p hp
      obtain ⟨hx, hy, hxy⟩ := (relation₀ x y).mp ⟨p, pair, hp⟩
      exact ⟨x, y, hx, hy, hxy, pair⟩
    · rintro ⟨x, y, hx, hy, hxy, pair⟩
      obtain ⟨q, qp, hq⟩ := (relation₀ x y).mpr ⟨hx, hy, hxy⟩
      exact kpair_unique_l M hZF.1 qp pair ▸ hq
  have relation x y (hx : M.mem x B) (hy : M.mem y B) : Rd_entry_d x y R₁ ↔ Rd_entry_d x y R :=
    (relation₀ x y).trans
      ⟨fun h => (hm.2 x y).mpr ⟨source.transitive B hBX x h.1, source.transitive B hBX y h.2.1, h.2.2⟩,
        fun h => ⟨hx, hy, ((hm.2 x y).mp h).2.2⟩⟩
  obtain ⟨P, G, D, pool⟩ := eb_pool_l hZF source power hL hBX system.indices
  obtain ⟨U₀, Q, hU₀, hQ, range, graph, qs⟩ := pool.relation_l hZF source hL hBX hF hR₁
  obtain ⟨H, hBH, hHB⟩ := (js.2 B B').mp hBB
  obtain ⟨u, a, E, f, Q₀, _, sf, fc, hfE, pair, huH⟩ := constants B H hBH
  have fv : Ep_repr_d q a f H := ⟨u, E, pair, hfE, huH⟩
  obtain ⟨t, map, _, member⟩ := pool.evaluation_l hZF source family system limit hBX range relation qs
    wc bij (sf.function_l source.transitive) fc fv hHB (tr.mp transitive)
  obtain ⟨hB', ht⟩ := sc_presentation_l hZF source.omega source.transitive hm source.theory source.collapse
    pool.carrier hQ (pool.rank_small_l hZF source hL hl level hκ hB) graph map.transitive map.function map.onto member
  exact ⟨hB', D, Q, t, J, P, G, U₀, R₁, pool, system.indices, hU₀, hR₁, hQ, ht, range, membership₀,
    fun p hp => (graph.1 p hp).elim fun u hu => hu.elim fun v hv =>
      ⟨u, (graph.2 u v ⟨p, hv, hp⟩).1, v, (graph.2 u v ⟨p, hv, hp⟩).2, hv⟩,
    qs, map, member⟩

/-- 同一有界塌缩既恢复容器的像，也逐点恢复容器中每个集合的常值像。 -/
theorem Eb_collapse_d.image_l {ω κ K L X R F c d j N S B A Q Y e : M.Domain}
    (source : Ep_source_d hZF ω κ K X R) (family : Em_source_d ω κ L X F)
    (hm : Smem_d I c X R) (hn : Smem_d I d N S) (ultra : It_ultra_d hZF ω κ L F c d j)
    (hB : M.mem B X) (trans : M.TransitiveSet B) (collapse : Eb_collapse_d ω κ L K X B F A Q Y e) :
    Rd_entry_d B Y j ∧ ∀ x y, M.mem x B → (Eb_const_d X B A e x y ↔ Rd_entry_d x y j) := by
  have hN := ultra.transitive_l hZF hn.1
  obtain ⟨X₀, R₀, N₀, S₀, J, O, Z, D, p, T, U, q, b, C, W, i, g,
    mx, nx, system, limit, _, wc, bij, _, _, constants, hj, js⟩ := ultra
  obtain ⟨ex, er⟩ := smdl_unique_l I mx.1 hm.1
  obtain ⟨en, es⟩ := smdl_unique_l I nx.1 hn.1
  subst X₀ R₀ N₀ S₀
  obtain ⟨J₀, P, G, U₀, R₁, pool, indices, _, _, _, _, range, membership, _, edges, map, _⟩ := collapse
  have eq := hZF.1.eq_of_same_members J₀ J (fun a => (indices a).trans (system.indices a).symm)
  subst J₀
  obtain ⟨B', _, hBB⟩ := hj.1.1.2.2 B hB
  have tr := smap_delta_l I hZF source.omega source.transitive hN hm hn hj (n := 1)
    (Formula.isTransitive .newest) (by simp -implicitDefEqProofs) (Formula.isTransitive_delta0 _)
    ⟨fun _ => B, fun _ => B⟩ ⟨fun _ => B', fun _ => B'⟩ (fun _ => hBB)
  simp only [Formula.satisfies_isTransitive_iff] at tr
  have relation x y (hx : M.mem x B) (hy : M.mem y B) : Rd_entry_d x y R₁ ↔ Rd_entry_d x y R :=
    (rt_mem_graph_l (ZF.modelsKP hZF) membership x y).trans
      ⟨fun h => (hm.2 x y).mpr ⟨source.transitive B hB x hx, source.transitive B hB y hy, h.2.2⟩,
        fun h => ⟨hx, hy, ((hm.2 x y).mp h).2.2⟩⟩
  obtain ⟨H, hBH, hHB⟩ := (js.2 B B').mp hBB
  obtain ⟨u, a, E, f, D₀, _, sf, fc, hfE, pair, huH⟩ := constants B H hBH
  have fv : Ep_repr_d q a f H := ⟨u, E, pair, hfE, huH⟩
  obtain ⟨t, evaluation, values, _⟩ := pool.evaluation_l hZF source family system limit hB range relation edges wc bij
    (sf.function_l source.transitive) fc fv hHB (tr.mp trans)
  have values : ∀ u x, Rd_entry_d u x e ↔ M.mem u A ∧ ∃ E, Eb_value_d q u E ∧ Rd_entry_d E x g :=
    (map.graph_unique_l hZF evaluation).symm ▸ values
  refine ⟨(map.unique_l hZF evaluation).symm ▸ hBB, fun x y hx => ⟨?_, ?_⟩⟩
  · rintro ⟨u, _, a, _, f, _, D₁, _, pair, ff, constant, hux⟩
    obtain ⟨_, E, ⟨a', f', pair', ev⟩, hEy⟩ := (values u y).mp hux
    obtain ⟨rfl, rfl⟩ := kpair_injective_l M pair' pair
    obtain ⟨y', _, hxy⟩ := hj.1.1.2.2 x (source.transitive B hB x hx)
    obtain ⟨H', hxH, hHy⟩ := (js.2 x y').mp hxy
    obtain ⟨u', a', B₀, f', D₂, _, sf', constant', hfB, pair', huH'⟩ := constants x H' hxH
    have eq := ep_repr_constant_l hZF source family system limit
      (ff.mono_target_l (source.transitive B hB)) (sf'.function_l source.transitive)
      constant constant' ev ⟨u', B₀, pair', hfB, huH'⟩
    exact (bij.1.1.1.2 E y y' hEy (eq.symm ▸ hHy)).symm ▸ hxy
  · intro hxy
    obtain ⟨H', hxH, hHy⟩ := (js.2 x y).mp hxy
    obtain ⟨u', a', B₀, f', D₁, _, sf', constant, hfB, pair', huH'⟩ := constants x H' hxH
    have ev : Ep_repr_d q a' f' H' := ⟨u', B₀, pair', hfB, huH'⟩
    obtain ⟨hfX, n, hnω, ha, D₂, space, ff⟩ := ev.source_l hZF family system limit
    have eq := ff.domain_eq_l hZF.1 (sf'.function_l source.transitive)
    subst D₂
    have fb : Fn0_d D₁ B f' := ff.retarget_l fun i z hiz =>
      (fn0_function_l (ZF.modelsKP hZF) ff).1.2 i z x hiz (constant i (ff.bound_l hiz).1) ▸ hx
    obtain ⟨v, pair⟩ := (I).total a' f'
    have haJ := ev.index_l hZF system limit
    have hv := pool.node_l hZF source hnω haJ ha space hfX fb pair
    exact ⟨v, hv, a', source.transitive J pool.indices a' haJ, f', hfX, D₁,
      source.space_mem_l hZF hnω space, pair, fb, constant, (values v y).mpr ⟨hv, H', ⟨a', f', pair, ev⟩, hHy⟩⟩

end YesMetaZFC.SetTheory.LargeCardinal
