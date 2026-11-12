import YesMetaZFC.SetTheory.LargeCardinal.Extender.BoundedGraph
import YesMetaZFC.SetTheory.LargeCardinal.Extender.UltraCertificate
import YesMetaZFC.SetTheory.Collapse.RelationMap
import YesMetaZFC.SetTheory.Notation
import YesMetaZFC.SetTheory.LargeCardinal.Extender.RawCoherence
import YesMetaZFC.SetTheory.LargeCardinal.Cardinals.RelativeRankSegment
import YesMetaZFC.SetTheory.LargeCardinal.Iteration.Step
import YesMetaZFC.Model.SetTheory.Source.Presentation
import YesMetaZFC.Model.SetTheory.Relations.CollectCode
import YesMetaZFC.Model.SetTheory.Relations.RankImage

/-! # 有界节点在指定实际超幂中的求值

原商投影与传递坍缩复合，覆盖常值像中的全部成员。该图既满足塌缩递归，
又逐对精确读取节点关系，因此可用于源内呈示和既有求值证书的唯一性比较。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Eb_pool_d.evaluation_l {ω κ K X R L F J O Z A p T S q C W B R' P G D U Q N g D₀ a₀ f₀ H B' : M.Domain}
    (source : Ep_source_d (kp_pair_l (ZF.modelsKP hZF)) ω κ K X R) (family : Em_source_d ω κ L X F)
    (system : Ep_system_d I ω κ L X R F J O Z A p T S) (limit : Di_limit_d A p T S q C W)
    (pool : Eb_pool_d ω κ L X B J K P G D) (hB : M.mem B X) (range : M.IsRangeOf I U F)
    (relation : ∀ x y, M.mem x B → M.mem y B → (Rd_entry_d x y R' ↔ Rd_entry_d x y R))
    (edges : ∀ u v, Rd_entry_d u v Q ↔ M.mem u D ∧ M.mem v D ∧ Eb_link_d ω κ L B J K U R' F G u v)
    (wc : Wc_graph_d C W g) (bij : M.IsSetBijectionFromTo I g C N)
    (ff : Fn0_d D₀ X f₀) (constant : Rs_const_d D₀ B f₀) (fv : Ep_repr_d q a₀ f₀ H)
    (hHB : Rd_entry_d H B' g) (trans : M.TransitiveSet B') : ∃ t, Wc_map_d D Q B' t ∧
      (∀ u x, Rd_entry_d u x t ↔ M.mem u D ∧ ∃ E, Eb_value_d q u E ∧ Rd_entry_d E x g) ∧
      ∀ u v x y, Rd_entry_d u x t → Rd_entry_d v y t → (Rd_entry_d u v Q ↔ M.mem x y) := by
  obtain ⟨v, vf, values, reads, covers⟩ := pool.projection_l hZF source family system limit
    (source.transitive B hB) range relation edges
  obtain ⟨t, tf, ts⟩ := ZF.exists_compositionFunction hZF I (fn0_function_l (ZF.modelsKP hZF) vf) bij.1.1
  obtain ⟨_, n, hn, ha, D₁, hd, ff'⟩ := fv.source_l hZF family system limit
  have eq := ff'.domain_eq_l hZF.1 ff
  subst D₁
  have into u x (hux : Rd_entry_d u x t) : M.mem x B' := by
    obtain ⟨hu, E, huE, hEx⟩ := (ts u x).mp hux
    obtain ⟨m, a, D', f, hm, _, hma, space, _, fn, pair⟩ := pool.read_l (ZF.modelsKP hZF) (source.finite_l (ZF.modelsKP hZF)) hu
    obtain ⟨_, a', f', pair', ev⟩ := (values u E).mp huE
    obtain ⟨rfl, rfl⟩ := kpair_injective_l M pair pair'
    exact (wc.member_l (fn0_of_function_l (ZF.modelsKP hZF) bij.1.1) bij.1.2 hEx hHB).mp
      (ep_repr_bound_mem_l hZF source family system limit ff constant fv hB hm hma space fn ev)
  have onto x (hx : M.mem x B') : ∃ u, M.mem u D ∧ Rd_entry_d u x t := by
    obtain ⟨E, _, edge, hEx⟩ := ((wc.2 H B' hHB).2.2 x).mp hx
    obtain ⟨m, a, D', f, hm, haJ, hma, space, hf, fn, ev⟩ :=
      ep_repr_bounded_l hZF source family system limit hn ha hd ff constant fv hB edge
    obtain ⟨u, hu, huE⟩ := covers m a D' f E hm haJ hma space hf fn ev
    exact ⟨u, hu, (ts u x).mpr ⟨hu, E, huE, hEx⟩⟩
  have member u v x y (hx : Rd_entry_d u x t) (hy : Rd_entry_d v y t) : Rd_entry_d u v Q ↔ M.mem x y := by
    obtain ⟨_, E, huE, hEx⟩ := (ts u x).mp hx
    obtain ⟨_, H', hvH, hHy⟩ := (ts v y).mp hy
    exact (reads u v E H' huE hvH).trans
      (wc.member_l (fn0_of_function_l (ZF.modelsKP hZF) bij.1.1) bij.1.2 hEx hHy)
  refine ⟨t, ⟨trans, (fn0_of_function_l (ZF.modelsKP hZF) tf).retarget_l into, onto, ?_⟩, ?_, member⟩
  · intro u _ x _ hux y hy
    exact ⟨fun hyx => (onto y hy).elim fun v hv => ⟨v, hv.1, (member v u y x hv.2 hux).mpr hyx, hv.2⟩,
      fun ⟨v, _, hvu, hvy⟩ => (member v u y x hvy hux).mp hvu⟩
  · intro u x
    exact (ts u x).trans ⟨fun ⟨hu, E, huE, hEx⟩ => ⟨hu, E, ((values u E).mp huE).2, hEx⟩,
      fun ⟨hu, E, value, hEx⟩ => ⟨hu, E, (values u E).mpr ⟨hu, value⟩, hEx⟩⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 有界节点中的常值代表

常值测试只量化所属源内的支撑、定义域和函数，以及已有节点和求值图。
它是原 Δ₀ 公式；任意传递外层都可准确读取这些有限数据。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

def Eb_const_d (X B A e x y : M.Domain) : Prop := ∃ u, M.mem u A ∧
  ∃ a, M.mem a X ∧ ∃ f, M.mem f X ∧ ∃ D, M.mem D X ∧
    KPair_d M u a f ∧ Fn0_d D B f ∧ Rs_const_d D x f ∧ Rd_entry_d u y e

def eb_const_m {d} (X B A e x y : Term d) : Formula 1 d := set[d] ⟪
  ∃ u ∈ ⌜A⌝ₛ, ∃ a ∈ ⌜X⌝ₛ, ∃ f ∈ ⌜X⌝ₛ, ∃ D ∈ ⌜X⌝ₛ,
    ⌜kpair0_m⌝ₚ(u, a, f) ∧ ⌜fn0_m⌝ₚ(D, ⌜B⌝ₛ, f) ∧
    ⌜rs_const_m⌝ₚ(D, ⌜x⌝ₛ, f) ∧ ⌜rd_entry0_m⌝ₚ(u, ⌜y⌝ₛ, ⌜e⌝ₛ)⟫
derive_free_closed eb_const_m

theorem eb_const_delta_l {d} (X B A e x y : Term d) : (eb_const_m X B A e x y).IsDelta0 :=
  .existsMem _ (.existsMem _ (.existsMem _ (.existsMem _ (.conj (kpair0_delta_l ..)
    (.conj (fn0_delta_l ..) (.conj (.forallMem _ (rd_entry0_delta_l ..)) (rd_entry0_delta_l ..)))))))

theorem eb_const_sat_l (hE : Extensional M) {d} (ρ : Env M d) (X B A e x y : Term d) :
    Formula.satisfies ρ (eb_const_m X B A e x y) ↔
      Eb_const_d (X.eval ρ) (B.eval ρ) (A.eval ρ) (e.eval ρ) (x.eval ρ) (y.eval ρ) := by
  simp only [eb_const_m, Eb_const_d, Formula.satisfies_existsMem_iff, Formula.satisfies_conj_iff,
    kpair0_sat_l hE, fn0_sat_l hE, rs_const_sat_l hE, rd_entry0_sat_l hE, Definitional.Term.eval_weaken]
  rfl

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 有界超幂的实际像在所属源中计算

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

include hZF in
/-- 同一有界代表池的节点、关系及完整塌缩唯一，反复读取证书不会改变求值图。 -/
theorem Eb_collapse_d.unique_l {ω κ L K X B F A Q Y e A' Q' Y' e' : M.Domain}
    (h : Eb_collapse_d ω κ L K X B F A Q Y e)
    (g : Eb_collapse_d ω κ L K X B F A' Q' Y' e') :
    A = A' ∧ Q = Q' ∧ Y = Y' ∧ e = e' := by
  obtain ⟨J, P, G, U, R, pool, indices, _, _, _, _, range, membership, shape, edges, collapse, _⟩ := h
  obtain ⟨J', P', G', U', R', pool', indices', _, _, _, _, range', membership', shape', edges', collapse', _⟩ := g
  have eqJ := hZF.1.eq_of_same_members J J' (fun a => (indices a).trans (indices' a).symm)
  have eqP := hZF.1.eq_of_same_members P P' (fun a => (pool.subsets a).trans (pool'.subsets a).symm)
  have eqG := hZF.1.eq_of_same_members G G' (fun a => (pool.graphs a).trans (pool'.graphs a).symm)
  have eqU := hZF.1.eq_of_same_members U U' (fun a => (range a).trans (range' a).symm)
  have eqR := hZF.1.eq_of_same_members R R' (fun a => (membership a).trans (membership' a).symm)
  subst J' P' G' U' R'
  have eqA := hZF.1.eq_of_same_members A A' (fun a => (pool.nodes a).trans (pool'.nodes a).symm)
  subst A'
  have relation : M.IsSetRelation I Q := fun p hp =>
    (shape p hp).elim fun u hu => hu.2.elim fun v hv => ⟨u, v, hv.2⟩
  have relation' : M.IsSetRelation I Q' := fun p hp =>
    (shape' p hp).elim fun u hu => hu.2.elim fun v hv => ⟨u, v, hv.2⟩
  have eqQ := relation.eq_of_pairMember_iff hZF.1 relation' (fun u v => (edges u v).trans (edges' u v).symm)
  subst Q'
  exact ⟨rfl, rfl, collapse.unique_l hZF collapse', collapse.graph_unique_l hZF collapse'⟩

theorem Eb_pool_d.rank_small_l {ω κ K X R L B J P G A V : M.Domain}
    (source : Ep_source_d (kp_pair_l (ZF.modelsKP hZF)) ω κ K X R) (pool : Eb_pool_d ω κ L X B J K P G A)
    (hL : M.mem L X) (limit : M.IsLimitOrdinal L) (level : Er_level_d X L V)
    (hκ : M.mem κ V) (hB : M.mem B V) : Sc_small_d X A := by
  have hω := level.hierarchy.subset_mem_l source.transitive level.member hκ source.omega_mem source.below
  obtain ⟨c, S, code⟩ := smdl_membership_l I hZF ⟨ω, hω⟩
  have theory := source.rank_theory_l hZF level.member level.hierarchy limit code
  have trans := level.hierarchy.transitive_l source.transitive level.member
  have hK := level.hierarchy.relations_mem_l source.transitive level.member limit hω hκ source.finite.mem_l
    (fun f hf p hp => by
      obtain ⟨n, hn, fn⟩ := ((source.finite_l (ZF.modelsKP hZF)) f).mp hf
      obtain ⟨i, hi, x, hx, pair⟩ := (fn0_of_function_l (ZF.modelsKP hZF) fn).1 p hp
      exact ⟨i, source.omega.transitive (ZF.modelsKP hZF) n hn i hi, x, hx, pair⟩)
  have sub u (hu : M.mem u A) : M.mem u V := by
    obtain ⟨n, a, D, f, hn, _, ha, hd, hf, fn, pair⟩ := pool.read_l (ZF.modelsKP hZF) (source.finite_l (ZF.modelsKP hZF)) hu
    have haV := sc_finite_function_l (ZF.modelsKP hZF) source.omega trans (theory.algebra_l _ (ZF.modelsKP hZF) trans code).pair (theory.algebra_l _ (ZF.modelsKP hZF) trans code).union hω
      (level.hierarchy.ordinal_subset_l hZF source.transitive level.member) hn ha
    have hfV := level.hierarchy.relation_mem_l source.transitive level.member limit hK hB hf (fun p hp => by
      obtain ⟨s, hs, x, hx, pair⟩ := fn.1 p hp
      exact ⟨s, ((source.finite_l (ZF.modelsKP hZF)) s).mpr ⟨n, hn, fn0_function_l (ZF.modelsKP hZF) ((hd s).mp hs)⟩, x, hx, pair⟩)
    obtain ⟨v, hv, vp⟩ := (theory.algebra_l _ (ZF.modelsKP hZF) trans code).kpair_l haV hfV
    exact kpair_unique_l M hZF.1 vp pair ▸ hv
  obtain ⟨c₀, hm⟩ := source.code
  obtain ⟨_, f, _, hf, iso⟩ := level.code
  have small := sc_small_image_l hZF source.omega source.transitive hm source.theory hL level.member hf
    ((rf_small_mem_l I (ZF.modelsKP hZF) source.transitive hm hL).mp (sc_ordinal_small_l hZF source.omega source.transitive hm source.theory hL limit.1)) iso.function iso.onto
  exact small.mono_l sub

/-- 源拥有扩展器及支撑秩段枚举时，低秩传递集合的超幂像仍属于该源。 -/
theorem it_ultra_owned_image_l {ω κ K L X R F c d j N S V B B' : M.Domain}
    (source : Ep_source_d (kp_pair_l (ZF.modelsKP hZF)) ω κ K X R) (power : Sc_power_d X) (family : Em_source_d ω κ L X F)
    (hm : Smem_d I c X R) (hn : Smem_d I d N S) (ultra : It_ultra_d (kp_pair_l (ZF.modelsKP hZF)) ω κ L F c d j)
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
    (source : Ep_source_d (kp_pair_l (ZF.modelsKP hZF)) ω κ K X R) (family : Em_source_d ω κ L X F)
    (hm : Smem_d I c X R) (hn : Smem_d I d N S) (ultra : It_ultra_d (kp_pair_l (ZF.modelsKP hZF)) ω κ L F c d j)
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
    have hv := pool.node_l (ZF.modelsKP hZF) (source.finite_l (ZF.modelsKP hZF)) hnω haJ ha space (source.space_mem_l hZF hnω space) hfX fb pair
    exact ⟨v, hv, a', source.transitive J pool.indices a' haJ, f', hfX, D₁,
      source.space_mem_l hZF hnω space, pair, fb, constant, (values v y).mpr ⟨hv, H', ⟨a', f', pair, ev⟩, hHy⟩⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 有界超幂池的精确有界编码

节点的反向完备性直接量化支撑和代表，再要求原节点集中的实际有序对。
因此原池的全部条款都有 Δ₀ 编码，不缩小代表或节点的数学范围。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

def eb_pool_m {d} (ω κ L X B J K P G A : Term d) : Formula 1 d := set[d] ⟪
  ⌜J⌝ₛ ∈ ⌜X⌝ₛ ∧ ⌜P⌝ₛ ∈ ⌜X⌝ₛ ∧ ⌜G⌝ₛ ∈ ⌜X⌝ₛ ∧ ⌜A⌝ₛ ∈ ⌜X⌝ₛ ∧
  ⌜FilterZF.source_m⌝ₚ(⌜X⌝ₛ, ⌜K⌝ₛ, ⌜P⌝ₛ) ∧ ⌜G⌝ₛ ⊆ ⌜X⌝ₛ ∧
  (∀ f ∈ ⌜X⌝ₛ, f ∈ ⌜G⌝ₛ ↔ ∀ p ∈ f, ∃ s ∈ ⌜K⌝ₛ, ∃ x ∈ ⌜B⌝ₛ, ⌜kpair0_m⌝ₚ(p, s, x)) ∧
  (∀ u ∈ ⌜A⌝ₛ, ⌜eb_node_m⌝ₚ(⌜ω⌝ₛ, ⌜κ⌝ₛ, ⌜L⌝ₛ, ⌜K⌝ₛ, ⌜B⌝ₛ, ⌜J⌝ₛ, ⌜G⌝ₛ, ⌜P⌝ₛ, u)) ∧
  (∀ a ∈ ⌜J⌝ₛ, ∀ f ∈ ⌜G⌝ₛ, ∀ n ∈ ⌜ω⌝ₛ, ∀ D ∈ ⌜P⌝ₛ,
    ⌜fn0_m⌝ₚ(n, ⌜L⌝ₛ, a) ∧ ⌜eb_space_m⌝ₚ(⌜κ⌝ₛ, ⌜K⌝ₛ, n, D) ∧ ⌜fn0_m⌝ₚ(D, ⌜B⌝ₛ, f) →
      ∃ u ∈ ⌜A⌝ₛ, ⌜kpair0_m⌝ₚ(u, a, f))⟫
derive_free_closed eb_pool_m

theorem eb_pool_delta_l {d} (ω κ L X B J K P G A : Term d) : (eb_pool_m ω κ L X B J K P G A).IsDelta0 := by
  unfold eb_pool_m
  repeat first
    | exact FilterZF.source_delta_l .. | exact eb_node_delta_l .. | exact eb_space_delta_l ..
    | exact fn0_delta_l .. | exact kpair0_delta_l .. | exact .mem .. | exact .atom ..
    | apply Formula.IsDelta0.conj | apply Formula.IsDelta0.forallMem
    | apply Formula.IsDelta0.existsMem | apply Formula.IsDelta0.iff
    | apply Formula.IsDelta0.imp

theorem eb_pool_sat_l (hKP : M.Models KP) {d} (ρ : Env M d) (ω κ L X B J K P G A : Term d) :
    Formula.satisfies ρ (eb_pool_m ω κ L X B J K P G A) ↔
      Eb_pool_d (ω.eval ρ) (κ.eval ρ) (L.eval ρ) (X.eval ρ) (B.eval ρ) (J.eval ρ) (K.eval ρ) (P.eval ρ) (G.eval ρ) (A.eval ρ) := by
  simp only [eb_pool_m, Formula.satisfies_conj_iff, Formula.satisfies_mem_iff, FilterZF.source_sat_l,
    Formula.satisfies_subset_iff, Formula.satisfies_forallMem_iff, Formula.satisfies_iff_iff,
    Formula.satisfies_existsMem_iff, Formula.satisfies_imp_iff, kpair0_sat_l hKP.1,
    eb_node_sat_l hKP.1, fn0_sat_l hKP.1, eb_space_sat_l hKP.1, Definitional.Term.eval_weaken]
  constructor
  · rintro ⟨hj, hp, hg, ha, subsets, sub, graphs, nodes, total⟩
    refine ⟨hj, hp, hg, ha, subsets, fun f => ⟨fun hf => ⟨sub f hf, (graphs f (sub f hf)).mp hf⟩,
      fun ⟨hf, hs⟩ => (graphs f hf).mpr hs⟩, fun u => ⟨nodes u, ?_⟩⟩
    rintro ⟨a, ha, f, hf, pair, n, hn, D, hd, fn, space, gf⟩
    obtain ⟨v, hv, code⟩ := total a ha f hf n hn D hd ⟨fn, space, gf⟩
    exact kpair_unique_l M hKP.1 code pair ▸ hv
  · intro h
    refine ⟨h.indices, h.powers, h.functions, h.carrier, h.subsets, fun f hf => ((h.graphs f).mp hf).1,
      fun f hf => (h.graphs f).trans (and_iff_right hf), fun u hu => (h.nodes u).mp hu, ?_⟩
    intro a ha f hf n hn D hd spec
    obtain ⟨u, pair⟩ := (kp_pair_l hKP).total a f
    exact ⟨u, (h.nodes u).mpr ⟨a, ha, f, hf, pair, n, hn, D, hd, spec⟩, pair⟩

def ep_indices0_m {d} (ω L H J : Term d) : Formula 1 d := .conj (Formula.subset J H)
  (Formula.forallMem H (.iff (.mem .newest J.weaken) (ei_m ω.weaken L.weaken .newest)))
derive_free_closed ep_indices0_m

theorem ep_indices0_delta_l {d} (ω L H J : Term d) : (ep_indices0_m ω L H J).IsDelta0 :=
  .conj (.atom ..) (.forallMem _ (.iff (.mem ..) (ei_delta_l ..)))

theorem ep_indices0_sat_l (hKP : M.Models KP) {d} (ρ : Env M d) (ω L H J : Term d)
    (seq : Fseq_space_d (kp_pair_l hKP) (ω.eval ρ) (L.eval ρ) (H.eval ρ)) :
    Formula.satisfies ρ (ep_indices0_m ω L H J) ↔ ∀ a, M.mem a (J.eval ρ) ↔ Ei_d (ω.eval ρ) (L.eval ρ) a := by
  have mem a (h : Ei_d (ω.eval ρ) (L.eval ρ) a) : M.mem a (H.eval ρ) := by
    obtain ⟨n, hn, fn, _⟩ := h
    exact (seq a).mpr ⟨n, hn, fn0_function_l hKP fn⟩
  simp only [ep_indices0_m, Formula.satisfies_conj_iff, Formula.satisfies_subset_iff,
    Formula.satisfies_forallMem_iff, Formula.satisfies_iff_iff, Formula.satisfies_mem_iff,
    ei_sat_l hKP.1, Definitional.Term.eval_weaken]
  exact ⟨fun ⟨sub, h⟩ a => ⟨fun ha => (h a (sub a ha)).mp ha, fun ha => (h a (mem a ha)).mpr ha⟩,
    fun h => ⟨fun a ha => mem a ((h a).mp ha), fun a _ => h a⟩⟩

def eb_collapse_m {d} (ω κ L K X B F A Q Y e H : Term d) : Formula 1 d := set[d] ⟪
  ∃ J ∈ ⌜X⌝ₛ, ∃ P ∈ ⌜X⌝ₛ, ∃ G ∈ ⌜X⌝ₛ, ∃ U ∈ ⌜X⌝ₛ, ∃ R ∈ ⌜X⌝ₛ,
    ⌜eb_pool_m⌝ₚ(⌜ω⌝ₛ, ⌜κ⌝ₛ, ⌜L⌝ₛ, ⌜X⌝ₛ, ⌜B⌝ₛ, J, ⌜K⌝ₛ, P, G, ⌜A⌝ₛ) ∧
    ⌜ep_indices0_m⌝ₚ(⌜ω⌝ₛ, ⌜L⌝ₛ, ⌜H⌝ₛ, J) ∧ ⌜Q⌝ₛ ∈ ⌜X⌝ₛ ∧ ⌜e⌝ₛ ∈ ⌜X⌝ₛ ∧
    ⌜rd_graph_m .range⌝ₚ(⌜F⌝ₛ, ⌜F⌝ₛ, ⌜F⌝ₛ, U) ∧ ⌜rd_graph_m .mem⌝ₚ(⌜B⌝ₛ, ⌜B⌝ₛ, ⌜B⌝ₛ, R) ∧
    (∀ p ∈ ⌜Q⌝ₛ, ∃ u ∈ ⌜A⌝ₛ, ∃ v ∈ ⌜A⌝ₛ, ⌜kpair0_m⌝ₚ(p, u, v)) ∧
    (∀ u ∈ ⌜A⌝ₛ, ∀ v ∈ ⌜A⌝ₛ, ⌜rd_entry0_m⌝ₚ(u, v, ⌜Q⌝ₛ) ↔
      ⌜eb_link_m⌝ₚ(⌜ω⌝ₛ, ⌜κ⌝ₛ, ⌜L⌝ₛ, ⌜B⌝ₛ, J, ⌜K⌝ₛ, U, R, ⌜F⌝ₛ, G, u, v)) ∧
    ⌜wc_map_m⌝ₚ(⌜A⌝ₛ, ⌜Q⌝ₛ, ⌜Y⌝ₛ, ⌜e⌝ₛ) ∧
    (∀ u ∈ ⌜A⌝ₛ, ∀ v ∈ ⌜A⌝ₛ, ∀ x ∈ ⌜Y⌝ₛ, ∀ y ∈ ⌜Y⌝ₛ,
      ⌜rd_entry0_m⌝ₚ(u, x, ⌜e⌝ₛ) → ⌜rd_entry0_m⌝ₚ(v, y, ⌜e⌝ₛ) → (⌜rd_entry0_m⌝ₚ(u, v, ⌜Q⌝ₛ) ↔ x ∈ y))⟫
derive_free_closed eb_collapse_m

theorem eb_collapse_delta_l {d} (ω κ L K X B F A Q Y e H : Term d) :
    (eb_collapse_m ω κ L K X B F A Q Y e H).IsDelta0 := by
  unfold eb_collapse_m
  repeat first
    | exact eb_pool_delta_l .. | exact ep_indices0_delta_l .. | exact rd_graph_delta_l ..
    | exact eb_link_delta_l .. | exact wc_map_delta_l .. | exact rd_entry0_delta_l ..
    | exact kpair0_delta_l .. | exact .mem ..
    | apply Formula.IsDelta0.conj | apply Formula.IsDelta0.forallMem
    | apply Formula.IsDelta0.existsMem | apply Formula.IsDelta0.iff
    | apply Formula.IsDelta0.imp

theorem eb_collapse_sat_l (hKP : M.Models KP) {d} (ρ : Env M d) (ω κ L K X B F A Q Y e H : Term d)
    (seq : Fseq_space_d (kp_pair_l hKP) (ω.eval ρ) (L.eval ρ) (H.eval ρ)) :
    Formula.satisfies ρ (eb_collapse_m ω κ L K X B F A Q Y e H) ↔
      Eb_collapse_d (ω.eval ρ) (κ.eval ρ) (L.eval ρ) (K.eval ρ) (X.eval ρ) (B.eval ρ) (F.eval ρ)
        (A.eval ρ) (Q.eval ρ) (Y.eval ρ) (e.eval ρ) := by
  have indices (J P G U R : M.Domain) :
      Formula.satisfies (((((ρ.push J).push P).push G).push U).push R)
        (ep_indices0_m ω.weaken.weaken.weaken.weaken.weaken L.weaken.weaken.weaken.weaken.weaken
          H.weaken.weaken.weaken.weaken.weaken Term.newest.weaken.weaken.weaken.weaken) ↔
        ∀ a, M.mem a J ↔ Ei_d (ω.eval ρ) (L.eval ρ) a := by
    simpa only [Definitional.Term.eval_weaken, Definitional.Term.eval_newest] using
      (ep_indices0_sat_l hKP (((((ρ.push J).push P).push G).push U).push R)
        ω.weaken.weaken.weaken.weaken.weaken L.weaken.weaken.weaken.weaken.weaken
        H.weaken.weaken.weaken.weaken.weaken Term.newest.weaken.weaken.weaken.weaken
        (by simpa only [Definitional.Term.eval_weaken] using seq))
  simp only [eb_collapse_m, Formula.satisfies_existsMem_iff, Formula.satisfies_conj_iff,
    eb_pool_sat_l hKP, indices, Formula.satisfies_mem_iff,
    rd_graph_sat_l hKP, Formula.satisfies_forallMem_iff, kpair0_sat_l hKP.1,
    Formula.satisfies_iff_iff, rd_entry0_sat_l hKP.1, eb_link_sat_l hKP.1, wc_map_sat_l hKP.1,
    Formula.satisfies_imp_iff, Definitional.Term.eval_weaken]
  constructor
  · rintro ⟨J, _, P, _, G, _, U, hU, R, hR, pool, indices, hQ, he, range, rel, shape, edges, wc, member⟩
    refine ⟨J, P, G, U, R, pool, indices, hU, hR, hQ, he, range, rel, shape, ?_, wc, ?_⟩
    · intro u v
      refine ⟨fun h => ?_, fun ⟨hu, hv, h⟩ => (edges u hu v hv).mpr h⟩
      obtain ⟨p, pair, hp⟩ := h
      obtain ⟨a, ha, b, hb, code⟩ := shape p hp
      obtain ⟨rfl, rfl⟩ := kpair_injective_l M code pair
      exact ⟨ha, hb, (edges a ha b hb).mp ⟨p, pair, hp⟩⟩
    · intro u v x y hu hv
      exact member u (wc.function.bound_l hu).1 v (wc.function.bound_l hv).1
        x (wc.function.bound_l hu).2 y (wc.function.bound_l hv).2 hu hv
  · rintro ⟨J, P, G, U, R, pool, indices, hU, hR, hQ, he, range, rel, shape, edges, wc, member⟩
    exact ⟨J, pool.indices, P, pool.powers, G, pool.functions, U, hU, R, hR, pool, indices, hQ, he,
      range, rel, shape, fun u hu v hv => (edges u v).trans ⟨fun h => h.2.2, fun h => ⟨hu, hv, h⟩⟩,
      wc, fun u _ v _ x _ y _ => member u v x y⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 同一有界超幂在严格秩截断中的保持

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
  have ht := rank.transitive_l hX hV
  have hJ := rank.relations_mem_l hX hV hα hw hL pool.indices (fun a ha p hp => by
    obtain ⟨n, hn, fn, _⟩ := (indices a).mp ha
    obtain ⟨i, hi, x, hx, pair⟩ := fn.1 p hp
    exact ⟨i, hω.transitive (ZF.modelsKP hZF) n hn i hi, x, hx, pair⟩)
  have hP := rank.subsets_mem_l hX hV hα hK pool.powers
    (fun x hx => ((pool.subsets x).mp hx).2)
  have hG := rank.relations_mem_l hX hV hα hK hB pool.functions
    (fun f hf => ((pool.graphs f).mp hf).2)
  have hA := rank.relation_mem_l hX hV hα hJ hG pool.carrier (fun u hu => by
    obtain ⟨a, ha, f, hf, pair, _⟩ := (pool.nodes u).mp hu
    exact ⟨a, ha, f, hf, pair⟩)
  exact ⟨hJ, hP, hG, hA, fun x =>
    ⟨fun hx => ⟨ht P hP x hx, ((pool.subsets x).mp hx).2⟩,
      fun ⟨hx, sub⟩ => (pool.subsets x).mpr ⟨hX V hV x hx, sub⟩⟩,
    fun f => ⟨fun hf => ⟨ht G hG f hf, ((pool.graphs f).mp hf).2⟩,
      fun ⟨hf, bound⟩ => (pool.graphs f).mpr ⟨hX V hV f hf, bound⟩⟩, pool.nodes⟩

/-- 截断保留全部原节点、原关系、同一个传递像及原求值图。 -/
theorem Eb_collapse_d.rank_l {ω κ K X α V R L B A Q Y e F W : M.Domain}
    (source : Ep_source_d (kp_pair_l (ZF.modelsKP hZF)) ω κ K V R) (hX : M.TransitiveSet X) (hV : M.mem V X)
    (rank : Vr_d X α V) (hα : M.IsLimitOrdinal α) (hL : M.mem L V) (hF : M.mem F V)
    (limit : M.IsLimitOrdinal L) (level : Er_level_d V L W) (hκ : M.mem κ W) (hB : M.mem B W)
    (collapse : Eb_collapse_d ω κ L K X B F A Q Y e) :
    M.mem Y V ∧ Eb_collapse_d ω κ L K V B F A Q Y e := by
  obtain ⟨J, P, G, U, T, pool, indices, _, hT, hQ, _, range, membership, shape, edges, wc, member⟩ := collapse
  have hBV := source.transitive W level.member B hB
  have pool' := pool.rank_l hZF source.omega hX hV rank hα source.omega_mem source.finite.mem_l hL hBV indices
  have hTV := rank.relation_mem_l hX hV hα hBV hBV hT (fun p hp => by
    obtain ⟨x, y, hx, hy, _, pair⟩ := (membership p).mp hp
    exact ⟨x, hx, y, hy, pair⟩)
  have hQV := rank.relation_mem_l hX hV hα pool'.carrier pool'.carrier hQ shape
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

omit hZF in
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
      fun ⟨hf, bound⟩ => (pool.graphs f).mpr ⟨rank.relation_mem_l hX hV hα hK hB hf bound, bound⟩⟩

omit hZF in
/-- 同一个有界呈示及塌缩在大源中保持；无需再次构造商或选择新的求值图。 -/
theorem Eb_collapse_d.of_rank_l {ω κ K X α V L B A Q Y e F : M.Domain}
    (hX : M.TransitiveSet X) (hV : M.mem V X) (rank : Vr_d X α V) (hα : M.IsLimitOrdinal α)
    (hK : M.mem K V) (hB : M.mem B V) (collapse : Eb_collapse_d ω κ L K V B F A Q Y e) :
    Eb_collapse_d ω κ L K X B F A Q Y e := by
  obtain ⟨J, P, G, U, R, pool, indices, hU, hR, hQ, he, rest⟩ := collapse
  exact ⟨J, P, G, U, R, pool.of_rank_l hX hV rank hα hK hB, indices,
    hX V hV U hU, hX V hV R hR, hX V hV Q hQ, hX V hV e he, rest⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 原所属模型中有界池与坍塌的实际像

所属全初等图搬运原证书的全部对象，并保留原有限支撑范围。
支撑列空间也由同一个图实际搬运，目标中的新节点仍由完整原公式覆盖。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

/-- 原源内部的池、关系、坍塌图随所属图共同搬运，不更换坍塌或其定义域。 -/
theorem Eb_collapse_d.owner_image_l {Ω c N T c' N' T' σ : M.Domain}
    (hΩ : M.IsOmega Ω) (mx : Smdl_d I c N T) (my : Smdl_d I c' N' T')
    (map : Smap_d I Ω c c' N N' σ)
    (hN : (smdl_structure_l I (R := T) mx.2.1).Models KP)
    (hN' : (smdl_structure_l I (R := T') my.2.1).Models KP)
    (w κ ℓ K X B F A Q Y e H : (smdl_structure_l I (R := T) mx.2.1).Domain)
    (w' κ' ℓ' K' X' B' F' A' Q' Y' e' : (smdl_structure_l I (R := T') my.2.1).Domain)
    (hw : Rd_entry_d w.val w'.val σ) (hκ : Rd_entry_d κ.val κ'.val σ)
    (hℓ : Rd_entry_d ℓ.val ℓ'.val σ) (hK : Rd_entry_d K.val K'.val σ)
    (hX : Rd_entry_d X.val X'.val σ) (hB : Rd_entry_d B.val B'.val σ)
    (hF : Rd_entry_d F.val F'.val σ) (hA : Rd_entry_d A.val A'.val σ)
    (hQ : Rd_entry_d Q.val Q'.val σ) (hY : Rd_entry_d Y.val Y'.val σ) (he : Rd_entry_d e.val e'.val σ)
    (sequences : Fseq_space_d (kp_pair_l hN) w ℓ H)
    (owned : Eb_collapse_d w κ ℓ K X B F A Q Y e) :
    Eb_collapse_d w' κ' ℓ' K' X' B' F' A' Q' Y' e' ∧
      (∃ H' : (smdl_structure_l I (R := T') my.2.1).Domain,
        Rd_entry_d H.val H'.val σ ∧ Fseq_space_d (kp_pair_l hN') w' ℓ' H') ∧
      (∀ u x : (smdl_structure_l I (R := T) mx.2.1).Domain,
        ∀ u' x' : (smdl_structure_l I (R := T') my.2.1).Domain,
          Rd_entry_d u.val u'.val σ → Rd_entry_d x.val x'.val σ →
            (Rd_entry_d u x e ↔ Rd_entry_d u' x' e')) ∧
      ∃ D B₀ s D' B₁ s',
        (∀ x, M.mem x D ↔ M.mem x N ∧ Rd_entry_d x A.val T) ∧
        (∀ x, M.mem x B₀ ↔ M.mem x N ∧ Rd_entry_d x Y.val T) ∧
        (∀ x, M.mem x D' ↔ M.mem x N' ∧ Rd_entry_d x A'.val T') ∧
        (∀ x, M.mem x B₁ ↔ M.mem x N' ∧ Rd_entry_d x Y'.val T') ∧
        Fn0_d D B₀ s ∧ Fn0_d D' B₁ s' ∧
        (∀ u x : (smdl_structure_l I (R := T) mx.2.1).Domain, Rd_entry_d u.val x.val s ↔ Rd_entry_d u x e) ∧
        (∀ u x : (smdl_structure_l I (R := T') my.2.1).Domain, Rd_entry_d u.val x.val s' ↔ Rd_entry_d u x e') ∧
        (∀ u u', Rd_entry_d u u' σ → (M.mem u D ↔ M.mem u' D') ∧ (M.mem u B₀ ↔ M.mem u' B₁)) ∧
        (∀ u u' x x', Rd_entry_d u u' σ → Rd_entry_d x x' σ → (Rd_entry_d u x s ↔ Rd_entry_d u' x' s')) := by
  obtain ⟨h, hh, hH⟩ := map.1.1.2.2 H.val H.property
  let H' : (smdl_structure_l I (R := T') my.2.1).Domain := ⟨h, hh⟩
  let ρ₀ : Env (smdl_structure_l I (R := T) mx.2.1) 3 :=
    ⟨Fin.cases H (Fin.cases ℓ (fun _ => w)), fun _ => w⟩
  let η₀ : Env (smdl_structure_l I (R := T') my.2.1) 3 :=
    ⟨Fin.cases H' (Fin.cases ℓ' (fun _ => w')), fun _ => w'⟩
  have finite := smap_source_l I hZF hΩ mx my map
    (fseq_space_m (𝒞 := kpair_convention_l) (.bound 2) (.bound 1) .newest)
    (by simp -implicitDefEqProofs) ρ₀ η₀ (Fin.cases hH (Fin.cases hℓ (fun _ => hw)))
  have sequences' := (fseq_space_sat_l (kp_pair_l hN') hN'.1 η₀ (.bound 2) (.bound 1) .newest).mp
    (finite.mp ((fseq_space_sat_l (kp_pair_l hN) hN.1 ρ₀ (.bound 2) (.bound 1) .newest).mpr sequences))
  let ρ : Env (smdl_structure_l I (R := T) mx.2.1) 12 :=
    ⟨fun i => [H, e, Y, Q, A, F, B, X, K, ℓ, κ, w].get i, fun _ => w⟩
  let η : Env (smdl_structure_l I (R := T') my.2.1) 12 :=
    ⟨fun i => [H', e', Y', Q', A', F', B', X', K', ℓ', κ', w'].get i, fun _ => w'⟩
  have tr := smap_source_l I hZF hΩ mx my map
    (eb_collapse_m (.bound 11) (.bound 10) (.bound 9) (.bound 8) (.bound 7) (.bound 6)
      (.bound 5) (.bound 4) (.bound 3) (.bound 2) (.bound 1) .newest)
    (by simp -implicitDefEqProofs) ρ η
    (Fin.cases hH (Fin.cases he (Fin.cases hY (Fin.cases hQ (Fin.cases hA (Fin.cases hF
      (Fin.cases hB (Fin.cases hX (Fin.cases hK (Fin.cases hℓ (Fin.cases hκ (Fin.cases hw (fun i => Fin.elim0 i)))))))))))))
  have owned' := (eb_collapse_sat_l hN' η (.bound 11) (.bound 10) (.bound 9) (.bound 8) (.bound 7) (.bound 6)
    (.bound 5) (.bound 4) (.bound 3) (.bound 2) (.bound 1) .newest sequences').mp
      (tr.mp ((eb_collapse_sat_l hN ρ (.bound 11) (.bound 10) (.bound 9) (.bound 8) (.bound 7) (.bound 6)
        (.bound 5) (.bound 4) (.bound 3) (.bound 2) (.bound 1) .newest sequences).mpr owned))
  have entry u x u' x' (huu : Rd_entry_d u.val u'.val σ) (hxx : Rd_entry_d x.val x'.val σ) :
      Rd_entry_d u x e ↔ Rd_entry_d u' x' e' := by
    have tr := smap_source_l I hZF hΩ mx my map (n := 3) (rd_entry0_m (.bound 2) (.bound 1) .newest)
      (by simp -implicitDefEqProofs)
      ⟨Fin.cases e (Fin.cases x (fun _ => u)), fun _ => u⟩
      ⟨Fin.cases e' (Fin.cases x' (fun _ => u')), fun _ => u'⟩ (Fin.cases he (Fin.cases hxx (fun _ => huu)))
    exact (rd_entry0_sat_l hN.1 ..).symm.trans (tr.trans (rd_entry0_sat_l hN'.1 ..))
  -- 两张对象码图均从同一个内部坍塌及其指定像展开，完整定义域一起对应。
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, wc, _⟩ := owned
  have data := owned'
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, wc', _⟩ := data
  obtain ⟨D, B₀, s, dc, bc, fs, sr⟩ := smdl_graph_l hZF mx.2.1 hN.1 A Y e wc.function
  obtain ⟨D', B₁, s', dc', bc', fs', sr'⟩ := smdl_graph_l hZF my.2.1 hN'.1 A' Y' e' wc'.function
  refine ⟨owned', ⟨H', hH, sequences'⟩, entry, D, B₀, s, D', B₁, s', dc, bc, dc', bc', fs, fs', sr, sr', ?_, ?_⟩
  · intro u u' huu
    have hu := map.1.1.input_mem_of_pairMember huu
    have hu' := map.1.1.output_mem_of_pairMember huu
    exact ⟨(dc u).trans ((and_iff_right hu).trans ((map.relation_l I hZF hΩ mx my huu hA).trans
      ((dc' u').trans (and_iff_right hu')).symm)),
      (bc u).trans ((and_iff_right hu).trans ((map.relation_l I hZF hΩ mx my huu hY).trans
        ((bc' u').trans (and_iff_right hu')).symm))⟩
  · intro u u' x x' huu hxx
    let u₀ := (⟨u, map.1.1.input_mem_of_pairMember huu⟩ : (smdl_structure_l I (R := T) mx.2.1).Domain)
    let x₀ := (⟨x, map.1.1.input_mem_of_pairMember hxx⟩ : (smdl_structure_l I (R := T) mx.2.1).Domain)
    let u₁ := (⟨u', map.1.1.output_mem_of_pairMember huu⟩ : (smdl_structure_l I (R := T') my.2.1).Domain)
    let x₁ := (⟨x', map.1.1.output_mem_of_pairMember hxx⟩ : (smdl_structure_l I (R := T') my.2.1).Domain)
    exact (sr u₀ x₀).trans ((entry u₀ x₀ u₁ x₁ huu hxx).trans (sr' u₁ x₁).symm)

/-- 工作侧的真实隶属表示将同一个原生池与坍塌读回；有限支撑范围由完整源提供。 -/
theorem Eb_collapse_d.read_mem_l {ω μ K₀ c N T z : M.Domain}
    (work : Ep_source_d I ω μ K₀ N T) (model : Smem_d I c N T)
    (hN : (smdl_structure_l I (R := T) model.1.2.1).Models KP)
    (w κ ℓ K X B F A Q Y e H : (smdl_structure_l I (R := T) model.1.2.1).Domain)
    (numbers : Rr_layer_d I ω N T w.val z) (sequences : Fseq_space_d (kp_pair_l hN) w ℓ H)
    (owned : Eb_collapse_d w κ ℓ K X B F A Q Y e) :
    Eb_collapse_d ω κ.val ℓ.val K.val X.val B.val F.val A.val Q.val Y.val e.val := by
  have hw := (numbers.omega_mem_l I (ZF.modelsKP hZF) work.omega work.transitive model).1
  have finite : Sc_fseq_d I w.val ℓ.val H.val N T :=
    (sc_fseq_native_l I model.1.2.1 hN.1 w ℓ H).mpr (fun f => (sequences f).trans
      (exists_congr fun n => and_congr_right fun _ =>
        ⟨fn0_of_function_l hN, fn0_function_l hN⟩))
  have algebra := work.algebra_l (ZF.modelsKP hZF)
  have actual : Fseq_space_d I w.val ℓ.val H.val := hw.symm ▸
    ((sc_fseq_mem_l I (ZF.modelsKP hZF) work.omega work.transitive model work.omega_mem
      ℓ.property H.property algebra.pair algebra.union).mp (hw ▸ finite))
  let ρ : Env (smdl_structure_l I (R := T) model.1.2.1) 12 :=
    ⟨fun i => [H, e, Y, Q, A, F, B, X, K, ℓ, κ, w].get i, fun _ => w⟩
  have valid := (eb_collapse_sat_l hN ρ (.bound 11) (.bound 10) (.bound 9) (.bound 8) (.bound 7) (.bound 6)
    (.bound 5) (.bound 4) (.bound 3) (.bound 2) (.bound 1) .newest sequences).mpr owned
  have moved := (smem_delta_image_l I model work.transitive (eb_collapse_delta_l ..) ρ).mp valid
  let η : Env M 12 := image_env_l (M := smdl_structure_l I (R := T) model.1.2.1) (N := M) Subtype.val ρ
  have result : Eb_collapse_d w.val κ.val ℓ.val K.val X.val B.val F.val A.val Q.val Y.val e.val :=
    (eb_collapse_sat_l (ZF.modelsKP hZF) η
      (.bound 11) (.bound 10) (.bound 9) (.bound 8) (.bound 7) (.bound 6)
      (.bound 5) (.bound 4) (.bound 3) (.bound 2) (.bound 1) .newest actual).mp moved
  exact hw ▸ result

/-- 原生小秩源中的同一池读回完整工作源，有限列空间由已有源唯一确定。 -/
theorem Eb_collapse_d.read_rank_l {ω K₀ c N T z : M.Domain}
    (model : Smem_d I c N T) (hN : (smdl_structure_l I (R := T) model.1.2.1).Models KP)
    (w κ ℓ K X B F A Q Y e H δ : (smdl_structure_l I (R := T) model.1.2.1).Domain)
    (work : Ep_source_d I ω κ.val K₀ N T) (numbers : Rr_layer_d I ω N T w.val z)
    (finite : Fseq_space_d (kp_pair_l hN) w κ K) (support : Fseq_space_d (kp_pair_l hN) w ℓ H)
    (rank : V_d (kp_pair_l hN) δ X) (height : (smdl_structure_l I (R := T) model.1.2.1).IsLimitOrdinal δ)
    (hK : (smdl_structure_l I (R := T) model.1.2.1).mem K X)
    (hB : (smdl_structure_l I (R := T) model.1.2.1).mem B X)
    (owned : Eb_collapse_d w κ ℓ K X B F A Q Y e) :
    Eb_collapse_d ω κ.val ℓ.val K₀ N B.val F.val A.val Q.val Y.val e.val := by
  have read := owned.read_mem_l hZF work model hN w κ ℓ K X B F A Q Y e H numbers support
  have relative := (rr_rank_mem_l I (ZF.modelsKP hZF) model work.transitive δ.property X.property).mp
    ((rr_rank_native_l I model.1.2.1 hN δ X).mpr rank)
  let ρ : Env (smdl_structure_l I (R := T) model.1.2.1) 1 := ⟨fun _ => δ, fun _ => δ⟩
  have height' : M.IsLimitOrdinal δ.val := (KP.limit0_sat_l (ZF.modelsKP hZF)
    (image_env_l (M := smdl_structure_l I (R := T) model.1.2.1) (N := M) Subtype.val ρ) .newest).mp
      ((smem_delta_image_l I model work.transitive (KP.limit0_delta_l .newest) ρ).mp
        ((KP.limit0_sat_l hN ρ .newest).mpr height))
  have lift := read.of_rank_l work.transitive X.property relative height'
    ((model.2 K.val X.val).mp hK).2.2 ((model.2 B.val X.val).mp hB).2.2
  have hw := (numbers.omega_mem_l I (ZF.modelsKP hZF) work.omega work.transitive model).1
  have seq : Sc_fseq_d I w.val κ.val K.val N T :=
    (sc_fseq_native_l I model.1.2.1 hN.1 w κ K).mpr (fun f => (finite f).trans
      (exists_congr fun n => and_congr_right fun _ => ⟨fn0_of_function_l hN, fn0_function_l hN⟩))
  have algebra := work.algebra_l (ZF.modelsKP hZF)
  have actual := (sc_fseq_mem_l I (ZF.modelsKP hZF) work.omega work.transitive model work.omega_mem
    κ.property K.property algebra.pair algebra.union).mp (hw ▸ seq)
  have eq : K.val = K₀ := hZF.1.eq_of_same_members K.val K₀
    (fun f => (actual f).trans ((work.finite_l (ZF.modelsKP hZF)) f).symm)
  exact eq ▸ lift

end YesMetaZFC.SetTheory.LargeCardinal
