import YesMetaZFC.SetTheory.LargeCardinal.ExtenderSystem
import YesMetaZFC.Model.SetTheory.Internal.DirectedSystem.Limit

/-! # 同一有限支撑超幂中的代表元计算

直接以商投影读取 [a,f]，给出实际代表的存在、同分量原子方程及坐标
拉回不变性。这些计算不预设原派生嵌入或超幂良基性。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

def Ep_repr_d (q a f E : M.Domain) : Prop :=
  ∃ u B, KPair_d M u a B ∧ M.mem f B ∧ Rd_entry_d u E q

def ep_repr_m {d} (q a f E : Term d) : Formula 1 d := .existsE (.existsE
  (.conj (kpair_m (.bound 1) a.weaken.weaken .newest)
    (.conj (.mem f.weaken.weaken .newest) (rd_entry_m (.bound 1) E.weaken.weaken q.weaken.weaken))))
derive_free_closed ep_repr_m

theorem ep_repr_sat_l (hE : Extensional M) {d} (ρ : Env M d) (q a f E : Term d) :
    Formula.satisfies ρ (ep_repr_m q a f E) ↔ Ep_repr_d (q.eval ρ) (a.eval ρ) (f.eval ρ) (E.eval ρ) := by
  simp only [ep_repr_m, Ep_repr_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    kpair_sat_l M hE, Formula.satisfies_mem_iff, rd_entry_sat_l hE, Definitional.Term.eval_weaken]; rfl

variable (hZF : M.Models ZF) {ω κ L X R F J O Z A p T S q C W : M.Domain}
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Ep_repr_d.index_l (h : Ep_system_d I ω κ L X R F J O Z A p T S)
    (limit : Di_limit_d A p T S q C W) {a f E} (he : Ep_repr_d q a f E) : M.mem a J := by
  obtain ⟨u, B, hu, _, huE⟩ := he
  exact (h.projection.bound_l ((h.index u a B hu).mpr (limit.projection.bound_l huE).1)).2

theorem ep_repr_exists_l (family : Em_source_d ω κ L X F)
    (h : Ep_system_d I ω κ L X R F J O Z A p T S) (limit : Di_limit_d A p T S q C W)
    {n D a f : M.Domain} (haJ : M.mem a J) (ha : Fn0_d n L a) (hD : Ep_space_d κ n D)
    (hfX : M.mem f X) (hf : Fn0_d D X f) : ∃ E, M.mem E C ∧ Ep_repr_d q a f E := by
  obtain ⟨_, hz, models⟩ := h.models
  obtain ⟨b, _, hab⟩ := hz.2.1 a haJ
  obtain ⟨m, D', U, G, r, H, V, _, ha', hD', haU, hG, model⟩ := models a b hab
  have en := ha'.domain_eq_l hZF.1 ha
  subst m
  have eD := hZF.1.eq_of_same_members D' D (fun s => (hD' s).trans (hD s).symm)
  subst D'
  obtain ⟨B, hBH, hfB⟩ := model.map.projection.2.2 f ((hG f).mpr ⟨hfX, hf⟩)
  obtain ⟨u, hu⟩ := (I).total a B
  have huA := (h.nodes u).mpr ⟨a, B, hu, b, H, V, hab, model.code.1, hBH⟩
  obtain ⟨E, hEC, huE⟩ := limit.projection.2.1 u huA
  exact ⟨E, hEC, u, B, hu, model.map.representative_l I (family.at_l hZF.1 haU ha hD).base hfB, huE⟩

/-- 极限的每个元素都有实际源内代表。 -/
theorem ep_repr_surjective_l (family : Em_source_d ω κ L X F)
    (h : Ep_system_d I ω κ L X R F J O Z A p T S) (limit : Di_limit_d A p T S q C W)
    {E : M.Domain} (hEC : M.mem E C) : ∃ n a D f, M.mem n ω ∧ M.mem a J ∧ Fn0_d n L a ∧
      Ep_space_d κ n D ∧ M.mem f X ∧ Fn0_d D X f ∧ Ep_repr_d q a f E := by
  obtain ⟨u, huE⟩ := (limit.range E).mp hEC
  have huA := (limit.projection.bound_l huE).1
  obtain ⟨a, B, hu, _, _, _, _, _, _⟩ := (h.nodes u).mp huA
  obtain ⟨_, _, models⟩ := h.models
  obtain ⟨_, _, _, _, component, model, hB⟩ := ep_at_model_l hZF models (h.toEp_graph_d.at_l huA hu)
  obtain ⟨n, hn, ha, ⟨f, hfB⟩, reps⟩ := ep_representatives_l I hZF.1 family component model hB
  obtain ⟨hfX, D, hD, hf⟩ := reps f hfB
  exact ⟨n, a, D, f, hn, (h.projection.bound_l ((h.index u a B hu).mpr huA)).2,
    ha, hD, hfX, hf, u, B, hu, hfB, huE⟩

/-- 代表所属的实际源和内部有限定义域，可由商证书直接读回。 -/
theorem Ep_repr_d.source_l (family : Em_source_d ω κ L X F)
    (h : Ep_system_d I ω κ L X R F J O Z A p T S) (limit : Di_limit_d A p T S q C W)
    {a f E : M.Domain} (he : Ep_repr_d q a f E) : M.mem f X ∧ ∃ n, M.mem n ω ∧ Fn0_d n L a ∧ Ep_fun_d κ X n f := by
  obtain ⟨u, B, hu, hf, huE⟩ := he
  obtain ⟨_, _, models⟩ := h.models
  obtain ⟨_, _, _, _, component, model, hB⟩ := ep_at_model_l hZF models
    (h.toEp_graph_d.at_l (limit.projection.bound_l huE).1 hu)
  obtain ⟨n, hn, ha, _, reps⟩ := ep_representatives_l I hZF.1 family component model hB
  exact ⟨(reps f hf).1, n, hn, ha, (reps f hf).2⟩

/-- 固定分量中，极限上的等号和隶属恰好由原代表的测度一关系判定。 -/
theorem ep_repr_atoms_l (family : Em_source_d ω κ L X F)
    (h : Ep_system_d I ω κ L X R F J O Z A p T S) (limit : Di_limit_d A p T S q C W)
    {a f g E H U : M.Domain} (haU : Rd_entry_d a U F) (he : Ep_repr_d q a f E) (hh : Ep_repr_d q a g H) :
    (E = H ↔ Rp_eq_d X U f g) ∧ (Rd_entry_d E H W ↔ Rp_rel_d I X U R f g) := by
  obtain ⟨u, B, hu, hf, huE⟩ := he
  obtain ⟨v, D, hv, hg, hvH⟩ := hh
  have huA := (limit.projection.bound_l huE).1
  have hvA := (limit.projection.bound_l hvH).1
  have hua := (h.index u a B hu).mpr huA
  have hva := (h.index v a D hv).mpr hvA
  obtain ⟨_, hz, models⟩ := h.models
  obtain ⟨b, Q, V, hab, component, model, hBQ⟩ := ep_at_model_l hZF models (h.toEp_graph_d.at_l huA hu)
  have hDQ := (ep_at_read_l hz hab model.1).mp (h.toEp_graph_d.at_l hvA hv)
  have relation := ep_relation_l I hZF.1 family component model hBQ hDQ hf hg haU
  have rel := (limit.relation u v E H huE hvH).trans
    (h.diagram.rel_at_l hua hva (h.diagram.identity u huA) (h.diagram.identity v hvA))
  have same : u = v ↔ B = D := ⟨fun e => ((kpair_injective_l M (e ▸ hu) hv).2),
    fun e => kpair_unique_l M hZF.1 (e ▸ hu) hv⟩
  obtain ⟨n, Q₀, V₀, G, r, Q', S', _, ha, hQ₀, haV, _, md⟩ := component
  obtain ⟨rfl, rfl⟩ := smdl_unique_l I md.code model
  have ev := family.function a V₀ U haV haU
  subst V₀
  have ultra := (family.at_l hZF.1 haU ha hQ₀).base
  refine ⟨(limit.kernel u v E H huE hvH).trans ((h.diagram.eq_at_l hua hva).trans
    (same.trans (rp_kernel_l I hZF.1 ultra md.map (md.map.member_l I hZF.1 ultra hBQ hf)
      (md.map.member_l I hZF.1 ultra hDQ hg)))), rel.trans ?_⟩
  exact (h.toEp_graph_d.relation_l hu hv).trans
    ((and_congr_right fun _ => and_congr_right fun _ => ep_rel_read_l hz hab model.1).trans
      (Iff.trans ⟨And.right ∘ And.right, fun hr => ⟨huA, hvA, hr⟩⟩ relation))

theorem ep_repr_pull_l
    (h : Ep_system_d I ω κ L X R F J O Z A p T S) (limit : Di_limit_d A p T S q C W)
    {m n a b r f g E H : M.Domain} (hm : M.mem m ω) (hn : M.mem n ω)
    (hr : Fn0_d m n r) (hb : Fn0_d n L b) (hra : Cp0_d m n L r b a)
    (pull : Ep_pull_d κ X m n r f g) (he : Ep_repr_d q a f E) (hh : Ep_repr_d q b g H) : E = H := by
  obtain ⟨u, B, hu, hf, huE⟩ := he
  obtain ⟨v, D, hv, hg, hvH⟩ := hh
  exact limit.commute_l h.diagram ((h.toEp_graph_d.arrow_l hu hv).mpr
    ⟨(limit.projection.bound_l huE).1, (limit.projection.bound_l hvH).1,
      m, n, r, f, g, hm, hn, hr, hb, hra, hf, hg, pull⟩) huE hvH

/-- 实际构造拉回代表，并保留它在同一极限中的值。 -/
theorem ep_repr_reindex_l {R₀ : M.Domain} (source : Ep_source_d hZF ω κ K X R₀) (family : Em_source_d ω κ L X F)
    (h : Ep_system_d I ω κ L X R F J O Z A p T S) (limit : Di_limit_d A p T S q C W)
    {n m a b D E r f B : M.Domain} (hn : M.mem n ω) (hm : M.mem m ω)
    (hr : Fn0_d n m r) (hbJ : M.mem b J) (hb : Fn0_d m L b) (hra : Cp0_d n m L r b a)
    (hD : Ep_space_d κ n D) (hE : Ep_space_d κ m E) (hfX : M.mem f X) (hf : Fn0_d D X f)
    (value : Ep_repr_d q a f B) : ∃ g, M.mem g X ∧ Fn0_d E X g ∧
      Ep_pull_d κ X n m r f g ∧ Ep_repr_d q b g B := by
  obtain ⟨t, htX, ht, ts⟩ := source.projection_l hZF hn hm hr hD hE
  obtain ⟨c, code⟩ := source.code
  obtain ⟨g, hg, comp⟩ := sc_compose_l hZF source.omega source.transitive code source.theory
    (source.space_mem_l hZF hm hE) (source.space_mem_l hZF hn hD) htX hfX ht hf
  have pull := ep_pull_of_comp_l hD hE ht hf ts comp
  obtain ⟨H, _, hh⟩ := ep_repr_exists_l hZF family h limit hbJ hb hE hg.1 comp.1
  exact ⟨g, hg.1, comp.1, pull, (ep_repr_pull_l hZF h limit hn hm hr hb hra pull value hh).symm ▸ hh⟩

end YesMetaZFC.SetTheory.LargeCardinal
