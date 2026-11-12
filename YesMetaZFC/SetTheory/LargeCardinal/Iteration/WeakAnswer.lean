import YesMetaZFC.SetTheory.LargeCardinal.Iteration.KeepTransfer
import YesMetaZFC.SetTheory.LargeCardinal.Iteration.BranchTail
import YesMetaZFC.SetTheory.LargeCardinal.Iteration.WeakBranch
import YesMetaZFC.SetTheory.LargeCardinal.Iteration.LimitDiagram
import YesMetaZFC.SetTheory.LargeCardinal.Iteration.NiceReturn
import YesMetaZFC.SetTheory.LargeCardinal.Iteration.CountableCover
import YesMetaZFC.SetTheory.LargeCardinal.Iteration.Branch
import YesMetaZFC.SetTheory.TransitiveClosure

/-! # 线性模型列沿实际返回方块的后继

只消费已经构造的根映射及返回因子。所有新箭头由末边复合产生，
结合律把当前返回方块推广到全部旧节点，旧模型、箭头和返回图保持原值。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Wi_state_d.extend_l {ω α ξ T Q G a A S P c X R d N W π j σ : M.Domain}
    (h : Wi_state_d (kp_pair_l (ZF.modelsKP hZF)) ω α T Q G a A S P) (hw : M.IsOmega ω)
    (hα : M.SuccessorOf α ξ) (hc : Rd_entry_d ξ c Q) (hπ : Rd_entry_d ξ π P)
    (mx : Smdl_d I c X R) (mn : Smem_d I d N W)
    (source : ∃ K, Ep_source_d I ω ω K N W) (count : M.CardinalLessOrEqual I N ω)
    (edgeMap : Smap_d I ω c d X N j) (ret : Smap_d I ω d a N A σ) (square : It_comp_d j σ π) :
    ∃ β U Q' G' P', Wi_state_d (kp_pair_l (ZF.modelsKP hZF)) ω β U Q' G' a A S P' ∧
      Wi_extension_d α Q G P β Q' G' P' ∧
      (∀ i b, Rd_entry_d i b Q' ↔ Rd_entry_d i b Q ∨ i = α ∧ b = d) ∧
      (∀ i f, Rd_entry_d i f P' ↔ Rd_entry_d i f P ∨ i = α ∧ f = σ) ∧ It_map_d G' ξ α j := by
  obtain ⟨β,U,Q',G',e,hβ,diagram,us,qs,gs,edge⟩ :=
    it_diagram_extend_l hZF hw h.diagram hα hc mx mn.1 edgeMap
  have no := KP.mem_irrefl_d (ZF.modelsKP hZF) α
  have old i k f (hk : M.mem k α) : It_map_d G' i k f ↔ It_map_d G i k f := (gs i k f).trans
    ⟨fun hh => hh.elim id (fun hh => (no (hh.1 ▸ hk)).elim), Or.inl⟩
  have tip i (hi : M.mem i α) : Rd_entry_d i α U := by
    apply (us i α).mpr
    refine Or.inr ⟨rfl,Or.inr ?_⟩
    rcases (hα i).mp hi with hi | eq
    · exact h.linear i ξ hα.predecessor_mem hi
    · exact (hZF.1.eq_of_same_members i ξ eq).symm ▸ h.diagram.order.refl ξ hα.predecessor_mem
  have squares i f k (hf : Rd_entry_d i f P) (hk : It_map_d G' i α k) : It_comp_d k σ f := by
    rcases (gs i α k).mp hk with hk | ⟨_,⟨eq,_⟩ | ⟨g,hg,comp⟩⟩
    · exact (no (h.diagram.order.bound i α (h.diagram.map_bound_l hZF hk)).2).elim
    · exact (no (eq ▸ (h.returns.domain i).mpr ⟨f,hf⟩)).elim
    · exact comp.assoc_l square (h.returns.comp_l hZF h.diagram (fun _ h => h) hg hf hπ)
  obtain ⟨P',state,ps⟩ := h.append_l hZF hβ diagram (fun i k hik => (us i k).mpr (Or.inl hik))
    tip qs old mn source count ret squares
  exact ⟨β,U,Q',G',P',state,
    ⟨hβ,fun i b hb => (qs i b).mpr (Or.inl hb),old,fun i f hf => (ps i f).mpr (Or.inl hf)⟩,qs,ps,edge⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 弱迭代在可数极限处的完整延长

旧返回列证明原直接极限良基，并产生与全部旧腿交换的同一返回因子。
可数性和完整源由实际极限构造保持，随后追加原规范腿及新返回值。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZFC : M.Models ZFC)
local notation "hZF" => ZFC.models_zf_l hZFC
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Wi_state_d.limit_l {ω α T Q G a A S P : M.Domain}
    (h : Wi_state_d (kp_pair_l (ZF.modelsKP hZF)) ω α T Q G a A S P) (ma : Smem_d I a A S)
    (limit : M.IsLimitOrdinal α) (count : M.CardinalLessOrEqual I α ω) :
    ∃ β U Q' G' P' c N W H σ, Wi_state_d (kp_pair_l (ZF.modelsKP hZF)) ω β U Q' G' a A S P' ∧
      Wi_extension_d α Q G P β Q' G' P' ∧ Rd_entry_d α c Q' ∧ Rd_entry_d α σ P' ∧
      Wi_limit_d hZF ω α Q G c N W H ∧ Wi_limit_tree_d hZF ω α T Q G c N W H ∧
      It_wf_branch_d hZF ω α T Q G α ∧
      Smap_d I ω c a N A σ ∧
      (∀ i j, M.mem i α → (It_map_d G' i α j ↔ Rd_entry_d i j H)) ∧
      ∀ i f j, Rd_entry_d i f P → Rd_entry_d i j H → It_comp_d j σ f := by
  obtain ⟨o, ho⟩ := limit.2.1
  obtain ⟨c₀, hc₀⟩ := (h.diagram.model_domain o).mp ho
  obtain ⟨X₀, R₀, K₀, mx₀, source⟩ := h.sources o c₀ hc₀
  have ready := it_source_mem_l hZF mx₀ source
  have hw := source.omega
  obtain ⟨L, D, p, F, R, r, c, N, W, H, σ, s, lim, mn, cone, ready, cn, hs, projects, squares, ls, wfN⟩ :=
    it_countable_limit_l hZFC hw h.diagram (h.branch_l hZF) ho hc₀ ready ma h.returns count h.count
  have wfBranch := It_branch_d.wf_of_limit_l hZF h.diagram hw (h.branch_l hZF) s ls lim mn wfN
  obtain ⟨β, U, Q', G', e, hβ, diagram, us, qs, gs⟩ :=
    it_limit_diagram_l hZF hw h.diagram limit (h.branch_l hZF) cone
  have no := KP.mem_irrefl_d (ZF.modelsKP hZF) α
  have old i j f (hj : M.mem j α) : It_map_d G' i j f ↔ It_map_d G i j f := (gs i j f).trans
    ⟨fun hh => hh.elim id (fun hh => (no (hh.1 ▸ hj)).elim), Or.inl⟩
  have square i f j (hf : Rd_entry_d i f P) (hj : It_map_d G' i α j) : It_comp_d j σ f := by
    rcases (gs i α j).mp hj with hj | ⟨_, ⟨eq, _⟩ | hj⟩
    · exact (no (h.diagram.order.bound i α (h.diagram.map_bound_l hZF hj)).2).elim
    · exact (no (eq ▸ (h.returns.domain i).mpr ⟨f, hf⟩)).elim
    · exact squares i f j hf hj
  obtain ⟨P', state, ps⟩ := h.append_l hZF hβ diagram (fun i j hij => (us i j).mpr (Or.inl hij))
    (fun i hi => (us i α).mpr (Or.inr ⟨rfl, Or.inr hi⟩)) qs old mn ready cn hs square
  refine ⟨β, U, Q', G', P', c, N, W, H, σ, state,
    ⟨hβ, fun i d hd => (qs i d).mpr (Or.inl hd), old, fun i f hf => (ps i f).mpr (Or.inl hf)⟩,
    (qs α c).mpr (Or.inr ⟨rfl, rfl⟩), (ps α σ).mpr (Or.inr ⟨rfl, rfl⟩),
    ⟨L, D, p, F, R, r, s, lim, mn, cone, projects⟩,
    ⟨L, D, p, F, R, r, s, ls, lim, mn, cone, projects, wfN⟩, wfBranch, hs, ?_, squares⟩
  intro i j hi
  exact (gs i α j).trans ⟨fun hh => hh.elim
    (fun hh => (no (h.diagram.order.bound i α (h.diagram.map_bound_l hZF hh)).2).elim)
    (fun hh => hh.2.elim (fun hh => (no (hh.1 ▸ hi)).elim) id), fun hh => Or.inr ⟨rfl, Or.inr hh⟩⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 弱迭代后继步由可复制原关系树的返回定理自动产生

选择同一棵 ω 树的共尾枝和实际极限，再把根腿接到原线性列。
新模型可数，返回因子满足原根复合式，故全部旧返回三角形继续交换。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZFC : M.Models ZFC)
local notation "hZF" => ZFC.models_zf_l hZFC
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Wi_state_d.successor_l {ω α ξ T Q G a A S P θ c T₀ Q₀ G₀ E₀ : M.Domain}
    (h : Wi_state_d (kp_pair_l (ZF.modelsKP hZF)) ω α T Q G a A S P) (rank : V_d I θ A) (ma : Smem_d I a A S)
    (hα : M.SuccessorOf α ξ) (hc : Rd_entry_d ξ c Q)
    (tree : It_tree_d hZF ω c ω T₀ Q₀ G₀ E₀) (copy : It_copyable_d hZF ω c T₀ Q₀ G₀ E₀) :
    ∃ β U Q' G' P' B d N W H σ j, Wi_state_d (kp_pair_l (ZF.modelsKP hZF)) ω β U Q' G' a A S P' ∧
      Wi_extension_d α Q G P β Q' G' P' ∧ Rd_entry_d α d Q' ∧ Rd_entry_d α σ P' ∧
      It_branch_d ω T₀ B ∧ It_wf_branch_d hZF ω ω T₀ Q₀ G₀ B ∧ Wi_limit_d hZF ω B Q₀ G₀ d N W H ∧ Wi_limit_tree_d hZF ω B T₀ Q₀ G₀ d N W H ∧
      It_map_d G' ξ α j ∧ ∀ o, (∀ x, ¬ M.mem x o) → Rd_entry_d o j H := by
  have hw := tree.omega
  obtain ⟨o, ho, _⟩ := hw.1.1
  obtain ⟨X, R, K, mx, sx⟩ := h.sources ξ c hc
  obtain ⟨π, hπ⟩ := (h.returns.domain ξ).mp hα.predecessor_mem
  have embed := h.returns.elementary ξ π c X R hπ hc mx.1
  obtain ⟨B, L, D, p, F, V, r, d, N, W, H, σ, branch, system, limit, mn, cone, ready, hs, projects, j, hj, square, ls, wfN⟩ :=
    it_copyable_return_l hZFC tree copy
      mx sx.transitive (h.count ξ c X R hc mx.1.1) ho rank ma embed
  have wfBranch := It_branch_d.wf_of_limit_l hZF tree.diagram hw branch system ls limit mn wfN
  obtain ⟨en, enumerated⟩ := tree.ja_enum_l hZFC mx.1 (h.count ξ c X R hc mx.1.1)
  have count := cone.countable_enum_l hZF hw tree.diagram branch.subset
    (ZF.exists_inclusionInjection hZF I branch.subset) enumerated
  have jj := cone.elementary o j c X R hj (tree.root o ho) mx.1
  obtain ⟨β,U,Q',G',P',state,extension,qs,ps,edge⟩ :=
    h.extend_l hZF hw hα hc hπ mx.1 mn ready count jj hs square
  refine ⟨β, U, Q', G', P', B, d, N, W, H, σ, j, state,extension,
    (qs α d).mpr (Or.inr ⟨rfl, rfl⟩), (ps α σ).mpr (Or.inr ⟨rfl, rfl⟩),
    branch, wfBranch, ⟨L, D, p, F, V, r, system, limit, mn, cone, projects⟩, ⟨L, D, p, F, V, r, system, ls, limit, mn, cone, projects, wfN⟩, edge, ?_⟩
  intro o' ho'
  exact (hZF.1.eq_of_same_members o o' (fun x => iff_of_false (ho x) (ho' x))) ▸ hj

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 任意极限长度的相容弱迭代历史取并

模型、箭头和返回三列逐项取并；函数性在两个旧行的共同后继验证。
含给定指标的旧行给出并图的精确限制，所有有限元条件因而回到原状态。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}
private def wi_pick {A : Type u} (Q G P : A) : Fin 3 → A := Fin.cases Q (Fin.cases G (fun _ => P))
private def Wi_union_d (k : Fin 3) (H x : M.Domain) : Prop := ∃ i s T Q G P,
  Rd_entry_d i s H ∧ Rd_quad_d s T Q G P ∧ M.mem x (wi_pick Q G P k)
private def wi_union_m (k : Fin 3) {d} (H x : Term d) : Formula 1 d := set[d] ⟪
  ∃ i s T Q G P, ⌜rd_entry0_m⌝ₚ(i, s, ⌜H⌝ₛ) ∧ ⌜rd_quad_m⌝ₚ(s, T, Q, G, P) ∧
    ⌜(fun Q G P x => (Definitional.Formula.mem x (wi_pick Q G P k) : Formula 1 _))⌝ₚ(Q, G, P, ⌜x⌝ₛ)⟫
@[simp] private theorem wi_union_closed_l (k : Fin 3) {d} (H x : Term d)
    (hH : H.freeSupport = []) (hx : x.freeSupport = []) : (wi_union_m k H x).FreeClosed := by
  refine Fin.cases ?_ (Fin.cases ?_ (fun _ => ?_)) k <;>
    simp -implicitDefEqProofs [wi_union_m, wi_pick, Definitional.Formula.FreeClosed, hH, hx] <;> rfl
private theorem wi_union_sat_l (hE : Extensional M) (k : Fin 3) {d} (η : Env M d) (H x : Term d) :
    Formula.satisfies η (wi_union_m k H x) ↔ Wi_union_d k (H.eval η) (x.eval η) := by
  refine Fin.cases ?_ (Fin.cases ?_ (fun _ => ?_)) k <;>
    simp only [wi_union_m, Wi_union_d, wi_pick, Fin.cases_zero, Fin.cases_succ,
      Formula.satisfies_exists_iff, Formula.satisfies_conj_iff, Formula.satisfies_mem_iff,
      rd_entry0_sat_l hE, rd_quad_sat_l hE, Definitional.Term.eval_weaken] <;> rfl

variable (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Wi_history_d.union_l {ω a A S α D H : M.Domain} (hist : Wi_history_d hZF ω a A S α D H)
    (limit : M.IsLimitOrdinal α) : ∃ T Q G P, Wi_state_d (kp_pair_l (ZF.modelsKP hZF)) ω α T Q G a A S P ∧
      ∀ i U Q' G' P', Wi_at_d H i U Q' G' P' → Wi_keep_d Q' G' P' Q G P := by
  have ff := fn0_function_l (ZF.modelsKP hZF) hist.function
  have read {i s T Q G P} (hs : Rd_entry_d i s H) (pack : Rd_quad_d s T Q G P) := hist.at_l hZF ⟨s, hs, pack⟩
  have self {Q G P : M.Domain} : Wi_keep_d (M := M) Q G P Q G P := Wi_keep_d.refl_l Q G P
  have merge {i j s t T Q G P U Q' G' P'} (hs : Rd_entry_d i s H) (ht : Rd_entry_d j t H)
      (ps : Rd_quad_d s T Q G P) (pt : Rd_quad_d t U Q' G' P') :
      ∃ k v V Q'' G'' P'', Rd_entry_d k v H ∧ Rd_quad_d v V Q'' G'' P'' ∧
        Wi_keep_d Q G P Q'' G'' P'' ∧ Wi_keep_d Q' G' P' Q'' G'' P'' := by
    rcases limit.1.wellOrder.linear.compare i (hist.function.bound_l hs).1 j (hist.function.bound_l ht).1 with eq | lt | gt
    · have eq := hZF.1.eq_of_same_members i j eq
      subst j
      have eq := ff.1.2 i t s ht hs
      subst t
      obtain ⟨rfl, rfl, rfl, rfl⟩ := ps.unique_l pt
      exact ⟨i, s, T, Q, G, P, hs, ps, self, self⟩
    · exact ⟨j, t, U, Q', G', P', ht, pt, hist.past i j T Q G P U Q' G' P' lt ⟨s, hs, ps⟩ ⟨t, ht, pt⟩, self⟩
    · exact ⟨i, s, T, Q, G, P, hs, ps, self, hist.past j i U Q' G' P' T Q G P gt ⟨t, ht, pt⟩ ⟨s, hs, ps⟩⟩
  have part {β T Q G P} (state : Wi_state_d (kp_pair_l (ZF.modelsKP hZF)) ω β T Q G a A S P) (k : Fin 3) : M.IsSetFunction I (wi_pick Q G P k) :=
    Fin.cases state.diagram.model_function (Fin.cases state.diagram.map_function (fun _ => state.returns.function)) k
  have keeps {β T Q G P Q' G' P'} (state : Wi_state_d (kp_pair_l (ZF.modelsKP hZF)) ω β T Q G a A S P)
      (keep : Wi_keep_d Q G P Q' G' P') (k : Fin 3) :
      ∀ x y, Rd_entry_d x y (wi_pick Q G P k) → Rd_entry_d x y (wi_pick Q' G' P' k) := by
    refine Fin.cases keep.1 (Fin.cases ?_ (fun _ => keep.2.2)) k
    intro r f hr
    obtain ⟨i, j, pair⟩ := state.diagram.order.relation r ((state.diagram.map_domain r).mpr ⟨f, hr⟩)
    obtain ⟨r', pair', hr'⟩ := keep.2.1 i j f ⟨r, pair, hr⟩
    exact kpair_unique_l M hZF.1 pair' pair ▸ hr'
  obtain ⟨Z, zt, hD, _⟩ := ZF.tc_exists_l I hZF D
  have collect (k : Fin 3) : ∃ C, ∀ x, M.mem x C ↔ Wi_union_d k H x := by
    let φ : UnarySchema 1 := { body := wi_union_m k (.bound 1) .newest }
    let ρ : Env M 1 := ⟨fun _ => H, fun _ => H⟩
    obtain ⟨C, cs⟩ := ZF.separation_exists_d hZF φ ρ Z
    refine ⟨C, fun x => (cs x).trans ?_⟩
    change (M.mem x Z ∧ φ.denote ρ x) ↔ _
    rw [show φ.denote ρ x ↔ Wi_union_d k H x from wi_union_sat_l hZF.1 k ..]
    refine ⟨And.right, fun h => ⟨?_, h⟩⟩
    obtain ⟨i, s, T, Q, G, P, hs, pack, hx⟩ := h
    have owned := pack.mem_l zt (zt D hD s (hist.function.bound_l hs).2)
    have hk : M.mem (wi_pick Q G P k) Z := by
      refine Fin.cases ?_ (Fin.cases ?_ (fun _ => ?_)) k
      · exact owned.2.1
      · exact owned.2.2.1
      · exact owned.2.2.2
    exact zt _ hk x hx
  have graphs (k : Fin 3) {C} (cs : ∀ x, M.mem x C ↔ Wi_union_d k H x) : M.IsSetFunction I C ∧
      ∀ x y, Rd_entry_d x y C ↔ ∃ i s T Q G P, Rd_entry_d i s H ∧ Rd_quad_d s T Q G P ∧ Rd_entry_d x y (wi_pick Q G P k) := by
    have entries x y : Rd_entry_d x y C ↔ ∃ i s T Q G P, Rd_entry_d i s H ∧ Rd_quad_d s T Q G P ∧ Rd_entry_d x y (wi_pick Q G P k) := by
      refine ⟨fun ⟨r, pair, hr⟩ => ?_, fun ⟨i, s, T, Q, G, P, hs, pack, r, pair, hr⟩ => ?_⟩
      · obtain ⟨i, s, T, Q, G, P, hs, pack, hr⟩ := (cs r).mp hr
        exact ⟨i, s, T, Q, G, P, hs, pack, r, pair, hr⟩
      · exact ⟨r, pair, (cs r).mpr ⟨i, s, T, Q, G, P, hs, pack, hr⟩⟩
    refine ⟨⟨fun r hr => ?_, fun x y z hy hz => ?_⟩, entries⟩
    · obtain ⟨i, s, T, Q, G, P, hs, pack, hr⟩ := (cs r).mp hr
      obtain ⟨_, _, state⟩ := read hs pack
      exact (part state k).1 r hr
    · obtain ⟨i, s, T, Q, G, P, hs, pack, hy⟩ := (entries x y).mp hy
      obtain ⟨j, t, U, Q', G', P', ht, pack', hz⟩ := (entries x z).mp hz
      obtain ⟨l, v, V, Q'', G'', P'', hv, pv, sv, tv⟩ := merge hs ht pack pack'
      obtain ⟨_, _, st⟩ := read hv pv
      obtain ⟨_, _, si⟩ := read hs pack
      obtain ⟨_, _, sj⟩ := read ht pack'
      exact (part st k).2 x y z (keeps si sv k x y hy) (keeps sj tv k x z hz)
  obtain ⟨Q, qs⟩ := collect 0
  obtain ⟨G, gs⟩ := collect 1
  obtain ⟨P, ps⟩ := collect 2
  obtain ⟨qf, qe⟩ := graphs 0 qs
  obtain ⟨gf, ge⟩ := graphs 1 gs
  obtain ⟨pf, pe⟩ := graphs 2 ps
  have edge i j f : It_map_d G i j f ↔ ∃ k s T Q G' P,
      Rd_entry_d k s H ∧ Rd_quad_d s T Q G' P ∧ It_map_d G' i j f := by
    refine ⟨fun ⟨r, pair, hr⟩ => ?_, fun ⟨k, s, T, Q, G', P, hs, pack, r, pair, hr⟩ => ?_⟩
    · obtain ⟨k, s, T, Q, G', P, hs, pack, hr⟩ := (ge r f).mp hr
      exact ⟨k, s, T, Q, G', P, hs, pack, r, pair, hr⟩
    · exact ⟨r, pair, (ge r f).mpr ⟨k, s, T, Q, G', P, hs, pack, hr⟩⟩
  have keep {i U Q' G' P'} (hi : Wi_at_d H i U Q' G' P') : Wi_keep_d Q' G' P' Q G P := by
    obtain ⟨s, hs, pack⟩ := hi
    exact ⟨fun j c hc => (qe j c).mpr ⟨i, s, U, Q', G', P', hs, pack, hc⟩,
      fun j k f hf => (edge j k f).mpr ⟨i, s, U, Q', G', P', hs, pack, hf⟩,
      fun j f hf => (pe j f).mpr ⟨i, s, U, Q', G', P', hs, pack, hf⟩⟩
  have stage i (hi : M.mem i α) : ∃ β U Q' G' P', M.SuccessorOf β i ∧ Wi_at_d H i U Q' G' P' ∧ Wi_state_d (kp_pair_l (ZF.modelsKP hZF)) ω β U Q' G' a A S P' := by
    obtain ⟨s, _, hs⟩ := hist.function.2.1 i hi
    obtain ⟨β, U, Q', G', P', hβ, pack, state⟩ := hist.rows i s hs
    exact ⟨β, U, Q', G', P', hβ, ⟨s, hs, pack⟩, state⟩
  have below {i β j} (hi : M.mem i α) (hβ : M.SuccessorOf β i) (hj : M.mem j β) : M.mem j α :=
    ((hβ j).mp hj).elim (limit.1.transitive i hi j) (fun eq => (hZF.1.eq_of_same_members j i eq).symm ▸ hi)
  have qold {i β U Q' G' P'} (hi : Wi_at_d H i U Q' G' P') (st : Wi_state_d (kp_pair_l (ZF.modelsKP hZF)) ω β U Q' G' a A S P')
      {j c} (hj : M.mem j β) : Rd_entry_d j c Q ↔ Rd_entry_d j c Q' := by
    refine ⟨fun hc => ?_, (keep hi).1 j c⟩
    obtain ⟨d, hd⟩ := (st.diagram.model_domain j).mp hj
    exact qf.2 j d c ((keep hi).1 j d hd) hc ▸ hd
  have pold {i β U Q' G' P'} (hi : Wi_at_d H i U Q' G' P') (st : Wi_state_d (kp_pair_l (ZF.modelsKP hZF)) ω β U Q' G' a A S P')
      {j f} (hj : M.mem j β) : Rd_entry_d j f P ↔ Rd_entry_d j f P' := by
    refine ⟨fun hf => ?_, (keep hi).2.2 j f⟩
    obtain ⟨g, hg⟩ := (st.returns.domain j).mp hj
    exact pf.2 j g f ((keep hi).2.2 j g hg) hf ▸ hg
  have bounds {i j f} (hf : It_map_d G i j f) : M.mem i α ∧ M.mem j α ∧ (i = j ∨ M.mem i j) := by
    obtain ⟨k, s, U, Q', G', P', hs, pack, hf⟩ := (edge i j f).mp hf
    obtain ⟨β, hβ, st⟩ := read hs pack
    have h := st.diagram.map_bound_l hZF hf
    exact ⟨below (hist.function.bound_l hs).1 hβ (st.diagram.order.bound i j h).1,
      below (hist.function.bound_l hs).1 hβ (st.diagram.order.bound i j h).2, st.diagram.order.forward i j h⟩
  have gold {k β U Q' G' P'} (hk : Wi_at_d H k U Q' G' P') (st : Wi_state_d (kp_pair_l (ZF.modelsKP hZF)) ω β U Q' G' a A S P')
      {i j f} (hj : M.mem j β) (hf : It_map_d G i j f) : It_map_d G' i j f := by
    have ij := (bounds hf).2.2
    have hit : Rd_entry_d i j U := ij.elim (fun eq => eq.symm ▸ st.diagram.order.refl j hj) (st.linear i j hj)
    obtain ⟨g, hg⟩ := st.diagram.map_l hZF hit
    obtain ⟨r, pr, hr⟩ := (keep hk).2.1 i j g hg
    obtain ⟨s, ps, hs⟩ := hf
    exact gf.2 r g f hr (kpair_unique_l M hZF.1 ps pr ▸ hs) ▸ hg
  obtain ⟨T, order, ts, _⟩ := it_linear_order_l (ZF.modelsKP hZF) limit.1
  have qdom : M.IsDomainOf I α Q := by
    intro i
    refine ⟨fun hi => ?_, fun ⟨c, hc⟩ => ?_⟩
    · obtain ⟨β, U, Q', G', P', hβ, hi', st⟩ := stage i hi
      obtain ⟨c, hc⟩ := (st.diagram.model_domain i).mp hβ.predecessor_mem
      exact ⟨c, (keep hi').1 i c hc⟩
    · obtain ⟨k, s, U, Q', G', P', hs, pack, hc⟩ := (qe i c).mp hc
      obtain ⟨β, hβ, st⟩ := read hs pack
      exact below (hist.function.bound_l hs).1 hβ ((st.diagram.model_domain i).mpr ⟨c, hc⟩)
  have pdom : M.IsDomainOf I α P := by
    intro i
    refine ⟨fun hi => ?_, fun ⟨f, hf⟩ => ?_⟩
    · obtain ⟨β, U, Q', G', P', hβ, hi', st⟩ := stage i hi
      obtain ⟨f, hf⟩ := (st.returns.domain i).mp hβ.predecessor_mem
      exact ⟨f, (keep hi').2.2 i f hf⟩
    · obtain ⟨k, s, U, Q', G', P', hs, pack, hf⟩ := (pe i f).mp hf
      obtain ⟨β, hβ, st⟩ := read hs pack
      exact below (hist.function.bound_l hs).1 hβ ((st.returns.domain i).mpr ⟨f, hf⟩)
  have gdom : M.IsDomainOf I T G := by
    intro r
    refine ⟨fun hr => ?_, fun ⟨f, hr⟩ => ?_⟩
    · obtain ⟨i, j, pair⟩ := order.relation r hr
      obtain ⟨_, hj, ij⟩ := (ts i j).mp ⟨r, pair, hr⟩
      obtain ⟨β, U, Q', G', P', hβ, hj', st⟩ := stage j hj
      have hit : Rd_entry_d i j U := ij.elim (fun eq => eq.symm ▸ st.diagram.order.refl j hβ.predecessor_mem) (st.linear i j hβ.predecessor_mem)
      obtain ⟨f, hf⟩ := st.diagram.map_l hZF hit
      obtain ⟨r', pair', hr'⟩ := (keep hj').2.1 i j f hf
      exact ⟨f, kpair_unique_l M hZF.1 pair' pair ▸ hr'⟩
    · obtain ⟨k, s, U, Q', G', P', hs, pack, hr'⟩ := (ge r f).mp hr
      obtain ⟨_, _, st⟩ := read hs pack
      obtain ⟨i, j, pair⟩ := st.diagram.order.relation r ((st.diagram.map_domain r).mpr ⟨f, hr'⟩)
      obtain ⟨r', pair', hrT⟩ := (ts i j).mpr (bounds ⟨r, pair, hr⟩)
      exact kpair_unique_l M hZF.1 pair' pair ▸ hrT
  have sources i c (hc : Rd_entry_d i c Q) : ∃ X R K, Smem_d I c X R ∧ Ep_source_d I ω ω K X R := by
    obtain ⟨k, s, U, Q', G', P', hs, pack, hc⟩ := (qe i c).mp hc
    obtain ⟨_, _, st⟩ := read hs pack
    exact st.sources i c hc
  have diagram : It_diagram_d (kp_pair_l (ZF.modelsKP hZF)) ω α T Q G := by
    refine ⟨order, qf, qdom, fun i c hc => ?_, gf, gdom, ?_, ?_, ?_⟩
    · obtain ⟨X, R, _, mx, _⟩ := sources i c hc
      exact ⟨X, R, mx.1⟩
    · intro i j f c X R d Y W hf hc hd mx my
      obtain ⟨β, U, Q', G', P', hβ, hj', st⟩ := stage j (bounds hf).2.1
      have edge := gold hj' st hβ.predecessor_mem hf
      have hi := (st.diagram.order.bound i j (st.diagram.map_bound_l hZF edge)).1
      exact st.diagram.elementary i j f c X R d Y W edge ((qold hj' st hi).mp hc) ((qold hj' st hβ.predecessor_mem).mp hd) mx my
    · intro i f hf x y hxy
      obtain ⟨k, s, U, Q', G', P', hs, pack, hf⟩ := (edge i i f).mp hf
      obtain ⟨_, _, st⟩ := read hs pack
      exact st.diagram.identity i f hf x y hxy
    · intro i j k f g h hf hg hh x y z hxy hyz
      obtain ⟨β, U, Q', G', P', hβ, hk', st⟩ := stage k (bounds hg).2.1
      have g' := gold hk' st hβ.predecessor_mem hg
      have hj := (st.diagram.order.bound j k (st.diagram.map_bound_l hZF g')).1
      exact st.diagram.comp i j k f g h (gold hk' st hj hf) g' (gold hk' st hβ.predecessor_mem hh) x y z hxy hyz
  obtain ⟨o, ho⟩ := limit.2.1
  obtain ⟨_, _, _, _, _, _, _, first⟩ := stage o ho
  refine ⟨T, Q, G, P, ⟨⟨diagram, fun i j hj hij => (ts i j).mpr ⟨limit.1.transitive j hj i hij, hj, Or.inr hij⟩,
    sources, ?_⟩, ⟨first.returns.model, pf, pdom, ?_, ?_⟩⟩, fun _ _ _ _ _ hi => keep hi⟩
  · intro i c X R hc pair
    obtain ⟨k, s, U, Q', G', P', hs, pack, hc⟩ := (qe i c).mp hc
    obtain ⟨_, _, st⟩ := read hs pack
    exact st.count i c X R hc pair
  · intro i f c X R hf hc mx
    obtain ⟨β, U, Q', G', P', hβ, hi', st⟩ := stage i ((pdom i).mpr ⟨f, hf⟩)
    exact st.returns.elementary i f c X R ((pold hi' st hβ.predecessor_mem).mp hf) ((qold hi' st hβ.predecessor_mem).mp hc) mx
  · intro i j f u v hf hu hv x y z hxy hyz
    obtain ⟨β, U, Q', G', P', hβ, hj', st⟩ := stage j (bounds hf).2.1
    have edge := gold hj' st hβ.predecessor_mem hf
    have hi := (st.diagram.order.bound i j (st.diagram.map_bound_l hZF edge)).1
    exact st.returns.commute i j f u v edge ((pold hj' st hi).mp hu) ((pold hj' st hβ.predecessor_mem).mp hv) x y z hxy hyz

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 弱迭代的实际应答及其三种延拓

应答记录所选枝和下一行状态。后继步保留该枝的原商投影与根腿；
极限步保留整段历史的规范腿。合法性只用于证明这些实际应答存在。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

def Wi_tree_d (t T Q G E L : M.Domain) : Prop := ∃ p, KPair_d M p E L ∧ Rd_quad_d t T Q G p
def Wi_past_d (H Q G P : M.Domain) : Prop :=
  ∀ i U Q' G' P', Wi_at_d H i U Q' G' P' → Wi_keep_d Q' G' P' Q G P

def Wi_success_d (hZF : M.Models ZF) (ω α t B Q G : M.Domain) : Prop :=
  ∃ ξ T₀ Q₀ G₀ E₀ L₀ c N W F j, M.SuccessorOf α ξ ∧ Wi_tree_d t T₀ Q₀ G₀ E₀ L₀ ∧
    Rd_entry_d α c Q ∧ It_branch_d ω T₀ B ∧ Wi_limit_d hZF ω B Q₀ G₀ c N W F ∧
    It_map_d G ξ α j ∧ ∀ o, (∀ x, ¬ M.mem x o) → Rd_entry_d o j F

def Wi_continuous_d (hZF : M.Models ZF) (ω a A S α H Q' G' : M.Domain) : Prop :=
  ∃ T Q G P c N W F, Wi_state_d (kp_pair_l (ZF.modelsKP hZF)) ω α T Q G a A S P ∧ Wi_past_d H Q G P ∧
    Rd_entry_d α c Q' ∧ Wi_limit_d hZF ω α Q G c N W F ∧
    ∀ i j, M.mem i α → (It_map_d G' i α j ↔ Rd_entry_d i j F)


/-! 强证书层保留同一返回 witness 的树关系运输与目标良基性。
旧 `Wi_success_d`/`Wi_continuous_d` 保持公式接口不变，强层供 5.23
的实际分支消费。 -/
def Wi_success_tree_d (hZF : M.Models ZF) (ω α t B Q G : M.Domain) : Prop :=
  ∃ ξ T₀ Q₀ G₀ E₀ L₀ c N W F j, M.SuccessorOf α ξ ∧ Wi_tree_d t T₀ Q₀ G₀ E₀ L₀ ∧
    Rd_entry_d α c Q ∧ It_branch_d ω T₀ B ∧ It_wf_branch_d hZF ω ω T₀ Q₀ G₀ B ∧
    Wi_limit_d hZF ω B Q₀ G₀ c N W F ∧ Wi_limit_tree_d hZF ω B T₀ Q₀ G₀ c N W F ∧
    It_map_d G ξ α j ∧ ∀ o, (∀ x, ¬ M.mem x o) → Rd_entry_d o j F

variable (hZF : M.Models ZF)

theorem Wi_success_tree_d.to_success_d {ω α t B Q G : M.Domain}
    (h : Wi_success_tree_d hZF ω α t B Q G) : Wi_success_d hZF ω α t B Q G := by
  obtain ⟨ξ, T₀, Q₀, G₀, E₀, L₀, c, N, W, F, j, hs, tree, hc, branch, _, limit, _, edge, root⟩ := h
  exact ⟨ξ, T₀, Q₀, G₀, E₀, L₀, c, N, W, F, j, hs, tree, hc, branch,
    limit, edge, root⟩
def Wi_continuous_tree_d (hZF : M.Models ZF) (ω a A S α H Q' G' : M.Domain) : Prop :=
  ∃ T Q G P c N W F, Wi_state_d (kp_pair_l (ZF.modelsKP hZF)) ω α T Q G a A S P ∧ Wi_past_d H Q G P ∧
    Rd_entry_d α c Q' ∧ Wi_limit_d hZF ω α Q G c N W F ∧ Wi_limit_tree_d hZF ω α T Q G c N W F ∧
    It_wf_branch_d hZF ω α T Q G α ∧
    ∀ i j, M.mem i α → (It_map_d G' i α j ↔ Rd_entry_d i j F)


theorem Wi_continuous_tree_d.to_continuous_d
    {ω a A S α H Q' G' : M.Domain}
    (h : Wi_continuous_tree_d hZF ω a A S α H Q' G') :
    Wi_continuous_d hZF ω a A S α H Q' G' := by
  obtain ⟨T, Q, G, P, c, N, W, F, state, past, hc, limit, _, _, edges⟩ := h
  exact ⟨T, Q, G, P, c, N, W, F, state, past, hc, limit, edges⟩
/-! 强应答记录同时保留成功分支或连续极限的完整树证书。 -/
def Wi_answer_tree_d (hZF : M.Models ZF) (ω a A S o s₀ α H t B s : M.Domain) : Prop :=
  ∃ β T Q G P, M.SuccessorOf β α ∧ Rd_quad_d s T Q G P ∧
    Wi_state_d (kp_pair_l (ZF.modelsKP hZF)) ω β T Q G a A S P ∧ Wi_past_d H Q G P ∧
    ((α = o ∧ B = o ∧ s = s₀) ∨ Wi_success_tree_d hZF ω α t B Q G ∨
      (M.IsLimitOrdinal α ∧ B = o ∧ Wi_continuous_tree_d hZF ω a A S α H Q G))
def Wi_answer_d (hZF : M.Models ZF) (ω a A S o s₀ α H t B s : M.Domain) : Prop :=
  ∃ β T Q G P, M.SuccessorOf β α ∧ Rd_quad_d s T Q G P ∧ Wi_state_d (kp_pair_l (ZF.modelsKP hZF)) ω β T Q G a A S P ∧
    Wi_past_d H Q G P ∧ ((α = o ∧ B = o ∧ s = s₀) ∨ Wi_success_d hZF ω α t B Q G ∨
      (M.IsLimitOrdinal α ∧ B = o ∧ Wi_continuous_d hZF ω a A S α H Q G))

theorem Wi_answer_tree_d.to_answer_d
    {ω a A S o s₀ α H t B s : M.Domain}
    (h : Wi_answer_tree_d hZF ω a A S o s₀ α H t B s) :
    Wi_answer_d hZF ω a A S o s₀ α H t B s := by
  obtain ⟨β, T, Q, G, P, succ, pack, state, past, cases⟩ := h
  rcases cases with root | success | continuous
  · exact ⟨β, T, Q, G, P, succ, pack, state, past, Or.inl root⟩
  · exact ⟨β, T, Q, G, P, succ, pack, state, past,
      Or.inr (Or.inl success.to_success_d)⟩
  · exact ⟨β, T, Q, G, P, succ, pack, state, past,
      Or.inr (Or.inr ⟨continuous.1, continuous.2.1, continuous.2.2.to_continuous_d⟩)⟩
variable (hZF : M.Models ZF)

theorem Wi_history_d.last_keep_l {ω a A S α D H ξ T Q G P : M.Domain}
    (hist : Wi_history_d hZF ω a A S α D H) (hα : M.SuccessorOf α ξ) (last : Wi_at_d H ξ T Q G P) :
    Wi_past_d H Q G P := by
  intro i U Q' G' P' hi
  obtain ⟨s, hs, ps⟩ := hi
  rcases (hα i).mp (hist.function.bound_l hs).1 with hi | eq
  · exact hist.past i ξ U Q' G' P' T Q G P hi ⟨s, hs, ps⟩ last
  · have eq := hZF.1.eq_of_same_members i ξ eq
    subst i
    obtain ⟨t, ht, pt⟩ := last
    have eq := (fn0_function_l (ZF.modelsKP hZF) hist.function).1.2 ξ s t hs ht
    obtain ⟨rfl, rfl, rfl, rfl⟩ := (eq ▸ ps).unique_l pt
    exact Wi_keep_d.refl_l Q' G' P'

theorem wi_answer_root_l {ω a A S o s₀ α D H t T Q G P : M.Domain}
    (ho : ∀ x, ¬ M.mem x o) (hα : M.SuccessorOf α o) (pack : Rd_quad_d s₀ T Q G P)
    (state : Wi_state_d (kp_pair_l (ZF.modelsKP hZF)) ω α T Q G a A S P) (hist : Wi_history_d hZF ω a A S o D H) :
    Wi_answer_d hZF ω a A S o s₀ o H t o s₀ :=
  ⟨α, T, Q, G, P, hα, pack, state, fun i _ _ _ _ ⟨_, hs, _⟩ => (ho i (hist.function.bound_l hs).1).elim,
    Or.inl ⟨rfl, rfl, rfl⟩⟩

theorem wi_answer_tree_root_l {ω a A S o s₀ α D H t T Q G P : M.Domain}
    (ho : ∀ x, ¬ M.mem x o) (hα : M.SuccessorOf α o) (pack : Rd_quad_d s₀ T Q G P)
    (state : Wi_state_d (kp_pair_l (ZF.modelsKP hZF)) ω α T Q G a A S P) (hist : Wi_history_d hZF ω a A S o D H) :
    Wi_answer_tree_d hZF ω a A S o s₀ o H t o s₀ :=
  ⟨α, T, Q, G, P, hα, pack, state,
    fun i _ _ _ _ ⟨_, hs, _⟩ => (ho i (hist.function.bound_l hs).1).elim,
    Or.inl ⟨rfl, rfl, rfl⟩⟩

variable (hZFC : M.Models ZFC)
local notation "hZF'" => ZFC.models_zf_l hZFC
local notation "I" => kp_pair_l (ZF.modelsKP hZF')

theorem wi_answer_successor_l {ω a A S o s₀ α D H ξ T Q G P θ c t T₀ Q₀ G₀ E₀ L₀ : M.Domain}
    (hist : Wi_history_d hZF' ω a A S α D H) (hα : M.SuccessorOf α ξ)
    (last : Wi_at_d H ξ T Q G P) (hc : Rd_entry_d ξ c Q) (pack : Wi_tree_d t T₀ Q₀ G₀ E₀ L₀)
    (nice : It_nice_d hZF' ω c ω T₀ Q₀ G₀ E₀ L₀) (rank : V_d I θ A) (ma : Smem_d I a A S) :
    ∃ B s, Wi_answer_d hZF' ω a A S o s₀ α H t B s := by
  obtain ⟨α', hα', state⟩ := hist.at_l hZF' last
  have eq := Structure.SuccessorOf.eq hZF'.1 hα' hα
  subst α'
  obtain ⟨β, U, Q', G', P', B, d, N, W, F, σ, j, next, extension, hd, _, branch, _, limit, _, edge, root⟩ :=
    state.successor_l hZFC rank ma hα hc nice.tree (nice.toIt_pnice_d.copyable_l hZFC)
  obtain ⟨s, ps⟩ := rd_quad_exists_l (ZF.modelsKP hZF') U Q' G' P'
  have keep := extension.keep_l hZF' state
  exact ⟨B, s, β, U, Q', G', P', extension.1, ps, next,
    fun i V Q₁ G₁ P₁ hi => (hist.last_keep_l hZF' hα last i V Q₁ G₁ P₁ hi).trans_l keep,
    Or.inr (Or.inl ⟨ξ, T₀, Q₀, G₀, E₀, L₀, d, N, W, F, j, hα, pack, hd, branch, limit, edge, root⟩)⟩

/-! 后继应答的强证书出口。它与旧 `Wi_success_d` 共享同一 producer，
只额外保留返回树枝、`L↔T` 运输和极限良基性。 -/
theorem wi_success_tree_successor_l {ω a A S α D H ξ T Q G P θ c t T₀ Q₀ G₀ E₀ L₀ : M.Domain}
    (hist : Wi_history_d hZF' ω a A S α D H) (hα : M.SuccessorOf α ξ)
    (last : Wi_at_d H ξ T Q G P) (hc : Rd_entry_d ξ c Q) (pack : Wi_tree_d t T₀ Q₀ G₀ E₀ L₀)
    (nice : It_nice_d hZF' ω c ω T₀ Q₀ G₀ E₀ L₀) (rank : V_d I θ A) (ma : Smem_d I a A S) :
    ∃ B Q' G', Wi_success_tree_d hZF' ω α t B Q' G' := by
  obtain ⟨α', hα', state⟩ := hist.at_l hZF' last
  have eq := Structure.SuccessorOf.eq hZF'.1 hα' hα
  subst α'
  obtain ⟨β, U, Q', G', P', B, d, N, W, F, σ, j, next, extension, hd, _, branch,
    wfBranch, limit, strong, edge, root⟩ := state.successor_l hZFC rank ma hα hc nice.tree (nice.toIt_pnice_d.copyable_l hZFC)
  exact ⟨B, Q', G', ξ, T₀, Q₀, G₀, E₀, L₀, d, N, W, F, j, hα, pack, hd,
    branch, wfBranch, limit, strong, edge, root⟩

/-! 连续极限路径的强证书出口。 -/
theorem wi_continuous_tree_limit_l {ω a A S α D H : M.Domain}
    (hist : Wi_history_d hZF' ω a A S α D H) (limit : M.IsLimitOrdinal α)
    (count : M.CardinalLessOrEqual I α ω) (ma : Smem_d I a A S) :
    ∃ Q' G', Wi_continuous_tree_d hZF' ω a A S α H Q' G' := by
  obtain ⟨T, Q, G, P, state, past⟩ := hist.union_l hZF' limit
  obtain ⟨β, U, Q', G', P', c, N, W, F, σ, next, extension, hc, _, lim, strong,
    wfBranch, _, edges, _⟩ := state.limit_l hZFC ma limit count
  exact ⟨Q', G', T, Q, G, P, c, N, W, F, state, past, hc, lim, strong,
    wfBranch, edges⟩
/-! 强应答的两条实际构造出口。 -/
theorem wi_answer_tree_successor_l {ω a A S o s₀ α D H ξ T Q G P θ c t T₀ Q₀ G₀ E₀ L₀ : M.Domain}
    (hist : Wi_history_d hZF' ω a A S α D H) (hα : M.SuccessorOf α ξ)
    (last : Wi_at_d H ξ T Q G P) (hc : Rd_entry_d ξ c Q) (pack : Wi_tree_d t T₀ Q₀ G₀ E₀ L₀)
    (nice : It_nice_d hZF' ω c ω T₀ Q₀ G₀ E₀ L₀) (rank : V_d I θ A) (ma : Smem_d I a A S) :
    ∃ B s, Wi_answer_tree_d hZF' ω a A S o s₀ α H t B s := by
  obtain ⟨α', hα', state⟩ := hist.at_l hZF' last
  have eq := Structure.SuccessorOf.eq hZF'.1 hα' hα
  subst α'
  obtain ⟨β, U, Q', G', P', B, d, N, W, F, σ, j, next, extension, hd, _, branch,
    wfBranch, limit, strong, edge, root⟩ := state.successor_l hZFC rank ma hα hc nice.tree (nice.toIt_pnice_d.copyable_l hZFC)
  obtain ⟨s, ps⟩ := rd_quad_exists_l (ZF.modelsKP hZF') U Q' G' P'
  have keep := extension.keep_l hZF' state
  exact ⟨B, s, β, U, Q', G', P', extension.1, ps, next,
    fun i V Q₁ G₁ P₁ hi => (hist.last_keep_l hZF' hα last i V Q₁ G₁ P₁ hi).trans_l keep,
    Or.inr (Or.inl ⟨ξ, T₀, Q₀, G₀, E₀, L₀, d, N, W, F, j, hα, pack, hd,
      branch, wfBranch, limit, strong, edge, root⟩)⟩

theorem wi_answer_tree_limit_l {ω a A S o s₀ α D H t : M.Domain}
    (hist : Wi_history_d hZF' ω a A S α D H) (limit : M.IsLimitOrdinal α)
    (count : M.CardinalLessOrEqual I α ω) (ma : Smem_d I a A S) :
    ∃ s, Wi_answer_tree_d hZF' ω a A S o s₀ α H t o s := by
  obtain ⟨T, Q, G, P, state, past⟩ := hist.union_l hZF' limit
  obtain ⟨β, U, Q', G', P', c, N, W, F, σ, next, extension, hc, _, lim, strong,
    wfBranch, _, edges, _⟩ := state.limit_l hZFC ma limit count
  obtain ⟨s, ps⟩ := rd_quad_exists_l (ZF.modelsKP hZF') U Q' G' P'
  exact ⟨s, β, U, Q', G', P', extension.1, ps, next,
    fun i V Q₁ G₁ P₁ hi => (past i V Q₁ G₁ P₁ hi).trans_l (extension.keep_l hZF' state),
    Or.inr (Or.inr ⟨limit, rfl, T, Q, G, P, c, N, W, F, state, past, hc, lim,
      strong, wfBranch, edges⟩)⟩
theorem wi_answer_limit_l {ω a A S o s₀ α D H t : M.Domain}
    (hist : Wi_history_d hZF' ω a A S α D H) (limit : M.IsLimitOrdinal α)
    (count : M.CardinalLessOrEqual I α ω) (ma : Smem_d I a A S) :
    ∃ s, Wi_answer_d hZF' ω a A S o s₀ α H t o s := by
  obtain ⟨T, Q, G, P, state, past⟩ := hist.union_l hZF' limit
  obtain ⟨β, U, Q', G', P', c, N, W, F, σ, next, extension, hc, _, lim, _, _, _, edges, _⟩ :=
    state.limit_l hZFC ma limit count
  obtain ⟨s, ps⟩ := rd_quad_exists_l (ZF.modelsKP hZF') U Q' G' P'
  exact ⟨s, β, U, Q', G', P', extension.1, ps, next,
    fun i V Q₁ G₁ P₁ hi => (past i V Q₁ G₁ P₁ hi).trans_l (extension.keep_l hZF' state),
    Or.inr (Or.inr ⟨limit, rfl, T, Q, G, P, c, N, W, F, state, past, hc, lim, edges⟩)⟩

end YesMetaZFC.SetTheory.LargeCardinal
