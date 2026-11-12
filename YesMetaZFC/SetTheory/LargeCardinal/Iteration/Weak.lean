import YesMetaZFC.SetTheory.LargeCardinal.Iteration.WeakAnswer
import YesMetaZFC.SetTheory.HereditaryFunction
import YesMetaZFC.SetTheory.LargeCardinal.Iteration.WeakAnswerTreeSyntax
import YesMetaZFC.SetTheory.DependentChoice
import YesMetaZFC.SetTheory.HereditaryCover

/-! # 弱迭代状态属于同一个实际集合包络

可数传递模型、其结构码及小定义域上的整张箭头图均属于正则 Hχ。
返回目标只需属于该包络；因此所有可数长度状态统一有界，可使用对象选择。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZFC : M.Models ZFC)
local notation "hZF" => ZFC.models_zf_l hZFC
local notation "I" => kp_pair_l (ZF.modelsKP hZF)
variable {ω χ Z : M.Domain} (hω : M.IsOmega ω)
  (hχ : M.IsRegularCardinal (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) χ)
  (hωχ : M.mem ω χ) (hZ : H_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) χ Z)
include hZFC hω hχ hωχ hZ

theorem it_model_mem_l {c X R : M.Domain} (model : Smdl_d I c X R)
    (trans : M.TransitiveSet X) (count : M.CardinalLessOrEqual I X ω) : M.mem c Z ∧ M.mem X Z ∧ M.mem R Z := by
  have hx := (hZ X).mpr (ZF.hmem_of_subset_l I hZF hχ.isLimitOrdinal trans (fun _ h => h) hωχ count)
  have hr := ZFC.h_relation_l hZFC hω hχ hωχ hZ hx hx (R := R) (by
    intro p hp
    obtain ⟨x, y, pair⟩ := model.2.2.1 p hp
    have bound := model.2.2.2 x y ⟨p, pair, hp⟩
    exact ⟨x, bound.1, y, bound.2, pair⟩)
  exact ⟨ZFC.h_kpair_l hZFC hω hχ hωχ hZ model.1 hx hr, hx, hr⟩

theorem It_diagram_d.h_mem_l {α T Q G : M.Domain} (diagram : It_diagram_d (kp_pair_l (ZF.modelsKP hZF)) ω α T Q G)
    (hα : M.mem α Z) (models : ∀ i c, Rd_entry_d i c Q → ∃ X R,
      Smdl_d I c X R ∧ M.TransitiveSet X ∧ M.CardinalLessOrEqual I X ω) : M.mem T Z ∧ M.mem Q Z ∧ M.mem G Z := by
  have zt := ZF.h_transitive_l I hZF hZ
  have model {i c} (hc : Rd_entry_d i c Q) : ∃ X R, Smdl_d I c X R ∧ M.mem c Z ∧ M.mem X Z := by
    obtain ⟨X, R, mx, trans, count⟩ := models i c hc
    have owned := it_model_mem_l hZFC hω hχ hωχ hZ mx trans count
    exact ⟨X, R, mx, owned.1, owned.2.1⟩
  have ht := ZFC.h_relation_l hZFC hω hχ hωχ hZ hα hα (R := T) (by
    intro p hp
    obtain ⟨i, j, pair⟩ := diagram.order.relation p hp
    have ij := diagram.order.bound i j ⟨p, pair, hp⟩
    exact ⟨i, ij.1, j, ij.2, pair⟩)
  have hq := ZFC.h_function_l hZFC hω hχ hωχ hZ hα (F := Q) ⟨diagram.model_function, diagram.model_domain, fun i hi => by
    obtain ⟨c, hc⟩ := (diagram.model_domain i).mp hi
    obtain ⟨_, _, _, owned, _⟩ := model hc
    exact ⟨c, owned, hc⟩⟩
  refine ⟨ht, hq, ZFC.h_function_l hZFC hω hχ hωχ hZ ht ⟨diagram.map_function, diagram.map_domain, ?_⟩⟩
  intro r hr
  obtain ⟨f, hf⟩ := (diagram.map_domain r).mp hr
  obtain ⟨i, j, pair⟩ := diagram.order.relation r hr
  have ij := diagram.order.bound i j ⟨r, pair, hr⟩
  obtain ⟨c, hc⟩ := (diagram.model_domain i).mp ij.1
  obtain ⟨d, hd⟩ := (diagram.model_domain j).mp ij.2
  obtain ⟨X, R, mx, _, hx⟩ := model hc
  obtain ⟨Y, W, my, _, hy⟩ := model hd
  have ff := (diagram.elementary i j f c X R d Y W ⟨r, pair, hf⟩ hc hd mx my).1.1
  exact ⟨f, ZFC.h_function_l hZFC hω hχ hωχ hZ hx
    ⟨ff.1, ff.2.1, fun x hx' => (ff.2.2 x hx').imp fun y hy' => ⟨zt Y hy y hy'.1, hy'.2⟩⟩, hf⟩

theorem Wi_state_d.mem_l {α T Q G a A S P s : M.Domain} (state : Wi_state_d (kp_pair_l (ZF.modelsKP hZF)) ω α T Q G a A S P)
    (hα : M.mem α Z) (hA : M.mem A Z) (pack : Rd_quad_d s T Q G P) : M.mem s Z := by
  have zt := ZF.h_transitive_l I hZF hZ
  have models i c (hc : Rd_entry_d i c Q) : ∃ X R,
      Smdl_d I c X R ∧ M.TransitiveSet X ∧ M.CardinalLessOrEqual I X ω := by
    obtain ⟨X, R, _, mx, source⟩ := state.sources i c hc
    exact ⟨X, R, mx.1, source.transitive, state.count i c X R hc mx.1.1⟩
  obtain ⟨ht, hq, hg⟩ := state.diagram.h_mem_l hZFC hω hχ hωχ hZ hα models
  have hp := ZFC.h_function_l hZFC hω hχ hωχ hZ hα (F := P) ⟨state.returns.function, state.returns.domain, fun i hi => by
    obtain ⟨f, hf⟩ := (state.returns.domain i).mp hi
    obtain ⟨c, hc⟩ := (state.diagram.model_domain i).mp hi
    obtain ⟨X, R, mx, trans, count⟩ := models i c hc
    have owned := it_model_mem_l hZFC hω hχ hωχ hZ mx trans count
    have ff := (state.returns.elementary i f c X R hf hc mx).1.1
    exact ⟨f, ZFC.h_function_l hZFC hω hχ hωχ hZ owned.2.1
      ⟨ff.1, ff.2.1, fun x hx => (ff.2.2 x hx).imp fun y hy => ⟨zt A hA y hy.1, hy.2⟩⟩, hf⟩⟩
  obtain ⟨p, pp, q, pq, code⟩ := pack
  exact ZFC.h_kpair_l hZFC hω hχ hωχ hZ code ht (ZFC.h_kpair_l hZFC hω hχ hωχ hZ pq hq
    (ZFC.h_kpair_l hZFC hω hχ hωχ hZ pp hg hp))

/-- 任意实际 nice ω 树都在同一包络中，合法走法没有额外大小限制。 -/
theorem Wi_tree_d.mem_l {t c X R T Q G E L : M.Domain} (hωZ : M.mem ω Z)
    (pack : Wi_tree_d t T Q G E L) (nice : It_nice_d hZF ω c ω T Q G E L)
    (mx : Smem_d I c X R) (count : M.CardinalLessOrEqual I X ω) : M.mem t Z := by
  have zt := ZF.h_transitive_l I hZF hZ
  have actual i d (hd : Rd_entry_d i d Q) : ∃ Y W K, Smem_d I d Y W ∧ Ep_source_d I ω ω K Y W := by
    obtain ⟨j,succ,hj⟩ := hω.1.2 i ((nice.tree.diagram.model_domain i).mpr ⟨d,hd⟩)
    obtain ⟨p,hp⟩ := (nice.tree.move_domain i).mpr ⟨j,hj,succ⟩
    obtain ⟨κ,ρ,F,pay⟩ := nice.active i p hp
    obtain ⟨a,Y,W,ha,my,yt,_,_⟩ := nice.exactness i p κ ρ F hp pay
    have eq := nice.tree.diagram.model_function.2 i a d ha hd
    subst a
    exact (nice.tree.sources i d hd).mem_l hZF ⟨Y,W,my,yt⟩
  have counts := it_countable_l hZF nice.tree mx.1 count
  have models i d (hd : Rd_entry_d i d Q) : ∃ Y W,
      Smdl_d I d Y W ∧ M.TransitiveSet Y ∧ M.CardinalLessOrEqual I Y ω := by
    obtain ⟨Y, W, _, my, source⟩ := actual i d hd
    exact ⟨Y, W, my.1, source.transitive, counts i d Y W hd my.1.1⟩
  obtain ⟨ht, hq, hg⟩ := nice.tree.diagram.h_mem_l hZFC hω hχ hωχ hZ hωZ models
  have step i (hi : M.mem i ω) : ∃ p ρ, Rd_entry_d i p E ∧ Rd_entry_d i ρ L ∧ M.mem p Z ∧ M.mem ρ Z := by
    obtain ⟨j, sj, hj⟩ := hω.1.2 i hi
    obtain ⟨_,d,_,_,_,p,κ,ρ,F,Y,W,_,_,_,hd,_,_,_,hp,pay,my,yt,_,active,_,_,hρ⟩ := nice.step_l hZF hj sj
    have loc := active.local_mem_l hZF hω yt my pay
    obtain ⟨Y', W', _, my', source⟩ := actual i d hd
    obtain ⟨rfl, rfl⟩ := smdl_unique_l I my'.1 my.1
    have hy := (it_model_mem_l hZFC hω hχ hωχ hZ my.1 source.transitive (counts i d Y' W' hd my.1.1)).2.1
    obtain ⟨q, pq, qf⟩ := pay
    have hκ := zt _ hy _ loc.2.1
    have hρZ := zt _ hy _ loc.2.2.1
    have hF := zt _ hy _ loc.2.2.2.1
    exact ⟨p, ρ, hp, hρ, ZFC.h_kpair_l hZFC hω hχ hωχ hZ pq hκ
      (ZFC.h_kpair_l hZFC hω hχ hωχ hZ qf hρZ hF), hρZ⟩
  have ed i : (∃ p, Rd_entry_d i p E) ↔ M.mem i ω := (nice.tree.move_domain i).trans
    ⟨fun ⟨j, hj, sj⟩ => (hω.isOrdinal (ZF.modelsKP hZF)).transitive j hj i sj.predecessor_mem,
      fun hi => (hω.1.2 i hi).imp fun j ⟨sj, hj⟩ => ⟨hj, sj⟩⟩
  have he := ZFC.h_function_l hZFC hω hχ hωχ hZ hωZ (F := E) ⟨nice.tree.move_function, fun i => (ed i).symm,
    fun i hi => (step i hi).elim fun p ⟨_, hp, _, owned, _⟩ => ⟨p, owned, hp⟩⟩
  have hl := ZFC.h_function_l hZFC hω hχ hωχ hZ hωZ (F := L) ⟨nice.function, fun i => ⟨
    fun hi => (step i hi).elim fun _ ⟨ρ, _, hρ, _⟩ => ⟨ρ, hρ⟩,
    fun ⟨ρ, hρ⟩ => ((nice.levels i ρ).mp hρ).elim fun p ⟨_, _, hp, _⟩ => (ed i).mp ⟨p, hp⟩⟩,
    fun i hi => (step i hi).elim fun _ ⟨ρ, _, hρ, _, owned⟩ => ⟨ρ, owned, hρ⟩⟩
  obtain ⟨p, pp, q, pq, r, pr, code⟩ := pack
  exact ZFC.h_kpair_l hZFC hω hχ hωχ hZ code ht (ZFC.h_kpair_l hZFC hω hχ hωχ hZ pr hq
    (ZFC.h_kpair_l hZFC hω hχ hωχ hZ pq hg (ZFC.h_kpair_l hZFC hω hχ hωχ hZ pp he hl)))

theorem Wi_answer_d.mem_l {a A S o s₀ α H t B s : M.Domain} (hωZ : M.mem ω Z)
    (hA : M.mem A Z) (ho : ∀ x, ¬ M.mem x o) (next : ∀ β, M.SuccessorOf β α → M.mem β Z)
    (answer : Wi_answer_d hZF ω a A S o s₀ α H t B s) : M.mem B Z ∧ M.mem s Z := by
  obtain ⟨β, T, Q, G, P, hβ, pack, state, _, cases⟩ := answer
  have sub : M.MemberSubset B ω := by
    rcases cases with ⟨_, eq, _⟩ | step | ⟨_, eq, _⟩
    · exact fun x hx => (ho x (eq ▸ hx)).elim
    · obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, branch, _⟩ := step
      exact branch.subset
    · exact fun x hx => (ho x (eq ▸ hx)).elim
  exact ⟨ZF.h_subsets_l I hZF hχ.isLimitOrdinal hZ hωZ B sub,
    state.mem_l hZFC hω hχ hωχ hZ (next β hβ) hA pack⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 同一集合上的实际应答选择函数

有可用应答时选择真实枝及下一状态；仅在没有应答时取固定初始值。
后续合法博弈的归纳将逐步排除后一个分支。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)

def Wi_request_d (ω a A S o s₀ r u : M.Domain) : Prop := ∃ α H t B s,
  Rd_triple_d r α H t ∧ KPair_d M u B s ∧ Wi_answer_d hZF ω a A S o s₀ α H t B s
def wi_request_m {d} (ω a A S o s₀ r u : Term d) : Formula 1 d := set[d] ⟪
  ∃ α H t B s, ⌜rd_triple0_m⌝ₚ(⌜r⌝ₛ, α, H, t) ∧ ⌜kpair0_m⌝ₚ(⌜u⌝ₛ, B, s) ∧
    ⌜wi_answer_m⌝ₚ(⌜ω⌝ₛ, ⌜a⌝ₛ, ⌜A⌝ₛ, ⌜S⌝ₛ, ⌜o⌝ₛ, ⌜s₀⌝ₛ, α, H, t, B, s)⟫
derive_free_closed wi_request_m
theorem wi_request_sat_l {d} (η : Env M d) (ω a A S o s₀ r u : Term d) :
    Formula.satisfies η (wi_request_m ω a A S o s₀ r u) ↔ Wi_request_d hZF
      (ω.eval η) (a.eval η) (A.eval η) (S.eval η) (o.eval η) (s₀.eval η) (r.eval η) (u.eval η) := by
  simp only [wi_request_m, Wi_request_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    rd_triple0_sat_l hZF.1, kpair0_sat_l hZF.1, wi_answer_sat_l hZF, Definitional.Term.eval_weaken]; rfl

structure Wi_selector_d (ω a A S o s₀ Z Ψ : M.Domain) : Prop where
  function : Fn0_d Z Z Ψ
  values : ∀ r u, Rd_entry_d r u Ψ → ∃ B s, KPair_d M u B s
  selects : ∀ r u, Rd_entry_d r u Ψ →
    (∃ v, M.mem v Z ∧ Wi_request_d hZF ω a A S o s₀ r v) → Wi_request_d hZF ω a A S o s₀ r u

theorem Wi_selector_d.answer_l {ω a A S o s₀ Z Ψ r u α H t B s : M.Domain}
    (h : Wi_selector_d hZF ω a A S o s₀ Z Ψ) (hr : Rd_triple_d r α H t) (hu : KPair_d M u B s)
    (edge : Rd_entry_d r u Ψ) (available : ∃ v, M.mem v Z ∧ Wi_request_d hZF ω a A S o s₀ r v) :
    Wi_answer_d hZF ω a A S o s₀ α H t B s := by
  obtain ⟨β, H', t', B', s', request, response, answer⟩ := h.selects r u edge available
  obtain ⟨rfl, rfl, rfl⟩ := request.unique_l hr
  obtain ⟨rfl, rfl⟩ := kpair_injective_l M response hu
  exact answer

/-! 强请求/选择层只消费实际强应答证书。其存在性仍需后续把强关系内部公式化，
这里先提供严格可调用接口和到旧选择层的投影。 -/
def Wi_request_tree_d (ω a A S o s₀ r u : M.Domain) : Prop := ∃ α H t B s,
  Rd_triple_d r α H t ∧ KPair_d M u B s ∧ Wi_answer_tree_d hZF ω a A S o s₀ α H t B s

theorem Wi_request_tree_d.to_request_d {ω a A S o s₀ r u : M.Domain}
    (h : Wi_request_tree_d hZF ω a A S o s₀ r u) :
    Wi_request_d hZF ω a A S o s₀ r u := by
  obtain ⟨α, H, t, B, s, hr, hu, ha⟩ := h
  exact ⟨α, H, t, B, s, hr, hu, ha.to_answer_d⟩

structure Wi_selector_tree_d (ω a A S o s₀ Z Ψ : M.Domain) : Prop where
  function : Fn0_d Z Z Ψ
  values : ∀ r u, Rd_entry_d r u Ψ → ∃ B s, KPair_d M u B s
  selects : ∀ r u, Rd_entry_d r u Ψ →
    (∃ v, M.mem v Z ∧ Wi_request_tree_d hZF ω a A S o s₀ r v) →
      Wi_request_tree_d hZF ω a A S o s₀ r u

theorem Wi_selector_tree_d.answer_l {ω a A S o s₀ Z Ψ r u α H t B s : M.Domain}
    (h : Wi_selector_tree_d hZF ω a A S o s₀ Z Ψ) (hr : Rd_triple_d r α H t)
    (hu : KPair_d M u B s) (edge : Rd_entry_d r u Ψ)
    (available : ∃ v, M.mem v Z ∧ Wi_request_tree_d hZF ω a A S o s₀ r v) :
    Wi_answer_tree_d hZF ω a A S o s₀ α H t B s := by
  obtain ⟨β, H', t', B', s', request, response, answer⟩ := h.selects r u edge available
  obtain ⟨rfl, rfl, rfl⟩ := request.unique_l hr
  obtain ⟨rfl, rfl⟩ := kpair_injective_l M response hu
  exact answer

/-! 若调用方提供强请求关系及其回退选择公式，ZFC 的同一 uniformization
直接生成强 selector。 -/
theorem wi_selector_tree_exists_of_formula_l
    (hZFC : M.Models ZFC) {ω a A S o s₀ Z u₀ : M.Domain}
    (hu₀ : M.mem u₀ Z) (pair : KPair_d M u₀ o s₀)
    {d} (φ : BinarySchema d) (η : Env M d)
    (sat : ∀ r u, φ.denote η r u ↔
      Wi_request_tree_d (ZFC.models_zf_l hZFC) ω a A S o s₀ r u ∨
        (u = u₀ ∧ ¬ ∃ v, M.mem v Z ∧
          Wi_request_tree_d (ZFC.models_zf_l hZFC) ω a A S o s₀ r v)) :
    ∃ Ψ, Wi_selector_tree_d (ZFC.models_zf_l hZFC) ω a A S o s₀ Z Ψ := by
  classical
  let hZF := ZFC.models_zf_l hZFC
  let I := kp_pair_l (ZF.modelsKP hZF)
  obtain ⟨Ψ, hf, selects⟩ := ZFC.uniformize_formula_l I hZFC φ η
    (X := Z) (Y := Z) (fun r _ => by
      by_cases good : ∃ v, M.mem v Z ∧ Wi_request_tree_d hZF ω a A S o s₀ r v
      · obtain ⟨u, hu, answer⟩ := good
        exact ⟨u, hu, (sat r u).mpr (Or.inl answer)⟩
      · exact ⟨u₀, hu₀, (sat r u₀).mpr (Or.inr ⟨rfl, good⟩)⟩)
  refine ⟨Ψ, fn0_of_function_l (ZF.modelsKP hZF) hf, ?_, ?_⟩
  · intro r u edge
    rcases (sat r u).mp (selects r u edge) with ⟨_, _, _, B, s, _, pu, _⟩ | ⟨eq, _⟩
    · exact ⟨B, s, pu⟩
    · exact ⟨o, s₀, eq.symm ▸ pair⟩
  · intro r u edge available
    exact ((sat r u).mp (selects r u edge)).elim id
      (fun hh => (hh.2 available).elim)
def wi_select_m {d} (ω a A S o s₀ Z u₀ r u : Term d) : Formula 1 d := set[d] ⟪
  ⌜wi_request_m⌝ₚ(⌜ω⌝ₛ, ⌜a⌝ₛ, ⌜A⌝ₛ, ⌜S⌝ₛ, ⌜o⌝ₛ, ⌜s₀⌝ₛ, ⌜r⌝ₛ, ⌜u⌝ₛ) ∨
  (⌜u⌝ₛ = ⌜u₀⌝ₛ ∧ ¬ (∃ v ∈ ⌜Z⌝ₛ, ⌜wi_request_m⌝ₚ(⌜ω⌝ₛ, ⌜a⌝ₛ, ⌜A⌝ₛ, ⌜S⌝ₛ, ⌜o⌝ₛ, ⌜s₀⌝ₛ, ⌜r⌝ₛ, v)))⟫
derive_free_closed wi_select_m

/-- 原选择公理在实际 Z 上一次选择所有可用应答，不使用元层数据选择。 -/
theorem wi_selector_exists_l (hZFC : M.Models ZFC) {ω a A S o s₀ Z u₀ : M.Domain}
    (hu₀ : M.mem u₀ Z) (pair : KPair_d M u₀ o s₀) :
    ∃ Ψ, Wi_selector_d (ZFC.models_zf_l hZFC) ω a A S o s₀ Z Ψ := by
  classical
  let hZF := ZFC.models_zf_l hZFC
  let I := kp_pair_l (ZF.modelsKP hZF)
  let η : Env M 8 := (((((((⟨fun _ => ω, fun _ => ω⟩ : Env M 1).push a).push A).push S).push o).push s₀).push Z).push u₀
  let φ : BinarySchema 8 := { body := (wi_select_m (.bound 9) (.bound 8) (.bound 7) (.bound 6)
    (.bound 5) (.bound 4) (.bound 3) (.bound 2) (.bound 1) .newest) }
  have sat r u : φ.denote η r u ↔ Wi_request_d hZF ω a A S o s₀ r u ∨
      (u = u₀ ∧ ¬ ∃ v, M.mem v Z ∧ Wi_request_d hZF ω a A S o s₀ r v) := by
    simp only [φ, BinarySchema.denote, wi_select_m, Formula.satisfies_disj_iff, Formula.satisfies_conj_iff,
      Formula.satisfies_extensionalEq_iff_eq hZF.1, Formula.satisfies_neg_iff, Formula.satisfies_existsMem_iff,
      wi_request_sat_l hZF, Definitional.Term.eval_weaken]; rfl
  obtain ⟨Ψ, hf, selects⟩ := ZFC.uniformize_formula_l I hZFC φ η (X := Z) (Y := Z) (fun r _ => by
    by_cases good : ∃ v, M.mem v Z ∧ Wi_request_d hZF ω a A S o s₀ r v
    · obtain ⟨u, hu, answer⟩ := good
      exact ⟨u, hu, (sat r u).mpr (Or.inl answer)⟩
    · exact ⟨u₀, hu₀, (sat r u₀).mpr (Or.inr ⟨rfl, good⟩)⟩)
  refine ⟨Ψ, fn0_of_function_l (ZF.modelsKP hZF) hf, ?_, ?_⟩
  · intro r u edge
    rcases (sat r u).mp (selects r u edge) with ⟨_, _, _, B, s, _, pu, _⟩ | ⟨eq, _⟩
    · exact ⟨B, s, pu⟩
    · exact ⟨o, s₀, eq.symm ▸ pair⟩
  · intro r u edge available
    exact ((sat r u).mp (selects r u edge)).elim id (fun hh => (hh.2 available).elim)

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 应答函数驱动的唯一超限运行

后继阶段只读取此前的一个走法，零和极限阶段使用空标记。
递归值是应答的状态分量，所选枝仍可由同一请求重新读取。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

def Wi_input_d (o F α t : M.Domain) : Prop :=
  (∃ ξ, M.SuccessorOf α ξ ∧ Rd_entry_d ξ t F) ∨ ((∀ ξ, ¬ M.SuccessorOf α ξ) ∧ t = o)
def wi_input_m {d} (o F α t : Term d) : Formula 1 d := set[d] ⟪
  (∃ ξ, ⌜KP.succ0_m⌝ₚ(⌜α⌝ₛ, ξ) ∧ ⌜rd_entry0_m⌝ₚ(ξ, ⌜t⌝ₛ, ⌜F⌝ₛ)) ∨
  ((∀ ξ, ¬ ⌜KP.succ0_m⌝ₚ(⌜α⌝ₛ, ξ)) ∧ ⌜t⌝ₛ = ⌜o⌝ₛ)⟫
derive_free_closed wi_input_m
theorem wi_input_sat_l (hE : Extensional M) {d} (η : Env M d) (o F α t : Term d) :
    Formula.satisfies η (wi_input_m o F α t) ↔ Wi_input_d (o.eval η) (F.eval η) (α.eval η) (t.eval η) := by
  simp only [wi_input_m, Wi_input_d, Formula.satisfies_disj_iff, Formula.satisfies_exists_iff,
    Formula.satisfies_conj_iff, Formula.satisfies_forall_iff, Formula.satisfies_neg_iff,
    Formula.satisfies_extensionalEq_iff_eq hE, KP.succ0_sat_l hE, rd_entry0_sat_l hE, Definitional.Term.eval_weaken]; rfl

theorem Wi_input_d.unique_l (hKP : M.Models KP) {o F α t v : M.Domain} (ho : M.IsOrdinal α)
    (hf : M.IsSetFunction (kp_pair_l hKP) F) (h : Wi_input_d o F α t) (g : Wi_input_d o F α v) : t = v := by
  rcases h with ⟨ξ, hξ, ht⟩ | ⟨no, ht⟩
  · rcases g with ⟨η, hη, hv⟩ | ⟨no, _⟩
    · have eq := Structure.SuccessorOf.predecessor_eq hKP.1 (ho.mem hξ.predecessor_mem) hξ hη
      exact hf.2 ξ t v ht (eq.symm ▸ hv)
    · exact (no ξ hξ).elim
  · exact g.elim (fun ⟨ξ, hξ, _⟩ => (no ξ hξ).elim) (fun hh => ht.trans hh.2.symm)

def Wi_drive_d (o Ψ F H s : M.Domain) : Prop := ∃ α t r u B,
  (∀ i, M.mem i α ↔ ∃ v, Rd_entry_d i v H) ∧ Wi_input_d o F α t ∧ Rd_triple_d r α H t ∧
    Rd_entry_d r u Ψ ∧ KPair_d M u B s
def wi_drive_m {d} (o Ψ F H s : Term d) : Formula 1 d := set[d] ⟪
  ∃ α t r u B, ⌜Formula.isDomain kpair_convention_l⌝ₚ(α, ⌜H⌝ₛ) ∧ ⌜wi_input_m⌝ₚ(⌜o⌝ₛ, ⌜F⌝ₛ, α, t) ∧
    ⌜rd_triple0_m⌝ₚ(r, α, ⌜H⌝ₛ, t) ∧ ⌜rd_entry0_m⌝ₚ(r, u, ⌜Ψ⌝ₛ) ∧ ⌜kpair0_m⌝ₚ(u, B, ⌜s⌝ₛ)⟫
derive_free_closed wi_drive_m
def wi_drive_schema : BinarySchema 3 where
  body := wi_drive_m (.bound 4) (.bound 3) (.bound 2) (.bound 1) .newest
theorem wi_drive_sat_l (hKP : M.Models KP) (η : Env M 3) (H s : M.Domain) :
    wi_drive_schema.denote η H s ↔ Wi_drive_d (η.bound 2) (η.bound 1) (η.bound 0) H s := by
  simp only [wi_drive_schema, BinarySchema.denote, wi_drive_m, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    Formula.satisfies_isDomain_iff (kp_pair_l hKP), wi_input_sat_l hKP.1,
    rd_triple0_sat_l hKP.1, rd_entry0_sat_l hKP.1, kpair0_sat_l hKP.1, Definitional.Term.eval_weaken]; rfl

def Wi_run_d (hZF : M.Models ZF) (o Ψ F α Z H : M.Domain) : Prop :=
  M.IsRecursiveSequenceIn (kp_pair_l (ZF.modelsKP hZF)) (Wi_drive_d o Ψ F) H α Z

theorem Wi_drive_d.unique_l (hKP : M.Models KP) {o Ψ F α H s v : M.Domain}
    (seq : M.IsSequenceOfLength (kp_pair_l hKP) H α) (hf : M.IsSetFunction (kp_pair_l hKP) F)
    (hp : M.IsSetFunction (kp_pair_l hKP) Ψ) (h : Wi_drive_d o Ψ F H s) (g : Wi_drive_d o Ψ F H v) : s = v := by
  obtain ⟨β, t, r, u, B, dom, input, pack, edge, pair⟩ := h
  obtain ⟨γ, t', r', u', B', dom', input', pack', edge', pair'⟩ := g
  have eβ := Structure.IsDomainOf.eq (𝕀 := kp_pair_l hKP) hKP.1 dom seq.2.2
  have eγ := Structure.IsDomainOf.eq (𝕀 := kp_pair_l hKP) hKP.1 dom' seq.2.2
  subst β γ
  have eq := input.unique_l hKP seq.1 hf input'
  subst t'
  obtain ⟨q, pq, pr⟩ := pack
  obtain ⟨q', pq', pr'⟩ := pack'
  have eq := kpair_unique_l M hKP.1 pq pq'
  subst q'
  have eq := kpair_unique_l M hKP.1 pr pr'
  subst r'
  exact (kpair_injective_l M (hp.2 r u u' edge edge' ▸ pair) pair').2

theorem wi_run_exists_l (hZFC : M.Models ZFC) {ω χ Z Ω a A S o s₀ Ψ F : M.Domain}
    (hω : M.IsOmega ω) (hχ : M.IsRegularCardinal (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) χ)
    (hωχ : M.mem ω χ) (hZ : H_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) χ Z)
    (hΩ : M.IsOrdinal Ω) (hΩZ : M.mem Ω Z) (hoZ : M.mem o Z)
    (select : Wi_selector_d (ZFC.models_zf_l hZFC) ω a A S o s₀ Z Ψ) (moves : Fn0_d Ω Z F) :
    ∃ H, Wi_run_d (ZFC.models_zf_l hZFC) o Ψ F Ω Z H ∧
      ∀ H', Wi_run_d (ZFC.models_zf_l hZFC) o Ψ F Ω Z H' → H' = H := by
  classical
  let hZF := ZFC.models_zf_l hZFC
  let I := kp_pair_l (ZF.modelsKP hZF)
  let η : Env M 3 := ((⟨fun _ => o, fun _ => o⟩ : Env M 1).push Ψ).push F
  have sat H s : wi_drive_schema.denote η H s ↔ Wi_drive_d o Ψ F H s := wi_drive_sat_l (ZF.modelsKP hZF) ..
  have zt := ZF.h_transitive_l I hZF hZ
  have ff := fn0_function_l (ZF.modelsKP hZF) moves
  have pf := fn0_function_l (ZF.modelsKP hZF) select.function
  have total H (seq : M.IsSequenceInBelow I H Ω Z) : ∃ s, Wi_drive_d o Ψ F H s := by
    obtain ⟨_, α, hα, seq⟩ := seq
    have hαZ := zt Ω hΩZ α hα
    have hh := ZFC.h_function_l hZFC hω hχ hωχ hZ hαZ seq.2
    have input : ∃ t, M.mem t Z ∧ Wi_input_d o F α t := by
      by_cases succ : ∃ ξ, M.SuccessorOf α ξ
      · obtain ⟨ξ, hξ⟩ := succ
        obtain ⟨t, ht, edge⟩ := moves.2.1 ξ (hΩ.transitive α hα ξ hξ.predecessor_mem)
        exact ⟨t, ht, Or.inl ⟨ξ, hξ, edge⟩⟩
      · exact ⟨o, hoZ, Or.inr ⟨fun ξ hξ => succ ⟨ξ, hξ⟩, rfl⟩⟩
    obtain ⟨t, ht, input⟩ := input
    obtain ⟨p, pp⟩ := I.total H t
    obtain ⟨r, pr⟩ := I.total α p
    have hr := ZFC.h_kpair_l hZFC hω hχ hωχ hZ pr hαZ (ZFC.h_kpair_l hZFC hω hχ hωχ hZ pp hh ht)
    obtain ⟨u, _, edge⟩ := select.function.2.1 r hr
    obtain ⟨B, s, pair⟩ := select.values r u edge
    exact ⟨s, α, t, r, u, B, seq.2.2.1, input, ⟨p, pp, pr⟩, edge, pair⟩
  have functional : M.IsClassFunctionOnSequencesInBelow I (wi_drive_schema.denote η) Ω Z := by
    intro H seq
    obtain ⟨s, hs⟩ := total H seq
    refine ⟨s, (sat H s).mpr hs, fun v hv => ?_⟩
    obtain ⟨_, α, _, seq⟩ := seq
    exact ((sat H v).mp hv).unique_l (ZF.modelsKP hZF) ⟨seq.1, seq.2.1, seq.2.2.1⟩ ff.1 pf.1 hs
  have into : M.MapsSequencesInBelowInto I (wi_drive_schema.denote η) Ω Z := by
    intro H s _ hs
    obtain ⟨_, _, r, u, _, _, _, _, edge, pair⟩ := (sat H s).mp hs
    exact (pair.mem_l M zt (select.function.bound_l edge).2).2
  obtain ⟨H, run, unique⟩ := ZF.recursiveSequenceIn_existsUnique hZF I η wi_drive_schema hΩ functional into
  have convert K : M.IsRecursiveSequenceIn I (wi_drive_schema.denote η) K Ω Z ↔ Wi_run_d hZF o Ψ F Ω Z K := by
    refine and_congr_right fun _ => forall_congr' fun i => imp_congr_right fun hi => forall_congr' fun s => imp_congr_right fun edge => ?_
    exact exists_congr fun J => and_congr_right fun _ => sat J s
  exact ⟨H, (convert H).mp run, fun K hk => unique K ((convert K).mpr hk)⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 运行的唯一性与前缀重放

唯一性只使用 ZF 和两张已给定图的单值性，不调用集合包络或新的选择。
限制对手走法后，旧运行的相同前缀仍是递归运行。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Wi_run_d.unique_l {o Ψ F α Z H K : M.Domain} (hF : M.IsSetFunction I F) (hΨ : M.IsSetFunction I Ψ)
    (h : Wi_run_d hZF o Ψ F α Z H) (k : Wi_run_d hZF o Ψ F α Z K) : H = K := by
  change M.IsRecursiveSequenceIn I (Wi_drive_d o Ψ F) H α Z at h
  change M.IsRecursiveSequenceIn I (Wi_drive_d o Ψ F) K α Z at k
  let η : Env M 3 := ((⟨fun _ => o, fun _ => o⟩ : Env M 1).push Ψ).push F
  have eq : wi_drive_schema.denote η = Wi_drive_d o Ψ F :=
    funext fun H => funext fun s => propext (wi_drive_sat_l (ZF.modelsKP hZF) η H s)
  apply ZF.recursiveSequenceIn_unique hZF I η wi_drive_schema h.1.1 (Or.inl rfl) ?_ (eq.symm ▸ h) (eq.symm ▸ k)
  intro J ⟨_, β, _, seq⟩ x y hx hy
  exact (eq ▸ hx).unique_l (ZF.modelsKP hZF) ⟨seq.1, seq.2.1, seq.2.2.1⟩ hF hΨ (eq ▸ hy)

theorem Wi_run_d.restrict_moves_l {o Ψ F Ω Z R α H F' : M.Domain} (run : Wi_run_d hZF o Ψ F Ω Z R)
    (hi : M.mem α Ω) (rh : M.IsRestrictionOf I H R α) (rf : M.IsRestrictionOf I F' F α) :
    Wi_run_d hZF o Ψ F' α Z H := by
  have part := run.restriction hi rh
  refine ⟨part.1, fun i hi s hs => ?_⟩
  obtain ⟨J, rj, β, t, r, u, B, dom, input, request, edge, pair⟩ := part.2 i hi s hs
  have seq := part.restriction hi rj
  have eq := Structure.IsDomainOf.eq (𝕀 := I) hZF.1 dom seq.1.2.2.1
  subst β
  refine ⟨J, rj, i, t, r, u, B, dom, ?_, request, edge, pair⟩
  exact input.elim (fun ⟨ξ, next, ht⟩ => Or.inl ⟨ξ, next, (rf.2 ξ t).mpr
    ⟨part.1.1.transitive i hi ξ next.predecessor_mem, ht⟩⟩) Or.inr

def wi_run_m {d} (o Ψ F α Z H : Term d) : Formula 1 d :=
  Formula.isRecursiveSequenceIn kpair_convention_l wi_drive_schema
    (Definitional.TermVector.ofFn (Fin.cases F (Fin.cases Ψ (fun _ => o)))) H α Z

@[simp] theorem wi_run_closed_l {d} (o Ψ F α Z H : Term d) (ho : o.freeSupport = []) (hp : Ψ.freeSupport = [])
    (hf : F.freeSupport = []) (hα : α.freeSupport = []) (hz : Z.freeSupport = []) (hh : H.freeSupport = []) :
    (wi_run_m o Ψ F α Z H).FreeClosed := by
  have he : (Definitional.TermVector.ofFn (Fin.cases F (Fin.cases Ψ (fun _ : Fin 1 => o)))).FreeClosed := by
    intro i
    cases i using Fin.cases with
    | zero => exact hf
    | succ i => cases i using Fin.cases with
      | zero => exact hp
      | succ i => simpa only [Definitional.TermVector.get_ofFn, Fin.cases_succ] using ho
  exact Formula.isRecursiveSequenceIn_freeClosed _ _ _ _ _ _ he hh hα hz

theorem wi_run_sat_l {d} (η : Env M d) (o Ψ F α Z H : Term d) :
    Formula.satisfies η (wi_run_m o Ψ F α Z H) ↔
      Wi_run_d hZF (o.eval η) (Ψ.eval η) (F.eval η) (α.eval η) (Z.eval η) (H.eval η) := by
  rw [wi_run_m, Formula.satisfies_isRecursiveSequenceIn_iff I hZF.1]
  refine and_congr_right fun _ => forall_congr' fun i => imp_congr_right fun hi =>
    forall_congr' fun s => imp_congr_right fun hs => exists_congr fun J => and_congr_right fun _ => ?_
  exact wi_drive_sat_l (ZF.modelsKP hZF) _ J s

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 仅以公开走法历史为输入的集合策略

唯一重放恢复内部状态，再由同一请求读取树枝。策略的定义域包含所有指定长度的
走法历史；返回映射与内部状态均不作为对手必须提供的输入。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)

def Wi_position_d (Ω Z F : M.Domain) : Prop := ∃ α ξ, M.mem α Ω ∧ M.SuccessorOf α ξ ∧ Fn0_d α Z F
def wi_position_m {d} (Ω Z F : Term d) : Formula 1 d := set[d] ⟪
  ∃ α ξ, α ∈ ⌜Ω⌝ₛ ∧ ⌜KP.succ0_m⌝ₚ(α, ξ) ∧ ⌜fn0_m⌝ₚ(α, ⌜Z⌝ₛ, ⌜F⌝ₛ)⟫
derive_free_closed wi_position_m
theorem wi_position_sat_l (hE : Extensional M) {d} (η : Env M d) (Ω Z F : Term d) :
    Formula.satisfies η (wi_position_m Ω Z F) ↔ Wi_position_d (Ω.eval η) (Z.eval η) (F.eval η) := by
  simp only [wi_position_m, Wi_position_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    Formula.satisfies_mem_iff, KP.succ0_sat_l hE, fn0_sat_l hE, Definitional.Term.eval_weaken]; rfl

def Wi_public_d (o Ψ Z F B : M.Domain) : Prop := ∃ α ξ H t r u s,
  M.SuccessorOf α ξ ∧ Fn0_d α Z F ∧ Wi_run_d hZF o Ψ F α Z H ∧ Rd_entry_d ξ t F ∧
    Rd_triple_d r α H t ∧ Rd_entry_d r u Ψ ∧ KPair_d M u B s
def wi_public_m {d} (o Ψ Z F B : Term d) : Formula 1 d := set[d] ⟪
  ∃ α ξ H t r u s, ⌜KP.succ0_m⌝ₚ(α, ξ) ∧ ⌜fn0_m⌝ₚ(α, ⌜Z⌝ₛ, ⌜F⌝ₛ) ∧
    ⌜wi_run_m⌝ₚ(⌜o⌝ₛ, ⌜Ψ⌝ₛ, ⌜F⌝ₛ, α, ⌜Z⌝ₛ, H) ∧ ⌜rd_entry0_m⌝ₚ(ξ, t, ⌜F⌝ₛ) ∧
    ⌜rd_triple0_m⌝ₚ(r, α, H, t) ∧ ⌜rd_entry0_m⌝ₚ(r, u, ⌜Ψ⌝ₛ) ∧ ⌜kpair0_m⌝ₚ(u, ⌜B⌝ₛ, s)⟫
derive_free_closed wi_public_m
theorem wi_public_sat_l {d} (η : Env M d) (o Ψ Z F B : Term d) :
    Formula.satisfies η (wi_public_m o Ψ Z F B) ↔
      Wi_public_d hZF (o.eval η) (Ψ.eval η) (Z.eval η) (F.eval η) (B.eval η) := by
  simp only [wi_public_m, Wi_public_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    KP.succ0_sat_l hZF.1, fn0_sat_l hZF.1, wi_run_sat_l hZF, rd_entry0_sat_l hZF.1,
    rd_triple0_sat_l hZF.1, kpair0_sat_l hZF.1, Definitional.Term.eval_weaken]; rfl

def Wi_strategy_d (o Ψ Ω Z D Γ : M.Domain) : Prop :=
  (∀ F, M.mem F D ↔ Wi_position_d Ω Z F) ∧ Fn0_d D Z Γ ∧
    ∀ F B, Rd_entry_d F B Γ ↔ M.mem F D ∧ Wi_public_d hZF o Ψ Z F B

theorem Wi_public_d.unique_l {o Ψ Z F B C : M.Domain}
    (hΨ : M.IsSetFunction (kp_pair_l (ZF.modelsKP hZF)) Ψ)
    (h : Wi_public_d hZF o Ψ Z F B) (k : Wi_public_d hZF o Ψ Z F C) : B = C := by
  obtain ⟨α, ξ, H, t, r, u, s, hα, ff, run, ht, pack, edge, pair⟩ := h
  obtain ⟨β, η, K, t', r', u', s', hβ, ff', run', ht', pack', edge', pair'⟩ := k
  have eq := ff'.domain_eq_l hZF.1 ff
  subst β
  have eq := Structure.SuccessorOf.predecessor_eq hZF.1 (run.1.1.mem hα.predecessor_mem) hα hβ
  subst η
  have eq := run'.unique_l hZF (fn0_function_l (ZF.modelsKP hZF) ff).1 hΨ run
  subst K
  have eq := (fn0_function_l (ZF.modelsKP hZF) ff).1.2 ξ t' t ht' ht
  subst t'
  obtain ⟨p, pp, pr⟩ := pack
  obtain ⟨q, pq, qr⟩ := pack'
  have eq := kpair_unique_l M hZF.1 pq pp
  subst q
  have eq := kpair_unique_l M hZF.1 qr pr
  subst r'
  exact (kpair_injective_l M pair (hΨ.2 r u' u edge' edge ▸ pair')).1

theorem wi_strategy_exists_l (hZFC : M.Models ZFC) {ω χ Z Ω a A S o s₀ Ψ : M.Domain}
    (hω : M.IsOmega ω) (hχ : M.IsRegularCardinal (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) χ)
    (hωχ : M.mem ω χ) (hZ : H_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) χ Z)
    (hΩ : M.IsOrdinal Ω) (hΩZ : M.mem Ω Z) (hoZ : M.mem o Z)
    (select : Wi_selector_d (ZFC.models_zf_l hZFC) ω a A S o s₀ Z Ψ) :
    ∃ D Γ, Wi_strategy_d (ZFC.models_zf_l hZFC) o Ψ Ω Z D Γ := by
  let hZF := ZFC.models_zf_l hZFC
  let I := kp_pair_l (ZF.modelsKP hZF)
  have zt := ZF.h_transitive_l I hZF hZ
  let φ : UnarySchema 2 := { body := wi_position_m (.bound 2) (.bound 1) .newest }
  let ρ : Env M 2 := (⟨fun _ => Ω, fun _ => Ω⟩ : Env M 1).push Z
  obtain ⟨D, ds⟩ := ZF.separation_exists_d hZF φ ρ Z
  have domain F : M.mem F D ↔ Wi_position_d Ω Z F := by
    have sat : φ.denote ρ F ↔ Wi_position_d Ω Z F := wi_position_sat_l hZF.1 ..
    refine (ds F).trans ⟨fun hh => sat.mp hh.2, fun hh => ⟨?_, sat.mpr hh⟩⟩
    obtain ⟨α, _, hα, _, ff⟩ := hh
    exact ZFC.h_function_l hZFC hω hχ hωχ hZ (zt Ω hΩZ α hα) (fn0_function_l (ZF.modelsKP hZF) ff)
  have total F (hf : M.mem F D) : ∃ B, Wi_public_d hZF o Ψ Z F B := by
    obtain ⟨α, ξ, hα, succ, ff⟩ := (domain F).mp hf
    have hαZ := zt Ω hΩZ α hα
    obtain ⟨H, run, _⟩ := wi_run_exists_l hZFC hω hχ hωχ hZ (hΩ.mem hα) hαZ hoZ select ff
    have hh := ZFC.h_function_l hZFC hω hχ hωχ hZ hαZ run.1.2
    obtain ⟨t, ht, move⟩ := ff.2.1 ξ succ.predecessor_mem
    obtain ⟨p, pp⟩ := I.total H t
    obtain ⟨r, pr⟩ := I.total α p
    have hr := ZFC.h_kpair_l hZFC hω hχ hωχ hZ pr hαZ (ZFC.h_kpair_l hZFC hω hχ hωχ hZ pp hh ht)
    obtain ⟨u, _, edge⟩ := select.function.2.1 r hr
    obtain ⟨B, s, pair⟩ := select.values r u edge
    exact ⟨B, α, ξ, H, t, r, u, s, succ, ff, run, move, ⟨p, pp, pr⟩, edge, pair⟩
  let ψ : BinarySchema 3 := { body := wi_public_m (.bound 4) (.bound 3) (.bound 2) (.bound 1) .newest }
  let η : Env M 3 := ((⟨fun _ => o, fun _ => o⟩ : Env M 1).push Ψ).push Z
  have sat F B : ψ.denote η F B ↔ Wi_public_d hZF o Ψ Z F B := wi_public_sat_l hZF ..
  obtain ⟨Γ, fn, gs⟩ := ZF.exists_setFunctionFromTo_of_denote hZF I ψ η (source := D) (target := Z)
    (fun F hf => (total F hf).imp fun B hb => (sat F B).mpr hb)
    (fun F _ B C hb hc => ((sat F B).mp hb).unique_l hZF (fn0_function_l (ZF.modelsKP hZF) select.function).1 ((sat F C).mp hc))
    (fun F B _ hb => by
      obtain ⟨_, _, _, _, r, u, _, _, _, _, _, _, edge, pair⟩ := (sat F B).mp hb
      exact (pair.mem_l M zt (select.function.bound_l edge).2).1)
  exact ⟨D, Γ, domain, fn0_of_function_l (ZF.modelsKP hZF) fn,
    fun F B => (gs F B).trans (and_congr_right fun _ => sat F B)⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 合法弱迭代对局的每一步都有实际应答

合法性只要求对手在当前模型上给出 nice ω 树。对历史正确性的原公式做超限归纳，
逐步证明所选应答真实存在，因而备用值永远不会造成一次合法对局的失败。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

def Wi_legal_d (ω Ω F R : M.Domain) : Prop := ∀ i j s T Q G P c t,
  M.mem j Ω → M.SuccessorOf j i → Rd_entry_d i s R → Rd_quad_d s T Q G P → Rd_entry_d i c Q → Rd_entry_d i t F →
    ∃ U Q' G' E L, Wi_tree_d t U Q' G' E L ∧ It_nice_d hZF ω c ω U Q' G' E L

def Wi_reply_d (ω a A S o s₀ Ψ F R i s : M.Domain) : Prop := ∃ H t r u B,
  M.IsRestrictionOf I H R i ∧ Wi_input_d o F i t ∧ Rd_triple_d r i H t ∧ Rd_entry_d r u Ψ ∧
    KPair_d M u B s ∧ Wi_answer_d hZF ω a A S o s₀ i H t B s

/-! 强应答记录与旧回复接口平行，保留同一完整树证书。 -/
def Wi_reply_tree_d (ω a A S o s₀ Ψ F R i s : M.Domain) : Prop := ∃ H t r u B,
  M.IsRestrictionOf I H R i ∧ Wi_input_d o F i t ∧ Rd_triple_d r i H t ∧ Rd_entry_d r u Ψ ∧
    KPair_d M u B s ∧ Wi_answer_tree_d hZF ω a A S o s₀ i H t B s

theorem Wi_reply_tree_d.to_reply_d
    {ω a A S o s₀ Ψ F R i s : M.Domain}
    (h : Wi_reply_tree_d hZF ω a A S o s₀ Ψ F R i s) :
    Wi_reply_d hZF ω a A S o s₀ Ψ F R i s := by
  obtain ⟨H, t, r, u, B, rh, input, triple, edge, pair, answer⟩ := h
  exact ⟨H, t, r, u, B, rh, input, triple, edge, pair, answer.to_answer_d⟩
variable (hZFC : M.Models ZFC)
local notation "hZF'" => ZFC.models_zf_l hZFC
local notation "I'" => kp_pair_l (ZF.modelsKP hZF')

theorem wi_run_wins_l {ω χ Z Ω a A S o s₀ Ψ F R θ α₀ T₀ Q₀ G₀ P₀ : M.Domain}
    (hω : M.IsOmega ω) (hχ : M.IsRegularCardinal I' χ) (hωχ : M.mem ω χ) (hZ : H_d I' χ Z)
    (hωZ : M.mem ω Z) (hA : M.mem A Z) (hΩ : M.IsOrdinal Ω)
    (count : ∀ i, M.mem i Ω → M.CardinalLessOrEqual I' i ω)
    (ho : ∀ x, ¬ M.mem x o) (hα₀ : M.SuccessorOf α₀ o) (pack₀ : Rd_quad_d s₀ T₀ Q₀ G₀ P₀)
    (root : Wi_state_d (kp_pair_l (ZF.modelsKP hZF')) ω α₀ T₀ Q₀ G₀ a A S P₀) (rank : V_d I' θ A) (ma : Smem_d I' a A S)
    (select : Wi_selector_d hZF' ω a A S o s₀ Z Ψ) (run : Wi_run_d hZF' o Ψ F Ω Z R)
    (legal : Wi_legal_d hZF' ω Ω F R) :
    Wi_history_d hZF' ω a A S Ω Z R ∧ ∀ i s, Rd_entry_d i s R → Wi_reply_d hZF' ω a A S o s₀ Ψ F R i s := by
  have answer {i H s} (hi : M.mem i Ω) (rh : M.IsRestrictionOf I' H R i)
      (hist : Wi_history_d hZF' ω a A S i Z H) (drive : Wi_drive_d o Ψ F H s) :
      Wi_reply_d hZF' ω a A S o s₀ Ψ F R i s := by
    obtain ⟨α, t, r, u, B, dom, input, request, edge, pair⟩ := drive
    have seq := run.restriction hi rh
    have eq := Structure.IsDomainOf.eq (𝕀 := I') hZF'.1 dom seq.1.2.2.1
    subst α
    have available : ∃ C v, Wi_answer_d hZF' ω a A S o s₀ i H t C v := by
      rcases (hΩ.mem hi).classify hZF'.1 with empty | ⟨ξ, hξ, succ⟩ | limit
      · have eq := hZF'.1.eq_of_same_members i o (fun x => iff_of_false (empty x) (ho x))
        subst i
        exact ⟨o, s₀, wi_answer_root_l hZF' ho hα₀ pack₀ root hist⟩
      · have move : Rd_entry_d ξ t F := by
          rcases input with ⟨η, next, ht⟩ | ⟨no, _⟩
          · exact (Structure.SuccessorOf.predecessor_eq hZF'.1 hξ succ next).symm ▸ ht
          · exact (no ξ succ).elim
        obtain ⟨v, _, hv⟩ := hist.function.2.1 ξ succ.predecessor_mem
        obtain ⟨β, T, Q, G, P, hβ, pack, state⟩ := hist.rows ξ v hv
        have eq := Structure.SuccessorOf.eq hZF'.1 hβ succ
        subst β
        obtain ⟨c, hc⟩ := (state.diagram.model_domain ξ).mp succ.predecessor_mem
        obtain ⟨U, Q', G', E, L, pt, nice⟩ := legal ξ i v T Q G P c t hi succ ((rh.2 ξ v).mp hv).2 pack hc move
        exact wi_answer_successor_l hZFC hist succ ⟨v, hv, pack⟩ hc pt nice rank ma
      · obtain ⟨v, hv⟩ := wi_answer_limit_l hZFC hist limit (count i hi) ma (o := o) (s₀ := s₀) (t := t)
        exact ⟨o, v, hv⟩
    obtain ⟨C, v, av⟩ := available
    have next β (hb : M.SuccessorOf β i) : M.mem β Z := by
      have cn := ZF.countable_insert_l I' hZF' hω (count i hi) (fun x => (hb x).trans
        (or_congr Iff.rfl ⟨hZF'.1.eq_of_same_members x i, fun eq => eq ▸ fun _ => Iff.rfl⟩))
      exact (hZ β).mpr (ZF.hmem_of_subset_l I' hZF' hχ.isLimitOrdinal
        (KP.successor_isOrdinal (ZF.modelsKP hZF') (hΩ.mem hi) hb).transitive (fun _ h => h) hωχ cn)
    obtain ⟨hC, hv⟩ := av.mem_l hZFC hω hχ hωχ hZ hωZ hA ho next
    obtain ⟨w, pw⟩ := (I').total C v
    have hw := ZFC.h_kpair_l hZFC hω hχ hωχ hZ pw hC hv
    exact ⟨H, t, r, u, B, rh, input, request, edge, pair,
      select.answer_l hZF' request pair edge ⟨w, hw, i, H, t, C, v, request, pw, av⟩⟩
  -- 归纳谓词是原一阶历史公式；合法 nice 条件只作为归纳步的已知事实使用。
  let η : Env M 6 := (((((⟨fun _ => ω, fun _ => ω⟩ : Env M 1).push a).push A).push S).push Z).push R
  let φ : UnarySchema 6 := { body := .forallE (.imp
    (Formula.isRestriction kpair_convention_l .newest (.bound 2) (.bound 1))
    (wi_history_m (.bound 7) (.bound 6) (.bound 5) (.bound 4) (.bound 1) (.bound 3) .newest)) }
  have sat α : φ.denote η α ↔ ∀ H, M.IsRestrictionOf I' H R α → Wi_history_d hZF' ω a A S α Z H := by
    simp only [φ, UnarySchema.denote, Formula.satisfies_forall_iff, Formula.satisfies_imp_iff,
      Formula.satisfies_isRestriction_iff I', wi_history_sat_l hZF']; rfl
  have all : φ.denote η Ω := by
    apply hΩ.inductionWithin (fun α => φ.denote η α)
    · obtain ⟨C, hc⟩ := ZF.separation_exists_d hZF' φ.neg η Ω
      exact ⟨C, fun i => (hc i).trans (and_congr_right fun _ => Formula.satisfies_neg_iff ..)⟩
    · intro α hα within ih
      apply (sat α).mpr
      intro H rh
      have sub : M.MemberSubset α Ω := within.elim (fun eq _ hi => eq ▸ hi) (fun hi => hΩ.transitive α hi)
      have get i s (hs : Rd_entry_d i s H) : Wi_reply_d hZF' ω a A S o s₀ Ψ F R i s := by
        have read := (rh.2 i s).mp hs
        obtain ⟨J, rj, drive⟩ := run.2 i (sub i read.1) s read.2
        exact answer (sub i read.1) rj ((sat i).mp (ih i read.1) J rj) drive
      refine ⟨fn0_of_function_l (ZF.modelsKP hZF') (rh.isSetFunctionFromTo run.1.2 sub), ?_, ?_⟩
      · intro i s hs
        obtain ⟨_, _, _, _, _, _, _, _, _, _, β, T, Q, G, P, hβ, pack, state, _⟩ := get i s hs
        exact ⟨β, T, Q, G, P, hβ, pack, state⟩
      · intro i j T Q G P U Q' G' P' hij ⟨s, hs, ps⟩ ⟨t, ht, pt⟩
        obtain ⟨J, _, _, _, _, rj, _, _, _, _, _, V, Q'', G'', P'', _, pack, _, past, _⟩ := get j t ht
        obtain ⟨eqT, eqQ, eqG, eqP⟩ := pack.unique_l pt
        subst V Q'' G'' P''
        exact past i T Q G P ⟨s, (rj.2 i s).mpr ⟨hij, ((rh.2 i s).mp hs).2⟩, ps⟩
  have self : M.IsRestrictionOf I' R R Ω := ⟨run.1.2.1.1,
    fun i s => ⟨fun hs => ⟨run.1.2.input_mem_of_pairMember hs, hs⟩, And.right⟩⟩
  have history := (sat Ω).mp all R self
  refine ⟨history, fun i s hs => ?_⟩
  have hi := run.1.2.input_mem_of_pairMember hs
  obtain ⟨H, rh, drive⟩ := run.2 i hi s hs
  exact answer hi rh (history.restrict_l hZF' (hΩ.transitive i hi) rh) drive

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 公开策略给出的正是合法运行中的原共尾枝 -/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)


def Wi_play_d (ω a A S F R α ξ B : M.Domain) : Prop := ∃ H t s β T Q G P,
  M.IsRestrictionOf I H R α ∧ Rd_entry_d ξ t F ∧ Rd_entry_d α s R ∧ Rd_quad_d s T Q G P ∧
    M.SuccessorOf β α ∧ Wi_state_d (kp_pair_l (ZF.modelsKP hZF)) ω β T Q G a A S P ∧ Wi_success_d hZF ω α t B Q G

/-! 强返回层的公开 play 证书。它保留同一局面的树枝运输与良基极限，
并可严格投影回旧公式层。 -/
def Wi_play_tree_d (ω a A S F R α ξ B : M.Domain) : Prop := ∃ H t s β T Q G P,
  M.IsRestrictionOf I H R α ∧ Rd_entry_d ξ t F ∧ Rd_entry_d α s R ∧ Rd_quad_d s T Q G P ∧
    M.SuccessorOf β α ∧ Wi_state_d (kp_pair_l (ZF.modelsKP hZF)) ω β T Q G a A S P ∧
    Wi_success_tree_d hZF ω α t B Q G

theorem Wi_play_tree_d.to_play_d {ω a A S F R α ξ B : M.Domain}

    (h : Wi_play_tree_d hZF ω a A S F R α ξ B) : Wi_play_d hZF ω a A S F R α ξ B := by
  obtain ⟨H, t, s, β, T, Q, G, P, rh, move, hs, pack, hb, state, success⟩ := h
  exact ⟨H, t, s, β, T, Q, G, P, rh, move, hs, pack, hb, state, success.to_success_d⟩


theorem Wi_strategy_d.play_l {ω a A S o s₀ Ψ Ω Λ Z D Γ F R α ξ F' B : M.Domain}
    (strategy : Wi_strategy_d hZF o Ψ Ω Z D Γ) (hΨ : M.IsSetFunction I Ψ)
    (ho : ∀ x, ¬ M.mem x o) (moves : Fn0_d Λ Z F) (run : Wi_run_d hZF o Ψ F Λ Z R)
    (wins : ∀ i s, Rd_entry_d i s R → Wi_reply_d hZF ω a A S o s₀ Ψ F R i s)
    (hα : M.mem α Λ) (succ : M.SuccessorOf α ξ) (rf : M.IsRestrictionOf I F' F α)
    (chosen : Rd_entry_d F' B Γ) : Wi_play_d hZF ω a A S F R α ξ B := by
  obtain ⟨β, η, H, t, r, u, v, hβ, ff, play, ht, pack, edge, pair⟩ := ((strategy.2.2 F' B).mp chosen).2
  have fn := fn0_of_function_l (ZF.modelsKP hZF)
    (rf.isSetFunctionFromTo (fn0_function_l (ZF.modelsKP hZF) moves) (run.1.1.transitive α hα))
  have eq := ff.domain_eq_l hZF.1 fn
  subst β
  have eq := Structure.SuccessorOf.predecessor_eq hZF.1 (play.1.1.mem hβ.predecessor_mem) hβ succ
  subst η
  obtain ⟨K, rk⟩ := ZF.exists_restriction hZF I R α
  have eq := (run.restrict_moves_l hZF hα rk rf).unique_l hZF (fn0_function_l (ZF.modelsKP hZF) ff).1 hΨ play
  have rh : M.IsRestrictionOf I H R α := eq ▸ rk
  have move := ((rf.2 ξ t).mp ht).2
  obtain ⟨s, _, hs⟩ := run.1.2.2.2 α hα
  obtain ⟨J, t', r', u', C, rj, input, pack', edge', pair', answer⟩ := wins α s hs
  have eq := rj.eq hZF.1 rh
  subst J
  have eq := input.unique_l (ZF.modelsKP hZF) play.1.1 (fn0_function_l (ZF.modelsKP hZF) moves).1 (Or.inl ⟨ξ, succ, move⟩)
  subst t'
  obtain ⟨p, pp, pr⟩ := pack
  obtain ⟨q, pq, qr⟩ := pack'
  have eq := kpair_unique_l M hZF.1 pq pp
  subst q
  have eq := kpair_unique_l M hZF.1 qr pr
  subst r'
  have eq := hΨ.2 r u' u edge' edge
  subst u'
  have eq := (kpair_injective_l M pair' pair).1
  subst C
  obtain ⟨β, T, Q, G, P, hb, ps, state, _, cases⟩ := answer
  refine ⟨H, t, s, β, T, Q, G, P, rh, move, hs, ps, hb, state, ?_⟩
  rcases cases with ⟨eq, _⟩ | step | ⟨limit, _⟩
  · exact (ho ξ (eq ▸ succ.predecessor_mem)).elim
  · exact step
  · obtain ⟨j, hj, hξj⟩ := limit.2.2 ξ succ.predecessor_mem
    rcases (succ j).mp hj with hj | eq
    · exact (KP.mem_irrefl_d (ZF.modelsKP hZF) ξ ((limit.1.mem succ.predecessor_mem).transitive j hj ξ hξj)).elim
    · exact (KP.mem_irrefl_d (ZF.modelsKP hZF) ξ (hZF.1.eq_of_same_members j ξ eq ▸ hξj)).elim

/-! 强回复对象可直接驱动同一公开策略证明，最终保留 `Wi_success_tree_d`。 -/
theorem Wi_strategy_d.play_tree_l {ω a A S o s₀ Ψ Ω Λ Z D Γ F R α ξ F' B : M.Domain}
    (strategy : Wi_strategy_d hZF o Ψ Ω Z D Γ) (hΨ : M.IsSetFunction I Ψ)
    (ho : ∀ x, ¬ M.mem x o) (moves : Fn0_d Λ Z F) (run : Wi_run_d hZF o Ψ F Λ Z R)
    (wins : ∀ i s, Rd_entry_d i s R → Wi_reply_tree_d hZF ω a A S o s₀ Ψ F R i s)
    (hα : M.mem α Λ) (succ : M.SuccessorOf α ξ) (rf : M.IsRestrictionOf I F' F α)
    (chosen : Rd_entry_d F' B Γ) : Wi_play_tree_d hZF ω a A S F R α ξ B := by
  obtain ⟨β, η, H, t, r, u, v, hβ, ff, play, ht, pack, edge, pair⟩ := ((strategy.2.2 F' B).mp chosen).2
  have fn := fn0_of_function_l (ZF.modelsKP hZF)
    (rf.isSetFunctionFromTo (fn0_function_l (ZF.modelsKP hZF) moves) (run.1.1.transitive α hα))
  have eq := ff.domain_eq_l hZF.1 fn
  subst β
  have eq := Structure.SuccessorOf.predecessor_eq hZF.1 (play.1.1.mem hβ.predecessor_mem) hβ succ
  subst η
  obtain ⟨K, rk⟩ := ZF.exists_restriction hZF I R α
  have eq := (run.restrict_moves_l hZF hα rk rf).unique_l hZF (fn0_function_l (ZF.modelsKP hZF) ff).1 hΨ play
  have rh : M.IsRestrictionOf I H R α := eq ▸ rk
  have move := ((rf.2 ξ t).mp ht).2
  obtain ⟨s, _, hs⟩ := run.1.2.2.2 α hα
  obtain ⟨J, t', r', u', C, rj, input, pack', edge', pair', answer⟩ := wins α s hs
  have eq := rj.eq hZF.1 rh
  subst J
  have eq := input.unique_l (ZF.modelsKP hZF) play.1.1 (fn0_function_l (ZF.modelsKP hZF) moves).1 (Or.inl ⟨ξ, succ, move⟩)
  subst t'
  obtain ⟨p, pp, pr⟩ := pack
  obtain ⟨q, pq, qr⟩ := pack'
  have eq := kpair_unique_l M hZF.1 pq pp
  subst q
  have eq := kpair_unique_l M hZF.1 qr pr
  subst r'
  have eq := hΨ.2 r u' u edge' edge
  subst u'
  have eq := (kpair_injective_l M pair' pair).1
  subst C
  obtain ⟨β, T, Q, G, P, hb, ps, state, _, cases⟩ := answer
  refine ⟨H, t, s, β, T, Q, G, P, rh, move, hs, ps, hb, state, ?_⟩
  rcases cases with ⟨eq, _⟩ | step | ⟨limit, _⟩
  · exact (ho ξ (eq ▸ succ.predecessor_mem)).elim
  · exact step
  · obtain ⟨j, hj, hξj⟩ := limit.2.2 ξ succ.predecessor_mem
    rcases (succ j).mp hj with hj | eq
    · exact (KP.mem_irrefl_d (ZF.modelsKP hZF) ξ ((limit.1.mem succ.predecessor_mem).transitive j hj ξ hξj)).elim
    · exact (KP.mem_irrefl_d (ZF.modelsKP hZF) ξ (hZF.1.eq_of_same_members j ξ eq ▸ hξj)).elim
end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 可数 nice 树的 ω₁ 弱可迭代性

由给定根到真实 Vθ 的初等嵌入自动构造公开获胜策略。对象选择只进行一次；
任意对手走法均有唯一运行，合法时每个可数阶段保持实际传递极限和完整返回列。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}
section Winning
variable (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

/-- 公开枝策略及其对全部对手走法的获胜证书；模型和返回列由内部重放构造。 -/
def Wi_winning_d (ω c Ω Z D Γ : M.Domain) : Prop := ∃ a A S o s₀ Ψ α₀ T₀ Q₀ G₀ P₀,
  (∀ x, ¬ M.mem x o) ∧ M.SuccessorOf α₀ o ∧ Rd_quad_d s₀ T₀ Q₀ G₀ P₀ ∧
  Wi_state_d (kp_pair_l (ZF.modelsKP hZF)) ω α₀ T₀ Q₀ G₀ a A S P₀ ∧ Rd_entry_d o c Q₀ ∧ Wi_strategy_d hZF o Ψ Ω Z D Γ ∧
  (∀ t d X R T Q G E L, Wi_tree_d t T Q G E L → It_nice_d hZF ω d ω T Q G E L →
    Smem_d I d X R → M.TransitiveSet X → M.CardinalLessOrEqual I X ω → M.mem t Z) ∧
  ∀ β, (β = Ω ∨ M.mem β Ω) → ∀ F, Fn0_d β Z F → ∃ R, Wi_run_d hZF o Ψ F β Z R ∧
    (∀ R', Wi_run_d hZF o Ψ F β Z R' → R' = R) ∧
    (Wi_legal_d hZF ω β F R → Wi_history_d hZF ω a A S β Z R ∧
      (∀ i s, Rd_entry_d i s R → Wi_reply_d hZF ω a A S o s₀ Ψ F R i s) ∧
      ∀ α ξ F', M.mem α β → M.SuccessorOf α ξ → M.IsRestrictionOf I F' F α →
        ∃ B, Rd_entry_d F' B Γ ∧ Wi_play_d hZF ω a A S F R α ξ B)
end Winning

variable (hZFC : M.Models ZFC)
local notation "hZF" => ZFC.models_zf_l hZFC
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

/-- Neeman 推论 2.4：实际 ω₁ 上的 nice 弱迭代博弈有集合编码获胜策略。 -/
theorem it_nice_weakly_iterable_l {ω c X R K θ a A S π : M.Domain}
    (source : Ep_source_d I ω ω K X R) (mx : Smem_d I c X R) (count : M.CardinalLessOrEqual I X ω)
    (rank : V_d I θ A) (ma : Smem_d I a A S) (embed : Smap_d I ω c a X A π) :
    ∃ Ω Z D Γ, M.IsHartogsNumber I Ω ω ∧ Wi_winning_d hZF ω c Ω Z D Γ := by
  have hω := source.omega
  obtain ⟨o, α₀, T₀, Q₀, G₀, P₀, ho, hα₀, root, hc, _⟩ := wi_root_l hZF source mx count ma embed
  obtain ⟨s₀, pack₀⟩ := rd_quad_exists_l (ZF.modelsKP hZF) T₀ Q₀ G₀ P₀
  obtain ⟨Ω, hΩ⟩ := ZF.exists_hartogsNumber hZF I ω
  obtain ⟨p, pp⟩ := rd_quad_exists_l (ZF.modelsKP hZF) s₀ A Ω ω
  obtain ⟨χ, Z, hχ, hωχ, hZ, hp⟩ := ZFC.h_cover_l I hZFC hω p
  have zt := ZF.h_transitive_l I hZF hZ
  obtain ⟨hs₀, hA, hΩZ, hωZ⟩ := pp.mem_l zt hp
  obtain ⟨z, hz, hzω⟩ := hω.1.1
  have eq := hZF.1.eq_of_same_members z o (fun x => iff_of_false (hz x) (ho x))
  have hoZ := zt ω hωZ o (eq ▸ hzω)
  obtain ⟨u₀, pair⟩ := (I).total o s₀
  obtain ⟨Ψ, select⟩ := wi_selector_exists_l hZFC (ZFC.h_kpair_l hZFC hω hχ hωχ hZ pair hoZ hs₀) pair
    (ω := ω) (a := a) (A := A) (S := S)
  obtain ⟨D, Γ, strategy⟩ := wi_strategy_exists_l hZFC hω hχ hωχ hZ hΩ.1 hΩZ hoZ select
  refine ⟨Ω, Z, D, Γ, hΩ, a, A, S, o, s₀, Ψ, α₀, T₀, Q₀, G₀, P₀,
    ho, hα₀, pack₀, root, hc, strategy, ?_, ?_⟩
  · intro t d Y W T Q G E L pack nice my yt cy
    exact pack.mem_l hZFC hω hχ hωχ hZ hωZ nice my cy
  · intro β within F moves
    have hb : M.IsOrdinal β := within.elim (fun eq => eq.symm ▸ hΩ.1) hΩ.1.mem
    have hbZ : M.mem β Z := within.elim (fun eq => eq.symm ▸ hΩZ) (zt Ω hΩZ β)
    have sub : M.MemberSubset β Ω := within.elim (fun eq _ hi => eq ▸ hi) (fun hi => hΩ.1.transitive β hi)
    obtain ⟨H, run, unique⟩ := wi_run_exists_l hZFC hω hχ hωχ hZ hb hbZ hoZ select moves
    refine ⟨H, run, unique, fun legal => ?_⟩
    obtain ⟨history, replies⟩ := wi_run_wins_l hZFC hω hχ hωχ hZ hωZ hA hb
      (fun i hi => (hΩ.2 i (hΩ.1.mem (sub i hi))).mp (sub i hi)) ho hα₀ pack₀ root rank ma select run legal
    refine ⟨history, replies, fun α ξ F' hα succ rf => ?_⟩
    have fn := fn0_of_function_l (ZF.modelsKP hZF)
      (rf.isSetFunctionFromTo (fn0_function_l (ZF.modelsKP hZF) moves) (hb.transitive α hα))
    obtain ⟨B, _, chosen⟩ := strategy.2.1.2.1 F' ((strategy.1 F').mpr ⟨α, ξ, sub α hα, succ, fn⟩)
    exact ⟨B, chosen, strategy.play_l hZF (fn0_function_l (ZF.modelsKP hZF) select.function).1 ho moves run replies hα succ rf chosen⟩

end YesMetaZFC.SetTheory.LargeCardinal
