import YesMetaZFC.SetTheory.LargeCardinal.IterationWeakAnswer
import YesMetaZFC.SetTheory.HereditaryFunction

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

theorem It_diagram_d.h_mem_l {α T Q G : M.Domain} (diagram : It_diagram_d hZF ω α T Q G)
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

theorem Wi_state_d.mem_l {α T Q G a A S P s : M.Domain} (state : Wi_state_d hZF ω α T Q G a A S P)
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
  have counts := it_countable_l hZF nice.tree mx.1 count
  have models i d (hd : Rd_entry_d i d Q) : ∃ Y W,
      Smdl_d I d Y W ∧ M.TransitiveSet Y ∧ M.CardinalLessOrEqual I Y ω := by
    obtain ⟨Y, W, _, my, source⟩ := nice.tree.sources i d hd
    exact ⟨Y, W, my.1, source.transitive, counts i d Y W hd my.1.1⟩
  obtain ⟨ht, hq, hg⟩ := nice.tree.diagram.h_mem_l hZFC hω hχ hωχ hZ hωZ models
  have step i (hi : M.mem i ω) : ∃ p ρ, Rd_entry_d i p E ∧ Rd_entry_d i ρ L ∧ M.mem p Z ∧ M.mem ρ Z := by
    obtain ⟨j, sj, hj⟩ := hω.1.2 i hi
    obtain ⟨_, d, _, _, _, p, κ, ρ, F, Y, W, _, _, _, hd, _, _, _, hp, pay, my, _, loc, _, _, _, _, hρ⟩ := nice.step_l hZF hj sj
    obtain ⟨Y', W', _, my', source⟩ := nice.tree.sources i d hd
    obtain ⟨rfl, rfl⟩ := smdl_unique_l I my'.1 my.1
    have hy := (it_model_mem_l hZFC hω hχ hωχ hZ my.1 source.transitive (counts i d Y' W' hd my.1.1)).2.1
    obtain ⟨q, pq, qf⟩ := pay
    have hκ := zt _ hy _ loc.2.1
    have hρZ := zt _ hy _ loc.2.2.1
    have hF := zt _ hy _ loc.2.2.2.1
    exact ⟨p, ρ, hp, hρ, ZFC.h_kpair_l hZFC hω hχ hωχ hZ pq hκ
      (ZFC.h_kpair_l hZFC hω hχ hωχ hZ qf hρZ hF), hρZ⟩
  have ed i : (∃ p, Rd_entry_d i p E) ↔ M.mem i ω := (nice.tree.move_domain i).trans
    ⟨fun ⟨j, hj, sj⟩ => (hω.isOrdinal hZF).transitive j hj i sj.predecessor_mem,
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
