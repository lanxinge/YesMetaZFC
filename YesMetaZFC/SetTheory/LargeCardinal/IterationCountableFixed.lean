import YesMetaZFC.SetTheory.LargeCardinal.IterationAttempt
import YesMetaZFC.Model.SetTheory.Internal.EmbeddingFixed

/-! # 原可数树的编码在复制嵌入下固定

公共可数传递载体先被逐点固定。模型域是其子集，关系和树嵌入的坐标
都落在该载体中；自然数索引的模型列、嵌入列及枚举列因而整体固定。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem it_countable_fixed_l {ω T Q G E C ι c Z V d U W j : M.Domain}
    (hω : M.IsOmega ω) (tree : It_diagram_d hZF ω ω T Q G) (en : Ja_enum_d I ω ω Q E)
    (hZ : M.TransitiveSet Z) (hU : M.TransitiveSet U) (mz : Smem_d I c Z V) (mu : Smem_d I d U W)
    (hj : Smap_d I ω c d Z U j) (algebra : Sc_algebra_d Z) (hωZ : M.mem ω Z)
    (hC : M.mem C Z) (hι : M.mem ι Z) (trans : M.TransitiveSet C) (inj : M.IsSetInjectionFromTo I ι C ω)
    (cover : ∀ i a X R, Rd_entry_d i a Q → KPair_d M a X R → M.MemberSubset X C)
    (hT : M.mem T Z) (hQ : M.mem Q Z) (hG : M.mem G Z) (hE : M.mem E Z) :
    Rd_entry_d C C j ∧ (∀ x, M.mem x C → Rd_entry_d x x j) ∧
      Rd_entry_d T T j ∧ Rd_entry_d Q Q j ∧ Rd_entry_d G G j ∧ Rd_entry_d E E j := by
  obtain ⟨fixed, point, _⟩ := hj.countable_fixed_l hZF hω hZ hU mz mu hωZ hC trans hι inj
  have natural := hj.natural_l hZF hω hZ hU mz mu hωZ
  have omega := hj.omega_l I hZF hω hZ hU mz mu hωZ
  have order := hj.fixed_relation_l hZF hω hZ hU mz mu omega natural hT ⟨tree.order.relation, tree.order.bound⟩
  have pairs r (hr : M.mem r T) : Rd_entry_d r r j := by
    obtain ⟨i, k, pair⟩ := tree.order.relation r hr
    have bounds := tree.order.bound i k ⟨r, pair, hr⟩
    exact hj.fixed_pair_l hZF hω hZ hU mz mu (hZ T hT r hr) pair (natural i bounds.1) (natural k bounds.2)
  have model i a X R (ha : Rd_entry_d i a Q) (ma : Smdl_d I a X R) : Rd_entry_d a a j := by
    have owned := rd_entry_transitive_l hZ hQ ha
    have coords := ma.1.mem_l M hZ owned.2
    have sub := cover i a X R ha ma.1
    have hx := hj.fixed_subset_l hZF hω hZ hU mz mu fixed point coords.1 sub
    have hr := hj.fixed_relation_l hZF hω hZ hU mz mu fixed point coords.2
      ⟨ma.2.2.1, fun x y hxy => ⟨sub x (ma.2.2.2 x y hxy).1, sub y (ma.2.2.2 x y hxy).2⟩⟩
    exact hj.fixed_pair_l hZF hω hZ hU mz mu owned.2 ma.1 hx hr
  have function D f (hD : Rd_entry_d D D j) (pts : ∀ x, M.mem x D → Rd_entry_d x x j)
      (hf : M.mem f Z) (fn : M.IsSetFunction I f) (dom : M.IsDomainOf I D f)
      (values : ∀ x y, Rd_entry_d x y f → Rd_entry_d y y j) : Rd_entry_d f f j := by
    obtain ⟨B, hB, coords⟩ := algebra.envelope_l hf
    apply hj.fixed_function_l hZF hω hZ hU mz mu hD pts hB hf
      (fn0_of_function_l (ZF.modelsKP hZF) ⟨fn, dom, fun x hx => ?_⟩) values
    obtain ⟨y, hxy⟩ := (dom x).mp hx
    exact ⟨y, (coords x y hxy).2, hxy⟩
  have models := function ω Q omega natural hQ tree.model_function tree.model_domain (fun i a ha => by
    obtain ⟨X, R, ma⟩ := tree.models i a ha
    exact model i a X R ha ma)
  have maps := function T G order pairs hG tree.map_function tree.map_domain (fun r f hr => by
    obtain ⟨i, k, pair⟩ := tree.order.relation r ((tree.map_domain r).mpr ⟨f, hr⟩)
    have edge : It_map_d G i k f := ⟨r, pair, hr⟩
    have bounds := tree.order.bound i k (tree.map_bound_l hZF edge)
    obtain ⟨a, A, R, ha, ma⟩ := tree.model_l hZF bounds.1
    obtain ⟨b, B, S, hb, mb⟩ := tree.model_l hZF bounds.2
    have full := tree.elementary i k f a A R b B S edge ha hb ma mb
    exact hj.fixed_relation_l hZF hω hZ hU mz mu fixed point (rd_entry_transitive_l hZ hG hr).2
      ⟨full.1.1.1.1, fun x y hxy => ⟨cover i a A R ha ma.1 x (full.1.1.input_mem_of_pairMember hxy),
        cover k b B S hb mb.1 y (full.1.1.output_mem_of_pairMember hxy)⟩⟩)
  have enumeration := function ω E omega natural hE en.function en.domain (fun i e he => by
    obtain ⟨a, A, R, ha, ma⟩ := tree.model_l hZF ((en.domain i).mpr ⟨e, he⟩)
    have fn := (en.rows i e a A R he ha ma.1).1
    have hA := (ma.1.mem_l M hZ (rd_entry_transitive_l hZ hQ ha).2).1
    exact hj.fixed_function_l hZF hω hZ hU mz mu omega natural hA (rd_entry_transitive_l hZ hE he).2 fn
      (fun x y hxy => point y (cover i a A R ha ma.1 y (fn.bound_l hxy).2)))
  exact ⟨fixed, point, order, models, maps, enumeration⟩

end YesMetaZFC.SetTheory.LargeCardinal
