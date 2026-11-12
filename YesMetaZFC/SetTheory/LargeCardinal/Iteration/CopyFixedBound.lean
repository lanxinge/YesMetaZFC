import YesMetaZFC.SetTheory.LargeCardinal.Iteration.FrameUnion
import YesMetaZFC.SetTheory.LargeCardinal.Iteration.CopyRoundSyntax
import YesMetaZFC.Model.SetTheory.Relations.Parity

/-! # 固定 nice 树的活动前缀与共同端点

活动所属模型使用真实传递呈示；两个活动步之间的 padding 保留同一模型。
内部自然数归纳因此恢复当前活动点之前的全部传递模型，再由完整前驱图
把共同层端点识别为原支撑本身。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

/-- 两侧真实传递呈示中的共同层图及端点具有相同背景对象。 -/
theorem Ic_common_d.mem_endpoint_l {X R Y S L l U V D t c d : M.Domain}
    (h : Ic_common_d I X R Y S L l U V D t)
    (mx : Smem_d I c X R) (my : Smem_d I d Y S)
    (xt : M.TransitiveSet X) (yt : M.TransitiveSet Y) : L = l := by
  have rank := (rr_rank_mem_l I (ZF.modelsKP hZF) mx xt h.left_rank.1 h.left_rank.2.1).mp h.left_rank
  have dc x : M.mem x D ↔ M.mem x U := (h.carrier x).trans
    ⟨fun hx => ((mx.2 x U).mp hx.2).2.2,fun hx =>
      ⟨xt U h.left_rank.2.1 x hx,(mx.2 x U).mpr ⟨xt U h.left_rank.2.1 x hx,h.left_rank.2.1,hx⟩⟩⟩
  have eq := hZF.1.eq_of_same_members D U dc
  subst D
  have layer : Rr_layer_d I U Y S V t := by
    refine ⟨rank.transitive_l xt h.left_rank.2.1,h.right_rank.2.1,h.injection,h.image,?_⟩
    intro x y hxy z
    apply (h.pred x y hxy z).trans
    constructor
    · rintro ⟨a,ha,az⟩
      exact ⟨a,((mx.2 a x).mp ha).2.2,az⟩
    · rintro ⟨a,ha,az⟩
      have hx := xt U h.left_rank.2.1 x (h.injection.1.input_mem_of_pairMember hxy)
      exact ⟨a,(mx.2 a x).mpr ⟨xt x hx a ha,hx,ha⟩,az⟩
  have fixed := (layer.mem_l (ZF.modelsKP hZF) yt my).2
  apply hZF.1.eq_of_same_members L l
  intro x
  constructor
  · intro hx
    have hxU := rank.ordinal_subset_l hZF xt h.left_rank.2.1 x hx
    exact ((my.2 x l).mp ((h.endpoint.2.2 x).mpr ⟨x,xt L h.left_rank.1 x hx,
      (mx.2 x L).mpr ⟨xt L h.left_rank.1 x hx,h.left_rank.1,hx⟩,
      (fixed x x).mpr ⟨hxU,rfl⟩⟩)).2.2
  · intro hx
    obtain ⟨a,_,ha,ax⟩ := (h.endpoint.2.2 x).mp
      ((my.2 x l).mpr ⟨yt l h.right_rank.1 x hx,h.right_rank.1,hx⟩)
    exact ((fixed a x).mp ax).2.symm ▸ ((mx.2 a L).mp ha).2.2

/-- 当前活动点之前，每行已传递规范化，或仍是最后一个 padding 尾段的同一模型。 -/
theorem It_pnice_d.active_prefix_l {ω c T Q G E L n ρ : M.Domain}
    (nice : It_pnice_d hZF ω c ω T Q G E L) (hn : M.mem n ω) (active : Rd_entry_d n ρ L) :
    ∀ i a, (i = n ∨ M.mem i n) → Rd_entry_d i a Q →
      ∃ X R, Smem_d I a X R ∧ M.TransitiveSet X := by
  let normal a := ∃ X R, Smem_d I a X R ∧ M.TransitiveSet X
  have normalized i μ a (hi : Rd_entry_d i μ L) (ha : Rd_entry_d i a Q) : normal a := by
    obtain ⟨p,κ,F,hp,pay⟩ := (nice.levels i μ).mp hi
    obtain ⟨b,X,R,hb,model,trans,_,_⟩ := nice.exactness i p κ μ F hp pay
    exact nice.tree.diagram.model_function.2 i b a hb ha ▸ ⟨X,R,model,trans⟩
  let η : Env M 1 := ⟨fun _ => Q,fun _ => Q⟩
  let φ : UnarySchema 1 := { body := set[2] ⟪∀ i a,
    (i = ⌜(.newest : Term 2)⌝ₛ ∨ i ∈ ⌜(.newest : Term 2)⌝ₛ) →
    ⌜rd_entry0_m⌝ₚ(i,a,⌜(.bound 1 : Term 2)⌝ₛ) →
      (∃ X R, ⌜(smem_m (𝒞 := kpair_convention_l))⌝ₚ(a,X,R) ∧ ⌜Formula.isTransitive⌝ₚ(X)) ∨
      ⌜rd_entry0_m⌝ₚ(⌜(.newest : Term 2)⌝ₛ,a,⌜(.bound 1 : Term 2)⌝ₛ)⟫ }
  have sat j : φ.denote η j ↔ ∀ i a, (i = j ∨ M.mem i j) → Rd_entry_d i a Q →
      normal a ∨ Rd_entry_d j a Q := by
    simp only [φ,UnarySchema.denote,Formula.satisfies_forall_iff,Formula.satisfies_imp_iff,
      Formula.satisfies_disj_iff,Formula.satisfies_extensionalEq_iff_eq hZF.1,Formula.satisfies_mem_iff,
      Formula.satisfies_exists_iff,Formula.satisfies_conj_iff,smem_sat_l I,
      Formula.satisfies_isTransitive_iff,rd_entry0_sat_l hZF.1]; rfl
  have all : ∀ j, M.mem j ω → φ.denote η j := by
    apply nice.tree.omega.induction (fun j => φ.denote η j) (ZF.separation_exists_d hZF φ η ω)
    · intro e empty
      apply (sat e).mpr
      intro i a hi ha
      exact hi.elim (fun eq => Or.inr (eq ▸ ha)) (fun hi => (empty i hi).elim)
    · intro j hj ih k succ
      obtain ⟨k',step,hk'⟩ := nice.tree.omega.1.2 j hj
      have hk : M.mem k ω := step.eq hZF.1 succ ▸ hk'
      have keep a (ha : Rd_entry_d j a Q) : normal a ∨ Rd_entry_d k a Q := by
        classical
        by_cases act : ∃ μ, Rd_entry_d j μ L
        · obtain ⟨μ,hμ⟩ := act
          exact Or.inl (normalized j μ a hμ ha)
        · obtain ⟨_,b,_,d,_,p,_,hb,_,hd,_,hp,move⟩ := nice.tree.steps j k hk succ
          rcases move with ⟨_,_,eq,_⟩ | ⟨κ,μ,F,_,_,_,_,pay,_⟩
          · have eq' := nice.tree.diagram.model_function.2 j b a hb ha
            exact Or.inr (eq' ▸ eq ▸ hd)
          · exact (act ⟨μ,(nice.levels j μ).mpr ⟨p,κ,F,hp,pay⟩⟩).elim
      apply (sat k).mpr
      intro i a hi ha
      rcases hi with rfl | hi
      · exact Or.inr ha
      · have old : i = j ∨ M.mem i j := ((succ i).mp hi).elim Or.inr
          (fun eq => Or.inl (hZF.1.eq_of_same_members i j eq))
        exact ((sat j).mp ih i a old ha).elim Or.inl (keep a)
  intro i a hi ha
  exact ((sat n).mp (all n hn) i a hi ha).elim id (normalized n ρ a active)

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 固定 nice 树中本次支撑严格高于真实历史界

界的非空来源是某两行的最大共同端点。历史给出的同两行共同层将它识别为
已实施的原支撑；规范化端点与 nice 的支撑递增随后给出当前模型中的严格关系。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

/-- 真实活动行自动提供历史最大界及严格支撑比较，不把比较另作假设。 -/
theorem Ic_history_d.fixed_bound_l
    {ω c₀ T Q G E L m H ST QT GT n N R B σ u U β c ρ : M.Domain}
    (nice : It_pnice_d hZF ω c₀ ω T Q G E L)
    (hist : Ic_history_d hZF ω T Q G E L m H ST QT GT)
    (top : Ic_at_d H n N B σ u U β) (hn : M.mem n ω)
    (qc : Rd_entry_d n c Q) (mn : Smdl_d I c N R) (active : Rd_entry_d n ρ L) :
    ∃ χ, Ic_bound_d I H Q N R σ n χ ∧ Rd_entry_d χ ρ R := by
  have hw := nice.tree.omega
  have qf := nice.tree.diagram.model_function
  obtain ⟨p,κ,F,hp,pay⟩ := (nice.levels n ρ).mp active
  obtain ⟨c',N',R',qc',model,trans,strong,card⟩ := nice.exactness n p κ ρ F hp pay
  have eq := qf.2 n c' c qc' qc
  subst c'
  obtain ⟨eqN,eqR⟩ := smdl_unique_l I model.1 mn
  subst N' R'
  obtain ⟨ωN,ρN,card⟩ := card
  have ωρ : M.mem ω ρ := ((Formula.satisfies_conj_iff ..).mp card).1
  have ord : M.IsOrdinal ρ := strong.2.2.2.2.1
  obtain ⟨χ,bound⟩ := hist.height_bound_l hZF top hw hn qf qc mn
  refine ⟨χ,bound,?_⟩
  have χN := bound.ordinal.1 0
  apply (model.2 χ ρ).mpr
  refine ⟨χN,ρN,?_⟩
  rcases bound.origin with empty | ⟨i,hi,height⟩
  · exact ord.empty_mem_of_nonempty (ZF.modelsKP hZF) ⟨ω,ωρ⟩ (fun x hx =>
      empty x (trans χ χN x hx) ((model.2 x χ).mpr ⟨trans χ χN x hx,χN,hx⟩))
  · obtain ⟨_,X,A,π,z,Z,α,B',u',U',β',d,e,S,μ,φ,V,W,D,t,ai,an,qi,qn,mx,mn',common⟩ := height
    have eq := qf.2 n e c qn qc
    subst e
    obtain ⟨X',S',old,xt⟩ := nice.active_prefix_l hZF hn active i d (Or.inr hi) qi
    obtain ⟨eqX,eqS⟩ := smdl_unique_l I old.1 mx
    subst X' S'
    have endpoint : μ = χ := common.common.mem_endpoint_l hZF old model xt trans
    obtain ⟨d',qd',_,row⟩ := hist.row_l hZF ai
    have eq := qf.2 i d' d qd' qi
    subst d'
    obtain ⟨S',SA,_,a,_,_,mx',ma,_,_,_,_,_,_,map⟩ := row
    have eq := (smdl_unique_l I mx' mx).2
    subst S'
    rcases hist.past i n X A π z Z α N B' σ u' U' β' ai an hi with
        ⟨d',qi',qn',eqX,eqA,eqπ,_⟩ |
        ⟨k,ν,l,φ',V',W',D',s,d',e',S',R',_,kn,hν,_,qi',qn',mx',mn'',same⟩
    · have eq := qf.2 i d' d qi' qi
      subst d'
      have eq := qf.2 n d c qn' qc
      subst d X A π
      have eq := (smdl_unique_l I mx mn).2
      subst S
      exact (common.not_refl_l hZF hw mx ma map).elim
    · have eq := qf.2 i d' d qi' qi
      subst d'
      have eq := qf.2 n e' c qn' qc
      subst e'
      have eq := (smdl_unique_l I mx' mx).2
      subst S'
      have eq := (smdl_unique_l I mn'' mn).2
      subst R'
      obtain ⟨_,_,_,own⟩ := hist.row_l hZF an
      obtain ⟨_,_,_,_,_,_,_,_,_,_,_,_,_,_,copy⟩ := own
      have equal := (common.height_unique_l hZF same hw mx ma map copy.1).1
      have χν : χ = ν := endpoint.symm.trans equal
      exact χν.symm ▸ nice.increasing k n ν ρ hν active kn

end YesMetaZFC.SetTheory.LargeCardinal
