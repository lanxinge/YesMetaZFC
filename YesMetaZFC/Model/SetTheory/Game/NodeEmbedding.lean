import YesMetaZFC.Model.SetTheory.Reflection.TransitiveSequence
import YesMetaZFC.SetTheory.FunctionConstruction
import YesMetaZFC.SetTheory.Cumulative
import YesMetaZFC.SetTheory.Descriptive.Tree.TreeTail
import YesMetaZFC.Model.SetTheory.Internal.Hereditary
import YesMetaZFC.Model.SetTheory.Internal.FiniteSetCode
import YesMetaZFC.Model.SetTheory.Internal.FiniteSource
import YesMetaZFC.Model.SetTheory.Types.Embedding
import YesMetaZFC.SetTheory.FlatPairing.CumulativeSource
import YesMetaZFC.SetTheory.Rank
import YesMetaZFC.Model.SetTheory.Reflection.RankLargest
import YesMetaZFC.Model.SetTheory.Embedding.RankFixed
import YesMetaZFC.Model.SetTheory.Internal.FiniteRecordRelative

/-! # 类型游戏的完整节点谓词

节点仍是有限函数图。三张坐标图都有同一个精确定义域，逐点合成的三元组图
必须属于树；不从一个裸成员式推断函数性，也不对标签的枚举位置加条件。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} (I : kpair_convention_l.Interpretation M)

def Tg_graph_d (k f : M.Domain) : Prop := M.IsSetFunction I f ∧ M.IsDomainOf I k f

def tg_graph_m {d} (k f : Term d) : Formula 1 d :=
  .conj (Formula.isFunction kpair_convention_l f) (Formula.isDomain kpair_convention_l k f)
derive_free_closed tg_graph_m

theorem tg_graph_sat_l (hE : Extensional M) {d} (ρ : Env M d) (k f : Term d) :
    Formula.satisfies ρ (tg_graph_m k f) ↔ Tg_graph_d I (k.eval ρ) (f.eval ρ) := by
  simp only [tg_graph_m, Tg_graph_d, Formula.satisfies_conj_iff,
    Formula.satisfies_isFunction_iff I hE, Formula.satisfies_isDomain_iff I]

def Tg_join_d (k s t g q : M.Domain) : Prop := Tg_graph_d I k q ∧ ∀ i, M.mem i k →
  ∃ x y z v p, M.PairMember I i x s ∧ M.PairMember I i y t ∧ M.PairMember I i z g ∧
    I.Codes v y z ∧ I.Codes p x v ∧ M.PairMember I i p q

def tg_join_m {d} (k s t g q : Term d) : Formula 1 d := set[d] ⟪⌜tg_graph_m⌝ₚ(⌜k⌝ₛ, ⌜q⌝ₛ) ∧
  (∀ i ∈ ⌜k⌝ₛ, ∃ x y z v p, ⌜Formula.orderedPairMem kpair_convention_l⌝ₚ(i, x, ⌜s⌝ₛ) ∧
    ⌜Formula.orderedPairMem kpair_convention_l⌝ₚ(i, y, ⌜t⌝ₛ) ∧
    ⌜Formula.orderedPairMem kpair_convention_l⌝ₚ(i, z, ⌜g⌝ₛ) ∧
    ⌜kpair_convention_l.code⌝ₚ(v, y, z) ∧ ⌜kpair_convention_l.code⌝ₚ(p, x, v) ∧
    ⌜Formula.orderedPairMem kpair_convention_l⌝ₚ(i, p, ⌜q⌝ₛ))⟫
derive_free_closed tg_join_m

theorem tg_join_sat_l (hE : Extensional M) {d} (ρ : Env M d) (k s t g q : Term d) :
    Formula.satisfies ρ (tg_join_m k s t g q) ↔ Tg_join_d I (k.eval ρ) (s.eval ρ) (t.eval ρ) (g.eval ρ) (q.eval ρ) := by
  simp only [tg_join_m, Tg_join_d, Formula.satisfies_conj_iff, tg_graph_sat_l I hE,
    Formula.satisfies_forallMem_iff, Formula.satisfies_exists_iff, Formula.satisfies_orderedPairMem_iff I,
    I.satisfies_code_iff, Definitional.Term.eval_weaken]
  rfl

def Tg_node_d (k S s t g : M.Domain) : Prop := Tg_graph_d I k s ∧ Tg_graph_d I k t ∧
  Tg_graph_d I k g ∧ ∃ q, M.mem q S ∧ Tg_join_d I k s t g q

def tg_node_m {d} (k S s t g : Term d) : Formula 1 d := set[d] ⟪
  ⌜tg_graph_m⌝ₚ(⌜k⌝ₛ, ⌜s⌝ₛ) ∧ ⌜tg_graph_m⌝ₚ(⌜k⌝ₛ, ⌜t⌝ₛ) ∧ ⌜tg_graph_m⌝ₚ(⌜k⌝ₛ, ⌜g⌝ₛ) ∧
    (∃ q ∈ ⌜S⌝ₛ, ⌜tg_join_m⌝ₚ(⌜k⌝ₛ, ⌜s⌝ₛ, ⌜t⌝ₛ, ⌜g⌝ₛ, q))⟫
derive_free_closed tg_node_m

theorem tg_node_sat_l (hE : Extensional M) {d} (ρ : Env M d) (k S s t g : Term d) :
    Formula.satisfies ρ (tg_node_m k S s t g) ↔ Tg_node_d I (k.eval ρ) (S.eval ρ) (s.eval ρ) (t.eval ρ) (g.eval ρ) := by
  simp only [tg_node_m, Tg_node_d, Formula.satisfies_conj_iff, tg_graph_sat_l I hE,
    Formula.satisfies_existsMem_iff, tg_join_sat_l I hE, Definitional.Term.eval_weaken]
  rfl

theorem tg_graph_empty_l {e : M.Domain} (he : ∀ x, ¬ M.mem x e) : Tg_graph_d I e e := by
  have no a b : ¬ M.PairMember I a b e := fun ⟨p, _, hp⟩ => he p hp
  exact ⟨⟨fun p hp => (he p hp).elim, fun a b _ h _ => (no a b h).elim⟩,
    fun i => iff_of_false (he i) (fun ⟨x, hx⟩ => no i x hx)⟩

/-- 长度零的完整节点条件恰为空根属于树。 -/
theorem tg_node_empty_l (hE : Extensional M) {e S : M.Domain} (he : ∀ x, ¬ M.mem x e) :
    Tg_node_d I e S e e e ↔ M.mem e S := by
  constructor
  · rintro ⟨_, _, _, q, hq, graph, _⟩
    have empty p (hp : M.mem p q) : False := by
      obtain ⟨i, x, pair⟩ := graph.1.1 p hp
      exact he i ((graph.2 i).mpr ⟨x, p, pair, hp⟩)
    exact hE.eq_of_same_members q e (fun x => iff_of_false (empty x) (he x)) ▸ hq
  · intro hS
    have graph := tg_graph_empty_l I he
    exact ⟨graph, graph, graph, e, hS, graph, fun i hi => (he i hi).elim⟩

/-- 三张实际同域函数图总能合成原节点图，字母表和节点均为模型内集合。 -/
theorem tg_join_exists_l (hZF : M.Models ZF) {k X Y Z s t g : M.Domain}
    (hs : M.IsSetFunctionFromTo I s k X) (ht : M.IsSetFunctionFromTo I t k Y) (hg : M.IsSetFunctionFromTo I g k Z) :
    ∃ V P q, M.IsCartesianProduct I V Y Z ∧ M.IsCartesianProduct I P X V ∧
      M.IsSetFunctionFromTo I q k P ∧ Tg_join_d I k s t g q := by
  obtain ⟨V, hv⟩ := ZF.exists_cartesianProduct hZF I Y Z
  obtain ⟨P, hp⟩ := ZF.exists_cartesianProduct hZF I X V
  let φ : BinarySchema 3 := {
    body := set[5] ⟪∃ x y z v,
      ⌜Formula.orderedPairMem kpair_convention_l⌝ₚ(⌜(.bound 1 : Term 5)⌝ₛ, x, ⌜(.bound 4 : Term 5)⌝ₛ) ∧
      ⌜Formula.orderedPairMem kpair_convention_l⌝ₚ(⌜(.bound 1 : Term 5)⌝ₛ, y, ⌜(.bound 3 : Term 5)⌝ₛ) ∧
      ⌜Formula.orderedPairMem kpair_convention_l⌝ₚ(⌜(.bound 1 : Term 5)⌝ₛ, z, ⌜(.bound 2 : Term 5)⌝ₛ) ∧
      ⌜kpair_convention_l.code⌝ₚ(v, y, z) ∧ ⌜kpair_convention_l.code⌝ₚ(⌜(.newest : Term 5)⌝ₛ, x, v)⟫ }
  let ρ : Env M 3 := ⟨Fin.cases g (Fin.cases t (fun _ => s)), fun _ => s⟩
  have read i p : φ.denote ρ i p ↔ ∃ x y z v, M.PairMember I i x s ∧ M.PairMember I i y t ∧
      M.PairMember I i z g ∧ I.Codes v y z ∧ I.Codes p x v := by
    simp only [φ, BinarySchema.denote, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
      Formula.satisfies_orderedPairMem_iff I, I.satisfies_code_iff]
    rfl
  obtain ⟨q, fn, graph⟩ := ZF.exists_setFunctionFromTo_of_denote hZF I φ ρ (source := k) (target := P)
    (fun i hi => by
      obtain ⟨x, _, hx⟩ := hs.2.2 i hi
      obtain ⟨y, _, hy⟩ := ht.2.2 i hi
      obtain ⟨z, _, hz⟩ := hg.2.2 i hi
      obtain ⟨v, cv⟩ := I.total y z
      obtain ⟨p, cp⟩ := I.total x v
      exact ⟨p, (read i p).mpr ⟨x, y, z, v, hx, hy, hz, cv, cp⟩⟩)
    (fun i _ p q hp hq => by
      obtain ⟨x, y, z, v, hx, hy, hz, cv, cp⟩ := (read i p).mp hp
      obtain ⟨x', y', z', v', hx', hy', hz', cv', cq⟩ := (read i q).mp hq
      have ex := hs.1.2 i x' x hx' hx
      have ey := ht.1.2 i y' y hy' hy
      have ez := hg.1.2 i z' z hz' hz
      subst x' y' z'
      exact I.unique cp (I.unique cv' cv ▸ cq))
    (fun i p _ h => by
      obtain ⟨x, y, z, v, hx, hy, hz, cv, cp⟩ := (read i p).mp h
      exact (hp p).mpr ⟨x, hs.output_mem_of_pairMember hx, v,
        (hv v).mpr ⟨y, ht.output_mem_of_pairMember hy, z, hg.output_mem_of_pairMember hz, cv⟩, cp⟩)
  refine ⟨V, P, q, hv, hp, fn, ⟨fn.1, fn.2.1⟩, fun i hi => ?_⟩
  obtain ⟨p, _, hq⟩ := fn.2.2 i hi
  obtain ⟨x, y, z, v, hx, hy, hz, cv, cp⟩ := (read i p).mp ((graph i p).mp hq).2
  exact ⟨x, y, z, v, p, hx, hy, hz, cv, cp, hq⟩

end YesMetaZFC.SetTheory.Internal

/-! ## 原树两组标签严格低于原树秩界

从实际三元节点只展开一份累积历史，两组标签共用同一秩比较。
α 不要求为极限序数；旧第三图接口直接读取该共同证明的第二分量。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

/-- 两个辅助坐标的标签对都属于包含原树的同一实际 Vα。 -/
theorem Tg_node_d.aux_labels_rank_l {α V k S s t g : M.Domain}
    (hV : V_d I α V) (hS : M.mem S V) (node : Tg_node_d I k S s t g) :
    M.MemberSubset t V ∧ M.MemberSubset g V := by
  have tr := v_transitive_l I hV
  obtain ⟨q,hq,_,join⟩ := node.2.2.2
  have label {p i z} (cp : KPair_d M p i z)
      (point : Rd_entry_d i z t ∨ Rd_entry_d i z g) : M.mem p V := by
    have hi := point.elim (fun h => (node.2.1.2 i).mpr ⟨z,h⟩)
      (fun h => (node.2.2.1.2 i).mpr ⟨z,h⟩)
    obtain ⟨x,y,z',v,a,_,hy,hz,cv,ca,j,cj,hj⟩ := join i hi
    obtain ⟨β,W,hb,hW,sub⟩ := (ZF.v_unfold_l I hZF hV j).mp (tr q (tr S hS q hq) j hj)
    obtain ⟨s₀,t₀,hs₀,ht₀,hj⟩ := cj
    obtain ⟨s₁,t₁,hs₁,ht₁,hp⟩ := cp
    have ss := hZF.1.eq_of_same_members s₁ s₀ (fun b => (hs₁ b).trans (hs₀ b).symm)
    have hsW : M.mem s₁ W := ss.symm ▸ sub s₀ ((hj s₀).mpr (Or.inl rfl))
    obtain ⟨γ,Z,hγ,hZ,tz⟩ := (ZF.v_unfold_l I hZF hW t₀).mp (sub t₀ ((hj t₀).mpr (Or.inr rfl)))
    have trZ := v_transitive_l I hZ
    have hiZ := tz i ((ht₀ i).mpr (Or.inl rfl))
    have both := cv.mem_l M trZ (ca.mem_l M trZ (tz a ((ht₀ a).mpr (Or.inr rfl)))).2
    have hzZ : M.mem z Z := point.elim
      (fun h => node.2.1.1.2 i y z hy h ▸ both.1)
      (fun h => node.2.2.1.1.2 i z' z hz h ▸ both.2)
    have htW : M.mem t₁ W := (ZF.v_unfold_l I hZF hW t₁).mpr ⟨γ,Z,hγ,hZ,fun b hb =>
      ((ht₁ b).mp hb).elim (fun eq => eq.symm ▸ hiZ) (fun eq => eq.symm ▸ hzZ)⟩
    exact (ZF.v_unfold_l I hZF hV p).mpr ⟨β,W,hb,hW,fun b hb =>
      ((hp b).mp hb).elim (fun eq => eq.symm ▸ hsW) (fun eq => eq.symm ▸ htW)⟩
  constructor
  · intro p hp
    obtain ⟨i,z,cp⟩ := node.2.1.1.1 p hp
    exact label cp (Or.inl ⟨p,cp,hp⟩)
  · intro p hp
    obtain ⟨i,z,cp⟩ := node.2.2.1.1.1 p hp
    exact label cp (Or.inr ⟨p,cp,hp⟩)

/-- 单辅助图的原消费者沿用同一份双组秩证明。 -/
theorem Tg_node_d.labels_rank_l {α V k S s t g : M.Domain}
    (hV : V_d I α V) (hS : M.mem S V) (node : Tg_node_d I k S s t g) : M.MemberSubset g V :=
  (node.aux_labels_rank_l hZF hV hS).2

end YesMetaZFC.SetTheory.Internal

/-! ## 三坐标节点的精确限制与坐标唯一性 -/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel Descriptive
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Tg_join_d.typed_l {n A B C P Y s a b q : M.Domain}
    (join : Tg_join_d I n s a b q) (fs : Fn0_d n A s) (fa : Fn0_d n B a) (fb : Fn0_d n C b)
    (pair : M.IsCartesianProduct I P B C) (triple : M.IsCartesianProduct I Y A P) : Fn0_d n Y q := by
  refine fn0_of_function_l (ZF.modelsKP hZF) ⟨join.1.1,join.1.2,?_⟩
  intro i hi
  obtain ⟨x,y,z,t,p,ix,iy,iz,tp,pp,ip⟩ := join.2 i hi
  exact ⟨p,(triple p).mpr ⟨x,(fs.bound_l ix).2,t,
    (pair t).mpr ⟨y,(fa.bound_l iy).2,z,(fb.bound_l iz).2,tp⟩,pp⟩,ip⟩

theorem Tg_join_d.coordinates_l {n s a b q s' a' b' : M.Domain}
    (join : Tg_join_d I n s a b q) (other : Tg_join_d I n s' a' b' q)
    (gs : Tg_graph_d I n s) (ga : Tg_graph_d I n a) (gb : Tg_graph_d I n b)
    (gs' : Tg_graph_d I n s') (ga' : Tg_graph_d I n a') (gb' : Tg_graph_d I n b') :
    s = s' ∧ a = a' ∧ b = b' := by
  have values i (hi : M.mem i n) : ∃ x y z,
      Rd_entry_d i x s ∧ Rd_entry_d i x s' ∧ Rd_entry_d i y a ∧ Rd_entry_d i y a' ∧
      Rd_entry_d i z b ∧ Rd_entry_d i z b' := by
    obtain ⟨x,y,z,t,p,ix,iy,iz,tp,pp,ip⟩ := join.2 i hi
    obtain ⟨x',y',z',t',p',ix',iy',iz',tp',pp',ip'⟩ := other.2 i hi
    have eq := join.1.1.2 i p p' ip ip'
    obtain ⟨ex,et⟩ := (I).injective (eq ▸ pp) pp'
    obtain ⟨ey,ez⟩ := (I).injective (et ▸ tp) tp'
    exact ⟨x,y,z,ix,ex.symm ▸ ix',iy,ey.symm ▸ iy',iz,ez.symm ▸ iz'⟩
  have same {f g : M.Domain} (ff : Tg_graph_d I n f) (fg : Tg_graph_d I n g)
      (points : ∀ i, M.mem i n → ∃ x, Rd_entry_d i x f ∧ Rd_entry_d i x g) : f = g := by
    apply ff.1.1.eq_of_pairMember_iff hZF.1 fg.1.1
    intro i x
    constructor
    · intro ix
      obtain ⟨y,iy,iy'⟩ := points i ((ff.2 i).mpr ⟨x,ix⟩)
      exact ff.1.2 i y x iy ix ▸ iy'
    · intro ix
      obtain ⟨y,iy,iy'⟩ := points i ((fg.2 i).mpr ⟨x,ix⟩)
      exact fg.1.2 i y x iy' ix ▸ iy
  exact ⟨same gs gs' (by intro i hi; obtain ⟨x,y,z,ix,ix',_⟩ := values i hi; exact ⟨x,ix,ix'⟩),
    same ga ga' (by intro i hi; obtain ⟨x,y,z,_,_,iy,iy',_⟩ := values i hi; exact ⟨y,iy,iy'⟩),
    same gb gb' (by intro i hi; obtain ⟨x,y,z,_,_,_,_,iz,iz'⟩ := values i hi; exact ⟨z,iz,iz'⟩)⟩

theorem Tg_node_d.restrict_l {ω Y F S n m s a b : M.Domain}
    (space : Fseq_space_d I ω Y F) (tree : Tree_d F S)
    (node : Tg_node_d I n S s a b) (hm : M.mem m ω) (sub : M.MemberSubset m n)
    {s' a' b' : M.Domain} (rs : M.IsRestrictionOf I s' s m) (ra : M.IsRestrictionOf I a' a m)
    (rb : M.IsRestrictionOf I b' b m) : Tg_node_d I m S s' a' b' := by
  obtain ⟨gs,ga,gb,q,hq,join⟩ := node
  obtain ⟨_,_,fq⟩ := (space q).mp (tree.1 q hq)
  have restrict {f g : M.Domain} (graph : Tg_graph_d I n f) (cut : M.IsRestrictionOf I g f m) : Tg_graph_d I m g :=
    ⟨cut.isSetFunction graph.1,cut.isDomainOf graph.2 sub⟩
  obtain ⟨q',rq⟩ := ZF.exists_restriction hZF I q m
  have gq := restrict join.1 rq
  have length := fq.2.1.eq hZF.1 join.1.2
  have fq : M.IsSetFunctionFromTo I q n Y := length ▸ fq
  have fq' := rq.isSetFunctionFromTo fq sub
  refine ⟨restrict gs rs,restrict ga ra,restrict gb rb,q',
    tree.2 q hq q' ((space q').mpr ⟨m,hm,fq'⟩) ((ds_restrict_iff_l I fq' fq.1).mp rq),gq,?_⟩
  intro i hi
  obtain ⟨x,y,z,t,p,ix,iy,iz,tp,pp,ip⟩ := join.2 i (sub i hi)
  exact ⟨x,y,z,t,p,(rs.2 i x).mpr ⟨hi,ix⟩,(ra.2 i y).mpr ⟨hi,iy⟩,
    (rb.2 i z).mpr ⟨hi,iz⟩,tp,pp,(rq.2 i p).mpr ⟨hi,ip⟩⟩

end YesMetaZFC.SetTheory.Internal

/-! ## 三图合成的有界公式

所有取值都显式限制在原三字母积中，故合成关系可沿成员满地嵌入
和传递极限双向读取。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}}

def tg_join_bound_m {d} (n A B C P Y s a b q : Term d) : Formula 1 d := set[d] ⟪
  ⌜fn0_m⌝ₚ(⌜n⌝ₛ,⌜A⌝ₛ,⌜s⌝ₛ) ∧ ⌜fn0_m⌝ₚ(⌜n⌝ₛ,⌜B⌝ₛ,⌜a⌝ₛ) ∧
  ⌜fn0_m⌝ₚ(⌜n⌝ₛ,⌜C⌝ₛ,⌜b⌝ₛ) ∧ ⌜fn0_m⌝ₚ(⌜n⌝ₛ,⌜Y⌝ₛ,⌜q⌝ₛ) ∧
  (∀ i ∈ ⌜n⌝ₛ, ∃ x ∈ ⌜A⌝ₛ, ∃ y ∈ ⌜B⌝ₛ, ∃ z ∈ ⌜C⌝ₛ, ∃ t ∈ ⌜P⌝ₛ, ∃ p ∈ ⌜Y⌝ₛ,
    ⌜rd_entry0_m⌝ₚ(i,x,⌜s⌝ₛ) ∧ ⌜rd_entry0_m⌝ₚ(i,y,⌜a⌝ₛ) ∧ ⌜rd_entry0_m⌝ₚ(i,z,⌜b⌝ₛ) ∧
    ⌜kpair0_m⌝ₚ(t,y,z) ∧ ⌜kpair0_m⌝ₚ(p,x,t) ∧ ⌜rd_entry0_m⌝ₚ(i,p,⌜q⌝ₛ))⟫
derive_free_closed tg_join_bound_m

theorem tg_join_bound_delta_l {d} (n A B C P Y s a b q : Term d) : (tg_join_bound_m n A B C P Y s a b q).IsDelta0 := by
  unfold tg_join_bound_m
  repeat first
    | exact fn0_delta_l .. | exact rd_entry0_delta_l .. | exact kpair0_delta_l ..
    | apply Formula.IsDelta0.conj | apply Formula.IsDelta0.forallMem | apply Formula.IsDelta0.existsMem

theorem tg_join_bound_sat_l (hZF : M.Models ZF) {d} (ρ : Env M d) (n A B C P Y s a b q : Term d)
    (pair : M.IsCartesianProduct (kp_pair_l (ZF.modelsKP hZF)) (P.eval ρ) (B.eval ρ) (C.eval ρ))
    (triple : M.IsCartesianProduct (kp_pair_l (ZF.modelsKP hZF)) (Y.eval ρ) (A.eval ρ) (P.eval ρ)) :
    Formula.satisfies ρ (tg_join_bound_m n A B C P Y s a b q) ↔
      Fn0_d (n.eval ρ) (A.eval ρ) (s.eval ρ) ∧ Fn0_d (n.eval ρ) (B.eval ρ) (a.eval ρ) ∧
      Fn0_d (n.eval ρ) (C.eval ρ) (b.eval ρ) ∧
      Tg_join_d (kp_pair_l (ZF.modelsKP hZF)) (n.eval ρ) (s.eval ρ) (a.eval ρ) (b.eval ρ) (q.eval ρ) := by
  let I := kp_pair_l (ZF.modelsKP hZF)
  simp only [tg_join_bound_m,Formula.satisfies_conj_iff,fn0_sat_l hZF.1,Formula.satisfies_forallMem_iff,
    Formula.satisfies_existsMem_iff,rd_entry0_sat_l hZF.1,kpair0_sat_l hZF.1,Definitional.Term.eval_weaken]
  constructor
  · rintro ⟨fs,fa,fb,fq,join⟩
    refine ⟨fs,fa,fb,⟨(fn0_function_l (ZF.modelsKP hZF) fq).1,(fn0_function_l (ZF.modelsKP hZF) fq).2.1⟩,?_⟩
    intro i hi
    obtain ⟨x,_,y,_,z,_,t,_,p,_,ix,iy,iz,tp,pp,ip⟩ := join i hi
    exact ⟨x,y,z,t,p,ix,iy,iz,tp,pp,ip⟩
  · rintro ⟨fs,fa,fb,join⟩
    refine ⟨fs,fa,fb,join.typed_l hZF fs fa fb pair triple,?_⟩
    intro i hi
    obtain ⟨x,y,z,t,p,ix,iy,iz,tp,pp,ip⟩ := join.2 i hi
    have ht := (pair t).mpr ⟨y,(fa.bound_l iy).2,z,(fb.bound_l iz).2,tp⟩
    exact ⟨x,(fs.bound_l ix).2,y,(fa.bound_l iy).2,z,(fb.bound_l iz).2,t,ht,p,
      (triple p).mpr ⟨x,(fs.bound_l ix).2,t,ht,pp⟩,ix,iy,iz,tp,pp,ip⟩

theorem Tg_node_d.typed_l (hZF : M.Models ZF) {ω A B C P Y F S n s a b : M.Domain}
    (space : Fseq_space_d (kp_pair_l (ZF.modelsKP hZF)) ω Y F)
    (tree : Descriptive.Tree_d F S)
    (pair : M.IsCartesianProduct (kp_pair_l (ZF.modelsKP hZF)) P B C)
    (triple : M.IsCartesianProduct (kp_pair_l (ZF.modelsKP hZF)) Y A P)
    (node : Tg_node_d (kp_pair_l (ZF.modelsKP hZF)) n S s a b) :
    Fn0_d n A s ∧ Fn0_d n B a ∧ Fn0_d n C b := by
  let I := kp_pair_l (ZF.modelsKP hZF)
  obtain ⟨gs,ga,gb,q,hq,join⟩ := node
  obtain ⟨_,_,fq⟩ := (space q).mp (tree.1 q hq)
  have total i (hi : M.mem i n) : ∃ x y z, M.mem x A ∧ M.mem y B ∧ M.mem z C ∧
      Rd_entry_d i x s ∧ Rd_entry_d i y a ∧ Rd_entry_d i z b := by
    obtain ⟨x,y,z,t,p,ix,iy,iz,tp,pp,ip⟩ := join.2 i hi
    obtain ⟨x',hx,t',ht,pp'⟩ := (triple p).mp (fq.output_mem_of_pairMember ip)
    obtain ⟨ex,et⟩ := (I).injective pp pp'
    obtain ⟨y',hy,z',hz,tp'⟩ := (pair t').mp ht
    obtain ⟨ey,ez⟩ := (I).injective (et ▸ tp) tp'
    exact ⟨x,y,z,ex.symm ▸ hx,ey.symm ▸ hy,ez.symm ▸ hz,ix,iy,iz⟩
  refine ⟨fn0_of_function_l (ZF.modelsKP hZF) ⟨gs.1,gs.2,?_⟩,
    fn0_of_function_l (ZF.modelsKP hZF) ⟨ga.1,ga.2,?_⟩,
    fn0_of_function_l (ZF.modelsKP hZF) ⟨gb.1,gb.2,?_⟩⟩
  · intro i hi; obtain ⟨x,_,_,hx,_,_,ix,_⟩ := total i hi; exact ⟨x,hx,ix⟩
  · intro i hi; obtain ⟨_,y,_,_,hy,_,_,iy,_⟩ := total i hi; exact ⟨y,hy,iy⟩
  · intro i hi; obtain ⟨_,_,z,_,_,hz,_,_,iz⟩ := total i hi; exact ⟨z,hz,iz⟩

end YesMetaZFC.SetTheory.Internal

/-! ## 完整树节点在传递源中的绝对性

所有见证均从已有函数图或树成员中回收。源模型只需传递性，
不要求后继秩层对配对、替换或 ZF 封闭。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} {X : M.Domain} (hX : M.TransitiveSet X)
  (nx : Nonempty {x // M.mem x X}) (hE : Extensional M)
  (hP : ∀ a b : M.Domain, ∃ p, Pair_d M p a b)
local notation "N" => rt_model_l X nx
local notation "I" => kpair_interpretation_l M hE hP
include hX

theorem tg_graph_source_l {d} (ρ : Env N d) (k f : Term d) :
    Formula.satisfies ρ (tg_graph_m k f) ↔ Tg_graph_d I (k.eval ρ).val (f.eval ρ).val := by
  simp only [tg_graph_m, Tg_graph_d, Formula.satisfies_conj_iff,
    rt_function_formula_l hX nx hE hP, rt_domain_formula_l hX nx hE hP]

theorem tg_join_source_l {d} (ρ : Env N d) (k s t g q : Term d) :
    Formula.satisfies ρ (tg_join_m k s t g q) ↔
      Tg_join_d I (k.eval ρ).val (s.eval ρ).val (t.eval ρ).val (g.eval ρ).val (q.eval ρ).val := by
  simp only [tg_join_m, Tg_join_d, Formula.satisfies_conj_iff, tg_graph_source_l hX nx hE hP,
    Formula.satisfies_forallMem_iff, Formula.satisfies_exists_iff,
    rt_entry_formula_l hX nx hE, rt_kpair_formula_l hX nx hE,
    Definitional.Term.eval_weaken, Definitional.Term.eval_newest]
  refine and_congr Iff.rfl ⟨?_, ?_⟩
  · intro h i hi
    obtain ⟨x, y, z, v, p, hx, hy, hz, hv, hp, hq⟩ := h ⟨i, hX _ (k.eval ρ).property i hi⟩ hi
    exact ⟨x.val, y.val, z.val, v.val, p.val, hx, hy, hz, hv, hp, hq⟩
  · intro h i hi
    obtain ⟨x, y, z, v, p, hx, hy, hz, hv, hp, hq⟩ := h i.val hi
    have xp := rd_entry_transitive_l hX (s.eval ρ).property hx
    have yp := rd_entry_transitive_l hX (t.eval ρ).property hy
    have zp := rd_entry_transitive_l hX (g.eval ρ).property hz
    have pp := (rd_entry_transitive_l hX (q.eval ρ).property hq).2
    have vp := (hp.mem_l M hX pp).2
    exact ⟨⟨x, xp.2⟩, ⟨y, yp.2⟩, ⟨z, zp.2⟩, ⟨v, vp⟩, ⟨p, pp⟩, hx, hy, hz, hv, hp, hq⟩

theorem tg_node_source_l {d} (ρ : Env N d) (k S s t g : Term d) :
    Formula.satisfies ρ (tg_node_m k S s t g) ↔
      Tg_node_d I (k.eval ρ).val (S.eval ρ).val (s.eval ρ).val (t.eval ρ).val (g.eval ρ).val := by
  simp only [tg_node_m, Tg_node_d, Formula.satisfies_conj_iff, tg_graph_source_l hX nx hE hP,
    Formula.satisfies_existsMem_iff, tg_join_source_l hX nx hE hP,
    Definitional.Term.eval_weaken, Definitional.Term.eval_newest]
  refine and_congr Iff.rfl (and_congr Iff.rfl (and_congr Iff.rfl ⟨?_, ?_⟩))
  · rintro ⟨q, hq, h⟩
    exact ⟨q.val, hq, h⟩
  · rintro ⟨q, hq, h⟩
    exact ⟨⟨q, hX _ (S.eval ρ).property q hq⟩, hq, h⟩

end YesMetaZFC.SetTheory.Internal

/-! ## 类型游戏的内部有限节点程序

原变量之间任意排列；程序仅检验其中间坐标所成的集合是一张完整节点图。
只绑定该低秩图，不把原元组本身当作新增自由参数。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem tg_node_build_l {ω e l b : M.Domain} (hω : M.IsOmega ω)
    (hl : M.mem l ω) (hb : M.mem b ω) (he : M.mem e l) (lb : M.MemberSubset l b)
    (σ : Fin 3 → M.Domain) (hσ : ∀ i, M.mem (σ i) b) :
    ∃ a m G u, Sformula_d I ω a m G u ∧ ∀ c X R f S s t k,
      Smem_d I c X R → M.TransitiveSet X → M.IsSetFunctionFromTo I f ω X →
      Rd_entry_d e S f → Rd_entry_d (σ 0) s f → Rd_entry_d (σ 1) t f → Rd_entry_d (σ 2) k f →
      (Satisfies_d I ω c a f ↔ ∃ g, M.mem g X ∧ Sg_set_d I e l f g ∧ Tg_node_d I k S s t g) := by
  obtain ⟨p, hs, hp⟩ := hω.1.2 b hb
  have bp := hs.predecessor_mem
  have up {i} (hi : M.mem i b) : M.mem i p := (hs i).mpr (Or.inl hi)
  obtain ⟨m₀, G₀, u₀, prog, root, set⟩ := sg_set_build_l I hZF hω hl hb hp bp (fun i hi => up (lb i hi))
  let φ : Formula 1 5 := tg_node_m (.bound 0) (.bound 1) (.bound 2) (.bound 3) (.bound 4)
  have hc : φ.FreeClosed := tg_node_m_freeClosed _ _ _ _ _ rfl rfl rfl rfl rfl
  let v : Fin 5 → M.Domain := Fin.cases (σ 2) (Fin.cases e (Fin.cases (σ 0) (Fin.cases (σ 1) (fun _ => b))))
  have hv : ∀ i, M.mem (v i) p := Fin.cases (up (hσ 2))
    (Fin.cases (up (lb e he)) (Fin.cases (up (hσ 0)) (Fin.cases (up (hσ 1)) (fun _ => bp))))
  obtain ⟨m₁, G₁, u₁, add, compile⟩ := source_compile_core_l I hZF hω (source_core_l φ)
    (source_core_closed_l φ hc) v hp hv prog
  obtain ⟨m₂, G₂, u₂, bothProg, both⟩ := sfm_and_l I hZF hω add.program (add.span u₀ root) add.root
  obtain ⟨m, G, u, finalProg, ex⟩ := sfm_ex_l I hZF hω bothProg.program hb bothProg.root
  obtain ⟨a, ca⟩ := (I).total G u
  have form : Sformula_d I ω a m G u := ⟨ca, finalProg.program, finalProg.root⟩
  refine ⟨a, m, G, u, form, fun c X R f S s t k model trans ff fS fs ft fk => ?_⟩
  obtain ⟨E, hE⟩ := ZF.exists_functionSpace hZF I ω X
  have hf := (hE f).mpr ff
  let nx : Nonempty {x // M.mem x X} := ⟨⟨S, ff.output_mem_of_pairMember fS⟩⟩
  have body g (hg : M.mem g X) f₁ (update : Senv_update_d I f b g f₁) :
      Ssat_d I X R E G₂ m₂ u₂ f₁ ↔ Sg_set_d I e l f g ∧ Tg_node_d I k S s t g := by
    have ff₁ := update.function_l I ff hb hg
    have hf₁ := (hE f₁).mpr ff₁
    have fb := (update.2 b g).mpr (Or.inl ⟨rfl, rfl⟩)
    have same := update.agree_l I (KP.mem_irrefl_d (ZF.modelsKP hZF) b)
    have sets : Sg_set_d I e l f₁ g ↔ Sg_set_d I e l f g :=
      forall_congr' fun x => iff_congr Iff.rfl (exists_congr fun i => and_congr_right fun hi =>
        and_congr_right fun _ => (same i x (lb i hi)).symm)
    have setRead := (add.sat_l I hZF prog root X R E f₁).symm.trans
      ((set c X R E f₁ g model trans hE hf₁ fb).trans sets)
    let ρ : Env (rt_model_l X nx) 5 := ⟨Fin.cases ⟨k, ff.output_mem_of_pairMember fk⟩
      (Fin.cases ⟨S, ff.output_mem_of_pairMember fS⟩ (Fin.cases ⟨s, ff.output_mem_of_pairMember fs⟩
        (Fin.cases ⟨t, ff.output_mem_of_pairMember ft⟩ (fun _ => ⟨g, hg⟩)))), fun _ => ⟨g, hg⟩⟩
    let η : Env (smdl_structure_l I (R := R) model.1.2.1) 5 := ⟨ρ.bound, ρ.free⟩
    have values : ∀ i, Rd_entry_d (v i) (η.bound i).val f₁ :=
      Fin.cases ((same (σ 2) k (hσ 2)).mp fk) (Fin.cases ((same e S (lb e he)).mp fS)
        (Fin.cases ((same (σ 0) s (hσ 0)).mp fs) (Fin.cases ((same (σ 1) t (hσ 1)).mp ft) (fun _ => fb))))
    have nodeRead := (compile X R model.1.2.1 E hE f₁ hf₁ η values).trans ((source_core_sat_l φ η).trans
      ((smem_formula_l I model nx φ ρ).symm.trans
        (tg_node_source_l trans nx (ZF.modelsKP hZF).1 (KP.exists_pair (ZF.modelsKP hZF)) ρ _ _ _ _ _)))
    exact (both X R E f₁ hf₁).trans (and_congr setRead nodeRead)
  refine (satisfies_decode_l I hZF.1 model.1 form hE).trans ((ex X R E f hf).trans ⟨?_, ?_⟩)
  · rintro ⟨g, f₁, hg, update, truth⟩
    exact ⟨g, hg, (body g hg f₁ update).mp truth⟩
  · rintro ⟨g, hg, truth⟩
    obtain ⟨f₁, update, _⟩ := senv_update_exists_l I hZF ff hb hg
    exact ⟨g, f₁, hg, update, (body g hg f₁ update).mpr truth⟩

end YesMetaZFC.SetTheory.Internal

/-! ## 完整类型中的实际节点查询

查询码只依赖内部元数和低秩参数 s、t、k。所有原坐标保留为变量，
读出的是中间值的集合，而非预先指定的标签顺序。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}}

def Tg_node_query_d (I : kpair_convention_l.Interpretation M) (ω e n l U D s t k q : M.Domain) : Prop :=
  M.mem q D ∧ ∀ c X R r δ T S, Smem_d I c X R → M.TransitiveSet X →
    Tt_realized_d I ω c X R n r δ U D T → Rd_entry_d e S r →
      (M.mem q T ↔ ∃ g, M.mem g X ∧ Sg_set_d I e l r g ∧ Tg_node_d I k S s t g)

variable (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem tt_node_query_l {ω e n l U D s t k : M.Domain} (hω : M.IsOmega ω)
    (hn : M.mem n ω) (hl : M.mem l n) (he : M.mem e l) (pool : Tt_pool_d I ω n U D)
    (hs : M.mem s U) (ht : M.mem t U) (hk : M.mem k U) :
    ∃ q, Tg_node_query_d I ω e n l U D s t k q := by
  obtain ⟨N, E, names, sequences, product⟩ := pool
  obtain ⟨b, σ, hb, nb, bound, _, columns⟩ := tt_column_build_l hZF hω hn 3
  let a : Fin 3 → M.Domain := Fin.cases s (Fin.cases t (fun _ => k))
  have ha : ∀ i, M.mem (a i) U := Fin.cases hs (Fin.cases ht (fun _ => hk))
  obtain ⟨v, hv⟩ := Classical.axiomOfChoice (fun i => (I).total (a i) (a i))
  obtain ⟨C, column, original, params⟩ := columns U N names v
    (fun i => (names (v i)).mpr (Or.inr (Or.inr ⟨a i, ha i, hv i⟩)))
  have ord := hω.members_areOrdinals (ZF.modelsKP hZF) n hn
  have ln : M.MemberSubset l n := ord.transitive l hl
  obtain ⟨f, m, G, u, form, node⟩ := tg_node_build_l hZF hω (hω.transitive (ZF.modelsKP hZF) n hn l hl) hb he
    (fun i hi => nb i (ln i hi)) σ bound
  obtain ⟨z, code⟩ := sc_num_exists_l I hZF hω form
  obtain ⟨q, cq⟩ := (I).total z C
  have hz := sc_num_natural_l I hZF hω code
  have hq := (product q).mpr ⟨z, hz, C, (sequences C).mpr ⟨b, hb, column⟩, cq⟩
  refine ⟨q, hq, fun c X R r δ T S model trans type rS => ?_⟩
  obtain ⟨r₁, assign, fr₁⟩ := tn_assign_exists_l hZF ord type.tuple type.point type.constants names
    (fn0_of_function_l (ZF.modelsKP hZF) column)
  obtain ⟨f₁, fill, ff₁⟩ := senv_fill_exists_l I hZF (fn0_function_l (ZF.modelsKP hZF) fr₁) type.point
  have value i j x (hj : Rd_entry_d i j C) (hx : Tn_value_d n r δ j x) : Rd_entry_d i x f₁ :=
    (fill.2 i x).mpr ⟨hω.transitive (ZF.modelsKP hZF) b hb i (column.input_mem_of_pairMember hj),
      Or.inl ⟨column.input_mem_of_pairMember hj, (assign.2 i x).mpr ⟨j, hj, hx⟩⟩⟩
  have vars i x (hx : Rd_entry_d i x r) : Rd_entry_d i x f₁ :=
    value i i x (original i (type.tuple.bound_l hx).1) (Or.inl hx)
  have same i x (hi : M.mem i n) : Rd_entry_d i x r ↔ Rd_entry_d i x f₁ := by
    refine ⟨vars i x, fun hx => ?_⟩
    obtain ⟨y, _, hy⟩ := type.tuple.2.1 i hi
    exact ff₁.1.2 i y x (vars i y hy) hx ▸ hy
  have sets g : Sg_set_d I e l f₁ g ↔ Sg_set_d I e l r g :=
    forall_congr' fun x => iff_congr Iff.rfl (exists_congr fun i => and_congr_right fun hi =>
      and_congr_right fun _ => (same i x (ln i hi)).symm)
  have constants i : Rd_entry_d (σ i) (a i) f₁ := value (σ i) (v i) (a i) (params i) (Or.inr (Or.inr (hv i)))
  exact (type.truth q).trans ((and_iff_right hq).trans
    ((tt_query_decode_l I (ZF.modelsKP hZF) cq hz hb column.2.1 assign fill).trans
      ((sc_sat_decode_l I hZF hω code).trans
        ((node c X R f₁ S s t k model trans ff₁ (vars e S rS) (constants 0) (constants 1) (constants 2)).trans
          (exists_congr fun g => and_congr Iff.rfl (and_congr (sets g) Iff.rfl))))))

end YesMetaZFC.SetTheory.Internal

/-! ## 空根的单个类型查询

唯一附加坐标条件为 ∅∈v₀。它不规定历史标签的位置；空集由外延性识别，
查询本身没有新增集合常量。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}}

def Tg_root_query_d (I : kpair_convention_l.Interpretation M) (ω e n U D q : M.Domain) : Prop :=
  M.mem q D ∧ ∀ c X R r δ T S, Smem_d I c X R → M.TransitiveSet X →
    Tt_realized_d I ω c X R n r δ U D T → Rd_entry_d e S r → (M.mem q T ↔ M.mem e S)

def tg_root_m {d} (S : Term d) : Formula 1 d := set[d] ⟪∃ e ∈ ⌜S⌝ₛ, ∀ x ∈ e, ⊥⟫
derive_free_closed tg_root_m

theorem tg_root_delta_l {d} (S : Term d) : (tg_root_m S).IsDelta0 :=
  .existsMem _ (.forallMem _ .falsum)

theorem tg_root_sat_l (hE : Extensional M) {e : M.Domain} (he : ∀ x, ¬ M.mem x e)
    {d} (ρ : Env M d) (S : Term d) : Formula.satisfies ρ (tg_root_m S) ↔ M.mem e (S.eval ρ) := by
  simp only [tg_root_m, Formula.satisfies_existsMem_iff, Formula.satisfies_forallMem_iff,
    Formula.satisfies_falsum_iff]
  exact ⟨fun ⟨z, hz, empty⟩ => hE.eq_of_same_members z e (fun x => iff_of_false (empty x) (he x)) ▸ hz,
    fun h => ⟨e, h, he⟩⟩

variable (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem tt_root_query_l {ω e n U D : M.Domain} (hω : M.IsOmega ω)
    (he : ∀ x, ¬ M.mem x e) (hen : M.mem e n) (pool : Tt_pool_d I ω n U D) :
    ∃ q, Tg_root_query_d I ω e n U D q := by
  obtain ⟨q, hq, read⟩ := tt_fixed_query_l hZF hω pool (tg_root_m .newest)
    (tg_root_m_freeClosed _ rfl) (fun _ : Fin 1 => e) (fun _ => Or.inl hen)
  refine ⟨q, hq, fun c X R r δ T S model trans type rS => ?_⟩
  let a : (smdl_structure_l I (R := R) type.model.2.1).Domain := ⟨S, (type.tuple.bound_l rS).2⟩
  let ρ : Env (smdl_structure_l I (R := R) type.model.2.1) 1 := ⟨fun _ => a, fun _ => a⟩
  exact (read c X R r δ T type ρ (fun _ => Or.inl rS)).trans
    ((smem_delta_image_l I model trans (tg_root_delta_l .newest) ρ).trans
      (tg_root_sat_l hZF.1 he (image_env_l Subtype.val ρ) .newest))

end YesMetaZFC.SetTheory.Internal

/-! ## 规则 (7) 的末位严格秩界

以 S∈Vα 表达 rank(S)<α，并同时检查 δ<α。实际累积层级在源中
双向读取，不预设源模型满足 ZF，也不把源内秩判断当成背景假设。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}}

def Tg_bound_d (I : kpair_convention_l.Interpretation M) (δ S α : M.Domain) : Prop :=
  M.IsOrdinal α ∧ M.mem δ α ∧ ∃ B, V_d I α B ∧ M.mem S B

def tg_bound_m {d} (δ S α : Term d) : Formula 1 d := set[d] ⟪
  ⌜Formula.isOrdinal⌝ₚ(⌜α⌝ₛ) ∧ ⌜δ⌝ₛ ∈ ⌜α⌝ₛ ∧ (∃ B, ⌜v_m FlatPairing.convention⌝ₚ(⌜α⌝ₛ, B) ∧ ⌜S⌝ₛ ∈ B)⟫
derive_free_closed tg_bound_m

variable (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem tg_bound_rank_l {δ S α : M.Domain} : Tg_bound_d I δ S α ↔
    M.IsOrdinal α ∧ M.mem δ α ∧ ∃ ρ, Rk_d I S ρ ∧ M.mem ρ α := by
  refine and_congr_right fun hα => and_congr_right fun _ => ⟨?_, ?_⟩
  · rintro ⟨B, hB, hS⟩
    obtain ⟨ρ, rank⟩ := ZF.rk_exists_l I hZF S
    exact ⟨ρ, rank, (ZF.rk_mem_l I hZF rank hB).mp hS⟩
  · rintro ⟨ρ, rank, lt⟩
    obtain ⟨B, hB⟩ := ZF.v_exists_l I hZF hα
    exact ⟨B, hB, (ZF.rk_mem_l I hZF rank hB).mpr lt⟩

theorem tg_bound_source_l {ω η X : M.Domain} (hω : M.IsOmega ω) (hX : V_d I η X) (hw : M.mem ω X)
    {d} (ρ : Env (rt_model_l X ⟨⟨ω, hw⟩⟩) d) (δ S α : Term d) :
    Formula.satisfies ρ (tg_bound_m δ S α) ↔ Tg_bound_d I (δ.eval ρ).val (S.eval ρ).val (α.eval ρ).val := by
  let J := fp_rank_interpretation_l I hZF hω hX hw
  have trans := v_transitive_l I hX
  simp only [tg_bound_m, Tg_bound_d, Formula.satisfies_conj_iff, Formula.satisfies_isOrdinal_iff,
    rt_ordinal_iff_l trans ⟨⟨ω, hw⟩⟩ (ZF.modelsKP hZF), Formula.satisfies_mem_iff,
    Formula.satisfies_exists_iff, v_sat_l J (rt_model_ext_l hZF.1 trans ⟨⟨ω, hw⟩⟩),
    Definitional.Term.eval_weaken, Definitional.Term.eval_newest]
  refine and_congr Iff.rfl (and_congr Iff.rfl ⟨?_, ?_⟩)
  · rintro ⟨B, hv, hS⟩
    exact ⟨B.val, (rt_fp_v_l I hZF hω hX hw (α.eval ρ) B).mp hv, hS⟩
  · rintro ⟨B, hv, hS⟩
    have hb := ZF.v_mem_l I hZF hv hX (ZF.v_ordinal_height_l hZF hX (v_ordinal_l I hv) (α.eval ρ).property)
    exact ⟨⟨B, hb⟩, (rt_fp_v_l I hZF hω hX hw (α.eval ρ) ⟨B, hb⟩).mpr hv, hS⟩

def Tg_bound_query_d (J : kpair_convention_l.Interpretation M) (ω e l n U D q : M.Domain) : Prop :=
  M.mem q D ∧ ∀ η X c R r δ T S α, V_d J η X → Smem_d J c X R →
    Tt_realized_d J ω c X R n r δ U D T → Rd_entry_d e S r → Rd_entry_d l α r →
      (M.mem q T ↔ Tg_bound_d J δ S α)

theorem tt_bound_query_l {ω e l n U D : M.Domain} (hω : M.IsOmega ω)
    (he : M.mem e n) (hl : M.mem l n) (hw : M.mem ω U) (pool : Tt_pool_d I ω n U D) :
    ∃ q, Tg_bound_query_d I ω e l n U D q := by
  let φ : Formula 1 3 := tg_bound_m (.bound 2) (.bound 1) .newest
  obtain ⟨q, hq, read⟩ := tt_fixed_query_l hZF hω pool φ (tg_bound_m_freeClosed _ _ _ rfl rfl rfl)
    (Fin.cases l (Fin.cases e (fun _ => n)))
    (Fin.cases (Or.inl hl) (Fin.cases (Or.inl he) (fun _ => Or.inr (Or.inl rfl))))
  refine ⟨q, hq, fun η X c R r δ T S α hX model type rS rα => ?_⟩
  have hwX := type.constants ω hw
  let ρ : Env (rt_model_l X ⟨⟨ω, hwX⟩⟩) 3 :=
    ⟨Fin.cases ⟨α, (type.tuple.bound_l rα).2⟩ (Fin.cases ⟨S, (type.tuple.bound_l rS).2⟩ (fun _ => ⟨δ, type.point⟩)),
      fun _ => ⟨δ, type.point⟩⟩
  let ξ : Env (smdl_structure_l I (R := R) type.model.2.1) 3 := ⟨ρ.bound, ρ.free⟩
  exact (read c X R r δ T type ξ (Fin.cases (Or.inl rα) (Fin.cases (Or.inl rS)
    (fun _ => Or.inr (Or.inl ⟨rfl, rfl⟩))))).trans
    ((smem_formula_l I model ⟨⟨ω, hwX⟩⟩ φ ρ).symm.trans (tg_bound_source_l hZF hω hX hwX ρ _ _ _))

end YesMetaZFC.SetTheory.Internal

/-! ## 末位最大序数查询准确固定实现高度

不预设见证秩层是后继层。原公式的真值本身推出层高为末位序数加一。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}}

def Tg_max_query_d (I : kpair_convention_l.Interpretation M) (ω l n U D q : M.Domain) : Prop :=
  M.mem q D ∧ ∀ ν X c R r δ T α, V_d I ν X → Smem_d I c X R →
    Tt_realized_d I ω c X R n r δ U D T → Rd_entry_d l α r → (M.mem q T ↔ M.SuccessorOf ν α)

variable (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem tt_max_query_l {ω l n U D : M.Domain} (hω : M.IsOmega ω)
    (hl : M.mem l n) (pool : Tt_pool_d I ω n U D) : ∃ q, Tg_max_query_d I ω l n U D q := by
  obtain ⟨q, hq, read⟩ := tt_fixed_query_l hZF hω pool (sv_max_m .newest)
    (sv_max_m_freeClosed _ rfl) (fun _ : Fin 1 => l) (fun _ => Or.inl hl)
  refine ⟨q, hq, fun ν X c R r δ T α hX model type rα => ?_⟩
  let nx : Nonempty {x // M.mem x X} := ⟨⟨α, (type.tuple.bound_l rα).2⟩⟩
  let a : (rt_model_l X nx).Domain := ⟨α, (type.tuple.bound_l rα).2⟩
  let ρ : Env (rt_model_l X nx) 1 := ⟨fun _ => a, fun _ => a⟩
  let η : Env (smdl_structure_l I (R := R) type.model.2.1) 1 := ⟨ρ.bound, ρ.free⟩
  have ht := v_transitive_l I hX
  have first := (read c X R r δ T type η (fun _ => Or.inl rα)).trans
    ((smem_formula_l I model nx (sv_max_m .newest) ρ).symm.trans (sv_max_sat_l ρ .newest))
  refine first.trans ⟨sv_max_successor_l hZF hX nx a, ?_⟩
  intro hs
  have hα := (v_ordinal_l I hX).mem hs.predecessor_mem
  refine ⟨rt_ordinal_l ht nx a hα, fun b hb x hx => ?_⟩
  have ob := (rt_ordinal_iff_l ht nx (ZF.modelsKP hZF) b).mp hb
  rcases (hs b.val).mp (ZF.v_ordinal_height_l hZF hX ob b.property) with lt | eq
  · exact hα.transitive b.val lt x.val hx
  · exact (eq x.val).mp hx

end YesMetaZFC.SetTheory.Internal

/-! ## 规则 (7) 的末位加二最大序数

原公式在源中构造两个后继，再检查最大序数。查询精确等价于
实现高度等于末位加三；所有后继对象均实际回收。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}}

def Tg_height_d (α η : M.Domain) : Prop :=
  ∃ β γ, M.SuccessorOf β α ∧ M.SuccessorOf γ β ∧ M.SuccessorOf η γ

/-- α<ν 且 ν+1<α+3 时，ν 必为 α+1。 -/
theorem Tg_height_d.gap_l (hE : Extensional M) (hirr : ∀ x, ¬ M.mem x x) {α η ν ρ : M.Domain}
    (h : Tg_height_d α η) (oη : M.IsOrdinal η) (hαν : M.mem α ν)
    (succ : M.SuccessorOf ρ ν) (gap : M.mem ρ η) : M.SuccessorOf ν α := by
  obtain ⟨β, γ, hb, hg, last⟩ := h
  have oγ := oη.mem last.predecessor_mem
  have oν := oη.mem (oη.transitive ρ gap ν succ.predecessor_mem)
  have hnγ : M.mem ν γ := by
    rcases (last ρ).mp gap with lt | eq
    · exact oγ.transitive ρ lt ν succ.predecessor_mem
    · exact (eq ν).mp succ.predecessor_mem
  rcases (hg ν).mp hnγ with lt | eq
  · rcases (hb ν).mp lt with lt | eq
    · exact (hirr ν (oν.transitive α hαν ν lt)).elim
    · exact (hirr ν ((hE.eq_of_same_members ν α eq).symm ▸ hαν)).elim
  · exact (hE.eq_of_same_members ν β eq).symm ▸ hb

def tg_height_m {d} (α : Term d) : Formula 1 d := set[d] ⟪
  ⌜Formula.isOrdinal⌝ₚ(⌜α⌝ₛ) ∧ (∃ β γ, ⌜Formula.isSuccessor⌝ₚ(β, ⌜α⌝ₛ) ∧
    ⌜Formula.isSuccessor⌝ₚ(γ, β) ∧ ⌜sv_max_m⌝ₚ(γ))⟫
derive_free_closed tg_height_m

def Tg_height_query_d (I : kpair_convention_l.Interpretation M) (ω l n U D q : M.Domain) : Prop :=
  M.mem q D ∧ ∀ η X c R r δ T α, V_d I η X → Smem_d I c X R →
    Tt_realized_d I ω c X R n r δ U D T → Rd_entry_d l α r → (M.mem q T ↔ Tg_height_d α η)

variable (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem tg_height_source_l {η X : M.Domain} (hX : V_d I η X) (nx : Nonempty {x // M.mem x X})
    {d} (ρ : Env (rt_model_l X nx) d) (α : Term d) :
    Formula.satisfies ρ (tg_height_m α) ↔ Tg_height_d (α.eval ρ).val η := by
  have trans := v_transitive_l I hX
  simp only [tg_height_m, Formula.satisfies_conj_iff, Formula.satisfies_isOrdinal_iff,
    rt_ordinal_iff_l trans nx (ZF.modelsKP hZF), Formula.satisfies_exists_iff,
    Formula.satisfies_isSuccessor_iff, rt_successor_l trans nx hZF.1, sv_max_sat_l,
    Definitional.Term.eval_weaken, Definitional.Term.eval_newest]
  constructor
  · rintro ⟨_, β, γ, hb, hg, last⟩
    exact ⟨β.val, γ.val, hb, hg, sv_max_successor_l hZF hX nx γ last⟩
  · rintro ⟨β, γ, hb, hg, last⟩
    have og := (v_ordinal_l I hX).mem last.predecessor_mem
    have ob := og.mem hg.predecessor_mem
    have oa := ob.mem hb.predecessor_mem
    have hγX := ZF.v_ordinal_mem_l I hZF hX last.predecessor_mem
    have hβX := trans γ hγX β hg.predecessor_mem
    let b : (rt_model_l X nx).Domain := ⟨β, hβX⟩
    let g : (rt_model_l X nx).Domain := ⟨γ, hγX⟩
    refine ⟨oa, b, g, hb, hg, rt_ordinal_l trans nx g og, fun a ha x hx => ?_⟩
    have oa' := (rt_ordinal_iff_l trans nx (ZF.modelsKP hZF) a).mp ha
    rcases (last a.val).mp (ZF.v_ordinal_height_l hZF hX oa' a.property) with lt | eq
    · exact og.transitive a.val lt x.val hx
    · exact (eq x.val).mp hx

theorem tt_height_query_l {ω l n U D : M.Domain} (hω : M.IsOmega ω)
    (hl : M.mem l n) (pool : Tt_pool_d I ω n U D) : ∃ q, Tg_height_query_d I ω l n U D q := by
  obtain ⟨q, hq, read⟩ := tt_fixed_query_l hZF hω pool (tg_height_m .newest)
    (tg_height_m_freeClosed _ rfl) (fun _ : Fin 1 => l) (fun _ => Or.inl hl)
  refine ⟨q, hq, fun η X c R r δ T α hX model type rα => ?_⟩
  let nx : Nonempty {x // M.mem x X} := ⟨⟨α, (type.tuple.bound_l rα).2⟩⟩
  let ρ : Env (rt_model_l X nx) 1 :=
    ⟨fun _ => ⟨α, (type.tuple.bound_l rα).2⟩, fun _ => ⟨α, (type.tuple.bound_l rα).2⟩⟩
  let ξ : Env (smdl_structure_l I (R := R) type.model.2.1) 1 := ⟨ρ.bound, ρ.free⟩
  exact (read c X R r δ T type ξ (fun _ => Or.inl rα)).trans
    ((smem_formula_l I model nx (tg_height_m .newest) ρ).symm.trans (tg_height_source_l hZF hX nx ρ .newest))

end YesMetaZFC.SetTheory.Internal

/-! ## 节点与端点查询证书的一阶表示

每条证书量化全部实际完整类型；节点保留三张函数图及两个包含方向。
这些公式用于开局前固定查询表，不给裸类型加入额外封闭规则。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} (I : kpair_convention_l.Interpretation M)

def tg_node_query_m {d} (ω e n l U D s t k q : Term d) : Formula 1 d := set[d] ⟪⌜q⌝ₛ ∈ ⌜D⌝ₛ ∧
  (∀ c X R r δ T S, ⌜smem_m (𝒞 := kpair_convention_l)⌝ₚ(c, X, R) → ⌜Formula.isTransitive⌝ₚ(X) →
    ⌜tt_realized_m⌝ₚ(⌜ω⌝ₛ, c, X, R, ⌜n⌝ₛ, r, δ, ⌜U⌝ₛ, ⌜D⌝ₛ, T) → ⌜rd_entry0_m⌝ₚ(⌜e⌝ₛ, S, r) →
    (⌜q⌝ₛ ∈ T ↔ ∃ g ∈ X, ⌜sg_set_m (𝒞 := kpair_convention_l)⌝ₚ(⌜e⌝ₛ, ⌜l⌝ₛ, r, g) ∧
      ⌜tg_node_m⌝ₚ(⌜k⌝ₛ, S, ⌜s⌝ₛ, ⌜t⌝ₛ, g)))⟫
derive_free_closed tg_node_query_m

theorem tg_node_query_sat_l (hKP : M.Models KP) {d} (ρ : Env M d) (ω e n l U D s t k q : Term d) :
    Formula.satisfies ρ (tg_node_query_m ω e n l U D s t k q) ↔ Tg_node_query_d I
      (ω.eval ρ) (e.eval ρ) (n.eval ρ) (l.eval ρ) (U.eval ρ) (D.eval ρ) (s.eval ρ) (t.eval ρ) (k.eval ρ) (q.eval ρ) := by
  simp only [tg_node_query_m, Tg_node_query_d, Formula.satisfies_conj_iff, Formula.satisfies_mem_iff,
    Formula.satisfies_forall_iff, Formula.satisfies_imp_iff, Formula.satisfies_iff_iff,
    Formula.satisfies_existsMem_iff, smem_sat_l I, Formula.satisfies_isTransitive_iff,
    tt_realized_sat_l I hKP, rd_entry0_sat_l hKP.1, sg_set_sat_l I hKP.1, tg_node_sat_l I hKP.1,
    Definitional.Term.eval_weaken]
  rfl

def tg_root_query_m {d} (ω e n U D q : Term d) : Formula 1 d := set[d] ⟪⌜q⌝ₛ ∈ ⌜D⌝ₛ ∧
  (∀ c X R r δ T S, ⌜smem_m (𝒞 := kpair_convention_l)⌝ₚ(c, X, R) → ⌜Formula.isTransitive⌝ₚ(X) →
    ⌜tt_realized_m⌝ₚ(⌜ω⌝ₛ, c, X, R, ⌜n⌝ₛ, r, δ, ⌜U⌝ₛ, ⌜D⌝ₛ, T) → ⌜rd_entry0_m⌝ₚ(⌜e⌝ₛ, S, r) →
    (⌜q⌝ₛ ∈ T ↔ ⌜e⌝ₛ ∈ S))⟫
derive_free_closed tg_root_query_m

theorem tg_root_query_sat_l (hKP : M.Models KP) {d} (ρ : Env M d) (ω e n U D q : Term d) :
    Formula.satisfies ρ (tg_root_query_m ω e n U D q) ↔
      Tg_root_query_d I (ω.eval ρ) (e.eval ρ) (n.eval ρ) (U.eval ρ) (D.eval ρ) (q.eval ρ) := by
  simp only [tg_root_query_m, Tg_root_query_d, Formula.satisfies_conj_iff, Formula.satisfies_mem_iff,
    Formula.satisfies_forall_iff, Formula.satisfies_imp_iff, Formula.satisfies_iff_iff,
    smem_sat_l I, Formula.satisfies_isTransitive_iff, tt_realized_sat_l I hKP, rd_entry0_sat_l hKP.1,
    Definitional.Term.eval_weaken]
  rfl

def tg_max_query0_m : Formula 1 6 :=
  let ω := Term.bound 0; let l := Term.bound 1; let n := Term.bound 2
  let U := Term.bound 3; let D := Term.bound 4; let q := Term.bound 5
  set[6] ⟪⌜q⌝ₛ ∈ ⌜D⌝ₛ ∧
  (∀ ν X c R r δ T α, ⌜v_m kpair_convention_l⌝ₚ(ν, X) → ⌜smem_m (𝒞 := kpair_convention_l)⌝ₚ(c, X, R) →
    ⌜tt_realized_m⌝ₚ(⌜ω⌝ₛ, c, X, R, ⌜n⌝ₛ, r, δ, ⌜U⌝ₛ, ⌜D⌝ₛ, T) → ⌜rd_entry0_m⌝ₚ(⌜l⌝ₛ, α, r) →
    (⌜q⌝ₛ ∈ T ↔ ⌜Formula.isSuccessor⌝ₚ(ν, α)))⟫
theorem tg_max_query0_closed_l : tg_max_query0_m.FreeClosed := by
  simp -implicitDefEqProofs [tg_max_query0_m,Definitional.Formula.FreeClosed]

def tg_max_query_m {d} (ω l n U D q : Term d) : Formula 1 d :=
  tg_max_query0_m.bind (fun i => [ω,l,n,U,D,q].get i)

@[simp] theorem tg_max_query_m_freeClosed {d} (ω l n U D q : Term d)
    (hω : ω.freeSupport = []) (hl : l.freeSupport = []) (hn : n.freeSupport = [])
    (hU : U.freeSupport = []) (hD : D.freeSupport = []) (hq : q.freeSupport = []) :
    (tg_max_query_m ω l n U D q).FreeClosed := by
  apply (Definitional.Formula.freeClosed_bind_iff_of_closed _ ?_ _).mpr tg_max_query0_closed_l
  exact Fin.cases hω (Fin.cases hl (Fin.cases hn (Fin.cases hU (Fin.cases hD
    (Fin.cases hq (fun i => Fin.elim0 i))))))

theorem tg_max_query_sat_l (hKP : M.Models KP) {d} (ρ : Env M d) (ω l n U D q : Term d) :
    Formula.satisfies ρ (tg_max_query_m ω l n U D q) ↔
      Tg_max_query_d I (ω.eval ρ) (l.eval ρ) (n.eval ρ) (U.eval ρ) (D.eval ρ) (q.eval ρ) := by
  simp only [tg_max_query_m,Formula.satisfies_bind,tg_max_query0_m, Tg_max_query_d, Formula.satisfies_conj_iff, Formula.satisfies_mem_iff,
    Formula.satisfies_forall_iff, Formula.satisfies_imp_iff, Formula.satisfies_iff_iff, v_sat_l I hKP.1,
    smem_sat_l I, tt_realized_sat_l I hKP, rd_entry0_sat_l hKP.1, Formula.satisfies_isSuccessor_iff,
    Definitional.Term.eval_weaken]
  rfl

def tg_bound_raw_m {d} (δ S α : Term d) : Formula 1 d := set[d] ⟪
  ⌜Formula.isOrdinal⌝ₚ(⌜α⌝ₛ) ∧ ⌜δ⌝ₛ ∈ ⌜α⌝ₛ ∧ (∃ B, ⌜v_m kpair_convention_l⌝ₚ(⌜α⌝ₛ, B) ∧ ⌜S⌝ₛ ∈ B)⟫
derive_free_closed tg_bound_raw_m

def tg_height_raw_m {d} (α η : Term d) : Formula 1 d := set[d] ⟪∃ β γ,
  ⌜Formula.isSuccessor⌝ₚ(β, ⌜α⌝ₛ) ∧ ⌜Formula.isSuccessor⌝ₚ(γ, β) ∧ ⌜Formula.isSuccessor⌝ₚ(⌜η⌝ₛ, γ)⟫
derive_free_closed tg_height_raw_m

theorem tg_bound_raw_sat_l (hE : Extensional M) {d} (ρ : Env M d) (δ S α : Term d) :
    Formula.satisfies ρ (tg_bound_raw_m δ S α) ↔ Tg_bound_d I (δ.eval ρ) (S.eval ρ) (α.eval ρ) := by
  simp only [tg_bound_raw_m, Tg_bound_d, Formula.satisfies_conj_iff, Formula.satisfies_isOrdinal_iff,
    Formula.satisfies_mem_iff, Formula.satisfies_exists_iff, v_sat_l I hE, Definitional.Term.eval_weaken]
  rfl

theorem tg_height_raw_sat_l {d} (ρ : Env M d) (α η : Term d) :
    Formula.satisfies ρ (tg_height_raw_m α η) ↔ Tg_height_d (α.eval ρ) (η.eval ρ) := by
  simp only [tg_height_raw_m, Tg_height_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    Formula.satisfies_isSuccessor_iff, Definitional.Term.eval_weaken]
  rfl

def tg_bound_query0_m : Formula 1 7 :=
  let ω := Term.bound 0; let e := Term.bound 1; let l := Term.bound 2; let n := Term.bound 3
  let U := Term.bound 4; let D := Term.bound 5; let q := Term.bound 6
  set[7] ⟪⌜q⌝ₛ ∈ ⌜D⌝ₛ ∧
  (∀ η X c R r δ T S α, ⌜v_m kpair_convention_l⌝ₚ(η, X) → ⌜smem_m (𝒞 := kpair_convention_l)⌝ₚ(c, X, R) →
    ⌜tt_realized_m⌝ₚ(⌜ω⌝ₛ, c, X, R, ⌜n⌝ₛ, r, δ, ⌜U⌝ₛ, ⌜D⌝ₛ, T) →
    ⌜rd_entry0_m⌝ₚ(⌜e⌝ₛ, S, r) → ⌜rd_entry0_m⌝ₚ(⌜l⌝ₛ, α, r) →
    (⌜q⌝ₛ ∈ T ↔ ⌜tg_bound_raw_m⌝ₚ(δ, S, α)))⟫
theorem tg_bound_query0_closed_l : tg_bound_query0_m.FreeClosed := by
  simp -implicitDefEqProofs [tg_bound_query0_m,Definitional.Formula.FreeClosed]

def tg_bound_query_m {d} (ω e l n U D q : Term d) : Formula 1 d :=
  tg_bound_query0_m.bind (fun i => [ω,e,l,n,U,D,q].get i)

@[simp] theorem tg_bound_query_m_freeClosed {d} (ω e l n U D q : Term d)
    (hω : ω.freeSupport = []) (he : e.freeSupport = []) (hl : l.freeSupport = [])
    (hn : n.freeSupport = []) (hU : U.freeSupport = []) (hD : D.freeSupport = [])
    (hq : q.freeSupport = []) :
    (tg_bound_query_m ω e l n U D q).FreeClosed := by
  apply (Definitional.Formula.freeClosed_bind_iff_of_closed _ ?_ _).mpr tg_bound_query0_closed_l
  exact Fin.cases hω (Fin.cases he (Fin.cases hl (Fin.cases hn (Fin.cases hU
    (Fin.cases hD (Fin.cases hq (fun i => Fin.elim0 i)))))))

theorem tg_bound_query_sat_l (hKP : M.Models KP) {d} (ρ : Env M d) (ω e l n U D q : Term d) :
    Formula.satisfies ρ (tg_bound_query_m ω e l n U D q) ↔ Tg_bound_query_d I
      (ω.eval ρ) (e.eval ρ) (l.eval ρ) (n.eval ρ) (U.eval ρ) (D.eval ρ) (q.eval ρ) := by
  simp only [tg_bound_query_m,Formula.satisfies_bind,tg_bound_query0_m, Tg_bound_query_d, Formula.satisfies_conj_iff, Formula.satisfies_mem_iff,
    Formula.satisfies_forall_iff, Formula.satisfies_imp_iff, Formula.satisfies_iff_iff, v_sat_l I hKP.1,
    smem_sat_l I, tt_realized_sat_l I hKP, rd_entry0_sat_l hKP.1, tg_bound_raw_sat_l I hKP.1,
    Definitional.Term.eval_weaken]
  rfl

def tg_height_query0_m : Formula 1 6 :=
  let ω := Term.bound 0; let l := Term.bound 1; let n := Term.bound 2
  let U := Term.bound 3; let D := Term.bound 4; let q := Term.bound 5
  set[6] ⟪⌜q⌝ₛ ∈ ⌜D⌝ₛ ∧
  (∀ η X c R r δ T α, ⌜v_m kpair_convention_l⌝ₚ(η, X) → ⌜smem_m (𝒞 := kpair_convention_l)⌝ₚ(c, X, R) →
    ⌜tt_realized_m⌝ₚ(⌜ω⌝ₛ, c, X, R, ⌜n⌝ₛ, r, δ, ⌜U⌝ₛ, ⌜D⌝ₛ, T) → ⌜rd_entry0_m⌝ₚ(⌜l⌝ₛ, α, r) →
    (⌜q⌝ₛ ∈ T ↔ ⌜tg_height_raw_m⌝ₚ(α, η)))⟫
theorem tg_height_query0_closed_l : tg_height_query0_m.FreeClosed := by
  simp -implicitDefEqProofs [tg_height_query0_m,Definitional.Formula.FreeClosed]

def tg_height_query_m {d} (ω l n U D q : Term d) : Formula 1 d :=
  tg_height_query0_m.bind (fun i => [ω,l,n,U,D,q].get i)

@[simp] theorem tg_height_query_m_freeClosed {d} (ω l n U D q : Term d)
    (hω : ω.freeSupport = []) (hl : l.freeSupport = []) (hn : n.freeSupport = [])
    (hU : U.freeSupport = []) (hD : D.freeSupport = []) (hq : q.freeSupport = []) :
    (tg_height_query_m ω l n U D q).FreeClosed := by
  apply (Definitional.Formula.freeClosed_bind_iff_of_closed _ ?_ _).mpr tg_height_query0_closed_l
  exact Fin.cases hω (Fin.cases hl (Fin.cases hn (Fin.cases hU (Fin.cases hD
    (Fin.cases hq (fun i => Fin.elim0 i))))))

theorem tg_height_query_sat_l (hKP : M.Models KP) {d} (ρ : Env M d) (ω l n U D q : Term d) :
    Formula.satisfies ρ (tg_height_query_m ω l n U D q) ↔ Tg_height_query_d I
      (ω.eval ρ) (l.eval ρ) (n.eval ρ) (U.eval ρ) (D.eval ρ) (q.eval ρ) := by
  simp only [tg_height_query_m,Formula.satisfies_bind,tg_height_query0_m, Tg_height_query_d, Formula.satisfies_conj_iff, Formula.satisfies_mem_iff,
    Formula.satisfies_forall_iff, Formula.satisfies_imp_iff, Formula.satisfies_iff_iff, v_sat_l I hKP.1,
    smem_sat_l I, tt_realized_sat_l I hKP, rd_entry0_sat_l hKP.1, tg_height_raw_sat_l,
    Definitional.Term.eval_weaken]
  rfl

end YesMetaZFC.SetTheory.Internal

/-! ## 固定低参数域中的查询向更大常量域延伸

完整类型在较小常量域上取交即可；查询、元组和指定点不变。
因此节点和四个端点查询可以先在低参数域中固定，再用于任意更大的类型域。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} (I : kpair_convention_l.Interpretation M) (hKP : M.Models KP)
include hKP

theorem Tt_realized_d.constants_restrict_l {ω c X R n r δ U D T V W : M.Domain}
    (type : Tt_realized_d I ω c X R n r δ U D T) (pool : Tt_pool_d I ω n V W)
    (sub : M.MemberSubset V U) :
    ∃ t, Tt_realized_d I ω c X R n r δ V W t ∧ ∀ q, M.mem q W → (M.mem q t ↔ M.mem q T) := by
  obtain ⟨t, cut⟩ := KP.intersection_exists_d hKP W T
  have smaller := pool.mono_l I type.pool sub
  refine ⟨t, ⟨type.model, type.finite, type.tuple, type.point,
    fun x hx => type.constants x (sub x hx), pool, ?_⟩, fun q hq => (cut q).trans (and_iff_right hq)⟩
  intro q
  exact (cut q).trans (and_congr_right fun hq => (type.truth q).trans (and_iff_right (smaller q hq)))

variable {ω e l n U D V W q s t k : M.Domain}
  (small : Tt_pool_d I ω n U D) (large : Tt_pool_d I ω n V W) (sub : M.MemberSubset U V)
include small large sub

theorem Tg_root_query_d.scope_l (h : Tg_root_query_d I ω e n U D q) : Tg_root_query_d I ω e n V W q := by
  refine ⟨small.mono_l I large sub q h.1, fun c X R r δ T S model trans type rS => ?_⟩
  obtain ⟨a, localType, same⟩ := type.constants_restrict_l I hKP small sub
  exact (same q h.1).symm.trans (h.2 c X R r δ a S model trans localType rS)

theorem Tg_max_query_d.scope_l (h : Tg_max_query_d I ω l n U D q) : Tg_max_query_d I ω l n V W q := by
  refine ⟨small.mono_l I large sub q h.1, fun ν X c R r δ T α rank model type rα => ?_⟩
  obtain ⟨a, localType, same⟩ := type.constants_restrict_l I hKP small sub
  exact (same q h.1).symm.trans (h.2 ν X c R r δ a α rank model localType rα)

theorem Tg_height_query_d.scope_l (h : Tg_height_query_d I ω l n U D q) : Tg_height_query_d I ω l n V W q := by
  refine ⟨small.mono_l I large sub q h.1, fun ν X c R r δ T α rank model type rα => ?_⟩
  obtain ⟨a, localType, same⟩ := type.constants_restrict_l I hKP small sub
  exact (same q h.1).symm.trans (h.2 ν X c R r δ a α rank model localType rα)

theorem Tg_bound_query_d.scope_l (h : Tg_bound_query_d I ω e l n U D q) : Tg_bound_query_d I ω e l n V W q := by
  refine ⟨small.mono_l I large sub q h.1, fun ν X c R r δ T S α rank model type rS rα => ?_⟩
  obtain ⟨a, localType, same⟩ := type.constants_restrict_l I hKP small sub
  exact (same q h.1).symm.trans (h.2 ν X c R r δ a S α rank model localType rS rα)

theorem Tg_node_query_d.scope_l (h : Tg_node_query_d I ω e n l U D s t k q) :
    Tg_node_query_d I ω e n l V W s t k q := by
  refine ⟨small.mono_l I large sub q h.1, fun c X R r δ T S model trans type rS => ?_⟩
  obtain ⟨a, localType, same⟩ := type.constants_restrict_l I hKP small sub
  exact (same q h.1).symm.trans (h.2 c X R r δ a S model trans localType rS)

end YesMetaZFC.SetTheory.Internal

/-! ## 恢复图及原节点沿实际初等图搬运

函数性和精确定义域使用传递源中的绝对性；完整节点公式同时搬运三张
坐标图。原记录按配对逐项回拉，保持同一条目而不重新选取回答。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)
variable {ω c d X R Y S j : M.Domain} (hw : M.IsOmega ω)
  (xt : M.TransitiveSet X) (yt : M.TransitiveSet Y)
  (mx : Smem_d (kp_pair_l (ZF.modelsKP hZF)) c X R)
  (my : Smem_d (kp_pair_l (ZF.modelsKP hZF)) d Y S)
  (h : Smap_d (kp_pair_l (ZF.modelsKP hZF)) ω c d X Y j)
include hZF hw xt yt mx my h

theorem Smap_d.tg_graph_l {n n' g g' : M.Domain}
    (hn : Rd_entry_d n n' j) (hg : Rd_entry_d g g' j) :
    Tg_graph_d I n g ↔ Tg_graph_d I n' g' := by
  let nx : Nonempty {x // M.mem x X} := ⟨⟨n, h.1.1.input_mem_of_pairMember hn⟩⟩
  let ny : Nonempty {x // M.mem x Y} := ⟨⟨n', h.1.1.output_mem_of_pairMember hn⟩⟩
  let v : Fin 2 → M.Domain := Fin.cases n (fun _ => g)
  let w : Fin 2 → M.Domain := Fin.cases n' (fun _ => g')
  have images : ∀ i, Rd_entry_d (v i) (w i) j := Fin.cases hn (Fin.cases hg (fun i => Fin.elim0 i))
  let ρ : Env (rt_model_l X nx) 2 := ⟨fun i => ⟨v i, h.1.1.input_mem_of_pairMember (images i)⟩, fun _ => ⟨n, h.1.1.input_mem_of_pairMember hn⟩⟩
  let η : Env (rt_model_l Y ny) 2 := ⟨fun i => ⟨w i, h.1.1.output_mem_of_pairMember (images i)⟩, fun _ => ⟨n', h.1.1.output_mem_of_pairMember hn⟩⟩
  obtain ⟨e, empty⟩ := KP.exists_empty (ZF.modelsKP hZF)
  have tr := spred_source_l I hZF hw ⟨c, R, d, S, mx.empty_pred_l I empty, my.empty_pred_l I empty, h⟩ nx ny
    (tg_graph_m (.bound 0) (.bound 1)) (by simp -implicitDefEqProofs) ρ η images
  exact (tg_graph_source_l xt nx hZF.1 (KP.exists_pair (ZF.modelsKP hZF)) ρ (.bound 0) (.bound 1)).symm.trans
    (tr.trans (tg_graph_source_l yt ny hZF.1 (KP.exists_pair (ZF.modelsKP hZF)) η (.bound 0) (.bound 1)))

theorem Smap_d.tg_join_l {v w : Fin 5 → M.Domain}
    (images : ∀ i, Rd_entry_d (v i) (w i) j) :
    Tg_join_d I (v 0) (v 1) (v 2) (v 3) (v 4) ↔
      Tg_join_d I (w 0) (w 1) (w 2) (w 3) (w 4) := by
  let nx : Nonempty {x // M.mem x X} :=
    ⟨⟨v 0, h.1.1.input_mem_of_pairMember (images 0)⟩⟩
  let ny : Nonempty {x // M.mem x Y} :=
    ⟨⟨w 0, h.1.1.output_mem_of_pairMember (images 0)⟩⟩
  let ρ : Env (rt_model_l X nx) 5 :=
    ⟨fun i => ⟨v i, h.1.1.input_mem_of_pairMember (images i)⟩,
      fun _ => ⟨v 0, h.1.1.input_mem_of_pairMember (images 0)⟩⟩
  let η : Env (rt_model_l Y ny) 5 :=
    ⟨fun i => ⟨w i, h.1.1.output_mem_of_pairMember (images i)⟩,
      fun _ => ⟨w 0, h.1.1.output_mem_of_pairMember (images 0)⟩⟩
  obtain ⟨e, empty⟩ := KP.exists_empty (ZF.modelsKP hZF)
  have tr := spred_source_l I hZF hw
    ⟨c, R, d, S, mx.empty_pred_l I empty, my.empty_pred_l I empty, h⟩ nx ny
    (tg_join_m (.bound 0) (.bound 1) (.bound 2) (.bound 3) (.bound 4))
    (by simp -implicitDefEqProofs) ρ η images
  exact (tg_join_source_l xt nx hZF.1 (KP.exists_pair (ZF.modelsKP hZF))
    ρ (.bound 0) (.bound 1) (.bound 2) (.bound 3) (.bound 4)).symm.trans
    (tr.trans (tg_join_source_l yt ny hZF.1 (KP.exists_pair (ZF.modelsKP hZF))
      η (.bound 0) (.bound 1) (.bound 2) (.bound 3) (.bound 4)))

theorem Smap_d.tg_node_l {v w : Fin 5 → M.Domain} (images : ∀ i, Rd_entry_d (v i) (w i) j) :
    Tg_node_d I (v 0) (v 1) (v 2) (v 3) (v 4) ↔ Tg_node_d I (w 0) (w 1) (w 2) (w 3) (w 4) := by
  let nx : Nonempty {x // M.mem x X} := ⟨⟨v 0, h.1.1.input_mem_of_pairMember (images 0)⟩⟩
  let ny : Nonempty {x // M.mem x Y} := ⟨⟨w 0, h.1.1.output_mem_of_pairMember (images 0)⟩⟩
  let ρ : Env (rt_model_l X nx) 5 := ⟨fun i => ⟨v i, h.1.1.input_mem_of_pairMember (images i)⟩, fun _ => ⟨v 0, h.1.1.input_mem_of_pairMember (images 0)⟩⟩
  let η : Env (rt_model_l Y ny) 5 := ⟨fun i => ⟨w i, h.1.1.output_mem_of_pairMember (images i)⟩, fun _ => ⟨w 0, h.1.1.output_mem_of_pairMember (images 0)⟩⟩
  obtain ⟨e, empty⟩ := KP.exists_empty (ZF.modelsKP hZF)
  have tr := spred_source_l I hZF hw ⟨c, R, d, S, mx.empty_pred_l I empty, my.empty_pred_l I empty, h⟩ nx ny
    (tg_node_m (.bound 0) (.bound 1) (.bound 2) (.bound 3) (.bound 4)) (by simp -implicitDefEqProofs) ρ η images
  exact (tg_node_source_l xt nx hZF.1 (KP.exists_pair (ZF.modelsKP hZF)) ρ (.bound 0) (.bound 1) (.bound 2) (.bound 3) (.bound 4)).symm.trans
    (tr.trans (tg_node_source_l yt ny hZF.1 (KP.exists_pair (ZF.modelsKP hZF)) η (.bound 0) (.bound 1) (.bound 2) (.bound 3) (.bound 4)))

theorem Smap_d.tuple_preimage_l {k} {p q : M.Domain} {v : Fin (k+1) → M.Domain}
    (hp : Rd_entry_d p q j) (code : Rt_tuple_d v q) :
    ∃ w : Fin (k+1) → M.Domain, Rt_tuple_d w p ∧ ∀ i, Rd_entry_d (w i) (v i) j := by
  induction k generalizing p q with
  | zero =>
    exact ⟨fun _ => p, rfl, Fin.cases (code ▸ hp) (fun i => Fin.elim0 i)⟩
  | succ k ih =>
    obtain ⟨r, pair, tail⟩ := code
    obtain ⟨a, b, _, _, ab, ha, hb⟩ := h.kpair_preimage_l hZF hw xt yt mx my hp pair
    obtain ⟨w, cw, images⟩ := ih hb tail
    refine ⟨Fin.cases (motive := fun _ => M.Domain) a w, ?_, ?_⟩
    · exact ⟨b, ab, cw⟩
    · exact Fin.cases ha images


end YesMetaZFC.SetTheory.Internal
