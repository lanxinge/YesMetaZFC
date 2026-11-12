import YesMetaZFC.SetTheory.LargeCardinal.Iteration.System
import YesMetaZFC.Model.SetTheory.DirectedSystem.Relative
import YesMetaZFC.SetTheory.LargeCardinal.Iteration.StepSyntax
import YesMetaZFC.Model.SetTheory.Relations.Parity
import YesMetaZFC.SetTheory.MembershipInduction
import YesMetaZFC.Model.SetTheory.Embedding.RankFixed
import YesMetaZFC.Model.SetTheory.Internal.FiniteRecordRelative
import YesMetaZFC.SetTheory.Card.Cofinality.Boundedness
import YesMetaZFC.SetTheory.DependentChoice
import YesMetaZFC.SetTheory.RelationChain

/-! # 树枝的实际直接极限及全部规范初等嵌入

先把旧嵌入经标签同构搬到各分量，再取实际集合商。规范嵌入保留精确
代表方程，因此极限覆盖与交换律可从同一批商类直接读出。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem It_system_d.elementary_l {ω α T Q G B L A p H R : M.Domain}
    (hω : M.IsOmega ω) (h : It_diagram_d (kp_pair_l (ZF.modelsKP hZF)) ω α T Q G) (s : It_system_d B L Q G A p H R)
    (inside : M.MemberSubset B α)
    (ls : ∀ i j, Rd_entry_d i j L ↔ M.mem i B ∧ M.mem j B ∧ Rd_entry_d i j T) :
    Di_elementary_d I ω L A p H R := by
  obtain ⟨D, hq⟩ := h.family_l hZF
  intro i j c X S d Y V si sj hij
  obtain ⟨hi, hj, hij⟩ := (ls i j).mp hij
  obtain ⟨c₀, X₀, S₀, hc, mx⟩ := h.model_l hZF (inside i hi)
  obtain ⟨d₀, Y₀, V₀, hd, my⟩ := h.model_l hZF (inside j hj)
  obtain ⟨f, hf⟩ := h.map_l hZF hij
  have elem := h.elementary i j f c₀ X₀ S₀ d₀ Y₀ V₀ hf hc hd mx my
  obtain ⟨e, _, he, _, es, _⟩ := it_tag_iso_l hZF hω s.tags hq si hc mx
  obtain ⟨_, u, _, hu, _, us⟩ := it_tag_iso_l hZF hω s.tags hq sj hd my
  obtain ⟨v, hv, vs⟩ := smap_comp_l I hZF he elem
  obtain ⟨w, hw, ws⟩ := smap_comp_l I hZF hv hu
  refine ⟨w, hw, fun a b => ⟨?_, ?_⟩⟩
  · intro hab
    obtain ⟨ha, y, hay, hyb⟩ := (ws a b).mp hab
    obtain ⟨_, x, hax, hxy⟩ := (vs a y).mp hay
    obtain ⟨_, hp⟩ := (es a x).mp hax
    obtain ⟨hb, hq'⟩ := (us y b).mp hyb
    exact ⟨ha, hb, (s.arrows a b i j x y hp hq').mpr
      ⟨((si.2.1 a).mp ha).1, ((sj.2.1 b).mp hb).1, f, hf, hxy⟩⟩
  · rintro ⟨ha, hb, hab⟩
    obtain ⟨x, hp, _⟩ := s.tags.label_l (((si.2.1 a).mp ha).2)
    obtain ⟨y, hq', _⟩ := s.tags.label_l (((sj.2.1 b).mp hb).2)
    obtain ⟨g, hg, hxy⟩ := ((s.arrows a b i j x y hp hq').mp hab).2.2
    have hxy := h.map_unique_l hZF hg hf ▸ hxy
    exact (ws a b).mpr ⟨ha, y, (vs a y).mpr ⟨ha, x, (es a x).mpr ⟨ha, hp⟩, hxy⟩,
      (us y b).mpr ⟨hb, hq'⟩⟩

theorem it_stage_limit_l {ω α T Q G B L A p H R q c C V i d X S : M.Domain}
    (hω : M.IsOmega ω) (h : It_diagram_d (kp_pair_l (ZF.modelsKP hZF)) ω α T Q G) (s : It_system_d B L Q G A p H R)
    (elementary : Di_elementary_d I ω L A p H R)
    (limit : Di_limit_d A p H R q C V) (model : Smdl_d I c C V)
    (hi : M.mem i B) (hd : Rd_entry_d i d Q) (mx : Smdl_d I d X S) :
    ∃ j, Smap_d I ω d c X C j ∧
      ∀ x y, Rd_entry_d x y j ↔ M.mem x X ∧ ∃ a, KPair_d M a i x ∧ Rd_entry_d a y q := by
  obtain ⟨D, hq⟩ := h.family_l hZF
  obtain ⟨x, hx⟩ := mx.2.1
  obtain ⟨a, hp⟩ := (I).total i x
  have ha := (s.tags.nodes a).mpr ⟨i, x, hi, hp, d, X, S, hd, mx.1, hx⟩
  obtain ⟨d', Y, W, stage⟩ := di_stage_exists_l hZF s.system ((s.tags.index a i x hp).mpr ha)
  obtain ⟨_, u, _, hu, _, us⟩ := it_tag_iso_l hZF hω s.tags hq stage hd mx
  obtain ⟨e, he, es⟩ := di_elementary_limit_l hZF hω s.system limit elementary stage model
  obtain ⟨j, hj, js⟩ := smap_comp_l I hZF hu he
  refine ⟨j, hj, fun x y => (js x y).trans (and_congr_right fun hx => ?_)⟩
  apply exists_congr
  intro a
  refine ⟨fun ⟨hxa, hay⟩ => ⟨((us x a).mp hxa).2, ((es a y).mp hay).2⟩, fun ⟨hp, hay⟩ => ?_⟩
  have ha := (s.tags.nodes a).mpr ⟨i, x, hi, hp, d, X, S, hd, mx.1, hx⟩
  have haY := (stage.2.1 a).mpr ⟨ha, (s.tags.index a i x hp).mpr ha⟩
  exact ⟨(us x a).mpr ⟨haY, hp⟩, (es a y).mpr ⟨haY, hay⟩⟩

/-- 非空树枝的原始极限总能实际构造；其良基性留给独立的数学判据证明。 -/
theorem it_branch_data_l {ω α T Q G B : M.Domain} (hω : M.IsOmega ω)
    (h : It_diagram_d (kp_pair_l (ZF.modelsKP hZF)) ω α T Q G) (b : It_branch_d α T B) (ne : ∃ i, M.mem i B) :
    ∃ L A p H R q c C V,
      (∀ i j, Rd_entry_d i j L ↔ M.mem i B ∧ M.mem j B ∧ Rd_entry_d i j T) ∧
      It_system_d B L Q G A p H R ∧ Di_elementary_d I ω L A p H R ∧
      Di_limit_d A p H R q C V ∧ Smdl_d I c C V := by
  obtain ⟨L, order, ls⟩ := b.order_l (ZF.modelsKP hZF) h.order
  obtain ⟨A, p, H, R, s⟩ := it_system_l hZF hω h order b.subset ls
  obtain ⟨i, hi⟩ := ne
  obtain ⟨d, X, S, hd, mx⟩ := h.model_l hZF (b.subset i hi)
  obtain ⟨x, hx⟩ := mx.2.1
  obtain ⟨a, hp⟩ := (I).total i x
  have ha := (s.tags.nodes a).mpr ⟨i, x, hi, hp, d, X, S, hd, mx.1, hx⟩
  obtain ⟨c, q, C, V, limit, model⟩ := di_model_exists_l hZF s.system ⟨a, ha⟩
  exact ⟨L, A, p, H, R, q, c, C, V, ls, s, s.elementary_l hZF hω h b.subset ls, limit, model⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 极限投影的规范集合图

r 把带标号代表送到目标。各腿由去标签的同一个公式定义，故图唯一，
可由替代一次收集整列；这一步不选择商类代表，也不选择初等嵌入。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

def It_project_d (r i f : M.Domain) : Prop := (∀ p, M.mem p f → ∃ x y, KPair_d M p x y) ∧
  ∀ x y, Rd_entry_d x y f ↔ ∃ a, KPair_d M a i x ∧ Rd_entry_d a y r

def it_project_m {d} (r i f : Term d) : Formula 1 d := .conj (Formula.isRelation kpair_convention_l f)
  (.forallE (.forallE (.iff (rd_entry_m (.bound 1) .newest f.weaken.weaken) (.existsE
    (.conj (kpair_m .newest i.weaken.weaken.weaken (.bound 2)) (rd_entry_m .newest (.bound 1) r.weaken.weaken.weaken))))))
derive_free_closed it_project_m

theorem it_project_sat_l (hKP : M.Models KP) {d} (ρ : Env M d) (r i f : Term d) :
    Formula.satisfies ρ (it_project_m r i f) ↔ It_project_d (r.eval ρ) (i.eval ρ) (f.eval ρ) := by
  simp only [it_project_m, It_project_d, Formula.satisfies_conj_iff,
    Formula.satisfies_isRelation_iff (kp_pair_l hKP), Formula.satisfies_forall_iff,
    Formula.satisfies_iff_iff, Formula.satisfies_exists_iff, kpair_sat_l M hKP.1,
    rd_entry_sat_l hKP.1, Definitional.Term.eval_weaken]; rfl

theorem It_project_d.unique_l (hE : Extensional M) {r i f g : M.Domain}
    (hf : It_project_d r i f) (hg : It_project_d r i g) : f = g := by
  have sub f g (hf : It_project_d r i f) (hg : It_project_d r i g) p (hp : M.mem p f) : M.mem p g := by
    obtain ⟨x, y, hx⟩ := hf.1 p hp
    obtain ⟨q, hq, hqg⟩ := (hg.2 x y).mpr ((hf.2 x y).mp ⟨p, hx, hp⟩)
    exact kpair_unique_l M hE hq hx ▸ hqg
  exact hE.eq_of_same_members f g fun p => ⟨sub f g hf hg p, sub g f hg hf p⟩

structure It_embedding_d (J : kpair_convention_l.Interpretation M) (ω B Q G d N W P : M.Domain) : Prop where
  model : Smdl_d J d N W
  function : M.IsSetFunction J P
  domain : M.IsDomainOf J B P
  elementary : ∀ i f c X R, Rd_entry_d i f P → Rd_entry_d i c Q →
    Smdl_d J c X R → Smap_d J ω c d X N f
  commute : ∀ i j f u v, It_map_d G i j f → Rd_entry_d i u P → Rd_entry_d j v P →
    ∀ x y z, Rd_entry_d x y f → Rd_entry_d y z v → Rd_entry_d x z u

structure It_cone_d (J : kpair_convention_l.Interpretation M) (ω B Q G d N W P : M.Domain) : Prop
    extends It_embedding_d J ω B Q G d N W P where
  cover : ∀ y, M.mem y N → ∃ i f x, Rd_entry_d i f P ∧ Rd_entry_d x y f

/-! 锥的 owner 读取接口。

只要给出待运输集合已经落在极限模型 `N` 中，锥的实际覆盖字段就直接
返回其所在阶段、该阶段的嵌入图以及成员的 owner 见证；这一步不把外部
可数性或 branch-wise coverage 偷换成模型内覆盖。 -/
theorem It_cone_d.owner_l
    {J : kpair_convention_l.Interpretation M} (cone : It_cone_d J ω B Q G d N W P) {U : M.Domain}
    (inside : M.MemberSubset U N) :
    ∀ y, M.mem y U → ∃ i f x, Rd_entry_d i f P ∧ Rd_entry_d x y f := by
  intro y hy
  exact cone.cover y (inside y hy)

/-! 极限模型内集合的 owner 读取。

`owner_l` 接受成员包含；这里用传递性把一个已知属于 `N` 的集合自动
转成该包含关系。这样后续只需证明 `j(U₁) ∈ N`，就能读取全部阶段 owner，
而不把该成员性或外部 bookkeeping 偷塞进本定理。 -/
theorem It_cone_d.owner_mem_l
    {J : kpair_convention_l.Interpretation M} {ω B Q G d N W P U : M.Domain}
    (cone : It_cone_d J ω B Q G d N W P) (transitive : M.TransitiveSet N)
    (hU : M.mem U N) :
    ∀ y, M.mem y U → ∃ i f x, Rd_entry_d i f P ∧ Rd_entry_d x y f := by
  apply cone.owner_l
  intro y hy
  exact transitive U hU y hy

variable (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem it_projects_l {B r : M.Domain} (total : ∀ i, M.mem i B → ∃ f, It_project_d r i f) :
    ∃ P, M.IsSetFunction I P ∧ M.IsDomainOf I B P ∧
      ∀ i f, Rd_entry_d i f P ↔ M.mem i B ∧ It_project_d r i f := by
  let φ : BinarySchema 1 := { body := it_project_m (.bound 2) (.bound 1) .newest }
  let ρ : Env M 1 := ⟨fun _ => r, fun _ => r⟩
  have sat i f : φ.denote ρ i f ↔ It_project_d r i f := it_project_sat_l (ZF.modelsKP hZF) ..
  have ht i hi := (total i hi).imp (fun f hf => (sat i f).mpr hf)
  have unique i f g (hf : φ.denote ρ i f) (hg : φ.denote ρ i g) : f = g :=
    ((sat i f).mp hf).unique_l hZF.1 ((sat i g).mp hg)
  obtain ⟨D, hd⟩ := ZF.exists_functionalImage hZF φ ρ B ht unique
  obtain ⟨P, hp, ps⟩ := ZF.exists_setFunctionFromTo_of_denote hZF I φ ρ ht (fun i _ => unique i)
    (fun i f hi hf => (hd f).mpr ⟨i, hi, hf⟩)
  exact ⟨P, hp.1, hp.2.1, fun i f => (ps i f).trans (and_congr_right fun _ => sat i f)⟩

theorem it_project_elementary_l {ω α T Q G B L A p H R q c C V d N e r i b X S : M.Domain}
    (hω : M.IsOmega ω) (h : It_diagram_d (kp_pair_l (ZF.modelsKP hZF)) ω α T Q G) (s : It_system_d B L Q G A p H R)
    (elementary : Di_elementary_d I ω L A p H R) (limit : Di_limit_d A p H R q C V)
    (model : Smdl_d I c C V) (he : Smap_d I ω c d C N e)
    (rs : ∀ a y, Rd_entry_d a y r ↔ M.mem a A ∧ ∃ z, Rd_entry_d a z q ∧ Rd_entry_d z y e)
    (hi : M.mem i B) (hb : Rd_entry_d i b Q) (mx : Smdl_d I b X S) :
    ∃ f, Smap_d I ω b d X N f ∧ It_project_d r i f := by
  obtain ⟨D, hq⟩ := h.family_l hZF
  obtain ⟨j, hj, js⟩ := it_stage_limit_l hZF hω h s elementary limit model hi hb mx
  obtain ⟨f, hf, fs⟩ := smap_comp_l I hZF hj he
  refine ⟨f, hf, hf.1.1.1.1, fun x y => ⟨?_, ?_⟩⟩
  · intro hxy
    obtain ⟨_, z, hxz, hzy⟩ := (fs x y).mp hxy
    obtain ⟨_, a, hp, haz⟩ := (js x z).mp hxz
    exact ⟨a, hp, (rs a y).mpr ⟨(limit.projection.bound_l haz).1, z, haz, hzy⟩⟩
  · rintro ⟨a, hp, hay⟩
    obtain ⟨ha, z, haz, hzy⟩ := (rs a y).mp hay
    have hx := (ep_at_read_l hq hb mx.1).mp (s.tags.at_l ha hp)
    exact (fs x y).mpr ⟨hx, z, (js x z).mpr ⟨hx, a, hp, haz⟩, hzy⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 共尾多个根图的固定性传到良基极限

极限中的成员先由锥的覆盖性拉回某一阶段，再推进到具有完整前驱对应
的较晚阶段。内部成员归纳于是证明根腿逐点固定原传递低层。假设只读取
实际根图在该低层上的总性与前驱对应，不要求其像另有内部集合编码。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem It_cone_d.fixed_l {ω α T Q G b o c X R d N W P K : M.Domain}
    (hw : M.IsOmega ω) (diagram : It_diagram_d (kp_pair_l (ZF.modelsKP hZF)) ω α T Q G) (branch : It_branch_d α T b)
    (root : Rd_entry_d o c Q) (mx : Smdl_d I c X R)
    (mn : Smem_d I d N W) (nt : M.TransitiveSet N) (cone : It_cone_d (kp_pair_l (ZF.modelsKP hZF)) ω b Q G d N W P)
    (anchors : ∀ i, M.mem i b → ∃ k f a Y S,
      M.mem k b ∧ Rd_entry_d i k T ∧ It_map_d G o k f ∧ Rd_entry_d k a Q ∧ Smdl_d I a Y S ∧
      M.TransitiveSet K ∧ (∀ x, M.mem x K → ∃ y, Rd_entry_d x y f) ∧
      ∀ x y, M.mem x K → Rd_entry_d x y f → ∀ z,
        Rd_entry_d z y S ↔ ∃ a, M.mem a x ∧ Rd_entry_d a z f) :
    ∀ r, Rd_entry_d o r P → ∀ x, M.mem x K → Rd_entry_d x x r := by
  have basic : M.TransitiveSet K ∧ M.MemberSubset K X ∧
      ∀ x z, M.mem x K → M.mem z x → Rd_entry_d z x R := by
    obtain ⟨i, hi, _⟩ := branch.cofinal o ((diagram.model_domain o).mpr ⟨c, root⟩)
    obtain ⟨k, f, a, Y, S, _, _, edge, ha, my, trans, total, pred⟩ := anchors i hi
    have map := diagram.elementary o k f c X R a Y S edge root ha mx my
    refine ⟨trans, (fun x hx => ?_), fun x z hx zx => ?_⟩
    · obtain ⟨y,hxy⟩ := total x hx
      exact map.1.1.input_mem_of_pairMember hxy
    · obtain ⟨x',hxx⟩ := total x hx
      obtain ⟨z',hzz⟩ := total z (trans x hx z zx)
      exact (map.relation_l I hZF hw mx my hzz hxx).mpr ((pred x x' hx hxx z').mpr ⟨z,zx,hzz⟩)
  have kt := basic.1
  have low := basic.2.1
  let ρ : Env M 3 := ⟨Fin.cases K (Fin.cases o (fun _ => P)), fun _ => K⟩
  let φ : UnarySchema 3 := { body := set[4] ⟪⌜(.newest : Term 4)⌝ₛ ∈ ⌜(.bound 1 : Term 4)⌝ₛ →
    ∀ r y, ⌜rd_entry0_m⌝ₚ(⌜(.bound 2 : Term 4)⌝ₛ,r,⌜(.bound 3 : Term 4)⌝ₛ) →
      ⌜rd_entry0_m⌝ₚ(⌜(.newest : Term 4)⌝ₛ,y,r) → y = ⌜(.newest : Term 4)⌝ₛ⟫ }
  have sat x : φ.denote ρ x ↔ M.mem x K → ∀ r y, Rd_entry_d o r P → Rd_entry_d x y r → y = x := by
    simp only [φ, UnarySchema.denote, Formula.satisfies_imp_iff, Formula.satisfies_mem_iff,
      Formula.satisfies_forall_iff, rd_entry0_sat_l hZF.1, Formula.satisfies_extensionalEq_iff_eq hZF.1]
    rfl
  have fixed x (hx : M.mem x K) r y (hr : Rd_entry_d o r P) (xy : Rd_entry_d x y r) : y = x := by
    apply (sat x).mp (ZF.mem_ind_l M hZF I φ ρ ?_ x) hx r y hr xy
    intro x ih
    apply (sat x).mpr
    intro hx r y hr xy
    have jr := cone.elementary o r c X R hr root mx
    apply hZF.1.eq_of_same_members y x
    intro z
    constructor
    · intro zy
      obtain ⟨i, u, a, hi, az⟩ := cone.cover z (nt y (jr.1.1.output_mem_of_pairMember xy) z zy)
      obtain ⟨k, f, c', Z, V, hk, ik, of, hc, mz, _, total, pred⟩ :=
        anchors i ((cone.domain i).mpr ⟨u, hi⟩)
      obtain ⟨e, he⟩ := (diagram.model_domain i).mp (branch.subset i ((cone.domain i).mpr ⟨u, hi⟩))
      obtain ⟨Y, S, my⟩ := diagram.models i e he
      obtain ⟨v, hv⟩ := (cone.domain k).mp hk
      obtain ⟨g, hg⟩ := diagram.map_l hZF ik
      have jg := diagram.elementary i k g e Y S c' Z V hg he hc my mz
      have jv := cone.elementary k v c' Z V hv hc mz
      obtain ⟨a', _, aa⟩ := jg.1.1.2.2 a ((cone.elementary i u e Y S hi he my).1.1.input_mem_of_pairMember az)
      obtain ⟨z', _, az'⟩ := jv.1.1.2.2 a' (jg.1.1.output_mem_of_pairMember aa)
      have eq := (cone.elementary i u e Y S hi he my).1.1.1.2 a z' z
        (cone.commute i k g u v hg hi hv a a' z' aa az') az
      have az : Rd_entry_d a' z v := eq ▸ az'
      obtain ⟨x',hxx⟩ := total x hx
      have jf := diagram.elementary o k f c X R c' Z V of root hc mx mz
      obtain ⟨y', _, xy'⟩ := jv.1.1.2.2 x' (jf.1.1.output_mem_of_pairMember hxx)
      have ey := jr.1.1.1.2 x y' y
        (cone.commute o k f r v of hr hv x x' y' hxx xy') xy
      have ax := (jv.relation_l I hZF hw mz mn.1 az (ey ▸ xy')).mpr
        ((mn.2 z y).mpr ⟨nt y (jr.1.1.output_mem_of_pairMember xy) z zy, jr.1.1.output_mem_of_pairMember xy, zy⟩)
      obtain ⟨a₀, ha₀, a₀a⟩ := (pred x x' hx hxx a').mp ax
      have rootz := cone.commute o k f r v of hr hv a₀ a' z a₀a az
      exact ((sat a₀).mp (ih a₀ ha₀) (kt x hx a₀ ha₀) r z hr rootz).symm ▸ ha₀
    · intro zx
      obtain ⟨z', _, zz⟩ := jr.1.1.2.2 z (low z (kt x hx z zx))
      have eq := (sat z).mp (ih z zx) (kt x hx z zx) r z' hr zz
      exact ((mn.2 z y).mp ((jr.relation_l I hZF hw mx mn.1 (eq ▸ zz) xy).mp
        (basic.2.2 x z hx zx))).2.2
  intro r hr x hx
  obtain ⟨y, _, xy⟩ := (cone.elementary o r c X R hr root mx).1.1.2.2 x (low x hx)
  exact fixed x hx r y hr xy ▸ xy

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 回拉图表的子集关系在同一锥中保持

先用壳图恢复原箭头，再以锥交换律识别两条腿上的像。只使用实际传递
隶属结构和全初等图，不要求极限目标满足 ZF。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

def It_pull_subset_d (G π P : M.Domain) : Prop := ∀ i j f a a' b b' c p q x y,
  It_map_d G i j f → Rd_entry_d a a' π → Rd_entry_d b b' π → Rd_entry_d a' c f →
    M.MemberSubset c b' → Rd_entry_d i p P → Rd_entry_d j q P →
    Rd_entry_d a x p → Rd_entry_d b y q → M.MemberSubset x y

variable (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

/-- 同一原箭头的两端回拉后，锥交换律使它们在极限中的像相等。 -/
theorem it_cone_pull_entry_l {ω B R b U S u π T Q G Q₀ G₀ A d N W P i j f a a' b₀ b' p q x y : M.Domain}
    (hw : M.IsOmega ω) (bt : M.TransitiveSet B) (ut : M.TransitiveSet U)
    (mb : Smem_d I b B R) (mu : Smem_d I u U S) (hj : Smap_d I ω b u B U π)
    (hωB : M.mem ω B) (hG : Rd_entry_d G₀ G π)
    (small : It_diagram_d (kp_pair_l (ZF.modelsKP hZF)) ω ω T Q₀ G₀) (big : It_diagram_d (kp_pair_l (ZF.modelsKP hZF)) ω ω T Q G)
    (cone : It_embedding_d (kp_pair_l (ZF.modelsKP hZF)) ω A Q₀ G₀ d N W P)
    (hf : It_map_d G i j f) (haa : Rd_entry_d a a' π) (hbb : Rd_entry_d b₀ b' π)
    (image : Rd_entry_d a' b' f) (hp : Rd_entry_d i p P) (hq : Rd_entry_d j q P)
    (hax : Rd_entry_d a x p) (hby : Rd_entry_d b₀ y q) : x = y := by
  have order := big.map_bound_l hZF hf
  have bounds := big.order.bound i j order
  obtain ⟨g, hg⟩ := small.map_l hZF order
  obtain ⟨r, pair, hr⟩ := hg
  have own := rd_entry_transitive_l bt (hj.1.1.input_mem_of_pairMember hG) hr
  have nat := hj.natural_l hZF hw bt ut mb mu hωB
  have fixed := hj.fixed_pair_l hZF hw bt ut mb mu own.1 pair (nat i bounds.1) (nat j bounds.2)
  obtain ⟨g', _, hgg⟩ := hj.1.1.2.2 g own.2
  have map : It_map_d G i j g' := ⟨r, pair, (hj.entry_l hZF hw bt ut mb mu fixed hgg hG).mp hr⟩
  have eq := big.map_unique_l hZF map hf
  subst g'
  have entry := (hj.entry_l hZF hw bt ut mb mu haa hbb hgg).mpr image
  obtain ⟨c, X, R₀, hc, mx⟩ := small.model_l hZF bounds.1
  exact (cone.elementary i p c X R₀ hp hc mx).1.1.1.2 a x y hax
    (cone.commute i j g p q ⟨r, pair, hr⟩ hp hq a b₀ y entry hby)

theorem it_cone_pull_subset_l {ω B R b U S u π T Q G Q₀ G₀ A d N W P : M.Domain}
    (hw : M.IsOmega ω) (bt : M.TransitiveSet B) (ut : M.TransitiveSet U) (nt : M.TransitiveSet N)
    (mb : Smem_d I b B R) (mu : Smem_d I u U S) (mn : Smem_d I d N W)
    (hj : Smap_d I ω b u B U π) (hωB : M.mem ω B) (hQ : M.mem Q₀ B) (hG : Rd_entry_d G₀ G π)
    (small : It_diagram_d (kp_pair_l (ZF.modelsKP hZF)) ω ω T Q₀ G₀) (big : It_diagram_d (kp_pair_l (ZF.modelsKP hZF)) ω ω T Q G)
    (models : ∀ i c, Rd_entry_d i c Q₀ → ∃ X R, Smem_d I c X R ∧ M.TransitiveSet X)
    (cone : It_embedding_d (kp_pair_l (ZF.modelsKP hZF)) ω A Q₀ G₀ d N W P) : It_pull_subset_d G π P := by
  intro i j f a a' b' b'' z p q x y hf haa hbb haz sub hp hq hax hby
  have order := big.map_bound_l hZF hf
  have bounds := big.order.bound i j order
  obtain ⟨g, hg⟩ := small.map_l hZF order
  obtain ⟨r, pair, hr⟩ := hg
  have own := rd_entry_transitive_l bt (hj.1.1.input_mem_of_pairMember hG) hr
  have nat := hj.natural_l hZF hw bt ut mb mu hωB
  have fixed := hj.fixed_pair_l hZF hw bt ut mb mu own.1 pair (nat i bounds.1) (nat j bounds.2)
  obtain ⟨g', _, hgg⟩ := hj.1.1.2.2 g own.2
  have image : It_map_d G i j g' := ⟨r, pair, (hj.entry_l hZF hw bt ut mb mu fixed hgg hG).mp hr⟩
  have eq := big.map_unique_l hZF image hf
  subst g'
  obtain ⟨c, hc⟩ := (small.model_domain i).mp bounds.1
  obtain ⟨e, he⟩ := (small.model_domain j).mp bounds.2
  obtain ⟨X, R₀, mx, xt⟩ := models i c hc
  obtain ⟨Y, S₀, my, yt⟩ := models j e he
  have left := cone.elementary i p c X R₀ hp hc mx.1
  have right := cone.elementary j q e Y S₀ hq he my.1
  have edge := small.elementary i j g c X R₀ e Y S₀ ⟨r, pair, hr⟩ hc he mx.1 my.1
  obtain ⟨v, hv, hav⟩ := edge.1.1.2.2 a (left.1.1.input_mem_of_pairMember hax)
  have hYB := (my.1.1.mem_l M bt (rd_entry_transitive_l bt hQ he).2).1
  obtain ⟨v', _, hvv⟩ := hj.1.1.2.2 v (bt Y hYB v hv)
  have image := (hj.entry_l hZF hw bt ut mb mu haa hvv hgg).mp hav
  obtain ⟨c', X', R', hc', mx'⟩ := big.model_l hZF bounds.1
  obtain ⟨e', Y', S', he', my'⟩ := big.model_l hZF bounds.2
  have original := big.elementary i j f c' X' R' e' Y' S' hf hc' he' mx' my'
  have eq := original.1.1.1.2 a' v' z image haz
  subst v'
  have smaller := (hj.subset_l hZF hw bt ut mb mu hvv hbb).mpr sub
  obtain ⟨w, _, hvw⟩ := right.1.1.2.2 v hv
  have eq := left.1.1.1.2 a w x (cone.commute i j g p q ⟨r, pair, hr⟩ hp hq a v w hav hvw) hax
  subst w
  exact (right.subset_l hZF hw yt nt my mn hvw hby).mp smaller

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 实际复合图的结合律及相容返回列的复合式 -/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

theorem It_comp_d.assoc_l {f g h p q r : M.Domain}
    (hp : It_comp_d f g p) (hq : It_comp_d g h q) (hr : It_comp_d f q r) : It_comp_d p h r := by
  refine ⟨hr.1, fun x z => ⟨?_, ?_⟩⟩
  · intro hxz
    obtain ⟨y, hxy, hyz⟩ := (hr.2 x z).mp hxz
    obtain ⟨v, hyv, hvz⟩ := (hq.2 y z).mp hyz
    exact ⟨v, (hp.2 x v).mpr ⟨y, hxy, hyv⟩, hvz⟩
  · rintro ⟨v, hxv, hvz⟩
    obtain ⟨y, hxy, hyv⟩ := (hp.2 x v).mp hxv
    exact (hr.2 x z).mpr ⟨y, hxy, (hq.2 y z).mpr ⟨v, hyv, hvz⟩⟩

theorem It_embedding_d.comp_l (hZF : M.Models ZF) {ω α T Q G B a A S P i j f u v : M.Domain}
    (diagram : It_diagram_d (kp_pair_l (ZF.modelsKP hZF)) ω α T Q G) (inside : M.MemberSubset B α)
    (maps : It_embedding_d (kp_pair_l (ZF.modelsKP hZF)) ω B Q G a A S P)
    (hf : It_map_d G i j f) (hu : Rd_entry_d i u P) (hv : Rd_entry_d j v P) : It_comp_d f v u := by
  obtain ⟨c, X, R, hc, mx⟩ := diagram.model_l hZF (inside i ((maps.domain i).mpr ⟨u, hu⟩))
  obtain ⟨d, Y, W, hd, my⟩ := diagram.model_l hZF (inside j ((maps.domain j).mpr ⟨v, hv⟩))
  have ff := (diagram.elementary i j f c X R d Y W hf hc hd mx my).1.1
  have uu := (maps.elementary i u c X R hu hc mx).1.1
  have vv := (maps.elementary j v d Y W hv hd my).1.1
  refine ⟨uu.1.1, fun x z => ⟨?_, fun ⟨y, hxy, hyz⟩ => maps.commute i j f u v hf hu hv x y z hxy hyz⟩⟩
  intro hxz
  obtain ⟨y, hy, hxy⟩ := ff.2.2 x (uu.input_mem_of_pairMember hxz)
  obtain ⟨z', _, hyz⟩ := vv.2.2 y hy
  have eq := uu.1.2 x z' z (maps.commute i j f u v hf hu hv x y z' hxy hyz) hxz
  exact ⟨y, hxy, eq ▸ hyz⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 良基树枝极限的传递模型与整列嵌入

规范投影与 Mostowski 图复合，实际产生新模型及每条枝嵌入。
源理论、有限序列空间及 ω 的保持从任一枝结点传递，不重新假设。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem it_limit_cone_l {ω α T Q G B L A p H R q c C V d N W e : M.Domain}
    (hω : M.IsOmega ω) (h : It_diagram_d (kp_pair_l (ZF.modelsKP hZF)) ω α T Q G) (inside : M.MemberSubset B α)
    (s : It_system_d B L Q G A p H R) (elementary : Di_elementary_d I ω L A p H R)
    (limit : Di_limit_d A p H R q C V) (model : Smdl_d I c C V) (target : Smdl_d I d N W)
    (he : Smap_d I ω c d C N e) (onto : ∀ y, M.mem y N → ∃ z, M.mem z C ∧ Rd_entry_d z y e) :
    ∃ P r, It_cone_d (kp_pair_l (ZF.modelsKP hZF)) ω B Q G d N W P ∧ Fn0_d A N r ∧
      (∀ a y, Rd_entry_d a y r ↔ M.mem a A ∧ ∃ z, Rd_entry_d a z q ∧ Rd_entry_d z y e) ∧
      ∀ i f, Rd_entry_d i f P ↔ M.mem i B ∧ It_project_d r i f := by
  obtain ⟨r, hr, rs⟩ := ZF.exists_compositionFunction hZF I
    (fn0_function_l (ZF.modelsKP hZF) limit.projection) he.1.1
  have leg i (hi : M.mem i B) : ∃ f, It_project_d r i f := by
    obtain ⟨b, X, S, hb, mx⟩ := h.model_l hZF (inside i hi)
    obtain ⟨f, _, hf⟩ := it_project_elementary_l hZF hω h s elementary limit model he rs hi hb mx
    exact ⟨f, hf⟩
  obtain ⟨P, pf, pd, ps⟩ := it_projects_l hZF leg
  have typed i f b X S (hf : Rd_entry_d i f P) (hb : Rd_entry_d i b Q) (mx : Smdl_d I b X S) :
      Smap_d I ω b d X N f := by
    obtain ⟨j, hj, js⟩ := it_project_elementary_l hZF hω h s elementary limit model he rs ((ps i f).mp hf).1 hb mx
    exact js.unique_l hZF.1 ((ps i f).mp hf).2 ▸ hj
  have commute i j f u v (hf : It_map_d G i j f) (hu : Rd_entry_d i u P) (hv : Rd_entry_d j v P)
      x y z (hxy : Rd_entry_d x y f) (hyz : Rd_entry_d y z v) : Rd_entry_d x z u := by
    obtain ⟨b, hb, hbr⟩ := (((ps j v).mp hv).2.2 y z).mp hyz
    obtain ⟨hbA, t, hbt, htz⟩ := (rs b z).mp hbr
    obtain ⟨c₀, X, S, hc, mx⟩ := h.model_l hZF (inside i ((ps i u).mp hu).1)
    obtain ⟨d₀, Y, W₀, hd, my⟩ := h.model_l hZF (inside j ((ps j v).mp hv).1)
    have ff := h.elementary i j f c₀ X S d₀ Y W₀ hf hc hd mx my
    obtain ⟨a, ha⟩ := (I).total i x
    have haA := (s.tags.nodes a).mpr ⟨i, x, ((ps i u).mp hu).1, ha,
      c₀, X, S, hc, mx.1, ff.1.1.input_mem_of_pairMember hxy⟩
    have hab := (s.arrows a b i j x y ha hb).mpr ⟨haA, hbA, f, hf, hxy⟩
    obtain ⟨t', _, hat⟩ := limit.projection.2.1 a haA
    have eq := limit.commute_l s.system hab hat hbt
    exact (((ps i u).mp hu).2.2 x z).mpr ⟨a, ha, (rs a z).mpr ⟨haA, t, eq ▸ hat, htz⟩⟩
  have cover y (hy : M.mem y N) : ∃ i f x, Rd_entry_d i f P ∧ Rd_entry_d x y f := by
    obtain ⟨z, hz, hzy⟩ := onto y hy
    obtain ⟨a, haz⟩ := (limit.range z).mp hz
    obtain ⟨i, x, hi, hp, _⟩ := (s.tags.nodes a).mp (limit.projection.bound_l haz).1
    obtain ⟨f, hf⟩ := (pd i).mp hi
    exact ⟨i, f, x, hf, (((ps i f).mp hf).2.2 x y).mpr
      ⟨a, hp, (rs a y).mpr ⟨(limit.projection.bound_l haz).1, z, haz, hzy⟩⟩⟩
  exact ⟨P, r, ⟨⟨target, pf, pd, typed, commute⟩, cover⟩, fn0_of_function_l (ZF.modelsKP hZF) hr, rs, ps⟩

theorem it_limit_model_l {ω α T Q G B L A p H R q c C V i b X S : M.Domain}
    (h : It_diagram_d (kp_pair_l (ZF.modelsKP hZF)) ω α T Q G) (inside : M.MemberSubset B α)
    (s : It_system_d B L Q G A p H R) (elementary : Di_elementary_d I ω L A p H R)
    (limit : Di_limit_d A p H R q C V) (model : Smdl_d I c C V) (wf : Wf_rel_d C V)
    (hi : M.mem i B) (hb : Rd_entry_d i b Q) (mx : Smdl_d I b X S) (source : It_source_d hZF ω b) :
    ∃ d N W P e r, It_cone_d (kp_pair_l (ZF.modelsKP hZF)) ω B Q G d N W P ∧ It_source_d hZF ω d ∧
      Smem_d I d N W ∧ M.TransitiveSet N ∧ Wc_graph_d C V e ∧ M.IsSetBijectionFromTo I e C N ∧
      Smap_d I ω c d C N e ∧ Fn0_d A N r ∧
      (∀ a y, Rd_entry_d a y r ↔ M.mem a A ∧ ∃ z, Rd_entry_d a z q ∧ Rd_entry_d z y e) ∧
      ∀ k f, Rd_entry_d k f P ↔ M.mem k B ∧ It_project_d r k f := by
  obtain ⟨X₀, S₀, _, _, _, code, core, _⟩ := source.objects
  obtain ⟨eqX, eqS⟩ := smdl_unique_l I code mx
  subst X₀ S₀
  obtain ⟨j, hj, _⟩ := it_stage_limit_l hZF source.omega h s elementary limit model hi hb mx
  obtain ⟨N, e, _, d, W, ht, wc, bij, target, elem, _, _, _⟩ :=
    wc_smaps_l hZF source.omega model wf (hj.extensional_l hZF source.omega mx model core.ext)
  obtain ⟨P, r, cone, hr, rs, ps⟩ := it_limit_cone_l hZF source.omega h inside s elementary limit model target.1 elem bij.2
  obtain ⟨f, hf⟩ := (cone.domain i).mp hi
  have ff := cone.elementary i f b X S hf hb mx
  obtain ⟨K', next⟩ := source.image_mem_l hZF mx target ht ff
  exact ⟨d, N, W, P, e, r, cone, it_source_mem_l hZF target next, target, ht, wc, bij, elem, hr, rs, ps⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 实际记录坐标在同一锥中的像列

只使用原记录函数、当前节点的原关系模型和实际锥映射。背景替换构造全像列，
目标不需要另有替换公理，记录元数及所读坐标均由调用处指定。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

def Tg_limit_value_d {n} (b a : Fin (n+1)) (f P i x : M.Domain) : Prop := ∃ v : Fin (n+1) → M.Domain,
  ∃ s j, Rd_entry_d i s f ∧ Rt_tuple_d v s ∧ Rd_entry_d (v b) j P ∧ Rd_entry_d (v a) x j

def tg_limit_value_m {d n} (b a : Fin (n+1)) (f P i x : Term d) : Formula 1 d :=
  let e : Term d → Term ((n+1)+d) := fun t => t.rename (Fin.natAdd (n+1))
  let v : Fin (n+1) → Term ((n+1)+d) := fun j => .bound (j.castAdd d)
  rb_exists_m (n := n+1) (.existsE (.existsE
    (.conj (rd_entry0_m (e i).weaken.weaken (.bound 1) (e f).weaken.weaken)
      (.conj (rt_tuple_m (fun j => (v j).weaken.weaken) (.bound 1))
        (.conj (rd_entry0_m (v b).weaken.weaken .newest (e P).weaken.weaken)
          (rd_entry0_m (v a).weaken.weaken (e x).weaken.weaken .newest))))))

@[simp] theorem tg_limit_value_closed_l {d n} (b a : Fin (n+1)) (f P i x : Term d)
    (hf : f.freeSupport = []) (hP : P.freeSupport = []) (hi : i.freeSupport = []) (hx : x.freeSupport = []) :
    (tg_limit_value_m b a f P i x).FreeClosed := by
  simp -implicitDefEqProofs [tg_limit_value_m,Definitional.Formula.FreeClosed,hf,hP,hi,hx]
  exact rt_tuple_closed_l _ _ (fun _ => rfl) rfl

theorem tg_limit_value_sat_l (hE : Extensional M) {d n} (b a : Fin (n+1))
    (η : Env M d) (f P i x : Term d) : Formula.satisfies η (tg_limit_value_m b a f P i x) ↔
      Tg_limit_value_d b a (f.eval η) (P.eval η) (i.eval η) (x.eval η) := by
  simp only [tg_limit_value_m,Tg_limit_value_d,rb_exists_sat_l,Formula.satisfies_exists_iff,
    Formula.satisfies_conj_iff,rd_entry0_sat_l hE,rt_tuple_sat_l hE,Definitional.Term.eval_weaken,
    rb_old_eval_l,Term.eval_bound,Fin.addCases_left]
  rfl

theorem It_embedding_d.record_values_l (hZF : M.Models ZF) {n} (b a : Fin (n+1))
    {ω B Q G d N W P D f : M.Domain} (cone : It_embedding_d (kp_pair_l (ZF.modelsKP hZF)) ω B Q G d N W P)
    (fn : Fn0_d ω D f) (records : ∀ i s, Rd_entry_d i s f → ∃ v : Fin (n+1) → M.Domain, Rt_tuple_d v s)
    (nodes : ∀ i s (v : Fin (n+1) → M.Domain), Rd_entry_d i s f → Rt_tuple_d v s →
      ∃ c X R, Rd_entry_d (v b) c Q ∧ Smdl_d (kp_pair_l (ZF.modelsKP hZF)) c X R ∧ M.mem (v a) X ∧ M.mem (v b) B) :
    ∃ F, Fn0_d ω N F ∧ ∀ i x, Rd_entry_d i x F ↔ Tg_limit_value_d b a f P i x := by
  let I := kp_pair_l (ZF.modelsKP hZF)
  have total i (hi : M.mem i ω) : ∃ x, Tg_limit_value_d b a f P i x := by
    obtain ⟨s,_,hs⟩ := fn.2.1 i hi
    obtain ⟨v,code⟩ := records i s hs
    obtain ⟨c,X,R,node,model,mem,hb⟩ := nodes i s v hs code
    obtain ⟨j,hj⟩ := (cone.domain (v b)).mp hb
    obtain ⟨x,_,hx⟩ := (cone.elementary (v b) j c X R hj node model).1.1.2.2 _ mem
    exact ⟨x,v,s,j,hs,code,hj,hx⟩
  have unique i x y (hx : Tg_limit_value_d b a f P i x) (hy : Tg_limit_value_d b a f P i y) : x = y := by
    obtain ⟨v,s,j,hs,ps,hj,hx⟩ := hx
    obtain ⟨w,t,k,ht,pt,hk,hy⟩ := hy
    have eq := (fn0_function_l (ZF.modelsKP hZF) fn).1.2 i t s ht hs
    subst t
    have eq := rt_tuple_inj_l pt ps
    subst w
    have eq := cone.function.2 (v b) k j hk hj
    subst k
    obtain ⟨c,X,R,node,model,_⟩ := nodes i s v hs ps
    exact (cone.elementary (v b) j c X R hj node model).1.1.1.2 _ x y hx hy
  let η : Env M 2 := ⟨fun i => [f,P].get i,fun _ => f⟩
  let φ : BinarySchema 2 := { body := tg_limit_value_m b a (.bound 2) (.bound 3) (.bound 1) .newest }
  have sat i x : φ.denote η i x ↔ Tg_limit_value_d b a f P i x := tg_limit_value_sat_l hZF.1 ..
  obtain ⟨F,ff,fs⟩ := ZF.exists_setFunctionFromTo_of_denote hZF I φ η
    (fun i hi => (total i hi).imp fun x hx => (sat i x).mpr hx)
    (fun i _ x y hx hy => unique i x y ((sat i x).mp hx) ((sat i y).mp hy)) (by
      intro i x _ hx
      obtain ⟨v,s,j,hs,code,hj,hx⟩ := (sat i x).mp hx
      obtain ⟨c,X,R,node,model,_⟩ := nodes i s v hs code
      exact (cone.elementary (v b) j c X R hj node model).1.1.output_mem_of_pairMember hx)
  refine ⟨F,fn0_of_function_l (ZF.modelsKP hZF) ff,fun i x => (fs i x).trans ?_⟩
  exact (and_congr_right fun _ => sat i x).trans ⟨And.right,fun hx =>
    ⟨hx.elim fun _ hv => hv.elim fun _ hs => hs.elim fun _ hs => (fn.bound_l hs.1).1,hx⟩⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 共尾树枝的内部良基性

分量使用实际良基证书；隶属实例由背景正则性构造。若时间长度的共尾度大于 ω，
内部可数指标族有界，共尾枝将其送到同一分量；ZF＋DC 因而排除下降链。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

/-- 指定结构码的实际良基性；一般树节点不带此条件。 -/
def It_wf_d (I : kpair_convention_l.Interpretation M) (c : M.Domain) : Prop :=
  ∃ X R, Smdl_d I c X R ∧ Wf_rel_d X R

/-- 任意实际隶属模型由背景正则性给出良基证书，无需载体传递。 -/
theorem it_wf_mem_l (hKP : M.Models KP) {c X R : M.Domain}
    (model : Smem_d (kp_pair_l hKP) c X R) : It_wf_d (kp_pair_l hKP) c := by
  refine ⟨X, R, model.1, fun Z _ ne => ?_⟩
  obtain ⟨x, hx, minimal⟩ := KP.mem_minimal_exists_d hKP ne
  exact ⟨x, hx, fun y hy rel => minimal y hy ((model.2 y x).mp rel).2.2⟩

theorem It_wf_d.read_l (I : kpair_convention_l.Interpretation M) {c X R : M.Domain}
    (h : It_wf_d I c) (model : Smdl_d I c X R) : Wf_rel_d X R := by
  obtain ⟨Y, S, code, wf⟩ := h
  obtain ⟨rfl, rfl⟩ := smdl_unique_l I code model
  exact wf

theorem It_tag_d.wf_l (hZF : M.Models ZF) {B Q A p R D H : M.Domain}
    (h : It_tag_d B Q A p R) (hq : Fn0_d D H Q)
    (models : ∀ i c, M.mem i B → Rd_entry_d i c Q → It_wf_d (kp_pair_l (ZF.modelsKP hZF)) c) :
    Di_wf_d A p R := by
  let I := kp_pair_l (ZF.modelsKP hZF)
  intro i Z hz indexed hn
  obtain ⟨u, hu⟩ := hn
  obtain ⟨_, _, c, _, _, hc, _, _⟩ := h.label_l (indexed u hu)
  obtain ⟨X, S, model, wx⟩ := models i c (h.projection.bound_l (indexed u hu)).2 hc
  let φ : BinarySchema 1 := { body := kpair_m (.bound 1) (.bound 2) .newest }
  let ρ : Env M 1 := ⟨fun _ => i, fun _ => i⟩
  have sat a x : φ.denote ρ a x ↔ KPair_d M a i x := kpair_sat_l M hZF.1 ..
  obtain ⟨f, hf, fs⟩ := ZF.exists_setFunctionFromTo_of_denote hZF I φ ρ (source := Z) (target := X)
    (fun a ha => by
      obtain ⟨x, hx, _⟩ := h.label_l (indexed a ha)
      exact ⟨x, (sat a x).mpr hx⟩)
    (fun a _ x y hx hy => (kpair_injective_l M ((sat a x).mp hx) ((sat a y).mp hy)).2)
    (fun a x ha hx => (ep_at_read_l hq hc model.1).mp (h.at_l (hz a ha) ((sat a x).mp hx)))
  have wz : Wf_rel_d Z R := wf_of_map_l hZF wx (fn0_of_function_l (ZF.modelsKP hZF) hf) (by
    intro a b x y hab hax hby
    have ha := (sat a x).mp ((fs a x).mp hax).2
    have hb := (sat b y).mp ((fs b y).mp hby).2
    exact (ep_rel_read_l hq hc model.1).mp ((h.relation_l ha hb).mp hab).2.2)
  exact wz Z (fun _ hx => hx) ⟨u, hu⟩

theorem It_branch_d.forward_l {α T B i j : M.Domain} (h : It_order_d α T) (b : It_branch_d α T B)
    (hi : M.mem i B) (hj : M.mem j B) (below : i = j ∨ M.mem i j) : Rd_entry_d i j T := by
  rcases below with rfl | hij
  · exact h.refl _ (b.subset _ hj)
  · rcases b.chain i j hi hj with ht | ht
    · exact ht
    · rcases h.forward j i ht with rfl | hji
      · exact (h.ordinal.wellOrder.linear.irrefl _ (b.subset _ hi) hij).elim
      · exact (h.ordinal.wellOrder.linear.irrefl j (b.subset j hj)
          ((h.ordinal.mem (b.subset j hj)).transitive i hij j hji)).elim

theorem It_branch_d.sigma_l (hZF : M.Models ZF) {ω α κ T B L : M.Domain}
    (h : It_order_d α T) (b : It_branch_d α T B)
    (hκ : M.IsCofinality (kp_pair_l (ZF.modelsKP hZF)) κ α) (hωκ : M.mem ω κ)
    (ls : ∀ i j, Rd_entry_d i j L ↔ M.mem i B ∧ M.mem j B ∧ Rd_entry_d i j T) : Di_sigma_d ω B L := by
  let I := kp_pair_l (ZF.modelsKP hZF)
  intro f hf
  have ff := fn0_function_l (ZF.modelsKP hZF) (hf.mono_target_l b.subset)
  obtain ⟨D, hd⟩ := ZF.exists_range_of_setFunction hZF I ff.1 ff.2.1
  obtain ⟨k, hk, upper⟩ := (hκ.range_bounded_of_domain_mem hZF I hωκ ff hd).exists_bound
  obtain ⟨j, hj, above⟩ := b.cofinal k hk
  refine ⟨j, hj, fun n i hni => (ls i j).mpr ⟨(hf.bound_l hni).2, hj, b.forward_l h (hf.bound_l hni).2 hj ?_⟩⟩
  rcases upper i ((hd i).mpr ⟨n, hni⟩) with rfl | hik
  · exact above
  · rcases above with rfl | hkj
    · exact Or.inr hik
    · exact Or.inr ((h.ordinal.mem (b.subset j hj)).transitive k hkj i hik)

/-- 证书记录实际树枝、实际带标号系统及其良基商；所有字段由下面的构造给出。 -/
def It_wf_branch_d (hZF : M.Models ZF) (ω α T Q G B : M.Domain) : Prop := It_branch_d α T B ∧
  ∃ L A p H R q c C V,
    (∀ i j, Rd_entry_d i j L ↔ M.mem i B ∧ M.mem j B ∧ Rd_entry_d i j T) ∧
    It_system_d B L Q G A p H R ∧ Di_elementary_d (kp_pair_l (ZF.modelsKP hZF)) ω L A p H R ∧
    Di_limit_d A p H R q C V ∧ Smdl_d (kp_pair_l (ZF.modelsKP hZF)) c C V ∧ Wf_rel_d C V

/-- 实际非良基极限的证书保留原带标号系统、投影及商模型。 -/
def It_ill_branch_d (hZF : M.Models ZF) (ω α T Q G B : M.Domain) : Prop := It_branch_d α T B ∧
  ∃ L A p H R q c C V,
    (∀ i j, Rd_entry_d i j L ↔ M.mem i B ∧ M.mem j B ∧ Rd_entry_d i j T) ∧
    It_system_d B L Q G A p H R ∧ Di_elementary_d (kp_pair_l (ZF.modelsKP hZF)) ω L A p H R ∧
    Di_limit_d A p H R q C V ∧ Smdl_d (kp_pair_l (ZF.modelsKP hZF)) c C V ∧ ¬ Wf_rel_d C V

theorem it_sigma_branch_l (hZF : M.Models ZF) {ω α κ T Q G B : M.Domain}
    (hω : M.IsOmega ω) (h : It_diagram_d (kp_pair_l (ZF.modelsKP hZF)) ω α T Q G) (b : It_branch_d α T B)
    (hκ : M.IsCofinality (kp_pair_l (ZF.modelsKP hZF)) κ α) (hωκ : M.mem ω κ)
    (dc : Dc_d (kp_pair_l (ZF.modelsKP hZF)) ω)
    (models : ∀ i c, M.mem i B → Rd_entry_d i c Q → It_wf_d (kp_pair_l (ZF.modelsKP hZF)) c) :
    It_wf_branch_d hZF ω α T Q G B := by
  obtain ⟨i, hi⟩ := hκ.hasCofinalSequence.elim fun _ hf => hf.1.2.1
  obtain ⟨j, hj, _⟩ := b.cofinal i hi
  obtain ⟨L, A, p, H, R, q, c, C, V, ls, s, elem, limit, model⟩ := it_branch_data_l hZF hω h b ⟨j, hj⟩
  obtain ⟨D, hq⟩ := h.family_l hZF
  exact ⟨b, L, A, p, H, R, q, c, C, V, ls, s, elem, limit, model,
    di_sigma_wf_l hZF hω dc s.system (b.sigma_l hZF h.order hκ hωκ ls) (s.tags.wf_l hZF hq models) limit⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 良基原枝回拉各节点的内部良基性

直接使用该枝已经给出的原始直接极限及其规范阶段嵌入，不另选坍塌，
也不要求源模型有完整背景数字图。关系保持映射已经足够回拉良基性。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

/-- 枝上任一实际节点都嵌入同一个良基直接极限。 -/
theorem It_wf_branch_d.node_wf_l
    {ω α T Q G B i c X R : M.Domain}
    (wf : It_wf_branch_d hZF ω α T Q G B) (hw : M.IsOmega ω)
    (diagram : It_diagram_d (kp_pair_l (ZF.modelsKP hZF)) ω α T Q G) (hi : M.mem i B)
    (node : Rd_entry_d i c Q) (model : Smdl_d I c X R) : Wf_rel_d X R := by
  obtain ⟨_,L,A,p,H,S,q,d,N,W,_,system,elementary,limit,target,well⟩ := wf
  obtain ⟨j,map,_⟩ := it_stage_limit_l hZF hw diagram system elementary limit target hi node model
  exact wf_of_map_l hZF well (fn0_of_function_l (ZF.modelsKP hZF) map.1.1)
    (fun a b x y ab ax by' => (map.relation_l I hZF hw model target ax by').mp ab)

/-- ω 长原图的每条共尾枝含有根；非良基根因而不可能有良基共尾枝。 -/
theorem It_wf_branch_d.root_wf_l
    {ω T Q G B o c X R : M.Domain}
    (wf : It_wf_branch_d hZF ω ω T Q G B) (hw : M.IsOmega ω)
    (diagram : It_diagram_d (kp_pair_l (ZF.modelsKP hZF)) ω ω T Q G) (empty : ∀ x, ¬ M.mem x o)
    (node : Rd_entry_d o c Q) (model : Smdl_d I c X R) : Wf_rel_d X R := by
  have ho := num_mem_l hZF.1 hw (show Num_d 0 o from empty)
  obtain ⟨k,hk,_⟩ := wf.1.cofinal o ho
  have root := wf.1.down o k
    (diagram.order.root_l hZF empty k (wf.1.subset k hk)) hk
  exact wf.node_wf_l hZF hw diagram root node model

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 共尾 ω 树枝的实际相邻结点列

每一步取分支上严格较大的最小结点，以 ZF 的确定迭代构造内部 ω 列。
最小性保证相邻项确实是树前驱，因而不会跳过恢复图的一点扩张。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)
include hZF

theorem It_pred_d.unique_l {ω T i j y : M.Domain} (order : It_order_d ω T)
    (h : It_pred_d T i y) (g : It_pred_d T j y) (hy : M.mem y ω) : i = j := by
  have ij := ((g.2 i).mp ((h.2 i).mpr (Or.inr (order.refl i (order.ordinal.transitive y hy i h.1))))).elim
    (fun eq => (KP.mem_irrefl_d (ZF.modelsKP hZF) y (eq ▸ h.1)).elim) id
  have ji := ((h.2 j).mp ((g.2 j).mpr (Or.inr (order.refl j (order.ordinal.transitive y hy j g.1))))).elim
    (fun eq => (KP.mem_irrefl_d (ZF.modelsKP hZF) y (eq ▸ g.1)).elim) id
  rcases order.forward i j ij with eq | lt
  · exact eq
  · rcases order.forward j i ji with eq | gt
    · exact eq.symm
    · exact (KP.mem_irrefl_d (ZF.modelsKP hZF) i ((order.ordinal.mem (order.bound j i ji).2).transitive j gt i lt)).elim

theorem It_branch_d.successor_sequence_l {ω T B z : M.Domain} (hw : M.IsOmega ω)
    (order : It_order_d ω T) (branch : It_branch_d ω T B) (hz : M.mem z B) :
    ∃ F, Fn0_d ω B F ∧ (∀ e, (∀ x, ¬ M.mem x e) → Rd_entry_d e z F) ∧
      (∀ i j x y, M.SuccessorOf j i → Rd_entry_d i x F → Rd_entry_d j y F → It_pred_d T x y) ∧
      ∀ i x, Rd_entry_d i x F → z = x ∨ M.mem z x := by
  have ord := hw.isOrdinal (ZF.modelsKP hZF)
  have next x (hx : M.mem x B) : ∃ y, M.mem y B ∧ M.mem x y := by
    obtain ⟨j, succ, hj⟩ := hw.1.2 x (branch.subset x hx)
    obtain ⟨y, hy, le⟩ := branch.cofinal j hj
    exact ⟨y, hy, le.elim (fun eq => eq ▸ succ.predecessor_mem)
      (fun h => (ord.mem (branch.subset y hy)).transitive j h x succ.predecessor_mem)⟩
  let ρ : Env M 1 := ⟨fun _ => B, fun _ => B⟩
  let φ : BinarySchema 1 := { body := set[3] ⟪⌜(.newest : Term 3)⌝ₛ ∈ ⌜(.bound 2 : Term 3)⌝ₛ ∧
    ⌜(.bound 1 : Term 3)⌝ₛ ∈ ⌜(.newest : Term 3)⌝ₛ ∧
    (∀ y ∈ ⌜(.bound 2 : Term 3)⌝ₛ, ⌜(.bound 1 : Term 3)⌝ₛ ∈ y → ⌜(.newest : Term 3)⌝ₛ ⊆ y)⟫ }
  have sat x y : φ.denote ρ x y ↔ M.mem y B ∧ M.mem x y ∧
      ∀ v, M.mem v B → M.mem x v → M.MemberSubset y v := by
    simp only [φ, BinarySchema.denote, Formula.satisfies_conj_iff, Formula.satisfies_mem_iff,
      Formula.satisfies_forallMem_iff, Formula.satisfies_imp_iff, Formula.satisfies_subset_iff]; rfl
  have least x (hx : M.mem x B) : ∃ y, φ.denote ρ x y := by
    let ψ : UnarySchema 1 := { body := .mem (.bound 1) .newest }
    let η : Env M 1 := ⟨fun _ => x, fun _ => x⟩
    obtain ⟨C, spec⟩ := ZF.separation_exists_d hZF ψ η B
    have read v : M.mem v C ↔ M.mem v B ∧ M.mem x v := spec v
    obtain ⟨y, hy, hxy⟩ := next x hx
    obtain ⟨v, hv, min⟩ := ord.wellOrder.least C (fun v h => branch.subset v ((read v).mp h).1)
      ⟨y, (read y).mpr ⟨hy, hxy⟩⟩
    refine ⟨v, (sat x v).mpr ⟨((read v).mp hv).1, ((read v).mp hv).2, fun w hw xw => ?_⟩⟩
    rcases min w ((read w).mpr ⟨hw, xw⟩) with eq | lt
    · exact fun a ha => (eq a).mp ha
    · exact (ord.mem (branch.subset w hw)).transitive v lt
  obtain ⟨G, gf, gs⟩ := ZF.exists_setFunctionFromTo_of_denote hZF I φ ρ least (by
    intro x _ y v hy hv
    obtain ⟨hy, xy, ly⟩ := (sat x y).mp hy
    obtain ⟨hv, xv, lv⟩ := (sat x v).mp hv
    exact hZF.1.eq_of_same_members y v (fun a => ⟨ly v hv xv a, lv y hy xy a⟩))
    (fun x y _ h => ((sat x y).mp h).1)
  obtain ⟨F, ff, first, steps⟩ := ZFC.iterate_l I hZF hw gf hz
  have step i j x y (succ : M.SuccessorOf j i) (hx : Rd_entry_d i x F) (hy : Rd_entry_d j y F) :=
    (sat x y).mp ((gs x y).mp (steps i j x y succ hx hy)).2
  have pred i j x y (succ : M.SuccessorOf j i) (hx : Rd_entry_d i x F) (hy : Rd_entry_d j y F) : It_pred_d T x y := by
    obtain ⟨hyB, xy, least⟩ := step i j x y succ hx hy
    obtain ⟨l, _, yl⟩ := hw.exists_predecessor_of_mem_of_nonempty hZF (branch.subset y hyB) ⟨x, xy⟩
    obtain ⟨k, pk⟩ := order.predecessor l y (branch.subset y hyB) yl
    have xyT := branch.forward_l order (ff.output_mem_of_pairMember hx) hyB (Or.inr xy)
    have xk := ((pk.2 x).mp xyT).elim (fun eq => (KP.mem_irrefl_d (ZF.modelsKP hZF) y (eq ▸ xy)).elim) id
    rcases order.forward x k xk with eq | xk
    · exact eq.symm ▸ pk
    · have ky := (pk.2 k).mpr (Or.inr (order.refl k (ord.transitive y (branch.subset y hyB) k pk.1)))
      exact (KP.mem_irrefl_d (ZF.modelsKP hZF) k (least k (branch.down k y ky hyB) xk k pk.1)).elim
  let η : Env M 0 := ⟨Fin.elim0, fun _ => F⟩
  let ψ : BinarySchema 0 := { body := .mem (.bound 1) .newest }
  have inc := ZF.rel_chain_l I hZF ψ η hw ff
    (fun x y z _ _ hz xy yz => (ord.mem (branch.subset z hz)).transitive y yz x xy)
    (fun i j x y succ hx hy => (step i j x y succ hx hy).2.1)
  obtain ⟨e, empty, he⟩ := hw.1.1
  refine ⟨F, fn0_of_function_l (ZF.modelsKP hZF) ff, first, pred, fun i x hx => ?_⟩
  rcases ord.wellOrder.linear.compare e he i (ff.input_mem_of_pairMember hx) with eq | lt | gt
  · have eq := hZF.1.eq_of_same_members e i eq
    exact Or.inl (ff.1.2 i z x (eq ▸ first e empty) hx)
  · exact Or.inr (inc e i z x lt (first e empty) hx)
  · exact (empty i gt).elim

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 相邻节点列精确枚举枝的整个尾段

内部成员归纳回溯真实树前驱；相同枝上同一个父节点的直接后继唯一。
因此相邻节点递归不会遗漏尾段中的非标准内部有限节点。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)
include hZF

theorem It_branch_d.child_unique_l {ω T B k x y : M.Domain} (order : It_order_d ω T)
    (branch : It_branch_d ω T B) (hx : M.mem x B) (hy : M.mem y B)
    (px : It_pred_d T k x) (py : It_pred_d T k y) : x = y := by
  have no a (ha : M.mem a ω) (ka : M.mem k a) (ak : Rd_entry_d a k T) : False := by
    rcases order.forward a k ak with eq | lt
    · exact KP.mem_irrefl_d (ZF.modelsKP hZF) a (eq.symm ▸ ka)
    · exact KP.mem_irrefl_d (ZF.modelsKP hZF) a ((order.ordinal.mem ha).transitive k ka a lt)
  rcases branch.chain x y hx hy with xy | yx
  · exact ((py.2 x).mp xy).elim id (fun h => (no x (branch.subset x hx) px.1 h).elim)
  · exact ((px.2 y).mp yx).elim Eq.symm (fun h => (no y (branch.subset y hy) py.1 h).elim)

theorem It_branch_d.successor_range_l {ω T B z F : M.Domain} (hw : M.IsOmega ω)
    (order : It_order_d ω T) (branch : It_branch_d ω T B) (hz : M.mem z B)
    (fn : Fn0_d ω B F) (first : ∀ e, (∀ x, ¬ M.mem x e) → Rd_entry_d e z F)
    (step : ∀ i j x y, M.SuccessorOf j i → Rd_entry_d i x F → Rd_entry_d j y F → It_pred_d T x y) :
    ∀ y, M.mem y B → (z = y ∨ M.mem z y) → ∃ i, Rd_entry_d i y F := by
  let ρ : Env M 3 := ⟨fun i => [B,z,F].get i,fun _ => F⟩
  let φ : UnarySchema 3 := { body := set[4] ⟪⌜(.newest : Term 4)⌝ₛ ∈ ⌜(.bound 1 : Term 4)⌝ₛ →
    (⌜(.bound 2 : Term 4)⌝ₛ = ⌜(.newest : Term 4)⌝ₛ ∨ ⌜(.bound 2 : Term 4)⌝ₛ ∈ ⌜(.newest : Term 4)⌝ₛ) →
    ∃ i, ⌜rd_entry0_m⌝ₚ(i,⌜(.newest : Term 4)⌝ₛ,⌜(.bound 3 : Term 4)⌝ₛ)⟫ }
  have sat y : φ.denote ρ y ↔ M.mem y B → (z = y ∨ M.mem z y) → ∃ i, Rd_entry_d i y F := by
    simp only [φ,UnarySchema.denote,Formula.satisfies_imp_iff,Formula.satisfies_mem_iff,
      Formula.satisfies_disj_iff,Formula.satisfies_extensionalEq_iff_eq hZF.1,
      Formula.satisfies_exists_iff,rd_entry0_sat_l hZF.1,Definitional.Term.eval_weaken]
    rfl
  intro y
  apply (sat y).mp (ZF.mem_ind_l M hZF I φ ρ ?_ y)
  intro y ih
  apply (sat y).mpr
  intro hy lower
  rcases lower with eq | zy
  · obtain ⟨e,empty,_⟩ := hw.1.1
    exact ⟨e,eq ▸ first e empty⟩
  · obtain ⟨n,_,succ⟩ := hw.exists_predecessor_of_mem_of_nonempty hZF (branch.subset y hy) ⟨z,zy⟩
    obtain ⟨k,pred⟩ := order.predecessor n y (branch.subset y hy) succ
    have hk := order.ordinal.transitive y (branch.subset y hy) k pred.1
    have kb := branch.down k y ((pred.2 k).mpr (Or.inr (order.refl k hk))) hy
    have zk : Rd_entry_d z k T := ((pred.2 z).mp (branch.forward_l order hz hy (Or.inr zy))).elim
      (fun eq => (KP.mem_irrefl_d (ZF.modelsKP hZF) y (eq ▸ zy)).elim) id
    obtain ⟨i,ik⟩ := (sat k).mp (ih k pred.1) kb (order.forward z k zk)
    obtain ⟨j,next,hj⟩ := hw.1.2 i (fn.bound_l ik).1
    obtain ⟨w,hw,iw⟩ := fn.2.1 j hj
    have eq := branch.child_unique_l hZF order hw hy (step i j k w next ik iw) pred
    exact ⟨j,eq ▸ iw⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 两条不同共尾枝最终分离

在任意给定有限界之后，另一条枝仍有不在当前枝中的节点。
档案的节点谓词只读实际行码的首坐标，不依赖余下记录的元数。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

def Tg_odd_node_d (H y : M.Domain) : Prop := ∃ n r t, Rd_entry_d n r H ∧ KPair_d M r y t
def Tg_odd_cofinal_d (ω b H : M.Domain) : Prop := ∀ i, M.mem i ω →
  ∃ j, M.mem j b ∧ (i = j ∨ M.mem i j) ∧ Tg_odd_node_d H j

theorem It_branch_d.separate_l (hE : Extensional M) {ω T B b α : M.Domain}
    (order : It_order_d ω T) (branch : It_branch_d ω T b) (other : It_branch_d ω T B)
    (ne : b ≠ B) (hα : M.mem α ω) : ∀ i, M.mem i ω →
      ∃ y, M.mem y b ∧ (i = y ∨ M.mem i y) ∧ ¬ M.mem y B ∧ ¬ M.mem y α := by
  classical
  have ord := order.ordinal
  have ir x hx := ord.wellOrder.linear.irrefl x hx
  have different : ∃ x, M.mem x b ∧ ¬ M.mem x B := by
    apply Classical.byContradiction
    intro no
    have sub x (hx : M.mem x b) : M.mem x B := Classical.byContradiction (fun h => no ⟨x,hx,h⟩)
    apply ne (hE.eq_of_same_members b B fun x => ⟨sub x,fun hx => ?_⟩)
    obtain ⟨y,hy,le⟩ := branch.cofinal x (other.subset x hx)
    exact branch.down x y (other.forward_l order hx (sub y hy) le) hy
  obtain ⟨x,hx,hxn⟩ := different
  have upper a d (ha : M.mem a ω) (hd : M.mem d ω) :
      ∃ z, M.mem z ω ∧ M.MemberSubset a z ∧ M.MemberSubset d z := by
    rcases ord.wellOrder.linear.compare a ha d hd with eq | lt | gt
    · exact ⟨d,hd,fun y hy => (eq y).mp hy,fun _ h => h⟩
    · exact ⟨d,hd,(ord.mem hd).transitive a lt,fun _ h => h⟩
    · exact ⟨a,ha,fun _ h => h,(ord.mem ha).transitive d gt⟩
  have le {a d} (ha : M.mem a ω) (hd : M.mem d ω) (sub : M.MemberSubset a d) : a = d ∨ M.mem a d := by
    rcases ord.wellOrder.linear.compare a ha d hd with eq | lt | gt
    · exact Or.inl (hE.eq_of_same_members a d eq)
    · exact Or.inr lt
    · exact (ir d hd (sub d gt)).elim
  intro i hi
  obtain ⟨z,hz,az,xz⟩ := upper α x hα (branch.subset x hx)
  obtain ⟨m,hm,zm,im⟩ := upper z i hz hi
  obtain ⟨y,hy,my⟩ := branch.cofinal m hm
  have hyω := branch.subset y hy
  have mysub : M.MemberSubset m y := my.elim (fun eq => eq ▸ fun _ h => h)
    (fun lt => (ord.mem hyω).transitive m lt)
  have iy := le hi hyω (fun a h => mysub a (im a h))
  have xy := le (branch.subset x hx) hyω (fun a h => mysub a (zm a (xz a h)))
  exact ⟨y,hy,iy,fun h => hxn (other.down x y (branch.forward_l order hx hy xy) h),
    fun h => ir y hyω (mysub y (zm y (az y h)))⟩

end YesMetaZFC.SetTheory.LargeCardinal
