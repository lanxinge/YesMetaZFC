import YesMetaZFC.SetTheory.LargeCardinal.Iteration.ActivityRead
import YesMetaZFC.SetTheory.LargeCardinal.Extender.RawCountable
import YesMetaZFC.SetTheory.LargeCardinal.Extender.RawCoherence
import YesMetaZFC.Model.SetTheory.DirectedSystem.Relative
import YesMetaZFC.SetTheory.LargeCardinal.Extender.SystemRead
import YesMetaZFC.SetTheory.LargeCardinal.Extender.Trace

/-! # 原迭代树核心及求值源证书

模型、嵌入和操作记录都是内部集合图。纯树核心保存实际后继与极限
条件，允许任意原关系模型上的恒等填充。需要原生求值和复制的执行树
另附完整源证书；背景数字图不再作为普通迭代树的隐含条件。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

def It_step_d (hZF : M.Models ZF) (ω T Q G E ξ η : M.Domain) : Prop := ∃ k c d b j p,
  It_pred_d T k η ∧ Rd_entry_d ξ c Q ∧ Rd_entry_d k d Q ∧ Rd_entry_d η b Q ∧
    It_map_d G k η j ∧ Rd_entry_d ξ p E ∧
    (((∀ x, ¬ M.mem x p) ∧ k = ξ ∧ b = c ∧ ∀ x y, Rd_entry_d x y j → x = y) ∨ It_active_d hZF ω c d b j p)

def It_limit_d (T Q G δ : M.Domain) : Prop := ∀ c X R,
  Rd_entry_d δ c Q → KPair_d M c X R → ∀ y, M.mem y X →
    ∃ i, M.mem i δ ∧ Rd_entry_d i δ T ∧ ∃ f, It_map_d G i δ f ∧ ∃ x, Rd_entry_d x y f

structure It_tree_core_d (hZF : M.Models ZF) (ω c₀ α T Q G E : M.Domain) : Prop where
  omega : M.IsOmega ω
  diagram : It_diagram_d (kp_pair_l (ZF.modelsKP hZF)) ω α T Q G
  root : ∀ z, (∀ x, ¬ M.mem x z) → Rd_entry_d z c₀ Q
  move_function : M.IsSetFunction (kp_pair_l (ZF.modelsKP hZF)) E
  move_domain : ∀ i, (∃ p, Rd_entry_d i p E) ↔ ∃ j, M.mem j α ∧ M.SuccessorOf j i
  steps : ∀ i j, M.mem j α → M.SuccessorOf j i → It_step_d hZF ω T Q G E i j
  limits : ∀ δ, M.mem δ α → M.IsLimitOrdinal δ → It_limit_d T Q G δ

/-- 原生求值和实际超幂构造所用的增强证书，不改变普通树的几何。 -/
structure It_tree_d (hZF : M.Models ZF) (ω c₀ α T Q G E : M.Domain) : Prop
    extends It_tree_core_d hZF ω c₀ α T Q G E where
  sources : ∀ i c, Rd_entry_d i c Q → It_source_d hZF ω c

def It_extension_d (α ξ k T Q G E β U Q' G' E' : M.Domain) : Prop := M.SuccessorOf β α ∧
  (∀ i l, Rd_entry_d i l U ↔ Rd_entry_d i l T ∨ l = α ∧ (i = α ∨ Rd_entry_d i k T)) ∧
  (∀ i a, Rd_entry_d i a Q → Rd_entry_d i a Q') ∧
  (∀ i l f, M.mem l α → (It_map_d G' i l f ↔ It_map_d G i l f)) ∧
  (∀ i a, Rd_entry_d i a E → Rd_entry_d i a E') ∧
  (∀ i a, i ≠ ξ → (Rd_entry_d i a E' ↔ Rd_entry_d i a E))



/-- 每个已有操作只有原树定义中的空操作或真实扩展器两种情形。 -/
theorem It_tree_d.move_cases_l (hZF : M.Models ZF) {ω c α T Q G E i p : M.Domain}
    (tree : It_tree_d hZF ω c α T Q G E) (hp : Rd_entry_d i p E) :
    (∀ x, ¬ M.mem x p) ∨ ∃ κ ρ F, It_payload_d p κ ρ F := by
  obtain ⟨j, hj, succ⟩ := (tree.move_domain i).mp ⟨p, hp⟩
  obtain ⟨_, _, _, _, _, q, _, _, _, _, _, hq, step⟩ := tree.steps i j hj succ
  have eq := tree.move_function.2 i q p hq hp
  subst q
  rcases step with ⟨empty, _⟩ | ⟨κ, ρ, F, _, _, _, _, pay, _⟩
  · exact Or.inl empty
  · exact Or.inr ⟨κ, ρ, F, pay⟩

variable (hKP : M.Models KP)
local notation "I" => kp_pair_l hKP

/-- 操作列添加一项，已有图条目精确保留。 -/
theorem it_move_push_l {E ξ p : M.Domain} (hf : M.IsSetFunction I E)
    (fresh : ∀ x, ¬ Rd_entry_d ξ x E) : ∃ E', M.IsSetFunction I E' ∧
      ∀ i x, Rd_entry_d i x E' ↔ Rd_entry_d i x E ∨ i = ξ ∧ x = p := by
  obtain ⟨r, hr⟩ := (I).total ξ p
  obtain ⟨B, hb⟩ := KP.exists_singleton hKP r
  obtain ⟨E', he⟩ := KP.exists_unionOfTwo hKP E B
  have read i x : Rd_entry_d i x E' ↔ Rd_entry_d i x E ∨ i = ξ ∧ x = p := by
    constructor
    · rintro ⟨s, hs, hsE⟩
      rcases (he s).mp hsE with hsE | hsB
      · exact Or.inl ⟨s, hs, hsE⟩
      · exact Or.inr (kpair_injective_l M hs (((hb s).mp hsB).symm ▸ hr))
    · rintro (⟨s, hs, hsE⟩ | ⟨rfl, rfl⟩)
      · exact ⟨s, hs, (he s).mpr (Or.inl hsE)⟩
      · exact ⟨r, hr, (he r).mpr (Or.inr ((hb r).mpr rfl))⟩
  refine ⟨E', ⟨fun s hs => ?_, fun i x y hx hy => ?_⟩, read⟩
  · rcases (he s).mp hs with hs | hs
    · exact hf.1 s hs
    · exact ⟨ξ, p, ((hb s).mp hs).symm ▸ hr⟩
  · rcases (read i x).mp hx with hx | ⟨rfl, rfl⟩
    · rcases (read i y).mp hy with hy | ⟨rfl, _⟩
      · exact hf.2 i x y hx hy
      · exact (fresh x hx).elim
    · rcases (read _ y).mp hy with hy | ⟨_, eq⟩
      · exact (fresh y hy).elim
      · exact eq.symm

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 可数根的 ω 长迭代树全部模型可数

内部归纳同时保留所有较早结点的计数界。活动步只读取原树指定的超幂，
支撑码属于所属载体，函数码属于指定前驱；padding 保留原模型。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem it_countable_l {ω c₀ T Q G E X₀ R₀ : M.Domain}
    (tree : It_tree_d hZF ω c₀ ω T Q G E) (mx : Smdl_d I c₀ X₀ R₀) (cx : M.CardinalLessOrEqual I X₀ ω) :
    ∀ i c X R, Rd_entry_d i c Q → KPair_d M c X R → M.CardinalLessOrEqual I X ω := by
  let φ : UnarySchema 2 := { body := set[3] ⟪∀ i, (i = ⌜(Term.newest : Term 3)⌝ₛ ∨ i ∈ ⌜(Term.newest : Term 3)⌝ₛ) →
    ∀ c X R, ⌜rd_entry0_m⌝ₚ(i, c, ⌜(Term.bound 1 : Term 3)⌝ₛ) → ⌜kpair_m⌝ₚ(c, X, R) →
      ∃ f, ⌜Formula.isInjectionFromTo kpair_convention_l⌝ₚ(f, X, ⌜(Term.bound 2 : Term 3)⌝ₛ)⟫ }
  let ρ : Env M 2 := ⟨Fin.cases Q (fun _ => ω), fun _ => ω⟩
  have sat n : φ.denote ρ n ↔ ∀ i, i = n ∨ M.mem i n →
      ∀ c X R, Rd_entry_d i c Q → KPair_d M c X R → M.CardinalLessOrEqual I X ω := by
    simp only [φ, UnarySchema.denote, Formula.satisfies_forall_iff, Formula.satisfies_imp_iff,
      Formula.satisfies_disj_iff, Formula.satisfies_extensionalEq_iff_eq hZF.1, Formula.satisfies_mem_iff,
      rd_entry0_sat_l hZF.1, kpair_sat_l M hZF.1, Formula.satisfies_exists_iff,
      Formula.satisfies_isInjectionFromTo_iff I hZF.1, Definitional.Term.eval_weaken]; rfl
  have all : ∀ n, M.mem n ω → φ.denote ρ n := by
    apply tree.omega.induction (fun n => φ.denote ρ n) (ZF.separation_exists_d hZF φ ρ ω)
    · intro z hz
      apply (sat z).mpr
      intro i hi c X R hc hp
      rcases hi with eq | hi
      · subst i
        have ec := tree.diagram.model_function.2 z c c₀ hc (tree.root z hz)
        obtain ⟨ex, _⟩ := kpair_injective_l M (ec ▸ hp) mx.1
        exact ex.symm ▸ cx
      · exact (hz i hi).elim
    · intro n hn ih m hm
      have hmω : M.mem m ω := by
        obtain ⟨m', hm', hm'ω⟩ := tree.omega.1.2 n hn
        exact Structure.SuccessorOf.eq hZF.1 hm' hm ▸ hm'ω
      have old i (hi : M.mem i m) := (sat n).mp ih i (((hm i).mp hi).elim Or.inr
        (fun eq => Or.inl (hZF.1.eq_of_same_members i n eq)))
      apply (sat m).mpr
      intro i hi c X R hc hp
      rcases hi with eq | hi
      · subst i
        obtain ⟨k, a, d, b, f, p, pred, ha, hd, hb, _, _, step⟩ := tree.steps n m hmω hm
        have ec := tree.diagram.model_function.2 m b c hb hc
        subst b
        rcases step with ⟨_, _, same, _⟩ | edge
        · exact (sat n).mp ih n (Or.inl rfl) a X R ha (same ▸ hp)
        · obtain ⟨N, S, mn⟩ := tree.diagram.models n a ha
          obtain ⟨Y, V, my⟩ := tree.diagram.models k d hd
          obtain ⟨X', R', mt⟩ := tree.diagram.models m c hc
          obtain ⟨ex, er⟩ := kpair_injective_l M mt.1 hp
          subst X' R'
          exact edge.countable_l hZF tree.omega ((sat n).mp ih n (Or.inl rfl) a N S ha mn.1)
            (old k pred.1 d Y V hd my.1) mn my mt
      · exact old i hi c X R hc hp
  exact fun i c X R hc hp => (sat i).mp (all i ((tree.diagram.model_domain i).mpr ⟨c, hc⟩)) i (Or.inl rfl) c X R hc hp

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 整棵 ω 树的模型列与全初等嵌入列回拉

自然数及其关系图保持原值。每个模型沿拥有集合上的实际限制回拉完整源；
每条边由两端限制的交换三角形恢复全内部初等性。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem it_diagram_pull_l {ω B R b K U S u J C V π T Q G T' Q' G' : M.Domain}
    (source : Ep_source_d (kp_pair_l (ZF.modelsKP hZF)) ω ω K B R) (target : Ep_source_d (kp_pair_l (ZF.modelsKP hZF)) ω ω J U S)
    (mb : Smem_d I b B R) (mu : Smem_d I u U S) (hj : Smap_d I ω b u B U π)
    (hC : M.mem C B) (ct : M.TransitiveSet C) (vt : M.TransitiveSet V)
    (hCV : Rd_entry_d C V π) (hQ : M.mem Q C) (hG : M.mem G C)
    (hTT : Rd_entry_d T T' π) (hQQ : Rd_entry_d Q Q' π) (hGG : Rd_entry_d G G' π)
    (diagram : It_diagram_d (kp_pair_l (ZF.modelsKP hZF)) ω ω T' Q' G')
    (sources : ∀ i c, Rd_entry_d i c Q' → It_source_d hZF ω c) :
    T = T' ∧ It_diagram_d (kp_pair_l (ZF.modelsKP hZF)) ω ω T Q G ∧ ∀ i c, Rd_entry_d i c Q → It_source_d hZF ω c := by
  have hw := source.omega
  have nat := hj.natural_l hZF hw source.transitive target.transitive mb mu source.omega_mem
  have omega := hj.omega_l I hZF hw source.transitive target.transitive mb mu source.omega_mem
  have same := hj.relation_preimage_l hZF hw source.transitive target.transitive mb mu omega nat hTT
    ⟨diagram.order.relation, diagram.order.bound⟩
  subst T'
  have ownQ := (hj.member_l I hZF hw mb mu hQQ hCV).mp hQ
  have ownG := (hj.member_l I hZF hw mb mu hGG hCV).mp hG
  have qf : Fn0_d ω C Q := (hj.function_l hZF hw source.transitive target.transitive mb mu omega hCV hQQ).mpr
    (fn0_of_function_l (ZF.modelsKP hZF) ⟨diagram.model_function, diagram.model_domain, fun i hi => by
      obtain ⟨a, ha⟩ := (diagram.model_domain i).mp hi
      exact ⟨a, (rd_entry_transitive_l vt ownQ ha).2, ha⟩⟩)
  have gf : Fn0_d T C G := (hj.function_l hZF hw source.transitive target.transitive mb mu hTT hCV hGG).mpr
    (fn0_of_function_l (ZF.modelsKP hZF) ⟨diagram.map_function, diagram.map_domain, fun i hi => by
      obtain ⟨a, ha⟩ := (diagram.map_domain i).mp hi
      exact ⟨a, (rd_entry_transitive_l vt ownG ha).2, ha⟩⟩)
  have model {i a} (ha : Rd_entry_d i a Q) : ∃ a' X P Y W,
      Rd_entry_d i a' Q' ∧ Rd_entry_d a a' π ∧ Smdl_d I a X P ∧ It_source_d hZF ω a ∧
      Smdl_d I a' Y W ∧ Rd_entry_d X Y π ∧ Rd_entry_d P W π := by
    obtain ⟨a', _, haa⟩ := hj.1.1.2.2 a (source.transitive C hC a (qf.bound_l ha).2)
    have hi := (hj.entry_l hZF hw source.transitive target.transitive mb mu (nat i (qf.bound_l ha).1) haa hQQ).mp ha
    have child := sources i a' hi
    obtain ⟨Y, W, _, _, _, my, _⟩ := child.objects
    obtain ⟨X, P, mx, hXY, hPW⟩ := ep_set_model_pull_l hZF hw source.transitive target.transitive mb mu hj haa my
    obtain ⟨σ, _, hs⟩ := ep_set_restriction_l hZF source target mb mu hj mx my hXY hPW
    exact ⟨a', X, P, Y, W, hi, haa, mx, child.pull_l hZF mx my hs, my, hXY, hPW⟩
  have ready i a (ha : Rd_entry_d i a Q) : It_source_d hZF ω a := by
    obtain ⟨_, _, _, _, _, _, _, _, h, _⟩ := model ha
    exact h
  have edge {i j f} (hf : It_map_d G i j f) : ∃ g, It_map_d G' i j g ∧ Rd_entry_d f g π := by
    obtain ⟨r, pair, hr⟩ := hf
    have rt := (gf.bound_l hr).1
    have ij := diagram.order.bound i j ⟨r, pair, rt⟩
    have fixed := hj.fixed_pair_l hZF hw source.transitive target.transitive mb mu
      (source.transitive T (hj.1.1.input_mem_of_pairMember hTT) r rt) pair (nat i ij.1) (nat j ij.2)
    obtain ⟨g, _, hfg⟩ := hj.1.1.2.2 f (source.transitive C hC f (gf.bound_l hr).2)
    exact ⟨g, ⟨r, pair, (hj.entry_l hZF hw source.transitive target.transitive mb mu fixed hfg hGG).mp hr⟩, hfg⟩
  have owned {i j f} (hf : It_map_d G i j f) : M.mem f C := hf.elim fun _ h => (gf.bound_l h.2).2
  have value {i j f x y} (hf : It_map_d G i j f) (hxy : Rd_entry_d x y f) : M.mem x B ∧ M.mem y B := by
    have xy := rd_entry_transitive_l ct (owned hf) hxy
    exact ⟨source.transitive C hC x xy.1, source.transitive C hC y xy.2⟩
  refine ⟨rfl, ⟨diagram.order, (fn0_function_l (ZF.modelsKP hZF) qf).1,
    (fn0_function_l (ZF.modelsKP hZF) qf).2.1, ?_, (fn0_function_l (ZF.modelsKP hZF) gf).1,
    (fn0_function_l (ZF.modelsKP hZF) gf).2.1, ?_, ?_, ?_⟩, ready⟩
  · intro i a ha
    obtain ⟨X, P, _, _, _, mx, _⟩ := (ready i a ha).objects
    exact ⟨X, P, mx⟩
  · intro i j f a X P d Y W hf ha hd mx my
    obtain ⟨a', X₀, P₀, X', P', ha', _, ma, _, ma', hXX, hPP⟩ := model ha
    obtain ⟨d', Y₀, W₀, Y', W', hd', _, md, _, md', hYY, hWW⟩ := model hd
    obtain ⟨rfl, rfl⟩ := smdl_unique_l I ma mx
    obtain ⟨rfl, rfl⟩ := smdl_unique_l I md my
    obtain ⟨g, hg, hfg⟩ := edge hf
    exact ep_set_map_pull_l hZF source target mb mu hj ma ma' md md' hXX hPP hYY hWW hfg
      (diagram.elementary i j g a' X' P' d' Y' W' hg ha' hd' ma' md')
  · intro i f hf x y hxy
    obtain ⟨g, hg, hfg⟩ := edge hf
    obtain ⟨x', _, hx⟩ := hj.1.1.2.2 x (value hf hxy).1
    obtain ⟨y', _, hy⟩ := hj.1.1.2.2 y (value hf hxy).2
    have eq := diagram.identity i g hg x' y'
      ((hj.entry_l hZF hw source.transitive target.transitive mb mu hx hy hfg).mp hxy)
    exact hj.1.2 x y y' (eq ▸ hx) hy
  · intro i j k f g h hf hg hh x y z hxy hyz
    obtain ⟨f', hf', ff⟩ := edge hf
    obtain ⟨g', hg', gg⟩ := edge hg
    obtain ⟨h', hh', hh⟩ := edge hh
    obtain ⟨x', _, hx⟩ := hj.1.1.2.2 x (value hf hxy).1
    obtain ⟨y', _, hy⟩ := hj.1.1.2.2 y (value hf hxy).2
    obtain ⟨z', _, hz⟩ := hj.1.1.2.2 z (value hg hyz).2
    exact (hj.entry_l hZF hw source.transitive target.transitive mb mu hx hz hh).mpr
      (diagram.comp i j k f' g' h' hf' hg' hh' x' y' z'
        ((hj.entry_l hZF hw source.transitive target.transitive mb mu hx hy ff).mp hxy)
        ((hj.entry_l hZF hw source.transitive target.transitive mb mu hy hz gg).mp hyz))

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 树的极限条件给出实际直接极限证书

把各前驱模型通过已存嵌入识别为目标中的像。带指标的这些像组成实际
定向系统，其取值图覆盖目标；一般相容锥定理于是识别同一个目标为直接极限。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

def It_image_d (G i δ y : M.Domain) : Prop := ∃ f, It_map_d G i δ f ∧ ∃ x, Rd_entry_d x y f
def it_image_m {d} (G i δ y : Term d) : Formula 1 d := .existsE
  (.conj (it_map_m G.weaken i.weaken δ.weaken .newest) (.existsE (rd_entry_m .newest y.weaken.weaken (.bound 1))))
derive_free_closed it_image_m

theorem it_image_sat_l (hE : Extensional M) {d} (ρ : Env M d) (G i δ y : Term d) :
    Formula.satisfies ρ (it_image_m G i δ y) ↔ It_image_d (G.eval ρ) (i.eval ρ) (δ.eval ρ) (y.eval ρ) := by
  simp only [it_image_m, It_image_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    it_map_sat_l hE, rd_entry_sat_l hE, Definitional.Term.eval_weaken]; rfl

theorem it_branch_limit_l (hZF : M.Models ZF) {ω α T Q G δ : M.Domain}
    (h : It_diagram_d (kp_pair_l (ZF.modelsKP hZF)) ω α T Q G) (hδ : M.mem δ α) (cover : It_limit_d T Q G δ) :
    ∃ c Y V J L A p B R e, Rd_entry_d δ c Q ∧ Smdl_d (kp_pair_l (ZF.modelsKP hZF)) c Y V ∧
      Di_system_d J L A p B R ∧ Di_limit_d A p B R e Y V ∧
      (∀ i, M.mem i J ↔ M.mem i δ ∧ Rd_entry_d i δ T) ∧
      (∀ i j, Rd_entry_d i j L ↔ M.mem i J ∧ M.mem j J ∧ Rd_entry_d i j T) ∧
      (∀ a, M.mem a A ↔ ∃ i, M.mem i J ∧ ∃ y, M.mem y Y ∧ KPair_d M a i y ∧ It_image_d G i δ y) ∧
      (∀ a i y, Rd_entry_d a i p → Rd_entry_d a y e → KPair_d M a i y) := by
  let I := kp_pair_l (ZF.modelsKP hZF)
  obtain ⟨c, Y, V, hc, model⟩ := h.model_l hZF hδ
  let φ : UnarySchema 2 := { body := rd_entry_m .newest (.bound 1) (.bound 2) }
  obtain ⟨J, js⟩ := ZF.separation_exists_d hZF φ ⟨Fin.cases δ (fun _ => T), fun _ => δ⟩ δ
  have index i : M.mem i J ↔ M.mem i δ ∧ Rd_entry_d i δ T :=
    (js i).trans (and_congr_right fun _ => rd_entry_sat_l hZF.1 ..)
  have inside i (hi : M.mem i J) := h.order.ordinal.transitive δ hδ i ((index i).mp hi).1
  let ψ : BinarySchema 1 := { body := rd_entry_m (.bound 1) .newest (.bound 2) }
  obtain ⟨L, _, ls⟩ := ZF.exists_setRelationOn_of_denote hZF I ψ ⟨fun _ => T, fun _ => T⟩ J
  have order i j : Rd_entry_d i j L ↔ M.mem i J ∧ M.mem j J ∧ Rd_entry_d i j T :=
    (ls i j).trans (and_congr_right fun _ => and_congr_right fun _ => rd_entry_sat_l hZF.1 ..)
  have directed : Di_order_d J L := ⟨fun i hi => (order i i).mpr ⟨hi, hi, h.order.refl i (inside i hi)⟩,
    fun i j k hij hjk => (order i k).mpr ⟨((order i j).mp hij).1, ((order j k).mp hjk).2.1,
      h.order.trans i j k ((order i j).mp hij).2.2 ((order j k).mp hjk).2.2⟩,
    fun i j hij => ⟨((order i j).mp hij).1, ((order i j).mp hij).2.1⟩, fun i j hi hj => by
      rcases h.order.chain i j δ ((index i).mp hi).2 ((index j).mp hj).2 with hij | hji
      · exact ⟨j, hj, (order i j).mpr ⟨hi, hj, hij⟩, (order j j).mpr ⟨hj, hj, h.order.refl j (inside j hj)⟩⟩
      · exact ⟨i, hi, (order i i).mpr ⟨hi, hi, h.order.refl i (inside i hi)⟩, (order j i).mpr ⟨hj, hi, hji⟩⟩⟩
  have mono i j (hij : Rd_entry_d i j L) y (hy : It_image_d G i δ y) : It_image_d G j δ y := by
    obtain ⟨hi, hj, hij⟩ := (order i j).mp hij
    obtain ⟨f, hf, x, hxy⟩ := hy
    obtain ⟨g, hg⟩ := h.map_l hZF hij
    obtain ⟨k, hk⟩ := h.map_l hZF ((index j).mp hj).2
    obtain ⟨b, X, R, hb, mx⟩ := h.model_l hZF (inside i hi)
    obtain ⟨d, Z, S, hd, mz⟩ := h.model_l hZF (inside j hj)
    have ff := h.elementary i δ f b X R c Y V hf hb hc mx model
    have gg := h.elementary i j g b X R d Z S hg hb hd mx mz
    have kk := h.elementary j δ k d Z S c Y V hk hd hc mz model
    obtain ⟨z, hz, hxz⟩ := gg.1.1.2.2 x (ff.1.1.input_mem_of_pairMember hxy)
    obtain ⟨y', _, hzy⟩ := kk.1.1.2.2 z hz
    exact ⟨k, hk, z, ff.1.1.1.2 x y' y (h.comp i j δ g k f hg hk hf x z y' hxz hzy) hxy ▸ hzy⟩
  obtain ⟨D, hd⟩ := ZF.exists_cartesianProduct hZF I J Y
  let ρ : Env M 4 := ⟨Fin.cases J (Fin.cases Y (Fin.cases G (fun _ => δ))), fun _ => δ⟩
  let θ : UnarySchema 4 := {
    body := Formula.existsMem (.bound 1) (Formula.existsMem (.bound 3)
      (.conj (kpair_m (.bound 2) (.bound 1) .newest) (it_image_m (.bound 5) (.bound 1) (.bound 6) .newest))) }
  obtain ⟨A, as⟩ := ZF.separation_exists_d hZF θ ρ D
  have nodes a : M.mem a A ↔ ∃ i, M.mem i J ∧ ∃ y, M.mem y Y ∧ KPair_d M a i y ∧ It_image_d G i δ y := by
    have sat : θ.denote ρ a ↔ ∃ i, M.mem i J ∧ ∃ y, M.mem y Y ∧ KPair_d M a i y ∧ It_image_d G i δ y := by
      simp only [θ, UnarySchema.denote, Formula.satisfies_existsMem_iff, Formula.satisfies_conj_iff,
        kpair_sat_l M hZF.1, it_image_sat_l hZF.1]; rfl
    exact (as a).trans ((and_congr_right fun _ => sat).trans ⟨And.right,
      fun ⟨i, hi, y, hy, hp, image⟩ => ⟨(hd a).mpr ⟨i, hi, y, hy, hp⟩, i, hi, y, hy, hp, image⟩⟩)
  let first : BinarySchema 0 := { body := .existsE (kpair_m (.bound 2) (.bound 1) .newest) }
  let second : BinarySchema 0 := { body := .existsE (kpair_m (.bound 2) .newest (.bound 1)) }
  let η : Env M 0 := ⟨Fin.elim0, fun _ => Y⟩
  have fval a i : first.denote η a i ↔ ∃ y, KPair_d M a i y := by
    simp only [first, BinarySchema.denote, Formula.satisfies_exists_iff, kpair_sat_l M hZF.1]; rfl
  have sval a y : second.denote η a y ↔ ∃ i, KPair_d M a i y := by
    simp only [second, BinarySchema.denote, Formula.satisfies_exists_iff, kpair_sat_l M hZF.1]; rfl
  obtain ⟨p, hp, ps⟩ := ZF.exists_setFunctionFromTo_of_denote hZF I first η (source := A) (target := J)
    (fun a ha => by obtain ⟨i, _, y, _, pair, _⟩ := (nodes a).mp ha; exact ⟨i, (fval a i).mpr ⟨y, pair⟩⟩)
    (fun a _ i j hi hj => by
      obtain ⟨x, hx⟩ := (fval a i).mp hi
      obtain ⟨y, hy⟩ := (fval a j).mp hj
      exact (kpair_injective_l M hx hy).1)
    (fun a i ha hi => by
      obtain ⟨j, hj, y, _, pair, _⟩ := (nodes a).mp ha
      obtain ⟨x, pair'⟩ := (fval a i).mp hi
      exact (kpair_injective_l M pair pair').1 ▸ hj)
  obtain ⟨e, he, es⟩ := ZF.exists_setFunctionFromTo_of_denote hZF I second η (source := A) (target := Y)
    (fun a ha => by obtain ⟨i, _, y, _, pair, _⟩ := (nodes a).mp ha; exact ⟨y, (sval a y).mpr ⟨i, pair⟩⟩)
    (fun a _ x y hx hy => by
      obtain ⟨i, hi⟩ := (sval a x).mp hx
      obtain ⟨j, hj⟩ := (sval a y).mp hy
      exact (kpair_injective_l M hi hj).2)
    (fun a y ha hy => by
      obtain ⟨i, _, x, hx, pair, _⟩ := (nodes a).mp ha
      obtain ⟨j, pair'⟩ := (sval a y).mp hy
      exact (kpair_injective_l M pair pair').2 ▸ hx)
  have read a i y (hai : Rd_entry_d a i p) (hay : Rd_entry_d a y e) : KPair_d M a i y := by
    obtain ⟨x, hx⟩ := (fval a i).mp ((ps a i).mp hai).2
    obtain ⟨j, hj⟩ := (sval a y).mp ((es a y).mp hay).2
    exact (kpair_injective_l M hx hj).2 ▸ hx
  have node i y (hi : M.mem i J) (hy : M.mem y Y) (image : It_image_d G i δ y) : ∃ a, Rd_entry_d a i p ∧ Rd_entry_d a y e := by
    obtain ⟨a, pair⟩ := I.total i y
    have ha := (nodes a).mpr ⟨i, hi, y, hy, pair, image⟩
    exact ⟨a, (ps a i).mpr ⟨ha, (fval a i).mpr ⟨y, pair⟩⟩, (es a y).mpr ⟨ha, (sval a y).mpr ⟨i, pair⟩⟩⟩
  have value a i y (hai : Rd_entry_d a i p) (hay : Rd_entry_d a y e) : It_image_d G i δ y := by
    obtain ⟨j, _, x, _, pair, image⟩ := (nodes a).mp (hp.input_mem_of_pairMember hai)
    obtain ⟨rfl, rfl⟩ := kpair_injective_l M pair (read a i y hai hay)
    exact image
  obtain ⟨B, R, system, bs, rs⟩ := di_cone_system_l (V := V) hZF directed
    (fn0_of_function_l (ZF.modelsKP hZF) hp) (fn0_of_function_l (ZF.modelsKP hZF) he)
    (fun a b i y ha hb hay hby => kpair_unique_l M hZF.1 (read a i y ha hay) (read b i y hb hby))
    (fun a i j y hai hij hay => node j y ((order i j).mp hij).2.1 (he.output_mem_of_pairMember hay)
      (mono i j hij y (value a i y hai hay)))
  have range y : M.mem y Y ↔ ∃ a, Rd_entry_d a y e := by
    constructor
    · intro hy
      obtain ⟨i, hi, hiδ, f, hf, x, hxy⟩ := cover c Y V hc model.1 y hy
      obtain ⟨a, _, hay⟩ := node i y ((index i).mpr ⟨hi, hiδ⟩) hy ⟨f, hf, x, hxy⟩
      exact ⟨a, hay⟩
    · exact fun ⟨_, hay⟩ => he.output_mem_of_pairMember hay
  exact ⟨c, Y, V, J, L, A, p, B, R, e, hc, model, system,
    di_cone_limit_l system (fn0_of_function_l (ZF.modelsKP hZF) he) range bs rs model.2.2.2 model.2.2.1,
    index, order, nodes, read⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 原实际超幂边的一阶编码

编码保留全部源分量、直接极限、坍塌和常值方块；满足关系解码回原边证书。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

def ea_agree_m {d} (ω κ X Y : Term d) : Formula 1 d := set[d] ⟪
  ∀ n D A, n ∈ ⌜ω⌝ₛ → ⌜ep_space_m⌝ₚ(⌜κ⌝ₛ, n, D) → A ⊆ D → (A ∈ ⌜X⌝ₛ ↔ A ∈ ⌜Y⌝ₛ)⟫
derive_free_closed ea_agree_m
theorem ea_agree_sat_l (hE : Extensional M) {d} (η : Env M d) (ω κ X Y : Term d) :
    Formula.satisfies η (ea_agree_m ω κ X Y) ↔ Ea_agree_d (ω.eval η) (κ.eval η) (X.eval η) (Y.eval η) := by
  simp only [ea_agree_m, Ea_agree_d, Formula.satisfies_forall_iff, Formula.satisfies_imp_iff,
    Formula.satisfies_iff_iff, Formula.satisfies_mem_iff, Formula.satisfies_subset_iff,
    ep_space_sat_l hE, Definitional.Term.eval_weaken]; rfl

def ep_constants_m {d} (X q i : Term d) : Formula 1 d := set[d] ⟪
  ∀ x E, ⌜rd_entry0_m⌝ₚ(x, E, ⌜i⌝ₛ) → ∃ u a B f D, D ∈ ⌜X⌝ₛ ∧ ⌜sfun_m⌝ₚ(⌜X⌝ₛ, D, f) ∧
    ⌜rs_const_m⌝ₚ(D, x, f) ∧ f ∈ B ∧ ⌜kpair0_m⌝ₚ(u, a, B) ∧ ⌜rd_entry0_m⌝ₚ(u, E, ⌜q⌝ₛ)⟫
derive_free_closed ep_constants_m

theorem ep_constants_sat_l (hE : Extensional M) {d} (η : Env M d) (X q i : Term d) :
    Formula.satisfies η (ep_constants_m X q i) ↔ Ep_constants_d (X.eval η) (q.eval η) (i.eval η) := by
  simp only [ep_constants_m, Ep_constants_d, Formula.satisfies_forall_iff, Formula.satisfies_imp_iff,
    Formula.satisfies_exists_iff, Formula.satisfies_conj_iff, Formula.satisfies_mem_iff,
    rd_entry0_sat_l hE, sfun_sat_l hE, rs_const_sat_l hE, kpair0_sat_l hE, Definitional.Term.eval_weaken]; rfl

def it_ultra_m {d} (ω κ L F c d' j : Term d) : Formula 1 d := set[d] ⟪
  ∃ X R Y S J O Z A p T V q b C W i e,
    ⌜smem_m (𝒞 := kpair_convention_l)⌝ₚ(⌜c⌝ₛ, X, R) ∧ ⌜smem_m (𝒞 := kpair_convention_l)⌝ₚ(⌜d'⌝ₛ, Y, S) ∧
    ⌜ep_system_m⌝ₚ(⌜ω⌝ₛ, ⌜κ⌝ₛ, ⌜L⌝ₛ, X, R, ⌜F⌝ₛ, J, O, Z, A, p, T, V) ∧
    ⌜di_limit_m⌝ₚ(A, p, T, V, q, C, W) ∧ ⌜smdl_m (𝒞 := kpair_convention_l)⌝ₚ(b, C, W) ∧
    ⌜wc_graph_m⌝ₚ(C, W, e) ∧ ⌜Formula.isBijectionFromTo kpair_convention_l⌝ₚ(e, C, Y) ∧
    ⌜smap_m (𝒞 := kpair_convention_l)⌝ₚ(⌜ω⌝ₛ, b, ⌜d'⌝ₛ, C, Y, e) ∧
    ⌜smap_m (𝒞 := kpair_convention_l)⌝ₚ(⌜ω⌝ₛ, ⌜c⌝ₛ, b, X, C, i) ∧ ⌜ep_constants_m⌝ₚ(X, q, i) ∧
    ⌜smap_m (𝒞 := kpair_convention_l)⌝ₚ(⌜ω⌝ₛ, ⌜c⌝ₛ, ⌜d'⌝ₛ, X, Y, ⌜j⌝ₛ) ∧ ⌜it_comp_m⌝ₚ(i, e, ⌜j⌝ₛ)⟫
derive_free_closed it_ultra_m

theorem it_ultra_sat_l (J : kpair_convention_l.Interpretation M) (hE : Extensional M) {d} (η : Env M d) (ω κ L F c d' j : Term d) :
    Formula.satisfies η (it_ultra_m ω κ L F c d' j) ↔
      It_ultra_d J (ω.eval η) (κ.eval η) (L.eval η) (F.eval η) (c.eval η) (d'.eval η) (j.eval η) := by
  simp only [it_ultra_m, It_ultra_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    smem_sat_l J, smdl_sat_l J, ep_system_sat_l J hE, di_limit_sat_l hE, wc_graph_sat_l hE,
    Formula.satisfies_isBijectionFromTo_iff J hE, smap_sat_l J hE, ep_constants_sat_l hE,
    it_comp_sat_l hE, Definitional.Term.eval_weaken]; rfl

def it_source_m {d} (ω c : Term d) : Formula 1 d := set[d] ⟪
  ⌜Formula.isOmega⌝ₚ(⌜ω⌝ₛ) ∧ (∃ X R w K z,
    ⌜smdl_m (𝒞 := kpair_convention_l)⌝ₚ(⌜c⌝ₛ, X, R) ∧
    ⌜er_source_m⌝ₚ(⌜ω⌝ₛ, w, w, K, X, R) ∧ ⌜rr_layer_m⌝ₚ(⌜ω⌝ₛ, X, R, w, z))⟫
derive_free_closed it_source_m

theorem it_source_sat_l {d} (η : Env M d) (ω c : Term d) :
    Formula.satisfies η (it_source_m ω c) ↔ It_source_d hZF (ω.eval η) (c.eval η) := by
  simp only [it_source_m, Formula.satisfies_conj_iff, Formula.satisfies_isOmega_iff,
    Formula.satisfies_exists_iff, smdl_sat_l I, er_source_sat_l I hZF.1, rr_layer_sat_l I hZF.1,
    Definitional.Term.eval_weaken, Definitional.Term.eval_newest]
  exact ⟨fun ⟨hw, h⟩ => ⟨hw, h⟩, fun h => ⟨h.omega, h.objects⟩⟩

end YesMetaZFC.SetTheory.LargeCardinal
