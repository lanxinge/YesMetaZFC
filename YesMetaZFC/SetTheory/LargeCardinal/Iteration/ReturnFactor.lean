import YesMetaZFC.SetTheory.LargeCardinal.Iteration.Branch
import YesMetaZFC.SetTheory.OrdinalChoice
import YesMetaZFC.SetTheory.IndexedIteration
import YesMetaZFC.SetTheory.RelationChain
import YesMetaZFC.SetTheory.Card.Cofinality.Basic
import YesMetaZFC.SetTheory.LargeCardinal.Iteration.BranchTail
import YesMetaZFC.Model.SetTheory.DirectedSystem.ElementaryFactor
import YesMetaZFC.Model.SetTheory.DirectedSystem.Isomorphism
import YesMetaZFC.Model.SetTheory.Embedding.Range
import YesMetaZFC.Model.SetTheory.Internal.Isomorphism

/-! # 可数共尾长度上实际选择一条共尾树枝

每个结点若都有任意高的树后继，就沿给定内部 ω 共尾序列逐项越过高度。
每步选最小可用序数，确定递归只用 ZF；最后取所得链的树序向下闭包。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem it_cofinal_branch_l {ω α T F a : M.Domain} (hω : M.IsOmega ω) (h : It_order_d α T)
    (cf : M.IsCofinalOrdinalSequence I F ω α) (ha : M.mem a α)
    (pruned : ∀ i k, M.mem i α → M.mem k α → ∃ j, M.mem j α ∧ Rd_entry_d i j T ∧ (k = j ∨ M.mem k j)) :
    ∃ B, It_branch_d α T B ∧ M.mem a B := by
  have seq := cf.isIncreasing.1.1
  have ff : M.IsSetFunctionFromTo I F ω α := ⟨seq.2.1, seq.2.2, fun n hn => by
    obtain ⟨k, hk⟩ := (seq.2.2 n).mp hn
    exact ⟨k, cf.value_mem hn hk, hk⟩⟩
  obtain ⟨D, hd⟩ := ZF.exists_cartesianProduct hZF I ω α
  let φ : BinarySchema 2 := { body := .existsE (.existsE (.conj
    (kpair_m (.bound 3) (.bound 1) .newest) (.conj (rd_entry_m .newest (.bound 2) (.bound 5))
      (.forallE (.imp (rd_entry_m (.bound 2) .newest (.bound 5))
        (.disj (Formula.extensionalEq .newest (.bound 3)) (.mem .newest (.bound 3)))))))) }
  let ρ : Env M 2 := ⟨Fin.cases F (fun _ => T), fun _ => a⟩
  have sat p y : φ.denote ρ p y ↔ ∃ n x, KPair_d M p n x ∧ Rd_entry_d x y T ∧
      ∀ k, Rd_entry_d n k F → k = y ∨ M.mem k y := by
    simp only [φ, BinarySchema.denote, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
      kpair_sat_l M hZF.1, rd_entry_sat_l hZF.1, Formula.satisfies_forall_iff,
      Formula.satisfies_imp_iff, Formula.satisfies_disj_iff, Formula.satisfies_extensionalEq_iff_eq hZF.1,
      Formula.satisfies_mem_iff]; rfl
  obtain ⟨K, hk, ks⟩ := ZF.ordinal_uniformize_l hZF φ ρ (D := D) h.ordinal (by
    intro p hp
    obtain ⟨n, hn, x, hx, hp⟩ := (hd p).mp hp
    obtain ⟨k, hka, hnk⟩ := ff.2.2 n hn
    obtain ⟨y, _, hxy, above⟩ := pruned x k hx hka
    exact ⟨y, (sat p y).mpr ⟨n, x, hp, hxy, fun k' hnk' => ff.1.2 n k' k hnk' hnk ▸ above⟩⟩) (by
    intro p y _ hy
    obtain ⟨_, x, _, hxy, _⟩ := (sat p y).mp hy
    exact (h.bound x y hxy).2)
  obtain ⟨g, hg, start, step⟩ := ZF.indexed_iteration_l I hZF hω hd (fn0_function_l (ZF.modelsKP hZF) hk) ha
  have advance n m x y (hm : M.SuccessorOf m n) (hx : Rd_entry_d n x g) (hy : Rd_entry_d m y g) :
      Rd_entry_d x y T ∧ ∀ k, Rd_entry_d n k F → k = y ∨ M.mem k y := by
    obtain ⟨p, hp, hpy⟩ := step n m x y hm hx hy
    obtain ⟨n', x', hp', hxy, above⟩ := (sat p y).mp (ks p y hpy)
    obtain ⟨rfl, rfl⟩ := kpair_injective_l M hp hp'
    exact ⟨hxy, above⟩
  let ψ : BinarySchema 1 := { body := rd_entry_m (.bound 1) .newest (.bound 2) }
  let η : Env M 1 := ⟨fun _ => T, fun _ => T⟩
  have psat x y : ψ.denote η x y ↔ Rd_entry_d x y T := rd_entry_sat_l hZF.1 ..
  have chain n m x y (hnm : M.mem n m) (hx : Rd_entry_d n x g) (hy : Rd_entry_d m y g) : Rd_entry_d x y T :=
    (psat x y).mp (ZF.rel_chain_l I hZF ψ η hω hg
      (fun x y z _ _ _ hx hy => (psat x z).mpr (h.trans x y z ((psat x y).mp hx) ((psat y z).mp hy)))
      (fun n m x y hm hx hy => (psat x y).mpr (advance n m x y hm hx hy).1) n m x y hnm hx hy)
  let χ : UnarySchema 2 := { body := .existsE (.existsE
    (.conj (rd_entry_m (.bound 1) .newest (.bound 3)) (rd_entry_m (.bound 2) .newest (.bound 4)))) }
  obtain ⟨B, bs⟩ := ZF.separation_exists_d hZF χ ⟨Fin.cases g (fun _ => T), fun _ => T⟩ α
  have read i : M.mem i B ↔ M.mem i α ∧ ∃ n x, Rd_entry_d n x g ∧ Rd_entry_d i x T := by
    simpa only [χ, UnarySchema.denote, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
      rd_entry_sat_l hZF.1] using! bs i
  have points n x (hx : Rd_entry_d n x g) : M.mem x B :=
    (read x).mpr ⟨hg.output_mem_of_pairMember hx, n, x, hx, h.refl x (hg.output_mem_of_pairMember hx)⟩
  have comparable i j (hi : M.mem i B) (hj : M.mem j B) : Rd_entry_d i j T ∨ Rd_entry_d j i T := by
    obtain ⟨_, n, x, hx, hix⟩ := (read i).mp hi
    obtain ⟨_, m, y, hy, hjy⟩ := (read j).mp hj
    rcases (hω.isOrdinal (ZF.modelsKP hZF)).wellOrder.linear.compare n (hg.input_mem_of_pairMember hx) m (hg.input_mem_of_pairMember hy) with eq | hnm | hmn
    · have eq := hZF.1.eq_of_same_members n m eq
      subst m
      have eq := hg.1.2 n x y hx hy
      exact h.chain i j y (eq ▸ hix) hjy
    · exact h.chain i j y (h.trans i x y hix (chain n m x y hnm hx hy)) hjy
    · exact h.chain i j x hix (h.trans j y x hjy (chain m n y x hmn hy hx))
  have cofinal i (hi : M.mem i α) : ∃ j, M.mem j B ∧ (i = j ∨ M.mem i j) := by
    obtain ⟨D, hd⟩ := ZF.exists_range_of_setFunction hZF I ff.1 ff.2.1
    obtain ⟨k, hk, hik⟩ := ((cf.range_isCofinalSubset hZF.1 hd).2.2 i).mp hi
    obtain ⟨n, hnk⟩ := (hd k).mp hk
    have hn := ff.input_mem_of_pairMember hnk
    obtain ⟨m, hm, hmω⟩ := hω.1.2 n hn
    obtain ⟨x, _, hx⟩ := hg.2.2 n hn
    obtain ⟨y, hyα, hy⟩ := hg.2.2 m hmω
    refine ⟨y, points m y hy, Or.inr ?_⟩
    rcases (advance n m x y hm hx hy).2 k hnk with rfl | hky
    · exact hik
    · exact (h.ordinal.mem hyα).transitive k hky i hik
  obtain ⟨z, hz, _⟩ := hω.1.1
  exact ⟨B, ⟨fun i hi => ((read i).mp hi).1, comparable, fun i j hij hj => by
    obtain ⟨_, n, x, hx, hjx⟩ := (read j).mp hj
    exact (read i).mpr ⟨(h.bound i j hij).1, n, x, hx, h.trans i j x hij hjx⟩, cofinal⟩,
    points z a (start z hz)⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 由实际相容实现证明树枝良基

每条腿是已编码的集合函数，只要求保持成员关系并与树嵌入交换。
不要求它满射、单射或初等。将整列腿装配成带标号载体上的映射，
直接极限的泛性质把良基目标上的最小元性质回拉到商。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

structure It_realizer_d (hZF : M.Models ZF) (B Q G Y V P : M.Domain) : Prop where
  function : M.IsSetFunction (kp_pair_l (ZF.modelsKP hZF)) P
  domain : M.IsDomainOf (kp_pair_l (ZF.modelsKP hZF)) B P
  maps : ∀ i f c X R, Rd_entry_d i f P → Rd_entry_d i c Q → Smdl_d (kp_pair_l (ZF.modelsKP hZF)) c X R →
    Fn0_d X Y f ∧ ∀ x y u v, Rd_entry_d x u f → Rd_entry_d y v f → Rd_entry_d x y R → Rd_entry_d u v V
  commute : ∀ i j f u v, It_map_d G i j f → Rd_entry_d i u P → Rd_entry_d j v P →
    ∀ x y z, Rd_entry_d x y f → Rd_entry_d y z v → Rd_entry_d x z u

def It_value_d (P a y : M.Domain) : Prop := ∃ i x f, KPair_d M a i x ∧ Rd_entry_d i f P ∧ Rd_entry_d x y f
def it_value_m {d} (P a y : Term d) : Formula 1 d := .existsE (.existsE (.existsE
  (.conj (kpair_m a.weaken.weaken.weaken (.bound 2) (.bound 1))
    (.conj (rd_entry_m (.bound 2) .newest P.weaken.weaken.weaken) (rd_entry_m (.bound 1) y.weaken.weaken.weaken .newest)))))
derive_free_closed it_value_m

theorem it_value_sat_l (hE : Extensional M) {d} (ρ : Env M d) (P a y : Term d) :
    Formula.satisfies ρ (it_value_m P a y) ↔ It_value_d (P.eval ρ) (a.eval ρ) (y.eval ρ) := by
  simp only [it_value_m, It_value_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    kpair_sat_l M hE, rd_entry_sat_l hE, Definitional.Term.eval_weaken]; rfl

variable (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem It_embedding_d.realizer_l {ω B Q G d Y V P : M.Domain} (hω : M.IsOmega ω)
    (h : It_embedding_d (kp_pair_l (ZF.modelsKP hZF)) ω B Q G d Y V P) : It_realizer_d hZF B Q G Y V P :=
  ⟨h.function, h.domain, fun i f c X R hf hc mx =>
    ⟨fn0_of_function_l (ZF.modelsKP hZF) (h.elementary i f c X R hf hc mx).1.1,
      fun _ _ _ _ hx hy hr => ((h.elementary i f c X R hf hc mx).relation_l I hZF hω mx h.model hx hy).mp hr⟩,
    h.commute⟩

theorem It_realizer_d.restrict_l {B D Q G Y V P : M.Domain} (h : It_realizer_d hZF B Q G Y V P)
    (sub : M.MemberSubset D B) : ∃ P', It_realizer_d hZF D Q G Y V P' ∧
      ∀ i f, Rd_entry_d i f P' ↔ M.mem i D ∧ Rd_entry_d i f P := by
  obtain ⟨P', hp⟩ := ZF.exists_restriction hZF I P D
  refine ⟨P', ⟨hp.isSetFunction h.function, ?_, fun i f c X R hi hc mx => h.maps i f c X R ((hp.2 i f).mp hi).2 hc mx,
    fun i j f u v hf hu hv => h.commute i j f u v hf ((hp.2 i u).mp hu).2 ((hp.2 j v).mp hv).2⟩, hp.2⟩
  intro i
  exact ⟨fun hi => by
    obtain ⟨f, hf⟩ := (h.domain i).mp (sub i hi)
    exact ⟨f, (hp.2 i f).mpr ⟨hi, hf⟩⟩, fun ⟨f, hf⟩ => ((hp.2 i f).mp hf).1⟩

theorem It_realizer_d.map_l {ω α T Q G B L A p H R Y V P : M.Domain}
    (realizer : It_realizer_d hZF B Q G Y V P) (h : It_diagram_d (kp_pair_l (ZF.modelsKP hZF)) ω α T Q G)
    (inside : M.MemberSubset B α) (s : It_system_d B L Q G A p H R) :
    ∃ r, Fn0_d A Y r ∧ (∀ a y, Rd_entry_d a y r ↔ M.mem a A ∧ It_value_d P a y) ∧
      ∀ a b u v, Rd_entry_d a b H → Rd_entry_d a u r → Rd_entry_d b v r → u = v := by
  obtain ⟨D, hq⟩ := h.family_l hZF
  have map i f (hf : Rd_entry_d i f P) : ∃ c X R, Rd_entry_d i c Q ∧ Smdl_d I c X R ∧ Fn0_d X Y f := by
    obtain ⟨c, X, R, hc, mx⟩ := h.model_l hZF (inside i ((realizer.domain i).mpr ⟨f, hf⟩))
    exact ⟨c, X, R, hc, mx, (realizer.maps i f c X R hf hc mx).1⟩
  let φ : BinarySchema 1 := { body := it_value_m (.bound 2) (.bound 1) .newest }
  let ρ : Env M 1 := ⟨fun _ => P, fun _ => P⟩
  have sat a y : φ.denote ρ a y ↔ It_value_d P a y := it_value_sat_l hZF.1 ..
  obtain ⟨r, hr, rs⟩ := ZF.exists_setFunctionFromTo_of_denote hZF I φ ρ (source := A) (target := Y)
    (fun a ha => by
      obtain ⟨i, x, hi, hp, hx⟩ := (s.tags.nodes a).mp ha
      obtain ⟨f, hf⟩ := (realizer.domain i).mp hi
      obtain ⟨c, X, R, hc, mx, ff⟩ := map i f hf
      obtain ⟨y, _, hxy⟩ := ff.2.1 x ((ep_at_read_l hq hc mx.1).mp hx)
      exact ⟨y, (sat a y).mpr ⟨i, x, f, hp, hf, hxy⟩⟩)
    (fun a _ u v hu hv => by
      obtain ⟨i, x, f, hp, hf, hxu⟩ := (sat a u).mp hu
      obtain ⟨j, y, g, hp', hg, hyv⟩ := (sat a v).mp hv
      obtain ⟨rfl, rfl⟩ := kpair_injective_l M hp hp'
      have eq := realizer.function.2 i g f hg hf
      obtain ⟨_, _, _, _, _, ff⟩ := map i f hf
      exact (fn0_function_l (ZF.modelsKP hZF) ff).1.2 x u v hxu (eq ▸ hyv))
    (fun a y _ hy => by
      obtain ⟨i, x, f, _, hf, hxy⟩ := (sat a y).mp hy
      obtain ⟨_, _, _, _, _, ff⟩ := map i f hf
      exact (ff.bound_l hxy).2)
  have compatible a b u v (hab : Rd_entry_d a b H) (hau : Rd_entry_d a u r) (hbv : Rd_entry_d b v r) : u = v := by
    obtain ⟨i, x, f, hp, hf, hxu⟩ := (sat a u).mp ((rs a u).mp hau).2
    obtain ⟨j, y, g, hp', hg, hyv⟩ := (sat b v).mp ((rs b v).mp hbv).2
    obtain ⟨k, hk, hxy⟩ := ((s.arrows a b i j x y hp hp').mp hab).2.2
    obtain ⟨_, _, _, _, _, ff⟩ := map i f hf
    exact (fn0_function_l (ZF.modelsKP hZF) ff).1.2 x u v hxu (realizer.commute i j k f g hk hf hg x y v hxy hyv)
  exact ⟨r, fn0_of_function_l (ZF.modelsKP hZF) hr,
    fun a y => (rs a y).trans (and_congr_right fun _ => sat a y), compatible⟩

theorem it_realizer_wf_l {ω α T Q G B L A p H R q C S Y V P : M.Domain}
    (h : It_diagram_d (kp_pair_l (ZF.modelsKP hZF)) ω α T Q G) (inside : M.MemberSubset B α) (s : It_system_d B L Q G A p H R)
    (limit : Di_limit_d A p H R q C S) (realizer : It_realizer_d hZF B Q G Y V P) (wf : Wf_rel_d Y V) : Wf_rel_d C S := by
  obtain ⟨D, hq⟩ := h.family_l hZF
  obtain ⟨r, hr, rs, compatible⟩ := realizer.map_l hZF h inside s
  have read a i x f y (hp : KPair_d M a i x) (hf : Rd_entry_d i f P) (hy : Rd_entry_d a y r) : Rd_entry_d x y f := by
    obtain ⟨j, z, g, hp', hg, hzy⟩ := ((rs a y).mp hy).2
    obtain ⟨rfl, rfl⟩ := kpair_injective_l M hp hp'
    exact realizer.function.2 i g f hg hf ▸ hzy
  have preserve a b i u v (_ : Rd_entry_d a i p) (_ : Rd_entry_d b i p)
      (hau : Rd_entry_d a u r) (hbv : Rd_entry_d b v r) (hab : Rd_entry_d a b R) : Rd_entry_d u v V := by
    obtain ⟨_, _, k, x, y, hp, hp', hxy⟩ := (s.tags.relations a b).mp hab
    obtain ⟨j, z, f, hpa, hf, _⟩ := ((rs a u).mp hau).2
    obtain ⟨rfl, rfl⟩ := kpair_injective_l M hp hpa
    obtain ⟨c, X, R₀, hc, mx⟩ := h.model_l hZF (inside k ((realizer.domain k).mpr ⟨f, hf⟩))
    exact (realizer.maps k f c X R₀ hf hc mx).2 x y u v (read a k x f u hp hf hau)
      (read b k y f v hp' hf hbv) ((ep_rel_read_l hq hc mx.1).mp hxy)
  exact (di_cone_wf_l hZF s.system limit hr wf compatible preserve).elim
    fun _ hh => hh.2.2

theorem it_realized_branch_l {ω α T Q G B Y V P : M.Domain} (hω : M.IsOmega ω)
    (h : It_diagram_d (kp_pair_l (ZF.modelsKP hZF)) ω α T Q G) (b : It_branch_d α T B) (ne : ∃ i, M.mem i B)
    (realizer : It_realizer_d hZF B Q G Y V P) (wf : Wf_rel_d Y V) : It_wf_branch_d hZF ω α T Q G B := by
  obtain ⟨L, A, p, H, R, q, c, C, S, ls, s, elem, limit, model⟩ := it_branch_data_l hZF hω h b ne
  exact ⟨b, L, A, p, H, R, q, c, C, S, ls, s, elem, limit, model,
    it_realizer_wf_l hZF h b.subset s limit realizer wf⟩

/-- 共尾枝由最小后继递归构造，良基性由实际相容腿证明；两步都只用 ZF。 -/
theorem it_pruned_wf_branch_l {ω α T Q G F a Y V P : M.Domain} (hω : M.IsOmega ω)
    (h : It_diagram_d (kp_pair_l (ZF.modelsKP hZF)) ω α T Q G) (cf : M.IsCofinalOrdinalSequence I F ω α) (ha : M.mem a α)
    (pruned : ∀ i k, M.mem i α → M.mem k α → ∃ j, M.mem j α ∧ Rd_entry_d i j T ∧ (k = j ∨ M.mem k j))
    (realizer : It_realizer_d hZF α Q G Y V P) (wf : Wf_rel_d Y V) :
    ∃ B, It_wf_branch_d hZF ω α T Q G B ∧ M.mem a B := by
  obtain ⟨B, b, haB⟩ := it_cofinal_branch_l hZF hω h.order cf ha pruned
  obtain ⟨P', rp, _⟩ := realizer.restrict_l hZF b.subset
  exact ⟨B, it_realized_branch_l hZF hω h b ⟨a, haB⟩ rp wf, haB⟩

/-! 在已有修剪树和良基实现下，把逐点分支存在性一次组织成
外部选择函数。这个出口供一般策略的统一 branch 消费端使用，
不把选择函数伪装成模型内可数枚举。 -/
theorem it_pruned_wf_branch_choice_l {ω α T Q G F Y V P : M.Domain} (hω : M.IsOmega ω)
    (h : It_diagram_d (kp_pair_l (ZF.modelsKP hZF)) ω α T Q G) (cf : M.IsCofinalOrdinalSequence I F ω α)
    (pruned : ∀ i k, M.mem i α → M.mem k α →
      ∃ j, M.mem j α ∧ Rd_entry_d i j T ∧ (k = j ∨ M.mem k j))
    (realizer : It_realizer_d hZF α Q G Y V P) (wf : Wf_rel_d Y V) :
    ∃ choose : M.Domain → M.Domain,
      ∀ a, M.mem a α → It_wf_branch_d hZF ω α T Q G (choose a) ∧ M.mem a (choose a) := by
  classical
  have total (a : M.Domain) (ha : M.mem a α) :
      ∃ B, It_wf_branch_d hZF ω α T Q G B ∧ M.mem a B :=
    it_pruned_wf_branch_l hZF hω h cf ha pruned realizer wf
  let choose : M.Domain → M.Domain := fun a =>
    if ha : M.mem a α then Classical.choose (total a ha) else Classical.choice M.nonempty
  refine ⟨choose, ?_⟩
  intro a ha
  dsimp [choose]
  rw [dif_pos ha]
  exact Classical.choose_spec (total a ha)

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 共尾枝的完整初等因子与实际传递极限

相容初等嵌入列通过同一个带标号系统下降到直接极限。目标不要求由像覆盖。
目标是实际隶属结构时，先证明良基，再坍塌，并保留根嵌入的精确复合式。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem it_embedding_factor_l {ω α T Q G B L A p H R q c C V d Y W P : M.Domain}
    (hω : M.IsOmega ω) (h : It_diagram_d (kp_pair_l (ZF.modelsKP hZF)) ω α T Q G) (inside : M.MemberSubset B α)
    (s : It_system_d B L Q G A p H R) (elementary : Di_elementary_d I ω L A p H R)
    (limit : Di_limit_d A p H R q C V) (model : Smdl_d I c C V)
    (maps : It_embedding_d (kp_pair_l (ZF.modelsKP hZF)) ω B Q G d Y W P) :
    ∃ e, Smap_d I ω c d C Y e ∧ ∀ a i x f z y, KPair_d M a i x → Rd_entry_d i f P →
      Rd_entry_d a z q → Rd_entry_d x y f → Rd_entry_d z y e := by
  obtain ⟨D, hq⟩ := h.family_l hZF
  obtain ⟨r, hr, rs, comm⟩ := (maps.realizer_l hZF hω).map_l hZF h inside s
  have cone i b X S (stage : Di_stage_d I A p R i b X S) : ∃ f, Smap_d I ω b d X Y f ∧
      ∀ a y, Rd_entry_d a y f ↔ M.mem a X ∧ Rd_entry_d a y r := by
    obtain ⟨a, ha⟩ := stage.1.2.1
    have hi := (s.tags.projection.bound_l ((stage.2.1 a).mp ha).2).2
    obtain ⟨c₀, Z, U, hc, mz⟩ := h.model_l hZF (inside i hi)
    obtain ⟨g, hg⟩ := (maps.domain i).mp hi
    obtain ⟨t, _, ht, _, ts, _⟩ := it_tag_iso_l hZF hω s.tags hq stage hc mz
    obtain ⟨f, hf, fs⟩ := smap_comp_l I hZF ht (maps.elementary i g c₀ Z U hg hc mz)
    refine ⟨f, hf, fun a y => ⟨?_, ?_⟩⟩
    · intro hay
      obtain ⟨ha, x, hax, hxy⟩ := (fs a y).mp hay
      exact ⟨ha, (rs a y).mpr ⟨((stage.2.1 a).mp ha).1, i, x, g, ((ts a x).mp hax).2, hg, hxy⟩⟩
    · rintro ⟨ha, hay⟩
      obtain ⟨_, j, x, u, hp, hu, hxy⟩ := (rs a y).mp hay
      obtain ⟨x', hx'⟩ := s.tags.label_l (((stage.2.1 a).mp ha).2)
      obtain ⟨ej, ex⟩ := kpair_injective_l M hp hx'.1
      subst j x'
      exact (fs a y).mpr ⟨ha, x, (ts a x).mpr ⟨ha, hx'.1⟩, maps.function.2 i u g hu hg ▸ hxy⟩
  obtain ⟨e, he, law, _⟩ := di_factor_elementary_l hZF hω s.system limit elementary model maps.model hr comm cone
  exact ⟨e, he, fun a i x f z y hp hf hz hy => law a z y hz
    ((rs a y).mpr ⟨(limit.projection.bound_l hz).1, i, x, f, hp, hf, hy⟩)⟩

def It_return_at_d (ω z T Q G d Y π B : M.Domain) : Prop := ∃ L A p H R r c N V P σ,
  It_branch_d ω T B ∧ It_system_d B L Q G A p H R ∧ Di_limit_d A p H R r N V ∧
    Smem_d I c N V ∧ It_cone_d (kp_pair_l (ZF.modelsKP hZF)) ω B Q G c N V P ∧ (∃ K, Ep_source_d I ω ω K N V) ∧
    Smap_d I ω c d N Y σ ∧ (∀ i f, Rd_entry_d i f P ↔ M.mem i B ∧ It_project_d r i f) ∧
    ∃ j, Rd_entry_d z j P ∧ It_comp_d j σ π ∧
    (∀ i j, Rd_entry_d i j L ↔ M.mem i B ∧ M.mem j B ∧ Rd_entry_d i j T) ∧ Wf_rel_d N V

/-- 不指定分支的返回存在性。 -/
def It_return_d (ω z T Q G d Y π : M.Domain) : Prop := ∃ B, It_return_at_d hZF ω z T Q G d Y π B

/-- 任意长度的相容初等列都有实际传递极限，返回因子与每一条腿交换。 -/
theorem it_embedding_limit_l {ω α T Q G B z c₀ d Y W P : M.Domain}
    (hω : M.IsOmega ω) (h : It_diagram_d (kp_pair_l (ZF.modelsKP hZF)) ω α T Q G) (b : It_branch_d α T B)
    (hz : M.mem z B) (hc : Rd_entry_d z c₀ Q) (source : It_source_d hZF ω c₀)
    (my : Smem_d I d Y W) (maps : It_embedding_d (kp_pair_l (ZF.modelsKP hZF)) ω B Q G d Y W P) :
    ∃ L A p H R r c N V P' σ, It_system_d B L Q G A p H R ∧ Di_limit_d A p H R r N V ∧
      Smem_d I c N V ∧ It_cone_d (kp_pair_l (ZF.modelsKP hZF)) ω B Q G c N V P' ∧ (∃ K, Ep_source_d I ω ω K N V) ∧
      Smap_d I ω c d N Y σ ∧ (∀ i f, Rd_entry_d i f P' ↔ M.mem i B ∧ It_project_d r i f) ∧
      (∀ i f j, Rd_entry_d i f P → Rd_entry_d i j P' → It_comp_d j σ f) ∧
      (∀ i j, Rd_entry_d i j L ↔ M.mem i B ∧ M.mem j B ∧ Rd_entry_d i j T) ∧
      Wf_rel_d N V := by
  obtain ⟨X₀, V₀, _, _, _, mx, _⟩ := source.objects
  have wf := (it_wf_mem_l (ZF.modelsKP hZF) my).read_l I my.1
  obtain ⟨L, A, p, H, R, q, c, C, V, ls, s, elem, limit, model⟩ := it_branch_data_l hZF hω h b ⟨z, hz⟩
  have wfC := it_realizer_wf_l hZF h b.subset s limit (maps.realizer_l hZF hω) wf
  obtain ⟨e, N, S, P', v, r, cone, ready, mn, nt, _, bij, hv, fr, rs, ps⟩ :=
    it_limit_model_l hZF h b.subset s elem limit model wfC hz hc mx source
  obtain ⟨N₀, S₀, K₀, mn₀, sn⟩ := ready.mem_l hZF ⟨N, S, mn, nt⟩
  obtain ⟨eN, eS⟩ := smdl_unique_l I mn₀.1 mn.1
  subst N₀ S₀
  have next := di_limit_iso_l (ZF.modelsKP hZF) limit bij fr rs mn.1.2.2
    (fun _ _ _ _ hx hy => hv.relation_l I hZF hω model mn.1 hx hy)
  obtain ⟨σ, hs, law⟩ := it_embedding_factor_l hZF hω h b.subset s elem next mn.1 maps
  have wfN : Wf_rel_d N S := (it_wf_mem_l (ZF.modelsKP hZF) mn).read_l I mn.1
  refine ⟨L, A, p, H, R, r, e, N, S, P', σ, s, next, mn, cone, ⟨K₀, sn⟩, hs, ps, ?_, ?_, wfN⟩
  intro i π j root hj
  obtain ⟨a, X, U, ha, mdl⟩ := h.model_l hZF (b.subset i ((cone.domain i).mpr ⟨j, hj⟩))
  have pi := maps.elementary i π a X U root ha mdl
  have jj := cone.elementary i j a X U hj ha mdl
  have factor x v y (hxv : Rd_entry_d x v j) (hxy : Rd_entry_d x y π) : Rd_entry_d v y σ := by
    obtain ⟨a, hp, hav⟩ := (((ps i j).mp hj).2.2 x v).mp hxv
    exact law a i x π v y hp root hav hxy
  refine ⟨pi.1.1.1.1, fun x y => ⟨?_, ?_⟩⟩
  · intro hxy
    obtain ⟨v, _, hxv⟩ := jj.1.1.2.2 x (pi.1.1.input_mem_of_pairMember hxy)
    exact ⟨v, hxv, factor x v y hxv hxy⟩
  · rintro ⟨v, hxv, hvy⟩
    obtain ⟨u, _, hxu⟩ := pi.1.1.2.2 x (jj.1.1.input_mem_of_pairMember hxv)
    exact hs.1.1.1.2 v u y (factor x v u hxv hxu) hvy ▸ hxu
  exact ls

theorem it_embedding_return_l {ω T Q G B z c₀ d Y W P π : M.Domain}
    (hω : M.IsOmega ω) (h : It_diagram_d (kp_pair_l (ZF.modelsKP hZF)) ω ω T Q G) (b : It_branch_d ω T B)
    (hz : M.mem z B) (hc : Rd_entry_d z c₀ Q) (source : It_source_d hZF ω c₀)
    (my : Smem_d I d Y W) (maps : It_embedding_d (kp_pair_l (ZF.modelsKP hZF)) ω B Q G d Y W P) (root : Rd_entry_d z π P) :
    It_return_d hZF ω z T Q G d Y π := by
  obtain ⟨L, A, p, H, R, r, c, N, V, P', σ, s, limit, mn, cone, ready, hs, ps, law, ls, wfN⟩ :=
    it_embedding_limit_l hZF hω h b hz hc source my maps
  obtain ⟨j, hj⟩ := (cone.domain z).mp hz
  exact ⟨B, L, A, p, H, R, r, c, N, V, P', σ, b, s, limit, mn, cone, ready, hs, ps, j, hj, law z π j root hj, ls, wfN⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 返回因子落实到同枝的指定实际极限

直接极限的泛性质给出两份极限之间的初等图。指定锥的覆盖性证明它满射，
实际逆图再把返回因子搬到指定目标；根图的复合式逐点保持。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem It_return_at_d.factor_l {ω o T Q G d Y π b c N R P j : M.Domain}
    (returned : It_return_at_d hZF ω o T Q G d Y π b)
    (hω : M.IsOmega ω) (diagram : It_diagram_d (kp_pair_l (ZF.modelsKP hZF)) ω ω T Q G)
    (cone : It_cone_d (kp_pair_l (ZF.modelsKP hZF)) ω b Q G c N R P) (leg : Rd_entry_d o j P) :
    ∃ σ, Smap_d I ω c d N Y σ ∧ It_comp_d j σ π := by
  obtain ⟨L,A,p,H,S,q,c₀,N₀,R₀,P₀,σ₀,branch,system,limit,model,old,_,returnMap,projects,
    j₀,leg₀,square,order,_⟩ := returned
  have elementary := system.elementary_l hZF hω diagram branch.subset order
  obtain ⟨e,map,law⟩ := it_embedding_factor_l hZF hω diagram branch.subset system elementary limit model.1 cone.toIt_embedding_d
  have onto : ∀ y, M.mem y N → ∃ x, M.mem x N₀ ∧ Rd_entry_d x y e := by
    intro y hy
    obtain ⟨i,f,x,hf,xy⟩ := cone.cover y hy
    have hi := (cone.domain i).mpr ⟨f,hf⟩
    obtain ⟨g,hg⟩ := (old.domain i).mp hi
    obtain ⟨a,X,W,ha,mx⟩ := diagram.model_l hZF (branch.subset i hi)
    have left := old.elementary i g a X W hg ha mx
    have right := cone.elementary i f a X W hf ha mx
    obtain ⟨v,hv,xv⟩ := left.1.1.2.2 x (right.1.1.input_mem_of_pairMember xy)
    obtain ⟨t,pair,tv⟩ := (((projects i g).mp hg).2.2 x v).mp xv
    exact ⟨v,hv,law t i x f v y pair hf tv xy⟩
  obtain ⟨inv,bij,inverse⟩ := ZF.exists_inverseBijectionWithPairs hZF I ⟨map.1,onto⟩
  have backMap : Smap_d I ω c c₀ N N₀ inv := smap_of_iso_l I hZF hω cone.model model.1 bij
    (fun x y a b xa yb => (map.relation_l I hZF hω model.1 cone.model
      ((inverse x a).mp xa) ((inverse y b).mp yb)).symm)
  obtain ⟨σ,embed,composition⟩ := smap_comp_l I hZF backMap returnMap
  have ho := (cone.domain o).mpr ⟨j,leg⟩
  obtain ⟨a,X,W,ha,mx⟩ := diagram.model_l hZF (branch.subset o ho)
  have left := old.elementary o j₀ a X W leg₀ ha mx
  have right := cone.elementary o j a X W leg ha mx
  have point x v y (xv : Rd_entry_d x v j₀) (xy : Rd_entry_d x y j) : Rd_entry_d v y e := by
    obtain ⟨t,pair,tv⟩ := (((projects o j₀).mp leg₀).2.2 x v).mp xv
    exact law t o x j v y pair leg tv xy
  have back x y : Rd_entry_d x y j₀ ↔ ∃ v, Rd_entry_d x v j ∧ Rd_entry_d v y inv := by
    constructor
    · intro xy
      obtain ⟨v,_,xv⟩ := right.1.1.2.2 x (left.1.1.input_mem_of_pairMember xy)
      exact ⟨v,xv,(inverse v y).mpr (point x y v xy xv)⟩
    · rintro ⟨v,xv,vy⟩
      obtain ⟨y₀,_,xy₀⟩ := left.1.1.2.2 x (right.1.1.input_mem_of_pairMember xv)
      exact map.1.2 y₀ y v (point x y₀ v xy₀ xv) ((inverse v y).mp vy) ▸ xy₀
  refine ⟨σ,embed,square.1,fun x y => (square.2 x y).trans ?_⟩
  constructor
  · rintro ⟨u,xu,uy⟩
    obtain ⟨v,xv,vu⟩ := (back x u).mp xu
    exact ⟨v,xv,(composition v y).mpr ⟨right.1.1.output_mem_of_pairMember xv,u,vu,uy⟩⟩
  · rintro ⟨v,xv,vy⟩
    obtain ⟨_,u,vu,uy⟩ := (composition v y).mp vy
    exact ⟨u,(back x u).mpr ⟨v,xv,vu⟩,uy⟩

end YesMetaZFC.SetTheory.LargeCardinal
