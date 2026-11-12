import YesMetaZFC.Model.SetTheory.Internal.RelativizationCorrect
import YesMetaZFC.Model.SetTheory.Internal.LargestSet
import YesMetaZFC.Model.SetTheory.Types.Embedding
import YesMetaZFC.Model.SetTheory.Embedding.RankFixed

/-! # 类型向前一秩层限制的纯语法代码

先编译所有量词的载体限制，再绑定该载体为当前结构的最大集合。
输出证书只包含原指令、自然数坐标和实际函数图，不包含真值假设。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

def Sr_minus_d (ω F n r G m u : M.Domain) : Prop := ∃ b T v w t,
  M.mem b ω ∧ Sbound_d I F b ∧ Sr_state_d I ω b F n m G T ∧ M.PairMember I r v T ∧
    Sr_top_code_d I b G w ∧ Sr_and_d I G t w v ∧ Sr_at_d I 3 G u b t

def sr_minus_m {d} (ω F n r G m u : Term d) : Formula 1 d := set[d] ⟪∃ b T v w t,
  b ∈ ⌜ω⌝ₛ ∧ ⌜sbound_m (𝒞 := 𝒞)⌝ₚ(⌜F⌝ₛ, b) ∧
  ⌜sr_state_m (𝒞 := 𝒞)⌝ₚ(⌜ω⌝ₛ, b, ⌜F⌝ₛ, ⌜n⌝ₛ, ⌜m⌝ₛ, ⌜G⌝ₛ, T) ∧
  ⌜Formula.orderedPairMem 𝒞⌝ₚ(⌜r⌝ₛ, v, T) ∧ ⌜sr_top_code_m (𝒞 := 𝒞)⌝ₚ(b, ⌜G⌝ₛ, w) ∧
  ⌜sr_and_m (𝒞 := 𝒞)⌝ₚ(⌜G⌝ₛ, t, w, v) ∧ ⌜sr_at_m (𝒞 := 𝒞) 3⌝ₚ(⌜G⌝ₛ, ⌜u⌝ₛ, b, t)⟫
derive_free_closed sr_minus_m

theorem sr_minus_sat_l (hE : Extensional M) {d} (ρ : Env M d) (ω F n r G m u : Term d) :
    Formula.satisfies ρ (sr_minus_m (𝒞 := 𝒞) ω F n r G m u) ↔
      Sr_minus_d I (ω.eval ρ) (F.eval ρ) (n.eval ρ) (r.eval ρ) (G.eval ρ) (m.eval ρ) (u.eval ρ) := by
  simp only [sr_minus_m, Sr_minus_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    Formula.satisfies_mem_iff, sbound_sat_l I, sr_state_sat_l I hE, Formula.satisfies_orderedPairMem_iff I,
    sr_top_code_sat_l I, sr_and_sat_l I, sr_at_sat_l I, Definitional.Term.eval_weaken]; rfl

theorem sr_minus_build_l (hZF : M.Models ZF) {ω F n r : M.Domain} (hω : M.IsOmega ω)
    (hF : Sfm_d I ω n F) (hr : M.mem r n) : ∃ m G u, Sr_minus_d I ω F n r G m u := by
  obtain ⟨b, m, G, T, hb, bound, state⟩ := sr_compile_l I hZF hω hF
  obtain ⟨v, hv, hrv⟩ := state.map.2.2 r hr
  obtain ⟨m₁, G₁, w, h₁, top⟩ := sr_top_build_l I hZF hω hb state.program
  obtain ⟨m₂, G₂, t, h₂, conj⟩ := sr_and_build_l I hZF hω h₁.program h₁.root (h₁.span v hv)
  obtain ⟨l, H, h₃, ex⟩ := sr_ex_add_l I hZF hω h₂.program hb h₂.root
  exact ⟨l, H, m₂, b, T, v, w, t, hb, bound, state.extend_l I ((h₁.comp I h₂).comp I h₃),
    hrv, top.extend_l I (h₂.comp I h₃), conj.extend_l I h₃, ex⟩

theorem Sr_minus_d.program_l {ω F n r G m u : M.Domain} (h : Sr_minus_d I ω F n r G m u) :
    Sfm_d I ω m G ∧ M.mem u m := by
  obtain ⟨_, _, _, _, _, _, _, state, _, _, _, c, hc, _⟩ := h
  exact ⟨state.program, (state.program.2.1.2.2 u).mpr ⟨c, hc⟩⟩

end YesMetaZFC.SetTheory.Internal

/-! ## 向前一秩层限制的语义

最大集合代码使新绑定的载体唯一等于指定小载体；限制证书随后恢复
原程序的真值；类型查询仍只使用原来的参数赋值。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

theorem Sr_minus_d.correct_l (hZF : M.Models ZF) {ω F n r G m u c X R d Y S E D f : M.Domain}
    (hω : M.IsOmega ω) (hF : Sfm_d I ω n F) (h : Sr_minus_d I ω F n r G m u)
    (hm : Smem_d I c X R) (hn : Smem_d I d Y S) (hY : M.TransitiveSet Y) (top : Sr_top_d Y X)
    (hE : M.IsFunctionSpace I E ω X) (hD : M.IsFunctionSpace I D ω Y) (hf : M.mem f E) :
    Ssat_d I X R E F n r f ↔ Ssat_d I Y S D G m u f := by
  obtain ⟨b, T, v, w, t, hb, bound, state, hrv, topcode, conj, cu, hcu, op⟩ := h
  have sub := hY X top.1
  have context := sr_context_l I hm hn sub top.1 hE hD
  have row := state.correct_l I hZF hF bound context (state.map.input_mem_of_pairMember hrv) hrv
  have ff := (hE f).mp hf
  have fg : M.IsSetFunctionFromTo I f ω Y := ⟨ff.1, ff.2.1, fun i hi =>
    (ff.2.2 i hi).imp fun x hx => ⟨sub x hx.1, hx.2⟩⟩
  have hg := (hD f).mpr fg
  obtain ⟨H, hH⟩ := seval_exists_l I hZF Y S D G state.program.2.1.1
  have read Z g (hZ : M.mem Z Y) (update : Senv_update_d I f b Z g) :
      Ssat_d I Y S D G m t g ↔ Sr_top_d Y Z ∧ Ssat_d I Y S D G m v g := by
    have hg := (hD g).mpr (update.function_l I fg hb hZ)
    exact (conj.correct_l I hZF state.program hg).trans (and_congr
      (topcode.correct_l I hZF hω state.program hn hY hD hg ((update.2 b Z).mpr (Or.inl ⟨rfl, rfl⟩))) Iff.rfl)
  rw [ssat_exists_l I hZF state.program hH hcu op hg]
  constructor
  · intro truth
    obtain ⟨g, update, fn⟩ := senv_update_exists_l I hZF fg hb top.1
    have agree := update.agree_l I (KP.mem_irrefl_d (ZF.modelsKP hZF) b)
    exact ⟨X, g, top.1, update, (read X g top.1 update).mpr
      ⟨top, (row f g hf ((hD g).mpr fn) ((update.2 b X).mpr (Or.inl ⟨rfl, rfl⟩)) agree).mp truth⟩⟩
  · rintro ⟨Z, g, hZ, update, truth⟩
    obtain ⟨top', truth'⟩ := (read Z g hZ update).mp truth
    have eq := top'.unique_l hZF.1 top
    subst Z
    exact (row f g hf ((hD g).mpr (update.function_l I fg hb top.1))
      ((update.2 b X).mpr (Or.inl ⟨rfl, rfl⟩)) (update.agree_l I (KP.mem_irrefl_d (ZF.modelsKP hZF) b))).mpr truth'

/-- 自动构造两边的赋值空间，把同一语法证书接回统一满足关系。 -/
theorem Sr_minus_d.satisfies_l (hZF : M.Models ZF) {ω F n r G m u c X R d Y S a a' f : M.Domain}
    (hω : M.IsOmega ω) (h : Sr_minus_d I ω F n r G m u)
    (ha : Sformula_d I ω a n F r) (ha' : Sformula_d I ω a' m G u)
    (hm : Smem_d I c X R) (hn : Smem_d I d Y S) (hY : M.TransitiveSet Y) (top : Sr_top_d Y X)
    (hf : M.IsSetFunctionFromTo I f ω X) : Satisfies_d I ω c a f ↔ Satisfies_d I ω d a' f := by
  obtain ⟨E, hE⟩ := ZF.exists_functionSpace hZF I ω X
  obtain ⟨D, hD⟩ := ZF.exists_functionSpace hZF I ω Y
  exact (satisfies_decode_l I hZF.1 hm.1 ha hE).trans
    ((h.correct_l I hZF hω ha.2.1 hm hn hY top hE hD ((hE f).mpr hf)).trans
      (satisfies_decode_l I hZF.1 hn.1 ha' hD).symm)

theorem sr_minus_formula_l (hZF : M.Models ZF) {ω a n F r : M.Domain} (hω : M.IsOmega ω)
    (ha : Sformula_d I ω a n F r) : ∃ a' m G u, Sformula_d I ω a' m G u ∧ Sr_minus_d I ω F n r G m u := by
  obtain ⟨m, G, u, h⟩ := sr_minus_build_l I hZF hω ha.2.1 ha.2.2
  obtain ⟨a', code⟩ := I.total G u
  have shape := h.program_l I
  exact ⟨a', m, G, u, ⟨code, shape.1, shape.2⟩, h⟩

end YesMetaZFC.SetTheory.Internal

/-! ## 完整类型的前驱算子

只改变查询的公式码，保留原名字列。查询之间的关系由实际语法证书定义，
不量化真值保持条件；前驱类型是上一级类型在这条关系下的逆像。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} (I : kpair_convention_l.Interpretation M)

def Tm_code_d (ω z z' : M.Domain) : Prop := ∃ a a' n F r m G u,
  Sc_num_d I ω a z ∧ Sc_num_d I ω a' z' ∧
    Sformula_d I ω a n F r ∧ Sformula_d I ω a' m G u ∧ Sr_minus_d I ω F n r G m u

def tm_code_m {d} (ω z z' : Term d) : Formula 1 d := set[d] ⟪∃ a a' n F r m G u,
  ⌜sc_num_m (𝒞 := kpair_convention_l)⌝ₚ(⌜ω⌝ₛ, a, ⌜z⌝ₛ) ∧
  ⌜sc_num_m (𝒞 := kpair_convention_l)⌝ₚ(⌜ω⌝ₛ, a', ⌜z'⌝ₛ) ∧
  ⌜sformula_m (𝒞 := kpair_convention_l)⌝ₚ(⌜ω⌝ₛ, a, n, F, r) ∧
  ⌜sformula_m (𝒞 := kpair_convention_l)⌝ₚ(⌜ω⌝ₛ, a', m, G, u) ∧
  ⌜sr_minus_m (𝒞 := kpair_convention_l)⌝ₚ(⌜ω⌝ₛ, F, n, r, G, m, u)⟫
derive_free_closed tm_code_m

theorem tm_code_sat_l (hE : Extensional M) {d} (ρ : Env M d) (ω z z' : Term d) :
    Formula.satisfies ρ (tm_code_m ω z z') ↔ Tm_code_d I (ω.eval ρ) (z.eval ρ) (z'.eval ρ) := by
  simp only [tm_code_m, Tm_code_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    sc_num_sat_l I hE, sformula_sat_l I hE, sr_minus_sat_l I hE, Definitional.Term.eval_weaken]; rfl

theorem Tm_code_d.natural_l (hZF : M.Models ZF) {ω z w : M.Domain} (hω : M.IsOmega ω)
    (h : Tm_code_d I ω z w) : M.mem z ω ∧ M.mem w ω := by
  obtain ⟨_, _, _, _, _, _, _, _, hz, hw, _⟩ := h
  exact ⟨sc_num_natural_l I hZF hω hz, sc_num_natural_l I hZF hω hw⟩

def Tm_query_d (ω p q : M.Domain) : Prop := ∃ z e z', I.Codes p z e ∧ I.Codes q z' e ∧ Tm_code_d I ω z z'

def tm_query_m {d} (ω p q : Term d) : Formula 1 d := set[d] ⟪∃ z e z',
  ⌜kpair_convention_l.code⌝ₚ(⌜p⌝ₛ, z, e) ∧ ⌜kpair_convention_l.code⌝ₚ(⌜q⌝ₛ, z', e) ∧
    ⌜tm_code_m⌝ₚ(⌜ω⌝ₛ, z, z')⟫
derive_free_closed tm_query_m

theorem tm_query_sat_l (hE : Extensional M) {d} (ρ : Env M d) (ω p q : Term d) :
    Formula.satisfies ρ (tm_query_m ω p q) ↔ Tm_query_d I (ω.eval ρ) (p.eval ρ) (q.eval ρ) := by
  simp only [tm_query_m, Tm_query_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    I.satisfies_code_iff, tm_code_sat_l I hE, Definitional.Term.eval_weaken]; rfl

def Tm_minus_d (ω D t u : M.Domain) : Prop :=
  ∀ p, M.mem p u ↔ M.mem p D ∧ ∃ q, Tm_query_d I ω p q ∧ M.mem q t

def tm_minus_m {d} (ω D t u : Term d) : Formula 1 d := set[d] ⟪∀ p,
  p ∈ ⌜u⌝ₛ ↔ p ∈ ⌜D⌝ₛ ∧ (∃ q, ⌜tm_query_m⌝ₚ(⌜ω⌝ₛ, p, q) ∧ q ∈ ⌜t⌝ₛ)⟫
derive_free_closed tm_minus_m

theorem tm_minus_sat_l (hE : Extensional M) {d} (ρ : Env M d) (ω D t u : Term d) :
    Formula.satisfies ρ (tm_minus_m ω D t u) ↔
      Tm_minus_d I (ω.eval ρ) (D.eval ρ) (t.eval ρ) (u.eval ρ) := by
  simp only [tm_minus_m, Tm_minus_d, Formula.satisfies_forall_iff, Formula.satisfies_iff_iff,
    Formula.satisfies_mem_iff, Formula.satisfies_conj_iff, Formula.satisfies_exists_iff,
    tm_query_sat_l I hE, Definitional.Term.eval_weaken]; rfl

theorem tm_minus_exists_l (hZF : M.Models ZF) (ω D t : M.Domain) : ∃ u, Tm_minus_d I ω D t u := by
  let φ : UnarySchema 2 := { body := .existsE (.conj
    (tm_query_m (.bound 3) (.bound 1) .newest) (.mem .newest (.bound 2))) }
  let ρ : Env M 2 := ⟨Fin.cases t (fun _ => ω), fun _ => ω⟩
  obtain ⟨u, sep⟩ := ZF.separation_exists_d hZF φ ρ D
  refine ⟨u, fun p => (sep p).trans (and_congr_right fun _ => ?_)⟩
  simp only [φ, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff, tm_query_sat_l I hZF.1,
    Formula.satisfies_mem_iff]; rfl

theorem Tm_minus_d.unique_l (hE : Extensional M) {ω D t u v : M.Domain}
    (h : Tm_minus_d I ω D t u) (k : Tm_minus_d I ω D t v) : u = v :=
  hE.eq_of_same_members u v (fun p => (h p).trans (k p).symm)

end YesMetaZFC.SetTheory.Internal

/-! ## 查询域对公式码替换的封闭性

查询域只约束名字列，允许全部自然数公式码。这个有界条件可送到初等像，
因此目标查询不必属于旧查询的逐点像，限制算子仍可在同一名字列内往返。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}}

def Tt_slots_d (ω D : M.Domain) : Prop := ∀ p z e w,
  M.mem p D → M.mem z ω → M.mem w ω → KPair_d M p z e → ∃ q, M.mem q D ∧ KPair_d M q w e

def tt_slots_m {d} (ω D : Term d) : Formula 1 d := set[d] ⟪
  ∀ p ∈ ⌜D⌝ₛ, ∀ z ∈ ⌜ω⌝ₛ, ∀ a ∈ p, ∀ e ∈ a, ∀ w ∈ ⌜ω⌝ₛ,
    ⌜kpair0_m⌝ₚ(p, z, e) → (∃ q ∈ ⌜D⌝ₛ, ⌜kpair0_m⌝ₚ(q, w, e))⟫
derive_free_closed tt_slots_m

theorem tt_slots_delta_l {d} (ω D : Term d) : (tt_slots_m ω D).IsDelta0 :=
  .forallMem _ (.forallMem _ (.forallMem _ (.forallMem _ (.forallMem _
    (.imp (kpair0_delta_l ..) (.existsMem _ (kpair0_delta_l ..)))))))

theorem tt_slots_sat_l (hE : Extensional M) {d} (ρ : Env M d) (ω D : Term d) :
    Formula.satisfies ρ (tt_slots_m ω D) ↔ Tt_slots_d (ω.eval ρ) (D.eval ρ) := by
  simp only [tt_slots_m, Formula.satisfies_forallMem_iff, Formula.satisfies_existsMem_iff,
    Formula.satisfies_imp_iff, kpair0_sat_l hE, Definitional.Term.eval_weaken]
  constructor
  · intro h p z e w hp hz hw code
    obtain ⟨a, ha, he⟩ := (kpair_union_l M code e).mpr (Or.inr rfl)
    exact h p hp z hz a ha e he w hw code
  · intro h p hp z hz _ _ e _ w hw code
    exact h p z e w hp hz hw code

variable (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Tt_pool_d.slots_l {ω n U D : M.Domain} (h : Tt_pool_d I ω n U D) : Tt_slots_d ω D := by
  obtain ⟨N, E, _, _, prod⟩ := h
  intro p z e w hp _ hw code
  obtain ⟨z', _, e', he, cp⟩ := (prod p).mp hp
  obtain ⟨ez, ee⟩ := kpair_injective_l M cp code
  subst z' e'
  obtain ⟨q, cq⟩ := (I).total w e
  exact ⟨q, (prod q).mpr ⟨w, hw, e, he, cq⟩, cq⟩

theorem Smap_d.type_slots_l {ω X R c Y S d j D D' : M.Domain}
    (hω : M.IsOmega ω) (hX : M.TransitiveSet X) (hY : M.TransitiveSet Y) (hωX : M.mem ω X)
    (hm : Smem_d I c X R) (hn : Smem_d I d Y S) (hj : Smap_d I ω c d X Y j)
    (hD : Rd_entry_d D D' j) (h : Tt_slots_d ω D) : Tt_slots_d ω D' := by
  have hωj := hj.omega_l I hZF hω hX hY hm hn hωX
  let ρ : Env M 2 := ⟨Fin.cases D (fun _ => ω), fun _ => ω⟩
  let η : Env M 2 := ⟨Fin.cases D' (fun _ => ω), fun _ => ω⟩
  have tr := smap_delta_l I hZF hω hX hY hm hn hj (tt_slots_m (.bound 1) .newest)
    (tt_slots_m_freeClosed _ _ rfl rfl) (tt_slots_delta_l ..) ρ η (Fin.cases hD (fun _ => hωj))
  exact (tt_slots_sat_l hZF.1 η (.bound 1) .newest).mp
    (tr.mp ((tt_slots_sat_l hZF.1 ρ (.bound 1) .newest).mpr h))

end YesMetaZFC.SetTheory.Internal

/-! ## 前驱类型由同一元组在前一秩层实现

查询域不变，名字列不变；每个合法公式都有实际限制代码。
纯语法证书的正确性使所有编译结果给出同一真值，故逆像正是前一层的完整类型。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem tm_query_exists_l {ω p z e a : M.Domain} (hω : M.IsOmega ω) (hp : (I).Codes p z e)
    (hz : Sc_num_d I ω a z) : ∃ q, Tm_query_d I ω p q := by
  have code := hz
  obtain ⟨n, F, r, _, _, ha, _⟩ := code
  obtain ⟨a', m, G, u, ha', lower⟩ := sr_minus_formula_l I hZF hω ha
  obtain ⟨z', hz'⟩ := sc_num_exists_l I hZF hω ha'
  obtain ⟨q, hq⟩ := (I).total z' e
  exact ⟨q, z, e, z', hp, hq, a, a', n, F, r, m, G, u, hz, hz', ha, ha', lower⟩

theorem Tm_query_d.pool_l {ω p q n U D : M.Domain} (hω : M.IsOmega ω)
    (h : Tm_query_d I ω p q) (pool : Tt_pool_d I ω n U D) (hp : M.mem p D) : M.mem q D := by
  obtain ⟨z, e, z', cp, cq, _, a', _, _, _, _, _, _, _, hz', _⟩ := h
  obtain ⟨N, E, _, _, prod⟩ := pool
  obtain ⟨v, _, s, he, code⟩ := (prod p).mp hp
  obtain ⟨ez, ee⟩ := (I).injective code cp
  subst v s
  exact (prod q).mpr ⟨z', sc_num_natural_l I hZF hω hz', e, he, cq⟩

theorem Tm_query_d.slots_l {ω p q D : M.Domain} (hω : M.IsOmega ω)
    (h : Tm_query_d I ω p q) (slots : Tt_slots_d ω D) : M.mem p D ↔ M.mem q D := by
  obtain ⟨z, e, w, cp, cq, code⟩ := h
  have zw := code.natural_l I hZF hω
  constructor
  · intro hp
    obtain ⟨q', hq', cq'⟩ := slots p z e w hp zw.1 zw.2 cp
    exact kpair_unique_l M hZF.1 cq' cq ▸ hq'
  · intro hq
    obtain ⟨p', hp', cp'⟩ := slots q w e z hq zw.2 zw.1 cq
    exact kpair_unique_l M hZF.1 cp' cp ▸ hp'

theorem Tm_query_d.sat_l {ω c X R d Y S n s δ p q z b e a f : M.Domain}
    (hω : M.IsOmega ω) (h : Tm_query_d I ω p q)
    (hm : Smem_d I c X R) (hn : Smem_d I d Y S) (hY : M.TransitiveSet Y) (top : Sr_top_d Y X)
    (hp : (I).Codes p z e) (hz : M.mem z ω) (hb : M.mem b ω) (he : M.IsDomainOf I b e)
    (ha : Tn_assign_d n s δ e a) (hf : Senv_fill_d I ω δ b a f) (ff : Fn0_d ω X f) :
    Tt_query_d I ω c n s δ p ↔ Tt_query_d I ω d n s δ q := by
  obtain ⟨z₀, e₀, z', cp, cq, c₀, c₁, l, F, r, m, G, u, code₀, code₁, form₀, form₁, lower⟩ := h
  obtain ⟨ez, ee⟩ := (I).injective cp hp
  subst z₀ e₀
  exact (tt_query_decode_l I (ZF.modelsKP hZF) hp hz hb he ha hf).trans
    ((sc_sat_decode_l I hZF hω code₀).trans ((lower.satisfies_l I hZF hω form₀ form₁ hm hn hY top
      (fn0_function_l (ZF.modelsKP hZF) ff)).trans ((sc_sat_decode_l I hZF hω code₁).symm.trans
        (tt_query_decode_l I (ZF.modelsKP hZF) cq (sc_num_natural_l I hZF hω code₁) hb he ha hf).symm)))

/-- 最大元素给出的限制类型自动存在，且由原元组及同一常量域实现。 -/
theorem Tt_realized_d.minus_l {ω d Y S n s δ U D t X : M.Domain} (hω : M.IsOmega ω)
    (h : Tt_realized_d I ω d Y S n s δ U D t) (model : Smem_d I d Y S)
    (hY : M.TransitiveSet Y) (top : Sr_top_d Y X) (tuple : Fn0_d n X s)
    (point : M.mem δ X) (constants : M.MemberSubset U X) : ∃ c R u,
      Smem_d I c X R ∧ Tm_minus_d I ω D t u ∧ Tt_realized_d I ω c X R n s δ U D u := by
  obtain ⟨c, R, code⟩ := smdl_membership_l I hZF ⟨δ, point⟩
  obtain ⟨u, truth, _⟩ := tt_truth_exists_l I hZF ω c n s δ D
  refine ⟨c, R, u, code, ?_, ⟨code.1, h.finite, tuple, point, constants, h.pool, truth⟩⟩
  intro p
  refine (truth p).trans (and_congr_right fun hpD => ?_)
  obtain ⟨z, b, e, a, f, hp, hz, hb, he, ha, hf, ff, decode⟩ :=
    Tt_pool_d.realize_l hZF (c := c) hω h.finite tuple point constants h.pool hpD
  constructor
  · intro hp'
    obtain ⟨a₀, code₀, _⟩ := decode.mp hp'
    obtain ⟨q, hq⟩ := tm_query_exists_l hZF hω hp code₀
    exact ⟨q, hq, (h.truth q).mpr ⟨hq.pool_l hZF hω h.pool hpD,
      (hq.sat_l hZF hω code model hY top hp hz hb he ha hf ff).mp hp'⟩⟩
  · rintro ⟨q, hq, hqt⟩
    exact (hq.sat_l hZF hω code model hY top hp hz hb he ha hf ff).mpr ((h.truth q).mp hqt).2

/-- Neeman 3.5 的类型保持结论：V(η+1) 中的类型经限制后，由同一元组在 Vη 中实现。 -/
theorem tt_minus_rank_l {ω ν μ X Y d S n s δ U D t : M.Domain} (hω : M.IsOmega ω)
    (hV : V_d I ν X) (hW : V_d I μ Y) (hs : M.SuccessorOf μ ν)
    (h : Tt_realized_d I ω d Y S n s δ U D t) (model : Smem_d I d Y S)
    (tuple : Fn0_d n X s) (point : M.mem δ X) (constants : M.MemberSubset U X) : ∃ c R u,
      Smem_d I c X R ∧ Tm_minus_d I ω D t u ∧ Tt_realized_d I ω c X R n s δ U D u :=
  h.minus_l hZF hω model (v_transitive_l I hW)
    (sr_top_power_l (ZF.v_successor_l I hZF hV hW hs)) tuple point constants

/-- 缩小常量域与取前驱交换；实际构造限制后的前驱，而非另加投影存在前提。 -/
theorem tm_minus_project_l {ω D E t t₀ u : M.Domain} (hω : M.IsOmega ω)
    (small : Tt_slots_d ω D) (large : Tt_slots_d ω E) (sub : M.MemberSubset t E)
    (cut : ∀ p, M.mem p t₀ ↔ M.mem p D ∧ M.mem p t) (h : Tm_minus_d I ω E t u) :
    ∃ u₀, Tm_minus_d I ω D t₀ u₀ ∧ ∀ p, M.mem p u₀ ↔ M.mem p D ∧ M.mem p u := by
  obtain ⟨u₀, h₀⟩ := tm_minus_exists_l I hZF ω D t₀
  refine ⟨u₀, h₀, fun p => (h₀ p).trans ⟨?_, ?_⟩⟩
  · rintro ⟨hp, q, code, hq⟩
    have qt := ((cut q).mp hq).2
    exact ⟨hp, (h p).mpr ⟨(code.slots_l hZF hω large).mpr (sub q qt), q, code, qt⟩⟩
  · rintro ⟨hp, hu⟩
    obtain ⟨_, q, code, hq⟩ := (h p).mp hu
    exact ⟨hp, q, code, (cut q).mpr ⟨(code.slots_l hZF hω small).mp hp, hq⟩⟩

end YesMetaZFC.SetTheory.Internal
