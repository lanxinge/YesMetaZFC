import YesMetaZFC.Model.SetTheory.Internal.FiniteSource
import YesMetaZFC.Model.SetTheory.Internal.Support
import YesMetaZFC.Model.SetTheory.Internal.Hereditary
import YesMetaZFC.SetTheory.Notation

/-! # 全部内部程序的限制翻译

新变量 b 指向被限制的载体。语义只要求旧关系是新关系在该载体上的限制，
且新关系通过指定对象正确读取这个载体的成员；任意实际隶属子结构都满足这些最弱条件。
翻译状态保存已经处理的各行，不要求内部程序有外部有限长度。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

structure Sr_context_d (ω X R Y S H E D : M.Domain) : Prop where
  subset : M.MemberSubset X Y
  relation : ∀ x y, M.mem x X → M.mem y X → (M.PairMember I x y R ↔ M.PairMember I x y S)
  guard : ∀ x, M.mem x Y → (M.PairMember I x H S ↔ M.mem x X)
  small : M.IsFunctionSpace I E ω X
  large : M.IsFunctionSpace I D ω Y

def sr_context_m {d} (ω X R Y S H E D : Term d) : Formula 1 d := set[d] ⟪
  ⌜X⌝ₛ ⊆ ⌜Y⌝ₛ ∧
  (∀ x y, x ∈ ⌜X⌝ₛ → y ∈ ⌜X⌝ₛ →
    (⌜Formula.orderedPairMem 𝒞⌝ₚ(x, y, ⌜R⌝ₛ) ↔ ⌜Formula.orderedPairMem 𝒞⌝ₚ(x, y, ⌜S⌝ₛ))) ∧
  (∀ x, x ∈ ⌜Y⌝ₛ → (⌜Formula.orderedPairMem 𝒞⌝ₚ(x, ⌜H⌝ₛ, ⌜S⌝ₛ) ↔ x ∈ ⌜X⌝ₛ)) ∧
  ⌜Formula.isFunctionSpace 𝒞⌝ₚ(⌜E⌝ₛ, ⌜ω⌝ₛ, ⌜X⌝ₛ) ∧
  ⌜Formula.isFunctionSpace 𝒞⌝ₚ(⌜D⌝ₛ, ⌜ω⌝ₛ, ⌜Y⌝ₛ)⟫

@[simp] theorem sr_context_closed_l {d} (ω X R Y S H E D : Term d)
    (hω : ω.freeSupport = []) (hX : X.freeSupport = []) (hR : R.freeSupport = [])
    (hY : Y.freeSupport = []) (hS : S.freeSupport = []) (hH : H.freeSupport = []) (hE : E.freeSupport = []) (hD : D.freeSupport = []) :
    (sr_context_m (𝒞 := 𝒞) ω X R Y S H E D).FreeClosed := by
  simp -implicitDefEqProofs [sr_context_m, Formula.isFunctionSpace, Definitional.Formula.FreeClosed,
    hω, hX, hR, hY, hS, hH, hE, hD]

theorem sr_context_sat_l (hE : Extensional M) {d} (ρ : Env M d) (ω X R Y S H E D : Term d) :
    Formula.satisfies ρ (sr_context_m (𝒞 := 𝒞) ω X R Y S H E D) ↔
      Sr_context_d I (ω.eval ρ) (X.eval ρ) (R.eval ρ) (Y.eval ρ) (S.eval ρ) (H.eval ρ) (E.eval ρ) (D.eval ρ) := by
  simp only [sr_context_m, Formula.satisfies_conj_iff, Formula.satisfies_subset_iff,
    Formula.satisfies_forall_iff, Formula.satisfies_imp_iff, Formula.satisfies_mem_iff,
    Formula.satisfies_iff_iff, Formula.satisfies_orderedPairMem_iff I,
    Formula.satisfies_isFunctionSpace_iff I hE, Definitional.Term.eval_weaken]
  exact ⟨fun h => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2⟩,
    fun h => ⟨h.subset, h.relation, h.guard, h.small, h.large⟩⟩

theorem sr_context_l {ω c X R d Y S E D : M.Domain} (hx : Smem_d I c X R) (hy : Smem_d I d Y S)
    (hXY : M.MemberSubset X Y) (hX : M.mem X Y) (hE : M.IsFunctionSpace I E ω X)
    (hD : M.IsFunctionSpace I D ω Y) : Sr_context_d I ω X R Y S X E D := by
  refine ⟨hXY, fun x y hxX hyX => ?_, fun x hxY => ?_, hE, hD⟩
  · exact (hx.2 x y).trans ⟨fun h => (hy.2 x y).mpr ⟨hXY x hxX, hXY y hyX, h.2.2⟩,
      fun h => ⟨hxX, hyX, ((hy.2 x y).mp h).2.2⟩⟩
  · exact (hy.2 x X).trans ⟨fun h => h.2.2, fun h => ⟨hxY, hX, h⟩⟩

def Sr_row_d (b X R Y S H E D F n m G r u : M.Domain) : Prop := ∀ f g,
  M.mem f E → M.mem g D → M.PairMember I b H g → Senv_agree_d I b f g →
    (Ssat_d I X R E F n r f ↔ Ssat_d I Y S D G m u g)

def sr_row_m {d} (b X R Y S H E D F n m G r u : Term d) : Formula 1 d := set[d] ⟪
  ∀ f g, f ∈ ⌜E⌝ₛ → g ∈ ⌜D⌝ₛ → ⌜Formula.orderedPairMem 𝒞⌝ₚ(⌜b⌝ₛ, ⌜H⌝ₛ, g) →
    ⌜senv_agree_m (𝒞 := 𝒞)⌝ₚ(⌜b⌝ₛ, f, g) →
    (⌜ssat_m (𝒞 := 𝒞)⌝ₚ(⌜X⌝ₛ, ⌜R⌝ₛ, ⌜E⌝ₛ, ⌜F⌝ₛ, ⌜n⌝ₛ, ⌜r⌝ₛ, f) ↔
     ⌜ssat_m (𝒞 := 𝒞)⌝ₚ(⌜Y⌝ₛ, ⌜S⌝ₛ, ⌜D⌝ₛ, ⌜G⌝ₛ, ⌜m⌝ₛ, ⌜u⌝ₛ, g))⟫
derive_free_closed sr_row_m

theorem sr_row_sat_l (hE : Extensional M) {d} (ρ : Env M d) (b X R Y S H E D F n m G r u : Term d) :
    Formula.satisfies ρ (sr_row_m (𝒞 := 𝒞) b X R Y S H E D F n m G r u) ↔
      Sr_row_d I (b.eval ρ) (X.eval ρ) (R.eval ρ) (Y.eval ρ) (S.eval ρ) (H.eval ρ) (E.eval ρ) (D.eval ρ)
        (F.eval ρ) (n.eval ρ) (m.eval ρ) (G.eval ρ) (r.eval ρ) (u.eval ρ) := by
  simp only [sr_row_m, Sr_row_d, Formula.satisfies_forall_iff, Formula.satisfies_imp_iff,
    Formula.satisfies_mem_iff, Formula.satisfies_orderedPairMem_iff I, senv_agree_sat_l I,
    Formula.satisfies_iff_iff, ssat_sat_l I hE, Definitional.Term.eval_weaken]; rfl

structure Sr_state_d (ω b F k m G T : M.Domain) : Prop where
  program : Sfm_d I ω m G
  map : M.IsSetFunctionFromTo I T k m
  rules : ∀ r c u, M.PairMember I r c F → M.PairMember I r u T → Sr_rule_d I b T G c u

def sr_state_m {d} (ω b F k m G T : Term d) : Formula 1 d := set[d] ⟪
  ⌜sfm_m (𝒞 := 𝒞)⌝ₚ(⌜ω⌝ₛ, ⌜m⌝ₛ, ⌜G⌝ₛ) ∧
  ⌜Formula.isFunctionFromTo 𝒞⌝ₚ(⌜T⌝ₛ, ⌜k⌝ₛ, ⌜m⌝ₛ) ∧
  (∀ r c u, ⌜Formula.orderedPairMem 𝒞⌝ₚ(r, c, ⌜F⌝ₛ) → ⌜Formula.orderedPairMem 𝒞⌝ₚ(r, u, ⌜T⌝ₛ) →
    ⌜sr_rule_m (𝒞 := 𝒞)⌝ₚ(⌜b⌝ₛ, ⌜T⌝ₛ, ⌜G⌝ₛ, c, u))⟫
derive_free_closed sr_state_m

theorem sr_state_sat_l (hE : Extensional M) {d} (ρ : Env M d) (ω b F k m G T : Term d) :
    Formula.satisfies ρ (sr_state_m (𝒞 := 𝒞) ω b F k m G T) ↔
      Sr_state_d I (ω.eval ρ) (b.eval ρ) (F.eval ρ) (k.eval ρ) (m.eval ρ) (G.eval ρ) (T.eval ρ) := by
  simp only [sr_state_m, Formula.satisfies_conj_iff, sfm_sat_l I hE, Formula.satisfies_isFunctionFromTo_iff I hE,
    Formula.satisfies_forall_iff, Formula.satisfies_imp_iff,
    Formula.satisfies_orderedPairMem_iff I, sr_rule_sat_l I, Definitional.Term.eval_weaken]
  exact ⟨fun h => ⟨h.1, h.2.1, h.2.2⟩, fun h => ⟨h.program, h.map, h.rules⟩⟩

theorem Sr_state_d.extend_l {ω b F k m G T l H z : M.Domain}
    (h : Sr_state_d I ω b F k m G T) (e : Sbuild_d I ω m G l H z) : Sr_state_d I ω b F k l H T := by
  refine ⟨e.program, ⟨h.map.1, h.map.2.1, fun i hi => ?_⟩, fun r c u hc hu => ?_⟩
  · obtain ⟨u, hu, hiu⟩ := h.map.2.2 i hi
    exact ⟨u, e.span u hu, hiu⟩
  · exact (h.rules r c u hc hu).mono_l I (fun _ _ h => h) (fun i j h => ((e.cut.2 i j).mp h).2)

end YesMetaZFC.SetTheory.Internal

/-! ## 限制编译的实际语法构造

每一步只追加合法指令。存在量词的五行代码完整保留在输出证书中，
正确性另对该纯语法证书证明，编译器不把真值保持作为定义条件。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

private theorem sr_add_l (hZF : M.Models ZF) {ω m G c i j} {k : Nat} (hω : M.IsOmega ω)
    (hG : Sfm_d I ω m G) (hc : Sfm_node_d I ω m c) (hs : Sop_d I k c i j) :
    ∃ l H, Sbuild_d I ω m G l H m ∧ Sr_at_d I k H m i j := by
  obtain ⟨l, H, h, row⟩ := sfm_node_build_l I hZF hω hG hc
  exact ⟨l, H, h, c, row, hs⟩

private theorem sr_ex_syntax_l (hZF : M.Models ZF) {ω b T m G c i j v}
    (hω : M.IsOmega ω) (hG : Sfm_d I ω m G) (hc : Sop_d I 3 c i j)
    (hv : M.mem v m) (hjv : M.PairMember I j v T) (hi : M.mem i ω) (hb : M.mem b ω) :
    ∃ l H k, Sbuild_d I ω m G l H k ∧ Sr_rule_d I b T H c k := by
  obtain ⟨m₁, G₁, h₁, a₁⟩ := sr_rel_add_l I hZF hω hG hi hb
  obtain ⟨m₂, G₂, t, h₂, a₂⟩ := sr_and_build_l I hZF hω h₁.program h₁.root (h₁.span v hv)
  obtain ⟨l, H, h₃, a₃⟩ := sr_ex_add_l I hZF hω h₂.program hi h₂.root
  obtain ⟨p, q, hp, hq, ht⟩ := a₂
  exact ⟨l, H, m₂, (h₁.comp I h₂).comp I h₃,
    Or.inr (Or.inr (Or.inr ⟨i, j, v, m, p, q, t, hc, hjv,
      a₁.extend_l I (h₂.comp I h₃), hp.extend_l I h₃, hq.extend_l I h₃, ht.extend_l I h₃, a₃⟩))⟩

/-- 每个旧指令都有实际新代码，返回的纯语法规则可独立核验。 -/
theorem sr_step_l (hZF : M.Models ZF) {ω b F n r c T m G : M.Domain}
    (hω : M.IsOmega ω) (hF : Sfm_d I ω n F) (hb : M.mem b ω) (hc : M.PairMember I r c F)
    (map : M.IsSetFunctionFromTo I T r m) (hG : Sfm_d I ω m G) :
    ∃ l H u, Sbuild_d I ω m G l H u ∧ Sr_rule_d I b T H c u := by
  rcases hF.2.2 r c hc with ⟨i, j, hs, hi, hj⟩ | ⟨i, j, hs, hi, hj⟩ |
    ⟨i, j, hs, hi, hj⟩ | ⟨i, j, hs, hi, hj⟩
  · obtain ⟨l, H, h, row⟩ := sr_add_l I hZF hω hG (Or.inl ⟨i, j, hs, hi, hj⟩) hs
    exact ⟨l, H, m, h, Or.inl ⟨i, j, hs, row⟩⟩
  · obtain ⟨l, H, h, row⟩ := sr_add_l I hZF hω hG (Or.inr (Or.inl ⟨i, j, hs, hi, hj⟩)) hs
    exact ⟨l, H, m, h, Or.inr (Or.inl ⟨i, j, hs, row⟩)⟩
  · obtain ⟨u, hu, hiu⟩ := map.2.2 i hi
    obtain ⟨v, hv, hjv⟩ := map.2.2 j hj
    obtain ⟨l, H, h, row⟩ := sr_nor_add_l I hZF hω hG hu hv
    exact ⟨l, H, m, h, Or.inr (Or.inr (Or.inl ⟨i, j, u, v, hs, hiu, hjv, row⟩))⟩
  · obtain ⟨v, hv, hjv⟩ := map.2.2 j hj
    exact sr_ex_syntax_l I hZF hω hG hs hv hjv hi hb

end YesMetaZFC.SetTheory.Internal

/-! ## 完整内部程序的统一限制编译

沿模型内部 ω 逐行追加翻译，维护旧根到新根的实际图及纯语法规则。
归纳性质是可分离的原公式，不要求内部程序可解码为宿主语法树。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

theorem sr_state_append_l (hZF : M.Models ZF) {ω b F k m G T l v H z}
    (hω : M.IsOmega ω) (hk : M.mem k ω) (hl : M.SuccessorOf l k) (h : Sr_state_d I ω b F k m G T)
    (hg : Sbuild_d I ω m G v H z) (hz : ∀ c, M.PairMember I k c F → Sr_rule_d I b T H c z) :
    ∃ U, Sr_state_d I ω b F l v H U := by
  have hko := hω.members_areOrdinals (ZF.modelsKP hZF) k hk
  have seq : M.IsSequenceOfLength I T k := ⟨hko, h.map.1, h.map.2.1⟩
  obtain ⟨U, hU, val⟩ := seq.exists_append (ZF.modelsKP hZF) I
    (KP.successor_isOrdinal (ZF.modelsKP hZF) hko hl) hl (value := z)
  have into i j (h : M.PairMember I i j T) := (val i j).mpr (Or.inl h)
  refine ⟨U, hg.program, ⟨hU.2.1, hU.2.2, fun i hi => ?_⟩, fun r c u hc hu => ?_⟩
  · rcases (hl i).mp hi with hi | hi
    · obtain ⟨u, hu, hiu⟩ := h.map.2.2 i hi
      exact ⟨u, hg.span u hu, into i u hiu⟩
    · exact ⟨z, hg.root, (val i z).mpr (Or.inr ⟨hZF.1.eq_of_same_members i k hi, rfl⟩)⟩
  · rcases (val r u).mp hu with hu | ⟨rfl, rfl⟩
    · exact (h.rules r c u hc hu).mono_l I into (fun i j h => ((hg.cut.2 i j).mp h).2)
    · exact (hz c hc).mono_l I into (fun _ _ h => h)

/-- 给定新载体坐标，实际构造完整语法翻译；新坐标的支撑外条件只在正确性中使用。 -/
theorem sr_compile_at_l (hZF : M.Models ZF) {ω F n b : M.Domain}
    (hω : M.IsOmega ω) (hF : Sfm_d I ω n F) (hb : M.mem b ω) :
    ∃ m G T, Sr_state_d I ω b F n m G T := by
  let ρ : Env M 4 := ⟨Fin.cases n (Fin.cases F (Fin.cases b (fun _ => ω))), fun _ => ω⟩
  let φ : UnarySchema 4 := { body := .imp (Formula.subset .newest (.bound 1)) (.existsE (.existsE (.existsE
    (sr_state_m (𝒞 := 𝒞) (.bound 7) (.bound 6) (.bound 5) (.bound 3) (.bound 2) (.bound 1) .newest)))) }
  have sat k : φ.denote ρ k ↔ (M.MemberSubset k n → ∃ m G T, Sr_state_d I ω b F k m G T) := by
    simp only [φ, UnarySchema.denote, Formula.satisfies_imp_iff, Formula.satisfies_subset_iff,
      Formula.satisfies_exists_iff, sr_state_sat_l I hZF.1]; rfl
  have build : ∀ k, M.mem k ω → M.MemberSubset k n → ∃ m G T, Sr_state_d I ω b F k m G T := by
    apply hω.induction
    · obtain ⟨A, hA⟩ := ZF.separation_exists_d hZF φ ρ ω
      exact ⟨A, fun k => (hA k).trans (and_congr_right fun _ => sat k)⟩
    · intro e he _
      have seq := Structure.IsSequenceOfLength.empty I he
      have empty : ∀ i j, ¬ M.PairMember I i j e := fun _ _ ⟨p, _, hp⟩ => he p hp
      exact ⟨e, e, e, ⟨num_mem_l hZF.1 hω (show Num_d 0 e from he), seq,
        fun i j h => (empty i j h).elim⟩, ⟨seq.2.1, seq.2.2, fun i hi => (he i hi).elim⟩,
        fun r _ u _ h => (empty r u h).elim⟩
    · intro k hk ih l hl hln
      have hkn := hln k hl.predecessor_mem
      obtain ⟨m, G, T, state⟩ := ih (fun i hi => hln i ((hl i).mpr (Or.inl hi)))
      obtain ⟨c, hc⟩ := (hF.2.1.2.2 k).mp hkn
      obtain ⟨v, H, r, hg, rule⟩ := sr_step_l I hZF hω hF hb hc state.map state.program
      have rules d (hd : M.PairMember I k d F) : Sr_rule_d I b T H d r :=
        hF.2.1.2.1.2 k c d hc hd ▸ rule
      obtain ⟨U, hU⟩ := sr_state_append_l I hZF hω hk hl state hg rules
      exact ⟨v, H, U, hU⟩
  exact build n hF.1 (fun _ h => h)

/-- 原程序自动给出支撑外坐标、翻译程序和全部根位置的实际映射。 -/
theorem sr_compile_l (hZF : M.Models ZF) {ω F n : M.Domain} (hω : M.IsOmega ω) (hF : Sfm_d I ω n F) :
    ∃ b m G T, M.mem b ω ∧ Sbound_d I F b ∧ Sr_state_d I ω b F n m G T := by
  obtain ⟨b, hb, bound⟩ := sbound_exists_l I hZF hω hF
  obtain ⟨m, G, T, h⟩ := sr_compile_at_l I hZF hω hF hb
  exact ⟨b, m, G, T, hb, bound, h⟩

end YesMetaZFC.SetTheory.Internal

/-! ## 纯语法限制证书的完整正确性

对原程序行作内部强归纳。此证明适用于任意通过语法检查的翻译，
并不依赖构造编译器时所取的程序或追加见证。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

theorem Sr_state_d.correct_l (hZF : M.Models ZF) {ω b F n m G T X R Y S H E D r u : M.Domain}
    (hF : Sfm_d I ω n F) (bound : Sbound_d I F b) (h : Sr_state_d I ω b F n m G T)
    (context : Sr_context_d I ω X R Y S H E D) (hr : M.mem r n) (hru : M.PairMember I r u T) :
    Sr_row_d I b X R Y S H E D F n m G r u := by
  obtain ⟨V, hV⟩ := seval_exists_l I hZF X R E F hF.2.1.1
  obtain ⟨W, hW⟩ := seval_exists_l I hZF Y S D G h.program.2.1.1
  let ρ : Env M 13 := ⟨Fin.cases H (Fin.cases T (Fin.cases G (Fin.cases m (Fin.cases n (Fin.cases F (Fin.cases D
    (Fin.cases E (Fin.cases S (Fin.cases Y (Fin.cases R (Fin.cases X (fun _ => b)))))))))))), fun _ => X⟩
  let φ : UnarySchema 13 := { body := .forallE (.imp
    (Formula.orderedPairMem 𝒞 (.bound 1) .newest (.bound 3))
    (sr_row_m (𝒞 := 𝒞) (.bound 14) (.bound 13) (.bound 12) (.bound 11) (.bound 10) (.bound 2) (.bound 9) (.bound 8)
      (.bound 7) (.bound 6) (.bound 5) (.bound 4) (.bound 1) .newest)) }
  have sat k : φ.denote ρ k ↔ ∀ v, M.PairMember I k v T → Sr_row_d I b X R Y S H E D F n m G k v := by
    simp only [φ, UnarySchema.denote, Formula.satisfies_forall_iff, Formula.satisfies_imp_iff,
      Formula.satisfies_orderedPairMem_iff I, sr_row_sat_l I hZF.1]; rfl
  apply (sat r).mp (sfm_induction_l I hZF hF φ ρ ?_ hr) u hru
  intro r hr ih
  apply (sat r).mpr
  intro u hru f g hf hg hbg agree
  have ff := (context.small f).mp hf
  have gg := (context.large g).mp hg
  obtain ⟨c, hc⟩ := (hF.2.1.2.2 r).mp hr
  rcases h.rules r c u hc hru with ⟨i, j, code, d, hd, op⟩ | ⟨i, j, code, d, hd, op⟩ |
    ⟨i, j, v, w, code, hiv, hjw, d, hd, op⟩ | ⟨i, j, v, a, p, q, t, code, hjv, ha, hp, hq, ht, hu⟩
  · have refs := (hF.2.2 r c hc).refs_l I (ZF.modelsKP hZF) code
    obtain ⟨x, hx, hix⟩ := ff.2.2 i refs.1
    obtain ⟨y, hy, hjy⟩ := ff.2.2 j refs.2
    have ij := bound.operands_l I hc code
    exact ((ssat_rel_l I hZF hF hV hc code context.small hf hix hjy).trans
      (context.relation x y hx hy)).trans
      (ssat_rel_l I hZF h.program hW hd op context.large hg ((agree i x ij.1).mp hix) ((agree j y ij.2).mp hjy)).symm
  · have refs := (hF.2.2 r c hc).refs_l I (ZF.modelsKP hZF) code
    obtain ⟨x, _, hix⟩ := ff.2.2 i refs.1
    obtain ⟨y, _, hjy⟩ := ff.2.2 j refs.2
    have ij := bound.operands_l I hc code
    exact (ssat_eq_l I hZF hF hV hc code context.small hf hix hjy).trans
      (ssat_eq_l I hZF h.program hW hd op context.large hg ((agree i x ij.1).mp hix) ((agree j y ij.2).mp hjy)).symm
  · have refs := (hF.2.2 r c hc).refs_l I (ZF.modelsKP hZF) code
    rw [ssat_nor_l I hZF hF hV hc code hf, ssat_nor_l I hZF h.program hW hd op hg]
    exact not_congr (or_congr ((sat i).mp (ih i refs.1) v hiv f g hf hg hbg agree)
      ((sat j).mp (ih j refs.2) w hjw f g hf hg hbg agree))
  · obtain ⟨ca, hca, opa⟩ := ha
    obtain ⟨cp, hcp, opp⟩ := hp
    obtain ⟨cq, hcq, opq⟩ := hq
    obtain ⟨ct, hct, opt⟩ := ht
    obtain ⟨cu, hcu, opu⟩ := hu
    have refs := (hF.2.2 r c hc).refs_l I (ZF.modelsKP hZF) code
    have hbi : b ≠ i := fun eq => KP.mem_irrefl_d (ZF.modelsKP hZF) b
      (eq.symm ▸ (bound.operands_l I hc code).1)
    have body x g' (hx : M.mem x Y) (update : Senv_update_d I g i x g') :
        Ssat_d I Y S D G m t g' ↔ M.mem x X ∧ Ssat_d I Y S D G m v g' := by
      have hg' := (context.large g').mpr (update.function_l I gg refs.1 hx)
      rw [ssat_nor_l I hZF h.program hW hct opt hg', ssat_nor_l I hZF h.program hW hcp opp hg',
        ssat_nor_l I hZF h.program hW hcq opq hg', ssat_rel_l I hZF h.program hW hca opa context.large hg'
          ((update.2 i x).mpr (Or.inl ⟨rfl, rfl⟩)) ((update.2 b H).mpr (Or.inr ⟨hbi, hbg⟩)), context.guard x hx]
      simp only [or_self, not_or, Classical.not_not]
    have transport x f' g' (hx : M.mem x X) (uf : Senv_update_d I f i x f') (ug : Senv_update_d I g i x g') :
        Ssat_d I X R E F n j f' ↔ Ssat_d I Y S D G m v g' :=
      (sat j).mp (ih j refs.2) v hjv f' g'
        ((context.small f').mpr (uf.function_l I ff refs.1 hx))
        ((context.large g').mpr (ug.function_l I gg refs.1 (context.subset x hx)))
        ((ug.2 b H).mpr (Or.inr ⟨hbi, hbg⟩)) (agree.update_l I uf ug)
    rw [ssat_exists_l I hZF hF hV hc code hf, ssat_exists_l I hZF h.program hW hcu opu hg]
    constructor
    · rintro ⟨x, f', hx, uf, truth⟩
      obtain ⟨g', ug, _⟩ := senv_update_exists_l I hZF gg refs.1 (context.subset x hx)
      exact ⟨x, g', context.subset x hx, ug, (body x g' (context.subset x hx) ug).mpr
        ⟨hx, (transport x f' g' hx uf ug).mp truth⟩⟩
    · rintro ⟨x, g', hx, ug, truth⟩
      obtain ⟨hxX, truth'⟩ := (body x g' hx ug).mp truth
      obtain ⟨f', uf, _⟩ := senv_update_exists_l I hZF ff refs.1 hxX
      exact ⟨x, f', hxX, uf, (transport x f' g' hxX uf ug).mpr truth'⟩

end YesMetaZFC.SetTheory.Internal
