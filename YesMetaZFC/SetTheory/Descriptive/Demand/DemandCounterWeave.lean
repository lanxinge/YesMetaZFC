import YesMetaZFC.SetTheory.Descriptive.Game.GameAttemptRank
import YesMetaZFC.SetTheory.Descriptive.Game.GameShift
import YesMetaZFC.Model.SetTheory.Game.NodeEmbedding
import YesMetaZFC.SetTheory.Descriptive.Game.ClosedDeterminacy
import YesMetaZFC.SetTheory.Descriptive.Game.FirstViolationMonotone
import YesMetaZFC.Model.SetTheory.Game.Graph

/-! # 固定原对局的补树博弈规则

两方仍逐个选择原字母。偶数位置由论文中的 I 选择 U₁ 值，奇数位置
由 II 选择 U₂ 值；每个完整轮都检查同一个 S 节点。有限历史始终是
单张交替图，两张辅助图由精确的奇偶坐标关系读取。
-/
namespace YesMetaZFC.SetTheory.Descriptive
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (I : kpair_convention_l.Interpretation M)

def Dg_weave_d (ω h a b : M.Domain) : Prop :=
  (∀ i, M.mem i ω → ∀ x, M.PairMember I i x a ↔
    ∃ j, M.IsOrdinalAddition I j i i ∧ M.PairMember I j x h) ∧
  (∀ i, M.mem i ω → ∀ x, M.PairMember I i x b ↔
    ∃ j l, M.IsOrdinalAddition I j i i ∧ M.SuccessorOf l j ∧ M.PairMember I l x h)

def dg_weave_m {d} (ω h a b : Term d) : Formula 1 d := set[d] ⟪
  (∀ i ∈ ⌜ω⌝ₛ, ∀ x, ⌜Formula.orderedPairMem kpair_convention_l⌝ₚ(i,x,⌜a⌝ₛ) ↔
    ∃ j, ⌜Formula.isOrdinalAddition kpair_convention_l⌝ₚ(j,i,i) ∧
      ⌜Formula.orderedPairMem kpair_convention_l⌝ₚ(j,x,⌜h⌝ₛ)) ∧
  (∀ i ∈ ⌜ω⌝ₛ, ∀ x, ⌜Formula.orderedPairMem kpair_convention_l⌝ₚ(i,x,⌜b⌝ₛ) ↔
    ∃ j l, ⌜Formula.isOrdinalAddition kpair_convention_l⌝ₚ(j,i,i) ∧
      ⌜Formula.isSuccessor⌝ₚ(l,j) ∧ ⌜Formula.orderedPairMem kpair_convention_l⌝ₚ(l,x,⌜h⌝ₛ))⟫
derive_free_closed dg_weave_m

theorem dg_weave_sat_l (hE : Extensional M) {d} (ρ : Env M d) (ω h a b : Term d) :
    Formula.satisfies ρ (dg_weave_m ω h a b) ↔ Dg_weave_d I (ω.eval ρ) (h.eval ρ) (a.eval ρ) (b.eval ρ) := by
  simp only [dg_weave_m,Dg_weave_d,Formula.satisfies_conj_iff,Formula.satisfies_forallMem_iff,
    Formula.satisfies_forall_iff,Formula.satisfies_iff_iff,Formula.satisfies_exists_iff,
    Formula.satisfies_orderedPairMem_iff I,Formula.satisfies_isOrdinalAddition_iff I hE,
    Formula.satisfies_isSuccessor_iff,Definitional.Term.eval_weaken]
  rfl

def Dg_round_d (ω U₁ U₂ x S n h : M.Domain) : Prop := ∃ k s a b,
  M.mem k ω ∧ M.IsOrdinalAddition I n k k ∧ Fn0_d k U₁ a ∧ Fn0_d k U₂ b ∧
    M.IsRestrictionOf I s x k ∧ Tg_node_d I k S s a b ∧ Dg_weave_d I ω h a b

def dg_round_m {d} (ω U₁ U₂ x S n h : Term d) : Formula 1 d := set[d] ⟪∃ k s a b,
  k ∈ ⌜ω⌝ₛ ∧ ⌜Formula.isOrdinalAddition kpair_convention_l⌝ₚ(⌜n⌝ₛ,k,k) ∧
    ⌜fn0_m⌝ₚ(k,⌜U₁⌝ₛ,a) ∧ ⌜fn0_m⌝ₚ(k,⌜U₂⌝ₛ,b) ∧
    ⌜Formula.isRestriction kpair_convention_l⌝ₚ(s,⌜x⌝ₛ,k) ∧
    ⌜tg_node_m⌝ₚ(k,⌜S⌝ₛ,s,a,b) ∧ ⌜dg_weave_m⌝ₚ(⌜ω⌝ₛ,⌜h⌝ₛ,a,b)⟫
derive_free_closed dg_round_m

theorem dg_round_sat_l (hE : Extensional M) {d} (ρ : Env M d) (ω U₁ U₂ x S n h : Term d) :
    Formula.satisfies ρ (dg_round_m ω U₁ U₂ x S n h) ↔
      Dg_round_d I (ω.eval ρ) (U₁.eval ρ) (U₂.eval ρ) (x.eval ρ) (S.eval ρ) (n.eval ρ) (h.eval ρ) := by
  simp only [dg_round_m,Dg_round_d,Formula.satisfies_exists_iff,Formula.satisfies_conj_iff,
    Formula.satisfies_mem_iff,Formula.satisfies_isOrdinalAddition_iff I hE,fn0_sat_l hE,
    Formula.satisfies_isRestriction_iff I,tg_node_sat_l I hE,dg_weave_sat_l I hE,Definitional.Term.eval_weaken]
  rfl

def Dg_check_d (ω V U₁ U₂ x S h : M.Domain) : Prop := ∃ n,
  M.mem n ω ∧ Fn0_d n V h ∧ ((∀ y, ¬ M.mem y n) ∨ ∃ m z,
    M.SuccessorOf n m ∧ M.PairMember I m z h ∧
      ((Gm_even_d I ω m ∧ M.mem z U₁) ∨
        (¬ Gm_even_d I ω m ∧ M.mem z U₂ ∧ Dg_round_d I ω U₁ U₂ x S n h)))

def dg_check_m {d} (ω V U₁ U₂ x S h : Term d) : Formula 1 d := set[d] ⟪∃ n ∈ ⌜ω⌝ₛ,
  ⌜fn0_m⌝ₚ(n,⌜V⌝ₛ,⌜h⌝ₛ) ∧ (⌜Formula.isEmpty⌝ₚ(n) ∨ (∃ m z,
    ⌜Formula.isSuccessor⌝ₚ(n,m) ∧ ⌜Formula.orderedPairMem kpair_convention_l⌝ₚ(m,z,⌜h⌝ₛ) ∧
      ((⌜gm_even_m (𝒞 := kpair_convention_l)⌝ₚ(⌜ω⌝ₛ,m) ∧ z ∈ ⌜U₁⌝ₛ) ∨
        (¬ ⌜gm_even_m (𝒞 := kpair_convention_l)⌝ₚ(⌜ω⌝ₛ,m) ∧ z ∈ ⌜U₂⌝ₛ ∧
          ⌜dg_round_m⌝ₚ(⌜ω⌝ₛ,⌜U₁⌝ₛ,⌜U₂⌝ₛ,⌜x⌝ₛ,⌜S⌝ₛ,n,⌜h⌝ₛ)))))⟫
derive_free_closed dg_check_m

theorem dg_check_sat_l (hE : Extensional M) {d} (ρ : Env M d) (ω V U₁ U₂ x S h : Term d) :
    Formula.satisfies ρ (dg_check_m ω V U₁ U₂ x S h) ↔
      Dg_check_d I (ω.eval ρ) (V.eval ρ) (U₁.eval ρ) (U₂.eval ρ) (x.eval ρ) (S.eval ρ) (h.eval ρ) := by
  simp only [dg_check_m,Dg_check_d,Formula.satisfies_existsMem_iff,Formula.satisfies_conj_iff,
    fn0_sat_l hE,Formula.satisfies_disj_iff,Formula.satisfies_isEmpty_iff,Formula.satisfies_exists_iff,
    Formula.satisfies_isSuccessor_iff,Formula.satisfies_orderedPairMem_iff I,gm_even_sat_l I hE,
    Formula.satisfies_mem_iff,Formula.satisfies_neg_iff,dg_round_sat_l I hE,Definitional.Term.eval_weaken]
  rfl

end YesMetaZFC.SetTheory.Descriptive

/-! ## 补树博弈的实际检查集、闭收益及控制

底层 Cg 的 true 方对应论文 G(¬Sₓ) 中的 II，因此负责奇数时刻。
全部合法的无限对局归该方；另一方在偶数时刻选择 U₁ 字母。
检查、合法历史、收益和策略控制均由同一组集合实际生成。
-/
namespace YesMetaZFC.SetTheory.Descriptive
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

structure Dg_counter_d (ω U₁ U₂ x S V F L G J B W O : M.Domain) : Prop where
  alphabet : ∀ z, M.mem z V ↔ M.mem z U₁ ∨ M.mem z U₂
  space : Fseq_space_d I ω V F
  checks : ∀ h, M.mem h L ↔ M.mem h F ∧ Dg_check_d I ω V U₁ U₂ x S h
  legal : Cg_legal_d F L G
  turns : ∀ n, M.mem n J ↔ M.mem n ω ∧ ¬ Gm_even_d I ω n
  runs : M.IsFunctionSpace I B ω V
  payoff : Cg_payoff_d ω V F L J B W
  complement : ∀ f, M.mem f O ↔ M.mem f B ∧ ¬ M.mem f W
  opened : Open_d F B O

theorem dg_counter_l {ω : M.Domain} (hw : M.IsOmega ω) (U₁ U₂ x S : M.Domain) :
    ∃ V F L G J B W O, Dg_counter_d hZF ω U₁ U₂ x S V F L G J B W O := by
  obtain ⟨V,alphabet⟩ := KP.exists_unionOfTwo (ZF.modelsKP hZF) U₁ U₂
  obtain ⟨F,space⟩ := ZF.fseq_space_exists_l I hZF hw V
  let ρ : Env M 6 := ⟨fun i => [ω,V,U₁,U₂,x,S].get i,fun _ => ω⟩
  let φ : UnarySchema 6 := { body := dg_check_m (.bound 1) (.bound 2) (.bound 3) (.bound 4) (.bound 5) (.bound 6) .newest }
  obtain ⟨L,ls⟩ := ZF.separation_exists_d hZF φ ρ F
  have checks h : M.mem h L ↔ M.mem h F ∧ Dg_check_d I ω V U₁ U₂ x S h :=
    (ls h).trans (and_congr_right fun _ => dg_check_sat_l I hZF.1 ..)
  obtain ⟨G,legal,_⟩ := cg_legal_l (ZF.modelsKP hZF) F L
  let ψ : UnarySchema 1 := { body := .neg (gm_even_m (𝒞 := kpair_convention_l) (.bound 1) .newest) }
  obtain ⟨J,js⟩ := ZF.separation_exists_d hZF ψ ⟨fun _ => ω,fun _ => ω⟩ ω
  have turns n : M.mem n J ↔ M.mem n ω ∧ ¬ Gm_even_d I ω n := by
    apply (js n).trans (and_congr_right fun _ => ?_)
    simp only [ψ,Formula.satisfies_neg_iff,gm_even_sat_l I hZF.1]
    rfl
  obtain ⟨B,runs⟩ := ZF.exists_functionSpace hZF I ω V
  obtain ⟨W,O,payoff,complement,opened⟩ := cg_payoff_l hZF ω V F L J B
  exact ⟨V,F,L,G,J,B,W,O,alphabet,space,checks,legal,turns,runs,payoff,complement,opened⟩

variable {ω U₁ U₂ x S V F L G J B W O : M.Domain}

/-- 检查空局面只用真实空图，原树可以尚无空节点。 -/
theorem Dg_counter_d.root_l (h : Dg_counter_d hZF ω U₁ U₂ x S V F L G J B W O)
    (hw : M.IsOmega ω) {e : M.Domain} (empty : ∀ y, ¬ M.mem y e) : M.mem e G := by
  have he := num_mem_l hZF.1 hw (show Num_d 0 e from empty)
  have fe : Fn0_d e V e := ⟨fun p hp => (empty p hp).elim,
    fun i hi => (empty i hi).elim,fun i hi => (empty i hi).elim⟩
  refine (h.legal e).mpr ⟨(h.space e).mpr ⟨e,he,fn0_function_l (ZF.modelsKP hZF) fe⟩,?_⟩
  intro q hq sub
  have fq : Fn0_d e V q := ⟨fun p hp => (empty p (sub p hp)).elim,
    fun i hi => (empty i hi).elim,fun i hi => (empty i hi).elim⟩
  exact (h.checks q).mpr ⟨hq,e,he,fq,Or.inl empty⟩

/-- 对指定真实获胜策略分离其合法服从历史，不重新选择策略。 -/
theorem Dg_counter_d.control_l (h : Dg_counter_d hZF ω U₁ U₂ x S V F L G J B W O)
    (hw : M.IsOmega ω) {τ : M.Domain} (win : Cg_win_d I true ω V F J B W τ) :
    ∃ e R, (∀ y, ¬ M.mem y e) ∧ Cg_control_d I true ω e V F L G J τ R := by
  obtain ⟨e,empty,_⟩ := hw.1.1
  obtain ⟨R,control⟩ := cg_control_l hZF hw empty h.space h.legal (h.root_l hZF hw empty) h.runs h.payoff win
  exact ⟨e,R,empty,control⟩

/-- 只要已有一个实际可选字母，闭博弈定理就生产其中一方的真实胜策。 -/
theorem Dg_counter_d.determined_l (hZFC : M.Models ZFC)
    (h : Dg_counter_d (ZFC.models_zf_l hZFC) ω U₁ U₂ x S V F L G J B W O)
    (hw : M.IsOmega ω) {a : M.Domain} (ha : M.mem a V) :
    Cg_det_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) ω V F J B W := by
  have subset : M.MemberSubset W B := fun f hf => h.payoff.elim fun _ h => h.elim fun _ h => ((h.2.2 f).mp hf).1
  exact cg_closed_det_l hZFC hw h.space h.runs ha subset h.complement h.opened

end YesMetaZFC.SetTheory.Descriptive

/-! ## 补树游戏及其先手获胜参数的原公式

所有量词读取实际检查集、时刻集和首次违规收益。先手获胜谓词指向
同一具体游戏，供原对局参数集合的分离及泛型扩张中的原生读取。
-/
namespace YesMetaZFC.SetTheory.Descriptive
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

@[simp] private theorem dg_space_closed_l {d} (B ω V : Term d)
    (hB : B.freeSupport = []) (hw : ω.freeSupport = []) (hV : V.freeSupport = []) :
    (Formula.isFunctionSpace kpair_convention_l B ω V).FreeClosed := by
  simp -implicitDefEqProofs [Formula.isFunctionSpace,Definitional.Formula.FreeClosed,hB,hw,hV]

def dg_counter_m {d} (ω U₁ U₂ x S V F L G J B W O : Term d) : Formula 1 d := set[d] ⟪
  (∀ z, z ∈ ⌜V⌝ₛ ↔ z ∈ ⌜U₁⌝ₛ ∨ z ∈ ⌜U₂⌝ₛ) ∧
  ⌜(fseq_space_m (𝒞 := kpair_convention_l))⌝ₚ(⌜ω⌝ₛ,⌜V⌝ₛ,⌜F⌝ₛ) ∧
  (∀ h, h ∈ ⌜L⌝ₛ ↔ h ∈ ⌜F⌝ₛ ∧ ⌜dg_check_m⌝ₚ(⌜ω⌝ₛ,⌜V⌝ₛ,⌜U₁⌝ₛ,⌜U₂⌝ₛ,⌜x⌝ₛ,⌜S⌝ₛ,h)) ∧
  ⌜cg_legal_m⌝ₚ(⌜F⌝ₛ,⌜L⌝ₛ,⌜G⌝ₛ) ∧
  (∀ n, n ∈ ⌜J⌝ₛ ↔ n ∈ ⌜ω⌝ₛ ∧ ¬ ⌜(gm_even_m (𝒞 := kpair_convention_l))⌝ₚ(⌜ω⌝ₛ,n)) ∧
  ⌜(Formula.isFunctionSpace kpair_convention_l)⌝ₚ(⌜B⌝ₛ,⌜ω⌝ₛ,⌜V⌝ₛ) ∧
  ⌜cg_payoff_m⌝ₚ(⌜ω⌝ₛ,⌜V⌝ₛ,⌜F⌝ₛ,⌜L⌝ₛ,⌜J⌝ₛ,⌜B⌝ₛ,⌜W⌝ₛ) ∧
  (∀ f, f ∈ ⌜O⌝ₛ ↔ f ∈ ⌜B⌝ₛ ∧ ¬ f ∈ ⌜W⌝ₛ) ∧ ⌜open_m⌝ₚ(⌜F⌝ₛ,⌜B⌝ₛ,⌜O⌝ₛ)⟫
derive_free_closed dg_counter_m

theorem dg_counter_sat_l {d} (ρ : Env M d) (ω U₁ U₂ x S V F L G J B W O : Term d) :
    Formula.satisfies ρ (dg_counter_m ω U₁ U₂ x S V F L G J B W O) ↔
      Dg_counter_d hZF (ω.eval ρ) (U₁.eval ρ) (U₂.eval ρ) (x.eval ρ) (S.eval ρ)
        (V.eval ρ) (F.eval ρ) (L.eval ρ) (G.eval ρ) (J.eval ρ) (B.eval ρ) (W.eval ρ) (O.eval ρ) := by
  simp only [dg_counter_m,Formula.satisfies_conj_iff,Formula.satisfies_forall_iff,
    Formula.satisfies_iff_iff,Formula.satisfies_mem_iff,Formula.satisfies_disj_iff,
    fseq_space_sat_l I hZF.1,dg_check_sat_l I hZF.1,cg_legal_sat_l,Formula.satisfies_neg_iff,
    gm_even_sat_l I hZF.1,Formula.satisfies_isFunctionSpace_iff I hZF.1,
    cg_payoff_sat_l hZF.1,open_sat_l,Definitional.Term.eval_weaken]
  exact ⟨fun ⟨a,b,c,d,e,f,g,h,i⟩ => ⟨a,b,c,d,e,f,g,h,i⟩,
    fun h => ⟨h.alphabet,h.space,h.checks,h.legal,h.turns,h.runs,h.payoff,h.complement,h.opened⟩⟩

/-- 论文的 a(¬S) 成员谓词：原补树游戏中 I 获胜。 -/
def Dg_first_win_d (ω U₁ U₂ S x : M.Domain) : Prop := ∃ V F L G J B W O τ,
  Dg_counter_d hZF ω U₁ U₂ x S V F L G J B W O ∧ Cg_win_d I false ω V F J B W τ

def dg_first_win_m {d} (ω U₁ U₂ S x : Term d) : Formula 1 d := set[d] ⟪∃ V F L G J B W O τ,
  ⌜dg_counter_m⌝ₚ(⌜ω⌝ₛ,⌜U₁⌝ₛ,⌜U₂⌝ₛ,⌜x⌝ₛ,⌜S⌝ₛ,V,F,L,G,J,B,W,O) ∧
    ⌜(cg_win_m false)⌝ₚ(⌜ω⌝ₛ,V,F,J,B,W,τ)⟫
derive_free_closed dg_first_win_m

theorem dg_first_win_sat_l {d} (ρ : Env M d) (ω U₁ U₂ S x : Term d) :
    Formula.satisfies ρ (dg_first_win_m ω U₁ U₂ S x) ↔
      Dg_first_win_d hZF (ω.eval ρ) (U₁.eval ρ) (U₂.eval ρ) (S.eval ρ) (x.eval ρ) := by
  simp only [dg_first_win_m,Dg_first_win_d,Formula.satisfies_exists_iff,Formula.satisfies_conj_iff,
    dg_counter_sat_l hZF,cg_win_sat_l I hZF.1,Definitional.Term.eval_weaken]
  rfl

/-- 实际分离先手获胜参数集合；输入范围是给定模型自己的对局空间。 -/
theorem dg_first_win_set_l (ω U₁ U₂ S B : M.Domain) :
    ∃ A, ∀ x, M.mem x A ↔ M.mem x B ∧ Dg_first_win_d hZF ω U₁ U₂ S x := by
  let ρ : Env M 4 := ⟨fun i => [ω,U₁,U₂,S].get i,fun _ => ω⟩
  let φ : UnarySchema 4 := { body := dg_first_win_m (.bound 1) (.bound 2) (.bound 3) (.bound 4) .newest }
  obtain ⟨A,read⟩ := ZF.separation_exists_d hZF φ ρ B
  exact ⟨A,fun x => (read x).trans (and_congr_right fun _ => dg_first_win_sat_l hZF ..)⟩

end YesMetaZFC.SetTheory.Descriptive

/-! ## 原先手胜策在完整轮后的实际挑战

在服从胜策的合法历史上，先手自己的落子必须仍合法。
因此偶数位置读出的实际字母确属第一辅助字母域。
-/
namespace YesMetaZFC.SetTheory.Descriptive
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Dg_counter_d.first_round_l {ω U₁ U₂ x S V F L G J B W O e σ R n h : M.Domain}
    (game : Dg_counter_d hZF ω U₁ U₂ x S V F L G J B W O) (hw : M.IsOmega ω)
    (control : Cg_control_d I false ω e V F L G J σ R)
    (hn : M.mem n ω) (fh : Fn0_d n V h) (hh : M.mem h R) (even : Gm_even_d I ω n) :
    ∃ m t d, M.mem m ω ∧ M.SuccessorOf m n ∧ Fn0_d m V t ∧ M.mem t R ∧
      Fseq_end_d I ω t h d ∧ M.mem d U₁ := by
  have hf := (game.space h).mpr ⟨n,hn,fn0_function_l (ZF.modelsKP hZF) fh⟩
  obtain ⟨d,hd,value⟩ := control.strategy.2.1 h hf
  obtain ⟨m,t,hm,ft,end'⟩ := ZF.fseq_end_exists_l I hZF hw hn (fn0_function_l (ZF.modelsKP hZF) fh) hd
  have own : ¬ M.mem n J := fun h => ((game.turns n).mp h).2 even
  have ht := control.step n h d t hn hh hd fh end' (Or.inr ⟨own,value⟩)
  have data := end'
  obtain ⟨m₀,n₀,data⟩ := data
  have eq := data.prefix_sequence.2.2.2.eq hZF.1 (fn0_function_l (ZF.modelsKP hZF) fh).2.1
  have eq' := data.source.2.2.2.eq hZF.1 ft.2.1
  subst n₀ m₀
  obtain ⟨l,_,fl,check⟩ := ((game.checks t).mp (game.legal.current_l ((control.positions t).mp ht).1)).2
  have eq := fl.domain_eq_l hZF.1 (fn0_of_function_l (ZF.modelsKP hZF) ft)
  subst l
  refine ⟨m,t,d,hm,data.length_successor,fn0_of_function_l (ZF.modelsKP hZF) ft,ht,end',?_⟩
  rcases check with no | ⟨i,z,succ,iz,rule⟩
  · exact (no n data.length_successor.predecessor_mem).elim
  · have eq := data.length_successor.predecessor_eq hZF.1 (hw.members_areOrdinals (ZF.modelsKP hZF) n hn) succ
    subst i
    have eq := ft.1.2 n z d iz data.last_value
    subst z
    exact rule.elim And.right (fun h => (h.1 even).elim)

end YesMetaZFC.SetTheory.Descriptive

/-! ## 辅助坐标不变的节点运输保持补树先手胜策

允许更多 II 回复只会使辅助先手更难获胜。因此较宽树上的同一先手
胜策也赢较窄树；实数前缀可由给定的实际节点运输一并替换。
-/
namespace YesMetaZFC.SetTheory.Descriptive
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Dg_first_win_d.mono_nodes_l {ω U₁ U₂ S T x y : M.Domain} (hw : M.IsOmega ω)
    (nodes : ∀ n s a b, M.mem n ω → M.IsRestrictionOf I s y n → Tg_node_d I n S s a b →
      ∃ t, M.IsRestrictionOf I t x n ∧ Tg_node_d I n T t a b)
    (winning : Dg_first_win_d hZF ω U₁ U₂ T x) : Dg_first_win_d hZF ω U₁ U₂ S y := by
  obtain ⟨V,F,L,G,J,B,W,O,σ,game,win⟩ := winning
  obtain ⟨V',F',L',G',J',B',W',O',old⟩ := dg_counter_l hZF hw U₁ U₂ y S
  have eq := hZF.1.eq_of_same_members V' V (fun z => (old.alphabet z).trans (game.alphabet z).symm)
  subst V'
  have eq := hZF.1.eq_of_same_members F' F (fun s => (old.space s).trans (game.space s).symm)
  subst F'
  have eq := hZF.1.eq_of_same_members J' J (fun n => (old.turns n).trans (game.turns n).symm)
  subst J'
  have eq := hZF.1.eq_of_same_members B' B (fun f => (old.runs f).trans (game.runs f).symm)
  subst B'
  have sub : M.MemberSubset L' L := by
    intro h hh
    obtain ⟨hf,n,hn,fn,rest⟩ := (old.checks h).mp hh
    refine (game.checks h).mpr ⟨hf,n,hn,fn,?_⟩
    rcases rest with zero | ⟨m,z,succ,mz,turn⟩
    · exact Or.inl zero
    · refine Or.inr ⟨m,z,succ,mz,?_⟩
      rcases turn with even | ⟨odd,hz,k,s,a,b,hk,twice,fa,fb,cut,node,weave⟩
      · exact Or.inl even
      · obtain ⟨t,cut',node'⟩ := nodes k s a b hk cut node
        exact Or.inr ⟨odd,hz,k,t,a,b,hk,twice,fa,fb,cut',node',weave⟩
  have unchanged i j p (hj : M.mem j ω) (fp : Fn0_d j V p) (succ : M.SuccessorOf j i)
      (turn : ¬ M.mem i J) (valid : M.mem p L) : M.mem p L' := by
    obtain ⟨hp,n,hn,fn,check⟩ := (game.checks p).mp valid
    have eq := fn.domain_eq_l hZF.1 fp
    subst n
    refine (old.checks p).mpr ⟨hp,j,hj,fp,?_⟩
    rcases check with empty | ⟨m,z,sm,mz,check⟩
    · exact (empty i succ.predecessor_mem).elim
    · have hi := hw.transitive (ZF.modelsKP hZF) j hj i succ.predecessor_mem
      have eq := succ.predecessor_eq hZF.1 (hw.members_areOrdinals (ZF.modelsKP hZF) i hi) sm
      subst m
      have even : Gm_even_d I ω i := Classical.byContradiction (fun odd => turn ((game.turns i).mpr ⟨hi,odd⟩))
      have hz := check.elim And.right (fun h => (h.1 even).elim)
      exact Or.inr ⟨i,z,succ,mz,Or.inl ⟨even,hz⟩⟩
  have zero p (hp : M.mem p F) (empty : ∀ x, ¬ M.mem x p) : M.mem p L' := by
    obtain ⟨e,he,heω⟩ := hw.1.1
    have fp : Fn0_d e V p := ⟨fun q hq => (empty q hq).elim,
      fun i hi => (he i hi).elim,fun i hi => (he i hi).elim⟩
    exact (old.checks p).mpr ⟨hp,e,heω,fp,Or.inl he⟩
  refine ⟨V,F,L',G',J,B,W',O',σ,old,win.1,?_⟩
  intro f hf follows hW
  exact win.2 f hf follows (old.payoff.mono_l hZF game.payoff hw game.space ((game.runs f).mp hf).1
    hf zero sub unchanged hW)

end YesMetaZFC.SetTheory.Descriptive

/-! ## 补树胜策对指定挑战的真实回复

先把实际 z∈U₁ 追加到原有限对局，再读取同一胜策的值并追加。
胜策控制保证两个历史都合法；第二次检查实际产生完整 S 节点，
没有把对手回复或节点保持作为额外的闭包参数。
-/
namespace YesMetaZFC.SetTheory.Descriptive
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Dg_counter_d.reply_round_l
    {ω U₁ U₂ x S V F L G J B W O e τ R n h z : M.Domain}
    (game : Dg_counter_d hZF ω U₁ U₂ x S V F L G J B W O) (hw : M.IsOmega ω)
    (control : Cg_control_d I true ω e V F L G J τ R)
    (hn : M.mem n ω) (fh : Fn0_d n V h) (hh : M.mem h R)
    (even : Gm_even_d I ω n) (hz : M.mem z U₁) :
    ∃ m n' h₁ h₂ z', M.mem m ω ∧ M.mem n' ω ∧ M.SuccessorOf m n ∧ M.SuccessorOf n' m ∧
      Fn0_d m V h₁ ∧ Fn0_d n' V h₂ ∧ M.mem h₁ R ∧ M.mem h₂ R ∧
      Fseq_end_d I ω h₁ h z ∧ Fseq_end_d I ω h₂ h₁ z' ∧
      Rd_entry_d h₁ z' τ ∧ M.mem z' U₂ ∧ Dg_round_d I ω U₁ U₂ x S n' h₂ := by
  have hzV := (game.alphabet z).mpr (Or.inl hz)
  obtain ⟨m,h₁,hm,f₁,end₁⟩ := ZF.fseq_end_exists_l I hZF hw hn (fn0_function_l (ZF.modelsKP hZF) fh) hzV
  have data₁ := end₁
  obtain ⟨m₀,n₀,d₁⟩ := data₁
  have eqn := d₁.prefix_sequence.2.2.2.eq hZF.1 (fn0_function_l (ZF.modelsKP hZF) fh).2.1
  have eqm := d₁.source.2.2.2.eq hZF.1 f₁.2.1
  subst n₀ m₀
  have h₁F := (game.space h₁).mpr ⟨m,hm,f₁⟩
  have check₁ : M.mem h₁ L := (game.checks h₁).mpr
    ⟨h₁F,m,hm,fn0_of_function_l (ZF.modelsKP hZF) f₁,
      Or.inr ⟨n,z,d₁.length_successor,d₁.last_value,Or.inl ⟨even,hz⟩⟩⟩
  have notOwn : ¬ M.mem n J := fun own => ((game.turns n).mp own).2 even
  have h₁R := control.step n h z h₁ hn hh hzV fh end₁ (Or.inl ⟨notOwn,check₁⟩)
  obtain ⟨z',hz'V,value⟩ := control.strategy.2.1 h₁ h₁F
  obtain ⟨n',h₂,hn',f₂,end₂⟩ := ZF.fseq_end_exists_l I hZF hw hm f₁ hz'V
  have data₂ := end₂
  obtain ⟨n₁,m₁,d₂⟩ := data₂
  have eqm := d₂.prefix_sequence.2.2.2.eq hZF.1 f₁.2.1
  have eqn := d₂.source.2.2.2.eq hZF.1 f₂.2.1
  subst m₁ n₁
  have odd : ¬ Gm_even_d I ω m := fun hmEven =>
    ((gm_even_successor_l I hZF hw hn d₁.length_successor).mp hmEven) even
  have own : M.mem m J := (game.turns m).mpr ⟨hm,odd⟩
  have h₂R := control.step m h₁ z' h₂ hm h₁R hz'V (fn0_of_function_l (ZF.modelsKP hZF) f₁)
    end₂ (Or.inr ⟨own,value⟩)
  have check₂ := ((game.checks h₂).mp (game.legal.current_l ((control.positions h₂).mp h₂R).1)).2
  obtain ⟨l,_,fl,check₂⟩ := check₂
  have eq := fl.domain_eq_l hZF.1 (fn0_of_function_l (ZF.modelsKP hZF) f₂)
  subst l
  have good : M.mem z' U₂ ∧ Dg_round_d I ω U₁ U₂ x S n' h₂ := by
    rcases check₂ with empty | ⟨i,y,succ,point,checks⟩
    · exact (empty m d₂.length_successor.predecessor_mem).elim
    · have eq : m = i := d₂.length_successor.predecessor_eq hZF.1
        (hw.members_areOrdinals (ZF.modelsKP hZF) m hm) succ
      subst i
      have eq := f₂.1.2 m y z' point d₂.last_value
      subst y
      exact checks.elim (fun h => (odd h.1).elim) And.right
  exact ⟨m,n',h₁,h₂,z',hm,hn',d₁.length_successor,d₂.length_successor,
    fn0_of_function_l (ZF.modelsKP hZF) f₁,fn0_of_function_l (ZF.modelsKP hZF) f₂,
    h₁R,h₂R,end₁,end₂,value,good⟩

end YesMetaZFC.SetTheory.Descriptive

/-! ## 同一对手回复使两张原辅助图各精确增加一点

交替历史的包含逐点传给两张图；自然数加倍的单射性把新检查中的
轮数识别为旧轮后继。指定挑战和实际策略回复分别成为两个新末值。
-/
namespace YesMetaZFC.SetTheory.Descriptive
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem dg_twice_inj_l {ω i j n : M.Domain} (hw : M.IsOmega ω)
    (hi : M.mem i ω) (hj : M.mem j ω)
    (left : M.IsOrdinalAddition I n i i) (right : M.IsOrdinalAddition I n j j) : i = j := by
  have ord := hw.members_areOrdinals (ZF.modelsKP hZF)
  have strict {i j a b} (hi : M.mem i ω) (hj : M.mem j ω) (ij : M.mem i j)
      (ha : M.IsOrdinalAddition I a i i) (hb : M.IsOrdinalAddition I b j j) : M.mem a b := by
    obtain ⟨p,hp,_⟩ := ZF.ordinalAddition_existsUnique hZF I i (ord j hj)
    obtain ⟨q,hq,_⟩ := ZF.ordinalAddition_existsUnique hZF I j (ord i hi)
    have eq := Structure.natural_add_comm hZF I hw hi hj hp hq
    have ap := ZF.ordinalAddition_isIncreasingOnOrdinals hZF I (ord i hi) i j (ord i hi) (ord j hj) ij a p ha hp
    have qb := ZF.ordinalAddition_isIncreasingOnOrdinals hZF I (ord j hj) i j (ord i hi) (ord j hj) ij q b hq hb
    exact (ZF.ordinalAddition_isOrdinal hZF I (ord j hj) (ord j hj) hb).transitive q qb a (eq ▸ ap)
  rcases (hw.isOrdinal (ZF.modelsKP hZF)).wellOrder.linear.compare i hi j hj with eq | ij | ji
  · exact hZF.1.eq_of_same_members i j eq
  · exact (KP.mem_irrefl_d (ZF.modelsKP hZF) n (strict hi hj ij left right)).elim
  · exact (KP.mem_irrefl_d (ZF.modelsKP hZF) n (strict hj hi ji right left)).elim

theorem dg_twice_next_l {ω k l n m r : M.Domain} (hw : M.IsOmega ω)
    (hk : M.mem k ω) (sk : M.SuccessorOf l k) (sn : M.SuccessorOf m n)
    (sm : M.SuccessorOf r m) (add : M.IsOrdinalAddition I n k k) : M.IsOrdinalAddition I r l l := by
  have ok := hw.members_areOrdinals (ZF.modelsKP hZF) k hk
  obtain ⟨p,hp,_⟩ := ZF.ordinalAddition_existsUnique hZF I l ok
  have next := Structure.natural_add_left_successor hZF I hw hk sk hk add hp
  have eq := next.eq hZF.1 sn
  exact (ZF.ordinalAddition_successor_iff hZF I ok sk).mpr ⟨m,eq ▸ hp,sm⟩

/-- 图包含只沿同一奇偶读取方程传递，不要求新旧图的坐标排序。 -/
theorem Dg_weave_d.subset_l (J : kpair_convention_l.Interpretation M)
    {ω k h h' a b a' b' : M.Domain} (old : Dg_weave_d J ω h a b) (next : Dg_weave_d J ω h' a' b')
    (hk : M.MemberSubset k ω) (fa : Tg_graph_d J k a) (fb : Tg_graph_d J k b)
    (sub : M.MemberSubset h h') : M.MemberSubset a a' ∧ M.MemberSubset b b' := by
  have keep {i x} (point : M.PairMember J i x h) : M.PairMember J i x h' :=
    point.elim fun p hp => ⟨p,hp.1,sub p hp.2⟩
  constructor
  · intro p hp
    obtain ⟨i,x,pair⟩ := fa.1.1 p hp
    have hi := hk i ((fa.2 i).mpr ⟨x,p,pair,hp⟩)
    obtain ⟨j,add,point⟩ := (old.1 i hi x).mp ⟨p,pair,hp⟩
    obtain ⟨q,pair',hq⟩ := (next.1 i hi x).mpr ⟨j,add,keep point⟩
    exact J.unique pair' pair ▸ hq
  · intro p hp
    obtain ⟨i,x,pair⟩ := fb.1.1 p hp
    have hi := hk i ((fb.2 i).mpr ⟨x,p,pair,hp⟩)
    obtain ⟨j,l,add,succ,point⟩ := (old.2 i hi x).mp ⟨p,pair,hp⟩
    obtain ⟨q,pair',hq⟩ := (next.2 i hi x).mpr ⟨j,l,add,succ,keep point⟩
    exact J.unique pair' pair ▸ hq

private theorem dg_end_at_l {ω n V h t z : M.Domain} (fn : Fn0_d n V h)
    (end' : Fseq_end_d I ω t h z) : Rd_entry_d n z t := by
  obtain ⟨_,m,data⟩ := end'
  have eq := data.prefix_sequence.2.2.2.eq hZF.1 (fn0_function_l (ZF.modelsKP hZF) fn).2.1
  exact eq ▸ data.last_value

/-- 指定挑战与同一胜策的回复分别成为两张图唯一新增的末项。 -/
theorem Dg_counter_d.reply_extend_l
    {ω U₁ U₂ x S V F L G J B W O e τ R k n h z a b : M.Domain}
    (game : Dg_counter_d hZF ω U₁ U₂ x S V F L G J B W O) (hw : M.IsOmega ω)
    (control : Cg_control_d I true ω e V F L G J τ R)
    (hk : M.mem k ω) (hn : M.mem n ω) (add : M.IsOrdinalAddition I n k k)
    (fh : Fn0_d n V h) (hh : M.mem h R) (fa : Fn0_d k U₁ a) (fb : Fn0_d k U₂ b)
    (weave : Dg_weave_d I ω h a b) (hz : M.mem z U₁) :
    ∃ k' n' h₁ h₂ z' s' a' b', M.SuccessorOf k' k ∧ M.mem k' ω ∧ M.mem n' ω ∧
      M.IsOrdinalAddition I n' k' k' ∧ Fn0_d n' V h₂ ∧ M.mem h₂ R ∧
      Fseq_end_d I ω h₁ h z ∧ Fseq_end_d I ω h₂ h₁ z' ∧ Rd_entry_d h₁ z' τ ∧ M.mem z' U₂ ∧
      M.IsRestrictionOf I s' x k' ∧ Tg_node_d I k' S s' a' b' ∧
      Fn0_d k' U₁ a' ∧ Fn0_d k' U₂ b' ∧ Dg_weave_d I ω h₂ a' b' ∧
      (∀ p, M.mem p a' ↔ M.mem p a ∨ KPair_d M p k z) ∧
      (∀ p, M.mem p b' ↔ M.mem p b ∨ KPair_d M p k z') := by
  obtain ⟨k',succ,hk'⟩ := hw.1.2 k hk
  obtain ⟨m,n',h₁,h₂,z',hm,hn',sn,sm,f₁,f₂,_,h₂R,end₁,end₂,value,hz',l,s',a',b',hl,add',fa',fb',rest,node,weave'⟩ :=
    game.reply_round_l hZF hw control hn fh hh ⟨k,hk,add⟩ hz
  have next := dg_twice_next_l hZF hw hk succ sn sm add
  have eq := dg_twice_inj_l hZF hw hl hk' add' next
  subst l
  have sub : M.MemberSubset h h₂ := fun p hp => end₂.subset_l I p (end₁.subset_l I p hp)
  have ga : Tg_graph_d I k a := ⟨(fn0_function_l (ZF.modelsKP hZF) fa).1,(fn0_function_l (ZF.modelsKP hZF) fa).2.1⟩
  have gb : Tg_graph_d I k b := ⟨(fn0_function_l (ZF.modelsKP hZF) fb).1,(fn0_function_l (ZF.modelsKP hZF) fb).2.1⟩
  have ga' : Tg_graph_d I k' a' := ⟨(fn0_function_l (ZF.modelsKP hZF) fa').1,(fn0_function_l (ZF.modelsKP hZF) fa').2.1⟩
  have gb' : Tg_graph_d I k' b' := ⟨(fn0_function_l (ZF.modelsKP hZF) fb').1,(fn0_function_l (ZF.modelsKP hZF) fb').2.1⟩
  obtain ⟨suba,subb⟩ := weave.subset_l I weave' (hw.transitive (ZF.modelsKP hZF) k hk) ga gb sub
  have hit : Rd_entry_d n z h₂ := (dg_end_at_l hZF fh end₁).elim fun p hp => ⟨p,hp.1,end₂.subset_l I p hp.2⟩
  have hitA := (weave'.1 k hk z).mpr ⟨n,add,hit⟩
  have hitB := (weave'.2 k hk z').mpr ⟨n,m,add,sn,dg_end_at_l hZF f₁ end₂⟩
  obtain ⟨u,pu,appendA⟩ := tg_graph_extend_l hZF.1 (KP.exists_pair (ZF.modelsKP hZF)) succ ga ga' suba
  have eu := ga'.1.2 k u z pu hitA
  subst u
  obtain ⟨v,pv,appendB⟩ := tg_graph_extend_l hZF.1 (KP.exists_pair (ZF.modelsKP hZF)) succ gb gb' subb
  have ev := gb'.1.2 k v z' pv hitB
  subst v
  exact ⟨k',n',h₁,h₂,z',s',a',b',succ,hk',hn',next,f₂,h₂R,end₁,end₂,value,hz',rest,node,
    fa',fb',weave',appendA,appendB⟩

end YesMetaZFC.SetTheory.Descriptive

/-! ## 交替历史和两张辅助图同步追加

同一完整轮的两次实际落子，分别成为两张辅助图的新末项。
奇偶性排除交叉位置，加倍单射性识别唯一的新轮号。
-/
namespace YesMetaZFC.SetTheory.Descriptive
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Dg_weave_d.append_l {ω k n m V A B h h₁ h₂ a b a' b' d r : M.Domain}
    (weave : Dg_weave_d I ω h a b) (hw : M.IsOmega ω) (hk : M.mem k ω)
    (add : M.IsOrdinalAddition I n k k) (succ : M.SuccessorOf m n)
    (fh : Fn0_d n V h) (f₁ : Fn0_d m V h₁) (fa : Fn0_d k A a) (fb : Fn0_d k B b)
    (e₁ : Fseq_end_d I ω h₁ h d) (e₂ : Fseq_end_d I ω h₂ h₁ r)
    (ea : Fseq_end_d I ω a' a d) (eb : Fseq_end_d I ω b' b r) : Dg_weave_d I ω h₂ a' b' := by
  have rh := e₁.entries_l I hZF.1 (fn0_function_l (ZF.modelsKP hZF) fh).2.1
  have rt := e₂.entries_l I hZF.1 (fn0_function_l (ZF.modelsKP hZF) f₁).2.1
  have ra := ea.entries_l I hZF.1 (fn0_function_l (ZF.modelsKP hZF) fa).2.1
  have rb := eb.entries_l I hZF.1 (fn0_function_l (ZF.modelsKP hZF) fb).2.1
  have hn := ZF.ordinalAddition_mem_omega hZF I hw hk hk add
  have odd : ¬ Gm_even_d I ω m := fun yes => ((gm_even_successor_l I hZF hw hn succ).mp yes) ⟨k,hk,add⟩
  constructor
  · intro i hi x
    constructor
    · intro ix
      rcases (ra i x).mp ix with ix | ⟨rfl,rfl⟩
      · obtain ⟨j,ji,jx⟩ := (weave.1 i hi x).mp ix
        exact ⟨j,ji,(rt j x).mpr (Or.inl ((rh j x).mpr (Or.inl jx)))⟩
      · exact ⟨n,add,(rt n x).mpr (Or.inl ((rh n x).mpr (Or.inr ⟨rfl,rfl⟩)))⟩
    · rintro ⟨j,ji,jx⟩
      rcases (rt j x).mp jx with jx | ⟨rfl,_⟩
      · rcases (rh j x).mp jx with jx | ⟨rfl,rfl⟩
        · exact (ra i x).mpr (Or.inl ((weave.1 i hi x).mpr ⟨j,ji,jx⟩))
        · exact (ra i x).mpr (Or.inr ⟨dg_twice_inj_l hZF hw hi hk ji add,rfl⟩)
      · exact (odd ⟨i,hi,ji⟩).elim
  · intro i hi x
    constructor
    · intro ix
      rcases (rb i x).mp ix with ix | ⟨rfl,rfl⟩
      · obtain ⟨j,l,ji,lj,lx⟩ := (weave.2 i hi x).mp ix
        exact ⟨j,l,ji,lj,(rt l x).mpr (Or.inl ((rh l x).mpr (Or.inl lx)))⟩
      · exact ⟨n,m,add,succ,(rt m x).mpr (Or.inr ⟨rfl,rfl⟩)⟩
    · rintro ⟨j,l,ji,lj,lx⟩
      rcases (rt l x).mp lx with lx | ⟨rfl,rfl⟩
      · rcases (rh l x).mp lx with lx | ⟨rfl,_⟩
        · exact (rb i x).mpr (Or.inl ((weave.2 i hi x).mpr ⟨j,l,ji,lj,lx⟩))
        · have hj := ZF.ordinalAddition_mem_omega hZF I hw hi hi ji
          exact (((gm_even_successor_l I hZF hw hj lj).mp ⟨k,hk,add⟩) ⟨i,hi,ji⟩).elim
      · have eq := succ.predecessor_eq hZF.1 (hw.members_areOrdinals (ZF.modelsKP hZF) n hn) lj
        subst j
        exact (rb i x).mpr (Or.inr ⟨dg_twice_inj_l hZF hw hi hk ji add,rfl⟩)

end YesMetaZFC.SetTheory.Descriptive

/-! ## 按实际枚举落子的对抗策略

偶数长度 n=k+k 时读取同一枚举的第 k 项；其他有限历史取枚举的零项。
全部策略值均属于 U₁。定义域和数值唯一性由实际有限函数及加倍单射性证明。
-/
namespace YesMetaZFC.SetTheory.Descriptive
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Dg_counter_d.enumeration_strategy_l
    {ω U₁ U₂ x S V F L G J B W O e : M.Domain}
    (game : Dg_counter_d hZF ω U₁ U₂ x S V F L G J B W O)
    (hw : M.IsOmega ω) (ef : Fn0_d ω U₁ e) :
    ∃ σ, Fn0_d F U₁ σ ∧ ∀ n s k z, Fn0_d n V s → M.mem k ω →
      M.IsOrdinalAddition I n k k → Rd_entry_d s z σ → Rd_entry_d k z e := by
  classical
  obtain ⟨o,_,ho⟩ := hw.1.1
  obtain ⟨a,ha,_⟩ := ef.2.1 o ho
  let ρ : Env M 4 := ⟨fun i => [ω,V,e,a].get i,fun _ => ω⟩
  let φ : BinarySchema 4 := { body := set[6] ⟪∃ n ∈ ⌜(.bound 2 : Term 6)⌝ₛ,
    ⌜fn0_m⌝ₚ(n,⌜(.bound 3 : Term 6)⌝ₛ,⌜(.bound 1 : Term 6)⌝ₛ) ∧
    ((∃ k ∈ ⌜(.bound 2 : Term 6)⌝ₛ,
      ⌜Formula.isOrdinalAddition kpair_convention_l⌝ₚ(n,k,k) ∧
      ⌜rd_entry0_m⌝ₚ(k,⌜(.newest : Term 6)⌝ₛ,⌜(.bound 4 : Term 6)⌝ₛ)) ∨
      (¬ ⌜(gm_even_m (𝒞 := kpair_convention_l))⌝ₚ(⌜(.bound 2 : Term 6)⌝ₛ,n) ∧
        ⌜(.newest : Term 6)⌝ₛ = ⌜(.bound 5 : Term 6)⌝ₛ))⟫ }
  have sat s y : φ.denote ρ s y ↔ ∃ n, M.mem n ω ∧ Fn0_d n V s ∧
      ((∃ k, M.mem k ω ∧ M.IsOrdinalAddition I n k k ∧ Rd_entry_d k y e) ∨
        (¬ Gm_even_d I ω n ∧ y = a)) := by
    simp only [φ,BinarySchema.denote,Formula.satisfies_existsMem_iff,Formula.satisfies_conj_iff,
      fn0_sat_l hZF.1,Formula.satisfies_disj_iff,Formula.satisfies_isOrdinalAddition_iff I hZF.1,
      rd_entry0_sat_l hZF.1,Formula.satisfies_neg_iff,gm_even_sat_l I hZF.1,
      Formula.satisfies_extensionalEq_iff_eq hZF.1,Definitional.Term.eval_weaken]
    rfl
  have total s (hs : M.mem s F) : ∃ y, φ.denote ρ s y := by
    obtain ⟨n,hn,fs⟩ := (game.space s).mp hs
    by_cases even : Gm_even_d I ω n
    · obtain ⟨k,hk,add⟩ := even
      obtain ⟨y,_,point⟩ := ef.2.1 k hk
      exact ⟨y,(sat s y).mpr ⟨n,hn,fn0_of_function_l (ZF.modelsKP hZF) fs,Or.inl ⟨k,hk,add,point⟩⟩⟩
    · exact ⟨a,(sat s a).mpr ⟨n,hn,fn0_of_function_l (ZF.modelsKP hZF) fs,Or.inr ⟨even,rfl⟩⟩⟩
  have one s y z (hy : φ.denote ρ s y) (hz : φ.denote ρ s z) : y = z := by
    obtain ⟨n,_,fs,left⟩ := (sat s y).mp hy
    obtain ⟨m,_,ft,right⟩ := (sat s z).mp hz
    have eq := ft.domain_eq_l hZF.1 fs
    subst m
    rcases left with ⟨i,hi,add,iy⟩ | ⟨odd,eqy⟩ <;>
      rcases right with ⟨j,hj,add',jz⟩ | ⟨odd',eqz⟩
    · have eq := dg_twice_inj_l hZF hw hi hj add add'
      exact (fn0_function_l (ZF.modelsKP hZF) ef).1.2 i y z iy (eq.symm ▸ jz)
    · exact (odd' ⟨i,hi,add⟩).elim
    · exact (odd ⟨j,hj,add'⟩).elim
    · exact eqy.trans eqz.symm
  obtain ⟨σ,fn,values⟩ := ZF.exists_setFunctionFromTo_of_denote hZF I φ ρ
    total (fun s _ => one s) (by
      intro s y _ hy
      obtain ⟨_,_,_,rule⟩ := (sat s y).mp hy
      rcases rule with ⟨_,_,_,point⟩ | ⟨_,eq⟩
      · exact (ef.bound_l point).2
      · exact eq.symm ▸ ha)
  refine ⟨σ,fn0_of_function_l (ZF.modelsKP hZF) fn,?_⟩
  intro n s k z fs hk add point
  obtain ⟨m,_,ft,rule⟩ := (sat s z).mp ((values s z).mp point).2
  have eq := ft.domain_eq_l hZF.1 fs
  subst m
  rcases rule with ⟨j,hj,add',jz⟩ | ⟨odd,_⟩
  · exact (dg_twice_inj_l hZF hw hj hk add' add) ▸ jz
  · exact (odd ⟨k,hk,add⟩).elim

end YesMetaZFC.SetTheory.Descriptive

/-! ## 同一枚举策略和原胜策的实际合法无限运行

先用原两张策略构造一份内部 ω 对局，再沿该对局的实际限制图归纳。
对手的偶数步由枚举保证合法，胜策负责的奇数步由原控制集合保证合法；
没有把所有前缀安全性作为额外输入。
-/
namespace YesMetaZFC.SetTheory.Descriptive
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

/-- 指定枚举驱动的实际对弈：全部有限前缀合法，偶数坐标逐点等于该枚举。 -/
theorem Dg_counter_d.enumerated_play_l
    {ω U₁ U₂ x S V F L G J B W O e τ : M.Domain}
    (game : Dg_counter_d hZF ω U₁ U₂ x S V F L G J B W O)
    (hw : M.IsOmega ω) (ef : Fn0_d ω U₁ e) (win : Cg_win_d I true ω V F J B W τ) :
    ∃ h, Fn0_d ω V h ∧ Cg_follows_d I true ω J τ h ∧
      (∀ n, M.mem n ω → ∀ t, M.IsRestrictionOf I t h n → M.mem t G) ∧
      (∀ k n y, M.mem k ω → M.IsOrdinalAddition I n k k → Rd_entry_d n y h → Rd_entry_d k y e) := by
  classical
  obtain ⟨σ,strategy,values⟩ := game.enumeration_strategy_l hZF hw ef
  have strategyV := strategy.mono_target_l (fun z hz => (game.alphabet z).mpr (Or.inl hz))
  obtain ⟨h,hf,follows,opponent⟩ := cg_battle_l hZF (J := J) hw game.space win.1 strategyV
  obtain ⟨o,R,empty,control⟩ := game.control_l hZF hw win
  let ρ : Env M 2 := ⟨Fin.cases h (fun _ => R),fun _ => ω⟩
  let φ : UnarySchema 2 := { body := set[3] ⟪∀ t,
    ⌜(Formula.isRestriction kpair_convention_l)⌝ₚ(t,⌜(.bound 1 : Term 3)⌝ₛ,⌜(.newest : Term 3)⌝ₛ) →
      t ∈ ⌜(.bound 2 : Term 3)⌝ₛ⟫ }
  have sat n : φ.denote ρ n ↔ ∀ t, M.IsRestrictionOf I t h n → M.mem t R := by
    simp only [φ,UnarySchema.denote,Formula.satisfies_forall_iff,Formula.satisfies_imp_iff,
      Formula.satisfies_isRestriction_iff I,Formula.satisfies_mem_iff,Definitional.Term.eval_weaken]
    rfl
  have all : ∀ n, M.mem n ω → ∀ t, M.IsRestrictionOf I t h n → M.mem t R := by
    apply hw.induction
    · obtain ⟨A,read⟩ := ZF.separation_exists_d hZF φ ρ ω
      exact ⟨A,fun n => (read n).trans (and_congr_right fun _ => sat n)⟩
    · intro z hz t rest
      have no p (hp : M.mem p t) : False := by
        obtain ⟨i,y,pair⟩ := rest.1 p hp
        exact hz i ((rest.2 i y).mp ⟨p,pair,hp⟩).1
      have eq := hZF.1.eq_of_same_members t o (fun p => iff_of_false (no p) (empty p))
      exact eq.symm ▸ control.root
    · intro n hn ih m succ t rest
      obtain ⟨m',succ',hm'⟩ := hw.1.2 n hn
      have hm : M.mem m ω := succ'.eq hZF.1 succ ▸ hm'
      obtain ⟨s,fs,rs,_⟩ := ds_prefix_l I hZF hw hf hn
      obtain ⟨y,hy,point⟩ := hf.2.2 n hn
      have ft := rest.isSetFunctionFromTo hf (hw.transitive (ZF.modelsKP hZF) m hm)
      have ends := ds_cut_end_l hZF hw hf hn succ rs rest point
      by_cases own : M.mem n J
      · exact control.step n s y t hn (ih s rs) hy (fn0_of_function_l (ZF.modelsKP hZF) fs) ends
          (Or.inr ⟨own,follows n hn own s rs y point⟩)
      · have even : Gm_even_d I ω n := Classical.byContradiction (fun odd => own ((game.turns n).mpr ⟨hn,odd⟩))
        have hy₁ := (strategy.bound_l (opponent n hn own s rs y point)).2
        have check : M.mem t L := (game.checks t).mpr
          ⟨(game.space t).mpr ⟨m,hm,ft⟩,m,hm,fn0_of_function_l (ZF.modelsKP hZF) ft,
            Or.inr ⟨n,y,succ,(rest.2 n y).mpr ⟨succ.predecessor_mem,point⟩,Or.inl ⟨even,hy₁⟩⟩⟩
        exact control.step n s y t hn (ih s rs) hy (fn0_of_function_l (ZF.modelsKP hZF) fs) ends
          (Or.inl ⟨own,check⟩)
  refine ⟨h,fn0_of_function_l (ZF.modelsKP hZF) hf,follows,
    fun n hn t rest => ((control.positions t).mp (all n hn t rest)).1,?_⟩
  intro k n y hk add point
  have hn := hf.input_mem_of_pairMember point
  have own : ¬ M.mem n J := fun h => ((game.turns n).mp h).2 ⟨k,hk,add⟩
  obtain ⟨s,fs,rest,_⟩ := ds_prefix_l I hZF hw hf hn
  exact values n s k y (fn0_of_function_l (ZF.modelsKP hZF) fs) hk add (opponent n hn own s rest y point)

end YesMetaZFC.SetTheory.Descriptive

/-! ## 同一合法无限补树对局的两张原字母图

从交替对局的奇数坐标收集第二张图；第一张图由实际偶步方程识别。
每个正长度节点都读取同一对局的完整轮检查，不假设空根或树闭包。
-/
namespace YesMetaZFC.SetTheory.Descriptive
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Dg_counter_d.weave_run_l
    {ω U₁ U₂ x S V F L G J B W O e h : M.Domain}
    (game : Dg_counter_d hZF ω U₁ U₂ x S V F L G J B W O) (hw : M.IsOmega ω)
    (ef : Fn0_d ω U₁ e) (hf : Fn0_d ω V h)
    (legal : ∀ n, M.mem n ω → ∀ t, M.IsRestrictionOf I t h n → M.mem t G)
    (evenExact : ∀ k n y, M.mem k ω → M.IsOrdinalAddition I n k k →
      Rd_entry_d n y h → Rd_entry_d k y e) :
    ∃ b, Fn0_d ω U₂ b ∧ Dg_weave_d I ω h e b ∧
      ∀ k, M.mem k ω → ∃ l n t s a b₀,
        M.SuccessorOf l k ∧ M.mem l ω ∧ M.IsOrdinalAddition I n l l ∧
        M.IsRestrictionOf I t h n ∧ M.IsRestrictionOf I s x l ∧
        M.IsRestrictionOf I a e l ∧ M.IsRestrictionOf I b₀ b l ∧ Tg_node_d I l S s a b₀ := by
  have fh := fn0_function_l (ZF.modelsKP hZF) hf
  have fe := fn0_function_l (ZF.modelsKP hZF) ef
  have ord := hw.members_areOrdinals (ZF.modelsKP hZF)
  -- 在 2(k+1) 处截取同一历史，奇数末步的检查给出实际完整轮。
  have rounds k (hk : M.mem k ω) : ∃ l n t s a b,
      M.SuccessorOf l k ∧ M.mem l ω ∧ M.IsOrdinalAddition I n l l ∧
      M.IsRestrictionOf I t h n ∧ M.IsRestrictionOf I s x l ∧
      Fn0_d l U₁ a ∧ Fn0_d l U₂ b ∧ Tg_node_d I l S s a b ∧ Dg_weave_d I ω t a b := by
    obtain ⟨l,sk,hl⟩ := hw.1.2 k hk
    obtain ⟨r,add,_⟩ := ZF.ordinalAddition_existsUnique hZF I k (ord k hk)
    have hr := ZF.ordinalAddition_mem_omega hZF I hw hk hk add
    obtain ⟨m,sr,hm⟩ := hw.1.2 r hr
    obtain ⟨n,sm,hn⟩ := hw.1.2 m hm
    have next := dg_twice_next_l hZF hw hk sk sr sm add
    obtain ⟨t,cut⟩ := ZF.exists_restriction hZF I h n
    have ft := fn0_of_function_l (ZF.modelsKP hZF)
      (cut.isSetFunctionFromTo fh (hw.transitive (ZF.modelsKP hZF) n hn))
    have check := ((game.checks t).mp (game.legal.current_l (legal n hn t cut))).2
    obtain ⟨n₀,_,ft₀,check⟩ := check
    have eq := ft₀.domain_eq_l hZF.1 ft
    subst n₀
    have odd : ¬ Gm_even_d I ω m := fun even =>
      ((gm_even_successor_l I hZF hw hr sr).mp even) ⟨k,hk,add⟩
    rcases check with empty | ⟨i,y,si,_,checks⟩
    · exact (empty m sm.predecessor_mem).elim
    · have eq := sm.predecessor_eq hZF.1 (ord m hm) si
      subst i
      have round : Dg_round_d I ω U₁ U₂ x S n t :=
        checks.elim (fun yes => (odd yes.1).elim) (fun yes => yes.2.2)
      obtain ⟨l₀,s,a,b,hl₀,add₀,fa,fb,rest,node,weave⟩ := round
      have eq := dg_twice_inj_l hZF hw hl₀ hl add₀ next
      subst l₀
      exact ⟨l,n,t,s,a,b,sk,hl,next,cut,rest,fa,fb,node,weave⟩
  -- 奇数坐标关系是单值的；其值域所属由上面的实际完整轮读出。
  let odd i y := ∃ j l, M.IsOrdinalAddition I j i i ∧ M.SuccessorOf l j ∧ Rd_entry_d l y h
  have total i (hi : M.mem i ω) : ∃ y, M.mem y U₂ ∧ odd i y := by
    obtain ⟨l,n,t,s,a,b,sk,_,_,cut,_,_,fb,_,weave⟩ := rounds i hi
    obtain ⟨y,hy,iy⟩ := fb.2.1 i sk.predecessor_mem
    obtain ⟨j,m,add,succ,point⟩ := (weave.2 i hi y).mp iy
    exact ⟨y,hy,j,m,add,succ,((cut.2 m y).mp point).2⟩
  have unique i (hi : M.mem i ω) y z (hy : odd i y) (hz : odd i z) : y = z := by
    obtain ⟨j,l,add,succ,point⟩ := hy
    obtain ⟨j',l',add',succ',point'⟩ := hz
    obtain ⟨_,_,one⟩ := ZF.ordinalAddition_existsUnique hZF I i (ord i hi)
    have eq := (one j add).trans (one j' add').symm
    subst j'
    have eq := succ.eq hZF.1 succ'
    subst l'
    exact fh.1.2 l y z point point'
  let ρ : Env M 1 := ⟨fun _ => h,fun _ => h⟩
  let φ : BinarySchema 1 := { body := .existsE (.existsE (.conj
    (Formula.isOrdinalAddition kpair_convention_l (.bound 1) (.bound 3) (.bound 3))
    (.conj (Formula.isSuccessor .newest (.bound 1))
      (Formula.orderedPairMem kpair_convention_l .newest (.bound 2) (.bound 4))))) }
  have sat i y : φ.denote ρ i y ↔ odd i y := by
    simp only [φ,odd,BinarySchema.denote,Formula.satisfies_exists_iff,Formula.satisfies_conj_iff,
      Formula.satisfies_isOrdinalAddition_iff I hZF.1,Formula.satisfies_isSuccessor_iff,
      Formula.satisfies_orderedPairMem_iff I]
    rfl
  obtain ⟨b,fb,graph⟩ := ZF.exists_setFunctionFromTo_of_denote hZF I φ ρ (source := ω) (target := U₂)
    (fun i hi => (total i hi).imp fun y hy => (sat i y).mpr hy.2)
    (fun i hi y z hy hz => unique i hi y z ((sat i y).mp hy) ((sat i z).mp hz)) (by
      intro i y hi hy
      obtain ⟨z,hz,iz⟩ := total i hi
      exact (unique i hi y z ((sat i y).mp hy) iz).symm ▸ hz)
  have weave : Dg_weave_d I ω h e b := by
    constructor
    · intro i hi y
      constructor
      · intro iy
        obtain ⟨j,add,_⟩ := ZF.ordinalAddition_existsUnique hZF I i (ord i hi)
        have hj := ZF.ordinalAddition_mem_omega hZF I hw hi hi add
        obtain ⟨z,_,jz⟩ := hf.2.1 j hj
        have eq := fe.1.2 i z y (evenExact i j z hi add jz) iy
        exact ⟨j,add,eq ▸ jz⟩
      · rintro ⟨j,add,jy⟩
        exact evenExact i j y hi add jy
    · intro i hi y
      exact (graph i y).trans ((and_congr_right fun _ => sat i y).trans
        ⟨And.right,fun hy => ⟨hi,hy⟩⟩)
  -- 同域全函数的逐点包含就是精确限制；无需另造节点或选择极限。
  have restriction {l U a f : M.Domain} (fa : Fn0_d l U a) (ff : M.IsSetFunction I f)
      (keep : ∀ i y, Rd_entry_d i y a → Rd_entry_d i y f) : M.IsRestrictionOf I a f l := by
    have af := fn0_function_l (ZF.modelsKP hZF) fa
    refine ⟨af.1.1,fun i y => ⟨fun iy => ⟨(fa.bound_l iy).1,keep i y iy⟩,?_⟩⟩
    rintro ⟨hi,iy⟩
    obtain ⟨z,_,iz⟩ := fa.2.1 i hi
    exact (ff.2 i y z iy (keep i z iz)).symm ▸ iz
  refine ⟨b,fn0_of_function_l (ZF.modelsKP hZF) fb,weave,?_⟩
  intro k hk
  obtain ⟨l,n,t,s,a,b₀,sk,hl,add,cut,rest,fa,fb₀,node,woven⟩ := rounds k hk
  have acut : M.IsRestrictionOf I a e l := restriction fa fe.1 (by
    intro i y iy
    have hi := hw.transitive (ZF.modelsKP hZF) l hl i (fa.bound_l iy).1
    obtain ⟨j,aj,jy⟩ := (woven.1 i hi y).mp iy
    exact (weave.1 i hi y).mpr ⟨j,aj,((cut.2 j y).mp jy).2⟩)
  have bcut : M.IsRestrictionOf I b₀ b l := restriction fb₀ fb.1 (by
    intro i y iy
    have hi := hw.transitive (ZF.modelsKP hZF) l hl i (fb₀.bound_l iy).1
    obtain ⟨j,m,aj,sj,jy⟩ := (woven.2 i hi y).mp iy
    exact (weave.2 i hi y).mpr ⟨j,m,aj,sj,((cut.2 m y).mp jy).2⟩)
  exact ⟨l,n,t,s,a,b₀,sk,hl,add,cut,rest,acut,bcut,node⟩

end YesMetaZFC.SetTheory.Descriptive
