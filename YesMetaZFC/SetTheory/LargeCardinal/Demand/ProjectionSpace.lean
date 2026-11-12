import YesMetaZFC.SetTheory.LargeCardinal.Game.ShiftedProjection
import YesMetaZFC.SetTheory.Descriptive.Demand.DemandCounterWeave

/-! # 第一辅助坐标满射的 demanding projection

实际满射图与第二辅助图一起合成原树的无限分支。正完整轮已经共尾，
故原树的前缀封闭性自动补齐零节点；不另加树根或无限分支假设。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal Descriptive
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

def Td_projection_d (ω U₁ U₂ Y F S x : M.Domain) : Prop := ∃ q a b,
  Fn0_d ω U₁ a ∧ M.IsSetSurjectiveOnto I a ω U₁ ∧ Fn0_d ω U₂ b ∧
    Fn0_d ω Y q ∧ Branch_d F S q ∧ Tg_join_d I ω x a b q

def td_projection_m {d} (ω U₁ U₂ Y F S x : Term d) : Formula 1 d := set[d] ⟪∃ q a b,
  ⌜fn0_m⌝ₚ(⌜ω⌝ₛ,⌜U₁⌝ₛ,a) ∧
  (∀ y ∈ ⌜U₁⌝ₛ, ∃ i ∈ ⌜ω⌝ₛ, ⌜Formula.orderedPairMem kpair_convention_l⌝ₚ(i,y,a)) ∧
  ⌜fn0_m⌝ₚ(⌜ω⌝ₛ,⌜U₂⌝ₛ,b) ∧ ⌜fn0_m⌝ₚ(⌜ω⌝ₛ,⌜Y⌝ₛ,q) ∧
  ⌜branch_m⌝ₚ(⌜F⌝ₛ,⌜S⌝ₛ,q) ∧ ⌜tg_join_m⌝ₚ(⌜ω⌝ₛ,⌜x⌝ₛ,a,b,q)⟫
derive_free_closed td_projection_m

theorem td_projection_sat_l {d} (ρ : Env M d) (ω U₁ U₂ Y F S x : Term d) :
    Formula.satisfies ρ (td_projection_m ω U₁ U₂ Y F S x) ↔
      Td_projection_d hZF (ω.eval ρ) (U₁.eval ρ) (U₂.eval ρ) (Y.eval ρ) (F.eval ρ) (S.eval ρ) (x.eval ρ) := by
  simp only [td_projection_m,Td_projection_d,Structure.IsSetSurjectiveOnto,Formula.satisfies_exists_iff,
    Formula.satisfies_conj_iff,fn0_sat_l hZF.1,Formula.satisfies_forallMem_iff,
    Formula.satisfies_existsMem_iff,Formula.satisfies_orderedPairMem_iff I,branch_sat_l,
    tg_join_sat_l I hZF.1,Definitional.Term.eval_weaken]
  rfl

/-- 同一无限图的共尾实际节点给出完整分支，满射性原样保留。 -/
theorem td_projection_of_nodes_l {ω X U₁ U₂ Y F S x a b : M.Domain}
    (hw : M.IsOmega ω) (fx : Fn0_d ω X x) (fa : Fn0_d ω U₁ a)
    (onto : M.IsSetSurjectiveOnto I a ω U₁) (fb : Fn0_d ω U₂ b)
    (space : Fseq_space_d I ω Y F) (tree : Tree_d F S)
    (nodes : ∀ n, M.mem n ω → ∃ l s u v, M.mem n l ∧ M.mem l ω ∧
      M.IsRestrictionOf I s x l ∧ M.IsRestrictionOf I u a l ∧ M.IsRestrictionOf I v b l ∧
      Tg_node_d I l S s u v) : Td_projection_d hZF ω U₁ U₂ Y F S x := by
  have f₀ := fn0_function_l (ZF.modelsKP hZF) fx
  have f₁ := fn0_function_l (ZF.modelsKP hZF) fa
  have f₂ := fn0_function_l (ZF.modelsKP hZF) fb
  obtain ⟨_,Z,q,_,_,fq,join⟩ := tg_join_exists_l I hZF f₀ f₁ f₂
  have sub {r f l : M.Domain} (rest : M.IsRestrictionOf I r f l) : M.MemberSubset r f := by
    intro p hp
    obtain ⟨i,z,pair⟩ := rest.1 p hp
    obtain ⟨t,pair',ht⟩ := ((rest.2 i z).mp ⟨p,pair,hp⟩).2
    exact kpair_unique_l M hZF.1 pair' pair ▸ ht
  have cofinal : Tg_cofinal_branch_d hZF ω Z S q := by
    refine ⟨fn0_of_function_l (ZF.modelsKP hZF) fq,?_⟩
    intro n hn
    obtain ⟨l,s,u,v,nl,hl,rs,ru,rv,_,_,_,t,ht,joined⟩ := nodes n hn
    exact ⟨l,t,nl,hl,ht,joined.1,
      Tg_join_d.subset_l joined join f₀.1 f₁.1 f₂.1
        (hw.transitive (ZF.modelsKP hZF) l hl) (sub rs) (sub ru) (sub rv)⟩
  obtain ⟨typed,branch⟩ := cofinal.branch_l hZF hw space tree
  exact ⟨q,a,b,fa,onto,fb,typed,branch,join⟩

/-! 给定共尾节点列及第一坐标满射时，直接得到 demanding projection。

这里的 `onto` 是唯一未在本层自动产生的高辅助域覆盖义务；其余分支、
有限空间、树和三图合成均由现有对象逐项读取。 -/
theorem Td_projection_d.of_cofinal_branch_l
    {ω X U₁ U₂ Y F S x q a b : M.Domain}
    (h : Tg_cofinal_branch_d hZF ω X S q) (hw : M.IsOmega ω)
    (fa : Fn0_d ω U₁ a) (onto : M.IsSetSurjectiveOnto I a ω U₁)
    (fb : Fn0_d ω U₂ b) (space : Fseq_space_d I ω Y F) (tree : Tree_d F S)
    (join : Tg_join_d I ω x a b q) :
    Td_projection_d hZF ω U₁ U₂ Y F S x := by
  obtain ⟨typed, branch⟩ := h.branch_l hZF hw space tree
  exact ⟨q, a, b, fa, onto, fb, typed, branch, join⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 补树胜策、实际满射与 demanding projection

指定的第一辅助坐标满射先驱动真实对弈。其每个正完整轮由同一胜策
给出原树节点，随后合成为完整分支；满射图没有重新选取或替换。
-/
namespace YesMetaZFC.SetTheory.Descriptive
open Definitional.Project InnerModel Internal LargeCardinal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Dg_counter_d.projection_l
    {ω X U₁ U₂ Y F S x V H L G J B W O e τ : M.Domain}
    (game : Dg_counter_d hZF ω U₁ U₂ x S V H L G J B W O) (hw : M.IsOmega ω)
    (fx : Fn0_d ω X x) (ef : Fn0_d ω U₁ e) (onto : M.IsSetSurjectiveOnto I e ω U₁)
    (space : Fseq_space_d I ω Y F) (tree : Tree_d F S)
    (win : Cg_win_d I true ω V H J B W τ) : Td_projection_d hZF ω U₁ U₂ Y F S x := by
  obtain ⟨h,hf,_,legal,values⟩ := game.enumerated_play_l hZF hw ef win
  obtain ⟨b,fb,_,nodes⟩ := game.weave_run_l hZF hw ef hf legal values
  apply td_projection_of_nodes_l hZF hw fx ef onto fb space tree
  intro n hn
  obtain ⟨l,_,_,s,a,b₀,succ,hl,_,_,rs,ra,rb,node⟩ := nodes n hn
  exact ⟨l,s,a,b₀,succ.predecessor_mem,hl,rs,ra,rb,node⟩

variable (hZFC : M.Models ZFC)
local notation "hZ" => ZFC.models_zf_l hZFC
local notation "K" => kp_pair_l (ZF.modelsKP hZ)

/-- 7.3：不属于 demanding projection 时，原补树游戏的 I 有实际胜策。 -/
theorem Dg_counter_d.first_wins_l
    {ω X U₁ U₂ Y F S x V H L G J B W O e : M.Domain}
    (game : Dg_counter_d hZ ω U₁ U₂ x S V H L G J B W O) (hw : M.IsOmega ω)
    (fx : Fn0_d ω X x) (ef : Fn0_d ω U₁ e) (onto : M.IsSetSurjectiveOnto K e ω U₁)
    (space : Fseq_space_d K ω Y F) (tree : Tree_d F S)
    (outside : ¬ Td_projection_d hZ ω U₁ U₂ Y F S x) : ∃ τ, Cg_win_d K false ω V H J B W τ := by
  obtain ⟨o,_,ho⟩ := hw.1.1
  obtain ⟨z,hz,_⟩ := ef.2.1 o ho
  rcases game.determined_l hZFC hw ((game.alphabet z).mpr (Or.inl hz)) with ⟨τ,win⟩ | won
  · exact (outside (game.projection_l hZ hw fx ef onto space tree win)).elim
  · exact won

end YesMetaZFC.SetTheory.Descriptive

/-! ## a(¬S) 的实际原对局收益集及两种反策略出口

不属于 demanding projection 时生成补树先手胜策；不属于先手获胜
参数集时，闭决定性在指定同一游戏中给出 II 胜策。后一出口只需要
一个实际第一字母，不要求所在泛型扩张内部枚举整个 U₁。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal Descriptive
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem td_negative_game_l {ω : M.Domain} (hw : M.IsOmega ω) (X U₁ U₂ S : M.Domain) :
    ∃ F J B W, Fseq_space_d I ω X F ∧ M.IsFunctionSpace I B ω X ∧
      (∀ n, M.mem n J ↔ M.mem n ω ∧ Gm_even_d I ω n) ∧
      ∀ f, M.mem f W ↔ M.mem f B ∧ Dg_first_win_d hZF ω U₁ U₂ S f := by
  obtain ⟨F,finite⟩ := ZF.fseq_space_exists_l I hZF hw X
  obtain ⟨B,runs⟩ := ZF.exists_functionSpace hZF I ω X
  let φ : UnarySchema 1 := { body := gm_even_m (𝒞 := kpair_convention_l) (.bound 1) .newest }
  obtain ⟨J,js⟩ := ZF.separation_exists_d hZF φ ⟨fun _ => ω,fun _ => ω⟩ ω
  have turns n : M.mem n J ↔ M.mem n ω ∧ Gm_even_d I ω n :=
    (js n).trans (and_congr_right fun _ => gm_even_sat_l I hZF.1 ..)
  obtain ⟨W,payoff⟩ := dg_first_win_set_l hZF ω U₁ U₂ S B
  exact ⟨F,J,B,W,finite,runs,turns,payoff⟩

variable (hZFC : M.Models ZFC)
local notation "hZ" => ZFC.models_zf_l hZFC
local notation "K" => kp_pair_l (ZF.modelsKP hZ)

/-- 7.3 的完整参数谓词版本，满射由原环境提供并实际用于对弈。 -/
theorem td_outside_first_win_l {ω X U₁ U₂ Y F S x e : M.Domain}
    (hw : M.IsOmega ω) (fx : Fn0_d ω X x) (ef : Fn0_d ω U₁ e)
    (onto : M.IsSetSurjectiveOnto K e ω U₁) (space : Fseq_space_d K ω Y F) (tree : Tree_d F S)
    (outside : ¬ Td_projection_d hZ ω U₁ U₂ Y F S x) : Dg_first_win_d hZ ω U₁ U₂ S x := by
  obtain ⟨V,H,L,G,J,B,W,O,game⟩ := dg_counter_l hZ hw U₁ U₂ x S
  obtain ⟨τ,win⟩ := game.first_wins_l hZFC hw fx ef onto space tree outside
  exact ⟨V,H,L,G,J,B,W,O,τ,game,win⟩

end YesMetaZFC.SetTheory.LargeCardinal

namespace YesMetaZFC.SetTheory.Descriptive
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZFC : M.Models ZFC)
local notation "hZF" => ZFC.models_zf_l hZFC
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

/-- 7.4 所用的实际反策略：只需指定游戏和一个可选 U₁ 字母。 -/
theorem Dg_counter_d.second_wins_l {ω U₁ U₂ x S V F L G J B W O z : M.Domain}
    (game : Dg_counter_d hZF ω U₁ U₂ x S V F L G J B W O) (hw : M.IsOmega ω)
    (hz : M.mem z U₁) (outside : ¬ Dg_first_win_d hZF ω U₁ U₂ S x) :
    ∃ τ, Cg_win_d I true ω V F J B W τ := by
  rcases game.determined_l hZFC hw ((game.alphabet z).mpr (Or.inl hz)) with won | ⟨τ,win⟩
  · exact won
  · exact (outside ⟨V,F,L,G,J,B,W,O,τ,game,win⟩).elim

end YesMetaZFC.SetTheory.Descriptive

/-! ## 外部点否定 projection 后的实际 counter control

先由闭决定性取得 true 方胜策，再沿同一 counter 游戏读取控制集；两步
保持同一游戏对象，不把 false/true 方向混写。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal Descriptive
universe u
variable {M : Structure.{u}} (hZFC : M.Models ZFC)
local notation "hZF" => ZFC.models_zf_l hZFC
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Dg_counter_d.second_control_l
    {ω U₁ U₂ x S V F L G J B W O z : M.Domain}
    (game : Dg_counter_d hZF ω U₁ U₂ x S V F L G J B W O)
    (hw : M.IsOmega ω) (hz : M.mem z U₁)
    (outside : ¬ Dg_first_win_d hZF ω U₁ U₂ S x) :
    ∃ τ e R, (∀ y, ¬ M.mem y e) ∧ Cg_control_d I true ω e V F L G J τ R := by
  obtain ⟨τ,win⟩ := game.second_wins_l hZFC hw hz outside
  obtain ⟨e,R,empty,control⟩ := game.control_l hZF hw win
  exact ⟨τ,e,R,empty,control⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## demanding 分支改用同一树的另一完整有限空间

保持原无限图和两个辅助图；原分支提供的共尾有限节点恢复新空间中的类型。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal Descriptive
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Td_projection_d.space_l {ω U V Y F Z G S x : M.Domain}
    (projection : Td_projection_d hZF ω U V Y F S x) (hw : M.IsOmega ω)
    (old : Fseq_space_d I ω Y F) (space : Fseq_space_d I ω Z G) (tree : Tree_d G S) :
    Td_projection_d hZF ω U V Z G S x := by
  obtain ⟨q,a,b,fa,onto,fb,fq,branch,join⟩ := projection
  have cofinal : Tg_cofinal_branch_d hZF ω Y S q := by
    refine ⟨fq,?_⟩
    intro n hn
    obtain ⟨m,sm,hm⟩ := hw.1.2 n hn
    obtain ⟨s,fs,rest,_⟩ := ds_prefix_l I hZF hw (fn0_function_l (ZF.modelsKP hZF) fq) hm
    have sub := (ds_restrict_iff_l I fs (fn0_function_l (ZF.modelsKP hZF) fq).1).mp rest
    exact ⟨m,s,sm.predecessor_mem,hm,branch s ((old s).mpr ⟨m,hm,fs⟩) sub,⟨fs.1,fs.2.1⟩,sub⟩
  obtain ⟨typed,branch⟩ := cofinal.branch_l hZF hw space tree
  exact ⟨q,a,b,fa,onto,fb,typed,branch,join⟩

end YesMetaZFC.SetTheory.LargeCardinal
