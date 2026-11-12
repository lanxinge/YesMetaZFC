import YesMetaZFC.SetTheory.LargeCardinal.Demand.RetractionFrame
import YesMetaZFC.SetTheory.LargeCardinal.Demand.AlphabetGround
import YesMetaZFC.Model.SetTheory.Internal.RealTrace
import YesMetaZFC.Model.SetTheory.Embedding.Theory
import YesMetaZFC.SetTheory.LargeCardinal.Demand.GenericAvoid
import YesMetaZFC.SetTheory.LargeCardinal.Demand.FirstLetter
import YesMetaZFC.SetTheory.LargeCardinal.Demand.ProjectionSpace
import YesMetaZFC.SetTheory.InaccessibleEnumeration
import YesMetaZFC.Model.Forcing.Collapse.NameCode
import YesMetaZFC.Model.Forcing.Collapse.FiniteRecode
import YesMetaZFC.Model.Forcing.Extension.Choice
import YesMetaZFC.SetTheory.LargeCardinal.Demand.RetractionTree
import YesMetaZFC.SetTheory.Descriptive.Tree.RetractionFixed
import YesMetaZFC.SetTheory.LargeCardinal.Demand.BranchDepth
import YesMetaZFC.SetTheory.LargeCardinal.Iteration.CopyRoundSyntax
import YesMetaZFC.SetTheory.LargeCardinal.Iteration.CopyTree
import YesMetaZFC.Model.SetTheory.ClassChoice
import YesMetaZFC.SetTheory.LargeCardinal.Iteration.CopyStart
import YesMetaZFC.SetTheory.LargeCardinal.Iteration.CopyNice
import YesMetaZFC.SetTheory.LargeCardinal.Iteration.CopyOriginalResult
import YesMetaZFC.SetTheory.LargeCardinal.Demand.StateReal
import YesMetaZFC.Model.SetTheory.Relations.Parity
import YesMetaZFC.SetTheory.LargeCardinal.Demand.BranchProjection
import YesMetaZFC.SetTheory.LargeCardinal.Demand.GeneralProjection
import YesMetaZFC.SetTheory.Descriptive.Game.GameStrategyProjection
import YesMetaZFC.SetTheory.LargeCardinal.Demand.RunPlay
import YesMetaZFC.SetTheory.LargeCardinal.Game.GeneralProjection

/-! # 同一收缩变换沿原模型与实际初等腿运输

先沿完整初等图运输原公式，再用传递隶属模型的成员满包含映射读取。
两个步骤都保留原有限对象组，不能重新选择另一棵逆像树。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal Descriptive Model.Forcing.Internal
universe u v
variable {M : Structure.{u}} {N : Structure.{v}}

theorem Td_frame_d.image_l (hM : M.Models ZF) (hN : N.Models ZF)
    (e : M.Domain → N.Domain) (hi : Function.Injective e)
    (he : ∀ a y, N.mem y (e a) ↔ ∃ c, M.mem c a ∧ e c = y)
    {v : Fin 15 → M.Domain} (frame : Td_frame_d hM v) (hw : N.IsOmega (e (v 0))) :
    Td_frame_d hN (fun i => e (v i)) := by
  have finite {A F} (space : Fseq_space_d (kp_pair_l (ZF.modelsKP hM)) (v 0) A F) :=
    image_fseq_l hM hN e hi he frame.omega hw space
  exact ⟨hw,image_product_l e hi he frame.pair,image_product_l e hi he frame.triple,
    finite frame.inputs,finite frame.left,finite frame.right,finite frame.space,
    image_tree_l e hi he frame.source,image_tree_l e hi he frame.inverse,
    Td_alphabet_d.ground_l hM hN e hi he frame.alphabet frame.space frame.source frame.pair frame.triple,
    Td_alphabet_d.ground_l hM hN e hi he frame.filled_alphabet frame.space
      (frame.fill.tree_l hM frame.space frame.inverse) frame.pair frame.triple,
    frame.pull.image_l hM hN e hi he frame.omega hw frame.inputs frame.space frame.source frame.pair frame.triple,
    image_first_l hM hN e hi he frame.omega hw frame.space frame.fill⟩

variable (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Td_frame_d.native_map_l {ω c d X R Y S j : M.Domain}
    (hw : M.IsOmega ω) (source : Smdl_d I c X R) (target : Smdl_d I d Y S)
    (map : Smap_d I ω c d X Y j)
    (hX : (smdl_structure_l I (R := R) source.2.1).Models ZF)
    (hY : (smdl_structure_l I (R := S) target.2.1).Models ZF)
    {v : Fin 15 → (smdl_structure_l I (R := R) source.2.1).Domain}
    {w : Fin 15 → (smdl_structure_l I (R := S) target.2.1).Domain}
    (frame : Td_frame_d hX v) (points : ∀ i, Rd_entry_d (v i).val (w i).val j) : Td_frame_d hY w := by
  let ρ := (⟨v,fun _ => v 0⟩ : Env _ 15)
  let η := (⟨w,fun _ => w 0⟩ : Env _ 15)
  exact (td_frame_sat_l hY η Term.bound).mp
    ((smap_source_l I hZF hw source target map (td_frame_m Term.bound)
      (td_frame_closed_l _ (fun _ => rfl)) ρ η points).mp ((td_frame_sat_l hX ρ Term.bound).mpr frame))

theorem Td_frame_d.mem_l {ω c X R : M.Domain} (source : Smem_d I c X R) (trans : M.TransitiveSet X)
    (native : (smdl_structure_l I (R := R) source.1.2.1).Models ZF)
    {v : Fin 15 → (smdl_structure_l I (R := R) source.1.2.1).Domain}
    (frame : Td_frame_d native v) (hw : M.IsOmega ω) (eq : (v 0).val = ω) :
    Td_frame_d hZF (fun i => (v i).val) :=
  frame.image_l native hZF Subtype.val (fun _ _ h => Subtype.ext h) (smem_full_l I source trans) (eq.symm ▸ hw)

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 7.4：原 I 胜策产生扩张中 a(¬S) 的实际 I 胜策

最小合法请求扫描产生策略。若服从对局不在收益集中，闭决定性给出同一
反游戏的 II 胜策；实际反策略控制与严格高度下降矛盾。实数字母非空由
原 I 胜策自身推出，不作为额外前提。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal Descriptive Model.Forcing.Internal
universe u v
variable {M : Structure.{u}} {N : Structure.{v}}

def Td_negative_win_d (hZF : M.Models ZF) (ω A U₁ U₂ S : M.Domain) : Prop :=
  let I := kp_pair_l (ZF.modelsKP hZF)
  ∃ F J B W σ, Fseq_space_d I ω A F ∧ M.IsFunctionSpace I B ω A ∧
    (∀ n, M.mem n J ↔ M.mem n ω ∧ Gm_even_d I ω n) ∧
    (∀ f, M.mem f W ↔ M.mem f B ∧ Dg_first_win_d hZF ω U₁ U₂ S f) ∧
    Cg_win_d I true ω A F J B W σ

variable (hZFC : M.Models ZFC) (hNZFC : N.Models ZFC)
  (e : M.Domain → N.Domain) (hi : Function.Injective e)
  (he : ∀ a y, N.mem y (e a) ↔ ∃ c, M.mem c a ∧ e c = y)
local notation "hM" => ZFC.models_zf_l hZFC
local notation "hN" => ZFC.models_zf_l hNZFC
local notation "I" => kp_pair_l (ZF.modelsKP hM)
local notation "J" => kp_pair_l (ZF.modelsKP hN)
include hi he

theorem Td_game_d.generic_transfer_l {p : Tg_params_d M.Domain}
    {X F L G O B W C Z v σ U₁ U₂ ζ Q : M.Domain} {U : M.Domain → Prop} {g : N.Domain}
    (game : Td_game_d hZFC p X F L G O B W C Z v) (hd : Woodin_d I p.δ)
    (win : Cg_win_d I true p.ω X F O B W σ) (hw : N.IsOmega (e p.ω))
    (fg : Fn0_d (e p.ω) (e X) g) (surj : N.IsSetSurjectiveOnto J g (e p.ω) (e X))
    (tree : Td_tree_d I p.ω p.A p.S) (alphabet : Td_alphabet_d p.S U₁ U₂) (chosen : M.mem ζ U₁)
    (order : ∀ q r, Entry_d M q r Q ↔ M.mem q F ∧ M.mem r F ∧ M.MemberSubset r q)
    (generic : Generic_d M F Q F U)
    (origin : ∀ q, U q → ∀ j y, Rd_entry_d j y q → Rd_entry_d (e j) (e y) g) :
    Td_negative_win_d hN (e p.ω) (e p.A) (e U₁) (e U₂) (e p.S) := by
  obtain ⟨p₀,pair₀⟩ := (I).total p.e ζ
  have pending : Td_pending_d I p.ω p.A p.e p.S p₀ := ⟨tree,ζ,pair₀,(alphabet.1 ζ).mp chosen⟩
  have root := pending.root_l hM game.setup.omega game.setup.empty
  obtain ⟨a,ha⟩ := game.first_letter_l hZFC hd root win
  obtain ⟨F',O',B',W',finite,runs,turns,payoff⟩ :=
    td_negative_game_l hN hw (e p.A) (e U₁) (e U₂) (e p.S)
  obtain ⟨R,K,D,T,τ,control,scan,strategy,values,plays⟩ :=
    game.generic_strategy_l hZFC hN e hi he hd root win ha hw fg surj finite
  refine ⟨F',O',B',W',τ,finite,runs,turns,payoff,strategy,fun f hf follows => ?_⟩
  apply (payoff f).mpr
  refine ⟨hf,?_⟩
  apply Classical.byContradiction
  intro outside
  obtain ⟨Vc,Fc,Lc,Gc,Jc,Bc,Wc,Oc,counter⟩ := dg_counter_l hN hw (e U₁) (e U₂) f (e p.S)
  obtain ⟨σc,cwin⟩ := counter.second_wins_l hNZFC hw ((image_member_l e hi he).mpr chosen) outside
  obtain ⟨o,Rc,empty,cc⟩ := counter.control_l hN hw cwin
  have empty' y : ¬ N.mem y (e p.e) := fun hy => (he p.e y).mp hy |>.elim fun x hx => game.setup.empty x hx.1
  have eo := hN.1.eq_of_same_members o (e p.e) (fun y => iff_of_false (empty y) (empty' y))
  subst o
  have ff := fn0_of_function_l (ZF.modelsKP hN) ((runs f).mp hf)
  obtain ⟨H,run,_⟩ := plays f ff
  exact game.setup.generic_no_counter_l hZFC hN e hi he hd game.histories game.owner control ha hw scan surj ff
    (fun s y sy => ((values s y).mp sy).2)
    (fun n hn even s cut y ny => follows n hn ((turns n).mpr ⟨hn,even⟩) s cut y ny)
    run tree alphabet chosen order generic origin counter cc

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 7.4 在原 Col(ω,δ) 名称扩张中的实际出口

由 Woodin 的不可达性构造 δ 与 Vδ 的真实双射，重编码实际有限条件及泛型
滤子。扩张的 ZFC、规范地嵌入和所需满射全部由原强迫构造给出。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal Descriptive Model.Forcing.Internal
universe u
variable {M : Structure.{u}}

def Td_collapse_win_d (hZF : M.Models ZF) (ω δ A U₁ U₂ S : M.Domain) : Prop :=
  let I := kp_pair_l (ZF.modelsKP hZF)
  ∀ C Q, Fseq_space_d I ω δ C →
    (∀ p q, Entry_d M p q Q ↔ M.mem p C ∧ M.mem q C ∧ M.MemberSubset q p) →
    ∀ (O : Cond_order_d M C Q C) U (generic : Generic_d M C Q C U) b, U b →
      let N := extension_l M hZF C Q C U
      ∃ e : M.Domain → N.Domain, Function.Injective e ∧
        (∀ a y, N.mem y (e a) ↔ ∃ c, M.mem c a ∧ e c = y) ∧
        (∀ a t, Check_d M b a t → Qval_d M C Q C U t (e a)) ∧
        Td_negative_win_d (preserves_zf_l O hZF generic) (e ω) (e A) (e U₁) (e U₂) (e S)

variable (hZFC : M.Models ZFC)
local notation "hM" => ZFC.models_zf_l hZFC
local notation "I" => kp_pair_l (ZF.modelsKP hM)

theorem Td_game_d.collapse_transfer_l {p : Tg_params_d M.Domain}
    {X F L G J B W O Z v σ U₁ U₂ ζ : M.Domain}
    (game : Td_game_d hZFC p X F L G J B W O Z v) (hd : Woodin_d I p.δ)
    (win : Cg_win_d I true p.ω X F J B W σ)
    (tree : Td_tree_d I p.ω p.A p.S) (alphabet : Td_alphabet_d p.S U₁ U₂) (chosen : M.mem ζ U₁) :
    Td_collapse_win_d hM p.ω p.δ p.A U₁ U₂ p.S := by
  have inaccessible := hd
  obtain ⟨_,_,_,_,regular,strong,_⟩ := inaccessible
  obtain ⟨ρ,bij⟩ := ZFC.inaccessible_enumeration_l I hZFC game.setup.omega game.setup.above regular strong game.setup.rank
  obtain ⟨r,inverse,_⟩ := ZF.exists_inverseBijectionWithPairs hM I bij
  obtain ⟨R,order,source,_⟩ := subset_order_l M hM F
  intro C Q collapse ord target U generic b hb
  let N := extension_l M hM C Q C U
  have hNZFC : N.Models ZFC := preserves_zfc_l target hZFC generic
  have hN : N.Models ZF := ZFC.models_zf_l hNZFC
  obtain ⟨e,hv,he,hi⟩ := check_map_l target hM generic hb
  have hw := image_omega_l (hEN := hN.1) e hi he hM (internal_foundation_l target hM generic) game.setup.omega
    (fun D => KP.difference_exists_d (ZF.modelsKP hN) D (e p.ω))
  obtain ⟨g,fg,onto,graph⟩ := fseq_generic_surjection_l hM game.setup.omega collapse ord generic target
    ⟨p.ω,game.setup.above⟩ hb e hi he hv
  obtain ⟨V,h,gen,fn,surj,origin⟩ := fseq_recode_generic_l hM hN e hi he game.setup.omega game.histories.1
    collapse inverse source order ord generic fg onto
    (fun q hq i y iy => (graph (e i) (e y)).mpr ⟨q,hq,i,y,iy,rfl,rfl⟩)
  exact ⟨e,hi,he,hv,game.generic_transfer_l hZFC hNZFC e hi he hd win hw
    (fn0_of_function_l (ZF.modelsKP hN) fn) surj tree alphabet chosen order gen origin⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 逆像树的反 demanding 胜策回到合法树

先限制普通全历史策略到本方回合，再由虚拟对局模拟产生合法树策略。
每条实际服从枝都对应一条原胜策对局；反游戏胜策沿同一节点包含关系运输。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal Descriptive
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

def Td_tree_negative_d (ω A F R U V S : M.Domain) : Prop :=
  ∃ σ, Gt_strategy_d hZF true ω A R σ ∧ ∀ f, Fn0_d ω A f → Branch_d F R f →
    Gm_follows_d I true ω σ f → Dg_first_win_d hZF ω U V S f

theorem Td_negative_win_d.tree_l {ω A F₀ R π U V P Y F S T W one z a : M.Domain}
    (win : Td_negative_win_d hZF ω A U V W)
    (hw : M.IsOmega ω) (inputs : Fseq_space_d I ω A F₀) (tree : Tree_d F₀ R)
    (retract : Tr_retract_d I ω A F₀ R π) (empty : ∀ x, ¬ M.mem x z) (root : M.mem z R) (ha : M.mem a A)
    (space : Fseq_space_d I ω Y F) (alphabet : Td_alphabet_d S U V)
    (pair : M.IsCartesianProduct I P U V) (triple : M.IsCartesianProduct I Y A P)
    (pull : Td_pull_d hZF ω A F π S T) (fill : Tr_first_d hZF F one T W) :
    Td_tree_negative_d hZF ω A F₀ R U V S := by
  obtain ⟨F',J,B,C,σ,finite,runs,turns,payoff,strategy,wins⟩ := win
  have eq : F' = F₀ := hZF.1.eq_of_same_members F' F₀ (fun s => (finite s).trans (inputs s).symm)
  subst F'
  obtain ⟨O,own⟩ := gm_turns_l hZF true ω A F₀
  obtain ⟨τ,fn,cut⟩ := own.restrict_l (ZF.modelsKP hZF) strategy
  obtain ⟨υ,legal,simulate⟩ := retract.strategy_l hZF hw inputs tree empty root ha ⟨O,own,fn⟩
  refine ⟨υ,legal,?_⟩
  intro f ff branch follows
  obtain ⟨x,fx,played,path⟩ := simulate f ff branch follows
  have played := (own.follows_l (ZF.modelsKP hZF) hw inputs fx cut).mp played
  have won := wins x ((runs x).mpr (fn0_function_l (ZF.modelsKP hZF) fx))
    (fun n hn turn s rest a na => played n hn ((turns n).mp turn).2 s rest a na)
  exact pull.filled_counter_l hZF fill hw space alphabet pair triple fx path ((payoff x).mp won).2

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 7.12 的实际坍缩泛型分支

对每个实际 Col(ω,δ) 泛型，运输既定收缩和逆像树，然后在该扩张内
模拟胜策。策略允许依赖泛型，全部服从对局也在相应扩张中量化。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal Descriptive Model.Forcing.Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

def Td_tree_collapse_d (ω δ A F R U V S : M.Domain) : Prop :=
  ∀ C Q, Fseq_space_d I ω δ C →
    (∀ p q, Entry_d M p q Q ↔ M.mem p C ∧ M.mem q C ∧ M.MemberSubset q p) →
    ∀ (O : Cond_order_d M C Q C) G (generic : Generic_d M C Q C G) b, G b →
      let N := extension_l M hZF C Q C G
      ∃ e : M.Domain → N.Domain, Function.Injective e ∧
        (∀ a y, N.mem y (e a) ↔ ∃ c, M.mem c a ∧ e c = y) ∧
        (∀ a t, Check_d M b a t → Qval_d M C Q C G t (e a)) ∧
        Td_tree_negative_d (preserves_zf_l O hZF generic) (e ω) (e A) (e F) (e R) (e U) (e V) (e S)

theorem Td_collapse_win_d.tree_l {ω δ A F₀ R π U V P Y F S T W one z a : M.Domain}
    (win : Td_collapse_win_d hZF ω δ A U V W)
    (hw : M.IsOmega ω) (inputs : Fseq_space_d I ω A F₀) (tree : Tree_d F₀ R)
    (retract : Tr_retract_d I ω A F₀ R π) (empty : ∀ x, ¬ M.mem x z) (root : M.mem z R) (ha : M.mem a A)
    (space : Fseq_space_d I ω Y F) (source : Tree_d F S) (alphabet : Td_alphabet_d S U V)
    (pair : M.IsCartesianProduct I P U V) (triple : M.IsCartesianProduct I Y A P)
    (pull : Td_pull_d hZF ω A F π S T) (fill : Tr_first_d hZF F one T W) :
    Td_tree_collapse_d hZF ω δ A F₀ R U V S := by
  intro C Q finite order O G generic b hb
  let N := extension_l M hZF C Q C G
  have hN : N.Models ZF := preserves_zf_l O hZF generic
  obtain ⟨e,hi,he,check,negative⟩ := win C Q finite order O G generic b hb
  have hw' := image_omega_l (hEN := hN.1) e hi he hZF (internal_foundation_l O hZF generic) hw
    (fun D => KP.difference_exists_d (ZF.modelsKP hN) D (e ω))
  exact ⟨e,hi,he,check,negative.tree_l hN hw'
    (image_fseq_l hZF hN e hi he hw hw' inputs) (image_tree_l e hi he tree)
    (image_retract_l hZF hN e hi he hw hw' inputs tree retract)
    (fun y hy => (he z y).mp hy |>.elim fun x hx => empty x hx.1)
    ((image_member_l e hi he).mpr root) ((image_member_l e hi he).mpr ha)
    (image_fseq_l hZF hN e hi he hw hw' space) (Td_alphabet_d.ground_l hZF hN e hi he alphabet space source pair triple)
    (image_product_l e hi he pair) (image_product_l e hi he triple)
    (pull.image_l hZF hN e hi he hw hw' inputs space source pair triple)
    (image_first_l hZF hN e hi he hw hw' space fill)⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 沿同一 demanding 原运行构造相容复制序列

复制状态同时记录原运行中的实际行和四项工作图。两种工厂已经证明每一步
保持复制帧，因此模型内部的类依赖选择产生整个 ω 序列，不另加后继假设。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

def Td_copy_state_d (hZF : M.Models ZF) (ω H i t : M.Domain) : Prop :=
  ∃ v : Fin 66 → M.Domain, ∃ s J S Q G,
    Rd_entry_d i s H ∧ Rt_tuple_d v s ∧ Rd_quad_d t J S Q G ∧
      Ic_frame_d hZF ω (td_copy_frame_d (fun k => v (k.castAdd 47))) J S Q G

def td_copy_state_m {d} (ω H i t : Term d) : Formula 1 d :=
  let e : Term d → Term (66+d) := fun x => x.rename (Fin.natAdd 66)
  let f : Term (66+d) → Term (5+(66+d)) := fun x => x.rename (Fin.natAdd 5)
  let v : Fin 66 → Term (5+(66+d)) := fun k => f (.bound (k.castAdd d))
  let z : Fin 5 → Term (5+(66+d)) := fun k => .bound (k.castAdd (66+d))
  rb_exists_m (n := 66) (rb_exists_m (n := 5)
    (.conj (rd_entry0_m (f (e i)) (z 0) (f (e H)))
      (.conj (rt_tuple_m v (z 0)) (.conj (rd_quad_m (f (e t)) (z 1) (z 2) (z 3) (z 4))
        (ic_frame_m (f (e ω)) (td_copy_frame_d (fun k => v (k.castAdd 47))) (z 1) (z 2) (z 3) (z 4))))))

@[simp] theorem td_copy_state_closed_l {d} (ω H i t : Term d)
    (hω : ω.freeSupport = []) (hH : H.freeSupport = []) (hi : i.freeSupport = []) (ht : t.freeSupport = []) :
    (td_copy_state_m ω H i t).FreeClosed := by
  simp -implicitDefEqProofs [td_copy_state_m,Definitional.Formula.FreeClosed,td_copy_frame_d,hω,hH,hi,ht]
  exact rt_tuple_closed_l _ _ (fun _ => rfl) rfl

theorem td_copy_state_sat_l (hZF : M.Models ZF) {d} (ρ : Env M d) (ω H i t : Term d) :
    Formula.satisfies ρ (td_copy_state_m ω H i t) ↔
      Td_copy_state_d hZF (ω.eval ρ) (H.eval ρ) (i.eval ρ) (t.eval ρ) := by
  simp only [td_copy_state_m,rb_exists_sat_l,Formula.satisfies_conj_iff,
    rd_entry0_sat_l hZF.1,rt_tuple_sat_l hZF.1,rd_quad_sat_l hZF.1,ic_frame_sat_l hZF,
    td_copy_frame_d,Definitional.Term.eval_rename,Env.reindex,Function.comp_def,
    Term.eval_bound,Fin.addCases_left,Fin.addCases_right]
  exact ⟨fun ⟨v,z,entry,code,quad,frame⟩ => ⟨v,z 0,z 1,z 2,z 3,z 4,entry,code,quad,frame⟩,
    fun ⟨v,s,J,S,Q,G,entry,code,quad,frame⟩ => ⟨v,fun i => [s,J,S,Q,G].get i,entry,code,quad,frame⟩⟩

variable (hZFC : M.Models ZFC)
local notation "hZF" => ZFC.models_zf_l hZFC
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Td_run_d.copy_sequence_l {g : Fin 10 → M.Domain} {X K r a f H o J₀ S₀ Q₀ G₀ : M.Domain}
    (run : Td_run_d hZF g X K r a f H) (empty : ∀ x, ¬ M.mem x o)
    {v₀ : Fin 66 → M.Domain} (initial : Rt_tuple_d v₀ r)
    (frame : Ic_frame_d hZF (g 0) (td_copy_frame_d (fun k => v₀ (k.castAdd 47))) J₀ S₀ Q₀ G₀) :
    ∃ D F t₀, Fn0_d (g 0) D F ∧ Rd_entry_d o t₀ F ∧ Rd_quad_d t₀ J₀ S₀ Q₀ G₀ ∧
      (∀ i t, Rd_entry_d i t F → Td_copy_state_d hZF (g 0) H i t) ∧
      ∀ i j s t, M.SuccessorOf j i → Rd_entry_d i s F → Rd_entry_d j t F → Ic_extend_d s t := by
  have hw := run.omega_l hZF
  obtain ⟨t₀,quad₀⟩ := rd_quad_exists_l (ZF.modelsKP hZF) J₀ S₀ Q₀ G₀
  let η : Env M 2 := ⟨Fin.cases H (fun _ => g 0),fun _ => H⟩
  let V : BinarySchema 2 := { body := td_copy_state_m (.bound 3) (.bound 2) (.bound 1) .newest }
  let φ : UnarySchema 4 := { body := ic_extend_m (.bound 1) .newest }
  have valid i t : V.denote η i t ↔ Td_copy_state_d hZF (g 0) H i t := td_copy_state_sat_l hZF ..
  have step i s t : φ.denote ((η.push i).push s) t ↔ Ic_extend_d s t := ic_extend_sat_l hZF.1 ..
  obtain ⟨D,F,fn,start,all,chain⟩ := ZFC.class_indexed_choice_l I hZFC V φ η hw empty
    ((valid o t₀).mpr ⟨v₀,r,J₀,S₀,Q₀,G₀,run.recursion.2.1 o empty,initial,quad₀,frame⟩) (by
      intro i j t hi succ ht
      obtain ⟨v,s,J,S,Q,G,hs,code,quad,frame⟩ := (valid i t).mp ht
      obtain ⟨j₀,sj,hj⟩ := hw.1.2 i hi
      have eq := sj.eq hZF.1 succ
      subst j₀
      obtain ⟨s',_,hs'⟩ := run.recursion.1.2.1 j hj
      obtain ⟨_,_,v',w,ps,pt,round⟩ := run.steps i j s s' succ hs hs'
      have eq := rt_tuple_inj_l ps code
      subst v'
      obtain ⟨J',S',Q',G',next,rows,codes,maps⟩ := round.1 J S Q G frame
      obtain ⟨t',quad'⟩ := rd_quad_exists_l (ZF.modelsKP hZF) J' S' Q' G'
      exact ⟨t',(valid j t').mpr ⟨w,s',J',S',Q',G',hs',pt,quad',next⟩,
        (step i t t').mpr ⟨J,S,Q,G,J',S',Q',G',quad,quad',rows,codes,maps⟩⟩)
  exact ⟨D,F,t₀,fn0_of_function_l (ZF.modelsKP hZF) fn,start,quad₀,
    fun i t ht => (valid i t).mp (all i t ht),
    fun i j s t succ hs ht => (step i s t).mp (chain i j s t succ hs ht)⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## demanding 同一全运行的完整工作复制

有限历史先改读为原并树上的历史，已实施区间的操作及支撑双向保持。
相容序列的并产生长度 ω 的真实历史；其规范呈示、实际施加和严格支撑增长
组成 nice 工作树，并保留指定根嵌入。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}
section
variable (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Td_run_d.copy_original_l {g : Fin 10 → M.Domain} {X K r a f H i s J S Qw Gw : M.Domain}
    (run : Td_run_d hZF g X K r a f H) {U : Fin 6 → M.Domain} (u : Td_union_d hZF g H U)
    {v : Fin 66 → M.Domain} (hs : Rd_entry_d i s H) (code : Rt_tuple_d v s)
    (frame : Ic_frame_d hZF (g 0) (td_copy_frame_d (fun k => v (k.castAdd 47))) J S Qw Gw) :
    Ic_history_d hZF (g 0) (U 0) (U 1) (U 2) (U 3) (U 4) (v 6) J S Qw Gw := by
  obtain ⟨_,Λ,_,levels,hist,_⟩ := frame
  have state := run.read_l hZF hs code
  have keep (b : Fin 6) {x y : M.Domain}
      (entry : Rd_entry_d x y (v (td_frame_idx_d ⟨8+b.val,by omega⟩))) := u.entry_l hZF hs code b entry
  have order := u.restriction i s v hs code
  have maps j k q (hk : M.mem k (v 6)) (hq : It_map_d (U 2) j k q) : It_map_d (v 9) j k q := by
    obtain ⟨q',r,pair,entry⟩ := state.tree.diagram.map_l hZF
      ((order j k hk).mp (u.tree.diagram.map_bound_l hZF hq))
    have eq := u.tree.diagram.map_unique_l hZF ⟨r,pair,keep 2 entry⟩ hq
    exact eq ▸ ⟨r,pair,entry⟩
  have moves j p (hj : M.mem j (v 5)) (hp : Rd_entry_d j p (U 3)) : Rd_entry_d j p (v 10) := by
    have no := state.tree.diagram.order.ordinal.mem state.successor.predecessor_mem
    obtain ⟨k,succ⟩ := KP.exists_successor (ZF.modelsKP hZF) j
    have sub : M.MemberSubset k (v 5) := by
      intro x hx
      rcases (succ x).mp hx with hx | eq
      · exact no.transitive j hj x hx
      · exact (hZF.1.eq_of_same_members x j eq).symm ▸ hj
    have hk : M.mem k (v 6) := Structure.IsOrdinal.mem_of_properSubset hZF.1
      (KP.successor_isOrdinal (ZF.modelsKP hZF) (no.mem hj) succ) state.tree.diagram.order.ordinal
      ⟨fun x hx => (state.successor x).mpr (Or.inl (sub x hx)),fun eq =>
        KP.mem_irrefl_d (ZF.modelsKP hZF) (v 5) (sub (v 5) ((eq (v 5)).mpr state.successor.predecessor_mem))⟩
      (KP.difference_exists_d (ZF.modelsKP hZF) k (v 6))
    obtain ⟨q,hq⟩ := (state.tree.move_domain j).mpr ⟨k,hk,succ⟩
    exact u.tree.move_function.2 j q p (keep 3 hq) hp ▸ hq
  have supports j ρ (hj : M.mem j (v 5)) : Rd_entry_d j ρ (U 4) ↔ Rd_entry_d j ρ Λ := by
    constructor
    · intro hρ
      obtain ⟨p,κ,F,hp,pay⟩ := (u.levels j ρ).mp hρ
      exact (levels j ρ).mpr ⟨p,κ,F,moves j p hj hp,pay⟩
    · intro hρ
      obtain ⟨p,κ,F,hp,pay⟩ := (levels j ρ).mp hρ
      exact (u.levels j ρ).mpr ⟨p,κ,F,keep 3 hp,pay⟩
  exact hist.original_prefix_l hZF state.successor order (fun _ _ _ hi => keep 1 hi) maps moves supports

end
variable (hZFC : M.Models ZFC)
local notation "hZF" => ZFC.models_zf_l hZFC
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Td_run_d.copy_history_l {g : Fin 10 → M.Domain} {X K r a f H o J₀ S₀ Q₀ G₀ : M.Domain}
    (run : Td_run_d hZF g X K r a f H) {U : Fin 6 → M.Domain} (u : Td_union_d hZF g H U)
    (empty : ∀ x, ¬ M.mem x o) {v₀ : Fin 66 → M.Domain} (initial : Rt_tuple_d v₀ r)
    (frame : Ic_frame_d hZF (g 0) (td_copy_frame_d (fun k => v₀ (k.castAdd 47))) J₀ S₀ Q₀ G₀) :
    ∃ J Qw Gw, Ic_history_d hZF (g 0) (U 0) (U 1) (U 2) (U 3) (U 4) (g 0) J (U 0) Qw Gw ∧
      M.MemberSubset J₀ J ∧ M.MemberSubset Q₀ Qw ∧ M.MemberSubset G₀ Gw := by
  obtain ⟨D,F,t₀,fn,start,quad₀,valid,chain⟩ := run.copy_sequence_l hZFC empty initial frame
  have frames i t (ht : Rd_entry_d i t F) : ∃ m J S Q G, M.mem m (g 0) ∧ M.mem i m ∧
      Rd_quad_d t J S Q G ∧ Ic_history_d hZF (g 0) (U 0) (U 1) (U 2) (U 3) (U 4) m J S Q G := by
    obtain ⟨v,s,J,S,Q,G,hs,code,quad,frame⟩ := valid i t ht
    have state := run.read_l hZF hs code
    obtain ⟨m,succ,hm⟩ := u.tree.omega.1.2 (v 5) state.finite
    exact ⟨v 6,J,S,Q,G,succ.eq hZF.1 state.successor ▸ hm,run.span_l hZF hs ⟨v,code,rfl⟩,
      quad,run.copy_original_l hZF u hs code frame⟩
  obtain ⟨J,Qw,Gw,hist,kept⟩ := ic_sequence_union_l hZF u.tree.omega u.tree.diagram fn frames chain
  exact ⟨J,Qw,Gw,hist,kept o t₀ J₀ S₀ Q₀ G₀ start quad₀⟩

/-- 指定原根嵌入实际复制全运行；初态的空历史界来自原游戏的空对象。 -/
theorem Td_run_d.copy_l {g : Fin 10 → M.Domain} {X K r a f H A π z Z α : M.Domain}
    (run : Td_run_d hZF g X K r a f H) {U : Fin 6 → M.Domain} (u : Td_union_d hZF g H U)
    {v : Fin 66 → M.Domain} (initial : Rt_tuple_d v r)
    (empty : ∀ x, ¬ M.mem x (v 5))
    (zero : ∀ x, M.mem x (v 0) → ¬ Rd_entry_d x (v 13) (v 1))
    (row : Ic_row_d hZF (g 0) (v 2) (v 0) A π z Z α) :
    ∃ J Qw Gw Ew Lw,
      Ic_history_d hZF (g 0) (U 0) (U 1) (U 2) (U 3) (U 4) (g 0) J (U 0) Qw Gw ∧
      It_pnice_d hZF (g 0) z (g 0) (U 0) Qw Gw Ew Lw ∧ Ic_at_d J (v 5) (v 0) A π z Z α ∧
      ∀ i p, Rd_entry_d i p Ew ↔ Ic_operation_d J (U 3) i p := by
  have state := run.read_l hZF (run.recursion.2.1 (v 5) empty) initial
  obtain ⟨J₀,S₀,Q₀,G₀,frame,first⟩ := row.frame_l hZF state.tree state.successor empty state.node
    state.model (state.model.2.2.2 _ _ state.height).1 zero
  have frame : Ic_frame_d hZF (g 0) (td_copy_frame_d (fun k => v (k.castAdd 47))) J₀ S₀ Q₀ G₀ := by
    rw [td_copy_frame_values_l]
    exact frame
  obtain ⟨J,Qw,Gw,hist,rows,_,_⟩ := run.copy_history_l hZFC u empty initial frame
  have start : Ic_at_d J (v 5) (v 0) A π z Z α := by
    obtain ⟨t,⟨p,pair,hp⟩,cell⟩ := first
    exact ⟨t,⟨p,pair,rows p hp⟩,cell⟩
  obtain ⟨Ew,Lw,nice,operations⟩ := hist.nice_l hZF u.tree u.levels empty start
  exact ⟨J,Qw,Gw,Ew,Lw,hist,nice,start,operations⟩

/-- 实际开局的任意根工作嵌入都能复制同一原并树。 -/
theorem Td_run_d.copyable_l {g : Fin 10 → M.Domain} {X K r a f H : M.Domain}
    (run : Td_run_d hZF g X K r a f H) {U : Fin 6 → M.Domain} (u : Td_union_d hZF g H U)
    {v : Fin 66 → M.Domain} (initial : Rt_tuple_d v r)
    (empty : ∀ x, ¬ M.mem x (v 5))
    (zero : ∀ x, M.mem x (v 0) → ¬ Rd_entry_d x (v 13) (v 1)) :
    It_copyable_d hZF (g 0) (g 1) (U 0) (U 1) (U 2) (U 3) := by
  have first := run.recursion.2.1 (v 5) empty
  have state := run.read_l hZF first initial
  have ec := u.tree.diagram.model_function.2 (v 5) (v 2) (g 1)
    (u.entry_l hZF first initial 1 state.node) (u.tree.root (v 5) empty)
  refine ⟨U 4,u.levels_function,u.levels,?_⟩
  intro o Y A π z Z α ho row
  have eo := hZF.1.eq_of_same_members o (v 5) (fun x => iff_of_false (ho x) (empty x))
  subst o
  have saved := row
  obtain ⟨R,_,_,_,_,_,model,_⟩ := row
  have source : Smdl_d I (g 1) (v 0) (v 1) := ec ▸ state.model
  have eY := (smdl_unique_l I model source).1
  subst Y
  have row : Ic_row_d hZF (g 0) (v 2) (v 0) A π z Z α := ec.symm ▸ saved
  obtain ⟨J,Qw,Gw,_,_,hist,_,start,_⟩ := run.copy_l hZFC u initial empty zero row
  exact ⟨J,Qw,Gw,hist,start⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 原回合确实落下指定的实数字母

三次实际追加将请求后的时钟从余数一推进至余数二。完整数字图保持
内部轮号及奇偶，故偶数轮的事件正是对手输入的根像。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal Descriptive
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem td_issued_digit_event_l (ρ : Env M 47) (issued : Formula.satisfies ρ td_issued0_m)
    {h t H a y b : M.Domain} (answer : Fseq_end_d I (ρ.bound 0) h (ρ.bound 20) a)
    (digit : Fseq_end_d I (ρ.bound 0) t h y) (request : Fseq_end_d I (ρ.bound 0) H t b) :
    Tg_event_d I (ρ.bound 4) (ρ.bound 19) (ρ.bound 3) H y := by
  have state := (td_issued_sat_l I hZF.1 ρ).mp issued
  have control := state.control
  simp only [td_control0_m,Formula.satisfies_conj_iff] at control
  have rules := (td_rules_sat_l hZF _ (tg_control_params_d Term.bound)
    (.bound 12) (.bound 13) (.bound 14) (.bound 16)).mp control.2.2.1
  obtain ⟨_,_,ans⟩ := answer
  obtain ⟨_,_,dig⟩ := digit
  have old := ans.prefix_sequence.2.2.2.eq hZF.1 (fn0_function_l (ZF.modelsKP hZF) state.history).2.1
  have same := ans.source.2.2.2.eq hZF.1 dig.prefix_sequence.2.2.2
  obtain ⟨hc,_⟩ := tg_clock_l hZF rules.omega rules.empty rules.one rules.two rules.three state.time
  have clock := tg_division_next_l hZF (rules.omega.members_areOrdinals (ZF.modelsKP hZF) _ hc)
    state.clock rules.two (old ▸ same ▸ ans.length_successor) rules.three.predecessor_mem
  exact (show Tg_event_d I (ρ.bound 4) (ρ.bound 19) (ρ.bound 3) t y from
    ⟨_,clock,dig.last_value⟩).end_l request

theorem Td_run_step_d.even_real_l {g : Fin 10 → M.Domain} {v w : Fin 66 → M.Domain} {x : M.Domain}
    (old : Td_state_d hZF g (fun i => v (i.castAdd 47)) (fun i => v (Fin.natAdd 19 i)))
    (next : Td_state_d hZF g (fun i => w (i.castAdd 47)) (fun i => w (Fin.natAdd 19 i)))
    (root : Zc_model_d I (g 0) (g 1) (g 3) (g 4))
    (step : Td_run_step_d hZF g x (fun i => v (i.castAdd 47)) (fun i => w (i.castAdd 47))
      (fun i => v (Fin.natAdd 19 i)) (fun i => w (Fin.natAdd 19 i)))
    (even : Gm_even_d I (g 0) (v 12)) : Td_real_d I w (v 12) x := by
  obtain ⟨_,_,_,_,_,j,_,e,e',edge,_,images,_⟩ := step.2
  obtain ⟨u,points,head,h,t,y,z,xz,digit⟩ := images
  have map := next.tree.diagram.elementary (v 5) (w 5) j (v 2) (v 0) (v 1) (w 2) (w 0) (w 1)
    edge (e'.2.2.1 _ _ (e.2.2.1 _ _ old.node)) next.node old.model next.model
  have origin := next.tree.diagram.elementary (g 2) (w 5) (w 3) (g 1) (g 3) (g 4) (w 2) (w 0) (w 1)
    next.origin next.root_node next.node root.model next.model
  have native := ZFC.models_zf_l ((root.map_l hZF next.tree.omega next.model origin).native_l I hZF next.tree.omega)
  have hN := ZF.modelsKP native
  let N := smdl_structure_l I (R := w 1) next.model.2.1
  let ρ : Env N 47 := ⟨fun i => ⟨u i,map.1.1.output_mem_of_pairMember (points i)⟩,
    fun _ => ⟨u 0,map.1.1.output_mem_of_pairMember (points 0)⟩⟩
  have raw := old.issued.map_l I hZF next.tree.omega old.model next.model map td_issued0_closed_l points
  have issued : Formula.satisfies ρ td_issued0_m :=
    (rr_truth_native_l I next.model.2.1 td_issued0_m td_issued0_closed_l ρ.bound).mp raw
  have wn : w 19 = u 0 := head 0
  have wc : w 23 = u 4 := head 4
  have wb : w 22 = u 3 := head 3
  obtain ⟨ev,_⟩ := old.native_base_l hZF
  have extV : Rf_ext_d I (v 0) (v 1) := fun a ha b hb same => congrArg Subtype.val
    (ev.eq_of_same_members ⟨a,ha⟩ ⟨b,hb⟩ (fun z => same z.val z.property))
  have extW : Rf_ext_d I (w 0) (w 1) := fun a ha b hb same => congrArg Subtype.val
    (hN.1.eq_of_same_members ⟨a,ha⟩ ⟨b,hb⟩ (fun z => same z.val z.property))
  obtain ⟨n,hn,index⟩ := next.numbers.injection.1.2.2 (v 12) old.round
  have image := (old.numbers.omega_map_l I hZF next.tree.omega old.model next.model map extV extW next.numbers).2
    (v 12) (v 38) n old.index index
  have eq := map.1.1.1.2 (v 38) n (u 19) image (points 19)
  have index : Rd_entry_d (v 12) (u 19) (w 4) := eq ▸ index
  have parity := (next.numbers.even_l hZF next.tree.omega native old.round (ρ.bound 19) index).mp even
  have parity : Gm_even_d (kp_pair_l hN) (ρ.bound 0) (ρ.bound 19) :=
    (show (⟨w 19,next.numbers.member⟩ : N.Domain) = ρ.bound 0 from Subtype.ext wn) ▸ parity
  let q := td_digit_values_d u (fun i => w (Fin.natAdd 19 i)) h t y z
  let η : Env N 11 := ⟨fun i => ⟨q i,digit.1 i⟩,fun _ => ρ.bound 0⟩
  have data := (td_digit0_sat_l hN η).mp
    ((rr_truth_native_l I next.model.2.1 td_digit0_m td_digit0_closed_l η.bound).mp digit)
  have yz : y = z := congrArg Subtype.val (data.2.1 parity)
  obtain ⟨b,answer⟩ := data.2.2.2.2.2.2
  have event := td_issued_digit_event_l native ρ issued answer data.2.2.2.1 data.2.2.2.2.1
  have event : Tg_event_d (kp_pair_l hN) ⟨w 23,next.issued.1 4⟩ (ρ.bound 19)
      ⟨w 22,next.issued.1 3⟩ ⟨w 39,next.issued.1 20⟩ ⟨y,digit.1 8⟩ := by
    have ec : ρ.bound 4 = (⟨w 23,next.issued.1 4⟩ : N.Domain) := Subtype.ext wc.symm
    have eb : ρ.bound 3 = (⟨w 22,next.issued.1 3⟩ : N.Domain) := Subtype.ext wb.symm
    exact ec ▸ eb ▸ event
  refine ⟨u 19,y,index,yz.symm ▸ xz,?_,?_⟩
  · exact Fin.cases (next.issued.1 4) (Fin.cases (ρ.bound 19).property
      (Fin.cases (next.issued.1 3) (Fin.cases (next.issued.1 20)
        (Fin.cases (digit.1 8) (fun i => Fin.elim0 i)))))
  · exact (tg_event_sat_l (kp_pair_l hN) hN.1 _ (.bound 0) (.bound 1) (.bound 2) (.bound 3) (.bound 4)).mpr event

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 原 II 胜策的统一内部 demanding 运行

从原树已有的辅助字母读出一个实际实数字母。初态、响应表和所有完整输入
的运行依次实际构造，并给出奇枝深度覆盖、偶数枝的不良基直接极限，
先固定同一完整原实数对局，再对任意良基奇枝给出原树像中的三坐标
无限分支及第一辅助图满射；
不额外要求原模型可数、ω 标准或已有无限运行。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal Descriptive
universe u
variable {M : Structure.{u}} (hZFC : M.Models ZFC)
local notation "hZF" => ZFC.models_zf_l hZFC
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Td_game_d.iteration_run_l
    {Ω c X R z : M.Domain} (hΩ : M.IsOmega Ω) (certificate : Zc_model_d I Ω c X R)
    {p : Tg_params_d (smdl_structure_l I (R := R) certificate.model.2.1).Domain}
    (numbers : Rr_layer_d I Ω X R p.ω.val z)
    {A F L G J B W O Z g σ U₁ U₂ a : (smdl_structure_l I (R := R) certificate.model.2.1).Domain}
    (game : Td_game_d (certificate.native_l I hZF hΩ) p A F L G J B W O Z g)
    (woodin : Woodin_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l
      (certificate.native_l I hZF hΩ)))) p.δ)
    (win : Cg_win_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l
      (certificate.native_l I hZF hΩ)))) false p.ω A F J B W σ)
    (treeS : Td_tree_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l
      (certificate.native_l I hZF hΩ)))) p.ω p.A p.S)
    (alphabet : Td_alphabet_d p.S U₁ U₂)
    (chosen : (smdl_structure_l I (R := R) certificate.model.2.1).mem a U₁)
    (separated : Td_separated_d p.S)
    (powerCount : Pc_count_d I Ω X R p.δ.val)
    (coding : ∃ P, (smdl_structure_l I (R := R) certificate.model.2.1).IsPowerSetOf P p.δ ∧
      (smdl_structure_l I (R := R) certificate.model.2.1).CardinalLessOrEqual
        (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l (certificate.native_l I hZF hΩ)))) U₁ P) :
    ∃ H, ∃ ι : Env (smdl_structure_l I (R := R) certificate.model.2.1) 47,
      (∀ i : Fin 19, ι.bound (i.castAdd 28) =
        [p.ω,p.e,p.a,p.b,p.c,p.δ,p.A,p.S,p.ν,p.E,p.P,p.Q,A,F,L,G,J,σ,H].get i) ∧
    ∃ o m T Q G₀ q A₀ D₀ V t Λ a₀ r Y D K,
      (∀ x, ¬ M.mem x o) ∧ M.mem a₀ A₀ ∧
      Tg_root_cut_d I c X R p.ω.val (ι.bound 24).val V p.A.val D₀ A₀ ∧
    let g : Fin 10 → M.Domain := fun i => [Ω,c,o,X,R,(ι.bound 24).val,D₀,p.e.val,p.A.val,p.S.val].get i
    let v : Fin 19 → M.Domain := fun i => [X,R,c,q,z,o,m,T,Q,G₀,o,o,o,p.e.val,p.e.val,(ι.bound 24).val,V,t,Λ].get i
    Rt_tuple_d (Fin.addCases (m := 19) (n := 47) (motive := fun _ => M.Domain) v (fun i => (ι.bound i).val)) r ∧
      Td_choice_d hZF g A₀ r Y D K ∧ ∀ f, Fn0_d Ω A₀ f →
        ∃ run, Td_run_d hZF g Y K r a₀ f run ∧
          ∃ U : Fin 6 → M.Domain, Td_union_d hZF g run U ∧
            It_copyable_d hZF Ω c (U 0) (U 1) (U 2) (U 3) ∧ Td_depth_cover_d Ω (U 5) (U 0) (U 2) ∧
            ∃ play, Td_run_play_d I Ω A₀ run play ∧
            ∃ B, It_ill_branch_d hZF Ω Ω (U 0) (U 1) (U 2) B ∧
              (∀ x, M.mem x B ↔ Tg_even_d (5 : Fin 66) run (U 0) x) ∧
              ∀ b, It_wf_branch_d hZF Ω Ω (U 0) (U 1) (U 2) b →
                Td_branch_projection_d hZF Ω o p.S.val (U 1) (U 2) b play := by
  -- 最小辅助域中的字母确实出现于原树，故同一节点给出默认实数字母。
  obtain ⟨q,i,t,x,b,d,s,hq,it,_⟩ := (alphabet.1 a).mp chosen
  obtain ⟨_,_,_,triples⟩ := treeS.nodes q hq
  obtain ⟨x₀,_,_,_,hx,_,_⟩ := triples i t it
  obtain ⟨H,ι,head,o,m,T,Q,G₀,q,A₀,D₀,V,t,Λ,empty,cut,initial⟩ :=
    game.iteration_start_l hZF hΩ certificate numbers woodin win treeS alphabet chosen separated powerCount coding
  have ha : M.mem x₀.val A₀ := (cut.letters x₀.val).mpr ⟨x₀.property,hx⟩
  -- 先固定全体输入共用的响应表，再对每个完整输入取内部运行及其并树。
  obtain ⟨r,Y,D,K,tuple,choice,runs⟩ := initial.recursion_l hZFC certificate numbers cut.letters rfl empty ha
  refine ⟨H,ι,head,o,m,T,Q,G₀,q,A₀,D₀,V,t,Λ,x₀.val,r,Y,D,K,empty,ha,cut,tuple,choice,?_⟩
  intro f hf
  obtain ⟨run,valid⟩ := runs f hf
  obtain ⟨U,tree,cover⟩ := valid.bookkeeping_l hZF
  have copy := valid.copyable_l hZFC tree tuple empty
    (fun x hx => game.setup.empty ⟨x,hx⟩)
  obtain ⟨play,played⟩ := valid.play_l hZF tree certificate cut.letters
  obtain ⟨B,ill,even⟩ := valid.even_limit_l hZF tree
  exact ⟨run,valid,U,tree,copy,cover,play,played,B,ill,even,
    fun _ wf => valid.wf_projection_l hZF tree certificate (fun x hx => ((cut.letters x).mp hx).1) played wf⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 收缩像保留同一 demanding 迭代树

在每条实际良基枝上，根腿固定有限历史收缩。原公式运输同一逆像及补全树；
去掉首层补全后，同两张辅助图给出原树投影，第一坐标的满射完全不变。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal Descriptive
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Td_fixed_gp_d.retract_l {c X E o R z x y : M.Domain}
    (source : Smem_d I c X E) (trans : M.TransitiveSet X)
    (native : (smdl_structure_l I (R := E) source.1.2.1).Models ZF)
    {v : Fin 15 → (smdl_structure_l I (R := E) source.1.2.1).Domain}
    (frame : Td_frame_d native v) (hw : M.IsOmega (v 0).val)
    (retract : Tr_retract_d I (v 0).val (v 1).val (v 6).val R (v 10).val)
    (hR : M.mem R X) (sub : M.MemberSubset R (v 6).val)
    (empty : ∀ a, ¬ M.mem a z) (succ : M.SuccessorOf (v 13).val z)
    (fx : Fn0_d (v 0).val (v 1).val x) (fy : Fn0_d (v 0).val (v 1).val y)
    (path : Tr_path_d hZF (v 0).val (v 10).val x y)
    (fixed : Td_fixed_gp_d hZF (v 0).val o c X (v 1).val (v 14).val x) :
    Td_fixed_gp_d hZF (v 0).val o c X (v 1).val (v 11).val y := by
  have original := frame.mem_l hZF source trans native hw rfl
  obtain ⟨ρ,γ,rank,lower,ordinal,T,Q,G,H,tree,owned,copy,bound,branches⟩ := fixed
  refine ⟨ρ,γ,rank,lower,ordinal,T,Q,G,H,tree,owned,copy,bound,?_⟩
  intro b wf
  obtain ⟨d,N,W,P,j,S,Y,F,U,V,target,nt,cone,leg,image,space,closed,alphabet,projection,map,fixedA,letters,low⟩ := branches b wf
  have native' := map.native_models_l hZF hw source.1 target.1 native
  obtain ⟨images,points⟩ := Classical.axiomOfChoice (fun i : Fin 15 => map.1.1.2.2 (v i).val (v i).property)
  let w : Fin 15 → (smdl_structure_l I (R := W) target.1.2.1).Domain := fun i => ⟨images i,(points i).1⟩
  have iw i : Rd_entry_d (v i).val (w i).val j := (points i).2
  have omega := map.omega_l I hZF hw trans nt source target (v 0).property
  have eq0 : (w 0).val = (v 0).val := map.1.1.1.2 _ _ _ (iw 0) omega
  have transported := (frame.native_map_l hZF hw source.1 target.1 map native native' iw).mem_l
    hZF target nt native' hw eq0
  obtain ⟨_,_,fixedπ⟩ := retract.fixed_l hZF hw trans nt source target map
    (v 0).property fixedA letters (v 6).property hR (v 10).property original.inputs sub
  have eqA : (w 1).val = (v 1).val := map.1.1.1.2 _ _ _ (iw 1) fixedA
  have eqπ : (w 10).val = (v 10).val := map.1.1.1.2 _ _ _ (iw 10) fixedπ
  have eqW : (w 14).val = S := map.1.1.1.2 _ _ _ (iw 14) image
  obtain ⟨e,he,heω⟩ := hw.1.1
  have ez := hZF.1.eq_of_same_members e z (fun a => iff_of_false (he a) (empty a))
  obtain ⟨one,sone,homega⟩ := hw.1.2 z (ez ▸ heω)
  have hOne := sone.eq hZF.1 succ ▸ homega
  have eqOne : (w 13).val = (v 13).val := map.1.1.1.2 _ _ _ (iw 13)
    (map.natural_l hZF hw trans nt source target (v 0).property (v 13).val hOne)
  obtain ⟨eqU,eqV⟩ := (eqW ▸ transported.filled_alphabet).ext_l hZF.1 alphabet
  have targetTree := transported.fill.tree_l hZF transported.space transported.inverse
  have copied : Td_projection_d hZF (w 0).val (w 2).val (w 3).val (w 5).val (w 9).val (w 14).val x := by
    have p := projection.space_l hZF hw space (eq0 ▸ transported.space) (eqW ▸ targetTree)
    simpa only [eq0,eqU,eqV,eqW] using p
  have p := transported.pull.filled_projection_l hZF transported.fill transported.omega
    transported.space transported.source transported.inverse transported.alphabet transported.pair transported.triple
    empty (by simpa only [eqOne] using succ)
    (by simpa only [eqπ] using (fn0_function_l (ZF.modelsKP hZF) retract.function).1)
    (by simpa only [eq0,eqA] using fx) (by simpa only [eq0,eqA] using fy)
    (by simpa only [eq0,eqπ] using path) copied
  exact ⟨d,N,W,P,j,(w 11).val,(w 5).val,(w 9).val,(w 2).val,(w 3).val,
    target,nt,cone,leg,iw 11,eq0 ▸ transported.space,transported.source,transported.alphabet,eq0 ▸ p,
    map,fixedA,letters,low⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 固定 demanding 响应表抽取原 II 策略

有限输入只决定当前状态；以固定字母查询下一状态，再读同轮的真实
实数事件。内部递归的因果性与原根嵌入的单射性保证回答唯一。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal Descriptive
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

def Td_response_d (ω X K r a s y : M.Domain) : Prop := ∃ n H u p t,
  M.IsDomainOf I n s ∧ Gi_d hZF true ω X K r a s H ∧ Rd_entry_d n u H ∧
    (I).Codes p u a ∧ Rd_entry_d p t K ∧ Td_real_record_d I t n y

def td_response_m {d} (ω X K r a s y : Term d) : Formula 1 d := set[d] ⟪∃ n H u p t,
  ⌜Formula.isDomain kpair_convention_l⌝ₚ(n,⌜s⌝ₛ) ∧
  ⌜(gi_m true)⌝ₚ(⌜ω⌝ₛ,⌜X⌝ₛ,⌜K⌝ₛ,⌜r⌝ₛ,⌜a⌝ₛ,⌜s⌝ₛ,H) ∧
  ⌜rd_entry0_m⌝ₚ(n,u,H) ∧ ⌜kpair_m⌝ₚ(p,u,⌜a⌝ₛ) ∧
  ⌜rd_entry0_m⌝ₚ(p,t,⌜K⌝ₛ) ∧ ⌜td_real_record_m⌝ₚ(t,n,⌜y⌝ₛ)⟫
derive_free_closed td_response_m

theorem td_response_sat_l {d} (ρ : Env M d) (ω X K r a s y : Term d) :
    Formula.satisfies ρ (td_response_m ω X K r a s y) ↔
      Td_response_d hZF (ω.eval ρ) (X.eval ρ) (K.eval ρ) (r.eval ρ) (a.eval ρ) (s.eval ρ) (y.eval ρ) := by
  simp only [td_response_m,Td_response_d,Formula.satisfies_exists_iff,Formula.satisfies_conj_iff,
    Formula.satisfies_isDomain_iff I,gi_sat_l hZF true,rd_entry0_sat_l hZF.1,kpair_sat_l M hZF.1,
    td_real_record_sat_l I hZF.1,Definitional.Term.eval_weaken]
  rfl

variable {g : Fin 10 → M.Domain} {A r X D K a s : M.Domain}

theorem Td_state_code_d.real_unique_l (state : Td_state_code_d hZF g s)
    (root : Smdl_d I (g 1) (g 3) (g 4)) {i x y : M.Domain}
    (hx : Td_real_record_d I s i x) (hy : Td_real_record_d I s i y) : x = y := by
  obtain ⟨v,cv,rx⟩ := hx
  obtain ⟨w,cw,ry⟩ := hy
  have eq := rt_tuple_inj_l cw cv
  subst w
  exact (state.read_l hZF cv).real_unique_l hZF root rx ry

/-- 下一状态的轮号严格增加，故本轮字母已经实际出现。 -/
theorem Td_choice_d.next_real_l (h : Td_choice_d hZF g A r X D K)
    (root : Zc_model_d I (g 0) (g 1) (g 3) (g 4))
    (letters : ∀ x, M.mem x A ↔ M.mem x (g 3) ∧ Rd_entry_d x (g 8) (g 4))
    {n u x p t : M.Domain} (state : Td_state_code_d hZF g u) (index : Rt_coord_d (12 : Fin 66) u n)
    (pair : (I).Codes p u x) (entry : Rd_entry_d p t K) :
    ∃ y, M.mem y A ∧ Td_real_record_d I t n y := by
  obtain ⟨next,v,w,cv,cw,_,edge⟩ := h.step u x t p state pair entry
  obtain ⟨_,_,_,_,_,_,_,_,_,_,succ,_⟩ := edge
  have eq := index.read_l v cv
  have inside : M.mem n (w 12) := eq ▸ (show M.mem (v 12) (w 12) from succ.predecessor_mem)
  obtain ⟨y,hy,real⟩ := (next.read_l hZF cw).real_total_l hZF root letters inside
  exact ⟨y,hy,w,cw,real⟩

theorem Td_choice_d.strategy_l (h : Td_choice_d hZF g A r X D K)
    (root : Zc_model_d I (g 0) (g 1) (g 3) (g 4))
    (letters : ∀ x, M.mem x A ↔ M.mem x (g 3) ∧ Rd_entry_d x (g 8) (g 4))
    (zero : Rt_coord_d (12 : Fin 66) r (g 2)) (empty : ∀ x, ¬ M.mem x (g 2))
    (ha : M.mem a A) {F : M.Domain} (space : Fseq_space_d I (g 0) A F) :
    ∃ σ, Fn0_d F A σ ∧ ∀ s y, Rd_entry_d s y σ ↔ M.mem s F ∧ Td_response_d hZF (g 0) X K r a s y := by
  have hw := h.initial.elim fun _ h => h.2.tree.omega
  have total s (hs : M.mem s F) : ∃ y, Td_response_d hZF (g 0) X K r a s y := by
    obtain ⟨n,hn,fs⟩ := (space s).mp hs
    obtain ⟨H,run⟩ := h.run_l hZF zero empty ha fs.1 (fun _ _ hi => fs.output_mem_of_pairMember hi)
    obtain ⟨u,hu,nu⟩ := run.recursion.1.2.1 n hn
    obtain ⟨p,pair⟩ := (I).total u a
    obtain ⟨t,_,pt⟩ := h.function.2.1 p ((h.product p).mpr ⟨u,hu,a,ha,pair⟩)
    obtain ⟨y,_,real⟩ := h.next_real_l hZF root letters (run.rows n u nu).1 (run.rows n u nu).2 pair pt
    exact ⟨y,n,H,u,p,t,fs.2.1,run.recursion,nu,pair,pt,real⟩
  have bound s y (answer : Td_response_d hZF (g 0) X K r a s y) : M.mem y A := by
    obtain ⟨n,H,u,p,t,_,run,nu,pair,pt,real⟩ := answer
    have state := (h.validate_l hZF zero empty run).rows n u nu
    obtain ⟨z,hz,rz⟩ := h.next_real_l hZF root letters state.1 state.2 pair pt
    exact ((h.step u a t p state.1 pair pt).1.real_unique_l hZF root.model rz real) ▸ hz
  have unique s (fs : M.IsSetFunction I s) x y
      (hx : Td_response_d hZF (g 0) X K r a s x) (hy : Td_response_d hZF (g 0) X K r a s y) : x = y := by
    obtain ⟨n,H,u,p,t,dom,run,nu,pair,pt,real⟩ := hx
    obtain ⟨n',H',u',p',t',dom',run',nu',pair',pt',real'⟩ := hy
    have eq := dom'.eq hZF.1 dom
    subst n'
    have fk := (fn0_function_l (ZF.modelsKP hZF) h.function).1
    have eq := run.agree_l hZF hw fk fs run' (run.1.bound_l nu).1 (fun _ _ _ => Iff.rfl) u u' nu nu'
    subst u'
    have eq := (I).unique pair' pair
    subst p'
    have eq := fk.2 p t' t pt' pt
    subst t'
    exact (h.step u a t p ((h.validate_l hZF zero empty run).rows n u nu).1 pair pt).1.real_unique_l
      hZF root.model real real'
  let ρ : Env M 5 := ⟨fun i => [g 0,X,K,r,a].get i,fun _ => g 0⟩
  let φ : BinarySchema 5 := { body := (td_response_m (.bound 2) (.bound 3) (.bound 4)
    (.bound 5) (.bound 6) (.bound 1) .newest) }
  have sat s y : φ.denote ρ s y ↔ Td_response_d hZF (g 0) X K r a s y := td_response_sat_l hZF ..
  obtain ⟨σ,fn,values⟩ := ZF.exists_setFunctionFromTo_of_denote hZF I φ ρ
    (fun s hs => (total s hs).imp fun y hy => (sat s y).mpr hy) (by
      intro s hs x y hx hy
      obtain ⟨_,_,fs⟩ := (space s).mp hs
      exact unique s fs.1 x y ((sat s x).mp hx) ((sat s y).mp hy))
    (fun s y _ hy => bound s y ((sat s y).mp hy))
  exact ⟨σ,fn0_of_function_l (ZF.modelsKP hZF) fn,fun s y =>
    (values s y).trans (and_congr_right fun _ => sat s y)⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 服从抽出策略的对局就是同一运行的原实数图

偶数轮使用实际输入；奇数轮把完整输入限制到当前长度，利用同一响应表
的前缀因果性识别策略值。比较均在模型内部进行，不假定 ω 外部标准。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal Descriptive
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)
variable {g : Fin 10 → M.Domain} {A r X D K a F σ f H : M.Domain} {U : Fin 6 → M.Domain}

theorem Td_choice_d.follows_play_l (h : Td_choice_d hZF g A r X D K)
    (root : Zc_model_d I (g 0) (g 1) (g 3) (g 4))
    (letters : ∀ x, M.mem x A ↔ M.mem x (g 3) ∧ Rd_entry_d x (g 8) (g 4))
    (zero : Rt_coord_d (12 : Fin 66) r (g 2)) (empty : ∀ x, ¬ M.mem x (g 2))
    (ha : M.mem a A) (space : Fseq_space_d I (g 0) A F) (sf : Fn0_d F A σ)
    (values : ∀ s y, Rd_entry_d s y σ ↔ M.mem s F ∧ Td_response_d hZF (g 0) X K r a s y)
    (input : Fn0_d (g 0) A f) (follows : Gm_follows_d I false (g 0) σ f)
    (run : Td_run_d hZF g X K r a f H) (u : Td_union_d hZF g H U) : Td_run_play_d I (g 0) A H f := by
  obtain ⟨play,played⟩ := run.play_l hZF u root letters
  have hw := u.tree.omega
  have ff := fn0_function_l (ZF.modelsKP hZF) input
  have same n (hn : M.mem n (g 0)) y (ny : Rd_entry_d n y play) : Rd_entry_d n y f := by
    obtain ⟨m,succ,hm⟩ := hw.1.2 n hn
    obtain ⟨s,_,ns⟩ := run.recursion.1.2.1 n hn
    obtain ⟨t,_,mt⟩ := run.recursion.1.2.1 m hm
    obtain ⟨x,p,inp,pair,pt⟩ := run.recursion.2.2 n m s t succ ns mt
    obtain ⟨next,edge⟩ := h.step s x t p (run.rows n s ns).1 pair pt
    obtain ⟨z,_,real⟩ := h.next_real_l hZF root letters (run.rows n s ns).1 (run.rows n s ns).2 pair pt
    have nz := (played.2 n z).mpr ⟨hn,m,t,mt,real⟩
    have yz := (fn0_function_l (ZF.modelsKP hZF) played.1).1.2 n y z ny nz
    subst z
    obtain ⟨b,_,nb⟩ := input.2.1 n hn
    have yb : y = b := by
      rcases Classical.em (Gm_even_d I (g 0) n) with even | odd
      · have xb : x = b := inp.elim (fun hx => ff.1.2 n x b hx.2 nb)
          (fun hx => (hx.1 ⟨even,b,nb⟩).elim)
        obtain ⟨v,w,cv,cw,step⟩ := edge
        have index := (run.rows n s ns).2.read_l v cv
        have event := step.even_real_l hZF ((run.rows n s ns).1.read_l hZF cv)
          (next.read_l hZF cw) root (index.symm ▸ even)
        have event : Td_real_record_d I t n x := ⟨w,cw,index ▸ event⟩
        exact (next.real_unique_l hZF root.model real event).trans xb
      · have xa : x = a := inp.elim (fun hx => (odd hx.1).elim) And.right
        obtain ⟨q,cut⟩ := ZF.exists_restriction hZF I f n
        have fq := cut.isSetFunctionFromTo ff (hw.transitive (ZF.modelsKP hZF) n hn)
        obtain ⟨G,grun⟩ := h.run_l hZF zero empty ha fq.1 (fun _ _ hi => fq.output_mem_of_pairMember hi)
        obtain ⟨s',_,ns'⟩ := grun.recursion.1.2.1 n hn
        have eq := run.recursion.prefix_l hZF hw (fn0_function_l (ZF.modelsKP hZF) h.function).1
          ff.1 grun.recursion hn cut s s' ns ns'
        have response : Td_response_d hZF (g 0) X K r a q y :=
          ⟨n,G,s,p,t,fq.2.1,grun.recursion,eq.symm ▸ ns',xa ▸ pair,pt,real⟩
        exact (fn0_function_l (ZF.modelsKP hZF) sf).1.2 q y b
          ((values q y).mpr ⟨(space q).mpr ⟨n,hn,fq⟩,response⟩) (follows n hn odd q cut b nb)
    exact yb.symm ▸ nb
  have eq : play = f := (fn0_function_l (ZF.modelsKP hZF) played.1).1.1.eq_of_pairMember_iff hZF.1 ff.1.1 (by
    intro n y
    refine ⟨fun ny => same n (played.1.bound_l ny).1 y ny,fun ny => ?_⟩
    obtain ⟨z,_,nz⟩ := played.1.2.1 n (input.bound_l ny).1
    exact (ff.1.2 n z y (same n (input.bound_l ny).1 z nz) ny) ▸ nz)
  exact eq ▸ played

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 编码版 7.8：原辅助 II 胜策给出广义 demanding 投影策略

在同一次初始化中固定响应表，抽出一张原博弈 II 策略。每个服从对局
沿该表运行；并树的临界点界和全部良基枝的满射三坐标投影同时成立。
第一辅助域的枚举沿用已实现的内部幂集编码，不增设枝命中前提。
本入口采用传递隶属根及非空最小第一辅助域；完整数字图由原根自动构造。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal Descriptive
universe u
variable {M : Structure.{u}} (hZFC : M.Models ZFC)
local notation "hZF" => ZFC.models_zf_l hZFC
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Td_game_d.fixed_strategy_l
    {Ω c X R : M.Domain} (hΩ : M.IsOmega Ω) (certificate : Zc_model_d I Ω c X R)
    (source : Smem_d I c X R) (trans : M.TransitiveSet X)
    {p : Tg_params_d (smdl_structure_l I (R := R) certificate.model.2.1).Domain}
    {A F L G J B W O Z g σ U₁ U₂ a : (smdl_structure_l I (R := R) certificate.model.2.1).Domain}
    (game : Td_game_d (certificate.native_l I hZF hΩ) p A F L G J B W O Z g)
    (woodin : Woodin_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l
      (certificate.native_l I hZF hΩ)))) p.δ)
    (win : Cg_win_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l
      (certificate.native_l I hZF hΩ)))) false p.ω A F J B W σ)
    (treeS : Td_tree_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l
      (certificate.native_l I hZF hΩ)))) p.ω p.A p.S)
    (alphabet : Td_alphabet_d p.S U₁ U₂)
    (chosen : (smdl_structure_l I (R := R) certificate.model.2.1).mem a U₁)
    (separated : Td_separated_d p.S)
    (powerCount : Pc_count_d I Ω X R p.δ.val)
    (coding : ∃ P, (smdl_structure_l I (R := R) certificate.model.2.1).IsPowerSetOf P p.δ ∧
      (smdl_structure_l I (R := R) certificate.model.2.1).CardinalLessOrEqual
        (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l (certificate.native_l I hZF hΩ)))) U₁ P) :
    ∃ o F₀ σ₀, (∀ x, ¬ M.mem x o) ∧ Fseq_space_d I Ω p.A.val F₀ ∧
      Gm_strategy_d I false Ω p.A.val F₀ σ₀ ∧
      ∀ f, Fn0_d Ω p.A.val f → Gm_follows_d I false Ω σ₀ f →
        Td_fixed_gp_d hZF Ω o c X p.A.val p.S.val f := by
  obtain ⟨_,z,numbers⟩ := tg_numbers_mem_l hZF hΩ certificate source trans p.ω game.setup.omega
  -- 同一次原开局固定全部对局共用的响应表。
  obtain ⟨H,ι,_,o,m,T,Q,G₀,q,A₀,D₀,V,t,Λ,a₀,r,Y,D,K,
    empty,ha,cut,tuple,choice,runs⟩ :=
    game.iteration_run_l hZFC hΩ certificate numbers woodin win treeS alphabet chosen separated powerCount coding
  have zero : Rt_coord_d (12 : Fin 66) r o := ⟨_,tuple,rfl⟩
  obtain ⟨F₀,space⟩ := ZF.fseq_space_exists_l I hZF hΩ A₀
  obtain ⟨τ,total,values⟩ := choice.strategy_l hZF certificate cut.letters zero empty ha space
  obtain ⟨Dσ,turns⟩ := gm_turns_l hZF false Ω A₀ F₀
  obtain ⟨σ₀,function,restriction⟩ := turns.restrict_l (ZF.modelsKP hZF) total
  obtain ⟨letters,ordinal,ρ,rank,lower⟩ := cut.canonical_l hZF source trans
  refine ⟨o,F₀,σ₀,empty,letters ▸ space,letters ▸ (show Gm_strategy_d I false Ω A₀ F₀ σ₀ from
    ⟨Dσ,turns,function⟩),?_⟩
  intro f input follows
  have input : Fn0_d Ω A₀ f := letters.symm ▸ input
  have follows := (turns.follows_l (ZF.modelsKP hZF) hΩ space input restriction).mp follows
  obtain ⟨run,valid,U,union,copy,_⟩ := runs f input
  -- 先识别服从对局，再用同一并树的临界点界和全部良基枝结论。
  have played := choice.follows_play_l hZF certificate cut.letters zero empty ha space total values input follows valid union
  exact ⟨ρ,(ι.bound 24).val,rank,lower,ordinal,valid.fixed_shifted_l hZF union copy certificate cut source trans played⟩

theorem Td_game_d.mem_strategy_l
    {Ω c X R : M.Domain} (hΩ : M.IsOmega Ω) (certificate : Zc_model_d I Ω c X R)
    (source : Smem_d I c X R) (trans : M.TransitiveSet X)
    {p : Tg_params_d (smdl_structure_l I (R := R) certificate.model.2.1).Domain}
    {A F L G J B W O Z g σ U₁ U₂ a : (smdl_structure_l I (R := R) certificate.model.2.1).Domain}
    (game : Td_game_d (certificate.native_l I hZF hΩ) p A F L G J B W O Z g)
    (woodin : Woodin_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l
      (certificate.native_l I hZF hΩ)))) p.δ)
    (win : Cg_win_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l
      (certificate.native_l I hZF hΩ)))) false p.ω A F J B W σ)
    (treeS : Td_tree_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l
      (certificate.native_l I hZF hΩ)))) p.ω p.A p.S)
    (alphabet : Td_alphabet_d p.S U₁ U₂)
    (chosen : (smdl_structure_l I (R := R) certificate.model.2.1).mem a U₁)
    (separated : Td_separated_d p.S)
    (powerCount : Pc_count_d I Ω X R p.δ.val)
    (coding : ∃ P, (smdl_structure_l I (R := R) certificate.model.2.1).IsPowerSetOf P p.δ ∧
      (smdl_structure_l I (R := R) certificate.model.2.1).CardinalLessOrEqual
        (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l (certificate.native_l I hZF hΩ)))) U₁ P) :
    ∃ o F₀ σ₀, (∀ x, ¬ M.mem x o) ∧ Fseq_space_d I Ω p.A.val F₀ ∧
      Gm_strategy_d I false Ω p.A.val F₀ σ₀ ∧
      ∀ f, Fn0_d Ω p.A.val f → Gm_follows_d I false Ω σ₀ f →
        Td_gp_d hZF Ω o c p.A.val p.S.val f := by
  obtain ⟨o,F₀,σ₀,empty,space,strategy,plays⟩ := game.fixed_strategy_l hZFC hΩ certificate source trans
    woodin win treeS alphabet chosen separated powerCount coding
  exact ⟨o,F₀,σ₀,empty,space,strategy,fun f input follows => (plays f input follows).projection_l hZF⟩
end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 编码版 7.11：同一辅助闭博弈的两种策略出口

先在原模型中决定原辅助博弈。II 分支使用背景幂集计数及内部编码；
I 分支对每个实际坍缩泛型调用原 7.4，保留扩张内部的对局量词。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal Descriptive
universe u
variable {M : Structure.{u}} (hZFC : M.Models ZFC)
local notation "hZF" => ZFC.models_zf_l hZFC
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Td_game_d.corollary711_l
    {Ω c X R : M.Domain} (hΩ : M.IsOmega Ω) (certificate : Zc_model_d I Ω c X R)
    (source : Smem_d I c X R) (trans : M.TransitiveSet X)
    {p : Tg_params_d (smdl_structure_l I (R := R) certificate.model.2.1).Domain}
    {A F L G J B W O Z g U₁ U₂ a : (smdl_structure_l I (R := R) certificate.model.2.1).Domain}
    (game : Td_game_d (certificate.native_l I hZF hΩ) p A F L G J B W O Z g)
    (woodin : Woodin_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l
      (certificate.native_l I hZF hΩ)))) p.δ)
    (treeS : Td_tree_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l
      (certificate.native_l I hZF hΩ)))) p.ω p.A p.S)
    (alphabet : Td_alphabet_d p.S U₁ U₂)
    (chosen : (smdl_structure_l I (R := R) certificate.model.2.1).mem a U₁)
    (separated : Td_separated_d p.S)
    (powerCount : Pc_count_d I Ω X R p.δ.val)
    (coding : ∃ P, (smdl_structure_l I (R := R) certificate.model.2.1).IsPowerSetOf P p.δ ∧
      (smdl_structure_l I (R := R) certificate.model.2.1).CardinalLessOrEqual
        (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l (certificate.native_l I hZF hΩ)))) U₁ P) :
    (∃ o F₀ σ₀, (∀ x, ¬ M.mem x o) ∧ Fseq_space_d I Ω p.A.val F₀ ∧
      Gm_strategy_d I false Ω p.A.val F₀ σ₀ ∧
      ∀ f, Fn0_d Ω p.A.val f → Gm_follows_d I false Ω σ₀ f →
        Td_gp_d hZF Ω o c p.A.val p.S.val f) ∨
    Td_collapse_win_d (ZFC.models_zf_l (certificate.native_l I hZF hΩ))
      p.ω p.δ p.A U₁ U₂ p.S := by
  have native := certificate.native_l I hZF hΩ
  obtain ⟨b,σ,_,win⟩ := game.determined_l native
  cases b with
  | false => exact Or.inl (game.mem_strategy_l hZFC hΩ certificate source trans woodin win
      treeS alphabet chosen separated powerCount coding)
  | true => exact Or.inr (game.collapse_transfer_l native woodin win treeS alphabet chosen)

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 编码版 7.12：无终端节点合法树上的 demanding 二择一

在原模型内构造历史收缩和补全逆像树，复用原辅助域及其幂集编码。
同一辅助闭博弈的 II 分支给出地面合法树策略，I 分支给出每个实际坍缩
扩张内部的合法树策略；不添加收缩图秩界或策略绝对性假设。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal Descriptive Model.Forcing.Internal
universe u
variable {M : Structure.{u}} (hZFC : M.Models ZFC)
local notation "hZF" => ZFC.models_zf_l hZFC
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Td_game_d.corollary712_l
    {Ω c X R : M.Domain} (hΩ : M.IsOmega Ω) (certificate : Zc_model_d I Ω c X R)
    (source : Smem_d I c X R) (trans : M.TransitiveSet X)
    {p : Tg_params_d (smdl_structure_l I (R := R) certificate.model.2.1).Domain}
    {A F L G J B W O Z g U₁ U₂ a F₀ R₀ : (smdl_structure_l I (R := R) certificate.model.2.1).Domain}
    (game : Td_game_d (certificate.native_l I hZF hΩ) p A F L G J B W O Z g)
    (woodin : Woodin_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l
      (certificate.native_l I hZF hΩ)))) p.δ)
    (treeS : Td_tree_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l
      (certificate.native_l I hZF hΩ)))) p.ω p.A p.S)
    (alphabet : Td_alphabet_d p.S U₁ U₂)
    (chosen : (smdl_structure_l I (R := R) certificate.model.2.1).mem a U₁)
    (separated : Td_separated_d p.S)
    (powerCount : Pc_count_d I Ω X R p.δ.val)
    (coding : ∃ P, (smdl_structure_l I (R := R) certificate.model.2.1).IsPowerSetOf P p.δ ∧
      (smdl_structure_l I (R := R) certificate.model.2.1).CardinalLessOrEqual
        (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l (certificate.native_l I hZF hΩ)))) U₁ P)
    (inputs : Fseq_space_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l
      (certificate.native_l I hZF hΩ)))) p.ω p.A F₀)
    (legal : Tree_d F₀ R₀)
    (root : (smdl_structure_l I (R := R) certificate.model.2.1).mem p.e R₀)
    (next : ∀ s, (smdl_structure_l I (R := R) certificate.model.2.1).mem s R₀ →
      ∃ t, (smdl_structure_l I (R := R) certificate.model.2.1).mem t R₀ ∧
        Step_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l (certificate.native_l I hZF hΩ)))) p.ω s t) :
    (∃ o σ₀, (∀ x, ¬ M.mem x o) ∧ Gt_strategy_d hZF false Ω p.A.val R₀.val σ₀ ∧
      ∀ f, Fn0_d Ω p.A.val f → Branch_d F₀.val R₀.val f → Gm_follows_d I false Ω σ₀ f →
        Td_fixed_gp_d hZF Ω o c X p.A.val p.S.val f) ∨
    Td_tree_collapse_d (ZFC.models_zf_l (certificate.native_l I hZF hΩ)) p.ω p.δ p.A F₀ R₀ U₁ U₂ p.S := by
  let native := certificate.native_l I hZF hΩ
  let hN := ZFC.models_zf_l native
  have hw := game.setup.omega
  have empty := game.setup.empty
  -- 原模型先完成收缩及首层补全，两个辅助域和原编码保持不变。
  obtain ⟨π,retract⟩ := tree_retraction_l native hw inputs legal empty root next
  obtain ⟨P,Y,F₁,F₂,F',T,W',frame,treeW,sepW⟩ := td_retraction_frame_l hN hw inputs retract
    treeS alphabet chosen separated empty game.setup.one
  let v : Fin 15 → (smdl_structure_l I (R := R) certificate.model.2.1).Domain :=
    fun i => [p.ω,p.A,U₁,U₂,P,Y,F₀,F₁,F₂,F',π,p.S,T,p.a,W'].get i
  have frame : Td_frame_d hN v := frame
  obtain ⟨t,ht,a₀,endt⟩ := next p.e root
  obtain ⟨_,_,ft⟩ := (inputs t).mp (legal.1 t ht)
  obtain ⟨_,_,last⟩ := endt
  have ha := ft.output_mem_of_pairMember last.last_value
  obtain ⟨q,Fq,Lq,Gq,Jq,Bq,Wq,Oq,Zq,gq,eqω,eqδ,eqA,eqS,aux⟩ :=
    td_game_l native (S := W') hw game.setup.limit game.setup.above game.setup.rank game.setup.letters
  obtain ⟨b,σ,_,win⟩ := aux.determined_l native
  cases b with
  | true =>
    -- 每个实际扩张内部重新模拟合法树策略，量化该扩张的所有服从对局。
    have won := aux.collapse_transfer_l native (U₁ := U₁) (U₂ := U₂) (by simpa only [eqδ] using woodin) win
      (by simpa only [eqω,eqA,eqS] using treeW)
      (by simpa only [eqS] using! frame.filled_alphabet) chosen
    have won : Td_collapse_win_d hN p.ω p.δ p.A U₁ U₂ W' := by
      simpa only [eqω,eqδ,eqA,eqS] using won
    exact Or.inr (won.tree_l hN hw inputs legal retract empty root ha frame.space frame.source
      alphabet frame.pair frame.triple frame.pull frame.fill)
  | false =>
    -- 原 7.8 保留同一根腿的固定性，随后逐条良基枝运输原树投影。
    have result := aux.fixed_strategy_l hZFC hΩ certificate source trans (U₁ := U₁) (U₂ := U₂)
      (by simpa only [eqδ] using woodin) win (by simpa only [eqω,eqA,eqS] using treeW)
      (by simpa only [eqS] using! frame.filled_alphabet) chosen (by simpa only [eqS] using sepW)
      (by simpa only [eqδ] using powerCount) (by simpa only [eqδ] using coding)
    simp only [eqA,eqS] at result
    obtain ⟨o,Fg,σg,zero,finite,strategy,plays⟩ := result
    obtain ⟨eqωval,_,_⟩ := tg_numbers_mem_l hZF hΩ certificate source trans p.ω hw
    have eqv : (v 0).val = Ω := eqωval
    have hwval : M.IsOmega p.ω.val := eqωval.symm ▸ hΩ
    have full := smem_full_l I source trans
    have inj : Function.Injective (Subtype.val : (smdl_structure_l I (R := R) certificate.model.2.1).Domain → M.Domain) :=
      fun _ _ h => Subtype.ext h
    have ambient := frame.mem_l hZF source trans hN hwval rfl
    have legal' := image_tree_l Subtype.val inj full legal
    have retract' := image_retract_l hN hZF Subtype.val inj full hw hwval inputs legal retract
    have empty' x (hx : M.mem x p.e.val) : False :=
      (full p.e x).mp hx |>.elim fun y hy => empty y hy.1
    have root' := (image_member_l Subtype.val inj full).mpr root
    have ha' := (image_member_l Subtype.val inj full).mpr ha
    have one' := image_successor_l (hEN := hZF.1) Subtype.val inj full hN.1 game.setup.one
    have same : Fg = F₀.val := hZF.1.eq_of_same_members Fg F₀.val
      (fun s => (finite s).trans ((eqωval ▸ ambient.inputs) s).symm)
    subst Fg
    obtain ⟨τ,legalτ,simulate⟩ := retract'.strategy_l hZF hwval ambient.inputs legal' empty' root' ha'
      (by simpa only [eqωval] using! strategy)
    refine Or.inl ⟨o,τ,zero,by simpa only [eqωval] using! legalτ,?_⟩
    intro f ff branch follows
    obtain ⟨x,fx,followx,path⟩ := simulate f (by simpa only [eqωval] using! ff) branch
      (by simpa only [eqωval] using! follows)
    have shifted := plays x (by simpa only [eqωval] using! fx) (by simpa only [eqωval] using! followx)
    have projected := Td_fixed_gp_d.retract_l hZF source trans hN frame hwval retract' R₀.property legal'.1
      empty' one' fx (by simpa only [eqv] using! ff) path (by simpa only [eqv] using! shifted)
    simpa only [eqv] using! projected

end YesMetaZFC.SetTheory.LargeCardinal
