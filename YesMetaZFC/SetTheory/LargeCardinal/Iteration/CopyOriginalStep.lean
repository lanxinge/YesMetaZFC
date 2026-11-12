import YesMetaZFC.SetTheory.LargeCardinal.Iteration.CopyAnchor
import YesMetaZFC.Model.SetTheory.Game.NodeEmbedding
import YesMetaZFC.SetTheory.LargeCardinal.Iteration.CopyOriginalResult
import YesMetaZFC.SetTheory.LargeCardinal.Iteration.CopyExtend
import YesMetaZFC.SetTheory.LargeCardinal.Iteration.CopyRawStep
import YesMetaZFC.SetTheory.LargeCardinal.Extender.RawAlphabet
import YesMetaZFC.SetTheory.LargeCardinal.Game.NativeRecord
import YesMetaZFC.SetTheory.LargeCardinal.Game.RawContinueCandidate
import YesMetaZFC.SetTheory.LargeCardinal.Types.ContinueScope
import YesMetaZFC.SetTheory.LargeCardinal.Game.NativePlay
import YesMetaZFC.SetTheory.LargeCardinal.Game.RawContinueRenewal
import YesMetaZFC.SetTheory.LargeCardinal.Game.Recovery
import YesMetaZFC.SetTheory.LargeCardinal.Game.Restart
import YesMetaZFC.SetTheory.LargeCardinal.Game.SavedNative
import YesMetaZFC.SetTheory.LargeCardinal.Extender.RawRankSource
import YesMetaZFC.SetTheory.LargeCardinal.Game.RoundNativeScope
import YesMetaZFC.SetTheory.LargeCardinal.Game.ReplyPool
import YesMetaZFC.SetTheory.LargeCardinal.Game.RawReply
import YesMetaZFC.SetTheory.LargeCardinal.Game.AnswerNativeInput
import YesMetaZFC.SetTheory.LargeCardinal.Game.Subtype
import YesMetaZFC.SetTheory.LargeCardinal.Game.ResetNative

/-! # 共同原秩段搬运完整函数图及精确定义域

配对由有界公式保持；完整前驱方程回收目标图的每个坐标。
函数性和定义域据此逐点转移；两侧只需外延性与配对，不额外假设值域对象属于共同层。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (I : kpair_convention_l.Interpretation M)

theorem rr_native_graph_l (hE : Extensional M) {X R Y S D g : M.Domain}
    (nx : ∃ x, M.mem x X) (ny : ∃ y, M.mem y Y)
    (hX : Extensional (smdl_structure_l I (R := R) nx))
    (pX : ∀ a b : (smdl_structure_l I (R := R) nx).Domain, ∃ p, Pair_d _ p a b)
    (hY : Extensional (smdl_structure_l I (R := S) ny))
    (pY : ∀ a b : (smdl_structure_l I (R := S) ny).Domain, ∃ p, Pair_d _ p a b)
    (Un : (smdl_structure_l I (R := R) nx).Domain)
    (Vn : (smdl_structure_l I (R := S) ny).Domain)
    (tx : (smdl_structure_l I (R := R) nx).TransitiveSet Un)
    (ty : (smdl_structure_l I (R := S) ny).TransitiveSet Vn)
    (domain : ∀ x, M.mem x D ↔ M.mem x X ∧ Rd_entry_d x Un.val R)
    (injection : M.IsSetInjectionFromTo I g D Y)
    (range : ∀ y, Rd_entry_d y Vn.val S ↔ ∃ x, M.mem x D ∧ Rd_entry_d x y g)
    (predecessors : ∀ x y, Rd_entry_d x y g → ∀ p,
      Rd_entry_d p y S ↔ ∃ z, Rd_entry_d z x R ∧ Rd_entry_d z p g)
    (k f : (smdl_structure_l I (R := R) nx).Domain)
    (k' f' : (smdl_structure_l I (R := S) ny).Domain)
    (ik : M.PairMember I k.val k'.val g) (ifn : M.PairMember I f.val f'.val g)
    (graph : Tg_graph_d (kpair_interpretation_l _ hX pX) k f) :
    Tg_graph_d (kpair_interpretation_l _ hY pY) k' f' := by
  let N := smdl_structure_l I (R := R) nx
  let P := smdl_structure_l I (R := S) ny
  have read x y f : Rd_entry_d x y f ↔ M.PairMember I x y f := by
    let ρ : Env M 3 := ⟨fun i => [x,y,f].get i,fun _ => x⟩
    exact (rd_entry_sat_l hE ρ (.bound 0) (.bound 1) (.bound 2)).symm.trans
      (Formula.satisfies_orderedPairMem_iff I ρ (.bound 0) (.bound 1) (.bound 2))
  have carrier x : M.mem x D ↔ M.mem x X ∧ M.PairMember I x Un.val R :=
    (domain x).trans (and_congr_right fun _ => read x Un.val R)
  have image y : M.PairMember I y Vn.val S ↔ ∃ x, M.mem x D ∧ M.PairMember I x y g :=
    (read y Vn.val S).symm.trans ((range y).trans (exists_congr fun x => and_congr_right fun _ => read x y g))
  have pred x y (xy : M.PairMember I x y g) p :
      M.PairMember I p y S ↔ ∃ z, M.PairMember I z x R ∧ M.PairMember I z p g :=
    (read p y S).symm.trans ((predecessors x y ((read x y g).mpr xy) p).trans
      (exists_congr fun z => and_congr (read z x R) (read z p g)))
  have hf : N.mem f Un := ((carrier f.val).mp (injection.1.input_mem_of_pairMember ifn)).2
  have hf' : P.mem f' Vn := (image f'.val).mpr ⟨f.val,injection.1.input_mem_of_pairMember ifn,ifn⟩
  have pick (x : N.Domain) (hx : N.mem x Un) : ∃ y : P.Domain, M.PairMember I x.val y.val g := by
    obtain ⟨y,hy,xy⟩ := injection.1.2.2 x.val ((carrier x.val).mpr ⟨x.property,hx⟩)
    exact ⟨⟨y,hy⟩,xy⟩
  have pull (y : P.Domain) (hy : P.mem y Vn) : ∃ x : N.Domain, M.PairMember I x.val y.val g := by
    obtain ⟨x,hx,xy⟩ := (image y.val).mp hy
    exact ⟨⟨x,((carrier x).mp hx).1⟩,xy⟩
  have move {n} (φ : Formula 1 n) (hc : φ.FreeClosed) (hd : φ.IsDelta0)
      (ρ : Env N n) (η : Env P n) (points : ∀ i, M.PairMember I (ρ.bound i).val (η.bound i).val g) :=
    rr_graph_delta_l I nx ny ⟨k.val,injection.1.input_mem_of_pairMember ik⟩
      (fun x hx => ((carrier x).mp hx).1)
      (fun x y hx hy hyx => (carrier y).mpr ⟨hy,
        tx ⟨x,((carrier x).mp hx).1⟩ ((carrier x).mp hx).2 ⟨y,hy⟩ hyx⟩)
      injection pred φ hc hd ρ η points
  have entry (i x : N.Domain) (i' x' : P.Domain)
      (ii : M.PairMember I i.val i'.val g) (xx : M.PairMember I x.val x'.val g) :
      Rd_entry_d i x f ↔ Rd_entry_d i' x' f' :=
    (rd_entry0_sat_l hX (⟨fun j => [i,x,f].get j,fun _ => f⟩ : Env N 3) ..).symm.trans
      ((move (rd_entry0_m (.bound 0) (.bound 1) (.bound 2)) (by simp -implicitDefEqProofs)
        (rd_entry0_delta_l ..) ⟨fun j => [i,x,f].get j,fun _ => f⟩ ⟨fun j => [i',x',f'].get j,fun _ => f'⟩
        (Fin.cases ii (Fin.cases xx (Fin.cases ifn (fun j => Fin.elim0 j))))).trans (rd_entry0_sat_l hY ..))
  have preimage (i' x' : P.Domain) (val : Rd_entry_d i' x' f') :
      ∃ i x : N.Domain, M.PairMember I i.val i'.val g ∧ M.PairMember I x.val x'.val g ∧ Rd_entry_d i x f := by
    have bounds := rd_entry_transitive_l ty hf' val
    obtain ⟨i,ii⟩ := pull i' bounds.1
    obtain ⟨x,xx⟩ := pull x' bounds.2
    exact ⟨i,x,ii,xx,(entry i x i' x' ii xx).mpr val⟩
  refine ⟨⟨?_,?_⟩,?_⟩
  · intro p' hp'
    obtain ⟨p,hp,ip⟩ := (pred f.val f'.val ifn p'.val).mp hp'
    let pn : N.Domain := ⟨p,((carrier p).mp (injection.1.input_mem_of_pairMember ip)).1⟩
    obtain ⟨i,x,pair⟩ := graph.1.1 pn hp
    have bounds := pair.mem_l N tx (tx f hf pn hp)
    obtain ⟨i',ii⟩ := pick i bounds.1
    obtain ⟨x',xx⟩ := pick x bounds.2
    exact ⟨i',x',(kpair0_sat_l hY ..).mp
      ((move (kpair0_m (.bound 0) (.bound 1) (.bound 2)) (by simp -implicitDefEqProofs) (kpair0_delta_l ..)
        (⟨fun j => [pn,i,x].get j,fun _ => f⟩ : Env N 3) ⟨fun j => [p',i',x'].get j,fun _ => f'⟩
        (Fin.cases ip (Fin.cases ii (Fin.cases xx (fun j => Fin.elim0 j))))).mp ((kpair0_sat_l hX ..).mpr pair))⟩
  · intro i' x' y' hi hy
    obtain ⟨i,x,ii,xx,ix⟩ := preimage i' x' hi
    obtain ⟨j,y,ji,yy,jy⟩ := preimage i' y' hy
    have ij : i = j := Subtype.ext (injection.2 _ _ _ ii ji)
    have xy := graph.1.2 j x y (ij ▸ ix) jy
    exact Subtype.ext (injection.1.1.2 _ _ _ (congrArg Subtype.val xy ▸ xx) yy)
  · intro i'
    constructor
    · intro hi
      obtain ⟨i,hi,ii⟩ := (pred k.val k'.val ik i'.val).mp hi
      let i₀ : N.Domain := ⟨i,((carrier i).mp (injection.1.input_mem_of_pairMember ii)).1⟩
      obtain ⟨x,ix⟩ := (graph.2 i₀).mp hi
      obtain ⟨x',xx⟩ := pick x (rd_entry_transitive_l tx hf ix).2
      exact ⟨x',(entry i₀ x i' x' ii xx).mp ix⟩
    · rintro ⟨x',ix'⟩
      obtain ⟨i,x,ii,xx,ix⟩ := preimage i' x' ix'
      exact (pred k.val k'.val ik i'.val).mpr ⟨i.val,(graph.2 i).mpr ⟨x,ix⟩,ii⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 原生继续及回答的两步同步复制

从工厂的同一完整输出取原极限、共同层及全代表池。原树先追加该边，
旧复制历史改读扩大的原图，再用这个确定的后继完成复制，最后两侧
历史具有同一长度。施加源的实际请求或回答记录沿同一原边搬运，给出
新历史界严格低于同一记录的 δ；固定到所选极限的完整原证书仍保留。
真实 issued 的完整候选沿此次相邻共同图传入目标反射层；查询行通过实际低层
锚点沿共同根传输，再由完整低层解释的唯一性核对同一个代表池图。
旧回答的高度查询与真实超过关系给出最大序数查询。目标实现、图恢复和程序
重启依次使用同一反射核，最终返回完整下一轮回答及其原坐标对应。
新存档使用该回答自身的支撑。严格极限切片及共同图的逆图把同一扩展器
施加到原偶数模型，再完成第二次工作侧复制，原树与复制历史再次等长。
完整规则 (7) 的全部参数及存在见证经同一个代表池进入这个原偶数后继。
原请求和回答随后回到同一反射层，实际秩历史给出合法查询键及原表项。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZFC : M.Models ZFC)
local notation "hZF" => ZFC.models_zf_l hZFC
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

/-- 原图、支撑列和工作图在一次实际活动步中共同延长。 -/
theorem Er_rank_cut_at_d.copy_history_l
    {ω c₀ Xᵣ Rᵣ c X Rₓ b N Rₕ q Γ ks zs n m T Q G E Λ H ST QT GT k o₀ χ
      A π z Z α B σ u U β Vₚ D₀ η wₚ ηₚ Cₚ κp δₚ rₚ
      Ls Js Os Zs Ds ps Vs Ws qs d P Rₚ j₀ q' p qN Cᵣ S₀ wᵣ zᵣ ηN CN γ₀ Bγ aγ Vγ sγ tγ Dₛ tₛ
      wₛ ηₛ Cₛ : M.Domain}
    (mx : Smdl_d I c X Rₓ) (mh : Smdl_d I b N Rₕ)
    (hN : (smdl_structure_l I (R := Rₕ) mh.2.1).Models KP)
    (U₀ w ξ ℓ e β₀ X₀ K₀ jN δ R₀ : (smdl_structure_l I (R := Rₕ) mh.2.1).Domain)
    (data : Er_rank_cut_at_d hZF ω c₀ Xᵣ Rᵣ c X Rₓ q Γ ks N Rₕ zs b mh.2.1 hN U₀ w ξ ℓ e β₀ X₀ K₀ jN
      Ls Js Os Zs Ds ps Vs Ws qs d P Rₚ j₀ q' p)
    (Aₛ Qₛ Bₛ eₛ : (smdl_structure_l I (R := Rₕ) mh.2.1).Domain)
    (poolₛ : Eb_collapse_d w ξ ℓ K₀ X₀ β₀ e Aₛ Qₛ Bₛ eₛ)
    (domainₛ : ∀ x, M.mem x Dₛ ↔ M.mem x N ∧ Rd_entry_d x Aₛ.val Rₕ)
    (relationₛ : M.IsSetRelation I tₛ)
    (presentₛ : Er_present_d I ω Ls N Rₕ zs Γ X ks qs eₛ.val Dₛ tₛ)
    (numbers : Rr_layer_d I ω N Rₕ w.val zs) (source : Ep_source_d (kp_pair_l hN) w ξ K₀ X₀ R₀)
    (rank : V_d (kp_pair_l hN) δ X₀) (height : (smdl_structure_l I (R := Rₕ) mh.2.1).IsLimitOrdinal δ)
    (loc : It_local_d (kp_pair_l hN) w X₀ R₀ ξ ℓ e)
    (strong : Ex_strength_d (kp_pair_l hN) w ξ ℓ X₀ e)
    (card : Sc_inaccessible_d (M := smdl_structure_l I (R := Rₕ) mh.2.1) w X₀ ℓ)
    (root : Zc_model_d I ω c₀ Xᵣ Rᵣ)
    (tree : It_tree_d hZF ω c₀ m T Q G E) (hist : Ic_history_d hZF ω T Q G E Λ m H ST QT GT)
    (hn : M.mem n ω) (hm : M.SuccessorOf m n) (hc : Rd_entry_d k c Q) (hb : Rd_entry_d n b Q)
    (origin : It_map_d G o₀ k q) (ai : Ic_at_d H k X A π z Z α) (an : Ic_at_d H n N B σ u U β)
    (lf : M.IsSetFunction I Λ)
    (levels : ∀ i ρ, Rd_entry_d i ρ Λ ↔ ∃ p κ F, Rd_entry_d i p E ∧ It_payload_d p κ ρ F)
    (bound : Ic_bound_d I H Q N Rₕ σ n χ) (above : Rd_entry_d χ ℓ.val Rₕ)
    (hU : Rd_entry_d U₀.val D₀ σ) (hD : M.mem D₀ A)
    (rA : Vr_d A η D₀) (rB : Vr_d B η D₀) (hη : M.IsLimitOrdinal η)
    (square : ∀ x x' y, Rd_entry_d x x' σ → Rd_entry_d x y ks → Rd_entry_d y x' π)
    (parent_image : ∀ y, Rd_entry_d y Vₚ Rₓ ↔ ∃ x, M.mem x Γ ∧ Rd_entry_d x y ks)
    (parent_small : Rr_small_d I X Rₓ Vₚ)
    (record : Tg_record_d I wₚ X Rₓ ηₚ Cₚ κp δₚ rₚ)
    (candidate : Rd_entry_d ξ.val κp ks) (omegaPoint : Rd_entry_d w.val wₚ ks)
    (fromRoot : Smap_d I ω c₀ b Xᵣ N qN) (current_origin : It_map_d G o₀ n qN)
    (rootNumbers : Rr_layer_d I ω Xᵣ Rᵣ wᵣ zᵣ)
    (rootOld : Rd_entry_d Cᵣ Cₚ q) (rootCurrent : Rd_entry_d Cᵣ CN qN)
    (context : Tg_context_d I w.val N Rₕ ηN CN)
    (nc : Nonempty {x : (smdl_structure_l I (R := Rₕ) mh.2.1).Domain //
      (smdl_structure_l I (R := Rₕ) mh.2.1).mem x ⟨CN, context.member⟩})
    (ρ : Env (rt_model_l (M := smdl_structure_l I (R := Rₕ) mh.2.1) ⟨CN, context.member⟩ nc) 29)
    (ι : Env (rt_model_l (M := smdl_structure_l I (R := Rₕ) mh.2.1) ⟨CN, context.member⟩ nc) 46)
    (seed : Formula.satisfies ρ tc_seed0_m) (issued : Formula.satisfies ι tg_issued0_m)
    (treeName : Rd_entry_d S₀ (ι.bound 7).val.val qN)
    (hw : (ρ.bound 0).val = w) (seed_height : (ρ.bound 1).val = ξ)
    (links : ∀ i : Fin 4, ρ.bound ([0,8,9,13].get i) = ι.bound ([0,24,28,25].get i))
    (arity : ρ.bound 3 = ι.bound 27)
    (high : (smdl_structure_l I (R := Rₕ) mh.2.1).mem (ρ.bound 8).val ℓ)
    (baseHeight : Rr_layer_d I γ₀ N Rₕ aγ sγ) (baseLayer : Rr_layer_d I Bγ N Rₕ Vγ tγ)
    (baseRank : Rr_rank_d I N Rₕ aγ Vγ)
    (baseLimit : (smdl_structure_l I (R := Rₕ) mh.2.1).IsLimitOrdinal ⟨aγ, baseHeight.member⟩)
    (baseLower : ∀ x, Rd_entry_d x aγ Rₕ → Rd_entry_d x ξ.val Rₕ)
    (baseOmega : Rd_entry_d w.val Vγ Rₕ) (baseLetters : Rd_entry_d (ι.bound 6).val.val Vγ Rₕ)
    (baseCurrent : Tg_anchor_d I γ₀ Bγ N Rₕ qN) (baseOld : Tg_anchor_d I γ₀ Bγ X Rₓ q)
    (ε₀ : Env (rt_model_l (M := smdl_structure_l I (R := Rₕ) mh.2.1) ⟨CN, context.member⟩ nc) 7)
    (reply : Formula.satisfies ε₀ tg_reply_base0_m)
    (ωε : ε₀.bound 0 = ρ.bound 0) (nε : ε₀.bound 3 = ρ.bound 3)
    (hi : (smdl_structure_l I (R := Rₕ) mh.2.1).mem (ε₀.bound 2).val (ρ.bound 3).val)
    (hh : (smdl_structure_l I (R := Rₕ) mh.2.1).mem (ε₀.bound 6).val (ρ.bound 7).val)
    (empty : ∀ x : (smdl_structure_l I (R := Rₕ) mh.2.1).Domain,
      ¬ (smdl_structure_l I (R := Rₕ) mh.2.1).mem x (ε₀.bound 1).val)
    (restored : Tg_context_d I wₛ P Rₚ ηₛ Cₛ)
    (iwₛ : Rd_entry_d wₚ wₛ j₀) (iηₛ : Rd_entry_d ηₚ ηₛ j₀) (iCₛ : Rd_entry_d Cₚ Cₛ j₀)
    (ncₛ : Nonempty {x : (smdl_structure_l I (R := Rₚ) ⟨wₛ, restored.omega_mem⟩).Domain //
      (smdl_structure_l I (R := Rₚ) ⟨wₛ, restored.omega_mem⟩).mem x ⟨Cₛ, restored.member⟩})
    (ρₛ : Env (rt_model_l (M := smdl_structure_l I (R := Rₚ) ⟨wₛ, restored.omega_mem⟩) ⟨Cₛ, restored.member⟩ ncₛ) 54)
    (θₛ : Env (rt_model_l (M := smdl_structure_l I (R := Rₚ) ⟨wₛ, restored.omega_mem⟩) ⟨Cₛ, restored.member⟩ ncₛ) 17)
    (oldRound : Formula.satisfies ρₛ tg_round0_m) (subtype : Formula.satisfies θₛ tg_subtype0_m)
    (program : Formula.satisfies (θₛ.reindex (fun i : Fin 11 => [0,1,7,8,10,11,12,13,14,15,16].get i)) ts_numeric0_m)
    (prior : ∀ i : Fin 5, θₛ.bound ([0,1,2,5,9].get i) = ρₛ.bound ([16,24,15,13,11].get i))
    (program_points : ∀ i : Fin 9, Rd_entry_d (ι.bound ([36,37,38,39,40,41,42,43,44].get i)).val.val
      (θₛ.bound ([7,8,10,11,12,13,14,15,16].get i)).val.val tₛ)
    (old_height : Rd_entry_d κp (ρₛ.bound 15).val.val j₀)
    (oldTree : Rd_entry_d S₀ (ρₛ.bound 19).val.val q')
    (s_old t_old k_old : (rt_model_l (M := smdl_structure_l I (R := Rₕ) mh.2.1)
      ⟨CN,context.member⟩ nc).Domain)
    (old_play : Tg_play_d I N Rₕ CN (ι.bound 4).val.val (ι.bound 3).val.val (ι.bound 20).val.val s_old.val.val)
    (old_graph : Tg_graph_d (kp_pair_l hN) k_old.val s_old.val)
    (old_size : (smdl_structure_l I (R := Rₕ) mh.2.1).MemberSubset k_old.val (ι.bound 26).val)
    (old_labels : (smdl_structure_l I (R := Rₕ) mh.2.1).MemberSubset t_old.val (ι.bound 23).val)
    (old_images : ∀ i : Fin 2, ∃ x,
      Rd_entry_d (([s_old,t_old].get i).val.val) x ks ∧
        Rd_entry_d x (ρₛ.bound ([40,41].get i)).val.val j₀)
    (pointsₛ : ∀ i : Fin 5, Rd_entry_d (ρ.bound ([0,8,9,13,3].get i)).val.val
      (θₛ.bound ([0,3,4,6,1].get i)).val.val tₛ) :
    Ic_two_step_d hZF ω c₀ Xᵣ Rᵣ c X Rₓ b N Rₕ q Γ ks zs n m T Q G E Λ H QT GT k o₀ B σ
      wₚ ηₚ Cₚ κp δₚ rₚ Ls Js Os Zs Ds ps Vs Ws qs d P Rₚ j₀ q' p qN Cᵣ S₀ ηN CN γ₀ Bγ Dₛ tₛ
      wₛ ηₛ Cₛ mh hN U₀ w ξ ℓ e β₀ X₀ K₀ jN eₛ tree.omega context nc ρ ι restored ncₛ ρₛ θₛ := by
  have saved := data
  have rawData := saved
  obtain ⟨finite, oc, carrier, hβU, hβX, transβ, products,
    length, raw, diagram, limit, mp, _, _, _, embed, rootMap, constants, agreement, payload, _, certificate, rootGraph,
    U₁, rankU, _, _, source_small, l, V₂, Γ₁, k₁, common, _, _, tail⟩ := rawData
  -- 保留固定证书 saved；下列读取只提取本次共同层末端的完整池及树延伸。
  obtain ⟨Pκ, rankP, lowSquare, κ₀, bκ, κ', hκ₀, hbκ, hκ', belowL, boundκ, neκ, memκ, ordκ, ord₀, ord₁,
    fixκ, lower_images, anchors, rest⟩ := tail
  have eq := agreement.injection.1.1.2 ξ.val bκ κp hbκ candidate
  subst bκ
  obtain ⟨cD, RD, cut, _, _, _, _, _, _, zD, _, _, _, rest⟩ := rest
  obtain ⟨w₀, w₂, z₀, z₁, hww₀, hww₂, omegaEdge, _, newNumbers, _, _, _, _, _, _, _, _, _, _, _, pool, build⟩ := rest
  obtain ⟨A₀, Q₀, B₀, e₀, Dp, Bp, s₁, v₁, t₀, pool, dc, bc, _, _, _, _, ft, restrict, endpoint, layer, present, prepare, _⟩ := pool
  -- 有界塌缩唯一性把本次读取与 subtype 已选的池识别，代表池图不是重新任选。
  have ground := ZFC.models_zf_l ((root.map_l hZF tree.omega mh fromRoot).native_l I hZF tree.omega)
  obtain ⟨eqA, _, _, eqE⟩ := pool.unique_l ground poolₛ
  have eqD : Dp = Dₛ := hZF.1.eq_of_same_members Dp Dₛ (fun x => by rw [dc x, domainₛ x, eqA])
  have fixed : Er_present_d I ω Ls N Rₕ zs Γ X ks qs e₀.val Dp tₛ := by
    rw [eqE, eqD]
    exact presentₛ
  have eqT := ft.1.1.1.eq_of_pairMember_iff hZF.1 relationₛ (fun x E => (present x E).trans (fixed x E).symm)
  subst t₀
  obtain ⟨_, _, _, extend⟩ := build.2 root
  obtain ⟨θ, T₁, Q₁, G₁, E₁, next, extension, node, edge, move, rootEdge, critical⟩ :=
    extend m n T Q G E k o₀ tree hm hb hc origin
  have ir := KP.mem_irrefl_d (ZF.modelsKP hZF)
  obtain ⟨b₀, hb₀, _, own⟩ := hist.row_l hZF an
  have eq := tree.diagram.model_function.2 n b₀ b hb₀ hb
  subst b₀
  obtain ⟨R, RB, _, bB, KB, _, mn, mb, _, sb, _, _, _, _, map⟩ := own
  have eq := (smdl_unique_l I mn mh).2
  subst R
  obtain ⟨Λ₁,Y,v,C,γ,τ,H₁,ST₁,QT₁,GT₁,Lw,lf₁,levels₁,entries,result,rows,codes,maps,last,bnd,adjacent⟩ :=
    hist.copy_original_cert_l hZFC mx mh hN U₀ w ξ ℓ e β₀ X₀ K₀ jN δ R₀ saved
      numbers source rank height loc
      (it_owner_l I mh hN w ξ ℓ e δ X₀ K₀ R₀ numbers rank height source loc card strong)
      hU hD rA rB hη square parent_image parent_small common tree hn hm next extension
      hc hb node edge move payload lf levels ai an bound above
  -- 完整记录给出 κt<δ₁；原生历史界的 χ₁⊆κt 随后给出严格界。
  have native := ZF.modelsKP (ZFC.models_zf_l ((certificate root).native_l I hZF tree.omega))
  obtain ⟨w₁, η₁, C₁, δ₁, r₁, iw, iη, iC, iδ, ir₁, record₁, hκδ, hχδ, hχC, regular⟩ :=
    record.map_l hZF tree.omega mx mp native embed hκ' bnd.ordinal boundκ
  have ewₛ := embed.1.1.1.2 wₚ wₛ w₁ iwₛ iw
  have eηₛ := embed.1.1.1.2 ηₚ ηₛ η₁ iηₛ iη
  have eCₛ := embed.1.1.1.2 Cₚ Cₛ C₁ iCₛ iC
  subst wₛ ηₛ Cₛ
  -- 当前候选的类型来自真实超过关系；其整个查询域严格低于本次支撑。
  let N₀ := smdl_structure_l I (R := Rₕ) mh.2.1
  let P₀ := smdl_structure_l I (R := Rₚ) mp.2.1
  have targetZF := ZFC.models_zf_l ((certificate root).native_l I hZF tree.omega)
  have fs := context.finite_l mh.2.1 ground.1
  have rankC : V_d (kp_pair_l hN) (⟨ηN, context.height⟩ : N₀.Domain) ⟨CN, context.member⟩ :=
    (rr_rank_native_l I mh.2.1 hN _ _).mp ((rr_rank_truth_l I).mpr context.rank)
  have lim : N₀.IsLimitOrdinal ℓ := (Formula.satisfies_isLimitOrdinal_iff ..).mp
    ((rr_truth_native_l I mh.2.1 (Formula.isLimitOrdinal .newest) (by simp -implicitDefEqProofs)
      (fun _ : Fin 1 => ℓ)).mp common.limit)
  have tau : N₀.mem (ρ.bound 8).val U₁ := KP.v_ordinal_subset_l hN rankU _ high
  obtain ⟨finiteCurrent, _, _, typeLow⟩ := tc_current_scope_l ground
    (numbers.omega_l I (ZF.modelsKP hZF) tree.omega hN.1) rankC fs nc ρ hw rankU lim tau seed
  let aq : N₀.Domain := ⟨aγ, baseHeight.member⟩
  let Vq : N₀.Domain := ⟨Vγ, baseLayer.member⟩
  have rq := (rr_rank_native_l I mh.2.1 hN aq Vq).mp baseRank
  have wi : (ι.bound 0).val = w := (congrArg Subtype.val (links 0)).symm.trans hw
  obtain ⟨ψ, χ, queries, queryCoords, queryNode, queryLow, query_play, valid, same⟩ :=
    tg_issued_query_scope_l (ZF.modelsKP ground) (numbers.omega_l I (ZF.modelsKP hZF) tree.omega hN.1)
      fs nc ι rq baseLimit wi baseOmega baseLetters issued
  have chi0 : (χ.bound 0).val = (ρ.bound 13).val :=
    congrArg Subtype.val ((same 0).trans (links 3).symm)
  have chi3 : (χ.bound 3).val = (ρ.bound 8).val :=
    congrArg Subtype.val ((same 3).trans (links 1).symm)
  have chiw : (χ.bound 2).val.val = w.val := congrArg Subtype.val
    ((congrArg Subtype.val ((same 2).trans (links 0).symm)).trans hw)
  -- 旧回答来自实际 prepare；空集由原规则与外延性识别，刚性不另加查询成员前提。
  have state := (tg_issued_sat_l (rt_pair_l fs.transitive nc ground.1 fs.pair)
    (rt_model_ext_l ground.1 fs.transitive nc) ι).mp issued
  have control := state.control
  simp only [tg_control0_m, Formula.satisfies_conj_iff] at control
  have rules := control.2.2.1
  simp only [tg_rules_m, Formula.satisfies_conj_iff, Formula.satisfies_isEmpty_iff] at rules
  have he : ∀ x : N₀.Domain, ¬ N₀.mem x (ι.bound 1).val := fun x hx =>
    rules.2.1 ⟨x, fs.transitive _ (ι.bound 1).property x hx⟩ hx
  have eqe : ι.bound 1 = ε₀.bound 1 := Subtype.ext (ground.1.eq_of_same_members _ _
    (fun x => ⟨fun hx => (he x hx).elim, fun hx => (empty x hx).elim⟩))
  have lower : N₀.MemberSubset aq (ρ.bound 1).val := fun x hx => by
    rw [seed_height]
    exact baseLower x.val hx
  obtain ⟨queryScope, sourceMax⟩ := tg_rigid_native_l ground rankC fs nc (context.kernel_l mh.2.1 nc)
    ρ χ ψ ε₀ rq lower ⟨queryLow 4, queryLow 5, queryLow 6⟩
    ((same 2).trans (links 0).symm) ((same 3).trans (links 1).symm)
    ((same 0).trans (links 3).symm) ((same 1).trans (links 2).symm)
    ((queryCoords 0).trans (links 0).symm) ((queryCoords 2).trans (same 4).symm)
    ((queryCoords 3).trans (links 2).symm) ((queryCoords 1).trans eqe)
    ωε nε hi hh seed valid queries reply
  have qm : N₀.mem (ψ.bound 8).val (ι.bound 25).val :=
    Eq.mp (congrArg (fun a => N₀.mem (ψ.bound 8).val a) (congrArg Subtype.val (links 3))) sourceMax
  -- 此次相邻共同层的端点就是新历史界，故完整目标共同层属于目标反射层。
  let Vn : P₀.Domain := ⟨V₂, common.right_rank.2.1⟩
  let ln : P₀.Domain := ⟨l, common.right_rank.1⟩
  let Cn : P₀.Domain := ⟨C₁, record₁.context.member⟩
  let ηn : P₀.Domain := ⟨η₁, record₁.context.height⟩
  have rv := (rr_rank_native_l I mp.2.1 native ln Vn).mp common.right_rank
  have rc := (rr_rank_native_l I mp.2.1 native ηn Cn).mp ((rr_rank_truth_l I).mpr record₁.context.rank)
  have ol : P₀.IsOrdinal ln := (KP.ord0_sat_l native _ .newest).mp
    ((rr_truth_native_l I mp.2.1 (KP.ord0_m .newest) (by simp -implicitDefEqProofs)
      (fun _ : Fin 1 => ln)).mp bnd.ordinal)
  have inside : Rd_entry_d V₂ C₁ Rₚ :=
    ZF.v_mem_l (kp_pair_l native) targetZF rv rc (ZF.v_ordinal_height_l targetZF rc ol hχC)
  obtain ⟨d', hd', _, row⟩ := result.row_l hZF last
  have eq := next.diagram.model_function.2 m d' d hd' node
  subst d'
  obtain ⟨Rp, RC, _, bC, KC, _, mp', mc, _, sc, _, _, _, _, copy⟩ := row
  have eq := (smdl_unique_l I mp' mp).2
  subst Rp
  have rootC : Rd_entry_d Cᵣ C₁ q' :=
    (rootGraph Cᵣ C₁).mpr ⟨fromRoot.1.1.input_mem_of_pairMember rootCurrent, Cₚ, rootOld, iC⟩
  have ew₀ : w₀ = wₚ := agreement.injection.1.1.2 w.val w₀ wₚ hww₀ omegaPoint
  have ew₁ : w₁ = w₂ := embed.1.1.1.2 wₚ w₁ w₂ iw (ew₀ ▸ omegaEdge)
  have targetNumbers : Rr_layer_d I ω P Rₚ w₁ z₁ := ew₁.symm ▸ newNumbers
  obtain ⟨nd, ε, points, ew, truth⟩ := common.candidate_native_l hZF tree.omega
    root.model mh mp hN native fromRoot rootMap root.ext rootNumbers numbers targetNumbers
    context record₁.context rootCurrent rootC
    (fun x hx => (record₁.context.finite_l mp.2.1 native.1).transitive Vn inside
      ⟨x,(mp.2.2.2 x V₂ hx).1⟩ hx) nc χ chiw (chi3.symm ▸ tau) (chi0.symm ▸ typeLow) valid
  have images i : Rd_entry_d
      (ι.bound ([25,28,0,24,27,29,30,31,32,33,34,35].get i)).val.val (ε.bound i).val.val k₁ :=
    congrArg (fun x => x.val.val) (same i) ▸ points i
  -- 低层锚点随同一原边延长；完整查询公式仍沿两条根图传输。
  have nextAnchor := anchors γ₀ Bγ aγ Vγ sγ tγ baseHeight baseLayer baseRank baseLower baseOld
  have fs' := record₁.context.finite_l mp.2.1 native.1
  have ex : Rf_ext_d I N Rₕ := fromRoot.extensional_l hZF tree.omega root.model mh root.ext
  -- 整个固定低层低于本次共同秩段，故共享的锚点交换证明给出同一图上的参数。
  have hξU : N₀.mem ξ U₁ := ((common.carrier ξ.val).mp
    (common.injection.1.input_mem_of_pairMember hκ₀)).2
  have hξℓ := ZF.v_ordinal_height_l ground rankU (v_ordinal_l (kp_pair_l hN) rankP) hξU
  have haℓ : N₀.mem aq ℓ := ordinal_down_l hN baseLimit.1 (v_ordinal_l (kp_pair_l hN) rankU)
    (fun x hx => baseLower x.val hx) hξℓ
  have hVU : N₀.mem Vq U₁ := ZF.v_mem_l (kp_pair_l hN) ground rq rankU haℓ
  obtain ⟨ζ, queryImages, queryTruth⟩ := common.anchor_peer_l hZF tree.omega root.model mh mp
    fromRoot rootMap ex (certificate root).ext baseCurrent nextAnchor baseLayer
    (v_transitive_l (kp_pair_l hN) rankU) hVU ⟨CN, context.member⟩ Cn fs.transitive fs'.transitive nc nd
    rootCurrent rootC tg_query_row0_m tg_query_row0_closed_l ψ queryLow queries
  have qw : (ζ.bound 0).val.val = w₁ :=
    (common.injection.1.1.2 _ _ _ (congrArg (fun x => x.val.val) (queryCoords 0) ▸ queryImages 0) (images 2)).trans ew
  have qnode : Rd_entry_d (ζ.bound 11).val.val (ε.bound 0).val.val Rₚ :=
    (common.pred _ _ (images 0) _).mpr ⟨_, queryNode, queryImages 11⟩
  have qmax : Rd_entry_d (ζ.bound 8).val.val (ε.bound 0).val.val Rₚ :=
    (common.pred _ _ (images 0) _).mpr ⟨_, qm, queryImages 8⟩
  -- 指定池的单值性把已搬运 subtype 与本次候选逐项识别，再调用同一实现核。
  have fullImages i := ((restrict.2 _ _).mp (images i)).2
  have h₀ : Rd_entry_d (ρ.bound 0).val.val (ε.bound 2).val.val tₛ :=
    (congrArg (fun x => x.val.val) (links 0)).symm ▸ fullImages 2
  have h₁ : Rd_entry_d (ρ.bound 8).val.val (ε.bound 3).val.val tₛ :=
    (congrArg (fun x => x.val.val) (links 1)).symm ▸ fullImages 3
  have h₂ : Rd_entry_d (ρ.bound 9).val.val (ε.bound 1).val.val tₛ :=
    (congrArg (fun x => x.val.val) (links 2)).symm ▸ fullImages 1
  have h₃ : Rd_entry_d (ρ.bound 13).val.val (ε.bound 0).val.val tₛ :=
    (congrArg (fun x => x.val.val) (links 3)).symm ▸ fullImages 0
  have sameCurrent : ∀ i : Fin 3, θₛ.bound ([3,4,6].get i) = ε.bound ([3,1,0].get i) :=
    Fin.cases (Subtype.ext (Subtype.ext (ft.1.1.2 _ _ _ (pointsₛ 1) h₁)))
      (Fin.cases (Subtype.ext (Subtype.ext (ft.1.1.2 _ _ _ (pointsₛ 2) h₂)))
        (Fin.cases (Subtype.ext (Subtype.ext (ft.1.1.2 _ _ _ (pointsₛ 3) h₃))) (fun i => Fin.elim0 i)))
  have sw : (θₛ.bound 0).val.val = w₁ := (ft.1.1.2 _ _ _ (pointsₛ 0) h₀).trans ew
  have finite' : N₀.mem (ι.bound 28).val (ι.bound 0).val := by
    have em : (ρ.bound 9).val = (ι.bound 28).val := congrArg Subtype.val (links 2)
    have hm : N₀.mem (ι.bound 28).val w := Eq.mp (congrArg (fun x => N₀.mem x w) em) finiteCurrent
    exact Eq.mp (congrArg (fun x => N₀.mem (ι.bound 28).val x) wi.symm) hm
  have finiteRaw : Rd_entry_d (ε.bound 1).val.val (ε.bound 2).val.val Rₚ :=
    (common.pred _ _ (images 2) _).mpr ⟨_, finite', images 1⟩
  have finiteTarget : P₀.mem (ε.bound 1).val ⟨w₁, record₁.context.omega_mem⟩ :=
    Eq.mp (congrArg (fun a => Rd_entry_d (ε.bound 1).val.val a Rₚ) ew) finiteRaw
  obtain ⟨W, ν, pool, below, realized⟩ := record₁.context.realize_native_l hZF mp.2.1 targetZF
    (targetNumbers.omega_l I (ZF.modelsKP hZF) tree.omega native.1) nd ρₛ ε θₛ
    oldRound truth subtype program prior sameCurrent sw finiteTarget
  -- 查询的旧元数也由指定池图识别，不能把旧元数在原边上的像当作不动点。
  have h₄ : Rd_entry_d (ρ.bound 3).val.val (ζ.bound 2).val.val tₛ :=
    congrArg (fun x => x.val.val) ((queryCoords 2).trans arity.symm) ▸
      ((restrict.2 _ _).mp (queryImages 2)).2
  have eqn : (ζ.bound 2).val = (ρₛ.bound 24).val := Subtype.ext
    ((ft.1.1.2 _ _ _ (pointsₛ 4) h₄).symm.trans (congrArg (fun x => x.val.val) (prior 1)))
  have eqm : ζ.bound 3 = ε.bound 1 := Subtype.ext (Subtype.ext
    (common.injection.1.1.2 _ _ _
      (congrArg (fun x => x.val.val) (queryCoords 3) ▸ queryImages 3) (images 1)))
  have scopeTarget : P₀.mem (ζ.bound 4).val (ε.bound 6).val ∧
      P₀.mem (ζ.bound 5).val (ε.bound 6).val ∧ P₀.mem (ζ.bound 6).val (ε.bound 6).val := by
    have carry i (h : N₀.mem (ψ.bound i).val (χ.bound 6).val) : P₀.mem (ζ.bound i).val (ε.bound 6).val :=
      (common.pred _ _ (images 6) _).mpr ⟨_,
        Eq.mp (congrArg (fun a => N₀.mem (ψ.bound i).val a) (congrArg Subtype.val (same 6))) h, queryImages i⟩
    exact ⟨carry 4 queryScope.1, carry 5 queryScope.2.1, carry 6 queryScope.2.2⟩
  have candidateDomain := ((Formula.satisfies_conj_iff ..).mp truth).1
  simp only [Formula.satisfies_rename, ee_language0_m, ee_domain_pack_m,
    Formula.satisfies_bind, ee_domain_pack0_m, Formula.satisfies_conj_iff] at candidateDomain
  have hwU : P₀.mem ⟨w₁, record₁.context.omega_mem⟩ (ε.bound 6).val :=
    Eq.mp (congrArg (fun a => P₀.mem a (ε.bound 6).val) (show (ε.bound 2).val = ⟨w₁, record₁.context.omega_mem⟩ from Subtype.ext ew))
      candidateDomain.1.1
  -- 完整前驱图保持空集；目标旧存档中的空集因此是同一个对象。
  have emptyQuery : ∀ x : P₀.Domain, ¬ P₀.mem x (ζ.bound 1).val := by
    intro x hx
    obtain ⟨y, hy, iy⟩ := (common.pred _ _ (queryImages 1) x.val).mp hx
    let yn : N₀.Domain := ⟨y, ((common.carrier y).mp (common.injection.1.input_mem_of_pairMember iy)).1⟩
    exact he yn (Eq.mp (congrArg (fun a => N₀.mem yn a) (congrArg Subtype.val (queryCoords 1))) hy)
  have oldSeed := ((Formula.satisfies_conj_iff ..).mp oldRound).1
  simp only [tg_seed0_m, Formula.satisfies_rename, tg_seed_m, Formula.satisfies_conj_iff] at oldSeed
  have emptyOld : ∀ x : P₀.Domain, ¬ P₀.mem x (ρₛ.bound 17).val := fun x hx =>
    (Formula.satisfies_isEmpty_iff ..).mp oldSeed.2.1
      ⟨x, fs'.transitive _ (ρₛ.bound 17).property x hx⟩ hx
  have eqe : (ζ.bound 1).val = (ρₛ.bound 17).val := targetZF.1.eq_of_same_members _ _
    (fun x => ⟨fun hx => (emptyQuery x hx).elim, fun hx => (emptyOld x hx).elim⟩)
  have witness : Tg_realized_in_d (M := P₀) ⟨w₁, record₁.context.omega_mem⟩
      (ρₛ.bound 18).val (ρₛ.bound 24).val (ρₛ.bound 29).val (ζ.bound 3).val
      (ε.bound 6).val W (ε.bound 0).val ν Cn := by
    rw [eqm]
    exact realized
  obtain ⟨εr, eqr, recovered⟩ := tg_recover_read_l native nd ρₛ ζ
    (targetNumbers.omega_l I (ZF.modelsKP hZF) tree.omega native.1) fs'
    (record₁.context.kernel_l mp.2.1 nd) oldRound queryTruth (Subtype.ext qw) eqe eqn
    hwU scopeTarget qnode qmax witness
  -- 当前真实标签函数沿完整前驱图搬运；恢复节点确定它的同一函数域。
  let ιl : Env (rt_model_l (M := N₀) ⟨CN, context.member⟩ nc) 3 :=
    ⟨fun i => [ι.bound 26,ι.bound 0,ι.bound 23].get i, ι.free⟩
  have labels₀ : Fn0_d (M := N₀) (ι.bound 26).val (ι.bound 0).val (ι.bound 23).val :=
    (fn0_sat_l ground.1 _ (.bound 0) (.bound 1) (.bound 2)).mp
      ((rt_model_delta_l fs.transitive nc (fn0_delta_l (.bound 0) (.bound 1) (.bound 2)) ιl).mp
        ((fn0_sat_l (rt_model_ext_l ground.1 fs.transitive nc) ιl (.bound 0) (.bound 1) (.bound 2)).mpr state.labels))
  have labels₁ := (rr_native_function_l I mh.2.1 mp.2.1 ground.1 targetZF.1 U₁
    (v_transitive_l (kp_pair_l hN) rankU) common.carrier common.injection common.pred
    (ι.bound 26).val (ι.bound 0).val (ι.bound 23).val (ζ.bound 4).val (ζ.bound 0).val (ζ.bound 6).val
    (congrArg (fun x => x.val.val) (queryCoords 4) ▸ queryImages 4)
    (congrArg (fun x => x.val.val) (queryCoords 0) ▸ queryImages 0)
    (congrArg (fun x => x.val.val) (queryCoords 5) ▸ queryImages 6) labels₀).1
  have labelsR : Fn0_d (M := P₀) (ζ.bound 4).val (εr.bound 7).val (εr.bound 16).val := by
    have ew : (εr.bound 7).val = (ζ.bound 0).val := (eqr 0).trans (Subtype.ext qw).symm
    have et : (εr.bound 16).val = (ζ.bound 6).val := eqr 9
    rw [ew, et]
    exact labels₁
  obtain ⟨label_domain, labels⟩ := tg_restart_labels_l native fs'.transitive nd εr recovered labelsR
  have oldω : (ρₛ.bound 16).val = (⟨w₁, record₁.context.omega_mem⟩ : P₀.Domain) :=
    Subtype.ext ((congrArg (fun x => x.val.val) (prior 0)).symm.trans sw)
  have sameL : ζ.bound 2 = ε.bound 4 := Subtype.ext (Subtype.ext
    (common.injection.1.1.2 _ _ _
      (congrArg (fun x => x.val.val) (queryCoords 2) ▸ queryImages 2) (images 4)))
  have sameRecovery : ∀ i : Fin 10, εr.bound ([7,8,10,11,12,13,23,24,25,28].get i) =
      [ρₛ.bound 16,ρₛ.bound 17,ρₛ.bound 23,ρₛ.bound 24,ε.bound 1,ε.bound 6,
        ρₛ.bound 18,ρₛ.bound 19,ρₛ.bound 20,ε.bound 0].get i := by
    intro i
    apply Subtype.ext
    exact Fin.cases ((eqr 0).trans oldω.symm) (Fin.cases (eqr 1) (Fin.cases (eqr 3)
      (Fin.cases (eqr 4) (Fin.cases ((eqr 5).trans (congrArg Subtype.val eqm)) (Fin.cases (eqr 6)
        (Fin.cases (eqr 16) (Fin.cases (eqr 17) (Fin.cases (eqr 18)
          (Fin.cases (eqr 21) (fun j => Fin.elim0 j)))))))))) i
  -- 候选 τ 低于共同端点，端点又包含于旧 κ 的原边像，给出重启所需严格界。
  have oldκ := embed.1.1.1.2 κp κ' (ρₛ.bound 15).val.val hκ' old_height
  have hτ := (rt_limit_l fs'.transitive nd native (ε.bound 3)).mp
    ((Formula.satisfies_isLimitOrdinal_iff ..).mp candidateDomain.2.1)
  have hτV : P₀.mem (ε.bound 3).val Vn := (common.image _).mpr
    ⟨_, common.injection.1.input_mem_of_pairMember (images 3), images 3⟩
  have belowNext : P₀.mem (ε.bound 3).val (ρₛ.bound 15).val :=
    Eq.mp (congrArg (fun a => Rd_entry_d (ε.bound 3).val.val a Rₚ) oldκ)
      (boundκ _ (ZF.v_ordinal_height_l targetZF rv hτ.1 hτV))
  obtain ⟨πp, eqp, v₂, seed₂, a₂, round₂⟩ := tg_restart_read_l (record₁.context.kernel_l mp.2.1 nd) ρₛ ε εr
    (θₛ.reindex (fun i : Fin 11 => [0,1,7,8,10,11,12,13,14,15,16].get i))
    oldRound truth recovered program labels sameRecovery
    (Subtype.ext ((Subtype.ext ew).trans oldω.symm))
    (Subtype.ext ((congrArg Subtype.val sameL).symm.trans eqn)) (prior 0) (prior 1) belowNext
  -- 新轮的完整请求坐标沿指定代表池图对应；程序槽位也使用同一内部有限元数。
  let ρ₂ := tg_round_env_d (tg_restart_env_d ρₛ ε εr πp v₂) a₂
  have qpts i := ((restrict.2 _ _).mp (queryImages i)).2
  have pw : Rd_entry_d (ι.bound 0).val.val (ρₛ.bound 16).val.val tₛ :=
    (congrArg Subtype.val (show (ε.bound 2).val = (ρₛ.bound 16).val from
      (Subtype.ext ew).trans oldω.symm)) ▸ fullImages 2
  have pe : Rd_entry_d (ι.bound 1).val.val (ρₛ.bound 17).val.val tₛ :=
    congrArg Subtype.val eqe ▸ (congrArg (fun x => x.val.val) (queryCoords 1) ▸ qpts 1)
  have pk : Rd_entry_d (ι.bound 26).val.val (ρₛ.bound 23).val.val tₛ :=
    congrArg Subtype.val (label_domain.trans (eqr 3)) ▸
      (congrArg (fun x => x.val.val) (queryCoords 4) ▸ qpts 4)
  have pl : Rd_entry_d (ι.bound 27).val.val (ρₛ.bound 24).val.val tₛ :=
    congrArg Subtype.val eqn ▸ (congrArg (fun x => x.val.val) (queryCoords 2) ▸ qpts 2)
  have pc (i : Fin 9) : Rd_entry_d (ι.bound ([36,37,38,39,40,41,42,43,44].get i)).val.val
      (πp.bound ([2,4,5,6,7,8,9,10,11].get i)).val.val tₛ :=
    (congrArg (fun x => x.val.val) (eqp i.succ.succ)).symm ▸ program_points i
  have pt : Rd_entry_d (ι.bound 23).val.val (εr.bound 16).val.val tₛ :=
    (congrArg Subtype.val (eqr 9)).symm ▸ (congrArg (fun x => x.val.val) (queryCoords 5) ▸ qpts 6)
  have request : Tg_request_d (fun y x => Rd_entry_d x y tₛ) (fun i => (ι.bound i).val.val)
      (fun i => (ρ₂.bound i).val.val) := by
    intro i
    exact Fin.cases pw (Fin.cases pe (Fin.cases pk (Fin.cases pl (Fin.cases (fullImages 1)
      (Fin.cases (pc 0) (Fin.cases (pc 1) (Fin.cases (pc 2) (Fin.cases (pc 3) (Fin.cases (pc 4)
        (Fin.cases (pc 5) (Fin.cases (pc 6) (Fin.cases (pc 7) (Fin.cases (pc 8)
          (Fin.cases (fullImages 3) (Fin.cases (fullImages 6) (Fin.cases (fullImages 7)
            (Fin.cases (fullImages 0) (Fin.cases pt (fun j => Fin.elim0 j))))))))))))))))))) i
  -- 保存使用新回答自己给出的支撑；同一个扩展器证书随存档返回，供下一条原边施加。
  obtain ⟨Lr, Wr, qr, saved₂, code₂, high₂, X₂, K₂, R₂, F₂, c₂, d₂, Y₂, S₂, j₂, κ₂, U₂, D₂, u₂, image₂⟩ :=
    record₁.context.save_round_native_l hZF mp.2.1
    ((certificate root).native_l I hZF tree.omega)
    (targetNumbers.omega_l I (ZF.modelsKP hZF) tree.omega native.1) nd ρ₂ round₂ (congrArg Subtype.val oldω)
  have rW := (rr_rank_native_l I mp.2.1 native Lr Wr).mp ((rr_rank_truth_l I).mpr saved₂.rank)
  have lower₂ : P₀.MemberSubset ln (ρ₂.bound 39).val := fun x hx =>
    Eq.mp (congrArg (fun a => Rd_entry_d x.val a Rₚ) oldκ) (boundκ x.val hx)
  have above₂ : Rd_entry_d l Lr.val Rₚ :=
    ordinal_down_l native ol (v_ordinal_l (kp_pair_l native) rW) lower₂ high₂
  -- 旧不可达支撑给出不可数共尾性；τ+ω 的完整秩历史实际进入右侧共同层。
  have uncountable := sc_v_inaccessible_up_l hN height rank card
  have point : Rd_entry_d (ρ.bound 8).val.val (ρ₂.bound 21).val.val k₁ :=
    (congrArg (fun x => x.val.val) (links 1)).symm ▸ images 3
  -- 原 γ₀ 下界随临界点像传入目标，再用真实超过关系提升到新临界点。
  have source_lower : It_lower_d I γ₀ N Rₕ ξ.val := ⟨aγ, sγ, baseHeight, baseLower⟩
  have facts := seed
  simp only [tc_seed0_m, Formula.satisfies_conj_iff] at facts
  obtain ⟨_, _, _, _, _, _, _, _, exceeds, _⟩ := facts
  have hξτ : N₀.mem ξ (ρ.bound 8).val :=
    Eq.mp (congrArg (fun x => N₀.mem x (ρ.bound 8).val) seed_height)
      ((Formula.satisfies_conj_iff ..).mp exceeds).1
  have below₀ : P₀.mem ⟨κ₀, common.injection.1.output_mem_of_pairMember hκ₀⟩ (ρ₂.bound 21).val :=
    (common.pred _ _ point κ₀).mpr ⟨ξ.val, hξτ, hκ₀⟩
  have lower_next : It_lower_d I γ₀ P Rₚ (ρ₂.bound 21).val.val := by
    obtain ⟨a, s, layer, down⟩ := (lower_images γ₀ source_lower).2.1
    refine ⟨a, s, layer, fun x hx => ?_⟩
    exact hτ.1.transitive ⟨κ₀, common.injection.1.output_mem_of_pairMember hκ₀⟩ below₀
      ⟨x, (mp.2.2.2 x a hx).1⟩ (down x hx)
  obtain ⟨α₂, β₂, hα₂, hβ₂, hκ₂, limitα₂, rankβ₂, _⟩ := common.limit_cut_l (ZF.modelsKP hZF)
    mh.2.1 mp.2.1 ground native w ℓ (ρ.bound 8).val (ρ₂.bound 21).val
    (numbers.omega_l I (ZF.modelsKP hZF) tree.omega hN.1) uncountable.2.1 uncountable.1 high point
  have limitP : P₀.IsLimitOrdinal ln := (KP.limit0_sat_l native _ .newest).mp
    ((rr_truth_native_l I mp.2.1 (KP.limit0_m .newest) (by simp -implicitDefEqProofs)
      (fun _ : Fin 1 => ln)).mp (adjacent.right_limit_l hZF tree.omega mp mc copy))
  have hαLr : P₀.mem α₂ Lr := (v_ordinal_l (kp_pair_l native) rW).transitive ln above₂ α₂ hα₂
  obtain ⟨Γ₂,k₂,carrier₂,fk₂,image_back,pred₂,graph₂⟩ :=
    adjacent.common.reverse_native_l hZF mh hN
  -- 原施加图独立于工作复制；此处仅为尚需复制的历史恢复实际交换方块。
  have square₂ x x' y (xx : Rd_entry_d x x' τ) (pair : Rd_entry_d x y k₂) : Rd_entry_d y x' σ := by
    have yx := (graph₂ x y).mp pair
    obtain ⟨y',_,yy⟩ := map.1.1.2.2 y
      ((adjacent.common.carrier y).mp (adjacent.common.injection.1.input_mem_of_pairMember yx)).1
    exact copy.1.1.1.2 x y' x' (adjacent.points y y' x yy yx) xx ▸ yy
  -- 恢复节点的完整函数域先沿逆共同图回读，再用同一历史的事件唯一性比较旧实数图。
  have query_node := recovered
  simp only [tc_recovered0_m,tc_recovered_m,Formula.satisfies_conj_iff] at query_node
  obtain ⟨_,_,_,_,_,_,_,_,_,query_node,_⟩ := query_node
  have query_node := (tg_node_source_l fs'.transitive nd native.1 (KP.exists_pair native) εr
    (.bound 10) (.bound 24) (.bound 15) (.bound 16) (.bound 2)).mp query_node
  have e_s : (εr.bound 15).val = (ζ.bound 5).val := eqr 8
  have query_graph₁ : Tg_graph_d (kp_pair_l native) (ζ.bound 4).val (ζ.bound 5).val :=
    Eq.mp (congrArg (Tg_graph_d (kp_pair_l native) (ζ.bound 4).val) e_s)
      (Eq.mpr (congrArg (fun n => Tg_graph_d (kp_pair_l native) n (εr.bound 15).val) label_domain) query_node.1)
  have query_graph := rr_native_graph_l I hZF.1 mp.2.1 mh.2.1 native.1 (KP.exists_pair native)
    hN.1 (KP.exists_pair hN) Vn U₁
    (v_transitive_l (kp_pair_l native) rv) (v_transitive_l (kp_pair_l hN) rankU)
    carrier₂ fk₂ image_back pred₂ (ζ.bound 4).val (ζ.bound 5).val (ψ.bound 4).val (ψ.bound 5).val
    ((graph₂ _ _).mpr (queryImages 4)) ((graph₂ _ _).mpr (queryImages 5)) query_graph₁
  have query_graph : Tg_graph_d (kp_pair_l hN) (ι.bound 26).val (ψ.bound 5).val :=
    Eq.mp (congrArg (fun k => Tg_graph_d (kp_pair_l hN) k (ψ.bound 5).val)
      (congrArg Subtype.val (queryCoords 4))) query_graph
  have query_play₀ : Tg_play_d I N Rₕ CN (ι.bound 4).val.val (ι.bound 3).val.val
      (ι.bound 20).val.val (ψ.bound 5).val.val :=
    (tg_play_native_l I mh.2.1 ground.1 ⟨CN,context.member⟩ fs.transitive nc
      (rt_pair_l fs.transitive nc ground.1 fs.pair)
      (ι.bound 4) (ι.bound 3) (ι.bound 20) (ψ.bound 5)).mpr query_play
  have short_sub := Tg_play_d.native_subset_l I mh.2.1 hN.1 (KP.exists_pair hN)
    ⟨CN,context.member⟩ fs.transitive nc
    (rt_pair_l fs.transitive nc ground.1 fs.pair) ι issued k_old.val (ι.bound 26).val s_old (ψ.bound 5)
    old_play query_play₀ old_graph query_graph old_size
  have label_sub : N₀.MemberSubset t_old.val (ψ.bound 6).val :=
    Eq.mpr (congrArg (fun t => N₀.MemberSubset t_old.val t) (congrArg Subtype.val (queryCoords 5))) old_labels
  have low_short := v_subset_mem_l (kp_pair_l hN) rq (queryLow 5) short_sub
  have low_label := v_subset_mem_l (kp_pair_l hN) rq (queryLow 6) label_sub
  have low_critical := (KP.v_compare_l hN rq rankP (fun x hx => baseLower x.val hx)).1
  obtain ⟨x_s,old_s,next_s⟩ := old_images 0
  obtain ⟨x_t,old_t,next_t⟩ := old_images 1
  have point_s := (lowSquare s_old.val x_s (ρₛ.bound 40).val.val (low_critical _ low_short) old_s).mpr next_s
  have point_t := (lowSquare t_old.val x_t (ρₛ.bound 41).val.val (low_critical _ low_label) old_t).mpr next_t
  have carry_subset (a b : N₀.Domain) (a' b' : P₀.Domain)
      (ia : Rd_entry_d a.val a'.val k₁) (ib : Rd_entry_d b.val b'.val k₁) (sub : N₀.MemberSubset a b) :
      P₀.MemberSubset a' b' := by
    let ρ : Env N₀ 2 := ⟨Fin.cases a (fun _ => b),fun _ => a⟩
    let η : Env P₀ 2 := ⟨Fin.cases a' (fun _ => b'),fun _ => a'⟩
    have moved := rr_graph_delta_l I mh.2.1 mp.2.1 ⟨a.val,common.injection.1.input_mem_of_pairMember ia⟩
      (fun x hx => ((common.carrier x).mp hx).1)
      (fun x y hx hy hyx => (common.carrier y).mpr ⟨hy,
        (v_transitive_l (kp_pair_l hN) rankU) ⟨x,((common.carrier x).mp hx).1⟩
          ((common.carrier x).mp hx).2 ⟨y,hy⟩ hyx⟩)
      common.injection common.pred (Formula.subset (.bound 0) (.bound 1))
      (by simp -implicitDefEqProofs) (.atom ..) ρ η (Fin.cases ia (fun _ => ib))
    exact (Formula.satisfies_subset_iff η ..).mp (moved.mp ((Formula.satisfies_subset_iff ρ ..).mpr sub))
  have short_new : P₀.MemberSubset (ρₛ.bound 40).val (ρ₂.bound 40).val :=
    Eq.mpr (congrArg (fun s => P₀.MemberSubset (ρₛ.bound 40).val s) (eqr 8))
      (carry_subset s_old.val (ψ.bound 5).val (ρₛ.bound 40).val (ζ.bound 5).val point_s (queryImages 5) short_sub)
  have label_new : P₀.MemberSubset (ρₛ.bound 41).val (ρ₂.bound 41).val :=
    Eq.mpr (congrArg (fun t => P₀.MemberSubset (ρₛ.bound 41).val t) (eqr 9))
      (carry_subset t_old.val (ψ.bound 6).val (ρₛ.bound 41).val (ζ.bound 6).val point_t (queryImages 6) label_sub)
  obtain ⟨graph_entry,graph_ends⟩ := tg_recovered_graph_l native.1 fs'.transitive nd εr recovered
  have e_n : (εr.bound 9).val = (ρₛ.bound 22).val := eqr 2
  have e_g : (εr.bound 26).val = (ρₛ.bound 42).val := eqr 19
  have e_pair : ((εr.bound 9).val,(εr.bound 26).val) = ((ρₛ.bound 22).val,(ρₛ.bound 42).val) :=
    Prod.ext e_n e_g
  have graph_entry := Eq.mp (congrArg (fun n => Rd_entry_d n (εr.bound 1).val (εr.bound 2).val) e_n) graph_entry
  have graph_ends (p : P₀.Domain) : P₀.mem p (ρ₂.bound 42).val ↔
      P₀.mem p (ρₛ.bound 42).val ∨ KPair_d P₀ p (ρₛ.bound 22).val (εr.bound 1).val :=
    Eq.mp (congrArg (fun q : P₀.Domain × P₀.Domain => P₀.mem p (εr.bound 2).val ↔
      P₀.mem p q.2 ∨ KPair_d P₀ p q.1 (εr.bound 1).val) e_pair) (graph_ends p)
  have size_next := (rt_successor_l fs'.transitive nd native.1 (ρₛ.bound 23) (ρₛ.bound 22)).mp
    ((Formula.satisfies_isSuccessor_iff ..).mp oldSeed.2.2.2.2.2.2.2.1)
  have restart_link := Tg_restart_link_d.of_native_l I mp.2.1 native.1
    (fun i => (ρₛ.bound ([19,22,40,41,42].get i)).val) (fun i => (ρ₂.bound i).val) (εr.bound 1).val rfl
    size_next short_new label_new graph_entry graph_ends
  -- 已保存回答的这份具体扩展器直接施加到原偶数模型，完整查询与超幂见证保留。
  have data₂ := image₂
  obtain ⟨rank₂, source₂, hLδ₂, hκL₂, hτL₂, _, hQW₂, loc₂, card₂, strong₂, mx₂, my₂, ultra₂, crit₂, bound₂,
    _, iU₂, iD₂, iu₂, _, _⟩ := data₂
  have limitC : P₀.IsLimitOrdinal ηn := (Formula.satisfies_isLimitOrdinal_iff ..).mp
    ((rr_truth_native_l I mp.2.1 (Formula.isLimitOrdinal .newest) (by simp -implicitDefEqProofs)
      (fun _ : Fin 1 => ηn)).mp record₁.context.limit)
  have height₂ := (tg_round_control_l native rc limitC fs' nd ρ₂ round₂).2.isLimitOrdinal
  obtain ⟨Ls₂, Js₂, Os₂, Zs₂, Ds₂, ps₂, Vs₂, Ws₂, qs₂, d₃, P₃, R₃, j₃, q₃, p₃, cut₂⟩ :=
    loc₂.raw_rank_source_l hZFC tree.omega mp.2.1 ((certificate root).native_l I hZF tree.omega)
      Vn ⟨w₁, record₁.context.omega_mem⟩ (ρ₂.bound 21).val Lr F₂ α₂ β₂ ln X₂ K₂ R₂ (ρ₂.bound 18).val
      c₂ d₂ Y₂ S₂ j₂ κ₂ mp root mh fromRoot targetNumbers rv limitP carrier₂ fk₂ image_back pred₂
      common.left_closed source_small hβ₂ hκ₂ limitα₂ rankβ₂ hαLr source₂ rank₂ height₂ mx₂ my₂ ultra₂
      card₂ strong₂ crit₂.image bound₂
  -- 保留固定的新原后继；只读取本次原模型、根图及树延伸证书。
  have fixed₂ := cut₂
  obtain ⟨finite₃, closed₃, _, hβV₃, hβX₃, transβ₃, products₃, length₃, raw₃, diagram₃, limit₃,
    mp₃, _, _, _, embed₃, rootMap₃, constants₃, agreement₃, payload₃, _, cert₃, rootGraph₃,
    U₃, rankU₃, readU₃, _, _, l₃, V₃, Γ₃, k₃, common₃, _, _, tail₃⟩ := cut₂
  obtain ⟨Pκ₃, rankP₃, lowSquare₃, κ₀₃, bκ₃, κt₃, iκ₀₃, ibκ₃, iκt₃, _, belowκ₃, _, memκ₃,
    _, _, _, _, lowerImages₃, anchors₃, rest₃⟩ := tail₃
  -- 同一根低层也进入第二个原后继；高度对象由完整解释唯一性识别。
  have atlas := nextAnchor
  obtain ⟨ag, Vg, sg, tg, heightg, layerg, rg, fixedg⟩ := atlas
  have cutoff := lower_next
  obtain ⟨bg, zg, heightb, boundg⟩ := cutoff
  have eqg := (heightg.unique_l (ZF.modelsKP hZF) heightb (certificate root).ext).1
  have anchor₃ := anchors₃ γ₀ Bγ ag Vg sg tg heightg layerg rg
    (fun x hx => boundg x (eqg ▸ hx)) baseCurrent
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, rest₃⟩ := rest₃
  obtain ⟨_, wT₃, _, zT₃, _, iwT₃, _, _, numbers₃, _, _, _, _, _, _, _, _, _, _, _, pool₃, build₃⟩ := rest₃
  obtain ⟨A₃, Q₃, B₃, e₃, Dp₃, Bp₃, _, _, t₃, pool₃, dc₃, bc₃, _, _, _, _, ft₃,
    restrict₃, endpoint₃, layer₃, present₃, prepare₃, bβ₃, Hβ₃, _, hbH₃, full₃, pred₃, commute₃, _⟩ := pool₃
  -- 新轮自身给出低秩参数；dcp 和子类型的存在见证留在本次所选完整池中。
  obtain ⟨hU₂, hD₂, hu₂, hl₂, hn₂, hk₂, labels₂, labelLow₂, digits₂⟩ := tg_round_members_l targetZF
    (targetNumbers.omega_l I (ZF.modelsKP hZF) tree.omega native.1) rc fs' nd ρ₂
    oldω rankβ₂ limitα₂ hκ₂ round₂
  have hWB₃ : P₀.mem Wr B₃ :=
    (ZF.v_unique_l (kp_pair_l native) targetZF rankU₃ rW) ▸
      ((bc₃ U₃.val).mp (ft₃.1.input_mem_of_pairMember layer₃)).2
  obtain ⟨transB₃, pairB₃, nb₃, ψ₃, values₃, replyB₃⟩ := image₂.reply_pool_l targetZF height₂ rankβ₂ limitα₂
    (height₂.1.transitive Lr hLδ₂ α₂ hαLr) hU₂ hD₂ hu₂ pool₃ hWB₃ (digits₂ 0) (digits₂ 1)
    (fun i => digits₂ i.succ.succ)
  let Hβn : (smdl_structure_l I (R := R₃) mp₃.2.1).Domain :=
    ⟨Hβ₃, embed₃.1.1.output_mem_of_pairMember hbH₃⟩
  obtain ⟨η₃, replyPoints₃, reply₃⟩ := tg_reply_raw_image_l I mp.2.1 mp₃.2.1
    (ZF.modelsKP (ZFC.models_zf_l ((cert₃ root).native_l I hZF tree.omega)))
    B₃ Hβn pairB₃ nb₃ ψ₃ replyB₃ bc₃ ft₃ full₃ pred₃
  -- 请求点先由共同层完整值域回到逆图，再由同一个常值方块进入原边。
  have back (x : P₀.Domain) a (hx : P₀.mem x β₂) (ha : Rd_entry_d a x.val tₛ) :
      Rd_entry_d x.val a k₂ := by
    obtain ⟨b, _, ib⟩ := (common.image x.val).mp ((v_transitive_l (kp_pair_l native) rv) β₂ hβ₂ x hx)
    have eq := ft.2 a b x.val ha ((restrict.2 b x.val).mp ib).2
    exact (graph₂ x.val a).mpr (eq.symm ▸ ib)
  let vals := tg_round_reply_values_d (fun j => (ρ₂.bound j).val) ⟨w₁, record₁.context.omega_mem⟩ κ₂ U₂ D₂ u₂
  have carry (x : P₀.Domain) i a (hx : P₀.mem x β₂) (hi : Rd_entry_d x (vals i) j₂)
      (ha : Rd_entry_d a x.val tₛ) : Rd_entry_d a (η₃.bound i).val j₃ := by
    have hi : Rd_entry_d x (ψ₃.bound i).val j₂ :=
      Eq.mp (congrArg (fun y => Rd_entry_d x y j₂) (values₃ i).symm) hi
    exact (commute₃ x (ψ₃.bound i).val a (η₃.bound i).val hx hi (back x a hx ha)).mp (replyPoints₃ i)
  have pj := ultra₂.elementary_l targetZF mx₂.1 my₂.1
  have pt := ultra₂.transitive_l targetZF my₂.1
  have iω₂ := pj.omega_l (kp_pair_l native) targetZF source₂.omega source₂.transitive pt mx₂ my₂ source₂.omega_mem
  have natural₂ := pj.natural_l targetZF source₂.omega source₂.transitive pt mx₂ my₂ source₂.omega_mem
  have hwβ₂ := v_subset_mem_l (kp_pair_l native) rankβ₂ hκ₂ source₂.below
  have low₂ (x : P₀.Domain) (hx : P₀.mem x ⟨w₁, record₁.context.omega_mem⟩) : P₀.mem x β₂ :=
    transβ₃ _ hwβ₂ x hx
  have pd (i : Fin 9) : Rd_entry_d (ι.bound ([36,37,38,39,40,41,42,43,44].get i)).val.val
      (ρ₂.bound ([36,38,47,48,49,50,51,52,53].get i)).val.val tₛ :=
    Fin.cases (request 5) (Fin.cases (request 6) (Fin.cases (request 7) (Fin.cases (request 8)
      (Fin.cases (request 9) (Fin.cases (request 10) (Fin.cases (request 11)
        (Fin.cases (request 12) (Fin.cases (request 13) (fun j => Fin.elim0 j))))))))) i
  have program₃ (i : Fin 9) : Rd_entry_d (ι.bound ([36,37,38,39,40,41,42,43,44].get i)).val.val
      (η₃.bound ([10,11,15,16,17,18,19,20,21].get i)).val j₃ := by
    have eq : vals ([10,11,15,16,17,18,19,20,21].get i) =
        (ρ₂.bound ([36,38,47,48,49,50,51,52,53].get i)).val := by
      exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl
        (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun j => Fin.elim0 j))))))))) i
    exact carry _ _ _ (low₂ _ (digits₂ i))
      (Eq.mp (congrArg (fun y => Rd_entry_d (ρ₂.bound ([36,38,47,48,49,50,51,52,53].get i)).val y j₂) eq.symm)
        (natural₂ _ (digits₂ i))) (pd i)
  have linked₃ : Tg_reply_link_d (fun x y => Rd_entry_d x y j₃)
      (fun i => (ι.bound i).val.val) (fun i => (η₃.bound i).val) :=
    Fin.cases (carry _ 0 _ hwβ₂ iω₂ ((congrArg Subtype.val oldω) ▸ request 0))
      (Fin.cases (carry _ 1 _ (low₂ _ hl₂) (natural₂ _ hl₂) (request 3))
        (Fin.cases (carry _ 2 _ (low₂ _ hn₂) (natural₂ _ hn₂) (request 4))
          (Fin.cases (carry _ 3 _ hκ₂ crit₂.image (request 14))
            (Fin.cases (carry _ 5 _ hU₂ iU₂ (request 15))
              (Fin.cases (carry _ 6 _ hD₂ iD₂ (request 16))
                (Fin.cases (carry _ 8 _ hu₂ iu₂ (request 17))
                  (Fin.cases (program₃ 0) (Fin.cases (program₃ 1) (Fin.cases (program₃ 2)
                    (Fin.cases (program₃ 3) (Fin.cases (program₃ 4) (Fin.cases (program₃ 5)
                      (Fin.cases (program₃ 6) (Fin.cases (program₃ 7)
                        (Fin.cases (program₃ 8) (fun i => Fin.elim0 i))))))))))))))))
  -- 原当前请求完整保存后沿 j₃ 搬运；新复制界使用同一记录的 δ。
  have targetKP₃ := ZF.modelsKP (ZFC.models_zf_l ((cert₃ root).native_l I hZF tree.omega))
  let P₀₃ := smdl_structure_l I (R := R₃) mp₃.2.1
  obtain ⟨rN, recordN, tupleN⟩ := rf_record_save_l I mh.2.1 hN.1 tg_issued0_m tg_issued0_closed_l
    ⟨CN, context.member⟩ fs.transitive fs.pair nc ι issued
  obtain ⟨w₃, _, iw₃⟩ := embed₃.1.1.2.2 w.val w.property
  obtain ⟨ηN₃, CN₃, iηN₃, iCN₃, context₃⟩ := context.map_l hZF tree.omega mh mp₃ embed₃ iw₃
  let CNn₃ : P₀₃.Domain := ⟨CN₃, context₃.member⟩
  let ηNn₃ : P₀₃.Domain := ⟨ηN₃, context₃.height⟩
  have fs₃ := context₃.finite_l mp₃.2.1 targetKP₃.1
  let nc₃ : Nonempty {x : P₀₃.Domain // P₀₃.mem x CNn₃} := ⟨⟨⟨w₃, context₃.omega_mem⟩, fs₃.omega_mem⟩⟩
  obtain ⟨_, ι₃, _, issuedPoints₃, _, _, issued₃⟩ := embed₃.record_image_l I hZF tree.omega mh mp₃
    targetKP₃.1 CNn₃ iCN₃ fs₃.transitive nc₃ tg_issued0_m tg_issued0_closed_l recordN tupleN
  have rankCN₃ := (rr_rank_native_l I mp₃.2.1 targetKP₃ ηNn₃ CNn₃).mp
    ((rr_rank_truth_l I).mpr context₃.rank)
  have limitCN₃ : P₀₃.IsLimitOrdinal ηNn₃ := (Formula.satisfies_isLimitOrdinal_iff ..).mp
    ((rr_truth_native_l I mp₃.2.1 (Formula.isLimitOrdinal .newest) (by simp -implicitDefEqProofs)
      (fun _ : Fin 1 => ηNn₃)).mp context₃.limit)
  obtain ⟨boundδ₃, regularδ₃⟩ := tg_issued_control_l targetKP₃ rankCN₃ limitCN₃ fs₃ nc₃ ι₃ issued₃
  have eqb := fk₂.1.1.2 _ bκ₃ (ι.bound 24).val.val ibκ₃ (back _ _ hκ₂ (request 14))
  have eqκ := embed₃.1.1.1.2 _ κt₃ (ι₃.bound 24).val.val (eqb ▸ iκt₃) (issuedPoints₃ 24)
  let ln₃ : P₀₃.Domain := ⟨l₃, common₃.right_rank.1⟩
  let Vn₃ : P₀₃.Domain := ⟨V₃, common₃.right_rank.2.1⟩
  have rankV₃ := (rr_rank_native_l I mp₃.2.1 targetKP₃ ln₃ Vn₃).mp common₃.right_rank
  have candidateBound₃ : P₀₃.MemberSubset ln₃ (ι₃.bound 24).val :=
    fun x hx => Eq.mp (congrArg (fun y => Rd_entry_d x.val y R₃) eqκ) (belowκ₃ x.val hx)
  have lowδ₃ : P₀₃.mem ln₃ (ι₃.bound 5).val := ordinal_down_l targetKP₃
    (v_ordinal_l (kp_pair_l targetKP₃) rankV₃) regularδ₃.isCardinal.1 candidateBound₃ boundδ₃
  have iwN : (ι.bound 0).val.val = w.val := congrArg (fun x => x.val.val) (links 0).symm |>.trans (congrArg Subtype.val hw)
  have eqω₃ := embed₃.1.1.1.2 w.val (ι₃.bound 0).val.val w₃ (iwN ▸ issuedPoints₃ 0) iw₃
  have ground₃ := ZFC.models_zf_l ((cert₃ root).native_l I hZF tree.omega)
  have hlC₃ := fs₃.transitive (ι₃.bound 5).val (ι₃.bound 5).property ln₃ lowδ₃
  -- 同一原边识别请求坐标；新查询域由真实共同秩层进入当前反射层。
  have points₃ i : Rd_entry_d (vals i).val (η₃.bound i).val t₃ :=
    Eq.mp (congrArg (fun x : P₀.Domain => Rd_entry_d x.val (η₃.bound i).val t₃) (values₃ i)) (replyPoints₃ i)
  have equal₃ : Tg_reply_link_d Eq (fun i => (ι₃.bound i).val) η₃.bound := fun i =>
    Subtype.ext (embed₃.1.1.1.2 _ _ _ (issuedPoints₃ _) (linked₃ i))
  have hVC₃ := ZF.v_mem_l (kp_pair_l targetKP₃) ground₃ rankV₃ rankCN₃
    (ZF.v_ordinal_height_l ground₃ rankCN₃ (v_ordinal_l (kp_pair_l targetKP₃) rankV₃) hlC₃)
  have lowPoint (x : P₀.Domain) y (hx : P₀.mem x Wr) (ip : Rd_entry_d x.val y t₃) :
      Rd_entry_d x.val y k₃ :=
    (restrict₃.2 _ _).mpr ⟨(common₃.carrier _).mpr ⟨x.property,
      (ZF.v_unique_l (kp_pair_l native) targetZF rW rankU₃) ▸ hx⟩, ip⟩
  have iQ₃ := lowPoint (ρ₂.bound 12).val (η₃.bound 7).val hQW₂ (points₃ 7)
  have hQC₃ := fs₃.transitive Vn₃ hVC₃ (η₃.bound 7)
    ((common₃.image _).mpr ⟨_, common₃.injection.1.input_mem_of_pairMember iQ₃, iQ₃⟩)
  have eqwT := ft₃.1.1.2 _ wT₃ (η₃.bound 0).val ((restrict₃.2 _ _).mp iwT₃).2 (points₃ 0)
  have realω₃ : P₀₃.IsOmega (η₃.bound 0) :=
    (show (⟨wT₃, numbers₃.member⟩ : P₀₃.Domain) = η₃.bound 0 from Subtype.ext eqwT) ▸
      numbers₃.omega_l I (ZF.modelsKP hZF) tree.omega targetKP₃.1
  have sourceNat₃ : P₀.mem (ψ₃.bound 1).val (ψ₃.bound 0).val := by
    rw [values₃ 1, values₃ 0]
    exact hl₂
  have hn₃ : P₀₃.mem (η₃.bound 1) (η₃.bound 0) :=
    (pred₃ _ _ (replyPoints₃ 0) _).mpr ⟨_, sourceNat₃, replyPoints₃ 1⟩
  have eqw₃ : η₃.bound 0 = (⟨w₃, context₃.omega_mem⟩ : P₀₃.Domain) :=
    (equal₃ 0).symm.trans (Subtype.ext eqω₃)
  -- 回答高度的完整极限性沿原共同图传输，供目标表的合法键构造使用。
  have language₂ := ((Formula.satisfies_conj_iff ..).mp round₂).2
  simp only [tg_witness0_m, tg_round_m, Formula.satisfies_conj_iff] at language₂
  have aboveτ₂ : P₀.mem (ρ₂.bound 39).val (ρ₂.bound 15).val :=
    (Formula.satisfies_mem_iff ..).mp language₂.1
  have language₂ := language₂.2.2.2.2.2.2.2.2.2.1
  let fields₂ : Fin 11 → Term 54 := fun i => [.bound 16,.bound 17,.bound 23,.bound 24,.bound 15,
    .bound 14,.bound 13,.bound 12,.bound 2,.bound 1,.bound 0].get i
  let languageEnv₂ := Definitional.Env.substitute ρ₂ fields₂
  have languageTruth₂ : Formula.satisfies languageEnv₂ tg_reply_language0_m :=
    (Formula.satisfies_bind ρ₂ fields₂ tg_reply_language0_m).mp language₂
  obtain ⟨finiteN₂, limitτ₂, rankA₂, constantsA₂, poolA₂⟩ :=
    tg_reply_domain_read_l targetZF rc fs' nd languageEnv₂ oldω languageTruth₂
  -- 新回答域严格高于重启的旧域，故已实现的 γ 下界随同一原码存入档案。
  have savedLower₂ : It_lower_d I γ₀ P Rₚ (ρ₂.bound 15).val.val := by
    obtain ⟨a,s,layer,lower⟩ := lower_next
    have high : P₀.mem (ρ₂.bound 21).val (ρ₂.bound 15).val :=
      limitτ₂.1.transitive (ρ₂.bound 39).val aboveτ₂ (ρ₂.bound 21).val belowNext
    exact ⟨a,s,layer,fun x hx => limitτ₂.1.transitive (ρ₂.bound 21).val high
      ⟨x,(mp.2.2.2 x a hx).1⟩ (lower x hx)⟩
  have hτU₃ := KP.v_ordinal_subset_l native rankU₃ (ρ₂.bound 15).val hτL₂
  have iτ₃ := lowPoint (ρ₂.bound 15).val (η₃.bound 4).val
    (KP.v_ordinal_subset_l native rW _ hτL₂) (points₃ 4)
  let nu₃ : Nonempty {x : P₀.Domain // P₀.mem x U₃} := ⟨⟨(ρ₂.bound 15).val,hτU₃⟩⟩
  let τsrc : Env (rt_model_l U₃ nu₃) 1 := ⟨fun _ => ⟨(ρ₂.bound 15).val,hτU₃⟩, fun _ => ⟨(ρ₂.bound 15).val,hτU₃⟩⟩
  let τdst : Env P₀₃ 1 := ⟨fun _ => η₃.bound 4, fun _ => η₃.bound 4⟩
  have limitτ₃ := (KP.limit0_sat_l targetKP₃ τdst .newest).mp
    ((rr_native_delta_l I mp.2.1 mp₃.2.1 U₃ (v_transitive_l (kp_pair_l native) rankU₃) nu₃
      common₃.carrier common₃.injection common₃.pred (KP.limit0_m .newest)
      (by simp -implicitDefEqProofs) (KP.limit0_delta_l _) τsrc τdst (fun _ => iτ₃)).mp
        ((KP.limit0_sat_l native _ .newest).mpr limitτ₂))
  obtain ⟨θ₃, valuesθ₃, reflected₃, sameθ₃, belowτ₃, keyTruth₃,
    BQ₃, UQ₃, DQ₃, rq₃, mq₃, bq₃, hq₃, qq₃, table₃, language₃, queries₃⟩ :=
    tg_answer_input_l ground₃ (eqw₃ ▸ realω₃) rankCN₃ limitCN₃ fs₃ nc₃ ι₃ η₃ issued₃
      (Subtype.ext eqω₃) reply₃ equal₃ hQC₃ (eqw₃ ▸ hn₃) limitτ₃
  -- 两侧 Vτ 历史、常量域及完整有限查询池沿同一图识别实际表项。
  let languageEnv₃ : Env (rt_model_l CNn₃ nc₃) 11 :=
    ⟨fun i => [ι₃.bound 0,ι₃.bound 1,ι₃.bound 27,ι₃.bound 28,θ₃.bound 4,
      BQ₃,UQ₃,DQ₃,rq₃,bq₃,hq₃].get i,ι₃.free⟩
  obtain ⟨finiteN₃, _, rankA₃, constantsA₃, poolA₃⟩ :=
    tg_reply_domain_read_l ground₃ rankCN₃ fs₃ nc₃ languageEnv₃ (Subtype.ext eqω₃) language₃
  have pointω₃ : Rd_entry_d w₁ w₃ t₃ :=
    Eq.mp (congrArg (fun x : P₀₃.Domain => Rd_entry_d w₁ x.val t₃) eqw₃) (points₃ 0)
  have pointn₃ : Rd_entry_d (ρ₂.bound 24).val.val (ι₃.bound 28).val.val t₃ :=
    Eq.mp (congrArg (fun x : P₀₃.Domain => Rd_entry_d (ρ₂.bound 24).val.val x.val t₃)
      (equal₃ 2).symm) (points₃ 2)
  have pointτ₃ : Rd_entry_d (ρ₂.bound 15).val.val (θ₃.bound 4).val.val t₃ :=
    Eq.mp (congrArg (fun x : P₀₃.Domain => Rd_entry_d (ρ₂.bound 15).val.val x.val t₃)
      (valuesθ₃ 4).symm) (points₃ 4)
  have pointD₃ : Rd_entry_d (ρ₂.bound 12).val.val (θ₃.bound 7).val.val t₃ :=
    Eq.mp (congrArg (fun x : P₀₃.Domain => Rd_entry_d (ρ₂.bound 12).val.val x.val t₃)
      (valuesθ₃ 7).symm) (points₃ 7)
  have domainEq₃ := tg_reply_domain_raw_l (ZF.modelsKP hZF) mp.2.1 mp₃.2.1 targetZF ground₃
    common₃ B₃ transB₃ bc₃ ft₃ pred₃ restrict₃ endpoint₃ layer₃
    ⟨w₁,record₁.context.omega_mem⟩ (ρ₂.bound 24).val (ρ₂.bound 15).val (ρ₂.bound 14).val
    (ρ₂.bound 13).val (ρ₂.bound 12).val ⟨w₃,context₃.omega_mem⟩ (ι₃.bound 28).val (θ₃.bound 4).val
    (θ₃.bound 7).val BQ₃.val UQ₃.val DQ₃.val
    (targetNumbers.omega_l I (ZF.modelsKP hZF) tree.omega native.1) (eqw₃ ▸ realω₃)
    finiteN₂ readU₃.omega_mem hτL₂ rankA₂ constantsA₂ poolA₂ rankA₃ constantsA₃ poolA₃
    pointω₃ pointn₃ pointτ₃ pointD₃
  -- 同一 γ₀ 低层的高度、整个层对象和内部 ω 均沿实际共同图识别。
  let agn : P₀.Domain := ⟨ag,heightg.member⟩
  let Vgn : P₀.Domain := ⟨Vg,layerg.member⟩
  have rankg := (rr_rank_native_l I mp.2.1 native agn Vgn).mp rg
  have hγU := KP.v_ordinal_subset_l hN rankU aq haℓ
  have iγg := (common.layer_image_l (ZF.modelsKP hZF) mh.2.1 (certificate root).ext
    baseHeight heightg (v_transitive_l (kp_pair_l hN) rankU) hγU).1
  have iVg := (common.layer_image_l (ZF.modelsKP hZF) mh.2.1 (certificate root).ext
    baseLayer layerg (v_transitive_l (kp_pair_l hN) rankU) hVU).1
  let ng : Nonempty {x : N₀.Domain // N₀.mem x U₁} := ⟨⟨aq,hγU⟩⟩
  let γsrc : Env (rt_model_l U₁ ng) 1 := ⟨fun _ => ⟨aq,hγU⟩,fun _ => ⟨aq,hγU⟩⟩
  let γdst : Env P₀ 1 := ⟨fun _ => agn,fun _ => agn⟩
  have limitg := (KP.limit0_sat_l native γdst .newest).mp
    ((rr_native_delta_l I mh.2.1 mp.2.1 U₁ (v_transitive_l (kp_pair_l hN) rankU) ng
      common.carrier common.injection common.pred (KP.limit0_m .newest)
      (by simp -implicitDefEqProofs) (KP.limit0_delta_l _) γsrc γdst (fun _ => iγg)).mp
        ((KP.limit0_sat_l hN _ .newest).mpr baseLimit))
  have iωg : Rd_entry_d w.val w₁ k₁ := ew₁.symm ▸ hww₂
  have hwg : P₀.mem ⟨w₁,record₁.context.omega_mem⟩ Vgn :=
    (common.pred _ _ iVg _).mpr ⟨w.val,baseOmega,iωg⟩
  have agL : P₀.mem agn Lr := ordinal_down_l native limitg.1 (v_ordinal_l (kp_pair_l native) rankU₃)
    (fun x hx => boundg x.val (eqg ▸ hx)) hκL₂
  have hgu : P₀.mem agn U₃ := KP.v_ordinal_subset_l native rankU₃ agn agL
  have hVgu : P₀.mem Vgn U₃ := ZF.v_mem_l (kp_pair_l native) targetZF rankg rankU₃ agL
  have atlas₃ := anchor₃
  obtain ⟨ag₃,Vg₃,sg₃,tg₃,heightg₃,layerg₃,rg₃,fixedg₃⟩ := atlas₃
  let agn₃ : P₀₃.Domain := ⟨ag₃,heightg₃.member⟩
  let Vgn₃ : P₀₃.Domain := ⟨Vg₃,layerg₃.member⟩
  have rankg₃ := (rr_rank_native_l I mp₃.2.1 targetKP₃ agn₃ Vgn₃).mp rg₃
  have iγg₃ := (common₃.layer_image_l (ZF.modelsKP hZF) mp.2.1 (cert₃ root).ext
    heightg heightg₃ (v_transitive_l (kp_pair_l native) rankU₃) hgu).1
  have iVg₃ := (common₃.layer_image_l (ZF.modelsKP hZF) mp.2.1 (cert₃ root).ext
    layerg layerg₃ (v_transitive_l (kp_pair_l native) rankU₃) hVgu).1
  let ng₃ : Nonempty {x : P₀.Domain // P₀.mem x U₃} := ⟨⟨agn,hgu⟩⟩
  let γsrc₃ : Env (rt_model_l U₃ ng₃) 1 := ⟨fun _ => ⟨agn,hgu⟩,fun _ => ⟨agn,hgu⟩⟩
  let γdst₃ : Env P₀₃ 1 := ⟨fun _ => agn₃,fun _ => agn₃⟩
  have limitg₃ := (KP.limit0_sat_l targetKP₃ γdst₃ .newest).mp
    ((rr_native_delta_l I mp.2.1 mp₃.2.1 U₃ (v_transitive_l (kp_pair_l native) rankU₃) ng₃
      common₃.carrier common₃.injection common₃.pred (KP.limit0_m .newest)
      (by simp -implicitDefEqProofs) (KP.limit0_delta_l _) γsrc₃ γdst₃ (fun _ => iγg₃)).mp
        ((KP.limit0_sat_l native _ .newest).mpr limitg))
  have iwk₃ : Rd_entry_d w₁ w₃ k₃ := (restrict₃.2 _ _).mpr
    ⟨(common₃.carrier _).mpr ⟨record₁.context.omega_mem,readU₃.omega_mem⟩,pointω₃⟩
  have hwg₃ : P₀₃.mem ⟨w₃,context₃.omega_mem⟩ Vgn₃ :=
    (common₃.pred _ _ iVg₃ _).mpr ⟨w₁,hwg,iwk₃⟩
  -- 表内查询先回到回答层核验；不要求两张表选取相同的公式码。
  let queriesEnv₃ : Env (rt_model_l CNn₃ nc₃) 12 :=
    ⟨fun i => [ι₃.bound 0,ι₃.bound 1,ι₃.bound 27,ι₃.bound 28,ι₃.bound 26,ι₃.bound 1,ι₃.bound 1,
      rq₃,mq₃,bq₃,hq₃,qq₃].get i,ι₃.free⟩
  let baseFields : Fin 7 → Term 12 := fun i => [.bound 0,.bound 1,.bound 2,.bound 3,.bound 7,.bound 9,.bound 10].get i
  let baseEnv₃ := Definitional.Env.substitute queriesEnv₃ baseFields
  have baseTruth₃ : Formula.satisfies baseEnv₃ tg_reply_base0_m :=
    (Formula.satisfies_bind queriesEnv₃ baseFields tg_reply_base0_m).mp
      ((Formula.satisfies_conj_iff ..).mp ((Formula.satisfies_conj_iff ..).mp queries₃).1).2
  have langFacts₃ := language₃
  simp only [tg_reply_language0_m, Formula.satisfies_conj_iff, Formula.satisfies_mem_iff] at langFacts₃
  have insideg₃ x (hx : P₀₃.mem x ⟨w₃,context₃.omega_mem⟩) :=
    (v_transitive_l (kp_pair_l targetKP₃) rankg₃) _ hwg₃ x hx
  have lowBase₃ : ∀ i : Fin 4, P₀₃.mem (baseEnv₃.bound (i.castAdd 3)).val Vgn₃ :=
    Fin.cases (Eq.mp (congrArg (fun x : P₀₃.Domain => P₀₃.mem x Vgn₃)
      (show (ι₃.bound 0).val = (⟨w₃,context₃.omega_mem⟩ : P₀₃.Domain) from Subtype.ext eqω₃).symm) hwg₃)
      (Fin.cases (insideg₃ _ ((eqw₃ ▸ realω₃).transitive targetKP₃ _ finiteN₃ _ langFacts₃.2.1))
        (Fin.cases (insideg₃ _ ((eqw₃ ▸ realω₃).transitive targetKP₃ _ finiteN₃ _ langFacts₃.2.2.1))
          (Fin.cases (insideg₃ _ finiteN₃) (fun i => Fin.elim0 i))))
  have seedFacts₂ := (Formula.satisfies_rename ..).mp ((Formula.satisfies_conj_iff ..).mp round₂).1
  simp only [tg_seed0_m, tg_seed_m, Formula.satisfies_conj_iff, Formula.satisfies_mem_iff] at seedFacts₂
  have he₂ : P₀.mem (ρ₂.bound 17).val ⟨w₁,record₁.context.omega_mem⟩ := oldω ▸ seedFacts₂.2.2.1
  have scalar (x : P₀.Domain) a b (hx : P₀.mem x ⟨w₁,record₁.context.omega_mem⟩)
      (old : Rd_entry_d a x.val tₛ) (next : Rd_entry_d a b j₃) : Rd_entry_d x.val b t₃ :=
    (commute₃ x x a b (low₂ x hx) (natural₂ x hx) (back x a (low₂ x hx) old)).mpr next
  have iwBase₃ : Rd_entry_d (ρ₂.bound 16).val.val (ι₃.bound 0).val.val t₃ := by
    rw [show (ρ₂.bound 16).val.val = w₁ from congrArg Subtype.val oldω,eqω₃]
    exact pointω₃
  have pointBase₃ : ∀ i : Fin 4, Rd_entry_d (ρ₂.bound ([16,17,23,24].get i)).val.val
      (baseEnv₃.bound (i.castAdd 3)).val.val t₃ :=
    Fin.cases iwBase₃ (Fin.cases (scalar _ _ _ he₂ (request 1) (issuedPoints₃ 1))
      (Fin.cases (scalar _ _ _ hl₂ (request 3) (issuedPoints₃ 27))
        (Fin.cases (scalar _ _ _ hn₂ (request 4) (issuedPoints₃ 28)) (fun i => Fin.elim0 i))))
  have rootC₃ : Rd_entry_d Cᵣ CN₃ q₃ := (rootGraph₃ Cᵣ CN₃).mpr
    ⟨fromRoot.1.1.input_mem_of_pairMember rootCurrent,CN,rootCurrent,iCN₃⟩
  have pointw₃ : Rd_entry_d (ρ₂.bound 11).val.val (θ₃.bound 9).val.val t₃ :=
    Eq.mp (congrArg (fun x : P₀₃.Domain => Rd_entry_d (ρ₂.bound 11).val.val x.val t₃)
      (valuesθ₃ 9).symm) (points₃ 9)
  have members₃ := common₃.reply_members_l hZF tree.omega root.model mp mp₃ rootMap rootMap₃
    (certificate root).ext (cert₃ root).ext nextAnchor anchor₃ layerg layerg₃
    (v_transitive_l (kp_pair_l native) rankU₃) hVgu Cn CNn₃ fs'.transitive nd nc₃ rootC rootC₃
    ground₃ ⟨w₃,context₃.omega_mem⟩ agn₃ (θ₃.bound 9).val (eqw₃ ▸ realω₃) fs₃ rankg₃ limitg₃
    (record₁.context.kernel_l mp.2.1 nd) ρ₂ round₂ baseEnv₃ (Subtype.ext eqω₃) finiteN₃ lowBase₃ baseTruth₃
    ft₃ restrict₃ pred₃ pointBase₃ pointw₃
  -- 当前表的代码已经核验；完整回答因此实际产生事件和每个落子后的下一请求。
  have finiteL₃ : P₀₃.mem (θ₃.bound 1).val ⟨w₃,context₃.omega_mem⟩ :=
    Eq.mp (congrArg (fun x : P₀₃.Domain => P₀₃.mem x ⟨w₃,context₃.omega_mem⟩)
      (valuesθ₃ 1).symm) (eqw₃ ▸ hn₃)
  have tableReply₃ := tg_reply_table_l ground₃ (eqw₃ ▸ realω₃) rankCN₃ limitCN₃ fs₃ nc₃
    θ₃ finiteL₃ reflected₃ rq₃ bq₃ hq₃ members₃.1 members₃.2.1 members₃.2.2
  let answerEnv₃ : Env (rt_model_l CNn₃ nc₃) 22 :=
    ⟨fun i => [ι₃.bound 0,ι₃.bound 27,ι₃.bound 28,ι₃.bound 24,θ₃.bound 4,
      ι₃.bound 30,ι₃.bound 31,DQ₃,ι₃.bound 25,θ₃.bound 9,ι₃.bound 36,ι₃.bound 37,rq₃,bq₃,hq₃,
      ι₃.bound 38,ι₃.bound 39,ι₃.bound 40,ι₃.bound 41,ι₃.bound 42,ι₃.bound 43,ι₃.bound 44].get i,
      fun _ => ι₃.bound 0⟩
  have answerValues₃ : (tg_reply_table_env_d θ₃ rq₃ bq₃ hq₃).bound = answerEnv₃.bound := by
    funext i
    exact Fin.cases (sameθ₃ 0).symm (Fin.cases (sameθ₃ 1).symm (Fin.cases (sameθ₃ 2).symm
      (Fin.cases (sameθ₃ 3).symm (Fin.cases rfl (Fin.cases (sameθ₃ 4).symm
        (Fin.cases (sameθ₃ 5).symm (Fin.cases (Subtype.ext domainEq₃) (Fin.cases (sameθ₃ 6).symm
          (Fin.cases rfl (Fin.cases (sameθ₃ 7).symm (Fin.cases (sameθ₃ 8).symm
            (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases (sameθ₃ 9).symm
              (Fin.cases (sameθ₃ 10).symm (Fin.cases (sameθ₃ 11).symm (Fin.cases (sameθ₃ 12).symm
                (Fin.cases (sameθ₃ 13).symm (Fin.cases (sameθ₃ 14).symm
                  (Fin.cases (sameθ₃ 15).symm (fun j => Fin.elim0 j)))))))))))))))))))))) i
  have answerTruth₃ := (Formula.closed_env_l tg_reply0_m tg_reply0_closed_l
    (ρ := tg_reply_table_env_d θ₃ rq₃ bq₃ hq₃) (η := answerEnv₃) answerValues₃).mp tableReply₃
  let requestEnv₃ : Env (rt_model_l CNn₃ nc₃) 5 :=
    ⟨fun i => [ι₃.bound 0,θ₃.bound 4,ι₃.bound 26,ι₃.bound 1,ι₃.bound 1].get i,fun _ => ι₃.bound 0⟩
  have requestTruth₃ : Formula.satisfies requestEnv₃ tg_query_request0_m :=
    (Formula.closed_env_l tg_query_request0_m tg_query_request0_closed_l
      (ρ := (⟨fun i => [ι₃.bound 0,θ₃.bound 4,ι₃.bound 26,ι₃.bound 1,ι₃.bound 1].get i,
        ι₃.free⟩ : Env (rt_model_l CNn₃ nc₃) 5)) (η := requestEnv₃) rfl).mp keyTruth₃
  -- 实际数字图识别外部轮号；源、目标事件使用各自的原对象码。
  have sameOmega₃ : wT₃ = w₃ := eqwT.trans (congrArg Subtype.val eqw₃)
  have currentNumbers₃ : Rr_layer_d I ω P₃ R₃ w₃ zT₃ :=
    Eq.mp (congrArg (fun a => Rr_layer_d I ω P₃ R₃ a zT₃) sameOmega₃) numbers₃
  have sourceExt := (root.map_l hZF tree.omega mh fromRoot).ext
  have digits₃ := (numbers.omega_map_l I hZF tree.omega mh mp₃ embed₃
    sourceExt (cert₃ root).ext currentNumbers₃).2
  have state₃ := (tg_issued_sat_l (rt_pair_l fs₃.transitive nc₃ targetKP₃.1 fs₃.pair)
    (rt_model_ext_l targetKP₃.1 fs₃.transitive nc₃) ι₃).mp issued₃
  have finiteRound₃ : P₀₃.mem (ι₃.bound 19).val ⟨w₃,context₃.omega_mem⟩ :=
    Eq.mp (congrArg (fun a => Rd_entry_d (ι₃.bound 19).val.val a R₃) eqω₃) state₃.round
  obtain ⟨m₀,index₃⟩ := tg_round_index_l I (ZF.modelsKP hZF) tree.omega mp₃.2.1 targetKP₃.1
    ⟨w₃,context₃.omega_mem⟩ (ι₃.bound 19).val currentNumbers₃ finiteRound₃
  obtain ⟨n₀,_,index₀⟩ := numbers.injection.1.2.2 m₀ index₃.finite
  have sameIndex₃ := embed₃.1.2 n₀ (ι.bound 19).val.val (ι₃.bound 19).val.val
    (digits₃ m₀ n₀ (ι₃.bound 19).val.val index₀ index₃.point) (issuedPoints₃ 19)
  have sourceIndex₃ : Rd_entry_d m₀ (ι.bound 19).val.val zs := sameIndex₃ ▸ index₀
  -- 所有旧事件的像保留同一个外部档案行号，并在后续包含历史中保持。
  have traces₃ := context₃.trace_image_l hZF tree.omega mh mp₃ embed₃ targetKP₃
    sourceExt numbers currentNumbers₃ nc₃
    (ι₃.bound 4) (ι₃.bound 1) (ι₃.bound 2) (ι₃.bound 3) (ι₃.bound 20)
    iw₃ iCN₃ (issuedPoints₃ 4) (issuedPoints₃ 1) (issuedPoints₃ 2) (issuedPoints₃ 3) (issuedPoints₃ 20)
  -- 恢复记录保存的正是当前查询短前缀；低层方块识别它与原边像的对应。
  obtain ⟨s₃,is₃,play₃⟩ := traces₃.2 (ψ.bound 5).val.val query_play₀
  have short_g : P₀.mem (ζ.bound 5).val Vgn :=
    (common.pred _ _ iVg _).mpr ⟨_,queryLow 5,queryImages 5⟩
  have short_k : P₀.mem (ζ.bound 5).val Pκ₃ :=
    (KP.v_compare_l native rankg rankP₃ (fun x hx => boundg x.val (eqg ▸ hx))).1 _ short_g
  have short_eq : (ρ₂.bound 40).val.val = (ζ.bound 5).val.val := congrArg Subtype.val (eqr 8)
  have short_view : Rd_entry_d (ρ₂.bound 40).val.val s₃ k₃ :=
    Eq.mpr (congrArg (fun x => Rd_entry_d x s₃ k₃) short_eq)
      ((lowSquare₃ (ζ.bound 5).val (ψ.bound 5).val.val s₃ short_k
        ((graph₂ _ _).mpr (queryImages 5))).mpr is₃)
  have saved_play : ∃ s, Rd_entry_d (ρ₂.bound 40).val.val s k₃ ∧
      Tg_play_d I P₃ R₃ CN₃ (ι₃.bound 4).val.val (ι₃.bound 3).val.val (ι₃.bound 20).val.val s :=
    ⟨s₃,short_view,play₃ _ (ι₃.bound 20).property (fun _ _ hx => hx)⟩
  have labelsFixed₂ := pj.finite_fixed_l targetZF source₂.omega source₂.transitive pt mx₂ my₂
    source₂.omega_mem hk₂ (source₂.transitive β₂ hβX₃ _ labelLow₂) labels₂
  have labelsPoint₃ : Rd_entry_d (ρ₂.bound 41).val.val (ι₃.bound 23).val.val t₃ :=
    (commute₃ (ρ₂.bound 41).val (ρ₂.bound 41).val _ _ labelLow₂ labelsFixed₂
      (back _ _ labelLow₂ (request 18))).mpr (issuedPoints₃ 23)
  -- 新档案的三个事件坐标落在同一共同图中，下一次 prepare 可直接读取原记录。
  have labelWr₂ := (v_transitive_l (kp_pair_l native) rW) β₂
    (ZF.v_mem_l (kp_pair_l native) targetZF rankβ₂ rW hαLr) (ρ₂.bound 41).val labelLow₂
  have labelView₃ := lowPoint (ρ₂.bound 41).val (ι₃.bound 23).val.val labelWr₂ labelsPoint₃
  obtain ⟨_,savedValues₂,savedCode₂,_,_,_,_,_,savedType₂⟩ := saved₂.read_l I hZF.1
  have sameType₂ : (savedValues₂.bound 11).val.val = (ρ₂.bound 11).val.val :=
    congrFun (savedCode₂.inj_l I hZF.1 code₂) 13
  have typeWr₂ : P₀.mem (ρ₂.bound 11).val Wr :=
    Eq.mp (congrArg (fun x => Rd_entry_d x Wr.val Rₚ) sameType₂) savedType₂
  have typeView₃ := lowPoint (ρ₂.bound 11).val (η₃.bound 9).val typeWr₂ (points₃ 9)
  have domainView₃ : Rd_entry_d (ρ₂.bound 15).val.val (θ₃.bound 4).val.val k₃ :=
    Eq.mp (congrArg (fun x : P₀₃.Domain => Rd_entry_d (ρ₂.bound 15).val.val x.val k₃)
      (valuesθ₃ 4).symm) iτ₃
  have typeView₃ : Rd_entry_d (ρ₂.bound 11).val.val (θ₃.bound 9).val.val k₃ :=
    Eq.mp (congrArg (fun x : P₀₃.Domain => Rd_entry_d (ρ₂.bound 11).val.val x.val k₃)
      (valuesθ₃ 9).symm) typeView₃
  obtain ⟨_, _, _, extend₃⟩ := build₃.2 root
  have origin₃ := (extension.2.2.2.1 o₀ n qN hm.predecessor_mem).mpr current_origin
  obtain ⟨θ₂, T₂, Q₂, G₂, E₂, tree₂, extension₂, node₃, edge₃, move₃, root₃, critical₃⟩ :=
    extend₃ θ m T₁ Q₁ G₁ E₁ n o₀ next extension.1 node (extension.2.2.1 n b hb) origin₃
  obtain ⟨Λ₂, lf₂, levels₂, entries₂, hist₂⟩ :=
    result.original_extend_l hZF next extension.1 lf₁ levels₁ tree₂ extension₂ move₃ payload₃
  -- 新原边继续使用刚才选出的完整池；两张实际工作图在原共同秩段上交换。
  obtain ⟨W₀, hWB, hWC, rWB, rWC, _, iV⟩ := adjacent.work
  obtain ⟨κw₃, _, iκw₃⟩ := copy.1.1.2.2 (ρ₂.bound 21).val.val (ρ₂.bound 21).val.property
  obtain ⟨Lw₃, _, iLw₃⟩ := copy.1.1.2.2 Lr.val Lr.property
  obtain ⟨Fw₃, _, iFw₃⟩ := copy.1.1.2.2 F₂.val F₂.property
  have parent₃ : Ic_at_d H₁ n N B σ u U β := by
    obtain ⟨r, ⟨p, pair, hp⟩, cell⟩ := an
    exact ⟨r, ⟨p, pair, rows p hp⟩, cell⟩
  have bound₃ := result.bound_extend_l hZF next tree₂ extension₂ extension.1.predecessor_mem bnd
  have parent_node := extension.2.2.1 n b hb
  have hnθ := (next.diagram.model_domain n).mpr ⟨b, parent_node⟩
  have oldOrder₃ i : Rd_entry_d i n T₂ ↔ Rd_entry_d i n T₁ :=
    (extension₂.2.1 i n).trans ⟨fun h => h.elim id (fun e => (ir θ (e.1 ▸ hnθ)).elim), Or.inl⟩
  have predecessor₃ : It_pred_d T₂ n θ := by
    refine ⟨hnθ, fun i => (extension₂.2.1 i θ).trans ?_⟩
    exact ⟨fun h => h.elim (fun h => (ir θ (next.diagram.order.bound i θ h).2).elim)
      (fun h => h.2.imp_right (oldOrder₃ i).mpr),
      fun h => Or.inr ⟨rfl, h.imp_right (oldOrder₃ i).mp⟩⟩
  obtain ⟨m', succ_m, hm'⟩ := tree.omega.1.2 n hn
  have hmω : M.mem m ω := (hm.eq hZF.1 succ_m).symm ▸ hm'
  obtain ⟨Y₃, v₃, C₃, γ₃, τ₃, r₃, H₂, ST₂, QT₂, GT₂, succ₃, result₃, rows₃, codes₃, maps₃,
    last₃, bound₄, adjacent₃⟩ := hist₂.copy_step_l hZFC mh mp native
      ⟨w₁, record₁.context.omega_mem⟩ (ρ₂.bound 21).val Lr F₂ X₂ (ρ₂.bound 18).val K₂ R₂ Vn β₂ A₃ Q₃ B₃ e₃
      targetNumbers source₂ rank₂ height₂ loc₂
      (it_owner_l I mp native ⟨w₁,record₁.context.omega_mem⟩ (ρ₂.bound 21).val Lr F₂
        (ρ₂.bound 18).val X₂ K₂ R₂ targetNumbers rank₂ height₂ source₂ loc₂ card₂ strong₂)
      iκw₃ iLw₃ iFw₃ finite₃ closed₃ carrier₂
      iV hWB rWB rWC adjacent.limit agreement₃ square₂ image_back source_small
      hβV₃ hβX₃ transβ₃ products₃ pool₃ dc₃ bc₃ (fn0_of_function_l (ZF.modelsKP hZF) ft₃.1)
      present₃ prepare₃ length₃ raw₃ diagram₃ limit₃ mp₃
      (fn0_of_function_l (ZF.modelsKP hZF) embed₃.1.1) constants₃ common₃ restrict₃ endpoint₃ layer₃
      tree₂ hmω extension.1 predecessor₃ (extension₂.2.2.1 n b parent_node) (extension₂.2.2.1 m d node)
      node₃ edge₃ move₃ payload₃ ((entries₂ m Lr.val).mpr (Or.inr ⟨rfl, rfl⟩)) lf₂ parent₃ last bound₃ above₂
  have eq := succ₃.eq hZF.1 extension₂.1
  subst r₃
  -- 旧档案的当前端点低于候选时，两次共同层复合与同一原边逐点相同。
  have archives₃ := adjacent.archive_image_l hZF adjacent₃ tree.omega mh mp mp₃ mb mc map copy
    native ground₃.1 (ρ₂.bound 21).val Pκ₃ rankP₃ point high hκL₂ graph₂ lowSquare₃
  -- 两份原生 V_L 相同，故新档案所存秩段就是本次复制共同图的源秩段。
  have eqW : U₃.val = Wr.val := congrArg Subtype.val (ZF.v_unique_l (kp_pair_l native) targetZF rankU₃ rW)
  have commonSaved := adjacent₃
  rw [eqW] at commonSaved
  -- 原档案的树结点、根图及工作复制行在两次延伸后共同保留。
  let oldFrame : Tg_archive_frame_d M.Domain := ⟨o₀,n,Q,G,Λ,H⟩
  let newFrame : Tg_archive_frame_d M.Domain := ⟨o₀,θ,Q₂,G₂,Λ₂,H₂⟩
  let archiveRow : Tg_archive_row_d M.Domain := ⟨m,d,P,Rₚ,w₁,η₁,C₁,Lr.val,Wr.val,qr,q',C,τ⟩
  have oldLinks (D : M.Domain) (old : Tg_archive_links_d I oldFrame D) :
      Tg_archive_links_d I newFrame D := by
    apply old.extend_l I
    · intro i hi
      exact (extension.1 i).mpr (Or.inl ((hm i).mpr (Or.inl hi)))
    · intro i c hc
      exact extension₂.2.2.1 i c (extension.2.2.1 i c hc)
    · intro i p hi hp
      have him := (hm i).mpr (Or.inl hi)
      have hiθ := (extension.1 i).mpr (Or.inl him)
      exact (extension₂.2.2.2.1 o₀ i p hiθ).mpr ((extension.2.2.2.1 o₀ i p him).mpr hp)
    · intro i L hL
      exact (entries₂ i L).mpr (Or.inl ((entries i L).mpr (Or.inl hL)))
    · exact fun x hx => rows₃ x (rows x hx)
  have newLink : archiveRow.link_d newFrame := by
    refine ⟨extension.1.predecessor_mem,extension₂.2.2.1 m d node,
      (extension₂.2.2.2.1 o₀ m q' extension.1.predecessor_mem).mpr rootEdge,
      (entries₂ m Lr.val).mpr (Or.inr ⟨rfl,rfl⟩),?_⟩
    obtain ⟨r,⟨p,pair,hp⟩,cell⟩ := last
    exact ⟨v,Y,γ,r,⟨p,pair,rows₃ p hp⟩,cell⟩
  have archiveMove := traces₃.archive_l (ZF.modelsKP hZF) archives₃
  have columns := archiveMove.columns_l I hZF.1 ω γ₀ Bγ Cᵣ oldFrame mh hN an hb
    (ρ.bound 8).val (lim.1.mem high).transitive
  -- 原根锚点及原生 γ 基底随本次新奇数存档保存，供下一次准备直接读取。
  have archiveRoot : Tg_basis_d I γ₀ Bγ Cᵣ archiveRow.w archiveRow.X archiveRow.R archiveRow.C archiveRow.p := by
    refine ⟨rootC,ag,Vg,sg,tg,heightg,layerg,rg,?_,hwg,fixedg⟩
    exact (rr_truth_native_l I mp.2.1 (Formula.isLimitOrdinal .newest)
      (by simp -implicitDefEqProofs) (fun _ : Fin 1 => agn)).mpr
        ((Formula.satisfies_isLimitOrdinal_iff ..).mpr limitg)
  have targetBasis : Tg_basis_d I γ₀ Bγ Cᵣ w₃ P₃ R₃ CN₃ q₃ := by
    refine ⟨rootC₃,ag₃,Vg₃,sg₃,tg₃,heightg₃,layerg₃,rg₃,?_,hwg₃,fixedg₃⟩
    exact (rr_truth_native_l I mp₃.2.1 (Formula.isLimitOrdinal .newest)
      (by simp -implicitDefEqProofs) (fun _ : Fin 1 => agn₃)).mpr
        ((Formula.satisfies_isLimitOrdinal_iff ..).mpr limitg₃)
  have targetLower : It_lower_d I γ₀ P₃ R₃ (ι₃.bound 24).val.val := by
    obtain ⟨a,s,layer,down⟩ := (lowerImages₃ γ₀ lower_next).2.1
    have high : P₀₃.mem ⟨κ₀₃,common₃.injection.1.output_mem_of_pairMember iκ₀₃⟩ (ι₃.bound 24).val :=
      Eq.mp (congrArg (fun b => Rd_entry_d κ₀₃ b R₃) eqκ) memκ₃
    exact ⟨a,s,layer,fun x hx => (regularδ₃.isCardinal.1.mem boundδ₃).transitive
      ⟨κ₀₃,common₃.injection.1.output_mem_of_pairMember iκ₀₃⟩ high ⟨x,(mp₃.2.2.2 x a hx).1⟩ (down x hx)⟩
  have priorRoot := (extension₂.2.2.2.1 o₀ n qN hnθ).mpr origin₃
  have rootComp := tree₂.diagram.comp o₀ n θ qN j₃ q₃ priorRoot edge₃ root₃
  have targetTree := rootComp S₀ (ι.bound 7).val.val (ι₃.bound 7).val.val treeName (issuedPoints₃ 7)
  have archiveName : Tg_saved_name_d I S₀ archiveRow.X archiveRow.R archiveRow.w archiveRow.U archiveRow.q archiveRow.p :=
    Tg_saved_name_d.of_code_l I hZF.1 code₂ oldTree
  have answered₃ := context₃.answer_native_l hZF mp₃.2.1 targetKP₃ nc₃ ι₃ issued₃ eqω₃ ω zT₃ m₀ index₃
    ln₃ (v_ordinal_l (kp_pair_l targetKP₃) rankV₃) candidateBound₃
    (θ₃.bound 4) (θ₃.bound 9) BQ₃ UQ₃ DQ₃ rq₃ mq₃ bq₃ hq₃ qq₃
    belowτ₃ requestTruth₃ table₃ answerTruth₃ γ₀ Bγ Cᵣ S₀ C₃ τ₃ k₃ q₃ rootMap₃.1.1.1
    (targetBasis.anchor_l I) targetTree archiveRow newFrame targetLower root₃ newLink archiveName
    mp saved₂ ⟨_,targetNumbers⟩ archiveRoot ⟨_,_,_,_,commonSaved⟩
    (fun i => (ρ₂.bound i).val.val) code₂ savedLower₂ labelView₃ domainView₃ typeView₃ saved_play
  have ready₃ : Tg_answer_step_d I d₃ P₃ R₃ t₃ k₃ j₃ qN l₃ w.val ηN CN N Rₕ (ρ₂.bound 41).val.val
      B σ C₃ τ₃ (ρ.bound 8).val.val ω zs γ₀ Bγ Cᵣ S₀ ⟨m,d,P,Rₚ,w₁,η₁,C₁,Lr.val,Wr.val,qr,q',C,τ⟩
      oldFrame newFrame
      (fun i => (ι.bound i).val.val) (fun i => (vals i).val) :=
    ⟨newLink,oldLinks,mp₃,(cert₃ root).ext,w₃,ηN₃,CN₃,iw₃,iηN₃,iCN₃,context₃,q₃,root₃,
      rootMap₃.1.1.1,rootMap₃.1.2,targetBasis,nc₃,ι₃,θ₃,
      issuedPoints₃,rootComp,issued₃,eqω₃,targetLower,lowδ₃,hlC₃,
      fun i => Eq.mp (congrArg (fun x : P₀₃.Domain => Rd_entry_d (vals i).val x.val t₃)
        (valuesθ₃ i).symm) (points₃ i), reflected₃, labelsPoint₃, labelView₃,
      domainView₃,typeView₃,sameθ₃,belowτ₃,keyTruth₃,
      BQ₃, UQ₃, DQ₃, rq₃, mq₃, bq₃, hq₃, qq₃, Subtype.ext domainEq₃.symm, table₃,
      members₃.1,members₃.2.1,members₃.2.2,language₃,queries₃,
      zT₃,m₀,numbers,sourceIndex₃,index₃,
      (fun k L s hL hk prior => prior.map_l hZF tree.omega mh mp₃ embed₃ sourceExt (cert₃ root).ext
        numbers index₃.numbers (fun x hx => by
          obtain ⟨_,_,_,t,_,layer,_,fixed⟩ := baseCurrent
          obtain ⟨y,hy,point⟩ := layer.injection.1.2.2 x (layer.transitive L hL x hx)
          exact ⟨y,hy,fixed x y point⟩) hk rootMap₃.1.1.1 rootComp
        iCN₃ (issuedPoints₃ 4) (issuedPoints₃ 3) (issuedPoints₃ 20)),
      (fun u i => index₃.even_l hZF ground₃ fs₃ nc₃
        (tg_position_env_d ⟨fun k => ι₃.bound (k.castAdd 27),fun _ => ι₃.bound 0⟩ (ι₃.bound 19) u i)
        (.bound 0) (.bound 19) (Subtype.ext eqω₃) rfl),
      answered₃,traces₃,archiveMove,
      fun H b bound below links views => columns H b bound below links views
        (ι₃.bound 20).val.val (ι₃.bound 20).property (fun _ _ hx => hx)⟩
  exact ⟨θ, T₁, Q₁, G₁, E₁, Λ₁, H₁, ST₁, QT₁, GT₁, Y, v, C, γ, τ, l, κ', w₁, η₁, C₁, δ₁, r₁,
    saved, certificate root, next, extension, lf₁, levels₁, entries, node, edge, rootEdge, rootMap,
    result, rows, codes, maps, last, bnd, hbκ, hκ', ord₁, boundκ,
    iw, iη, iC, iδ, ir₁, record₁, hκδ, hχδ, hχC, regular, critical,
    Lw, U₁.val, V₂, Γ₁, k₁, adjacent, restrict, presentₛ,
    mp, record₁.context, nd, ε, images, fun i => ((restrict.2 _ _).mp (images i)).2, ew, truth,
    nextAnchor, ψ, ζ, queries, queryTruth, queryCoords, queryImages,
    fun i => ((restrict.2 _ _).mp (queryImages i)).2, qw, qnode, qmax,
    W, ν, pool, below, realized, εr, eqr, recovered, ρₛ, fun _ => rfl, oldRound,
    πp, fun i => congrArg Subtype.val (eqp i), v₂, seed₂, a₂, round₂, request,
    Lr, Wr, qr, saved₂, code₂, restart_link, above₂, X₂, K₂, R₂, F₂, c₂, d₂, Y₂, S₂, j₂, κ₂, U₂, D₂, u₂, image₂,
    α₂, β₂, hα₂, hβ₂, hκ₂, limitα₂, rankβ₂,
    Γ₂, k₂, z₁, targetNumbers, carrier₂, fk₂, image_back, pred₂, graph₂, square₂,
    Ls₂, Js₂, Os₂, Zs₂, Ds₂, ps₂, Vs₂, Ws₂, qs₂, d₃, P₃, R₃, j₃, q₃, p₃, fixed₂,
    cert₃ root, embed₃, rootMap₃, anchor₃, θ₂, T₂, Q₂, G₂, E₂, Λ₂, tree₂, extension₂, node₃, edge₃, root₃,
    move₃, payload₃, lower_next, fun h => critical₃ γ₀ lower_next (critical γ₀ source_lower h),
    lf₂, levels₂, entries₂, A₃, Q₃, B₃, e₃, Dp₃, Bp₃, t₃, pool₃, dc₃, bc₃, ft₃, present₃,
    Y₃, v₃, C₃, γ₃, τ₃, H₂, ST₂, QT₂, GT₂, l₃, U₃.val, V₃, Γ₃, k₃, Lw₃,
    result₃, rows₃, codes₃, maps₃, last₃, bound₄, adjacent₃, restrict₃,
    ready₃⟩

end YesMetaZFC.SetTheory.LargeCardinal
