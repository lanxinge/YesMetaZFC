import YesMetaZFC.SetTheory.LargeCardinal.Iteration.CopyRoundSyntax
import YesMetaZFC.SetTheory.LargeCardinal.Iteration.FrameUnion
import YesMetaZFC.SetTheory.LargeCardinal.Game.AnswerNativeInput
import YesMetaZFC.SetTheory.LargeCardinal.Game.RawReply
import YesMetaZFC.SetTheory.LargeCardinal.Game.SavedNative
import YesMetaZFC.SetTheory.LargeCardinal.Game.Restart
import YesMetaZFC.SetTheory.LargeCardinal.Extender.RawAlphabet
import YesMetaZFC.SetTheory.LargeCardinal.Game.RawContinueRenewal
import YesMetaZFC.SetTheory.LargeCardinal.Game.ReplyPool
import YesMetaZFC.SetTheory.LargeCardinal.Game.RestartLinkSyntax

/-! # 原树实际延长时保留整份旧复制历史

只在末行追加本次实际支撑。已有前驱区间和已完成边均严格早于该末行，
所以原树延长后仍使用同一份工作历史；不提前要求尚未实施的支撑有序。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

/-- 原图在已实施区间精确保持时，整份复制历史改读同一新原图。 -/
theorem Ic_history_d.original_prefix_l
    {ω n m T Q G E L H S Qw Gw T₁ Q₁ G₁ E₁ L₁ : M.Domain}
    (hist : Ic_history_d hZF ω T Q G E L m H S Qw Gw) (hm : M.SuccessorOf m n)
    (old_order : ∀ i j, M.mem j m → (Rd_entry_d i j T₁ ↔ Rd_entry_d i j T))
    (codes : ∀ i c, M.mem i m → Rd_entry_d i c Q → Rd_entry_d i c Q₁)
    (maps : ∀ i j f, M.mem j m → It_map_d G₁ i j f → It_map_d G i j f)
    (moves : ∀ i p, M.mem i n → Rd_entry_d i p E₁ → Rd_entry_d i p E)
    (old_level : ∀ i ρ, M.mem i n → (Rd_entry_d i ρ L₁ ↔ Rd_entry_d i ρ L)) :
    Ic_history_d hZF ω T₁ Q₁ G₁ E₁ L₁ m H S Qw Gw := by
  have mo := hist.diagram.order.ordinal
  have no := mo.mem hm.predecessor_mem
  have prior {i j} (hj : M.mem j m) (hij : M.mem i j) : M.mem i n := by
    rcases (hm j).mp hj with hjn | eq
    · exact no.transitive j hjn i hij
    · exact hZF.1.eq_of_same_members j n eq ▸ hij
  have index {i X A π z Z α} (ai : Ic_at_d H i X A π z Z α) : M.mem i m :=
    (hist.domain i).mpr (ai.imp fun _ h => h.1)
  refine ⟨hist.diagram,?_,hist.function,hist.domain,?_,?_,hist.cuts,?_,?_,?_,?_⟩
  · intro i j
    exact (hist.order i j).trans ⟨fun ⟨h,hj⟩ => ⟨(old_order i j hj).mpr h,hj⟩,
      fun ⟨h,hj⟩ => ⟨(old_order i j hj).mp h,hj⟩⟩
  · intro i r hr
    obtain ⟨a,X,A,π,z,Z,α,cell,ha,hz,row⟩ := hist.rows i r hr
    exact ⟨a,X,A,π,z,Z,α,cell,codes i a ((hist.domain i).mpr ⟨r,hr⟩) ha,hz,row⟩
  · intro i j X A π z Z α Y B σ u U β ai aj hij
    have hin := prior (index aj) hij
    rcases hist.past i j X A π z Z α Y B σ u U β ai aj hij with
        ⟨a,hi,hj,ex,ea,ep,inactive⟩ |
        ⟨r,ρ,t,φ,V,W,D,f,a,b,R,T,hir,hrj,hρ,first,hi,hj,mx,my,same⟩
    · exact Or.inl ⟨a,codes i a (index ai) hi,codes j a (index aj) hj,ex,ea,ep,
        fun ρ hρ => inactive ρ ((old_level i ρ hin).mp hρ)⟩
    · exact Or.inr ⟨r,ρ,t,φ,V,W,D,f,a,b,R,T,hir,hrj,
        (old_level r ρ (prior (index aj) hrj)).mpr hρ,
        fun ν hν => first ν ((old_level i ν hin).mp hν),codes i a (index ai) hi,codes j b (index aj) hj,mx,my,same⟩
  · intro i j X A π z Z α Y B σ u U β f g ai aj hf hg
    exact hist.squares i j X A π z Z α Y B σ u U β f g ai aj (maps i j f (index aj) hf) hg
  · intro i j r X B σ u U β Y A π z Z α P C τ v V γ p κ ρ F f succ pred ai ar aj hp pay hf
    have hj := index aj
    have hr := mo.transitive j hj r pred.1
    have pred₀ : It_pred_d T r j := ⟨pred.1,fun i =>
      (old_order i j hj).symm.trans ((pred.2 i).trans (or_congr Iff.rfl (old_order i r hr)))⟩
    have hin := prior hj succ.predecessor_mem
    exact hist.steps i j r X B σ u U β Y A π z Z α P C τ v V γ p κ ρ F f succ pred₀ ai ar aj
      (moves i p hin hp) pay hf
  · intro i j p succ hj hp empty
    have hin := prior hj succ.predecessor_mem
    exact hist.pads i j p succ hj (moves i p hin hp) empty
  · intro i j r X A π z Z α Y B σ u U β ρ ψ a b ai aj succ hr hρ hψ ha hb hij
    have hjn := prior hr succ.predecessor_mem
    exact hist.increasing i j r X A π z Z α Y B σ u U β ρ ψ a b ai aj succ hr
      ((old_level i ρ (no.transitive j hjn i hij)).mp hρ) ((old_level j ψ hjn).mp hψ) ha hb hij

/-- 本次真实原树边及其支撑进入原图；旧复制行与全部旧前驱条件同步保留。 -/
theorem Ic_history_d.original_extend_l
    {ω c n m T Q G E L H S Qw Gw k l T₁ Q₁ G₁ E₁ p κ μ F : M.Domain}
    (tree : It_tree_d hZF ω c m T Q G E)
    (hist : Ic_history_d hZF ω T Q G E L m H S Qw Gw)
    (hm : M.SuccessorOf m n) (lf : M.IsSetFunction I L)
    (levels : ∀ i ρ, Rd_entry_d i ρ L ↔ ∃ p κ F, Rd_entry_d i p E ∧ It_payload_d p κ ρ F)
    (next : It_tree_d hZF ω c l T₁ Q₁ G₁ E₁)
    (extension : It_extension_d m n k T Q G E l T₁ Q₁ G₁ E₁)
    (move : Rd_entry_d n p E₁) (payload : It_payload_d p κ μ F) :
    ∃ L₁, M.IsSetFunction I L₁ ∧
      (∀ i ρ, Rd_entry_d i ρ L₁ ↔ ∃ p κ F, Rd_entry_d i p E₁ ∧ It_payload_d p κ ρ F) ∧
      (∀ i ρ, Rd_entry_d i ρ L₁ ↔ Rd_entry_d i ρ L ∨ i = n ∧ ρ = μ) ∧
      Ic_history_d hZF ω T₁ Q₁ G₁ E₁ L₁ m H S Qw Gw := by
  have ir := KP.mem_irrefl_d (ZF.modelsKP hZF)
  obtain ⟨L₁,fn,lv,entries⟩ := tree.levels_extend_l hZF hm lf levels next extension move payload
  have oldMoves := extension.2.2.2.2.2
  have oldLevel i ρ (hi : M.mem i n) : Rd_entry_d i ρ L₁ ↔ Rd_entry_d i ρ L :=
    (entries i ρ).trans ⟨fun h => h.elim id (fun e => (ir n (e.1 ▸ hi)).elim), Or.inl⟩
  have order i j (hj : M.mem j m) : Rd_entry_d i j T₁ ↔ Rd_entry_d i j T :=
    (extension.2.1 i j).trans ⟨fun h => h.elim id (fun e => (ir m (e.1 ▸ hj)).elim),Or.inl⟩
  exact ⟨L₁,fn,lv,entries,hist.original_prefix_l hZF hm order
    (fun i a _ => extension.2.2.1 i a)
    (fun i j f hj => (extension.2.2.2.1 i j f hj).mp)
    (fun i p hi => (oldMoves i p (fun eq => ir n (eq ▸ hi))).mp) oldLevel⟩

/-- 原模型列只追加末项时，既有行的共同端点及其高度界保持不变。 -/
theorem Ic_history_d.bound_extend_l
    {ω c m θ T Q G E Λ H S Qw Gw i k T₁ Q₁ G₁ E₁ n N R σ χ : M.Domain}
    (tree : It_tree_d hZF ω c m T Q G E)
    (hist : Ic_history_d hZF ω T Q G E Λ m H S Qw Gw)
    (next : It_tree_d hZF ω c θ T₁ Q₁ G₁ E₁)
    (extension : It_extension_d m i k T Q G E θ T₁ Q₁ G₁ E₁) (hn : M.mem n m)
    (bound : Ic_bound_d I H Q N R σ n χ) : Ic_bound_d I H Q₁ N R σ n χ := by
  have codes j a (hj : M.mem j m) : Rd_entry_d j a Q₁ ↔ Rd_entry_d j a Q := by
    obtain ⟨b, hb⟩ := (tree.diagram.model_domain j).mp hj
    exact ⟨fun ha => (next.diagram.model_function.2 j a b ha (extension.2.2.1 j b hb)).symm ▸ hb,
      extension.2.2.1 j a⟩
  have heights j (hj : M.mem j n) μ :
      Ic_height_d I H Q₁ N R σ n j μ ↔ Ic_height_d I H Q N R σ n j μ := by
    refine and_congr_right fun _ => ?_
    refine exists_congr fun X => exists_congr fun A => exists_congr fun π =>
      exists_congr fun z => exists_congr fun Z => exists_congr fun α =>
      exists_congr fun B => exists_congr fun u => exists_congr fun U => exists_congr fun β =>
      exists_congr fun c => exists_congr fun d => exists_congr fun R => exists_congr fun L =>
      exists_congr fun φ => exists_congr fun V => exists_congr fun W => exists_congr fun D => exists_congr fun t => ?_
    exact and_congr_right fun _ => and_congr_right fun _ =>
      and_congr (codes j c (hist.diagram.order.ordinal.transitive n hn j hj))
        (and_congr (codes n d hn) Iff.rfl)
  refine ⟨bound.ordinal, ?_, fun j μ hj h => bound.upper j μ hj ((heights j hj μ).mp h)⟩
  rcases bound.origin with empty | ⟨j, hj, h⟩
  · exact Or.inl empty
  · exact Or.inr ⟨j, hj, (heights j hj χ).mpr h⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 同一次继续与回答的完整两步复制结果

固定原工厂的全部对象、两次树延伸、共同图、存档及实际回答一起保留。
原两步定理直接返回此命题，准备入口使用同一结果，避免重复展开长结论。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

def Ic_two_step_d
    (ω c₀ Xᵣ Rᵣ c X Rₓ b N Rₕ q Γ ks zs n m T Q G E Λ H QT GT k o₀ B σ
      wₚ ηₚ Cₚ κp δₚ rₚ Ls Js Os Zs Ds ps Vs Ws qs d P Rₚ j₀ q' p qN Cᵣ S₀ ηN CN γ₀ Bγ Dₛ tₛ
      wₛ ηₛ Cₛ : M.Domain)
    (mh : Smdl_d I b N Rₕ) (hN : (smdl_structure_l I (R := Rₕ) mh.2.1).Models KP)
    (U₀ w ξ ℓ e β₀ X₀ K₀ jN eₛ : (smdl_structure_l I (R := Rₕ) mh.2.1).Domain)
    (hω : M.IsOmega ω) (context : Tg_context_d I w.val N Rₕ ηN CN)
    (nc : Nonempty {x : (smdl_structure_l I (R := Rₕ) mh.2.1).Domain //
      (smdl_structure_l I (R := Rₕ) mh.2.1).mem x ⟨CN, context.member⟩})
    (ρ : Env (rt_model_l (M := smdl_structure_l I (R := Rₕ) mh.2.1) ⟨CN, context.member⟩ nc) 29)
    (ι : Env (rt_model_l (M := smdl_structure_l I (R := Rₕ) mh.2.1) ⟨CN, context.member⟩ nc) 46)
    (restored : Tg_context_d I wₛ P Rₚ ηₛ Cₛ)
    (ncₛ : Nonempty {x : (smdl_structure_l I (R := Rₚ) ⟨wₛ, restored.omega_mem⟩).Domain //
      (smdl_structure_l I (R := Rₚ) ⟨wₛ, restored.omega_mem⟩).mem x ⟨Cₛ, restored.member⟩})
    (ρₛ : Env (rt_model_l (M := smdl_structure_l I (R := Rₚ) ⟨wₛ, restored.omega_mem⟩)
      ⟨Cₛ, restored.member⟩ ncₛ) 54)
    (θₛ : Env (rt_model_l (M := smdl_structure_l I (R := Rₚ) ⟨wₛ, restored.omega_mem⟩)
      ⟨Cₛ, restored.member⟩ ncₛ) 17) : Prop :=
    ∃ θ T₁ Q₁ G₁ E₁ Λ₁ H₁ ST₁ QT₁ GT₁ Y v C γ τ χ₁ κt w₁ η₁ C₁ δ₁ r₁,
      Er_rank_cut_at_d hZF ω c₀ Xᵣ Rᵣ c X Rₓ q Γ ks N Rₕ zs b mh.2.1 hN U₀ w ξ ℓ e β₀ X₀ K₀ jN
        Ls Js Os Zs Ds ps Vs Ws qs d P Rₚ j₀ q' p ∧
      ∃ rootNext : Zc_model_d I ω d P Rₚ, It_tree_d hZF ω c₀ θ T₁ Q₁ G₁ E₁ ∧
      It_extension_d m n k T Q G E θ T₁ Q₁ G₁ E₁ ∧ M.IsSetFunction I Λ₁ ∧
      (∀ i ρ, Rd_entry_d i ρ Λ₁ ↔ ∃ p κ F, Rd_entry_d i p E₁ ∧ It_payload_d p κ ρ F) ∧
      (∀ i ρ, Rd_entry_d i ρ Λ₁ ↔ Rd_entry_d i ρ Λ ∨ i = n ∧ ρ = ℓ.val) ∧
      Rd_entry_d m d Q₁ ∧ It_map_d G₁ k m j₀ ∧ It_map_d G₁ o₀ m q' ∧ Smap_d I ω c₀ d Xᵣ P q' ∧
      Ic_history_d hZF ω T₁ Q₁ G₁ E₁ Λ₁ θ H₁ ST₁ QT₁ GT₁ ∧
      M.MemberSubset H H₁ ∧ M.MemberSubset QT QT₁ ∧ M.MemberSubset GT GT₁ ∧ Ic_at_d H₁ m P C τ v Y γ ∧
      Ic_bound_d I H₁ Q₁ P Rₚ τ m χ₁ ∧ Rd_entry_d ξ.val κp ks ∧ Rd_entry_d κp κt j₀ ∧
      Rr_truth_d I P Rₚ (KP.ord0_m .newest) (fun _ : Fin 1 => κt) ∧
      (∀ x, Rd_entry_d x χ₁ Rₚ → Rd_entry_d x κt Rₚ) ∧
      Rd_entry_d wₚ w₁ j₀ ∧ Rd_entry_d ηₚ η₁ j₀ ∧ Rd_entry_d Cₚ C₁ j₀ ∧
      Rd_entry_d δₚ δ₁ j₀ ∧ Rd_entry_d rₚ r₁ j₀ ∧ Tg_record_d I w₁ P Rₚ η₁ C₁ κt δ₁ r₁ ∧
      Rd_entry_d κt δ₁ Rₚ ∧ Rd_entry_d χ₁ δ₁ Rₚ ∧
      Rd_entry_d χ₁ C₁ Rₚ ∧
      Rr_truth_d I P Rₚ (Formula.isRegularCardinal kpair_convention_l .newest) (fun _ : Fin 1 => δ₁) ∧
      (∀ γ, It_lower_d I γ N Rₕ ξ.val → It_critical_bound_d I γ Q E → It_critical_bound_d I γ Q₁ E₁) ∧
      ∃ φ U₁ V₂ D₁ k₁,
      ∃ adjacent : Ic_agree_d I N Rₕ B σ P Rₚ C τ ℓ.val χ₁ φ U₁ V₂ D₁ k₁,
        M.IsRestrictionOf I k₁ tₛ D₁ ∧ Er_present_d I ω Ls N Rₕ zs Γ X ks qs eₛ.val Dₛ tₛ ∧
      ∃ target : Smdl_d I d P Rₚ, ∃ current : Tg_context_d I w₁ P Rₚ η₁ C₁,
      ∃ nd : Nonempty {x : (smdl_structure_l I (R := Rₚ) target.2.1).Domain //
        (smdl_structure_l I (R := Rₚ) target.2.1).mem x ⟨C₁, current.member⟩},
      ∃ ε : Env (rt_model_l (M := smdl_structure_l I (R := Rₚ) target.2.1) ⟨C₁, current.member⟩ nd) 12,
        (∀ i : Fin 12, Rd_entry_d (ι.bound ([25,28,0,24,27,29,30,31,32,33,34,35].get i)).val.val
          (ε.bound i).val.val k₁) ∧
        (∀ i : Fin 12, Rd_entry_d (ι.bound ([25,28,0,24,27,29,30,31,32,33,34,35].get i)).val.val
          (ε.bound i).val.val tₛ) ∧
        (ε.bound 2).val.val = w₁ ∧ Formula.satisfies ε tg_candidate0_m ∧
        Tg_anchor_d I γ₀ Bγ P Rₚ q' ∧
      ∃ ψ : Env (rt_model_l (M := smdl_structure_l I (R := Rₕ) mh.2.1) ⟨CN, context.member⟩ nc) 12,
      ∃ ζ : Env (rt_model_l (M := smdl_structure_l I (R := Rₚ) target.2.1) ⟨C₁, current.member⟩ nd) 12,
        Formula.satisfies ψ tg_query_row0_m ∧ Formula.satisfies ζ tg_query_row0_m ∧
        (∀ i : Fin 6, ψ.bound ([0,1,2,3,4,6].get i) = ι.bound ([0,1,27,28,26,23].get i)) ∧
        (∀ i, Rd_entry_d (ψ.bound i).val.val (ζ.bound i).val.val k₁) ∧
        (∀ i, Rd_entry_d (ψ.bound i).val.val (ζ.bound i).val.val tₛ) ∧
        (ζ.bound 0).val.val = w₁ ∧ Rd_entry_d (ζ.bound 11).val.val (ε.bound 0).val.val Rₚ ∧
        Rd_entry_d (ζ.bound 8).val.val (ε.bound 0).val.val Rₚ ∧
      ∃ W ν : (smdl_structure_l I (R := Rₚ) target.2.1).Domain,
        Tt_pool_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l (rootNext.native_l I hZF hω))))
          ⟨w₁, current.omega_mem⟩ (ε.bound 1).val (ε.bound 6).val W ∧
        (smdl_structure_l I (R := Rₚ) target.2.1).mem ν (ρₛ.bound 10).val ∧
        Tg_realized_in_d (M := smdl_structure_l I (R := Rₚ) target.2.1)
          ⟨w₁, current.omega_mem⟩ (ρₛ.bound 18).val (ρₛ.bound 24).val (ρₛ.bound 29).val
          (ε.bound 1).val (ε.bound 6).val W (ε.bound 0).val ν ⟨C₁, current.member⟩ ∧
      ∃ εr : Env (rt_model_l (M := smdl_structure_l I (R := Rₚ) target.2.1) ⟨C₁, current.member⟩ nd) 29,
        (∀ i : Fin 22, (εr.bound i.succ.succ.succ.succ.succ.succ.succ).val =
          [⟨w₁, current.omega_mem⟩, (ρₛ.bound 17).val, (ρₛ.bound 22).val, (ρₛ.bound 23).val,
            (ρₛ.bound 24).val, (ζ.bound 3).val, (ε.bound 6).val, W, (ζ.bound 5).val, (ζ.bound 6).val,
            (ζ.bound 7).val, (ζ.bound 8).val, (ζ.bound 9).val, (ζ.bound 10).val, (ζ.bound 11).val,
            (ρₛ.bound 29).val, (ρₛ.bound 18).val, (ρₛ.bound 19).val, (ρₛ.bound 20).val, (ρₛ.bound 42).val,
            ν, (ε.bound 0).val].get i) ∧ Formula.satisfies εr tc_recovered0_m ∧
      ∃ ρr : Env (rt_model_l (M := smdl_structure_l I (R := Rₚ) target.2.1) ⟨C₁, current.member⟩ nd) 54,
        (∀ i, (ρr.bound i).val = (ρₛ.bound i).val) ∧ Formula.satisfies ρr tg_round0_m ∧
      ∃ π : Env (rt_model_l (M := smdl_structure_l I (R := Rₚ) target.2.1) ⟨C₁, current.member⟩ nd) 12,
        (∀ i : Fin 11, (π.bound ([0,1,2,4,5,6,7,8,9,10,11].get i)).val =
          (θₛ.bound ([0,1,7,8,10,11,12,13,14,15,16].get i)).val) ∧
        ∃ v, Formula.satisfies (tg_restart_env_d ρr ε εr π v) tg_seed0_m ∧
          ∃ a, let ρ₂ := tg_round_env_d (tg_restart_env_d ρr ε εr π v) a
            Formula.satisfies ρ₂ tg_round0_m ∧
            Tg_request_d (fun y x => Rd_entry_d x y tₛ) (fun i => (ι.bound i).val.val)
              (fun i => (ρ₂.bound i).val.val) ∧
          ∃ Lr Wr : (smdl_structure_l I (R := Rₚ) target.2.1).Domain, ∃ qr,
            Tg_saved_d I w₁ P Rₚ η₁ C₁ Lr.val Wr.val qr ∧
            Tg_saved_code_d P Rₚ w₁ Wr.val qr (fun i => (ρ₂.bound i).val.val) ∧
            Tg_restart_link_d I P Rₚ (fun i => (ρr.bound ([19,22,40,41,42].get i)).val.val)
              (fun i => (ρ₂.bound i).val.val) ∧
            Rd_entry_d χ₁ Lr.val Rₚ ∧
          ∃ X₂ K₂ R₂ F₂ c₂ d₂ Y₂ S₂ j₂ κ₂ U₂ D₂ u₂ : (smdl_structure_l I (R := Rₚ) target.2.1).Domain,
            Tg_image_at_d (ZF.modelsKP (ZFC.models_zf_l (rootNext.native_l I hZF hω)))
              ⟨w₁, current.omega_mem⟩ (ρ₂.bound 21).val (ρ₂.bound 18).val (ρ₂.bound 23).val (ρ₂.bound 24).val
              (ρ₂.bound 31).val (ρ₂.bound 32).val (ρ₂.bound 34).val (ρ₂.bound 15).val
              (ρ₂.bound 12).val (ρ₂.bound 11).val (ρ₂.bound 36).val
              (fun i => (ρ₂.bound ([47,48,49,50,51,52,53].get i)).val) (ρ₂.bound 38).val
              ⟨(ρ₂.bound 2).val, (ρ₂.bound 1).val, (ρ₂.bound 0).val⟩ Lr Wr X₂ K₂ R₂ F₂ c₂ d₂ Y₂ S₂ j₂ κ₂ U₂ D₂ u₂ ∧
          ∃ α₂ β₂ : (smdl_structure_l I (R := Rₚ) target.2.1).Domain,
            Rd_entry_d α₂.val χ₁ Rₚ ∧ Rd_entry_d β₂.val V₂ Rₚ ∧
            Rd_entry_d (ρ₂.bound 21).val.val β₂.val Rₚ ∧
            (smdl_structure_l I (R := Rₚ) target.2.1).IsLimitOrdinal α₂ ∧
            V_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l (rootNext.native_l I hZF hω)))) α₂ β₂ ∧
          ∃ Γ₂ k₂ z₂, Rr_layer_d I ω P Rₚ w₁ z₂ ∧
            (∀ x, M.mem x Γ₂ ↔ M.mem x P ∧ Rd_entry_d x V₂ Rₚ) ∧
            M.IsSetInjectionFromTo I k₂ Γ₂ N ∧
            (∀ y, Rd_entry_d y U₁ Rₕ ↔ ∃ x, M.mem x Γ₂ ∧ Rd_entry_d x y k₂) ∧
            (∀ x y, Rd_entry_d x y k₂ → ∀ z, Rd_entry_d z y Rₕ ↔ ∃ a, Rd_entry_d a x Rₚ ∧ Rd_entry_d a z k₂) ∧
            (∀ x y, Rd_entry_d x y k₂ ↔ Rd_entry_d y x k₁) ∧
            (∀ x x' y, Rd_entry_d x x' τ → Rd_entry_d x y k₂ → Rd_entry_d y x' σ) ∧
          ∃ Ls₂ Js₂ Os₂ Zs₂ Ds₂ ps₂ Vs₂ Ws₂ qs₂ d₃ P₃ R₃ j₃ q₃ p₃,
            Er_rank_cut_at_d hZF ω c₀ Xᵣ Rᵣ b N Rₕ qN Γ₂ k₂ P Rₚ z₂ d target.2.1
              (ZF.modelsKP (ZFC.models_zf_l (rootNext.native_l I hZF hω)))
              ⟨V₂, adjacent.common.right_rank.2.1⟩ ⟨w₁, current.omega_mem⟩ (ρ₂.bound 21).val Lr F₂ β₂ X₂ K₂ j₂
              Ls₂ Js₂ Os₂ Zs₂ Ds₂ ps₂ Vs₂ Ws₂ qs₂ d₃ P₃ R₃ j₃ q₃ p₃ ∧
            Zc_model_d I ω d₃ P₃ R₃ ∧ Smap_d I ω b d₃ N P₃ j₃ ∧ Smap_d I ω c₀ d₃ Xᵣ P₃ q₃ ∧
            Tg_anchor_d I γ₀ Bγ P₃ R₃ q₃ ∧
          ∃ θ₂ T₂ Q₂ G₂ E₂ Λ₂,
            It_tree_d hZF ω c₀ θ₂ T₂ Q₂ G₂ E₂ ∧ It_extension_d θ m n T₁ Q₁ G₁ E₁ θ₂ T₂ Q₂ G₂ E₂ ∧
            Rd_entry_d θ d₃ Q₂ ∧ It_map_d G₂ n θ j₃ ∧ It_map_d G₂ o₀ θ q₃ ∧
            Rd_entry_d m p₃ E₂ ∧ It_payload_d p₃ (ρ₂.bound 21).val.val Lr.val F₂.val ∧
            It_lower_d I γ₀ P Rₚ (ρ₂.bound 21).val.val ∧
            (It_critical_bound_d I γ₀ Q E → It_critical_bound_d I γ₀ Q₂ E₂) ∧
            M.IsSetFunction I Λ₂ ∧
            (∀ i ρ, Rd_entry_d i ρ Λ₂ ↔ ∃ p κ F, Rd_entry_d i p E₂ ∧ It_payload_d p κ ρ F) ∧
            (∀ i ρ, Rd_entry_d i ρ Λ₂ ↔ Rd_entry_d i ρ Λ₁ ∨ i = m ∧ ρ = Lr.val) ∧
          ∃ A₃ Q₃ B₃ e₃ : (smdl_structure_l I (R := Rₚ) target.2.1).Domain, ∃ Dp₃ Bp₃ t₃,
            Eb_collapse_d (M := smdl_structure_l I (R := Rₚ) target.2.1)
              ⟨w₁, current.omega_mem⟩ (ρ₂.bound 21).val Lr K₂ X₂ β₂ F₂ A₃ Q₃ B₃ e₃ ∧
            (∀ x, M.mem x Dp₃ ↔ M.mem x P ∧ Rd_entry_d x A₃.val Rₚ) ∧
            (∀ x, M.mem x Bp₃ ↔ M.mem x P ∧ Rd_entry_d x B₃.val Rₚ) ∧
            M.IsSetInjectionFromTo I t₃ Bp₃ P₃ ∧ Er_present_d I ω Ls₂ P Rₚ z₂ Γ₂ N k₂ qs₂ e₃.val Dp₃ t₃ ∧
          ∃ Y₃ v₃ C₃ γ₃ τ₃ H₂ ST₂ QT₂ GT₂ l₃ U₃ V₃ Γ₃ k₃ φ₃,
            Ic_history_d hZF ω T₂ Q₂ G₂ E₂ Λ₂ θ₂ H₂ ST₂ QT₂ GT₂ ∧
            M.MemberSubset H₁ H₂ ∧ M.MemberSubset QT₁ QT₂ ∧ M.MemberSubset GT₁ GT₂ ∧
            Ic_at_d H₂ θ P₃ C₃ τ₃ v₃ Y₃ γ₃ ∧ Ic_bound_d I H₂ Q₂ P₃ R₃ τ₃ θ l₃ ∧
            Ic_agree_d I P Rₚ C τ P₃ R₃ C₃ τ₃ Lr.val l₃ φ₃ U₃ V₃ Γ₃ k₃ ∧
            M.IsRestrictionOf I k₃ t₃ Γ₃ ∧
            Tg_answer_step_d I d₃ P₃ R₃ t₃ k₃ j₃ qN l₃ w.val ηN CN N Rₕ (ρ₂.bound 41).val.val
              B σ C₃ τ₃ (ρ.bound 8).val.val ω zs γ₀ Bγ Cᵣ S₀
              ⟨m,d,P,Rₚ,w₁,η₁,C₁,Lr.val,Wr.val,qr,q',C,τ⟩
              ⟨o₀,n,Q,G,Λ,H⟩ ⟨o₀,θ,Q₂,G₂,Λ₂,H₂⟩
              (fun i => (ι.bound i).val.val) (fun i =>
              (tg_round_reply_values_d (fun j => (ρ₂.bound j).val)
                ⟨w₁, current.omega_mem⟩ κ₂ U₂ D₂ u₂ i).val)

end YesMetaZFC.SetTheory.LargeCardinal
