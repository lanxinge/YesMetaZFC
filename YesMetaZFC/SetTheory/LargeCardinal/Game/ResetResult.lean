import YesMetaZFC.SetTheory.LargeCardinal.Game.AnswerNativeInput
import YesMetaZFC.SetTheory.LargeCardinal.Game.SavedNative
import YesMetaZFC.SetTheory.LargeCardinal.Game.ReplyPool
import YesMetaZFC.SetTheory.LargeCardinal.Extender.RawAlphabet

/-! # 原生重置的完整两步结果

同一次原工厂、两次树与复制历史延伸、完整回答及所有后续档案追加一起保留。
统一请求状态直接消费这份结论，不重新选择其中的后继或回答。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

def Tg_reset_native_d
    (ω c₀ X₀ R₀ n m T Q G E Λ H QT GT N R B σ u U β d o q C₀ S₀ γ Bγ w η C z χ : M.Domain)
    (mn : Smdl_d I d N R) (hN : (smdl_structure_l I (R := R) mn.2.1).Models KP)
    (context : Tg_context_d I w N R η C)
    (nc : Nonempty {x : (smdl_structure_l I (R := R) mn.2.1).Domain //
      (smdl_structure_l I (R := R) mn.2.1).mem x ⟨C,context.member⟩})
    (ι : Env (rt_model_l (M := smdl_structure_l I (R := R) mn.2.1) ⟨C,context.member⟩ nc) 46) : Prop :=
    ∃ θ T₁ Q₁ G₁ E₁ j H₁ ST₁ QT₁ GT₁ q₁,
      M.SuccessorOf θ m ∧ It_tree_d hZF ω c₀ θ T₁ Q₁ G₁ E₁ ∧
      It_extension_d m n n T Q G E θ T₁ Q₁ G₁ E₁ ∧ Rd_entry_d m d Q₁ ∧ It_map_d G₁ n m j ∧
      (∀ x y, Rd_entry_d x y j → x = y) ∧
      (∀ p, Rd_entry_d n p E₁ → ∀ x, ¬ M.mem x p) ∧
      (∀ i ρ, Rd_entry_d i ρ Λ ↔ ∃ p κ F, Rd_entry_d i p E₁ ∧ It_payload_d p κ ρ F) ∧
      Ic_history_d hZF ω T₁ Q₁ G₁ E₁ Λ θ H₁ ST₁ QT₁ GT₁ ∧
      M.MemberSubset H H₁ ∧ M.MemberSubset QT QT₁ ∧ M.MemberSubset GT GT₁ ∧
      Ic_at_d H₁ m N B σ u U β ∧ Ic_bound_d I H₁ Q₁ N R σ m χ ∧
      It_map_d G₁ o m q₁ ∧ (∀ x y, Rd_entry_d x y q → Rd_entry_d x y q₁) ∧
      Rd_entry_d C₀ C q₁ ∧ Tg_anchor_d I γ Bγ N R q₁ ∧
    ∃ ρ : Env (rt_model_l (M := smdl_structure_l I (R := R) mn.2.1) ⟨C,context.member⟩ nc) 54,
      Formula.satisfies ρ tg_round0_m ∧
      Tg_request_d Eq (fun i => (ι.bound i).val.val) (fun i => (ρ.bound i).val.val) ∧
      (ρ.bound 39).val.val = (ι.bound 24).val.val ∧
      (ρ.bound 22).val.val = (ι.bound 1).val.val ∧
      (ρ.bound 40).val.val = (ι.bound 1).val.val ∧
      (ρ.bound 41).val.val = (ι.bound 1).val.val ∧
      (ρ.bound 42).val.val = (ι.bound 1).val.val ∧
      (ρ.bound 19).val.val = (ι.bound 7).val.val ∧
      (ρ.bound 20).val.val = (ι.bound 8).val.val ∧
      (∀ a, It_lower_d I a N R (ι.bound 24).val.val → It_lower_d I a N R (ρ.bound 15).val.val) ∧
    ∃ L W : (smdl_structure_l I (R := R) mn.2.1).Domain, ∃ r,
      Tg_saved_d I w N R η C L.val W.val r ∧
      Tg_saved_code_d N R w W.val r (fun i => (ρ.bound i).val.val) ∧ Rd_entry_d χ L.val R ∧
    ∃ X K R₁ F c₁ d₁ Y S j₁ κ₁ U₁ D₁ u₁ : (smdl_structure_l I (R := R) mn.2.1).Domain,
      Tg_image_at_d hN ⟨w,context.omega_mem⟩
        (ρ.bound 21).val (ρ.bound 18).val (ρ.bound 23).val (ρ.bound 24).val
        (ρ.bound 31).val (ρ.bound 32).val (ρ.bound 34).val (ρ.bound 15).val
        (ρ.bound 12).val (ρ.bound 11).val (ρ.bound 36).val
        (fun i => (ρ.bound ([47,48,49,50,51,52,53].get i)).val) (ρ.bound 38).val
        ⟨(ρ.bound 2).val,(ρ.bound 1).val,(ρ.bound 0).val⟩ L W X K R₁ F c₁ d₁ Y S j₁ κ₁ U₁ D₁ u₁ ∧
    ∃ V : (smdl_structure_l I (R := R) mn.2.1).Domain,
    ∃ Γ k Ls Js Os Zs Ds ps Vs Ws qs d₂ P R₂ j₂ q₂ p₂,
      V_d (kp_pair_l hN) (ρ.bound 15).val V ∧
      (∀ x, M.mem x Γ ↔ M.mem x N ∧ Rd_entry_d x X.val R) ∧
      (∀ x y, Rd_entry_d x y k ↔ M.mem x Γ ∧ x = y) ∧
      Er_rank_cut_at_d hZF ω c₀ X₀ R₀ d N R q Γ k N R z d mn.2.1 hN
        X ⟨w,context.omega_mem⟩ (ρ.bound 21).val L F V X K j₁
        Ls Js Os Zs Ds ps Vs Ws qs d₂ P R₂ j₂ q₂ p₂ ∧
    ∃ θ₂ T₂ Q₂ G₂ E₂ Λ₂ H₂ ST₂ QT₂ GT₂ v₂ Y₂ β₂ B₂ σ₂ l φ Uc Vc Dc t,
      It_tree_d hZF ω c₀ θ₂ T₂ Q₂ G₂ E₂ ∧
      It_extension_d θ m n T₁ Q₁ G₁ E₁ θ₂ T₂ Q₂ G₂ E₂ ∧
      (It_critical_bound_d I γ Q E → It_critical_bound_d I γ Q₂ E₂) ∧
      Rd_entry_d θ d₂ Q₂ ∧ It_map_d G₂ n θ j₂ ∧ Rd_entry_d m p₂ E₂ ∧ It_map_d G₂ o θ q₂ ∧
      M.IsSetFunction I Λ₂ ∧
      (∀ i ρ, Rd_entry_d i ρ Λ₂ ↔ ∃ p κ F, Rd_entry_d i p E₂ ∧ It_payload_d p κ ρ F) ∧
      (∀ i ρ, Rd_entry_d i ρ Λ₂ ↔ Rd_entry_d i ρ Λ ∨ i = m ∧ ρ = L.val) ∧
      Ic_history_d hZF ω T₂ Q₂ G₂ E₂ Λ₂ θ₂ H₂ ST₂ QT₂ GT₂ ∧
      M.MemberSubset H₁ H₂ ∧ M.MemberSubset QT₁ QT₂ ∧ M.MemberSubset GT₁ GT₂ ∧
      Ic_at_d H₂ θ P B₂ σ₂ v₂ Y₂ β₂ ∧ Ic_bound_d I H₂ Q₂ P R₂ σ₂ θ l ∧
      Ic_agree_d I N R B σ P R₂ B₂ σ₂ L.val l φ Uc Vc Dc t ∧
    ∃ Aₚ Qₚ Bₚ eₚ : (smdl_structure_l I (R := R) mn.2.1).Domain, ∃ Dₚ Bp tₚ,
      Eb_collapse_d (M := smdl_structure_l I (R := R) mn.2.1)
        ⟨w,context.omega_mem⟩ (ρ.bound 21).val L K X V F Aₚ Qₚ Bₚ eₚ ∧
      (∀ x, M.mem x Dₚ ↔ M.mem x N ∧ Rd_entry_d x Aₚ.val R) ∧
      (∀ x, M.mem x Bp ↔ M.mem x N ∧ Rd_entry_d x Bₚ.val R) ∧
      M.IsSetInjectionFromTo I tₚ Bp P ∧
      Er_present_d I ω Ls N R z Γ N k qs eₚ.val Dₚ tₚ ∧
      M.IsRestrictionOf I t tₚ Dc ∧ Rd_entry_d L.val l tₚ ∧ Rd_entry_d Uc Vc tₚ ∧
    ∃ target : Smdl_d I d₂ P R₂, ∃ w₂ η₂ C₂,
      Rd_entry_d w w₂ j₂ ∧ Rd_entry_d η η₂ j₂ ∧ Rd_entry_d C C₂ j₂ ∧
    ∃ current : Tg_context_d I w₂ P R₂ η₂ C₂,
    ∃ nd : Nonempty {x : (smdl_structure_l I (R := R₂) target.2.1).Domain //
      (smdl_structure_l I (R := R₂) target.2.1).mem x ⟨C₂,current.member⟩},
    ∃ ι₂ : Env (rt_model_l (M := smdl_structure_l I (R := R₂) target.2.1) ⟨C₂,current.member⟩ nd) 46,
    ∃ ε₂ : Env (rt_model_l (M := smdl_structure_l I (R := R₂) target.2.1) ⟨C₂,current.member⟩ nd) 22,
      (∀ i, Rd_entry_d (ι.bound i).val.val (ι₂.bound i).val.val j₂) ∧
      Formula.satisfies ι₂ tg_issued0_m ∧ (ι₂.bound 0).val.val = w₂ ∧
      (∀ x, Rd_entry_d x l R₂ → Rd_entry_d x (ι₂.bound 24).val.val R₂) ∧
      Rd_entry_d l (ι₂.bound 5).val.val R₂ ∧ Rd_entry_d l C₂ R₂ ∧
      Rr_truth_d I P R₂ (Formula.isRegularCardinal kpair_convention_l .newest)
        (fun _ : Fin 1 => (ι₂.bound 5).val.val) ∧
    ∃ z₂, Rr_layer_d I ω P R₂ w₂ z₂ ∧
      (⟨m,d,N,R,w,η,C,L.val,W.val,r,q₁,B,σ⟩ : Tg_archive_row_d M.Domain).link_d
        ⟨o,θ,Q₂,G₂,Λ₂,H₂⟩ ∧
      (∀ D, Tg_archive_links_d I ⟨o,n,Q,G,Λ,H⟩ D → Tg_archive_links_d I ⟨o,θ,Q₂,G₂,Λ₂,H₂⟩ D) ∧
      Tg_archive_trace_d I N R B σ w C (ι.bound 4).val.val (ι.bound 1).val.val (ι.bound 2).val.val (ι.bound 3).val.val
        (ι.bound 20).val.val P R₂ B₂ σ₂ w₂ C₂ (ι₂.bound 4).val.val (ι₂.bound 1).val.val
        (ι₂.bound 2).val.val (ι₂.bound 3).val.val (ι₂.bound 20).val.val j₂ (ρ.bound 21).val.val z z₂ ∧
      (∀ D, Tg_archive_links_d I ⟨o,n,Q,G,Λ,H⟩ D →
        Tg_archive_views_d I ω γ Bγ C₀ D N R B σ w C (ι.bound 4).val.val
          (ι.bound 1).val.val (ι.bound 2).val.val (ι.bound 3).val.val z (ι.bound 20).val.val →
        Tg_archive_views_d I ω γ Bγ C₀ D P R₂ B₂ σ₂ w₂ C₂ (ι₂.bound 4).val.val
          (ι₂.bound 1).val.val (ι₂.bound 2).val.val (ι₂.bound 3).val.val z₂ (ι₂.bound 20).val.val) ∧
      (∀ i, Rd_entry_d (tg_round_reply_values_d (fun j => (ρ.bound j).val)
        ⟨w,context.omega_mem⟩ κ₁ U₁ D₁ u₁ i).val (ε₂.bound i).val.val tₚ) ∧
      Rd_entry_d (ρ.bound 41).val.val (ι₂.bound 23).val.val t ∧
      Rd_entry_d (ρ.bound 15).val.val (ε₂.bound 4).val.val t ∧
      Rd_entry_d (ρ.bound 11).val.val (ε₂.bound 9).val.val t ∧
      Formula.satisfies ε₂ tg_reply0_m ∧ Tg_reply_link_d Eq ι₂.bound ε₂.bound ∧
      Rd_entry_d (ε₂.bound 4).val.val (ι₂.bound 5).val.val R₂ ∧
      Formula.satisfies (⟨fun i => [ι₂.bound 0,ε₂.bound 4,ι₂.bound 26,ι₂.bound 1,ι₂.bound 1].get i,
        ι₂.free⟩ : Env (rt_model_l (M := smdl_structure_l I (R := R₂) target.2.1) ⟨C₂,current.member⟩ nd) 5)
        tg_query_request0_m ∧
      ∃ Aq Uq Dq rq mq bq hq qq,
        Dq = ε₂.bound 7 ∧
        Tg_query_data_d (ι₂.bound 11) (ε₂.bound 4) (ι₂.bound 26) (ι₂.bound 1) (ι₂.bound 1) Aq Uq Dq rq mq bq hq qq ∧
        Formula.satisfies (⟨fun i => [ι₂.bound 0,ι₂.bound 1,ι₂.bound 27,ι₂.bound 28,ε₂.bound 4,Aq,Uq,Dq,rq,bq,hq].get i,
          ι₂.free⟩ : Env (rt_model_l (M := smdl_structure_l I (R := R₂) target.2.1) ⟨C₂,current.member⟩ nd) 11)
          tg_reply_language0_m ∧
        Formula.satisfies (⟨fun i => [ι₂.bound 0,ι₂.bound 1,ι₂.bound 27,ι₂.bound 28,ι₂.bound 26,
          ι₂.bound 1,ι₂.bound 1,rq,mq,bq,hq,qq].get i,ι₂.free⟩ :
          Env (rt_model_l (M := smdl_structure_l I (R := R₂) target.2.1) ⟨C₂,current.member⟩ nd) 12)
          tg_query_row0_m ∧
        Tg_answer_step_d I d₂ P R₂ tₚ t j₂ q l w η C N R (ρ.bound 41).val.val
          B σ B₂ σ₂ (ρ.bound 21).val.val ω z γ Bγ C₀ S₀
          ⟨m,d,N,R,w,η,C,L.val,W.val,r,q₁,B,σ⟩
          ⟨o,n,Q,G,Λ,H⟩ ⟨o,θ,Q₂,G₂,Λ₂,H₂⟩
          (fun i => (ι.bound i).val.val) (fun i =>
            (tg_round_reply_values_d (fun j => (ρ.bound j).val) ⟨w,context.omega_mem⟩ κ₁ U₁ D₁ u₁ i).val) ∧
        (ι.bound 19 = ι.bound 1 → ∃ n A₀ A₂ t f,
          Rd_entry_d n (ι₂.bound 19).val.val z₂ ∧
          (∀ x, M.mem x A₀ ↔ M.mem x N ∧ Rd_entry_d x (ι.bound 6).val.val R) ∧
          (∀ x, M.mem x A₂ ↔ M.mem x P ∧ Rd_entry_d x (ι₂.bound 6).val.val R₂) ∧
          M.IsSetBijectionFromTo I t A₀ A₂ ∧ M.IsRestrictionOf I t j₂ A₀ ∧
          Tg_prefix_d I n A₀ P R₂ C₂ (ι₂.bound 4).val.val (ι₂.bound 3).val.val (ι₂.bound 20).val.val z₂ j₂ f)

end YesMetaZFC.SetTheory.LargeCardinal
