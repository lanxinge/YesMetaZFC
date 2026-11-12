import YesMetaZFC.SetTheory.LargeCardinal.Game.RawReplyInput
import YesMetaZFC.SetTheory.LargeCardinal.Game.RawRootContinueStep
import YesMetaZFC.SetTheory.LargeCardinal.Game.RawPrepareRoot
import YesMetaZFC.SetTheory.LargeCardinal.Game.RawAnswer
import YesMetaZFC.SetTheory.LargeCardinal.Game.RawCritical
import YesMetaZFC.SetTheory.LargeCardinal.Iteration.FrameUnion

/-! # 固定第二原后继中的完整回答收尾

第二工厂和共同图已经选定，本段只生产一次目标请求与查询表。
完整前驱方程推进根切片，实际两次低秩方块保持全部旧档案；最后
更新原树支撑列并调用原回答规则。没有重新选择工厂、池图或原记录。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

/-- 固定运输结果直接完成根几何、三查询、档案列及实际回答。 -/
theorem Tg_raw_reply_transport_d.continue_finish_l
    {ω S₀ X₀ R₀ w₀ γ₀ B₀ D₀ C₀ A₀ A N R w η C χ z k H r q c₀ n m T Q G E Λ c o f
      θ T₁ Q₁ G₁ E₁ Λ₁ parentIndex d P S wp ηp Cp zp q₁
      L₁ l₁ U₁ V₁ Γ₁ g₁ kback γ Vγ tγ γp Vγp tγp
      d₂ Z R₂ j₂ q₂ p₂ F₂ l Vc Γc gc D₃ t₃ r₂ : M.Domain}
    {v : Fin 46 → M.Domain}
    (request : Tg_raw_request_d I ω S₀ X₀ R₀ γ₀ D₀ C₀ A₀ N R w η C χ z k H r q ⟨o,n,Q,G,Λ⟩ v)
    (root : Zc_model_d I ω c₀ X₀ R₀)
    (cut : Tg_root_cut_d I c₀ X₀ R₀ w₀ γ₀ B₀ A₀ D₀ A)
    (tree : It_tree_d hZF ω c₀ m T Q G E) (hm : M.SuccessorOf m n)
    (qn : Rd_entry_d n c Q) (mn : Smdl_d I c N R) (qr : Rd_entry_d o c₀ Q)
    (prior : Tg_prefix_d I k A N R C (v 4) (v 3) (v 20) z q f)
    (tree₁ : It_tree_d hZF ω c₀ θ T₁ Q₁ G₁ E₁)
    (extension₁ : It_extension_d m n parentIndex T Q G E θ T₁ Q₁ G₁ E₁)
    (node₁ : Rd_entry_d m d Q₁) (root₁ : It_map_d G₁ o m q₁)
    (lf₁ : M.IsSetFunction I Λ₁)
    (levels₁ : ∀ i μ, Rd_entry_d i μ Λ₁ ↔ ∃ p κ F, Rd_entry_d i p E₁ ∧ It_payload_d p κ μ F)
    (keepLevels : ∀ i μ, Rd_entry_d i μ Λ → Rd_entry_d i μ Λ₁)
    (critical₁ : Tg_raw_critical_d I X₀ R₀ γ₀ D₀ C₀ o Q G E →
      Tg_raw_critical_d I X₀ R₀ γ₀ D₀ C₀ o Q₁ G₁ E₁)
    (mp : Smdl_d I d P S)
    (hN : (smdl_structure_l I (R := R) mn.2.1).Models KP)
    (ownerZF : (smdl_structure_l I (R := S) mp.2.1).Models ZF)
    (L₂ W₂ κ' A' D' u' B₃ : (smdl_structure_l I (R := S) mp.2.1).Domain)
    (saved₂ : Tg_saved_d I wp P S ηp Cp L₂.val W₂.val r₂)
    (numbersP : Rr_layer_d I ω P S wp zp)
    (rootMapP : Smap_d I ω c₀ d X₀ P q₁)
    (nc : Nonempty {x : (smdl_structure_l I (R := R) mn.2.1).Domain //
      (smdl_structure_l I (R := R) mn.2.1).mem x ⟨C,request.context.member⟩})
    (nd : Nonempty {x : (smdl_structure_l I (R := S) mp.2.1).Domain //
      (smdl_structure_l I (R := S) mp.2.1).mem x ⟨Cp,saved₂.context.member⟩})
    (ι : Env (rt_model_l (M := smdl_structure_l I (R := R) mn.2.1) ⟨C,request.context.member⟩ nc) 46)
    (ρ₂ : Env (rt_model_l (M := smdl_structure_l I (R := S) mp.2.1) ⟨Cp,saved₂.context.member⟩ nd) 54)
    (eq : ∀ i, (ι.bound i).val.val = v i)
    (issued : Formula.satisfies ι tg_issued0_m) (round₂ : Formula.satisfies ρ₂ tg_round0_m)
    (hw₂ : (ρ₂.bound 16).val.val = wp)
    (code₂ : Tg_saved_code_d P S wp W₂.val r₂ (fun i => (ρ₂.bound i).val.val))
    (base₂ : Tg_raw_saved_base_d I X₀ R₀ γ₀ D₀ C₀ P S wp Cp W₂.val r₂ q₁)
    (cofinal₂ : Tg_raw_cofinal_d I wp P S L₂.val)
    (name₂ : Tg_saved_name_d I S₀ P S wp W₂.val r₂ q₁)
    (first : Ic_common_d I N R P S L₁ l₁ U₁ V₁ Γ₁ g₁)
    (roots₁ : Tg_root_square_d D₀ q q₁ g₁)
    (inverse : ∀ x y, Rd_entry_d x y kback ↔ Rd_entry_d y x g₁)
    (point : Rd_entry_d (ι.bound 24).val.val (ρ₂.bound 21).val.val g₁)
    (highτ : Rd_entry_d (ι.bound 24).val.val L₁ R)
    (slice : Tg_root_slice_d I X₀ R₀ γ₀ D₀ C₀ N R C q γ Vγ tγ)
    (sliceP : Tg_root_slice_d I X₀ R₀ γ₀ D₀ C₀ P S Cp q₁ γp Vγp tγp)
    (iVγ : Rd_entry_d Vγ Vγp g₁) (omegaP : Rd_entry_d wp Vγp S)
    (lower₂ : ∀ x, Rd_entry_d x γp S → Rd_entry_d x (ρ₂.bound 21).val.val S)
    (s₀ : (smdl_structure_l I (R := R) mn.2.1).Domain)
    (queryPlay : Tg_play_d I N R C (ι.bound 4).val.val (ι.bound 3).val.val (ι.bound 20).val.val s₀.val)
    (lowShort : Rd_entry_d s₀.val Vγ R) (shortPoint : Rd_entry_d s₀.val (ρ₂.bound 40).val.val g₁)
    (mt : Smdl_d I d₂ Z R₂) (certificateZ : Zc_model_d I ω d₂ Z R₂)
    (embed₂ : Smap_d I ω c d₂ N Z j₂) (rootMapZ : Smap_d I ω c₀ d₂ X₀ Z q₂)
    (rootGraph : ∀ x y, Rd_entry_d x y q₂ ↔ M.mem x X₀ ∧ ∃ a, Rd_entry_d x a q ∧ Rd_entry_d a y j₂)
    (payload₂ : It_payload_d p₂ (ρ₂.bound 21).val.val L₂.val F₂)
    (extend₂ : ∀ a i TT QQ GG EE r o, It_tree_d hZF ω c₀ a TT QQ GG EE → M.SuccessorOf a i →
      Rd_entry_d i d QQ → Rd_entry_d r c QQ → It_map_d GG o r q →
      ∃ a' TT' QQ' GG' EE', It_tree_d hZF ω c₀ a' TT' QQ' GG' EE' ∧
        It_extension_d a i r TT QQ GG EE a' TT' QQ' GG' EE' ∧
        Rd_entry_d a d₂ QQ' ∧ It_map_d GG' r a j₂ ∧ Rd_entry_d i p₂ EE' ∧ It_map_d GG' o a q₂)
    (second : Ic_common_d I P S Z R₂ L₂.val l W₂.val Vc Γc gc)
    (Kκ : (smdl_structure_l I (R := S) mp.2.1).Domain)
    (rankKκ : V_d (kp_pair_l (ZF.modelsKP ownerZF)) (ρ₂.bound 21).val Kκ)
    (lowSquare₂ : ∀ x : (smdl_structure_l I (R := S) mp.2.1).Domain, ∀ y E,
      Rd_entry_d x.val Kκ.val S → Rd_entry_d x.val y kback → (Rd_entry_d x.val E gc ↔ Rd_entry_d y E j₂))
    (κL : Rd_entry_d (ρ₂.bound 21).val.val L₂.val S)
    (τL : Rd_entry_d (ρ₂.bound 15).val.val L₂.val S)
    (hQW : Rd_entry_d (ρ₂.bound 12).val.val W₂.val S)
    (huW : Rd_entry_d (ρ₂.bound 11).val.val W₂.val S)
    (transB₃ : (smdl_structure_l I (R := S) mp.2.1).TransitiveSet B₃)
    (carrier₃ : ∀ x, M.mem x D₃ ↔ M.mem x P ∧ Rd_entry_d x B₃.val S)
    (ft₃ : M.IsSetInjectionFromTo I t₃ D₃ Z) (restrict₃ : M.IsRestrictionOf I gc t₃ Γc)
    (endpoint₃ : Rd_entry_d L₂.val l t₃) (layer₃ : Rd_entry_d W₂.val Vc t₃)
    (pred₃ : ∀ x y, Rd_entry_d x y t₃ → ∀ z,
      Rd_entry_d z y R₂ ↔ ∃ a, Rd_entry_d a x S ∧ Rd_entry_d a z t₃)
    (ε₃ : Env (smdl_structure_l I (R := R₂) mt.2.1) 22)
    (transport : Tg_raw_reply_transport_d I ω Z R₂ j₂ gc t₃ l mt.2.1
      (fun i => (ρ₂.bound i).val.val) (fun i => (ι.bound i).val.val)
      (fun i => (tg_round_reply_values_d (fun j => (ρ₂.bound j).val)
        ⟨wp,saved₂.context.omega_mem⟩ κ' A' D' u' i).val) ε₃) :
    ∃ θ₂ T₂ Q₂ G₂ E₂ Λ₂ d₂ Z R₂ j₂ q₂ p₂,
      It_tree_d hZF ω c₀ θ₂ T₂ Q₂ G₂ E₂ ∧ It_extension_d θ m n T₁ Q₁ G₁ E₁ θ₂ T₂ Q₂ G₂ E₂ ∧
      Rd_entry_d θ d₂ Q₂ ∧ It_map_d G₂ n θ j₂ ∧ Rd_entry_d m p₂ E₂ ∧ It_map_d G₂ o θ q₂ ∧
      M.IsSetFunction I Λ₂ ∧
      (∀ i μ, Rd_entry_d i μ Λ₂ ↔ ∃ p κ F, Rd_entry_d i p E₂ ∧ It_payload_d p κ μ F) ∧
      (∀ i μ, Rd_entry_d i μ Λ₂ ↔ Rd_entry_d i μ Λ₁ ∨ i = m ∧ μ = L₂.val) ∧
      (⟨m,d,P,S,wp,ηp,Cp,L₂.val,W₂.val,r₂,q₁⟩ : Tg_raw_archive_row_d M.Domain).link_d ⟨o,θ,Q₂,G₂,Λ₂⟩ ∧
      Tg_raw_archive_links_d I ⟨o,θ,Q₂,G₂,Λ₂⟩ H ∧
    ∃ mt : Smdl_d I d₂ Z R₂, Zc_model_d I ω d₂ Z R₂ ∧
      Smap_d I ω c d₂ N Z j₂ ∧ Smap_d I ω c₀ d₂ X₀ Z q₂ ∧ It_comp_d q j₂ q₂ ∧
      (Tg_raw_critical_d I X₀ R₀ γ₀ D₀ C₀ o Q G E →
        Tg_raw_critical_d I X₀ R₀ γ₀ D₀ C₀ o Q₂ G₂ E₂) ∧
    ∃ l Vc Γc gc, Ic_common_d I P S Z R₂ L₂.val l W₂.val Vc Γc gc ∧ Tg_root_square_d D₀ q₁ q₂ gc ∧
    ∃ w₂ η₂ C₂ z₂, Rd_entry_d w w₂ j₂ ∧ Rd_entry_d η η₂ j₂ ∧ Rd_entry_d C C₂ j₂ ∧
      Rr_layer_d I ω Z R₂ w₂ z₂ ∧
    ∃ current : Tg_context_d I w₂ Z R₂ η₂ C₂,
    ∃ nd : Nonempty {x : (smdl_structure_l I (R := R₂) mt.2.1).Domain //
      (smdl_structure_l I (R := R₂) mt.2.1).mem x ⟨C₂,current.member⟩},
    ∃ ι₂ : Env (rt_model_l (M := smdl_structure_l I (R := R₂) mt.2.1) ⟨C₂,current.member⟩ nd) 46,
      (∀ i, Rd_entry_d (v i) (ι₂.bound i).val.val j₂) ∧ Formula.satisfies ι₂ tg_issued0_m ∧
      (ι₂.bound 0).val.val = w₂ ∧
      Tg_round_index_d I ω z₂ mt.2.1 ⟨w₂,current.omega_mem⟩ (ι₂.bound 19).val k ∧
      Rd_entry_d S₀ (ι₂.bound 7).val.val q₂ ∧ Rd_entry_d A₀ (ι₂.bound 6).val.val q₂ ∧
      (∀ x, Rd_entry_d x l R₂ → Rd_entry_d x (ι₂.bound 24).val.val R₂) ∧ Rd_entry_d l C₂ R₂ ∧
      Tg_prefix_d I k A Z R₂ C₂ (ι₂.bound 4).val.val (ι₂.bound 3).val.val (ι₂.bound 20).val.val z₂ q₂ f ∧
      Tg_raw_archive_views_d I ω S₀ X₀ R₀ γ₀ D₀ C₀ q₂ H Z R₂ l w₂ C₂ (ι₂.bound 4).val.val
        (ι₂.bound 1).val.val (ι₂.bound 2).val.val (ι₂.bound 3).val.val z₂ (ι₂.bound 20).val.val ∧
    ∃ γ₂ Vγ₂ tγ₂, Tg_root_slice_d I X₀ R₀ γ₀ D₀ C₀ Z R₂ C₂ q₂ γ₂ Vγ₂ tγ₂ ∧
      Rd_entry_d w₂ Vγ₂ R₂ ∧ (∀ x, Rd_entry_d x γ₂ R₂ → Rd_entry_d x (ι₂.bound 24).val.val R₂) ∧
    ∃ B fA, (∀ y, M.mem y B ↔ M.mem y Z ∧ Rd_entry_d y (ι₂.bound 6).val.val R₂) ∧
      M.IsSetBijectionFromTo I fA A B ∧ M.IsRestrictionOf I fA q₂ A ∧
    ∃ τ u Aq Uq Dq rq mq bq hq qq : (rt_model_l
      (M := smdl_structure_l I (R := R₂) mt.2.1) ⟨C₂,current.member⟩ nd).Domain,
      Rd_entry_d τ.val.val (ι₂.bound 5).val.val R₂ ∧
      Formula.satisfies (⟨fun i => [ι₂.bound 0,τ,ι₂.bound 26,ι₂.bound 1,ι₂.bound 1].get i,
        fun _ => ι₂.bound 0⟩ : Env (rt_model_l (M := smdl_structure_l I (R := R₂) mt.2.1)
          ⟨C₂,current.member⟩ nd) 5) tg_query_request0_m ∧
      Tg_query_data_d (ι₂.bound 11) τ (ι₂.bound 26) (ι₂.bound 1) (ι₂.bound 1) Aq Uq Dq rq mq bq hq qq ∧
      Formula.satisfies (⟨fun i => [ι₂.bound 0,ι₂.bound 27,ι₂.bound 28,ι₂.bound 24,τ,
        ι₂.bound 30,ι₂.bound 31,Dq,ι₂.bound 25,u,ι₂.bound 36,ι₂.bound 37,rq,bq,hq,
        ι₂.bound 38,ι₂.bound 39,ι₂.bound 40,ι₂.bound 41,ι₂.bound 42,ι₂.bound 43,ι₂.bound 44].get i,
        fun _ => ι₂.bound 0⟩ : Env (rt_model_l (M := smdl_structure_l I (R := R₂) mt.2.1)
          ⟨C₂,current.member⟩ nd) 22) tg_reply0_m ∧
      Rd_entry_d (ρ₂.bound 41).val.val (ι₂.bound 23).val.val gc ∧ Rd_entry_d (ρ₂.bound 15).val.val τ.val.val gc ∧
      Rd_entry_d (ρ₂.bound 11).val.val u.val.val gc ∧
      (∃ a, Rd_entry_d (ρ₂.bound 40).val.val a gc ∧ Tg_play_d I Z R₂ C₂ (ι₂.bound 4).val.val
        (ι₂.bound 3).val.val (ι₂.bound 20).val.val a) ∧
      Tg_raw_answer_result_d I mt.2.1 ⟨C₂,current.member⟩ nd w₂ η₂ ω z₂ k l
        X₀ R₀ γ₀ D₀ C₀ A₀ S₀ q₂ H gc ⟨m,d,P,S,wp,ηp,Cp,L₂.val,W₂.val,r₂,q₁⟩
        ⟨o,θ,Q₂,G₂,Λ₂⟩ ι₂ τ u := by
  let right := tree.diagram.elementary o n q c₀ X₀ R₀ c N R request.origin qr qn root.model mn
  have sourceZc := root.map_l hZF tree.omega mn right
  have hP := ZF.modelsKP ownerZF
  let Pn := smdl_structure_l I (R := S) mp.2.1
  have fp := saved₂.context.finite_l mp.2.1 hP.1
  have hwι : (ι.bound 0).val.val = w := (eq 0).trans request.omega
  have groundZ := certificateZ.native_l I hZF tree.omega
  have targetZF := ZFC.models_zf_l groundZ
  have hZ := ZF.modelsKP targetZF
  let Zn := smdl_structure_l I (R := R₂) mt.2.1
  have omegaOwner := numbersP.omega_l I (ZF.modelsKP hZF) tree.omega hP.1
  obtain ⟨η₂,C₂,iw,iη,iC,current,ne',ι₂,replyEnv,points,issued₂,eqω,ordinal₂,bound₂,belowδ,member₂,
    regular₂,replyValues,reflected,sameReply,label,domain,type,finiteL,finiteN,pointBase,belowτ,key,
    Aq,Uq,Dq,rq,mq,bq,hq,qq,domainEq,table,language,queryRow⟩ := transport.input_l hZF tree.omega
      mn mp mt hN ownerZF targetZF request.context saved₂.context embed₂ nc nd ι ρ₂ issued round₂
      hwι hw₂ omegaOwner κ' A' D' u' B₃ second transB₃ carrier₃ ft₃ restrict₃ endpoint₃ layer₃ pred₃
      τL hQW huW ε₃
  let w₂ := (ε₃.bound 0).val
  let Cz : Zn.Domain := ⟨C₂,current.member⟩
  have fz := current.finite_l mt.2.1 hZ.1
  obtain ⟨z₂,numbers₂⟩ := transport.numbers
  have currentPoints i : Rd_entry_d (v i) (ι₂.bound i).val.val j₂ := eq i ▸ points i
  have rootComp : It_comp_d q j₂ q₂ := ⟨rootMapZ.1.1.1.1,fun x y => (rootGraph x y).trans
    ⟨And.right,fun ⟨a,xa,ay⟩ => ⟨right.1.1.input_mem_of_pairMember xa,a,xa,ay⟩⟩⟩
  have rootContext := (rootComp.2 C₀ C₂).mpr ⟨C,slice.context,iC⟩
  have targetName := (rootComp.2 S₀ _).mpr ⟨v 7,request.name,currentPoints 7⟩
  have targetAlphabet := (rootComp.2 A₀ _).mpr ⟨v 6,request.alphabet,currentPoints 6⟩
  obtain ⟨γ₂,Vγ₂,tγ₂,ig₂,iV₂,comp₂,slice₂,highγ₂,roots₂⟩ := sliceP.continue_step_l hZF second mp mt hP hZ
    (ρ₂.bound 21).val Kκ rankKκ κL lower₂ roots₁ inverse (fun x hx y E xy => lowSquare₂ x y E hx xy)
    rootMapP.1.1.1 right.1.1 (fun x hx => ((cut.carrier x).mp hx).1) rootComp rootContext
  have ownerω : Rd_entry_d wp w₂ gc := hw₂ ▸ transport.omega
  have omegaSlice₂ : Rd_entry_d w₂ Vγ₂ R₂ := (second.pred Vγp Vγ₂ iV₂ w₂).mpr ⟨wp,omegaP,ownerω⟩
  have ordκ : Zn.IsOrdinal (ι₂.bound 24).val := (KP.ord0_sat_l hZ _ .newest).mp
    ((rr_truth_native_l I mt.2.1 (KP.ord0_m .newest) (by simp -implicitDefEqProofs)
      (fun _ : Fin 1 => (ι₂.bound 24).val)).mp ordinal₂)
  have lowerFinal x (hx : Rd_entry_d x γ₂ R₂) : Rd_entry_d x (ι₂.bound 24).val.val R₂ :=
    ordκ.transitive ⟨γ₂,slice₂.rank.1⟩ (bound₂ γ₂ highγ₂) ⟨x,(mt.2.2.2 x γ₂ hx).1⟩ hx
  have h₀ := ZF.modelsKP (ZFC.models_zf_l (root.native_l I hZF tree.omega))
  obtain ⟨AZ,fA,alphabetRange,alphabetBij,alphabetRest⟩ :=
    cut.alphabet_l hZF h₀ slice₂ rootMapZ.1.1.1 targetAlphabet
  -- 三个实际表项沿新根方块回到这次重启回答，再沿同一第二池返回。
  let queryEnv : Env (rt_model_l Cz ne') 12 :=
    ⟨fun i => [ι₂.bound 0,ι₂.bound 1,ι₂.bound 27,ι₂.bound 28,ι₂.bound 26,ι₂.bound 1,ι₂.bound 1,
      rq,mq,bq,hq,qq].get i,ι₂.free⟩
  let fields : Fin 7 → Term 12 := fun i => [.bound 0,.bound 1,.bound 2,.bound 3,.bound 7,.bound 9,.bound 10].get i
  let base := Definitional.Env.substitute queryEnv fields
  have baseTruth : Formula.satisfies base tg_reply_base0_m :=
    (Formula.satisfies_bind queryEnv fields tg_reply_base0_m).mp
      ((Formula.satisfies_conj_iff ..).mp ((Formula.satisfies_conj_iff ..).mp queryRow).1).2
  have facts := language
  simp only [tg_reply_language0_m,Formula.satisfies_conj_iff,Formula.satisfies_mem_iff] at facts
  let wz : Zn.Domain := ⟨w₂,current.omega_mem⟩
  let Vgz : Zn.Domain := ⟨Vγ₂,slice₂.rank.2.1⟩
  have omegaZ := numbers₂.omega_l I (ZF.modelsKP hZF) tree.omega hZ.1
  have hwz : (ι₂.bound 0).val = wz := Subtype.ext eqω
  have finiteNZ : Zn.mem (ι₂.bound 28).val wz := finiteN
  have rankGz := (rr_rank_native_l I mt.2.1 hZ ⟨γ₂,slice₂.rank.1⟩ Vgz).mp slice₂.rank
  have lowNat (x : Zn.Domain) (hx : Zn.mem x wz) : Zn.mem x Vgz :=
    v_transitive_l (kp_pair_l hZ) rankGz wz omegaSlice₂ x hx
  have lowBase : ∀ i : Fin 4, Zn.mem (base.bound (i.castAdd 3)).val Vgz :=
    Fin.cases (hwz.symm ▸ omegaSlice₂)
      (Fin.cases (lowNat _ (omegaZ.transitive hZ _ finiteNZ _ facts.2.1))
        (Fin.cases (lowNat _ (omegaZ.transitive hZ _ finiteNZ _ facts.2.2.1))
          (Fin.cases (lowNat _ finiteNZ) (fun i => Fin.elim0 i))))
  have basePoints : ∀ i : Fin 4, Rd_entry_d (ρ₂.bound ([16,17,23,24].get i)).val.val
      (base.bound (i.castAdd 3)).val.val t₃ :=
    Fin.cases (pointBase 0) (Fin.cases (pointBase 1)
      (Fin.cases (pointBase 2) (Fin.cases (pointBase 3) (fun i => Fin.elim0 i))))
  have members := sliceP.reply_members_l hZF slice₂ roots₂ tree.omega root.model mp mt rootMapP rootMapZ
    fp.transitive nd ne' hZ wz (replyEnv.bound 9).val omegaZ fz (saved₂.context.kernel_l mp.2.1 nd)
    ρ₂ round₂ base hwz finiteNZ lowBase baseTruth ft₃ restrict₃ pred₃ basePoints
      ((restrict₃.2 _ _).mp type).2
  have rankCz := (rr_rank_native_l I mt.2.1 hZ ⟨η₂,current.height⟩ Cz).mp ((rr_rank_truth_l I).mpr current.rank)
  have limitCz : Zn.IsLimitOrdinal ⟨η₂,current.height⟩ := (Formula.satisfies_isLimitOrdinal_iff ..).mp
    ((rr_truth_native_l I mt.2.1 (Formula.isLimitOrdinal .newest)
      (by simp -implicitDefEqProofs) (fun _ : Fin 1 => (⟨η₂,current.height⟩ : Zn.Domain))).mp current.limit)
  have tableReply := tg_reply_table_l targetZF omegaZ rankCz limitCz fz ne' replyEnv finiteL reflected
    rq bq hq members.1 members.2.1 members.2.2
  let answer : Env (rt_model_l Cz ne') 22 :=
    ⟨fun i => [ι₂.bound 0,ι₂.bound 27,ι₂.bound 28,ι₂.bound 24,replyEnv.bound 4,
      ι₂.bound 30,ι₂.bound 31,Dq,ι₂.bound 25,replyEnv.bound 9,ι₂.bound 36,ι₂.bound 37,rq,bq,hq,
      ι₂.bound 38,ι₂.bound 39,ι₂.bound 40,ι₂.bound 41,ι₂.bound 42,ι₂.bound 43,ι₂.bound 44].get i,
      fun _ => ι₂.bound 0⟩
  have aligned : (tg_reply_table_env_d replyEnv rq bq hq).bound = answer.bound := by
    funext i
    exact Fin.cases (sameReply 0).symm (Fin.cases (sameReply 1).symm (Fin.cases (sameReply 2).symm
      (Fin.cases (sameReply 3).symm (Fin.cases rfl (Fin.cases (sameReply 4).symm
        (Fin.cases (sameReply 5).symm (Fin.cases domainEq.symm (Fin.cases (sameReply 6).symm
          (Fin.cases rfl (Fin.cases (sameReply 7).symm (Fin.cases (sameReply 8).symm
            (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases (sameReply 9).symm
              (Fin.cases (sameReply 10).symm (Fin.cases (sameReply 11).symm (Fin.cases (sameReply 12).symm
                (Fin.cases (sameReply 13).symm (Fin.cases (sameReply 14).symm
                  (Fin.cases (sameReply 15).symm (fun i => Fin.elim0 i)))))))))))))))))))))) i
  have answerTruth := (Formula.closed_env_l tg_reply0_m tg_reply0_closed_l aligned).mp tableReply
  have requestTruth : Formula.satisfies
      (⟨fun i => [ι₂.bound 0,replyEnv.bound 4,ι₂.bound 26,ι₂.bound 1,ι₂.bound 1].get i,
        fun _ => ι₂.bound 0⟩ : Env (rt_model_l Cz ne') 5) tg_query_request0_m :=
    (Formula.closed_env_l tg_query_request0_m tg_query_request0_closed_l rfl).mp key
  -- 新保存短图先沿第一根层定位，再由第二工厂的同一低方块识别原边像。
  let Vgp : Pn.Domain := ⟨Vγp,sliceP.rank.2.1⟩
  have rankGp := (rr_rank_native_l I mp.2.1 hP ⟨γp,sliceP.rank.1⟩ Vgp).mp sliceP.rank
  have shortLow : Pn.mem (ρ₂.bound 40).val Vgp :=
    (first.pred Vγ Vγp iVγ (ρ₂.bound 40).val.val).mpr ⟨s₀.val,lowShort,shortPoint⟩
  have lowK := (KP.v_compare_l hP rankGp rankKκ (fun x hx => lower₂ x.val hx)).1
  have shortBack : Rd_entry_d (ρ₂.bound 40).val.val s₀.val kback :=
    (inverse _ _).mpr shortPoint
  obtain ⟨sZ,_,shortEdge⟩ := embed₂.1.1.2.2 s₀.val s₀.property
  have shortImage : Rd_entry_d (ρ₂.bound 40).val.val sZ gc :=
    (lowSquare₂ (ρ₂.bound 40).val s₀.val sZ (lowK _ shortLow) shortBack).mpr shortEdge
  have shortPlay := queryPlay.map_l I hZF tree.omega mn mt embed₂ iC (points 4) (points 3) (points 20) shortEdge
  -- 原轮号和原前缀只沿实际 parent 边搬运，当前模型并非第二施加的所属模型。
  have digits := (request.numbers.omega_map_l I hZF tree.omega mn mt embed₂ sourceZc.ext certificateZ.ext numbers₂).2
  have indexPoint : Rd_entry_d k (ι₂.bound 19).val.val z₂ := by
    obtain ⟨n',_,nn'⟩ := numbers₂.injection.1.2.2 k request.finite
    have ni := digits k (v 19) n' request.index nn'
    exact embed₂.1.1.1.2 (v 19) n' _ ni (currentPoints 19) ▸ nn'
  obtain ⟨k',index⟩ := tg_round_index_l I (ZF.modelsKP hZF) tree.omega mt.2.1 hZ.1 wz
    (ι₂.bound 19).val numbers₂ ((numbers₂.image _).mpr ⟨k,request.finite,indexPoint⟩)
  have indexEq := numbers₂.injection.2 k' k (ι₂.bound 19).val.val index.point indexPoint
  subst k'
  have letters x (hx : M.mem x A) : ∃ y, M.mem y N ∧ Rd_entry_d x y q := by
    have ha := (cut.carrier A₀).mpr ⟨(cut.model.2.2.2 A₀ B₀ cut.alphabet).1,cut.alphabet⟩
    have hd := cut.down_l hZF h₀ A₀ x ha ((cut.letters x).mp hx).2
    obtain ⟨y,hy,xy⟩ := slice.injection.1.2.2 x hd
    exact ⟨y,hy,slice.root x y xy⟩
  have play := prior.map_l hZF tree.omega mn mt embed₂ sourceZc.ext certificateZ.ext request.numbers numbers₂
    letters (tree.omega.transitive (ZF.modelsKP hZF) k request.finite) rootMapZ.1.1.1
    (fun x y z xy yz => (rootComp.2 x z).mpr ⟨y,xy,yz⟩) iC (currentPoints 4) (currentPoints 3) (currentPoints 20)
  have trace := current.trace_image_l hZF tree.omega mn mt embed₂ hZ sourceZc.ext request.numbers numbers₂ ne'
    (ι₂.bound 4) (ι₂.bound 1) (ι₂.bound 2) (ι₂.bound 3) (ι₂.bound 20) iw iC
    (currentPoints 4) (currentPoints 1) (currentPoints 2) (currentPoints 3) (currentPoints 20)
  have oldViews := request.views.advance_l hZF first second mn mp mt hN hP hZ.1
    (ρ₂.bound 21).val Kκ rankKκ point highτ κL
    ((eq 24).symm ▸ request.below) inverse
    (fun x y E hx xy => lowSquare₂ x y E hx xy) rootComp trace
    (ι₂.bound 20).property (fun _ _ hx => hx)
  -- 第二条原边的 parent 是原 n，owner 是第一次新结点 m；支撑恰追加新保存的 L₂。
  have parentNode := extension₁.2.2.1 n c qn
  have parentRoot := (extension₁.2.2.2.1 o n q hm.predecessor_mem).mpr request.origin
  obtain ⟨θ₂,T₂,Q₂,G₂,E₂,tree₂,extension₂,node₂,edge₂,move₂,root₂⟩ :=
    extend₂ θ m T₁ Q₁ G₁ E₁ n o tree₁ extension₁.1 node₁ parentNode parentRoot
  obtain ⟨Λ₂,lf₂,levels₂,entries₂⟩ := tree₁.levels_extend_l hZF extension₁.1 lf₁ levels₁
    tree₂ extension₂ move₂ payload₂
  have critical (old : Tg_raw_critical_d I X₀ R₀ γ₀ D₀ C₀ o Q G E) :
      Tg_raw_critical_d I X₀ R₀ γ₀ D₀ C₀ o Q₂ G₂ E₂ :=
    extension₂.raw_critical_apply_l I (ZF.modelsKP hZF)
      (fun i c hi => (tree₁.diagram.model_domain i).mpr ⟨c,hi⟩) (critical₁ old) tree₂.move_function
      move₂ payload₂ (extension₂.2.2.1 m d node₁) mp
      ((extension₂.2.2.2.1 o m q₁ extension₁.1.predecessor_mem).mpr root₁) sliceP lower₂
  let frame : Tg_raw_archive_frame_d M.Domain := ⟨o,θ,Q₂,G₂,Λ₂⟩
  let newRow : Tg_raw_archive_row_d M.Domain := ⟨m,d,P,S,wp,ηp,Cp,L₂.val,W₂.val,r₂,q₁⟩
  have rowLink : newRow.link_d frame := ⟨extension₁.1.predecessor_mem,
    extension₂.2.2.1 m d node₁,(extension₂.2.2.2.1 o m q₁ extension₁.1.predecessor_mem).mpr root₁,
    (entries₂ m L₂.val).mpr (Or.inr ⟨rfl,rfl⟩)⟩
  have oldLinks : Tg_raw_archive_links_d I frame H := request.links.extend_l I
    (fun i hi => (extension₁.1 i).mpr (Or.inl ((hm i).mpr (Or.inl hi))))
    (fun i c hi => extension₂.2.2.1 i c (extension₁.2.2.1 i c hi))
    (fun i p hi hp => (extension₂.2.2.2.1 o i p ((extension₁.1 i).mpr (Or.inl ((hm i).mpr (Or.inl hi))))).mpr
      ((extension₁.2.2.2.1 o i p ((hm i).mpr (Or.inl hi))).mpr hp))
    (fun i μ hi => (entries₂ i μ).mpr (Or.inl (keepLevels i μ hi)))
  have answered := current.answer_raw_l (ZF.modelsKP hZF) mt.2.1 hZ ne' ι₂ issued₂ eqω ω z₂ k index
    ⟨l,second.right_rank.1⟩ (fun x hx => bound₂ x.val hx)
    (replyEnv.bound 4) (replyEnv.bound 9) Aq Uq Dq rq mq bq hq qq belowτ requestTruth table answerTruth
    X₀ R₀ γ₀ D₀ C₀ A₀ S₀ q₂ gc Vc Γc newRow frame root₂ targetName targetAlphabet rowLink name₂
    mp saved₂ ⟨zp,numbersP⟩ base₂ cofinal₂ second roots₂
    (fun i => (ρ₂.bound i).val.val) code₂ label domain type ⟨sZ,shortImage,shortPlay⟩
    γ₂ Vγ₂ tγ₂ slice₂ omegaSlice₂ lowerFinal H request.sequence oldViews oldLinks
  exact ⟨θ₂,T₂,Q₂,G₂,E₂,Λ₂,d₂,Z,R₂,j₂,q₂,p₂,tree₂,extension₂,node₂,edge₂,move₂,root₂,
    lf₂,levels₂,entries₂,rowLink,oldLinks,mt,certificateZ,embed₂,rootMapZ,rootComp,critical,
    l,Vc,Γc,gc,second,roots₂,w₂,η₂,C₂,z₂,iw,iη,iC,numbers₂,current,ne',ι₂,currentPoints,issued₂,eqω,
    index,targetName,targetAlphabet,bound₂,member₂,play,oldViews,γ₂,Vγ₂,tγ₂,slice₂,omegaSlice₂,lowerFinal,
    AZ,fA,alphabetRange,alphabetBij,alphabetRest,replyEnv.bound 4,replyEnv.bound 9,Aq,Uq,Dq,rq,mq,bq,hq,qq,
    belowτ,requestTruth,table,answerTruth,label,domain,type,⟨sZ,shortImage,shortPlay⟩,answered⟩

end YesMetaZFC.SetTheory.LargeCardinal
