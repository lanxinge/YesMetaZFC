import YesMetaZFC.SetTheory.LargeCardinal.Game.RawAnswer
import YesMetaZFC.SetTheory.LargeCardinal.Game.NativeEntry
import YesMetaZFC.SetTheory.LargeCardinal.Game.RoundParity

/-! # 原字母输入与同一次完整原请求后继

实际根图的字母限制双射把外部输入送入原回答位置，再把真实落子读回。
新前缀由同一数字图与字母图解码，事件唯一性证明它恰为旧前缀追加本次字母。
原档案追加和下一请求始终取自同一个原生落子，未重新选择运行分支。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal Descriptive
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Tg_raw_answer_result_d.input_l
    {N R w η C Ω z m χ X₀ R₀ γ₀ D₀ C₀ A₀ S₀ p H g A B t x f : M.Domain}
    (context : Tg_context_d I w N R η C) (nx : ∃ x, M.mem x N)
    (native : (smdl_structure_l I (R := R) nx).Models ZF)
    (nc : Nonempty {x : (smdl_structure_l I (R := R) nx).Domain //
      (smdl_structure_l I (R := R) nx).mem x ⟨C,context.member⟩})
    (θ : Env (rt_model_l (M := smdl_structure_l I (R := R) nx) ⟨C,context.member⟩ nc) 46)
    (τ u : (rt_model_l (M := smdl_structure_l I (R := R) nx) ⟨C,context.member⟩ nc).Domain)
    (s : Tg_raw_archive_row_d M.Domain) (frame : Tg_raw_archive_frame_d M.Domain)
    (answer : Tg_raw_answer_result_d I nx ⟨C,context.member⟩ nc
      w η Ω z m χ X₀ R₀ γ₀ D₀ C₀ A₀ S₀ p H g s frame θ τ u)
    (index : Tg_round_index_d I Ω z nx ⟨w,context.omega_mem⟩ (θ.bound 19).val m)
    (hw : (θ.bound 0).val.val = w) (injective : M.IsSetInjective I p)
    (carrier : ∀ y, M.mem y B ↔ M.mem y N ∧ Rd_entry_d y (θ.bound 6).val.val R)
    (letters : M.IsSetBijectionFromTo I t A B) (restriction : M.IsRestrictionOf I t p A)
    (prior : Tg_prefix_d I m A N R C (θ.bound 4).val.val (θ.bound 3).val.val
      (θ.bound 20).val.val z p f) (input : M.mem x A) :
    ∃ m' H' r' r y f',
    ∃ ε : Env (rt_model_l (M := smdl_structure_l I (R := R) nx) ⟨C,context.member⟩ nc) 46,
      M.SuccessorOf m' m ∧ M.mem y A ∧ (Gm_even_d I Ω m → y = x) ∧
      (∀ i : Fin 19, ε.bound (i.castAdd 27) = θ.bound (i.castAdd 27)) ∧
      Tg_raw_request_d I Ω S₀ X₀ R₀ γ₀ D₀ C₀ A₀ N R w η C χ z m' H' r' p frame
        (fun i => (ε.bound i).val.val) ∧
      Rt_tuple_d s.values_d r ∧
      (∀ l a, M.PairMember I l a H' ↔ M.PairMember I l a H ∨ l = m ∧ a = r) ∧
      Tg_prefix_d I m' A N R C (ε.bound 4).val.val (ε.bound 3).val.val (ε.bound 20).val.val z p f' ∧
      Fseq_end_d I Ω f' f y ∧
      (smdl_structure_l I (R := R) nx).MemberSubset (θ.bound 20).val (ε.bound 20).val ∧
      (θ.bound 20).val ≠ (ε.bound 20).val := by
  let Nn := smdl_structure_l I (R := R) nx
  let Cn : Nn.Domain := ⟨C,context.member⟩
  let P := rt_model_l Cn nc
  have fs := context.finite_l nx native.1
  let J := rt_pair_l fs.transitive nc native.1 fs.pair
  have ext := rt_model_ext_l native.1 fs.transitive nc
  obtain ⟨y,hy,xy⟩ := letters.1.1.2.2 x input
  have hy₀ := (carrier y).mp hy
  let a : P.Domain := ⟨⟨y,hy₀.1⟩,fs.transitive (θ.bound 6).val (θ.bound 6).property ⟨y,hy₀.1⟩ hy₀.2⟩
  have point : Rd_entry_d x a.val.val p := ((restriction.2 x y).mp xy).2
  obtain ⟨v,h,j,_,position,_,_,_,moves⟩ := answer
  obtain ⟨y',h',j',n',hy',even,_,digit,_,_,ε,head,_,issued,_,aux,growth,keep,proper,_,_,
    m',H',r',r,successor,future,code,entries,next⟩ := moves a hy₀.2
  have control (i : Fin 19) : ε.bound (i.castAdd 27) = θ.bound (i.castAdd 27) := by
    simpa only [tg_position_env_d,Fin.addCases_left] using head i
  have same (i : Fin 19) : (ε.bound (i.castAdd 27)).val.val = (θ.bound (i.castAdd 27)).val.val :=
    congrArg (fun a => a.val.val) (control i)
  have range b : M.mem b B ↔ M.mem b N ∧ Rd_entry_d b (ε.bound 6).val.val R := by
    simpa only [show (ε.bound 6).val.val = (θ.bound 6).val.val from same 6] using carrier b
  obtain ⟨f',play⟩ := context.prefix_l hZF nx native.1 nc ε issued next.numbers next.index
    range letters restriction
  have hyB : M.mem y'.val.val B := (carrier _).mpr ⟨y'.val.property,hy'⟩
  obtain ⟨y₀,hyA,value⟩ := letters.2 y'.val.val hyB
  have played : Rd_entry_d y₀ y'.val.val p := ((restriction.2 y₀ y'.val.val).mp value).2
  let ψ := tg_position_env_d
    (⟨fun i => θ.bound (i.castAdd 27),fun _ => θ.bound 0⟩ : Env P 19) (θ.bound 19) h j
  have parity := index.even_l hZF native fs nc ψ (.bound 0) (.bound 19) (Subtype.ext hw) rfl
  have event := tg_position_digit_event_l J ext ψ position
    ((fseq_end_sat_l J ext ..).mp digit) ((fseq_end_sat_l J ext ..).mp aux)
  have endt := prior.append_l hZF nx native.1 Cn fs.transitive nc J θ ε y' issued control play
    index.numbers.injection.1.1 injective index.omega index.finite successor keep index.point played event
  refine ⟨m',H',r',r,y₀,f',ε,successor,hyA,?_,control,next,code,entries,play,endt,keep,proper⟩
  intro e
  have eq := congrArg (fun a => a.val.val) (even (parity.mpr e))
  exact injective y₀ x a.val.val (Eq.mp (congrArg (fun a => Rd_entry_d y₀ a p) eq) played) point

end YesMetaZFC.SetTheory.LargeCardinal
