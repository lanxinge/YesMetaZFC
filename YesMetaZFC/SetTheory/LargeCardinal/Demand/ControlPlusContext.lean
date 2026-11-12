import YesMetaZFC.SetTheory.LargeCardinal.Demand.ControlRecord
import YesMetaZFC.SetTheory.LargeCardinal.Demand.RoundScope
import YesMetaZFC.Model.SetTheory.Internal.FiniteRecordRelative
import YesMetaZFC.SetTheory.LargeCardinal.Demand.ResetControl
import YesMetaZFC.SetTheory.LargeCardinal.Demand.RankStep

/-! # 同一 II 原策略与 demanding 更新核的实际初始反射层

原控制记录和双图全称更新核进入同一个 C。实际原参数、原策略和控制集
全部保持记录坐标；既不替换策略，也不对 C 额外假定 ZF。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal Descriptive
universe u
variable {M : Structure.{u}} (hZFC : M.Models ZFC)
local notation "hZF" => ZFC.models_zf_l hZFC
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Td_game_d.control_context_l
    {p : Tg_params_d M.Domain} {A F L G J B W O Z g σ : M.Domain}
    (game : Td_game_d hZFC p A F L G J B W O Z g) (woodin : Woodin_d I p.δ) (root : M.mem p.e p.S)
    (win : Cg_win_d I false p.ω A F J B W σ) :
    ∃ H r θ X R c K η C, M.IsRegularCardinal I θ ∧ V_d I θ X ∧ Smem_d I c X R ∧
      Ic_model_d hZF p.ω p.ω K X R ∧ Td_context_d I p.ω X R η C ∧ Fs_read_d p.ω C ∧
      Rt_record_in_d td_control0_m C r ∧
      let v : Fin 19 → M.Domain := fun i =>
        [p.ω,p.e,p.a,p.b,p.c,p.δ,p.A,p.S,p.ν,p.E,p.P,p.Q,A,F,L,G,J,σ,H].get i
      Rt_tuple_d v r ∧ ∃ nc : Nonempty {x // M.mem x C}, ∃ ρ : Env (rt_model_l C nc) 19,
        (∀ i, (ρ.bound i).val = v i) ∧ Formula.satisfies ρ td_control0_m ∧ Td_kernel_d (rt_model_l C nc) := by
  obtain ⟨H,r,tuple,_,valid⟩ := game.control_record_l hZFC woodin root win
  let φ : Formula 1 1 := rt_record_m td_control0_m .newest
  have hc : φ.FreeClosed := rt_record_closed_l _ _ td_control0_closed_l rfl
  obtain ⟨θ,X,R,c,K,η,C,regular,rank,model,source,context,finite,hr,reflect⟩ :=
    td_context_l hZFC game.setup.omega r [⟨1,φ,hc⟩]
  have reflected := (reflect ⟨1,φ,hc⟩ (List.mem_cons_self ..)
    ((⟨Fin.elim0,fun _ => p.ω⟩ : Env M 0).push r) (Fin.cases hr (fun i => Fin.elim0 i))).mp valid
  have record : Rt_record_in_d td_control0_m C r := by
    apply (Formula.satisfies_conj_iff ..).mpr
    refine ⟨hr,?_⟩
    exact (Formula.closed_env_l _ (lr_rel_closed_l φ hc .newest (fun i => .bound i.succ)
      rfl (fun _ => rfl)) (ρ := ((⟨Fin.elim0,fun _ => p.ω⟩ : Env M 0).push r).push C)
      (η := ⟨Fin.cases C (fun _ => r),fun _ => C⟩)
      (funext (Fin.cases rfl (Fin.cases rfl (fun i => Fin.elim0 i))))).mp reflected
  let nc : Nonempty {x // M.mem x C} := ⟨⟨p.ω,finite.omega_mem⟩⟩
  obtain ⟨_,v,code,truth⟩ := (rt_record_in_read_l hZF.1 td_control0_m td_control0_closed_l finite.transitive nc).mp record
  have eq := rt_tuple_inj_l code tuple
  exact ⟨H,r,θ,X,R,c,K,η,C,regular,rank,model,source,context,finite,record,tuple,
    nc,⟨v,fun _ => v 0⟩,congrFun eq,truth,
    context.kernel_mem_l source.source.transitive ⟨c,model⟩ finite.transitive nc⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 同一参数域中的 reset/issue 控制合取

两条控制句均读取同一个 `Tg_params_d`。把它们在这里合取后，后续
记录只需反射一个控制对象；没有重新引入任何请求见证或额外假设。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

def td_issued_control_m {d} (p : Tg_params_d (Term d)) : Formula 1 d :=
  .conj (td_reset_control_m p) (td_issue_control_m p)

@[simp] theorem td_issued_control_closed_l {d} (p : Tg_params_d (Term d))
    (hp : p.closed_l) : (td_issued_control_m p).FreeClosed := by
  simp only [td_issued_control_m,Definitional.Formula.FreeClosed]
  exact ⟨td_reset_control_closed_l p hp,td_issue_control_closed_l p hp⟩

theorem Td_setup_d.issued_control_l (hZFC : M.Models ZFC) {d} (ρ : Env M d)
    (p : Tg_params_d (Term d)) {X : M.Domain}
    (setup : Td_setup_d hZFC (p.map_l (fun t => t.eval ρ)) X)
    (woodin : Woodin_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC)))
      (p.δ.eval ρ)) :
    Formula.satisfies ρ (td_issued_control_m p) := by
  simp only [td_issued_control_m,Formula.satisfies_conj_iff]
  exact ⟨td_reset_control_l hZFC ρ p setup woodin,setup.issue_control_l hZFC⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 原控制与 reset/issue 控制的同一记录

把三类控制句放进同一有限记录后再反射。记录的 tuple 仍是原策略、原表和
原参数的实际坐标；reset/issue 只增加同一坐标上的合法性，不改变记录编码。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal Descriptive
universe u
variable {M : Structure.{u}}

def td_issued_control0_m : Formula 1 19 :=
  td_issued_control_m (tg_control_params_d (fun i => (.bound i : Term 19)))

theorem td_issued_control0_closed_l : td_issued_control0_m.FreeClosed := by
  apply td_issued_control_closed_l
  simp only [Tg_params_d.closed_l]
  exact ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

def td_control_plus_m : Formula 1 19 :=
  .conj td_control0_m td_issued_control0_m

theorem td_control_plus_closed_l : td_control_plus_m.FreeClosed := by
  exact ⟨td_control0_closed_l,td_issued_control0_closed_l⟩

theorem Td_game_d.issued_control_l
    (hZFC : M.Models ZFC) {p : Tg_params_d M.Domain}
    {A F L G J B W O Z g σ : M.Domain}
    (game : Td_game_d hZFC p A F L G J B W O Z g)
    (tail : M.Domain)
    (woodin : Woodin_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) p.δ)
    (root : M.mem p.e p.S)
    (win : Cg_win_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) false p.ω A F J B W σ) :
    let v : Fin 19 → M.Domain := fun i =>
      [p.ω,p.e,p.a,p.b,p.c,p.δ,p.A,p.S,p.ν,p.E,p.P,p.Q,A,F,L,G,J,σ,tail].get i
    Formula.satisfies (⟨v,fun _ => p.ω⟩ : Env M 19) td_issued_control0_m := by
  let v : Fin 19 → M.Domain := fun i =>
    [p.ω,p.e,p.a,p.b,p.c,p.δ,p.A,p.S,p.ν,p.E,p.P,p.Q,A,F,L,G,J,σ,tail].get i
  let ρ : Env M 19 := ⟨v,fun _ => p.ω⟩
  let q : Tg_params_d (Term 19) := tg_control_params_d (fun i => (.bound i : Term 19))
  have hqp : q.map_l (fun t => t.eval ρ) = p := by
    cases p with
    | mk ω e a b c δ Ap Sp ν Ep Pp Qp =>
      simp [q,ρ,v,Tg_params_d.map_l,tg_control_params_d]
      change
        ([ω,e,a,b,c,δ,Ap,Sp,ν,Ep,Pp,Qp,A,F,L,G,J,σ,tail].get (3 : Fin 19) = b) ∧
        ([ω,e,a,b,c,δ,Ap,Sp,ν,Ep,Pp,Qp,A,F,L,G,J,σ,tail].get (4 : Fin 19) = c) ∧
        ([ω,e,a,b,c,δ,Ap,Sp,ν,Ep,Pp,Qp,A,F,L,G,J,σ,tail].get (5 : Fin 19) = δ) ∧
        ([ω,e,a,b,c,δ,Ap,Sp,ν,Ep,Pp,Qp,A,F,L,G,J,σ,tail].get (6 : Fin 19) = Ap) ∧
        ([ω,e,a,b,c,δ,Ap,Sp,ν,Ep,Pp,Qp,A,F,L,G,J,σ,tail].get (7 : Fin 19) = Sp) ∧
        ([ω,e,a,b,c,δ,Ap,Sp,ν,Ep,Pp,Qp,A,F,L,G,J,σ,tail].get (8 : Fin 19) = ν) ∧
        ([ω,e,a,b,c,δ,Ap,Sp,ν,Ep,Pp,Qp,A,F,L,G,J,σ,tail].get (9 : Fin 19) = Ep) ∧
        ([ω,e,a,b,c,δ,Ap,Sp,ν,Ep,Pp,Qp,A,F,L,G,J,σ,tail].get (10 : Fin 19) = Pp) ∧
        ([ω,e,a,b,c,δ,Ap,Sp,ν,Ep,Pp,Qp,A,F,L,G,J,σ,tail].get (11 : Fin 19) = Qp)
      exact ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩
  have setup : Td_setup_d hZFC (q.map_l (fun t => t.eval ρ)) A := by
    rw [hqp]
    exact game.setup
  have h := Td_setup_d.issued_control_l hZFC ρ q setup woodin
  change Formula.satisfies ρ td_issued_control0_m
  simpa [td_issued_control0_m,q] using h

theorem Td_game_d.control_plus_context_l
    (hZFC : M.Models ZFC)
    {p : Tg_params_d M.Domain} {A F L G J B W O Z g σ : M.Domain}
    (game : Td_game_d hZFC p A F L G J B W O Z g)
    (woodin : Woodin_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) p.δ)
    (root : M.mem p.e p.S)
    (win : Cg_win_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) false p.ω A F J B W σ) :
    ∃ H r θ X R c K η C, M.IsRegularCardinal
        (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) θ ∧
      V_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) θ X ∧
      Smem_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) c X R ∧
      Ic_model_d (ZFC.models_zf_l hZFC) p.ω p.ω K X R ∧
      Td_context_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) p.ω X R η C ∧
      Fs_read_d p.ω C ∧ Rt_record_in_d td_control_plus_m C r ∧
      let v : Fin 19 → M.Domain := fun i =>
        [p.ω,p.e,p.a,p.b,p.c,p.δ,p.A,p.S,p.ν,p.E,p.P,p.Q,A,F,L,G,J,σ,H].get i
      Rt_tuple_d v r ∧ ∃ nc : Nonempty {x // M.mem x C},
        ∃ ρ : Env (rt_model_l C nc) 19,
          (∀ i, (ρ.bound i).val = v i) ∧
          Formula.satisfies ρ td_control0_m ∧
          Formula.satisfies ρ td_issued_control0_m ∧
          Td_kernel_d (rt_model_l C nc) := by
  obtain ⟨H,r,tuple,control,_⟩ := game.control_record_l hZFC woodin root win
  let v : Fin 19 → M.Domain := fun i =>
    [p.ω,p.e,p.a,p.b,p.c,p.δ,p.A,p.S,p.ν,p.E,p.P,p.Q,A,F,L,G,J,σ,H].get i
  let ρ : Env M 19 := ⟨v,fun _ => p.ω⟩
  have issue : Formula.satisfies ρ td_issued_control0_m := by
    simpa [ρ,v] using Td_game_d.issued_control_l hZFC game H woodin root win
  have both : Formula.satisfies ρ td_control_plus_m :=
    (Formula.satisfies_conj_iff ..).mpr ⟨control,issue⟩
  let recordφ : Formula 1 1 := rt_record_m td_control_plus_m .newest
  have recordφ_closed : recordφ.FreeClosed :=
    rt_record_closed_l _ _ td_control_plus_closed_l rfl
  have record_valid : Formula.satisfies
      ((⟨Fin.elim0,fun _ => p.ω⟩ : Env M 0).push r) recordφ := by
    exact (rt_record_sat_l (ZFC.models_zf_l hZFC).1 _ _ _ td_control_plus_closed_l).mpr
      ⟨v,tuple,both⟩
  obtain ⟨θ,X,R,c,K,η,C,regular,rank,model,source,context,finite,hA,reflect⟩ :=
    td_context_l hZFC game.setup.omega r [⟨1,recordφ,recordφ_closed⟩]
  have reflected := (reflect ⟨1,recordφ,recordφ_closed⟩ (List.mem_cons_self ..)
    ((⟨Fin.elim0,fun _ => p.ω⟩ : Env M 0).push r)
    (Fin.cases hA (fun i => Fin.elim0 i))).mp record_valid
  have record : Rt_record_in_d td_control_plus_m C r := by
    apply (Formula.satisfies_conj_iff ..).mpr
    refine ⟨hA,?_⟩
    exact (Formula.closed_env_l _ (lr_rel_closed_l recordφ recordφ_closed .newest
      (fun i => .bound i.succ) rfl (fun _ => rfl))
      (ρ := ((⟨Fin.elim0,fun _ => p.ω⟩ : Env M 0).push r).push C)
      (η := ⟨Fin.cases C (fun _ => r),fun _ => C⟩)
      (funext (Fin.cases rfl (Fin.cases rfl (fun i => Fin.elim0 i))))).mp reflected
  let nc : Nonempty {x // M.mem x C} := ⟨⟨p.ω,finite.omega_mem⟩⟩
  obtain ⟨_,vC,code,truth⟩ :=
    (rt_record_in_read_l (ZFC.models_zf_l hZFC).1 td_control_plus_m td_control_plus_closed_l
      finite.transitive nc).mp record
  have eq := rt_tuple_inj_l code tuple
  have split := (Formula.satisfies_conj_iff ..).mp truth
  exact ⟨H,r,θ,X,R,c,K,η,C,regular,rank,model,source,context,finite,record,tuple,
    nc,⟨vC,fun _ => vC 0⟩,congrFun eq,split.1,split.2,
    context.kernel_mem_l source.source.transitive ⟨c,model⟩ finite.transitive nc⟩

end YesMetaZFC.SetTheory.LargeCardinal
