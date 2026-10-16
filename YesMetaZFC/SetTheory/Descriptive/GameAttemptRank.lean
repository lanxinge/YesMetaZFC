import YesMetaZFC.SetTheory.Descriptive.GameControl
import YesMetaZFC.SetTheory.Descriptive.TreeRank

/-! # II 获胜策略的合法尝试树有实际序数秩

控制树的一条无限枝同时是合法对局和服从原 II 策略的对局，矛盾。
ZF＋DC 将这一无枝性转为内部良基性，再由原良基递归构造秩函数。
最终证书只检查实际函数图与有界子边，可在后继传递模型中读取。
-/
namespace YesMetaZFC.SetTheory.Descriptive
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Cg_control_d.tree_l {b : Bool} {ω e X F L G J σ R : M.Domain} (hω : M.IsOmega ω)
    (control : Cg_control_d I b ω e X F L G J σ R) : Tree_d F R := by
  refine ⟨fun s hs => ((control.legal s).mp ((control.positions s).mp hs).1).1, ?_⟩
  intro s hs t ht sub
  obtain ⟨legal, follows⟩ := (control.positions s).mp hs
  obtain ⟨n, hn, ft⟩ := (control.space t).mp ht
  obtain ⟨_, _, fs⟩ := (control.space s).mp ((control.legal s).mp legal).1
  have res := (ds_restrict_iff_l I ft fs.1).mpr sub
  refine (control.positions t).mpr ⟨control.legal.prefix_l legal ht sub, ?_⟩
  intro i hi turn h rh v hv
  have hin := ft.input_mem_of_pairMember hv
  have rs : M.IsRestrictionOf I h s i := ⟨rh.1, fun k a => (rh.2 k a).trans
    ⟨fun ⟨hk, ht⟩ => ⟨hk, (res.2 k a).mp ht |>.2⟩,
      fun ⟨hk, hs⟩ => ⟨hk, (res.2 k a).mpr ⟨(hω.members_areOrdinals hZF n hn).transitive i hin k hk, hs⟩⟩⟩⟩
  exact follows i hi turn h rs v
    (hv.elim fun p hp => ⟨p, hp.1, sub p hp.2⟩)

theorem Cg_control_d.no_branch_l {ω e X F L G J B W σ R f : M.Domain} (hω : M.IsOmega ω)
    (control : Cg_control_d I false ω e X F L G J σ R) (runs : M.IsFunctionSpace I B ω X)
    (payoff : Cg_payoff_d (M := M) ω X F L J B W) (win : Cg_win_d I false ω X F J B W σ)
    (ff : M.IsSetFunctionFromTo I f ω X) : ¬ Branch_d F R f := by
  intro branch
  have hf := (runs f).mpr ff
  have legal := payoff.all_legal_l hf (fun s hs sf =>
    control.legal.current_l ((control.positions s).mp (branch s hs sf)).1)
  apply win.2 f hf ?_ legal
  intro i hi turn h rh v hv
  obtain ⟨j, succ, hj⟩ := hω.1.2 i hi
  obtain ⟨t, ft, rt, _⟩ := ds_prefix_l I hZF hω ff hj
  have tf := (ds_restrict_iff_l I ft ff.1).mp rt
  have ht := branch t ((control.space t).mpr ⟨j, hj, ft⟩) tf
  have fh := rh.isSetFunctionFromTo ff (hω.transitive hZF i hi)
  have ht' := ds_prefix_mono_l I fh ft.1 rh rt (fun x hx => (succ x).mpr (Or.inl hx))
  exact ((control.positions t).mp ht).2 i hi turn h ((ds_restrict_iff_l I fh ft.1).mpr ht')
    v ((rt.2 i v).mpr ⟨succ.predecessor_mem, hv⟩)

theorem Cg_control_d.rank_l {ω e X F L G J B W σ R : M.Domain} (hω : M.IsOmega ω) (dc : Dc_d I ω)
    (control : Cg_control_d I false ω e X F L G J σ R) (runs : M.IsFunctionSpace I B ω X)
    (payoff : Cg_payoff_d (M := M) ω X F L J B W) (win : Cg_win_d I false ω X F J B W σ) :
    ∃ α H, Cg_rank_d ω X R α H := by
  exact tree_rank_l hZF hω dc control.space (control.tree_l hZF hω)
    (fun _ ff => control.no_branch_l hZF hω runs payoff win ff)

end YesMetaZFC.SetTheory.Descriptive
