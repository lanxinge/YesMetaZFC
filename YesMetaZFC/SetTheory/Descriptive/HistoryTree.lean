import YesMetaZFC.SetTheory.Descriptive.GameCompletion
import YesMetaZFC.SetTheory.Descriptive.TreePullback

/-! # 指定旧对局或指定策略的有限历史树

两种树均由分离实际构造。它们的无限枝分别是指定对局，或所有服从策略
的对局；后者不预先要求策略获胜。
-/
namespace YesMetaZFC.SetTheory.Descriptive
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Cg_follows_d.prefix_l {b : Bool} {ω X J σ n s f : M.Domain} (hw : M.IsOmega ω) (hn : M.mem n ω)
    (fs : M.IsSetFunctionFromTo I s n X) (ff : M.IsSetFunction I f)
    (sub : M.MemberSubset s f) (follows : Cg_follows_d I b ω J σ f) : Cg_follows_d I b ω J σ s := by
  have cut := (ds_restrict_iff_l I fs ff).mpr sub
  intro i hi turn h rh v hv
  have hin := fs.input_mem_of_pairMember hv
  have rs : M.IsRestrictionOf I h f i := ⟨rh.1, fun k a => (rh.2 k a).trans
    ⟨fun ⟨hk, ht⟩ => ⟨hk, (cut.2 k a).mp ht |>.2⟩,
      fun ⟨hk, hs⟩ => ⟨hk, (cut.2 k a).mpr ⟨(hw.members_areOrdinals hZF n hn).transitive i hin k hk, hs⟩⟩⟩⟩
  exact follows i hi turn h rs v (hv.elim fun p hp => ⟨p, hp.1, sub p hp.2⟩)

theorem hg_strategy_exists_l (b : Bool) (ω F J σ : M.Domain) :
    ∃ S, ∀ s, M.mem s S ↔ M.mem s F ∧ Cg_follows_d I b ω J σ s := by
  let ρ : Env M 3 := ⟨fun i => [σ, J, ω].get i, fun _ => ω⟩
  let φ : UnarySchema 3 := { body := cg_follows_m b (.bound 3) (.bound 2) (.bound 1) .newest }
  obtain ⟨S, sep⟩ := ZF.separation_exists_d hZF φ ρ F
  exact ⟨S, fun s => (sep s).trans (and_congr_right fun _ => cg_follows_sat_l I hZF.1 ..)⟩

theorem hg_strategy_tree_l {b : Bool} {ω X F J σ S : M.Domain} (hw : M.IsOmega ω)
    (space : Fseq_space_d I ω X F)
    (read : ∀ s, M.mem s S ↔ M.mem s F ∧ Cg_follows_d I b ω J σ s) : Tree_d F S := by
  refine ⟨fun s hs => ((read s).mp hs).1, fun s hs t ht sub => ?_⟩
  obtain ⟨n, hn, ft⟩ := (space t).mp ht
  obtain ⟨_, _, fs⟩ := (space s).mp ((read s).mp hs).1
  exact (read t).mpr ⟨ht, ((read s).mp hs).2.prefix_l hZF hw hn ft fs.1 sub⟩

theorem hg_strategy_branch_l {b : Bool} {ω X F J σ S f : M.Domain} (hw : M.IsOmega ω)
    (space : Fseq_space_d I ω X F)
    (read : ∀ s, M.mem s S ↔ M.mem s F ∧ Cg_follows_d I b ω J σ s)
    (ff : M.IsSetFunctionFromTo I f ω X) : Branch_d F S f ↔ Cg_follows_d I b ω J σ f := by
  constructor
  · intro branch i hi turn h rh v hv
    obtain ⟨j, succ, hj⟩ := hw.1.2 i hi
    obtain ⟨t, ft, rt, _⟩ := ds_prefix_l I hZF hw ff hj
    have sub := (ds_restrict_iff_l I ft ff.1).mp rt
    have ht := branch t ((space t).mpr ⟨j, hj, ft⟩) sub
    have fh := rh.isSetFunctionFromTo ff (hw.transitive hZF i hi)
    have cut := (ds_restrict_iff_l I fh ft.1).mpr
      (ds_prefix_mono_l I fh ft.1 rh rt (fun k hk => (succ k).mpr (Or.inl hk)))
    exact ((read t).mp ht).2 i hi turn h cut v ((rt.2 i v).mpr ⟨succ.predecessor_mem, hv⟩)
  · intro follows s hs sub
    obtain ⟨n, hn, fs⟩ := (space s).mp hs
    exact (read s).mpr ⟨hs, follows.prefix_l hZF hw hn fs ff.1 sub⟩

include hZF in
theorem hg_section_exists_l (F x : M.Domain) :
    ∃ S, ∀ s, M.mem s S ↔ M.mem s F ∧ M.MemberSubset s x := by
  let ρ : Env M 1 := ⟨fun _ => x, fun _ => x⟩
  let φ : UnarySchema 1 := { body := Formula.subset .newest (.bound 1) }
  obtain ⟨S, sep⟩ := ZF.separation_exists_d hZF φ ρ F
  exact ⟨S, fun s => (sep s).trans (and_congr_right fun _ => Formula.satisfies_subset_iff ..)⟩

theorem hg_section_tree_l {F x S : M.Domain}
    (read : ∀ s, M.mem s S ↔ M.mem s F ∧ M.MemberSubset s x) : Tree_d F S :=
  ⟨fun s hs => ((read s).mp hs).1, fun s hs t ht sub =>
    (read t).mpr ⟨ht, fun p hp => ((read s).mp hs).2 p (sub p hp)⟩⟩

theorem hg_section_branch_l {ω X F x S f : M.Domain} (hw : M.IsOmega ω)
    (space : Fseq_space_d I ω X F)
    (read : ∀ s, M.mem s S ↔ M.mem s F ∧ M.MemberSubset s x)
    (fx : M.IsSetFunctionFromTo I x ω X) (ff : M.IsSetFunctionFromTo I f ω X) :
    Branch_d F S f ↔ f = x := by
  constructor
  · intro branch
    apply (ds_restrict_iff_l I ff fx.1).mpr ?_ |>.eq hZF.1
      ((ds_restrict_iff_l I fx fx.1).mpr (fun _ h => h))
    intro p hp
    obtain ⟨i, a, pair⟩ := ff.1.1 p hp
    have ia : Rd_entry_d i a f := ⟨p, pair, hp⟩
    obtain ⟨j, succ, hj⟩ := hw.1.2 i (ff.input_mem_of_pairMember ia)
    obtain ⟨s, fs, cut, _⟩ := ds_prefix_l I hZF hw ff hj
    have hs := branch s ((space s).mpr ⟨j, hj, fs⟩) ((ds_restrict_iff_l I fs ff.1).mp cut)
    obtain ⟨q, pq, hq⟩ := (cut.2 i a).mpr ⟨succ.predecessor_mem, ia⟩
    exact (I).unique pq pair ▸ ((read s).mp hs).2 q hq
  · rintro rfl s hs sub
    exact (read s).mpr ⟨hs, sub⟩

include hZF in
theorem tree_inter_exists_l (T U : M.Domain) :
    ∃ S, ∀ s, M.mem s S ↔ M.mem s T ∧ M.mem s U := by
  let ρ : Env M 1 := ⟨fun _ => U, fun _ => U⟩
  let φ : UnarySchema 1 := { body := .mem .newest (.bound 1) }
  exact ZF.separation_exists_d hZF φ ρ T

theorem tree_inter_l {F T U S : M.Domain} (t : Tree_d F T) (u : Tree_d F U)
    (read : ∀ s, M.mem s S ↔ M.mem s T ∧ M.mem s U) : Tree_d F S :=
  ⟨fun s hs => t.1 s ((read s).mp hs).1, fun s hs r hr sub =>
    (read r).mpr ⟨t.2 s ((read s).mp hs).1 r hr sub, u.2 s ((read s).mp hs).2 r hr sub⟩⟩

theorem tree_inter_branch_l {F T U S f : M.Domain}
    (read : ∀ s, M.mem s S ↔ M.mem s T ∧ M.mem s U) :
    Branch_d F S f ↔ Branch_d F T f ∧ Branch_d F U f :=
  ⟨fun h => ⟨fun s hs sub => ((read s).mp (h s hs sub)).1,
    fun s hs sub => ((read s).mp (h s hs sub)).2⟩,
    fun h s hs sub => (read s).mpr ⟨h.1 s hs sub, h.2 s hs sub⟩⟩

end YesMetaZFC.SetTheory.Descriptive
