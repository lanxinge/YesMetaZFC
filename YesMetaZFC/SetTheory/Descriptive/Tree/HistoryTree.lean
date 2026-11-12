import YesMetaZFC.SetTheory.Card.FiniteSequenceRecode
import YesMetaZFC.SetTheory.Descriptive.Tree.TreeTail
import YesMetaZFC.SetTheory.Descriptive.Game.ClosedDeterminacy

/-! # 字母映射下树的逆像

实际分离构造逆像树。逐项复合保留前缀，故任意内部无限列属于逆像树体，
当且仅当其像属于原树体；映射无需单射或满射。
-/
namespace YesMetaZFC.SetTheory.Descriptive
open Definitional.Project
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

def Tr_pull_d (f F T S : M.Domain) : Prop := ∀ p, M.mem p S ↔
  M.mem p F ∧ ∃ q, M.mem q T ∧ Fseq_recode_d I f p q

def tr_pull_m {d} (f F T S : Term d) : Formula 1 d := set[d] ⟪∀ p,
  p ∈ ⌜S⌝ₛ ↔ p ∈ ⌜F⌝ₛ ∧ (∃ q ∈ ⌜T⌝ₛ, ⌜fseq_recode_m (𝒞 := 𝒞)⌝ₚ(⌜f⌝ₛ,p,q))⟫
derive_free_closed tr_pull_m

theorem tr_pull_sat_l {d} (ρ : Env M d) (f F T S : Term d) :
    Formula.satisfies ρ (tr_pull_m (𝒞 := 𝒞) f F T S) ↔ Tr_pull_d I (f.eval ρ) (F.eval ρ) (T.eval ρ) (S.eval ρ) := by
  simp only [tr_pull_m, Tr_pull_d, Formula.satisfies_forall_iff, Formula.satisfies_iff_iff,
    Formula.satisfies_conj_iff, Formula.satisfies_mem_iff, Formula.satisfies_existsMem_iff,
    fseq_recode_sat_l I, Definitional.Term.eval_weaken]; rfl

theorem tr_pull_exists_l (hZF : M.Models ZF) (f F T : M.Domain) : ∃ S, Tr_pull_d I f F T S := by
  let ρ : Env M 2 := ⟨fun i => [f, T].get i, fun _ => f⟩
  let φ : UnarySchema 2 := { body := .existsE (.conj (.mem .newest (.bound 3))
    (fseq_recode_m (𝒞 := 𝒞) (.bound 2) (.bound 1) .newest)) }
  obtain ⟨S, hs⟩ := ZF.separation_exists_d hZF φ ρ F
  refine ⟨S, fun p => (hs p).trans (and_congr_right fun _ => ?_)⟩
  simp only [φ, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    Formula.satisfies_mem_iff, fseq_recode_sat_l I]; rfl

variable (hZF : M.Models ZF)
include hZF

theorem Tr_pull_d.tree_l {ω X Y f F G T S : M.Domain}
    (ff : M.IsSetFunctionFromTo I f X Y) (space : Fseq_space_d I ω X F)
    (target : Fseq_space_d I ω Y G) (tree : Tree_d G T) (pull : Tr_pull_d I f F T S) : Tree_d F S := by
  refine ⟨fun p hp => ((pull p).mp hp).1, fun p hp r hr sub => ?_⟩
  obtain ⟨_, q, hq, pq⟩ := (pull p).mp hp
  obtain ⟨n, hn, fr⟩ := (space r).mp hr
  obtain ⟨s, fs, rs⟩ := ZF.fseq_compose_l I hZF ff fr
  exact (pull r).mpr ⟨hr, s, tree.2 q hq s ((target s).mpr ⟨n, hn, fs⟩) (rs.mono_l I pq sub), rs⟩

theorem Tr_pull_d.branch_l {ω X Y f F G T S p q : M.Domain} (hw : M.IsOmega ω)
    (ff : M.IsSetFunctionFromTo I f X Y) (space : Fseq_space_d I ω X F)
    (target : Fseq_space_d I ω Y G) (pull : Tr_pull_d I f F T S)
    (fp : M.IsSetFunctionFromTo I p ω X) (pq : Fseq_recode_d I f p q) : Branch_d F S p ↔ Branch_d G T q := by
  have fq := pq.function_l I hZF ff fp
  constructor
  · intro branch r hr rq
    obtain ⟨n, hn, fr⟩ := (target r).mp hr
    obtain ⟨s, fs, sp, _⟩ := ds_prefix_l I hZF hw fp hn
    obtain ⟨v, fv, sv⟩ := ZF.fseq_compose_l I hZF ff fs
    have vq := sv.mono_l I pq ((ds_restrict_iff_l I fs fp.1).mp sp)
    have eq := ((ds_restrict_iff_l I fv fq.1).mpr vq).eq hZF.1 ((ds_restrict_iff_l I fr fq.1).mpr rq)
    obtain ⟨_, t, ht, st⟩ := (pull s).mp (branch s ((space s).mpr ⟨n, hn, fs⟩) ((ds_restrict_iff_l I fs fp.1).mp sp))
    exact (st.unique_l I hZF.1 sv).trans eq ▸ ht
  · intro branch s hs sp
    obtain ⟨n, hn, fs⟩ := (space s).mp hs
    obtain ⟨t, ft, st⟩ := ZF.fseq_compose_l I hZF ff fs
    exact (pull s).mpr ⟨hs, t, branch t ((target t).mpr ⟨n, hn, ft⟩) (st.mono_l I pq sp), st⟩

end YesMetaZFC.SetTheory.Descriptive

/-! ## 指定旧对局或指定策略的有限历史树

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
      fun ⟨hk, hs⟩ => ⟨hk, (cut.2 k a).mpr ⟨(hw.members_areOrdinals (ZF.modelsKP hZF) n hn).transitive i hin k hk, hs⟩⟩⟩⟩
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
    have fh := rh.isSetFunctionFromTo ff (hw.transitive (ZF.modelsKP hZF) i hi)
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
