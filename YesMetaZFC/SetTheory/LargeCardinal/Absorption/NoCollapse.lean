import YesMetaZFC.SetTheory.LargeCardinal.Absorption.Guard
import YesMetaZFC.SetTheory.LargeCardinal.Absorption.Trace
import YesMetaZFC.Model.Forcing.Order.GenericTreeGround
import YesMetaZFC.SetTheory.Descriptive.Demand.DemandCounterWeave
import YesMetaZFC.SetTheory.LargeCardinal.Absorption.BranchGeneric
import YesMetaZFC.Model.Forcing.Collapse.NameCode
import YesMetaZFC.Model.SetTheory.Demand.Separated
import YesMetaZFC.Model.SetTheory.Demand.Untag
import YesMetaZFC.Model.Forcing.Collapse.AbsorptionProduct
import YesMetaZFC.Model.Forcing.Ground.TreeShift
import YesMetaZFC.SetTheory.DependentChoice
import YesMetaZFC.SetTheory.Descriptive.Game.GameAttemptRank
import YesMetaZFC.SetTheory.Descriptive.Tree.TreeWellFounded
import YesMetaZFC.SetTheory.LargeCardinal.Demand.UntagGeneral
import YesMetaZFC.SetTheory.LargeCardinal.Demand.Corollary712
import YesMetaZFC.Model.Forcing.Ground.PowerGeneric

/-! # 延迟一轮的应答保持内部不变量

第零项选函数名字；正项读取前一稠密名字及前一大条件。
前一项仍是名字时使用泛型中的固定初始条件，其后沿统一应答函数加强。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project Descriptive InnerModel Internal Model.Forcing.Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Ag_guard_d.append_l {ω b τ g U H Γ n A V a v a' v' d r : M.Domain}
    (guard : Ag_guard_d b τ g U H Γ a v) (hw : M.IsOmega ω) (hn : M.mem n ω)
    (fa : Fn0_d n A a) (fv : Fn0_d n V v)
    (ea : Fseq_end_d I ω a' a d) (ev : Fseq_end_d I ω v' v r)
    (name : (n = b → r = τ) ∧ (n ≠ b → M.mem r g))
    (decrease : ∀ i t, M.SuccessorOf n i → Entry_d M i t v → i ≠ b → Entry_d M r t U)
    (hit : ∀ i e, M.SuccessorOf n i → Entry_d M i e a → Ag_safe_d H Γ e r) :
    Ag_guard_d b τ g U H Γ a' v' := by
  have ra := ea.entries_l I hZF.1 (fn0_function_l (ZF.modelsKP hZF) fa).2.1
  have rv := ev.entries_l I hZF.1 (fn0_function_l (ZF.modelsKP hZF) fv).2.1
  have earlier {i k} (ki : M.SuccessorOf k i) (hk : M.mem k n ∨ k = n) : M.mem i n :=
    hk.elim (fun hk => (hw.members_areOrdinals (ZF.modelsKP hZF) n hn).transitive k hk i ki.predecessor_mem)
      (fun eq => eq ▸ ki.predecessor_mem)
  have oldv {k i t} (ki : M.SuccessorOf k i) (hk : M.mem k n ∨ k = n)
      (it : Entry_d M i t v') : Entry_d M i t v := by
    rcases (rv i t).mp it with it | ⟨eq,_⟩
    · exact it
    · exact (KP.mem_irrefl_d (ZF.modelsKP hZF) n (eq ▸ earlier ki hk)).elim
  refine ⟨?_,?_,?_⟩
  · intro i t it
    rcases (rv i t).mp it with it | ⟨rfl,rfl⟩
    · exact guard.names i t it
    · exact name
  · intro k i t z kt iz ki nz
    rcases (rv k t).mp kt with kt | ⟨rfl,rfl⟩
    · exact guard.decreasing k i t z kt (oldv ki (Or.inl (fv.bound_l kt).1) iz) ki nz
    · exact decrease i z ki (oldv ki (Or.inr rfl) iz) nz
  · intro i e k t ie kt ki
    have use (hk : M.mem k n ∨ k = n) : Entry_d M i e a := by
      rcases (ra i e).mp ie with ie | ⟨eq,_⟩
      · exact ie
      · exact (KP.mem_irrefl_d (ZF.modelsKP hZF) n (eq ▸ earlier ki hk)).elim
    rcases (rv k t).mp kt with kt | ⟨rfl,rfl⟩
    · exact guard.dense i e k t (use (Or.inl (fv.bound_l kt).1)) kt ki
    · exact hit i e ki (use (Or.inr rfl))

theorem Ag_guard_d.reply_l {ω b τ g U H Γ D V B F n a v r₀ : M.Domain}
    (guard : Ag_guard_d b τ g U H Γ a v) (hw : M.IsOmega ω) (empty : ∀ z, ¬ M.mem z b)
    (hn : M.mem n ω) (fa : Fn0_d n D a) (fv : Fn0_d n V v)
    (hτ : M.mem τ V) (bound : M.MemberSubset g V) (start : M.mem r₀ g)
    (prod : M.IsCartesianProduct I B D g) (fn : Fn0_d B g F)
    (reply : ∀ d r z s, KPair_d M z d r → Entry_d M z s F → Entry_d M s r U ∧ Ag_safe_d H Γ d s) :
    ∃ r, M.mem r V ∧ ∀ d a' v', Fseq_end_d I ω a' a d → Fseq_end_d I ω v' v r →
      Ag_guard_d b τ g U H Γ a' v' := by
  classical
  by_cases zero : n = b
  · refine ⟨τ,hτ,fun d a' v' ea ev => guard.append_l hZF hw hn fa fv ea ev ⟨fun _ => rfl,fun ne => (ne zero).elim⟩ ?_ ?_⟩
    · intro i _ ni
      exact (empty i (zero ▸ ni.predecessor_mem)).elim
    · intro i _ ni
      exact (empty i (zero ▸ ni.predecessor_mem)).elim
  · have ne : ∃ i, M.mem i n := by
      apply Classical.byContradiction
      intro no
      exact zero (hZF.1.eq_of_same_members n b (fun i => iff_of_false (fun hi => no ⟨i,hi⟩) (empty i)))
    obtain ⟨i,hi,ni⟩ := hw.exists_predecessor_of_mem_of_nonempty hZF hn ne
    obtain ⟨d,hd,id⟩ := fa.2.1 i ni.predecessor_mem
    obtain ⟨t,_,it⟩ := fv.2.1 i ni.predecessor_mem
    have choose : ∃ r, M.mem r g ∧ Ag_safe_d H Γ d r ∧ (i ≠ b → Entry_d M r t U) := by
      by_cases first : i = b
      · obtain ⟨z,pair⟩ := (I).total d r₀
        obtain ⟨r,hr,zr⟩ := fn.2.1 z ((prod z).mpr ⟨d,hd,r₀,start,pair⟩)
        exact ⟨r,hr,(reply d r₀ z r pair zr).2,fun ne => (ne first).elim⟩
      · obtain ⟨z,pair⟩ := (I).total d t
        obtain ⟨r,hr,zr⟩ := fn.2.1 z ((prod z).mpr ⟨d,hd,t,(guard.names i t it).2 first,pair⟩)
        exact ⟨r,hr,(reply d t z r pair zr).2,fun _ => (reply d t z r pair zr).1⟩
    obtain ⟨r,hr,safe,decr⟩ := choose
    refine ⟨r,bound r hr,fun d' a' v' ea ev => guard.append_l hZF hw hn fa fv ea ev
      ⟨fun eq => (zero eq).elim,fun _ => hr⟩ ?_ ?_⟩
    · intro k z nk kz nz
      have eq := ni.predecessor_eq hZF.1 (hw.members_areOrdinals (ZF.modelsKP hZF) i hi) nk
      subst k
      exact (fn0_function_l (ZF.modelsKP hZF) fv).1.2 i t z it kz ▸ decr nz
    · intro k e nk ke
      have eq := ni.predecessor_eq hZF.1 (hw.members_areOrdinals (ZF.modelsKP hZF) i hi) nk
      subst k
      exact (fn0_function_l (ZF.modelsKP hZF) fa).1.2 i d e id ke ▸ safe

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 枚举对局生成命中同一稠密族的实际小滤子 -/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project Descriptive InnerModel Internal Model.Forcing.Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Ag_game_d.enumerated_filter_l {ω X Q T D P A F R e σ : M.Domain}
    (game : Ag_game_d hZF ω X Q T D P A F R) (hw : M.IsOmega ω)
    (O : Cond_order_d M Q T Q) (ef : Fn0_d ω D e) (onto : M.IsSetSurjectiveOnto I e ω D)
    (first : Gt_strategy_d hZF true ω A R σ) :
    ∃ f x q H, Fn0_d ω A f ∧ Branch_d F R f ∧ Gm_follows_d I true ω σ f ∧
      Fn0_d ω X x ∧ Fn0_d ω Q q ∧
      (∀ k n a y p, M.mem k ω → M.IsOrdinalAddition I n k k → Rd_entry_d n a f →
        KPair_d M a y p → Rd_entry_d k y x ∧ Rd_entry_d k p q) ∧
      (∀ p, M.mem p H ↔ M.mem p Q ∧ ∃ i r, Rd_entry_d i r q ∧ Entry_d M r p T) ∧
      Gset_d Q T Q D H := by
  obtain ⟨f,ff,branch,played,schedule⟩ := game.enumerated_play_l hZF hw ef first
  obtain ⟨x,q,fx,fq,coords⟩ := game.coordinates_l hZF hw ff branch
  obtain ⟨step,hits⟩ := game.chain_meets_l hZF hw ff branch fx fq coords ef onto schedule
  obtain ⟨H,members,filter,_⟩ := sequence_filter_l hZF O hw (fn0_function_l (ZF.modelsKP hZF) fq) step hits
  exact ⟨f,x,q,H,ff,branch,played,fx,fq,coords,members,filter⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 满足应答不变量的完整辅助轮

同一交替历史拆成两个同长度图。完整轮谓词只含实际模型内参数，
可用于分离先手控制树中可继续应答的局面。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project Descriptive InnerModel Internal Model.Forcing.Internal
universe u
variable {M : Structure.{u}} (I : kpair_convention_l.Interpretation M)

def Ag_round_d (ω D V A b τ g U H Γ h : M.Domain) : Prop := ∃ k n a v,
  M.mem k ω ∧ M.IsOrdinalAddition I n k k ∧ Fn0_d n A h ∧ Fn0_d k D a ∧ Fn0_d k V v ∧
    Dg_weave_d I ω h a v ∧ Ag_guard_d b τ g U H Γ a v

def ag_round_m {d} (ω D V A b τ g U H Γ h : Term d) : Formula 1 d := set[d] ⟪∃ k n a v,
  k ∈ ⌜ω⌝ₛ ∧ ⌜(Formula.isOrdinalAddition kpair_convention_l)⌝ₚ(n,k,k) ∧
    ⌜fn0_m⌝ₚ(n,⌜A⌝ₛ,⌜h⌝ₛ) ∧ ⌜fn0_m⌝ₚ(k,⌜D⌝ₛ,a) ∧ ⌜fn0_m⌝ₚ(k,⌜V⌝ₛ,v) ∧
    ⌜dg_weave_m⌝ₚ(⌜ω⌝ₛ,⌜h⌝ₛ,a,v) ∧
    ⌜ag_guard_m⌝ₚ(⌜b⌝ₛ,⌜τ⌝ₛ,⌜g⌝ₛ,⌜U⌝ₛ,⌜H⌝ₛ,⌜Γ⌝ₛ,a,v)⟫
derive_free_closed ag_round_m

theorem ag_round_sat_l (hE : Extensional M) {d} (ρ : Env M d) (ω D V A b τ g U H Γ h : Term d) :
    Formula.satisfies ρ (ag_round_m ω D V A b τ g U H Γ h) ↔
      Ag_round_d I (ω.eval ρ) (D.eval ρ) (V.eval ρ) (A.eval ρ) (b.eval ρ) (τ.eval ρ)
        (g.eval ρ) (U.eval ρ) (H.eval ρ) (Γ.eval ρ) (h.eval ρ) := by
  simp only [ag_round_m,Ag_round_d,Formula.satisfies_exists_iff,Formula.satisfies_conj_iff,
    Formula.satisfies_mem_iff,Formula.satisfies_isOrdinalAddition_iff I hE,fn0_sat_l hE,
    dg_weave_sat_l I hE,ag_guard_sat_l hE,Definitional.Term.eval_weaken]
  rfl

theorem ag_round_root_l (hZF : M.Models ZF) {ω D V A b τ g U H Γ : M.Domain}
    (hw : M.IsOmega ω) (empty : ∀ z, ¬ M.mem z b) :
    Ag_round_d (kp_pair_l (ZF.modelsKP hZF)) ω D V A b τ g U H Γ b := by
  let J := kp_pair_l (ZF.modelsKP hZF)
  have no i x : ¬ Entry_d M i x b := fun ⟨z,_,hz⟩ => empty z hz
  have ff X : Fn0_d b X b := fn0_of_function_l (ZF.modelsKP hZF) (ds_empty_fun_l J empty)
  refine ⟨b,b,b,b,num_mem_l hZF.1 hw (show Num_d 0 b from empty),?_,ff A,ff D,ff V,?_,?_⟩
  · exact (ZF.ordinalAddition_zero_iff hZF J empty).mpr rfl
  · exact ⟨fun i _ x => iff_of_false (no i x) (fun ⟨j,_,jx⟩ => no j x jx),
      fun i _ x => iff_of_false (no i x) (fun ⟨j,l,_,_,lx⟩ => no l x lx)⟩
  · exact ⟨fun i r ir => (no i r ir).elim,fun i _ r _ ir => (no i r ir).elim,
      fun i d _ _ id => (no i d id).elim⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 原小坍缩稠密集族在大扩张中的可数性

κ<δ 给出有限 κ 列条件域的 δ 以下大小界；强极限性质再控制它的旧幂集。
因此原稠密集族可在大坍缩扩张内枚举，而非假定整个地模型可数。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal Model.Forcing.Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Ag_system_d.dense_bound_l {ω κ δ X : M.Domain} {p : Ag_forcing_d hZF ω κ δ X}
    (s : Ag_system_d hZF p) (hw : M.IsOmega ω) (above : M.mem ω δ)
    (strong : M.IsStrongLimitCardinal I δ) (small : M.mem κ δ) :
    ∃ μ, M.mem μ δ ∧ M.CardinalLessOrEqual I s.E μ := by
  obtain ⟨ν,hν,infinite,bound,_⟩ := ZF.common_cardinal_l I hZF strong.1.1 above small small
  have size := ZF.fseq_bound_l I hZF hw infinite bound p.small_space
  obtain ⟨D,power⟩ := ZF.exists_powerSet hZF p.Q
  obtain ⟨μ,hμ,f,ff⟩ := ZF.strong_power_bound_l I hZF strong hν size power
  obtain ⟨g,fg⟩ := ZF.exists_inclusionInjection hZF I
    (fun E hE => (power E).mpr (fun q hq => (s.source.dense E hE).1 q hq |>.1))
  exact ⟨μ,hμ,ZF.exists_compositionInjection hZF I fg ff⟩

theorem Ag_system_d.dense_enumeration_l {ω κ δ X : M.Domain} {p : Ag_forcing_d hZF ω κ δ X}
    (s : Ag_system_d hZF p) (hw : M.IsOmega ω) (above : M.mem ω δ)
    (strong : M.IsStrongLimitCardinal I δ) (small : M.mem κ δ)
    {G : M.Domain → Prop} (generic : Generic_d M p.P p.U p.P G) {b} (hb : G b)
    (j : M.Domain → (extension_l M hZF p.P p.U p.P G).Domain) (inj : Function.Injective j)
    (full : ∀ a y, (extension_l M hZF p.P p.U p.P G).mem y (j a) ↔ ∃ x, M.mem x a ∧ j x = y)
    (checks : ∀ a t, Check_d M b a t → Qval_d M p.P p.U p.P G t (j a)) :
    let N := extension_l M hZF p.P p.U p.P G
    let hN := preserves_zf_l p.big_order hZF generic
    let J := kp_pair_l (ZF.modelsKP hN)
    ∃ e, N.IsSetFunctionFromTo J e (j ω) (j s.E) ∧ N.IsSetSurjectiveOnto J e (j ω) (j s.E) := by
  obtain ⟨μ,hμ,f,ff⟩ := s.dense_bound_l hZF hw above strong small
  obtain ⟨g,fg⟩ := ZF.exists_inclusionInjection hZF I (strong.1.1.transitive μ hμ)
  exact fseq_small_enumeration_l hZF p.big_order hw p.big_space p.big_edges
    (ZF.exists_compositionInjection hZF I ff fg) ⟨p.Q,s.source.full⟩ generic hb j inj full checks

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 大坍缩扩张中的原 I 对局及实际小泛型

实际枚举旧小条件域的稠密集族，与给定合法 I 策略对弈。所得小滤子是
大扩张中的集合，其旧条件回读满足原模型的完整泛型性，且保留同一实数列。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project Descriptive InnerModel Internal Model.Forcing.Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Ag_system_d.collapse_play_l {ω κ δ X : M.Domain} {p : Ag_forcing_d hZF ω κ δ X}
    (s : Ag_system_d hZF p) (hw : M.IsOmega ω) (above : M.mem ω δ)
    (strong : M.IsStrongLimitCardinal I δ) (small : M.mem κ δ)
    {G : M.Domain → Prop} (generic : Generic_d M p.P p.U p.P G) {b} (hb : G b)
    (j : M.Domain → (extension_l M hZF p.P p.U p.P G).Domain) (inj : Function.Injective j)
    (full : ∀ a y, (extension_l M hZF p.P p.U p.P G).mem y (j a) ↔ ∃ x, M.mem x a ∧ j x = y)
    (checks : ∀ a t, Check_d M b a t → Qval_d M p.P p.U p.P G t (j a))
    {σ : (extension_l M hZF p.P p.U p.P G).Domain}
    (first : Gt_strategy_d (preserves_zf_l p.big_order hZF generic) true (j ω) (j s.A) (j s.R₀) σ) :
    let N := extension_l M hZF p.P p.U p.P G
    let hN := preserves_zf_l p.big_order hZF generic
    let J := kp_pair_l (ZF.modelsKP hN)
    ∃ f x q H : N.Domain, Fn0_d (j ω) (j s.A) f ∧ Branch_d (j s.F₀) (j s.R₀) f ∧
      Gm_follows_d J true (j ω) σ f ∧ Fn0_d (j ω) (j X) x ∧ Fn0_d (j ω) (j p.Q) q ∧
      (∀ k n a y r, N.mem k (j ω) → N.IsOrdinalAddition J n k k → Entry_d N n a f →
        KPair_d N a y r → Entry_d N k y x ∧ Entry_d N k r q) ∧
      (∀ r, N.mem r H ↔ N.mem r (j p.Q) ∧ ∃ k t, Entry_d N k t q ∧ Entry_d N t r (j p.T)) ∧
      Gset_d (j p.Q) (j p.T) (j p.Q) (j s.E) H ∧
      N.MemberSubset H (j p.Q) ∧ Generic_d M p.Q p.T p.Q (fun r => N.mem (j r) H) := by
  let N := extension_l M hZF p.P p.U p.P G
  have hN : N.Models ZF := preserves_zf_l p.big_order hZF generic
  have omega : N.IsOmega (j ω) := image_omega_l (hEN := hN.1) j inj full hZF
    (internal_foundation_l p.big_order hZF generic) hw
    (fun D => KP.difference_exists_d (ZF.modelsKP hN) D (j ω))
  have game := s.source.image_l hZF hN j inj full hw omega
  have order := image_cond_order_l (ZF.modelsKP hZF) hN.1 j inj full p.small_order
  obtain ⟨e,ef,onto⟩ := s.dense_enumeration_l hZF hw above strong small generic hb j inj full checks
  obtain ⟨f,x,q,H,ff,branch,played,fx,fq,coords,members,filter⟩ :=
    game.enumerated_filter_l hN omega order (fn0_of_function_l (ZF.modelsKP hN) ef) onto first
  exact ⟨f,x,q,H,ff,branch,played,fx,fq,coords,members,filter,
    fun r hr => (filter.proper r hr).1,
    filter.ground_global_l hZF hN.1 j inj full p.small_order (fun E hE => (s.all_dense E).mpr hE)⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 7.23 专用树的实际分离编码及第一字母域界

原最小字母域由同一辅助树唯一确定。加标签是集合双射，因此保留
原稠密名字族到幂集的编码，并给出实际指定的首个挑战字母。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal Descriptive Model.Forcing.Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Ag_system_d.separate_l {ω κ δ X : M.Domain} {p : Ag_forcing_d hZF ω κ δ X}
    (s : Ag_system_d hZF p) (hw : M.IsOmega ω) :
    ∃ e o T U V a, e ≠ o ∧ Td_tree_d I ω s.A T ∧ Td_separated_d T ∧ Td_alphabet_d T U V ∧
      Nonempty (Td_retag_d hZF ω s.A s.S p.D s.V₀ e o T U V) ∧
      M.mem a U ∧ KPair_d M a e p.dp ∧ M.CardinalLessOrEqual I U p.K := by
  obtain ⟨e,o,U₀,V₀,T,U,V,ne,letters,tree,sep,alphabet,⟨retag⟩⟩ :=
    (s.auxiliary.demanding_l hZF s.source.space (s.source.tree_l hZF)).separate_l hZF hw
  obtain ⟨eqU,eqV⟩ := s.alphabet.ext_l hZF.1 letters
  subst U₀ V₀
  obtain ⟨a,pair⟩ := (I).total e p.dp
  obtain ⟨f,bij,_⟩ := tag_map_l hZF retag.left
  obtain ⟨g,inv,_⟩ := ZF.exists_inverseBijectionWithPairs hZF I bij
  obtain ⟨c,code⟩ := p.dense_code
  exact ⟨e,o,T,U,V,a,ne,tree,sep,alphabet,⟨retag⟩,(retag.left a).mpr ⟨p.dp,p.chosen_dense,pair⟩,pair,
    ZF.exists_compositionInjection hZF I inv.1 code⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 标签后的完整轮仍保存原应答不变量

交替历史读取标签图，而非反驳表读取未加标签的原辅助图。
两者由同域逐项编码联系，全部局面条件仍是内部可分离公式。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal Descriptive Model.Forcing.Internal
universe u
variable {M : Structure.{u}} (I : kpair_convention_l.Interpretation M)

def Ag_tag_round_d (ω D V A e o b τ g U H Γ h : M.Domain) : Prop := ∃ k n a v c d,
  M.mem k ω ∧ M.IsOrdinalAddition I n k k ∧ Fn0_d n A h ∧ Fn0_d k D a ∧ Fn0_d k V v ∧
    Tag_graph_d e a c ∧ Tag_graph_d o v d ∧ Dg_weave_d I ω h c d ∧ Ag_guard_d b τ g U H Γ a v

def ag_tag_round_m {d} (ω D V A e o b τ g U H Γ h : Term d) : Formula 1 d := set[d] ⟪∃ k n a v c d,
  k ∈ ⌜ω⌝ₛ ∧ ⌜(Formula.isOrdinalAddition kpair_convention_l)⌝ₚ(n,k,k) ∧
    ⌜fn0_m⌝ₚ(n,⌜A⌝ₛ,⌜h⌝ₛ) ∧ ⌜fn0_m⌝ₚ(k,⌜D⌝ₛ,a) ∧ ⌜fn0_m⌝ₚ(k,⌜V⌝ₛ,v) ∧
    ⌜tag_graph_m⌝ₚ(⌜e⌝ₛ,a,c) ∧ ⌜tag_graph_m⌝ₚ(⌜o⌝ₛ,v,d) ∧ ⌜dg_weave_m⌝ₚ(⌜ω⌝ₛ,⌜h⌝ₛ,c,d) ∧
    ⌜ag_guard_m⌝ₚ(⌜b⌝ₛ,⌜τ⌝ₛ,⌜g⌝ₛ,⌜U⌝ₛ,⌜H⌝ₛ,⌜Γ⌝ₛ,a,v)⟫
derive_free_closed ag_tag_round_m

theorem ag_tag_round_sat_l (hE : Extensional M) {d} (ρ : Env M d) (ω D V A e o b τ g U H Γ h : Term d) :
    Formula.satisfies ρ (ag_tag_round_m ω D V A e o b τ g U H Γ h) ↔
      Ag_tag_round_d I (ω.eval ρ) (D.eval ρ) (V.eval ρ) (A.eval ρ) (e.eval ρ) (o.eval ρ)
        (b.eval ρ) (τ.eval ρ) (g.eval ρ) (U.eval ρ) (H.eval ρ) (Γ.eval ρ) (h.eval ρ) := by
  simp only [ag_tag_round_m,Ag_tag_round_d,Formula.satisfies_exists_iff,Formula.satisfies_conj_iff,
    Formula.satisfies_mem_iff,Formula.satisfies_isOrdinalAddition_iff I hE,fn0_sat_l hE,
    tag_graph_sat_l hE,dg_weave_sat_l I hE,ag_guard_sat_l hE,Definitional.Term.eval_weaken]
  rfl

theorem ag_tag_round_root_l (hZF : M.Models ZF) {ω D V A e o b τ g U H Γ : M.Domain}
    (hw : M.IsOmega ω) (empty : ∀ z, ¬ M.mem z b) :
    Ag_tag_round_d (kp_pair_l (ZF.modelsKP hZF)) ω D V A e o b τ g U H Γ b := by
  let J := kp_pair_l (ZF.modelsKP hZF)
  have no i x : ¬ Entry_d M i x b := fun ⟨z,_,hz⟩ => empty z hz
  have ff X : Fn0_d b X b := fn0_of_function_l (ZF.modelsKP hZF) (ds_empty_fun_l J empty)
  have tag t : Tag_graph_d t b b := ⟨fun z hz => (empty z hz).elim,
    fun i z => iff_of_false (no i z) (fun ⟨x,ix,_⟩ => no i x ix)⟩
  refine ⟨b,b,b,b,b,b,num_mem_l hZF.1 hw (show Num_d 0 b from empty),
    (ZF.ordinalAddition_zero_iff hZF J empty).mpr rfl,ff A,ff D,ff V,tag e,tag o,?_,?_⟩
  · exact ⟨fun i _ x => iff_of_false (no i x) (fun ⟨j,_,jx⟩ => no j x jx),
      fun i _ x => iff_of_false (no i x) (fun ⟨j,l,_,_,lx⟩ => no l x lx)⟩
  · exact ⟨fun i r ir => (no i r ir).elim,fun i _ r _ ir => (no i r ir).elim,
      fun i d _ _ id => (no i d id).elim⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 吸收在同一原对局上的辅助应答见证

实际积同构先把指定实数搬到积扩张，再用规范函数名字族取得其名字。
大泛型的加强同时命中任意旧稠密名字，并对全部小泛型条件保持非反驳。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project Descriptive InnerModel Internal Model.Forcing.Internal
universe u v
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

structure Ag_witness_d {ω κ δ X : M.Domain} (p : Ag_forcing_d hZF ω κ δ X)
    {N : Structure.{v}} (k : M.Domain → N.Domain) (H x g : N.Domain) (τ : M.Domain) : Prop where
  name : M.mem τ p.N
  bound : N.MemberSubset g (k p.P)
  start : ∃ r, M.mem r p.P ∧ N.mem (k r) g
  step : ∀ d r, M.mem d p.D → N.mem (k r) g →
    ∃ s, M.mem s p.P ∧ N.mem (k s) g ∧ Entry_d M s r p.U ∧
      ∀ q, N.mem (k q) H → Ag_demand_d p.Q p.T p.b q s d
  values : ∀ q r n y, N.mem (k q) H → N.mem (k r) g → Entry_d N (k n) (k y) x →
    Ag_value_d p.C p.R p.c τ q r n y

theorem Ag_forcing_d.witness_l (hZFC : M.Models ZFC) {ω κ δ X : M.Domain}
    (p : Ag_forcing_d hZF ω κ δ X) (hw : M.IsOmega ω)
    (card : M.IsUncountableCardinal I ω δ) (smallκ : M.mem κ δ)
    {G : M.Domain → Prop} (generic : Generic_d M p.P p.U p.P G) {b} (hb : G b)
    (k : M.Domain → (extension_l M hZF p.P p.U p.P G).Domain) (ki : Function.Injective k)
    (full : ∀ a y, (extension_l M hZF p.P p.U p.P G).mem y (k a) ↔ ∃ c, M.mem c a ∧ k c = y)
    (checks : ∀ a t, Check_d M b a t → Qval_d M p.P p.U p.P G t (k a))
    (H x : (extension_l M hZF p.P p.U p.P G).Domain)
    (small : Generic_d M p.Q p.T p.Q (fun q => (extension_l M hZF p.P p.U p.P G).mem (k q) H))
    (bound : (extension_l M hZF p.P p.U p.P G).MemberSubset H (k p.Q))
    (real : Fn0_d (k ω) (k X) x) : ∃ g τ, Ag_witness_d hZF p k H x g τ := by
  let N := extension_l M hZF p.P p.U p.P G
  have hN : N.Models ZF := preserves_zf_l p.big_order hZF generic
  let H₀ := fun q => N.mem (k q) H
  let E := extension_l M hZF p.Q p.T p.Q H₀
  have hE : E.Models ZF := preserves_zf_l p.small_order hZF small
  have top q (hq : M.mem q p.Q) := (p.small_edges q p.b).mpr
    ⟨hq,p.small_base,fun a ha => (p.empty a ha).elim⟩
  obtain ⟨j,ji,jfull,jchecks,J,G',OJ,gg,order,i,ii,ifull,fixed,g,filter,accepted,gBound,prod,prodRule,iso⟩ :=
    fseq_product_absorption_l hZFC p.small_order p.big_order p.product_order p.product p.small_base top
      hw card smallκ p.big_space p.big_edges p.small_space generic hb k ki full checks H small bound
  let V := Prod_generic_d hZF p.C j G'
  let L := extension_l M hZF p.C p.R p.C V
  have hL : L.Models ZF := preserves_zf_l p.product_order hZF prod
  obtain ⟨a,ha⟩ := prod.inhabited
  have hc := prod.upward a p.c ha p.base_mem (p.top a (prod.proper a ha).1)
  obtain ⟨l,lc,lf,li⟩ := check_map_l p.product_order hZF prod hc
  obtain ⟨f,fmem,fi,onto,over⟩ := iso.symm_l
  have ffull a y : L.mem y (f a) ↔ ∃ c, N.mem c a ∧ f c = y := by
    obtain ⟨c,rfl⟩ := onto y
    exact ⟨fun h => ⟨c,(fmem c a).mpr h,rfl⟩,fun ⟨d,hd,eq⟩ => eq ▸ (fmem d a).mp hd⟩
  have ground a : f (k a) = l a := ((gval_check_map_l p.product_order hZF prod hc l lc a (f (k a))).mp
    ((over a (k a)).mp rfl)).symm
  have fx : L.IsSetFunctionFromTo (kp_pair_l (ZF.modelsKP hL)) (f x) (l ω) (l X) := by
    have moved : L.IsSetFunctionFromTo (kp_pair_l (ZF.modelsKP hL)) (f x) (f (k ω)) (f (k X)) :=
      image_function_l (hEN := hL.1) (hPN := KP.exists_pair (ZF.modelsKP hL)) f fi ffull
        (fn0_function_l (ZF.modelsKP hN) real)
    rw [ground ω,ground X] at moved
    exact moved
  obtain ⟨τ,hτ,valueτ⟩ := p.function_cover V prod (l ω) (l X) (f x)
    (lc ω p.t p.check_omega) (lc X p.w p.check_letters) fx
  refine ⟨g,τ,⟨hτ,gBound,?_,?_,?_⟩⟩
  · obtain ⟨r,hr⟩ := gg.inhabited
    obtain ⟨r₀,hr₀,eq⟩ := (jfull p.P r).mp (gg.proper r hr).1
    exact ⟨r₀,hr₀,(accepted r₀).mpr (eq.symm ▸ hr)⟩
  · intro d r hd hr
    have dW := ((p.dense_family d).mp hd).1
    obtain ⟨D,valueD⟩ := name_value_l (R := p.T) (z := p.Q) (U := H₀)
      (show Name_d M p.Q d from ⟨p.Wd,dW,p.dense_pool.closed⟩)
    let ρ := (ord_env_l M p.dp p.du).push d
    let η := (ord_env_l E (j p.P) (j p.U)).push D
    have values : Env_val_d hZF ρ η := by
      intro t; cases t with
      | free _ => exact jchecks p.U p.du p.check_order
      | bound n =>
        exact Fin.cases valueD
          (Fin.cases (jchecks p.P p.dp p.check_big) (fun _ => jchecks p.U p.du p.check_order)) n
    obtain ⟨q,hq⟩ := small.inhabited
    have forced := ((p.dense_family d).mp hd).2 q (small.proper q hq).1 (small.proper q hq).2
    have dense : Dense_set_d E (j p.P) (j p.U) (j p.P) D :=
      (dense_set_sat_l E hE.1 η _ _ _ _).mp
        ((forcing_truth_l p.small_order hZF small dn_s.body dn_s.freeClosed ρ η values).mp ⟨q,hq,forced⟩)
    have gr := (accepted r).mp hr
    let ζ : Env E 3 := ⟨fun n => [J,j r,D].get n,fun _ => J⟩
    let φ : UnarySchema 3 := { body := .conj (entry_m .newest (.bound 2) (.bound 1)) (.mem .newest (.bound 3)) }
    have sat s : φ.denote ζ s ↔ Entry_d E s (j r) J ∧ E.mem s D := by
      simp only [UnarySchema.denote,φ,Formula.satisfies_conj_iff,entry_sat_l E hE.1,Formula.satisfies_mem_iff]
      rfl
    obtain ⟨s,gs,sr,sD⟩ := generic_pick_l hE gg ⟨3,φ,ζ,sat⟩ gr (by
      intro t ht
      obtain ⟨s,st,sD⟩ := dense.2 t ht.1 ht.2.1
      have edge := (order s t st.1 ht.1).mp st.2.2
      exact ⟨s,⟨st.1,st.2.1,edge⟩,OJ.trans s t (j r) st.1 ht.1 (gg.proper (j r) gr).1 edge ht.2.2,sD⟩)
    obtain ⟨s₀,hs₀,eq⟩ := (jfull p.P s).mp (gg.proper s gs).1
    subst s
    have sr := (order (j s₀) (j r) (gg.proper (j s₀) gs).1 (gg.proper (j r) gr).1).mpr sr
    have sr := (image_entry_iff_l j ji jfull (KP.exists_pair (ZF.modelsKP hZF)) hE.1 s₀ r p.U).mpr sr
    exact ⟨s₀,hs₀,(accepted s₀).mpr gs,sr,fun q hq =>
      ag_demand_of_value_l hZF p.small_order small p.small_base hq j jchecks valueD sD⟩
  · intro q r n y hq hr point
    obtain ⟨s,ns,_,_⟩ := zf_check_l M hZF p.base_mem n
    obtain ⟨t,yt,_,_⟩ := zf_check_l M hZF p.base_mem y
    obtain ⟨v,pair⟩ := (I).total q r
    have rq := (small.proper q hq).1
    have rr := (image_member_l k ki full).mp (gBound (k r) hr)
    have vc := (p.product.pair v).mpr ⟨q,rq,r,rr,pair⟩
    have gv := (prodRule v).mpr ⟨vc,q,r,pair,hq,hr⟩
    let ρ : Env M 3 := ⟨fun z => [τ,s,t].get z,fun _ => τ⟩
    let η : Env L 3 := ⟨fun z => [f x,l n,l y].get z,fun _ => f x⟩
    have values : Env_val_d hZF ρ η := by
      intro z; cases z with
      | free _ => exact valueτ
      | bound z => exact Fin.cases valueτ (Fin.cases (lc n s ns) (Fin.cases (lc y t yt) (fun z => Fin.elim0 z))) z
    refine ⟨s,t,v,ns,yt,pair,fun no => ?_⟩
    have denied := (forcing_truth_l p.product_order hZF prod ag_value_body_m ag_value_body_m_freeClosed ρ η values).mp ⟨v,gv,no⟩
    have edge := (image_entry_iff_l f fi ffull (KP.exists_pair (ZF.modelsKP hN)) hL.1 (k n) (k y) x).mp point
    rw [ground n,ground y] at edge
    exact denied ((entry_sat_l L hL.1 η (.bound 1) (.bound 2) .newest).mpr edge)

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 同一坍缩 I 对局、生成小泛型与吸收名字的装配

实数、小条件列和小泛型来自同一枚举对局。吸收名字表示这个指定实数，
其大泛型加强同时供应后续辅助游戏需要的两类非反驳条件。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project Descriptive InnerModel Internal Model.Forcing.Internal
universe u
variable {M : Structure.{u}} (hZFC : M.Models ZFC)
local notation "hZF" => ZFC.models_zf_l hZFC
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Ag_system_d.collapse_witness_l {ω κ δ X : M.Domain} {p : Ag_forcing_d hZF ω κ δ X}
    (s : Ag_system_d hZF p) (hw : M.IsOmega ω) (above : M.mem ω δ)
    (strong : M.IsStrongLimitCardinal I δ) (smallκ : M.mem κ δ)
    {G : M.Domain → Prop} (generic : Generic_d M p.P p.U p.P G) {b} (hb : G b)
    (j : M.Domain → (extension_l M hZF p.P p.U p.P G).Domain) (inj : Function.Injective j)
    (full : ∀ a y, (extension_l M hZF p.P p.U p.P G).mem y (j a) ↔ ∃ x, M.mem x a ∧ j x = y)
    (checks : ∀ a t, Check_d M b a t → Qval_d M p.P p.U p.P G t (j a))
    {σ : (extension_l M hZF p.P p.U p.P G).Domain}
    (first : Gt_strategy_d (preserves_zf_l p.big_order hZF generic) true (j ω) (j s.A) (j s.R₀) σ) :
    let N := extension_l M hZF p.P p.U p.P G
    let hN := preserves_zf_l p.big_order hZF generic
    let J := kp_pair_l (ZF.modelsKP hN)
    ∃ f x q H g : N.Domain, ∃ τ : M.Domain,
      Fn0_d (j ω) (j s.A) f ∧ Branch_d (j s.F₀) (j s.R₀) f ∧ Gm_follows_d J true (j ω) σ f ∧
      Fn0_d (j ω) (j X) x ∧ Fn0_d (j ω) (j p.Q) q ∧
      (∀ k n a y r, N.mem k (j ω) → N.IsOrdinalAddition J n k k → Entry_d N n a f →
        KPair_d N a y r → Entry_d N k y x ∧ Entry_d N k r q) ∧
      (∀ r, N.mem r H ↔ N.mem r (j p.Q) ∧ ∃ k t, Entry_d N k t q ∧ Entry_d N t r (j p.T)) ∧
      N.MemberSubset H (j p.Q) ∧
      Generic_d M p.Q p.T p.Q (fun r => N.mem (j r) H) ∧ Ag_witness_d hZF p j H x g τ := by
  obtain ⟨f,x,q,H,ff,branch,played,fx,fq,coords,members,_,bound,small⟩ :=
    s.collapse_play_l hZF hw above strong smallκ generic hb j inj full checks first
  obtain ⟨g,τ,witness⟩ := p.witness_l hZF hZFC hw ⟨strong.1,above⟩ smallκ generic hb j inj full checks H x small bound fx
  exact ⟨f,x,q,H,g,τ,ff,branch,played,fx,fq,coords,members,bound,small,witness⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 内部应答不变量给出原辅助树的实际节点

先把有限三图拉回原模型。稠密要求读取旧真值表，函数值要求读取同一
原对局的实数；两者均在原模型的强迫关系中验证，再搬运已验证的节点。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project Descriptive InnerModel Internal Model.Forcing.Internal
universe u v
variable {M : Structure.{u}} {N : Structure.{v}} (hM : M.Models ZF) (hN : N.Models ZF)
  (j : M.Domain → N.Domain) (inj : Function.Injective j)
  (full : ∀ a y, N.mem y (j a) ↔ ∃ z, M.mem z a ∧ j z = y)
local notation "I" => kp_pair_l (ZF.modelsKP hM)
local notation "J" => kp_pair_l (ZF.modelsKP hN)
include inj full

theorem Ag_witness_d.guard_aux_l {ω κ δ X : M.Domain} {p : Ag_forcing_d hM ω κ δ X}
    {s : Ag_system_d hM p} (hw : M.IsOmega ω) {f x H g : N.Domain} {τ Γ : M.Domain}
    (w : Ag_witness_d hM p j H x g τ) (run : Ag_trace_d hN (j ω) (j X) (j s.A) (j s.F₀) (j s.R₀) f x H)
    (table : ∀ q r d, Ag_drel_d Γ q r d ↔ M.mem q p.Q ∧ M.mem r p.P ∧ M.mem d p.D ∧
      Ag_demand_d p.Q p.T p.b q r d)
    {h a v : M.Domain} (sub : N.MemberSubset (j h) f)
    (guard : Ag_guard_d (j p.b) (j τ) g (j p.U) H (j Γ) (j a) (j v)) :
    Ag_aux_d I ω p.Q p.T p.P p.U p.C p.R p.b p.c p.N h a v := by
  have entry := image_entry_iff_l j inj full (KP.exists_pair (ZF.modelsKP hM)) hN.1
  have edge {n y} (ny : Entry_d M n y h) : Entry_d N (j n) (j y) f :=
    ((entry n y h).mp ny).elim fun z hz => ⟨z,hz.1,sub z hz.2⟩
  have small {n y z q} (ny : Entry_d M n y h) (pair : KPair_d M y z q) (even : Gm_even_d I ω n) :=
    run.small (j n) (j y) (j z) (j q) (edge ny) (image_kpair_l j full pair)
      ((image_even_l hM hN j inj full hw).mp even)
  refine ⟨?_,?_,?_,?_⟩
  · intro i r ir
    have names := guard.names (j i) (j r) ((entry i r v).mp ir)
    refine ⟨fun eq => ?_,fun ne => ?_⟩
    · exact (inj (names.1 (congrArg j eq))).symm ▸ w.name
    · exact (image_member_l j inj full).mp (w.bound (j r) (names.2 (fun eq => ne (inj eq))))
  · intro i k r t ir kt ik nz
    exact (entry r t p.U).mpr (guard.decreasing (j i) (j k) (j r) (j t)
      ((entry i r v).mp ir) ((entry k t v).mp kt)
      (image_successor_l (hEN := hN.1) j inj full hM.1 ik) (fun eq => nz (inj eq)))
  · intro i d l r n y z q id lr li ny pair even _
    have safe := guard.dense (j i) (j d) (j l) (j r) ((entry i d a).mp id) ((entry l r v).mp lr)
      (image_successor_l (hEN := hN.1) j inj full hM.1 li)
    exact ((table q r d).mp ((ag_drel_image_l (ZF.modelsKP hM) hN.1 j inj full).mpr
      (safe (j q) (small ny pair even)))).2.2.2
  · intro n y z q r τ' i k a' t r' ny pair even nz nr bτ ia ap hk add _
    have eq := inj ((guard.names (j p.b) (j τ') ((entry p.b τ' v).mp bτ)).1 rfl)
    subst τ'
    exact w.values q r k t (small ny pair even)
      ((guard.names (j n) (j r) ((entry n r v).mp nr)).2 (fun eq => nz (inj eq)))
      (run.values (j k) (j i) (j a') (j t) (j r') ((image_member_l j inj full).mpr hk)
        (image_nat_add_l hM hN j inj full hw hk add) (edge ia) (image_kpair_l j full ap))

theorem Ag_witness_d.guard_node_l {ω κ δ X : M.Domain} {p : Ag_forcing_d hM ω κ δ X}
    {s : Ag_system_d hM p} (hw : M.IsOmega ω) (hw' : N.IsOmega (j ω))
    {f x H g : N.Domain} {τ Γ : M.Domain} (w : Ag_witness_d hM p j H x g τ)
    (run : Ag_trace_d hN (j ω) (j X) (j s.A) (j s.F₀) (j s.R₀) f x H)
    (table : ∀ q r d, Ag_drel_d Γ q r d ↔ M.mem q p.Q ∧ M.mem r p.P ∧ M.mem d p.D ∧
      Ag_demand_d p.Q p.T p.b q r d)
    {n h a v : N.Domain} (hn : N.mem n (j ω))
    (fh : Fn0_d n (j s.A) h) (fa : Fn0_d n (j p.D) a) (fv : Fn0_d n (j s.V) v)
    (sub : N.MemberSubset h f) (guard : Ag_guard_d (j p.b) (j τ) g (j p.U) H (j Γ) a v) :
    Tg_node_d J n (j s.S) h a v ∧ Fn0_d n (j s.V₀) v := by
  obtain ⟨k,h₀,hk,fh₀,eqk,eqh⟩ := image_finite_function_pull_l hM hN j inj full hw hw' hn
    (fn0_function_l (ZF.modelsKP hN) fh)
  obtain ⟨l,a₀,_,fa₀,eql,eqa⟩ := image_finite_function_pull_l hM hN j inj full hw hw' hn
    (fn0_function_l (ZF.modelsKP hN) fa)
  obtain ⟨m,v₀,_,fv₀,eqm,eqv⟩ := image_finite_function_pull_l hM hN j inj full hw hw' hn
    (fn0_function_l (ZF.modelsKP hN) fv)
  have eq := inj (eql.trans eqk.symm)
  subst l
  have eq := inj (eqm.trans eqk.symm)
  subst m n h a v
  have typedh := fn0_of_function_l (ZF.modelsKP hM) fh₀
  have typeda := fn0_of_function_l (ZF.modelsKP hM) fa₀
  have typedv := fn0_of_function_l (ZF.modelsKP hM) fv₀
  have legal : M.mem h₀ s.R₀ := (image_member_l j inj full).mp
    (run.branch (j h₀) ((image_fseq_l hM hN j inj full hw hw' s.source.space (j h₀)).mpr
      ⟨j k,hn,fn0_function_l (ZF.modelsKP hN) fh⟩) sub)
  have aux := w.guard_aux_l hM hN j inj full hw run table sub guard
  obtain ⟨_,_,q,_,_,_,join⟩ := tg_join_exists_l I hM fh₀ fa₀ fv₀
  have fq := join.typed_l hM typedh typeda typedv s.auxiliary.pair s.auxiliary.triple
  have qs := (s.auxiliary.nodes q).mpr ⟨(s.auxiliary.space q).mpr
    ⟨k,hk,fn0_function_l (ZF.modelsKP hM) fq⟩,k,h₀,a₀,v₀,hk,typedh,legal,typeda,typedv,join,aux⟩
  have node : Tg_node_d I k s.S h₀ a₀ v₀ :=
    ⟨⟨fh₀.1,fh₀.2.1⟩,⟨fa₀.1,fa₀.2.1⟩,⟨fv₀.1,fv₀.2.1⟩,q,qs,join⟩
  have fmin : M.IsSetFunctionFromTo I v₀ k s.V₀ := ⟨fv₀.1,fv₀.2.1,fun i hi => by
    obtain ⟨r,_,ir⟩ := fv₀.2.2 i hi
    exact ⟨r,(s.alphabet.node_l I hM.1 node).2 i r ir,ir⟩⟩
  refine ⟨?_,fn0_of_function_l (ZF.modelsKP hN) (image_function_l j inj full fmin)⟩
  have graph {A z} (fz : Fn0_d (j k) A z) : Tg_graph_d J (j k) z :=
    ⟨(fn0_function_l (ZF.modelsKP hN) fz).1,(fn0_function_l (ZF.modelsKP hN) fz).2.1⟩
  have fq' : N.IsSetFunctionFromTo J (j q) (j k) (j s.Y) :=
    image_function_l j inj full (fn0_function_l (ZF.modelsKP hM) fq)
  refine ⟨graph fh,graph fa,graph fv,j q,(image_member_l j inj full).mpr qs,⟨fq'.1,fq'.2.1⟩,?_⟩
  intro i hi
  obtain ⟨i₀,hi₀,eq⟩ := (full k i).mp hi
  subst i
  obtain ⟨y,d,r,t,z,iy,id,ir,tr,zt,iz⟩ := join.2 i₀ hi₀
  have entry := image_entry_iff_l j inj full (KP.exists_pair (ZF.modelsKP hM)) hN.1
  exact ⟨j y,j d,j r,j t,j z,(entry i₀ y h₀).mp iy,(entry i₀ d a₀).mp id,
    (entry i₀ r v₀).mp ir,image_kpair_l j full tr,image_kpair_l j full zt,(entry i₀ z q).mp iz⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 大扩张内部的统一应答函数

吸收见证保证每个稠密名字、当前泛型条件都有安全加强。
对原真值表的像应用内部选择，得到实际集合函数；安全性是扩张自身的公式。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project Descriptive InnerModel Internal Model.Forcing.Internal
universe u v
variable {M : Structure.{u}} (hZF : M.Models ZF)

theorem Ag_witness_d.reply_l {ω κ δ X : M.Domain} {p : Ag_forcing_d hZF ω κ δ X}
    {N : Structure.{v}} (hN : N.Models ZFC) (j : M.Domain → N.Domain) (inj : Function.Injective j)
    (full : ∀ a y, N.mem y (j a) ↔ ∃ x, M.mem x a ∧ j x = y)
    {H x g : N.Domain} {τ : M.Domain} (w : Ag_witness_d hZF p j H x g τ)
    (bound : N.MemberSubset H (j p.Q)) :
    ∃ Γ : M.Domain, ∃ B F : N.Domain,
      (∀ q r d, Ag_drel_d Γ q r d ↔ M.mem q p.Q ∧ M.mem r p.P ∧ M.mem d p.D ∧
        Ag_demand_d p.Q p.T p.b q r d) ∧
      N.IsCartesianProduct (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hN))) B (j p.D) g ∧
      Fn0_d B g F ∧ ∀ d r z s, KPair_d N z d r → Entry_d N z s F →
        Entry_d N s r (j p.U) ∧ Ag_safe_d H (j Γ) d s := by
  let hNZF := ZFC.models_zf_l hN
  let J := kp_pair_l (ZF.modelsKP hNZF)
  obtain ⟨Γ,table⟩ := ag_demand_relation_l hZF p.Q p.T p.b p.P p.D
  obtain ⟨B,prod⟩ := ZF.exists_cartesianProduct hNZF J (j p.D) g
  let ρ : Env N 3 := ⟨fun i => [j p.U,H,j Γ].get i,fun _ => H⟩
  let φ : BinarySchema 3 := { body := set[5] ⟪∃ d r,
    ⌜kpair_m⌝ₚ(⌜(.bound 1 : Term 5)⌝ₛ,d,r) ∧
      ⌜entry_m⌝ₚ(⌜(.newest : Term 5)⌝ₛ,r,⌜(.bound 2 : Term 5)⌝ₛ) ∧
      ⌜ag_safe_m⌝ₚ(⌜(.bound 3 : Term 5)⌝ₛ,⌜(.bound 4 : Term 5)⌝ₛ,d,⌜(.newest : Term 5)⌝ₛ)⟫ }
  have sat z s : φ.denote ρ z s ↔ ∃ d r,
      KPair_d N z d r ∧ Entry_d N s r (j p.U) ∧ Ag_safe_d H (j Γ) d s := by
    simp only [BinarySchema.denote,φ,Formula.satisfies_exists_iff,Formula.satisfies_conj_iff,
      kpair_sat_l N hNZF.1,entry_sat_l N hNZF.1,ag_safe_sat_l hNZF.1,Definitional.Term.eval_weaken]
    rfl
  obtain ⟨F,fn,read⟩ := ZFC.uniformize_formula_l J hN φ ρ (X := B) (Y := g) (by
    intro z hz
    obtain ⟨d,hd,r,hr,pair⟩ := (prod z).mp hz
    obtain ⟨d₀,hd₀,eqd⟩ := (full p.D d).mp hd
    obtain ⟨r₀,_,eqr⟩ := (full p.P r).mp (w.bound r hr)
    subst d r
    obtain ⟨s,hs,sg,sr,good⟩ := w.step d₀ r₀ hd₀ hr
    refine ⟨j s,sg,(sat z (j s)).mpr ⟨j d₀,j r₀,pair,
      (image_entry_iff_l j inj full (KP.exists_pair (ZF.modelsKP hZF)) hNZF.1 s r₀ p.U).mp sr,?_⟩⟩
    intro q hq
    obtain ⟨q₀,hq₀,eq⟩ := (full p.Q q).mp (bound q hq)
    subst q
    exact (ag_drel_image_l (ZF.modelsKP hZF) hNZF.1 j inj full).mp
      ((table q₀ s d₀).mpr ⟨hq₀,hs,hd₀,good q₀ hq⟩))
  refine ⟨Γ,B,F,table,prod,fn0_of_function_l (ZF.modelsKP hNZF) fn,?_⟩
  intro d r z s pair zs
  obtain ⟨d',r',pair',good⟩ := (sat z s).mp (read z s zs)
  obtain ⟨rfl,rfl⟩ := J.injective pair pair'
  exact good

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 先手控制树中安全完整轮的真延长

先读原先手策略的合法挑战，再用吸收应答函数选择大条件。
新三图在原辅助树中，因而新字母属于实际最小字母域，整个轮仍在原控制树中。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project Descriptive InnerModel Internal Model.Forcing.Internal
universe u v

theorem ag_end_length_l {M : Structure.{u}} (hZF : M.Models ZF)
    {ω n m A h t d : M.Domain} (fh : Fn0_d n A h) (ft : Fn0_d m A t)
    (end' : Fseq_end_d (kp_pair_l (ZF.modelsKP hZF)) ω t h d) : M.SuccessorOf m n := by
  obtain ⟨m',n',data⟩ := end'
  have eq := data.prefix_sequence.2.2.2.eq hZF.1 (fn0_function_l (ZF.modelsKP hZF) fh).2.1
  have eq' := data.source.2.2.2.eq hZF.1 (fn0_function_l (ZF.modelsKP hZF) ft).2.1
  exact eq' ▸ eq ▸ data.length_successor

variable {M : Structure.{u}} {N : Structure.{v}} (hM : M.Models ZF) (hN : N.Models ZF)
  (j : M.Domain → N.Domain) (inj : Function.Injective j)
  (full : ∀ a y, N.mem y (j a) ↔ ∃ z, M.mem z a ∧ j z = y)
local notation "J" => kp_pair_l (ZF.modelsKP hN)
include inj full

theorem Ag_witness_d.round_step_l {ω κ δ X : M.Domain} {p : Ag_forcing_d hM ω κ δ X}
    {s : Ag_system_d hM p} (hw : M.IsOmega ω) (hw' : N.IsOmega (j ω))
    {f x H g : N.Domain} {τ Γ : M.Domain} (w : Ag_witness_d hM p j H x g τ)
    (run : Ag_trace_d hN (j ω) (j X) (j s.A) (j s.F₀) (j s.R₀) f x H)
    (table : ∀ q r d, Ag_drel_d Γ q r d ↔ M.mem q p.Q ∧ M.mem r p.P ∧ M.mem d p.D ∧
      Ag_demand_d p.Q p.T p.b q r d)
    {B K : N.Domain} (prod : N.IsCartesianProduct J B (j p.D) g) (fn : Fn0_d B g K)
    (reply : ∀ d r z t, KPair_d N z d r → Entry_d N z t K →
      Entry_d N t r (j p.U) ∧ Ag_safe_d H (j Γ) d t)
    {V F L G T C W O e σ R h : N.Domain}
    (game : Dg_counter_d hN (j ω) (j p.D) (j s.V₀) f (j s.S) V F L G T C W O)
    (control : Cg_control_d J false (j ω) e V F L G T σ R) (hh : N.mem h R)
    (round : Ag_round_d J (j ω) (j p.D) (j s.V) V (j p.b) (j τ) g (j p.U) H (j Γ) h) :
    ∃ t, N.mem t R ∧ Ag_round_d J (j ω) (j p.D) (j s.V) V (j p.b) (j τ) g (j p.U) H (j Γ) t ∧
      N.MemberSubset h t ∧ h ≠ t := by
  obtain ⟨k,n,a,v,hk,add,fh,fa,fv,weave,guard⟩ := round
  have hn := ZF.ordinalAddition_mem_omega hN J hw' hk hk add
  obtain ⟨m,h₁,d,hm,sn,f₁,h₁R,e₁,hd⟩ := game.first_round_l hN hw' control hn fh hh ⟨k,hk,add⟩
  obtain ⟨r₀,_,start⟩ := w.start
  have empty z (hz : N.mem z (j p.b)) : False :=
    (full p.b z).mp hz |>.elim fun a ha => p.empty a ha.1
  have name : N.mem (j τ) (j s.V) := (image_member_l j inj full).mpr ((s.auxiliary.second τ).mpr (Or.inl w.name))
  have bound : N.MemberSubset g (j s.V) := by
    intro r hr
    obtain ⟨r₀,hr₀,eq⟩ := (full p.P r).mp (w.bound r hr)
    exact (full s.V r).mpr ⟨r₀,(s.auxiliary.second r₀).mpr (Or.inr hr₀),eq⟩
  obtain ⟨r,hr,extend⟩ := guard.reply_l hN hw' empty hk fa fv name bound start prod fn reply
  obtain ⟨k',a',hk',fa',ea⟩ := ZF.fseq_end_exists_l J hN hw' hk (fn0_function_l (ZF.modelsKP hN) fa) hd
  obtain ⟨l,v',_,fv',ev⟩ := ZF.fseq_end_exists_l J hN hw' hk (fn0_function_l (ZF.modelsKP hN) fv) hr
  have fa' := fn0_of_function_l (ZF.modelsKP hN) fa'
  have fv' := fn0_of_function_l (ZF.modelsKP hN) fv'
  have sk := ag_end_length_l hN fa fa' ea
  have eq := (ag_end_length_l hN fv fv' ev).eq hN.1 sk
  subst l
  have guard' := extend d a' v' ea ev
  obtain ⟨u,fu,cut,_⟩ := ds_prefix_l J hN hw' (fn0_function_l (ZF.modelsKP hN) run.play) hk'
  have sub := (ds_restrict_iff_l J fu (fn0_function_l (ZF.modelsKP hN) run.play).1).mp cut
  obtain ⟨node,minimal⟩ := w.guard_node_l hM hN j inj full hw hw' run table hk'
    (fn0_of_function_l (ZF.modelsKP hN) fu) fa' fv' sub guard'
  have kr := (ev.entries_l J hN.1 (fn0_function_l (ZF.modelsKP hN) fv).2.1 k r).mpr (Or.inr ⟨rfl,rfl⟩)
  have hr₀ := (minimal.bound_l kr).2
  have hrV := (game.alphabet r).mpr (Or.inr hr₀)
  obtain ⟨n',h₂,hn',f₂,e₂⟩ := ZF.fseq_end_exists_l J hN hw' hm (fn0_function_l (ZF.modelsKP hN) f₁) hrV
  have f₂ := fn0_of_function_l (ZF.modelsKP hN) f₂
  have sm := ag_end_length_l hN f₁ f₂ e₂
  have add' := dg_twice_next_l hN hw' hk sk sn sm add
  have weave' := weave.append_l hN hw' hk add sn fh f₁ fa fv e₁ e₂ ea ev
  have odd : ¬ Gm_even_d J (j ω) m := fun even => ((gm_even_successor_l J hN hw' hn sn).mp even) ⟨k,hk,add⟩
  have check : N.mem h₂ L := (game.checks h₂).mpr ⟨(game.space h₂).mpr
    ⟨n',hn',fn0_function_l (ZF.modelsKP hN) f₂⟩,n',hn',f₂,Or.inr ⟨m,r,sm,
      (e₂.entries_l J hN.1 (fn0_function_l (ZF.modelsKP hN) f₁).2.1 m r).mpr (Or.inr ⟨rfl,rfl⟩),
      Or.inr ⟨odd,hr₀,k',u,a',v',hk',add',fa',minimal,cut,node,weave'⟩⟩⟩
  have h₂R := control.step m h₁ r h₂ hm h₁R hrV f₁ e₂ (Or.inl ⟨(game.turns m).mpr ⟨hm,odd⟩,check⟩)
  refine ⟨h₂,h₂R,⟨k',n',a',v',hk',add',f₂,fa',fv',weave',guard'⟩,
    fun z hz => e₂.subset_l J z (e₁.subset_l J z hz),?_⟩
  intro eq
  have nd : Entry_d N n d h₂ :=
    ((e₁.entries_l J hN.1 (fn0_function_l (ZF.modelsKP hN) fh).2.1 n d).mpr
      (Or.inr ⟨rfl,rfl⟩)).elim fun z hz => ⟨z,hz.1,e₂.subset_l J z hz.2⟩
  exact KP.mem_irrefl_d (ZF.modelsKP hN) n (fh.bound_l (eq.symm ▸ nd)).1

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 排除同一原对局上的辅助先手胜策

若先手获胜，其合法服从历史树有内部序数秩。取满足吸收不变量的完整轮中
秩最小者；实际应答再延长一轮并保持全部不变量，严格降低该秩，矛盾。
候选秩由实际公式分离，不使用外部良基性或外部自然数递归。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project Descriptive InnerModel Internal Model.Forcing.Internal
universe u v
variable {M : Structure.{u}} {N : Structure.{v}} (hM : M.Models ZF) (hNZFC : N.Models ZFC)
  (j : M.Domain → N.Domain) (inj : Function.Injective j)
  (full : ∀ a y, N.mem y (j a) ↔ ∃ z, M.mem z a ∧ j z = y)
local notation "hN" => ZFC.models_zf_l hNZFC
local notation "J" => kp_pair_l (ZF.modelsKP hN)
include inj full

theorem Ag_witness_d.no_first_win_l {ω κ δ X : M.Domain} {p : Ag_forcing_d hM ω κ δ X}
    {s : Ag_system_d hM p} (hw : M.IsOmega ω) (hw' : N.IsOmega (j ω))
    {f x H g : N.Domain} {τ : M.Domain} (w : Ag_witness_d hM p j H x g τ)
    (run : Ag_trace_d hN (j ω) (j X) (j s.A) (j s.F₀) (j s.R₀) f x H)
    (bound : N.MemberSubset H (j p.Q)) :
    ¬ Dg_first_win_d hN (j ω) (j p.D) (j s.V₀) (j s.S) f := by
  rintro ⟨V,F,L,G,T,C,W,O,σ,game,win⟩
  have empty z (hz : N.mem z (j p.b)) : False :=
    (full p.b z).mp hz |>.elim fun a ha => p.empty a ha.1
  obtain ⟨R,control⟩ := cg_control_l hN hw' empty game.space game.legal (game.root_l hN hw' empty)
    game.runs game.payoff win
  obtain ⟨α,K,rank⟩ := control.rank_l hN hw' (ZFC.dc_l J hNZFC hw') game.runs game.payoff win
  obtain ⟨Γ,B,E,table,prod,fn,reply⟩ := w.reply_l hM hNZFC j inj full bound
  let ρ : Env N 10 := ⟨fun i => [j ω,j p.D,j s.V,V,j p.b,j τ,g,j p.U,H,j Γ].get i,fun _ => H⟩
  let φ : UnarySchema 10 := {
    body := ag_round_m (.bound 1) (.bound 2) (.bound 3) (.bound 4)
      (.bound 5) (.bound 6) (.bound 7) (.bound 8) (.bound 9) (.bound 10) .newest }
  have sat h : φ.denote ρ h ↔ Ag_round_d J (j ω) (j p.D) (j s.V) V (j p.b) (j τ) g (j p.U) H (j Γ) h :=
    ag_round_sat_l J hN.1 ..
  obtain ⟨A,read⟩ := ZF.separation_exists_d hN φ ρ R
  have states h := (read h).trans (and_congr_right fun _ => sat h)
  have root := ag_round_root_l hN (D := j p.D) (V := j s.V) (A := V)
    (τ := j τ) (g := g) (U := j p.U) (H := H) (Γ := j Γ) hw' empty
  obtain ⟨h,hh,least⟩ := rank.minimal_l hN (Q := A) (fun h hh => ((states h).mp hh).1)
    ⟨j p.b,(states (j p.b)).mpr ⟨control.root,root⟩⟩
  obtain ⟨hhR,round⟩ := (states h).mp hh
  obtain ⟨t,ht,round',sub,ne⟩ := w.round_step_l hM hN j inj full hw hw' run table prod fn reply game control hhR round
  exact ne (least t ((states t).mpr ⟨ht,round'⟩) sub)

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 分离编码后的安全完整轮仍可真延长

实际先手挑战先解去左标签；原吸收应答在验证节点后加上右标签。
同步追加的两张标签图给出同一反博弈的完整轮，原非反驳不变量保持。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal Descriptive Model.Forcing.Internal
universe u v
variable {M : Structure.{u}} {N : Structure.{v}} (hM : M.Models ZF) (hN : N.Models ZF)
  (j : M.Domain → N.Domain) (inj : Function.Injective j)
  (full : ∀ a y, N.mem y (j a) ↔ ∃ z, M.mem z a ∧ j z = y)
local notation "J" => kp_pair_l (ZF.modelsKP hN)
include inj full

theorem Ag_witness_d.tagged_step_l {ω κ δ X : M.Domain} {p : Ag_forcing_d hM ω κ δ X}
    {s : Ag_system_d hM p} (hw : M.IsOmega ω) (hw' : N.IsOmega (j ω))
    {f x H g : N.Domain} {τ Γ : M.Domain} (w : Ag_witness_d hM p j H x g τ)
    (run : Ag_trace_d hN (j ω) (j X) (j s.A) (j s.F₀) (j s.R₀) f x H)
    (table : ∀ q r d, Ag_drel_d Γ q r d ↔ M.mem q p.Q ∧ M.mem r p.P ∧ M.mem d p.D ∧
      Ag_demand_d p.Q p.T p.b q r d)
    {B K : N.Domain} (prod : N.IsCartesianProduct J B (j p.D) g) (fn : Fn0_d B g K)
    (reply : ∀ d r z t, KPair_d N z d r → Entry_d N z t K →
      Entry_d N t r (j p.U) ∧ Ag_safe_d H (j Γ) d t)
    {e o T Uc Vc : N.Domain} (retag : Td_retag_d hN (j ω) (j s.A) (j s.S) (j p.D) (j s.V₀) e o T Uc Vc)
    {V F L G J₀ C W O z σ R h : N.Domain}
    (game : Dg_counter_d hN (j ω) Uc Vc f T V F L G J₀ C W O)
    (control : Cg_control_d J false (j ω) z V F L G J₀ σ R) (hh : N.mem h R)
    (round : Ag_tag_round_d J (j ω) (j p.D) (j s.V₀) V e o (j p.b) (j τ) g (j p.U) H (j Γ) h) :
    ∃ t, N.mem t R ∧ Ag_tag_round_d J (j ω) (j p.D) (j s.V₀) V e o (j p.b) (j τ) g (j p.U) H (j Γ) t ∧
      N.MemberSubset h t ∧ h ≠ t := by
  obtain ⟨k,n,a,v,c,d,hk,add,fh,fa,fv,tc,tv,weave,guard⟩ := round
  have fc := tc.function_l hN retag.left fa
  have fd := tv.function_l hN retag.right fv
  have hn := ZF.ordinalAddition_mem_omega hN J hw' hk hk add
  obtain ⟨m,h₁,D,hm,sn,f₁,h₁R,e₁,hD⟩ := game.first_round_l hN hw' control hn fh hh ⟨k,hk,add⟩
  obtain ⟨a₀,ha₀,Da⟩ := (retag.left D).mp hD
  have empty y (hy : N.mem y (j p.b)) : False := (full p.b y).mp hy |>.elim fun a ha => p.empty a ha.1
  have subV : N.MemberSubset (j s.V₀) (j s.V) := by
    intro r hr
    obtain ⟨r₀,hr₀,eq⟩ := (full s.V₀ r).mp hr
    exact (full s.V r).mpr ⟨r₀,s.second_bound r₀ hr₀,eq⟩
  have fvFull : Fn0_d k (j s.V) v := fv.mono_target_l subV
  have name := (image_member_l j inj full).mpr ((s.auxiliary.second τ).mpr (Or.inl w.name))
  have bound : N.MemberSubset g (j s.V) := by
    intro r hr
    obtain ⟨r₀,hr₀,eq⟩ := (full p.P r).mp (w.bound r hr)
    exact (full s.V r).mpr ⟨r₀,(s.auxiliary.second r₀).mpr (Or.inr hr₀),eq⟩
  obtain ⟨r₀,_,start⟩ := w.start
  obtain ⟨r,hr,extend⟩ := guard.reply_l hN hw' empty hk fa fvFull name bound start prod fn reply
  obtain ⟨k',a',hk',fa',ea⟩ := ZF.fseq_end_exists_l J hN hw' hk (fn0_function_l (ZF.modelsKP hN) fa) ha₀
  obtain ⟨l,v',_,fv',ev⟩ := ZF.fseq_end_exists_l J hN hw' hk (fn0_function_l (ZF.modelsKP hN) fvFull) hr
  have fa' := fn0_of_function_l (ZF.modelsKP hN) fa'
  have fv' := fn0_of_function_l (ZF.modelsKP hN) fv'
  have sk := ag_end_length_l hN fa fa' ea
  have eq := (ag_end_length_l hN fvFull fv' ev).eq hN.1 sk
  subst l
  have guard' := extend a₀ a' v' ea ev
  obtain ⟨u,fu,cut,_⟩ := ds_prefix_l J hN hw' (fn0_function_l (ZF.modelsKP hN) run.play) hk'
  have sub := (ds_restrict_iff_l J fu (fn0_function_l (ZF.modelsKP hN) run.play).1).mp cut
  obtain ⟨node,minimal⟩ := w.guard_node_l hM hN j inj full hw hw' run table hk'
    (fn0_of_function_l (ZF.modelsKP hN) fu) fa' fv' sub guard'
  have kr := (ev.entries_l J hN.1 (fn0_function_l (ZF.modelsKP hN) fv).2.1 k r).mpr (Or.inr ⟨rfl,rfl⟩)
  obtain ⟨R₀,Rr⟩ := (J).total o r
  have hR₀ := (retag.right R₀).mpr ⟨r,(minimal.bound_l kr).2,Rr⟩
  obtain ⟨l,c',_,fc',ec⟩ := ZF.fseq_end_exists_l J hN hw' hk (fn0_function_l (ZF.modelsKP hN) fc) hD
  have fc' := fn0_of_function_l (ZF.modelsKP hN) fc'
  have eq := (ag_end_length_l hN fc fc' ec).eq hN.1 sk
  subst l
  obtain ⟨l,d',_,fd',ed⟩ := ZF.fseq_end_exists_l J hN hw' hk (fn0_function_l (ZF.modelsKP hN) fd) hR₀
  have fd' := fn0_of_function_l (ZF.modelsKP hN) fd'
  have eq := (ag_end_length_l hN fd fd' ed).eq hN.1 sk
  subst l
  have tc' := tc.append_l hN fa fc ea ec Da
  have tv' := tv.append_l hN fv fd ev ed Rr
  have node' := (retag.node_l hN hk' (fn0_of_function_l (ZF.modelsKP hN) fu) fa' minimal fc' fd' tc' tv').mp node
  have hR₀V := (game.alphabet R₀).mpr (Or.inr hR₀)
  obtain ⟨n',h₂,hn',f₂,e₂⟩ := ZF.fseq_end_exists_l J hN hw' hm (fn0_function_l (ZF.modelsKP hN) f₁) hR₀V
  have f₂ := fn0_of_function_l (ZF.modelsKP hN) f₂
  have sm := ag_end_length_l hN f₁ f₂ e₂
  have add' := dg_twice_next_l hN hw' hk sk sn sm add
  have weave' := weave.append_l hN hw' hk add sn fh f₁ fc fd e₁ e₂ ec ed
  have odd : ¬ Gm_even_d J (j ω) m := fun even => ((gm_even_successor_l J hN hw' hn sn).mp even) ⟨k,hk,add⟩
  have check : N.mem h₂ L := (game.checks h₂).mpr ⟨(game.space h₂).mpr
    ⟨n',hn',fn0_function_l (ZF.modelsKP hN) f₂⟩,n',hn',f₂,Or.inr ⟨m,R₀,sm,
      (e₂.entries_l J hN.1 (fn0_function_l (ZF.modelsKP hN) f₁).2.1 m R₀).mpr (Or.inr ⟨rfl,rfl⟩),
      Or.inr ⟨odd,hR₀,k',u,c',d',hk',add',fc',fd',cut,node',weave'⟩⟩⟩
  have h₂R := control.step m h₁ R₀ h₂ hm h₁R hR₀V f₁ e₂ (Or.inl ⟨(game.turns m).mpr ⟨hm,odd⟩,check⟩)
  refine ⟨h₂,h₂R,⟨k',n',a',v',c',d',hk',add',f₂,fa',minimal,tc',tv',weave',guard'⟩,
    fun z hz => e₂.subset_l J z (e₁.subset_l J z hz),?_⟩
  intro eq
  have nD : Entry_d N n D h₂ :=
    ((e₁.entries_l J hN.1 (fn0_function_l (ZF.modelsKP hN) fh).2.1 n D).mpr
      (Or.inr ⟨rfl,rfl⟩)).elim fun z hz => ⟨z,hz.1,e₂.subset_l J z hz.2⟩
  exact KP.mem_irrefl_d (ZF.modelsKP hN) n (fh.bound_l (eq.symm ▸ nD)).1

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 分离重编码后的辅助先手胜策同样不可能存在

标签历史只改变字母表示。内部可分离的完整轮集合仍处处有真延长，
与原先手控制树的实际序数秩所给出的极小节点矛盾。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal Descriptive Model.Forcing.Internal
universe u v
variable {M : Structure.{u}} {N : Structure.{v}} (hM : M.Models ZF) (hNZFC : N.Models ZFC)
  (j : M.Domain → N.Domain) (inj : Function.Injective j)
  (full : ∀ a y, N.mem y (j a) ↔ ∃ z, M.mem z a ∧ j z = y)
local notation "hN" => ZFC.models_zf_l hNZFC
local notation "J" => kp_pair_l (ZF.modelsKP hN)
include inj full

theorem Ag_witness_d.tagged_no_first_l {ω κ δ X : M.Domain} {p : Ag_forcing_d hM ω κ δ X}
    {s : Ag_system_d hM p} (hw : M.IsOmega ω) (hw' : N.IsOmega (j ω))
    {f x H g : N.Domain} {τ : M.Domain} (w : Ag_witness_d hM p j H x g τ)
    (run : Ag_trace_d hN (j ω) (j X) (j s.A) (j s.F₀) (j s.R₀) f x H)
    (bound : N.MemberSubset H (j p.Q))
    {e o T Uc Vc : N.Domain} (retag : Td_retag_d hN (j ω) (j s.A) (j s.S) (j p.D) (j s.V₀) e o T Uc Vc) :
    ¬ Dg_first_win_d hN (j ω) Uc Vc T f := by
  rintro ⟨V,F,L,G,T₀,C,W,O,σ,game,win⟩
  have empty z (hz : N.mem z (j p.b)) : False := (full p.b z).mp hz |>.elim fun a ha => p.empty a ha.1
  obtain ⟨R,control⟩ := cg_control_l hN hw' empty game.space game.legal (game.root_l hN hw' empty)
    game.runs game.payoff win
  obtain ⟨α,K,rank⟩ := control.rank_l hN hw' (ZFC.dc_l J hNZFC hw') game.runs game.payoff win
  obtain ⟨Γ,B,E,table,prod,fn,reply⟩ := w.reply_l hM hNZFC j inj full bound
  let ρ : Env N 12 := ⟨fun i => [j ω,j p.D,j s.V₀,V,e,o,j p.b,j τ,g,j p.U,H,j Γ].get i,fun _ => H⟩
  let φ : UnarySchema 12 := {
    body := ag_tag_round_m (.bound 1) (.bound 2) (.bound 3) (.bound 4) (.bound 5) (.bound 6)
      (.bound 7) (.bound 8) (.bound 9) (.bound 10) (.bound 11) (.bound 12) .newest }
  have sat h : φ.denote ρ h ↔ Ag_tag_round_d J (j ω) (j p.D) (j s.V₀) V e o (j p.b) (j τ) g (j p.U) H (j Γ) h :=
    ag_tag_round_sat_l J hN.1 ..
  obtain ⟨A,read⟩ := ZF.separation_exists_d hN φ ρ R
  have states h := (read h).trans (and_congr_right fun _ => sat h)
  have root := ag_tag_round_root_l hN (D := j p.D) (V := j s.V₀) (A := V) (e := e) (o := o)
    (τ := j τ) (g := g) (U := j p.U) (H := H) (Γ := j Γ) hw' empty
  obtain ⟨h,hh,least⟩ := rank.minimal_l hN (Q := A) (fun h hh => ((states h).mp hh).1)
    ⟨j p.b,(states (j p.b)).mpr ⟨control.root,root⟩⟩
  obtain ⟨hhR,round⟩ := (states h).mp hh
  obtain ⟨t,ht,round',sub,ne⟩ := w.tagged_step_l hM hN j inj full hw hw' run table prod fn reply retag game control hhR round
  exact ne (least t ((states t).mpr ⟨ht,round'⟩) sub)

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 专用树在实际大坍缩扩张中排除 7.12 的负分支

对任意原合法 I 策略，自动构造同一条枚举对局、小泛型、吸收名字和应答。
该原对局上的辅助 I 胜策被最小秩矛盾排除，故不可能满足负分支的全对局断言。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project Descriptive InnerModel Internal Model.Forcing.Internal
universe u
variable {M : Structure.{u}} (hZFC : M.Models ZFC)
local notation "hZF" => ZFC.models_zf_l hZFC
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Ag_system_d.collapse_no_first_l {ω κ δ X : M.Domain} {p : Ag_forcing_d hZF ω κ δ X}
    (s : Ag_system_d hZF p) (hw : M.IsOmega ω) (above : M.mem ω δ)
    (strong : M.IsStrongLimitCardinal I δ) (smallκ : M.mem κ δ)
    {G : M.Domain → Prop} (generic : Generic_d M p.P p.U p.P G) {b} (hb : G b)
    (j : M.Domain → (extension_l M hZF p.P p.U p.P G).Domain) (inj : Function.Injective j)
    (full : ∀ a y, (extension_l M hZF p.P p.U p.P G).mem y (j a) ↔ ∃ x, M.mem x a ∧ j x = y)
    (checks : ∀ a t, Check_d M b a t → Qval_d M p.P p.U p.P G t (j a))
    {σ : (extension_l M hZF p.P p.U p.P G).Domain}
    (first : Gt_strategy_d (preserves_zf_l p.big_order hZF generic) true (j ω) (j s.A) (j s.R₀) σ) :
    let hN := preserves_zf_l p.big_order hZF generic
    let J := kp_pair_l (ZF.modelsKP hN)
    ∃ f, Fn0_d (j ω) (j s.A) f ∧ Branch_d (j s.F₀) (j s.R₀) f ∧ Gm_follows_d J true (j ω) σ f ∧
      ¬ Dg_first_win_d hN (j ω) (j p.D) (j s.V₀) (j s.S) f := by
  let N := extension_l M hZF p.P p.U p.P G
  have hN : N.Models ZF := preserves_zf_l p.big_order hZF generic
  have hNZFC : N.Models ZFC := preserves_zfc_l p.big_order hZFC generic
  obtain ⟨f,x,q,H,g,τ,ff,branch,played,fx,fq,coords,members,bound,_,w⟩ :=
    s.collapse_witness_l hZFC hw above strong smallκ generic hb j inj full checks first
  have order := image_cond_order_l (ZF.modelsKP hZF) hN.1 j inj full p.small_order
  have run := ag_trace_l hN order ff branch fx fq coords members
  have omega : N.IsOmega (j ω) := image_omega_l (hEN := hN.1) j inj full hZF
    (internal_foundation_l p.big_order hZF generic) hw
    (fun D => KP.difference_exists_d (ZF.modelsKP hN) D (j ω))
  exact ⟨f,ff,branch,played,w.no_first_win_l hZF hNZFC j inj full hw omega run bound⟩

theorem Ag_system_d.collapse_not_negative_l {ω κ δ X : M.Domain} {p : Ag_forcing_d hZF ω κ δ X}
    (s : Ag_system_d hZF p) (hw : M.IsOmega ω) (above : M.mem ω δ)
    (strong : M.IsStrongLimitCardinal I δ) (smallκ : M.mem κ δ)
    {G : M.Domain → Prop} (generic : Generic_d M p.P p.U p.P G) {b} (hb : G b)
    (j : M.Domain → (extension_l M hZF p.P p.U p.P G).Domain) (inj : Function.Injective j)
    (full : ∀ a y, (extension_l M hZF p.P p.U p.P G).mem y (j a) ↔ ∃ x, M.mem x a ∧ j x = y)
    (checks : ∀ a t, Check_d M b a t → Qval_d M p.P p.U p.P G t (j a)) :
    ¬ Td_tree_negative_d (preserves_zf_l p.big_order hZF generic)
      (j ω) (j s.A) (j s.F₀) (j s.R₀) (j p.D) (j s.V₀) (j s.S) := by
  rintro ⟨σ,first,wins⟩
  obtain ⟨f,ff,branch,played,no⟩ := s.collapse_no_first_l hZFC hw above strong smallκ generic hb j inj full checks first
  exact no (wins f ff branch played)

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 分离专用树在大坍缩扩张中排除 7.12 的负分支

原模型的实际标签重编码随同地嵌入进入扩张。原对局、小泛型和吸收名字
保持同一组对象；标签后的最小秩矛盾因而适用于 7.12 所用的实际分离树。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal Descriptive Model.Forcing.Internal
universe u
variable {M : Structure.{u}} (hZFC : M.Models ZFC)
local notation "hZF" => ZFC.models_zf_l hZFC
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Ag_system_d.separated_no_first_l {ω κ δ X : M.Domain} {p : Ag_forcing_d hZF ω κ δ X}
    (s : Ag_system_d hZF p) (hw : M.IsOmega ω) (above : M.mem ω δ)
    (strong : M.IsStrongLimitCardinal I δ) (smallκ : M.mem κ δ)
    {e o T U V : M.Domain} (retag : Td_retag_d hZF ω s.A s.S p.D s.V₀ e o T U V)
    {G : M.Domain → Prop} (generic : Generic_d M p.P p.U p.P G) {b} (hb : G b)
    (j : M.Domain → (extension_l M hZF p.P p.U p.P G).Domain) (inj : Function.Injective j)
    (full : ∀ a y, (extension_l M hZF p.P p.U p.P G).mem y (j a) ↔ ∃ x, M.mem x a ∧ j x = y)
    (checks : ∀ a t, Check_d M b a t → Qval_d M p.P p.U p.P G t (j a))
    {σ : (extension_l M hZF p.P p.U p.P G).Domain}
    (first : Gt_strategy_d (preserves_zf_l p.big_order hZF generic) true (j ω) (j s.A) (j s.R₀) σ) :
    let hN := preserves_zf_l p.big_order hZF generic
    let J := kp_pair_l (ZF.modelsKP hN)
    ∃ f, Fn0_d (j ω) (j s.A) f ∧ Branch_d (j s.F₀) (j s.R₀) f ∧ Gm_follows_d J true (j ω) σ f ∧
      ¬ Dg_first_win_d hN (j ω) (j U) (j V) (j T) f := by
  let N := extension_l M hZF p.P p.U p.P G
  have hN : N.Models ZF := preserves_zf_l p.big_order hZF generic
  have hNZFC : N.Models ZFC := preserves_zfc_l p.big_order hZFC generic
  obtain ⟨f,x,q,H,g,τ,ff,branch,played,fx,fq,coords,members,bound,_,w⟩ :=
    s.collapse_witness_l hZFC hw above strong smallκ generic hb j inj full checks first
  have order := image_cond_order_l (ZF.modelsKP hZF) hN.1 j inj full p.small_order
  have run := ag_trace_l hN order ff branch fx fq coords members
  have omega : N.IsOmega (j ω) := image_omega_l (hEN := hN.1) j inj full hZF
    (internal_foundation_l p.big_order hZF generic) hw
    (fun D => KP.difference_exists_d (ZF.modelsKP hN) D (j ω))
  obtain ⟨retag'⟩ := retag.image_l hZF hN j inj full hw omega
  exact ⟨f,ff,branch,played,w.tagged_no_first_l hZF hNZFC j inj full hw omega run bound retag'⟩

theorem Ag_system_d.separated_not_negative_l {ω κ δ X : M.Domain} {p : Ag_forcing_d hZF ω κ δ X}
    (s : Ag_system_d hZF p) (hw : M.IsOmega ω) (above : M.mem ω δ)
    (strong : M.IsStrongLimitCardinal I δ) (smallκ : M.mem κ δ)
    {e o T U V : M.Domain} (retag : Td_retag_d hZF ω s.A s.S p.D s.V₀ e o T U V)
    {G : M.Domain → Prop} (generic : Generic_d M p.P p.U p.P G) {b} (hb : G b)
    (j : M.Domain → (extension_l M hZF p.P p.U p.P G).Domain) (inj : Function.Injective j)
    (full : ∀ a y, (extension_l M hZF p.P p.U p.P G).mem y (j a) ↔ ∃ x, M.mem x a ∧ j x = y)
    (checks : ∀ a t, Check_d M b a t → Qval_d M p.P p.U p.P G t (j a)) :
    ¬ Td_tree_negative_d (preserves_zf_l p.big_order hZF generic)
      (j ω) (j s.A) (j s.F₀) (j s.R₀) (j U) (j V) (j T) := by
  rintro ⟨σ,first,wins⟩
  obtain ⟨f,ff,branch,played,no⟩ := s.separated_no_first_l hZFC hw above strong smallκ retag generic hb j inj full checks first
  exact no (wins f ff branch played)

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 用实际大泛型消去 7.12 的泛型分支

原 𝒫(δ) 的内部可数证书给出包含空条件的大坍缩泛型。
把 7.12 的全泛型断言应用到这个已构造的滤子，再与分离树负分支排除矛盾。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal Descriptive Model.Forcing.Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)
theorem Ag_system_d.not_collapse_l {Ω c X R : M.Domain}
    (hΩ : M.IsOmega Ω) (certificate : Zc_model_d I Ω c X R)
    (source : Smem_d I c X R) (trans : M.TransitiveSet X) (dc : Dc_d I Ω)
    {ω κ δ A : (smdl_structure_l I (R := R) certificate.model.2.1).Domain}
    {p : Ag_forcing_d (ZFC.models_zf_l (certificate.native_l I hZF hΩ)) ω κ δ A}
    (s : Ag_system_d (ZFC.models_zf_l (certificate.native_l I hZF hΩ)) p)
    (hw : (smdl_structure_l I (R := R) certificate.model.2.1).IsOmega ω)
    (above : (smdl_structure_l I (R := R) certificate.model.2.1).mem ω δ)
    (strong : (smdl_structure_l I (R := R) certificate.model.2.1).IsStrongLimitCardinal
      (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l (certificate.native_l I hZF hΩ)))) δ)
    (small : (smdl_structure_l I (R := R) certificate.model.2.1).mem κ δ)
    {e o T U V : (smdl_structure_l I (R := R) certificate.model.2.1).Domain}
    (retag : Td_retag_d (ZFC.models_zf_l (certificate.native_l I hZF hΩ)) ω s.A s.S p.D s.V₀ e o T U V)
    (count : Pc_count_d I Ω X R δ.val) :
    ¬ Td_tree_collapse_d (ZFC.models_zf_l (certificate.native_l I hZF hΩ)) ω δ s.A s.F₀ s.R₀ U V T := by
  let N := smdl_structure_l I (R := R) certificate.model.2.1
  have native := certificate.native_l I hZF hΩ
  have hN := ZFC.models_zf_l native
  let J := kp_pair_l (ZF.modelsKP hN)
  have infinite : N.IsInfiniteCardinal J ω δ :=
    ⟨strong.1,ZF.exists_inclusionInjection hN J (strong.1.1.transitive ω above)⟩
  obtain ⟨i,identity⟩ := ZF.exists_identityBijection hN J δ
  have bound := ZF.fseq_bound_l J hN hw infinite ⟨i,identity.1⟩ p.big_space
  obtain ⟨H,_,hb,generic⟩ := count.generic_l hZF hΩ dc source trans hN δ p.P p.U p.b p.big_order bound p.big_base
  intro collapse
  obtain ⟨j,inj,full,checks,negative⟩ := collapse p.P p.U p.big_space p.big_edges p.big_order
    (fun q => M.mem q.val H) generic p.b hb
  exact s.separated_not_negative_l native hw above strong small retag generic hb j inj full checks negative

end YesMetaZFC.SetTheory.LargeCardinal
