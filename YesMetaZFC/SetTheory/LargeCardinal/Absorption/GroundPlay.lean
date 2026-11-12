import YesMetaZFC.SetTheory.LargeCardinal.Absorption.Trace
import YesMetaZFC.SetTheory.Descriptive.Demand.DemandCounterWeave
import YesMetaZFC.Model.Forcing.Boolean.GroundGeneric
import YesMetaZFC.SetTheory.Descriptive.Tree.HistoryTree
import YesMetaZFC.SetTheory.Descriptive.Game.GameAttemptRank
import YesMetaZFC.SetTheory.Descriptive.Tree.TreeWellFounded
import YesMetaZFC.SetTheory.Descriptive.Tree.RetractionFixed
import YesMetaZFC.SetTheory.RelationChain
import YesMetaZFC.SetTheory.LargeCardinal.Absorption.BranchGeneric
import YesMetaZFC.Model.Forcing.Ground.PowerGeneric

/-! # 指定实数、泛型与共尾枚举的原历史

第 k 次 I 落子读出 x(k)，条件属于 H，且加强枚举第 k 项中属于 H 的条件。
所有要求只读取已出现的偶数项，因而对前缀保持；追加时仍命中原 II 稠密要求。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project Descriptive InnerModel Internal Model.Forcing.Internal
universe u
variable {M : Structure.{u}}

def Ag_match_d (I : kpair_convention_l.Interpretation M) (ω T H x e s : M.Domain) : Prop :=
  ∀ k n a y q, M.mem k ω → M.IsOrdinalAddition I n k k → Entry_d M n a s → KPair_d M a y q →
    M.mem q H ∧ Entry_d M k y x ∧ ∀ r, Entry_d M k r e → M.mem r H → Entry_d M q r T

def ag_match_m {d} (ω T H x e s : Term d) : Formula 1 d := set[d] ⟪
  ∀ k n a y q, k ∈ ⌜ω⌝ₛ → ⌜(Formula.isOrdinalAddition kpair_convention_l)⌝ₚ(n,k,k) →
    ⌜entry_m⌝ₚ(n,a,⌜s⌝ₛ) → ⌜kpair_m⌝ₚ(a,y,q) →
    q ∈ ⌜H⌝ₛ ∧ ⌜entry_m⌝ₚ(k,y,⌜x⌝ₛ) ∧
      (∀ r, ⌜entry_m⌝ₚ(k,r,⌜e⌝ₛ) → r ∈ ⌜H⌝ₛ → ⌜entry_m⌝ₚ(q,r,⌜T⌝ₛ))⟫
derive_free_closed ag_match_m

theorem ag_match_sat_l (I : kpair_convention_l.Interpretation M) (hE : Extensional M)
    {d} (ρ : Env M d) (ω T H x e s : Term d) :
    Formula.satisfies ρ (ag_match_m ω T H x e s) ↔
      Ag_match_d I (ω.eval ρ) (T.eval ρ) (H.eval ρ) (x.eval ρ) (e.eval ρ) (s.eval ρ) := by
  simp only [ag_match_m,Ag_match_d,Formula.satisfies_forall_iff,Formula.satisfies_imp_iff,
    Formula.satisfies_mem_iff,Formula.satisfies_isOrdinalAddition_iff I hE,entry_sat_l M hE,
    kpair_sat_l M hE,Formula.satisfies_conj_iff,Definitional.Term.eval_weaken]
  rfl

theorem Ag_match_d.restrict_l {I : kpair_convention_l.Interpretation M} {ω T H x e s t : M.Domain}
    (h : Ag_match_d I ω T H x e s) (sub : M.MemberSubset t s) : Ag_match_d I ω T H x e t :=
  fun k n a y q hk add na pair => h k n a y q hk add
    (na.elim fun p hp => ⟨p,hp.1,sub p hp.2⟩) pair

variable (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Ag_match_d.append_l {ω A T H x e s t n a : M.Domain}
    (h : Ag_match_d I ω T H x e s) (fs : M.IsSetFunctionFromTo I s n A)
    (end' : Fseq_end_d I ω t s a)
    (move : ∀ k y q, M.mem k ω → M.IsOrdinalAddition I n k k → KPair_d M a y q →
      M.mem q H ∧ Entry_d M k y x ∧ ∀ r, Entry_d M k r e → M.mem r H → Entry_d M q r T) :
    Ag_match_d I ω T H x e t := by
  intro k i b y q hk add ib pair
  rcases (end'.entries_l I hZF.1 fs.2.1 i b).mp ib with old | ⟨rfl,rfl⟩
  · exact h k i b y q hk add old pair
  · exact move k y q hk add pair

/-- 泛型条件 b 可以与原历史的上次条件同时加强，再命中尚未向下闭合的旧稠密集。 -/
theorem Ag_game_d.filter_move_l {ω X Q T D P A F R H x e n s b : M.Domain}
    (game : Ag_game_d hZF ω X Q T D P A F R) (hw : M.IsOmega ω)
    (O : Cond_order_d M Q T Q) (filter : Gset_d Q T Q D H)
    (hits : ∀ E, M.mem E D → ∀ p, M.mem p H → ∃ q, M.mem q H ∧ M.mem q E ∧ Entry_d M q p T)
    (match' : Ag_match_d I ω T H x e s) (hb : M.mem b H)
    (hn : M.mem n ω) (fs : M.IsSetFunctionFromTo I s n A) (hs : M.mem s R)
    (even : Gm_even_d I ω n) : ∃ q, M.mem q H ∧ Entry_d M q b T ∧ Ag_hit_d T s n q := by
  classical
  by_cases empty : ∀ i, ¬ M.mem i n
  · exact ⟨b,hb,O.refl b (filter.proper b hb).1,fun i _ succ _ => (empty i succ.predecessor_mem).elim⟩
  · obtain ⟨i,hi,ni⟩ := hw.exists_predecessor_of_mem_of_nonempty hZF hn
      (Classical.not_forall.mp empty |>.elim fun i h => ⟨i,Classical.not_not.mp h⟩)
    have odd := (gm_even_successor_l I hZF hw hi ni).mp even
    obtain ⟨E,_,iE⟩ := fs.2.2 i ni.predecessor_mem
    have hE := (((game.legal s).mp hs).2 i E iE).2 odd
    have ine : ∃ k, M.mem k i := by
      apply Classical.byContradiction
      intro no
      exact odd (gm_even_zero_l I hZF hw (fun k hk => no ⟨k,hk⟩))
    obtain ⟨k,hk,ik⟩ := hw.exists_predecessor_of_mem_of_nonempty hZF hi ine
    have keven : Gm_even_d I ω k := Classical.byContradiction
      (fun no => odd ((gm_even_successor_l I hZF hw hk ik).mpr no))
    have kn := (hw.members_areOrdinals (ZF.modelsKP hZF) n hn).transitive i ni.predecessor_mem k ik.predecessor_mem
    obtain ⟨a,_,ka⟩ := fs.2.2 k kn
    obtain ⟨y,p,_,hp,pair,_⟩ := (((game.legal s).mp hs).2 k a ka).1 keven
    obtain ⟨l,hl,add⟩ := keven
    have ph := (match' l k a y p hl add ka pair).1
    obtain ⟨r,rH,rp,rb⟩ := filter.directed p b ph hb
    obtain ⟨q,qH,qE,qr⟩ := hits E hE r rH
    have qp := O.trans q r p (filter.proper q qH).1 (filter.proper r rH).1 hp qr rp
    refine ⟨q,qH,O.trans q r b (filter.proper q qH).1 (filter.proper r rH).1 (filter.proper b hb).1 qr rb,?_⟩
    intro i' E' ni' iE'
    have eq := ni.predecessor_eq hZF.1 (hw.members_areOrdinals (ZF.modelsKP hZF) i hi) ni'
    subst i'
    have eq := fs.1.2 i E' E iE' iE
    subst E'
    refine ⟨qE,fun k' a' y' p' ik' ka' pair' => ?_⟩
    have eq := ik.predecessor_eq hZF.1 (hw.members_areOrdinals (ZF.modelsKP hZF) k hk) ik'
    subst k'
    have eq := fs.1.2 k a' a ka' ka
    subst a'
    exact (kpair_injective_l M pair' pair).2.symm ▸ qp

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 指定实数与小泛型的实际无限原对局

在原合法树内分离满足坐标要求且服从 II 的历史。偶数步由泛型性延长，
奇数步取同一 II 策略的值；内部 DC 给出遍历全部内部 ω 的分支。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project Descriptive InnerModel Internal Model.Forcing.Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Ag_game_d.prescribed_play_l {ω X Q T D P A F R H x e τ : M.Domain}
    (game : Ag_game_d hZF ω X Q T D P A F R) (hw : M.IsOmega ω) (dc : Dc_d I ω)
    (O : Cond_order_d M Q T Q) (filter : Gset_d Q T Q D H)
    (hits : ∀ E, M.mem E D → ∀ p, M.mem p H → ∃ q, M.mem q H ∧ M.mem q E ∧ Entry_d M q p T)
    (fx : Fn0_d ω X x) (fe : Fn0_d ω Q e) (second : Gt_strategy_d hZF false ω A R τ) :
    ∃ f, Fn0_d ω A f ∧ Branch_d F R f ∧ Gm_follows_d I false ω τ f ∧ Ag_match_d I ω T H x e f := by
  classical
  let ρ : Env M 1 := ⟨fun _ => ω,fun _ => ω⟩
  let φ : UnarySchema 1 := { body := gm_even_m (𝒞 := kpair_convention_l) (.bound 1) .newest }
  obtain ⟨J,readJ⟩ := ZF.separation_exists_d hZF φ ρ ω
  have turns n : M.mem n J ↔ M.mem n ω ∧ Gm_even_d I ω n :=
    (readJ n).trans (and_congr_right fun _ => gm_even_sat_l I hZF.1 ..)
  let η : Env M 7 := ⟨fun i => [ω,T,H,x,e,J,τ].get i,fun _ => ω⟩
  let ψ : UnarySchema 7 := {
    body := .conj
      (ag_match_m (.bound 1) (.bound 2) (.bound 3) (.bound 4) (.bound 5) .newest)
      (cg_follows_m false (.bound 1) (.bound 6) (.bound 7) .newest) }
  obtain ⟨U,cutU⟩ := ZF.separation_exists_d hZF ψ η R
  have sat s : ψ.denote η s ↔ Ag_match_d I ω T H x e s ∧ Cg_follows_d I false ω J τ s := by
    simp only [UnarySchema.denote,ψ,Formula.satisfies_conj_iff,ag_match_sat_l I hZF.1,
      cg_follows_sat_l I hZF.1]
    rfl
  have read s := (cutU s).trans (and_congr_right fun _ => sat s)
  have tree : Tree_d F U := by
    refine ⟨fun s hs => (game.tree_l hZF).1 s ((read s).mp hs).1,?_⟩
    intro s hs t ht sub
    obtain ⟨hr,match',follows⟩ := (read s).mp hs
    obtain ⟨n,hn,ft⟩ := (game.space t).mp ht
    obtain ⟨_,_,fs⟩ := (game.space s).mp ((game.tree_l hZF).1 s hr)
    exact (read t).mpr ⟨(game.tree_l hZF).2 s hr t ht sub,match'.restrict_l sub,
      follows.prefix_l hZF hw hn ft fs.1 sub⟩
  have next : ∀ s, M.mem s U → ∃ t, M.mem t U ∧ Step_d I ω s t := by
    intro s hs
    obtain ⟨hr,match',follows⟩ := (read s).mp hs
    obtain ⟨n,hn,fs⟩ := (game.space s).mp ((game.tree_l hZF).1 s hr)
    have move : ∃ a t, M.mem t R ∧ Fseq_end_d I ω t s a ∧ Ag_match_d I ω T H x e t ∧
        (¬ M.mem n J → Entry_d M s a τ) := by
      by_cases even : Gm_even_d I ω n
      · obtain ⟨k,hk,add⟩ := even
        obtain ⟨y,hy,ky⟩ := fx.2.1 k hk
        obtain ⟨r,_,kr⟩ := fe.2.1 k hk
        have choose : ∃ b, M.mem b H ∧ (M.mem r H → b = r) := by
          by_cases rh : M.mem r H
          · exact ⟨r,rh,fun _ => rfl⟩
          · exact filter.inhabited.imp fun b hb => ⟨hb,fun yes => (rh yes).elim⟩
        obtain ⟨b,bH,br⟩ := choose
        obtain ⟨q,qH,qb,hit⟩ := game.filter_move_l hZF hw O filter hits match' bH hn fs hr ⟨k,hk,add⟩
        obtain ⟨a,pair⟩ := (I).total y q
        have ha := (game.alphabet a).mpr (Or.inl ((game.pair a).mpr ⟨y,hy,q,(filter.proper q qH).1,pair⟩))
        obtain ⟨m,t,hm,ft,end'⟩ := ZF.fseq_end_exists_l I hZF hw hn fs ha
        have legal := ((game.legal s).mp hr).2.append_l hZF hw hn fs end'
          ⟨fun _ => ⟨y,q,hy,(filter.proper q qH).1,pair,hit⟩,fun no => (no ⟨k,hk,add⟩).elim⟩
        refine ⟨a,t,(game.legal t).mpr ⟨(game.space t).mpr ⟨m,hm,ft⟩,legal⟩,end',?_,
          fun no => (no ((turns n).mpr ⟨hn,k,hk,add⟩)).elim⟩
        apply match'.append_l hZF fs end'
        intro l y' q' hl add' pair'
        have eq := dg_twice_inj_l hZF hw hl hk add' add
        subst l
        obtain ⟨eqy,eqq⟩ := (I).injective pair' pair
        subst y' q'
        refine ⟨qH,ky,fun r' kr' rh => ?_⟩
        have eq := (fn0_function_l (ZF.modelsKP hZF) fe).1.2 k r' r kr' kr
        subst r'
        exact br rh ▸ qb
      · obtain ⟨V,own,fτ⟩ := second.strategy
        obtain ⟨a,_,sa⟩ := fτ.2.1 s ((own s).mpr ⟨hr,n,hn,fn0_of_function_l (ZF.modelsKP hZF) fs,even⟩)
        obtain ⟨t,ht,end'⟩ := second.legal s a sa
        exact ⟨a,t,ht,end',match'.append_l hZF fs end' (fun k _ _ hk add _ => (even ⟨k,hk,add⟩).elim),fun _ => sa⟩
    obtain ⟨a,t,ht,end',matched,sa⟩ := move
    exact ⟨t,(read t).mpr ⟨ht,matched,follows.extend_l hZF hw hn fs end' sa⟩,a,end'⟩
  obtain ⟨z,empty,_⟩ := hw.1.1
  have root : M.mem z U := (read z).mpr ⟨game.root_l hZF hw empty,
    fun _ _ _ _ _ _ _ na _ => na.elim fun p hp => (empty p hp.2).elim,
    fun _ _ _ _ _ _ na => na.elim fun p hp => (empty p hp.2).elim⟩
  obtain ⟨f,ff,branch⟩ := tree_pruned_dc_l I hZF hw dc game.space tree ⟨z,root⟩ next
  have prefixes {n} (hn : M.mem n ω) : ∃ s, M.IsSetFunctionFromTo I s n A ∧
      M.IsRestrictionOf I s f n ∧ M.mem s U := by
    obtain ⟨s,fs,cut,_⟩ := ds_prefix_l I hZF hw ff hn
    exact ⟨s,fs,cut,branch s ((game.space s).mpr ⟨n,hn,fs⟩) ((ds_restrict_iff_l I fs ff.1).mp cut)⟩
  refine ⟨f,fn0_of_function_l (ZF.modelsKP hZF) ff,
    fun s hs sub => ((read s).mp (branch s hs sub)).1,?_,?_⟩
  · intro n hn odd s cut a na
    obtain ⟨m,succ,hm⟩ := hw.1.2 n hn
    obtain ⟨t,ft,rt,ht⟩ := prefixes hm
    have fs := cut.isSetFunctionFromTo ff (hw.transitive (ZF.modelsKP hZF) n hn)
    have st := (ds_restrict_iff_l I fs ft.1).mpr
      (ds_prefix_mono_l I fs ft.1 cut rt (fun k hk => (succ k).mpr (Or.inl hk)))
    exact ((read t).mp ht).2.2 n hn (fun nj => odd ((turns n).mp nj).2) s st a
      ((rt.2 n a).mpr ⟨succ.predecessor_mem,na⟩)
  · intro k n a y q hk add na pair
    have hn := ff.input_mem_of_pairMember na
    obtain ⟨m,succ,hm⟩ := hw.1.2 n hn
    obtain ⟨t,_,rt,ht⟩ := prefixes hm
    exact ((read t).mp ht).2.1 k n a y q hk add ((rt.2 n a).mpr ⟨succ.predecessor_mem,na⟩) pair

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 同一原对局的小条件列在给定泛型中逐尾共尾

共尾性先由条件域满枚举取得，再沿原合法回合的递降性传到任意更晚轮号。
实数和小条件都从这一条对局读取，不重新选择实数或泛型。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project Descriptive InnerModel Internal Model.Forcing.Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Ag_game_d.cofinal_play_l {ω X Q T D P A F R H x e τ : M.Domain}
    (game : Ag_game_d hZF ω X Q T D P A F R) (hw : M.IsOmega ω) (dc : Dc_d I ω)
    (O : Cond_order_d M Q T Q) (filter : Gset_d Q T Q D H)
    (hits : ∀ E, M.mem E D → ∀ p, M.mem p H → ∃ q, M.mem q H ∧ M.mem q E ∧ Entry_d M q p T)
    (fx : Fn0_d ω X x) (fe : Fn0_d ω Q e) (onto : M.IsSetSurjectiveOnto I e ω Q)
    (second : Gt_strategy_d hZF false ω A R τ) :
    ∃ f q, Ag_trace_d hZF ω X A F R f x H ∧ Gm_follows_d I false ω τ f ∧ Fn0_d ω Q q ∧
      (∀ k n a y p, M.mem k ω → M.IsOrdinalAddition I n k k → Entry_d M n a f →
        KPair_d M a y p → Entry_d M k y x ∧ Entry_d M k p q) ∧
      (∀ i j p r, M.mem i j → Entry_d M i p q → Entry_d M j r q → Entry_d M r p T) ∧
      ∀ p, M.mem p H → ∀ i, M.mem i ω → ∃ k r, M.mem i k ∧ Entry_d M k r q ∧ Entry_d M r p T := by
  obtain ⟨f,ff,branch,follows,matched⟩ := game.prescribed_play_l hZF hw dc O filter hits fx fe second
  obtain ⟨_,q,_,fq,old⟩ := game.coordinates_l hZF hw ff branch
  have coords k n a y p (hk : M.mem k ω) (add : M.IsOrdinalAddition I n k k)
      (na : Entry_d M n a f) (pair : KPair_d M a y p) : Entry_d M k y x ∧ Entry_d M k p q :=
    ⟨(matched k n a y p hk add na pair).2.1,(old k n a y p hk add na pair).2⟩
  have step i j p r (succ : M.SuccessorOf j i) (ip : Entry_d M i p q) (jr : Entry_d M j r q) :
      Entry_d M r p T := by
    obtain ⟨_,_,_,_,_,_,_,rp⟩ := game.round_l hZF hw ff branch fx fq coords succ ip jr
    exact rp
  let ρ : Env M 1 := ⟨fun _ => T,fun _ => T⟩
  let φ : BinarySchema 1 := { body := entry_m .newest (.bound 1) (.bound 2) }
  have sat p r : φ.denote ρ p r ↔ Entry_d M r p T := entry_sat_l M hZF.1 ..
  have chain i j p r (ij : M.mem i j) (ip : Entry_d M i p q) (jr : Entry_d M j r q) : Entry_d M r p T :=
    (sat p r).mp (ZF.rel_chain_l I hZF φ ρ hw (fn0_function_l (ZF.modelsKP hZF) fq)
      (fun a b c ha hb hc ab bc => (sat a c).mpr (O.trans c b a hc hb ha ((sat b c).mp bc) ((sat a b).mp ab)))
      (fun i j a b succ ia jb => (sat a b).mpr (step i j a b succ ia jb)) i j p r ij ip jr)
  refine ⟨f,q,⟨ff,branch,fx,?_,fun k n a y p hk add na pair => (coords k n a y p hk add na pair).1⟩,
    follows,fq,coords,chain,?_⟩
  · rintro n a y p na pair ⟨k,hk,add⟩
    exact (matched k n a y p hk add na pair).1
  · intro p ph i hi
    obtain ⟨k,hk,kp⟩ := onto p (filter.proper p ph).1
    obtain ⟨r,_,kr⟩ := fq.2.1 k hk
    obtain ⟨y,_,ky⟩ := fx.2.1 k hk
    obtain ⟨n,a,add,na,pair⟩ := game.coordinate_read_l hZF hw ff branch fx fq coords ky kr
    have rp := (matched k n a y r hk add na pair).2.2 p kp ph
    have later : ∃ l, M.mem l ω ∧ M.mem i l ∧ M.mem k l := by
      rcases (hw.isOrdinal (ZF.modelsKP hZF)).wellOrder.linear.compare i hi k hk with eq | ik | ki
      · obtain ⟨l,succ,hl⟩ := hw.1.2 k hk
        exact ⟨l,hl,(hZF.1.eq_of_same_members i k eq).symm ▸ succ.predecessor_mem,succ.predecessor_mem⟩
      · obtain ⟨l,succ,hl⟩ := hw.1.2 k hk
        exact ⟨l,hl,(succ i).mpr (Or.inl ik),succ.predecessor_mem⟩
      · obtain ⟨l,succ,hl⟩ := hw.1.2 i hi
        exact ⟨l,hl,succ.predecessor_mem,(succ k).mpr (Or.inl ki)⟩
    obtain ⟨l,hl,il,kl⟩ := later
    obtain ⟨t,ht,lt⟩ := fq.2.1 l hl
    exact ⟨l,t,il,lt,O.trans t r p ht (fq.bound_l kr).2 (filter.proper p ph).1 (chain k l r t kl kr lt) rp⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 原幂集计数证书驱动给定泛型的专用对局

小坍缩有限列先内部编码到 δ，再编码到原幂集以取得环境中的实际枚举。
原泛型在指定条件以下命中旧稠密集，故可直接实例化同一原对局构造。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project Descriptive InnerModel Internal Model.Forcing.Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Ag_system_d.ground_play_l {Ω c X R : M.Domain} (hΩ : M.IsOmega Ω) (dc : Dc_d I Ω)
    (source : Smem_d I c X R) (trans : M.TransitiveSet X)
    (native : (smdl_structure_l I (R := R) source.1.2.1).Models ZF)
    {ω κ δ A : (smdl_structure_l I (R := R) source.1.2.1).Domain}
    {p : Ag_forcing_d native ω κ δ A} (s : Ag_system_d native p)
    (hw : (smdl_structure_l I (R := R) source.1.2.1).IsOmega ω)
    (infinite : (smdl_structure_l I (R := R) source.1.2.1).IsInfiniteCardinal (kp_pair_l (ZF.modelsKP native)) ω δ)
    (small : (smdl_structure_l I (R := R) source.1.2.1).MemberSubset κ δ)
    (count : Pc_count_d I Ω X R δ.val) {H x τ : M.Domain}
    (sub : M.MemberSubset H p.Q.val)
    (generic : Generic_d (smdl_structure_l I (R := R) source.1.2.1) p.Q p.T p.Q (fun q => M.mem q.val H))
    (fx : Fn0_d Ω A.val x) (second : Gt_strategy_d hZF false Ω s.A.val s.R₀.val τ) :
    ∃ f q, Ag_trace_d hZF Ω A.val s.A.val s.F₀.val s.R₀.val f x H ∧
      Gm_follows_d I false Ω τ f ∧ Fn0_d Ω p.Q.val q ∧
      (∀ k n a y r, M.mem k Ω → M.IsOrdinalAddition I n k k → Entry_d M n a f →
        KPair_d M a y r → Entry_d M k y x ∧ Entry_d M k r q) ∧
      (∀ i j r t, M.mem i j → Entry_d M i r q → Entry_d M j t q → Entry_d M t r p.T.val) ∧
      ∀ r, M.mem r H → ∀ i, M.mem i Ω → ∃ k t, M.mem i k ∧ Entry_d M k t q ∧ Entry_d M t r p.T.val := by
  let N := smdl_structure_l I (R := R) source.1.2.1
  let J := kp_pair_l (ZF.modelsKP native)
  have inj : Function.Injective (Subtype.val : N.Domain → M.Domain) := fun _ _ eq => Subtype.ext eq
  have full := smem_full_l I source trans
  have hw' := image_omega_l (hEN := hZF.1) Subtype.val inj full native
    (fun _ ne => KP.mem_minimal_exists_d (ZF.modelsKP hZF) ne) hw
    (fun D => KP.difference_exists_d (ZF.modelsKP hZF) D ω.val)
  have eq : ω.val = Ω := hZF.1.eq_of_same_members ω.val Ω
    (fun n => ⟨hw'.2 Ω hΩ.1 n,hΩ.2 ω.val hw'.1 n⟩)
  obtain ⟨i,fi⟩ := ZF.fseq_bound_l J native hw infinite (ZF.exists_inclusionInjection native J small) p.small_space
  obtain ⟨k,fk⟩ := ZF.exists_singletonInjectionToPowerSet native J p.power
  obtain ⟨e,fe,onto⟩ := count.enumeration_l hZF source trans native δ p.K p.Q p.power
    (ZF.exists_compositionInjection native J fi fk) ⟨p.b,p.small_base⟩
  have game := s.source.image_l native hZF Subtype.val inj full hw hw'
  have order := image_cond_order_l (ZF.modelsKP native) hZF.1 Subtype.val inj full p.small_order
  have values y : M.mem y H ↔ ∃ q : N.Domain, M.mem q.val H ∧ q.val = y := by
    refine ⟨fun hy => ?_,?_⟩
    · obtain ⟨q,_,qy⟩ := (full p.Q y).mp (sub y hy)
      exact ⟨q,qy.symm ▸ hy,qy⟩
    · rintro ⟨q,hq,rfl⟩
      exact hq
  have filter : Gset_d p.Q.val p.T.val p.Q.val s.E.val H :=
    image_gset_l native hZF.1 Subtype.val inj full generic values
  have hits : ∀ E, M.mem E s.E.val → ∀ r, M.mem r H →
      ∃ t, M.mem t H ∧ M.mem t E ∧ Entry_d M t r p.T.val := by
    intro E hE r rh
    obtain ⟨D,hD,rfl⟩ := (full s.E E).mp hE
    obtain ⟨a,_,rfl⟩ := (full p.Q r).mp (sub r rh)
    obtain ⟨b,bH,bD,ba⟩ := generic.meets_below_l native p.small_order rh
      (fun q hq => (s.source.dense D hD).2 q hq.1 hq.2.1)
    exact ⟨b.val,bH,(image_member_l Subtype.val inj full).mpr bD,
      (image_entry_iff_l Subtype.val inj full (KP.exists_pair (ZF.modelsKP native)) hZF.1 b a p.T).mp ba⟩
  have game : Ag_game_d hZF Ω A.val p.Q.val p.T.val s.E.val s.B.val s.A.val s.F₀.val s.R₀.val := by
    simpa only [eq] using! game
  exact game.cofinal_play_l hZF hΩ dc order filter hits fx (fn0_of_function_l (ZF.modelsKP hZF) fe) onto second

end YesMetaZFC.SetTheory.LargeCardinal
