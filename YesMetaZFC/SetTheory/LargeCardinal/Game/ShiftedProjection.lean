import YesMetaZFC.Model.SetTheory.Internal.FiniteRecordRelative
import YesMetaZFC.Model.SetTheory.Game.GraphUnion
import YesMetaZFC.SetTheory.Descriptive.Tree.TreeTail
import YesMetaZFC.Model.SetTheory.Game.NodeEmbedding
import YesMetaZFC.SetTheory.Descriptive.Game.ClosedDeterminacy
import YesMetaZFC.SetTheory.Descriptive.Game.GameShift
import YesMetaZFC.SetTheory.Descriptive.Game.GameStrategyProjection
import YesMetaZFC.SetTheory.Descriptive.Tree.HistoryTree
import YesMetaZFC.SetTheory.FunctionSpaceAlgebra
import YesMetaZFC.SetTheory.Descriptive.Tree.TreeShift
import YesMetaZFC.SetTheory.LargeCardinal.Iteration.CriticalBound
import YesMetaZFC.SetTheory.LargeCardinal.Iteration.ReturnFactor
import YesMetaZFC.SetTheory.Rank

/-! # 实际有限节点列的三图统一取并

每行保存长度、树和三张同域图。相邻长度恰增一，图列相容，
故其并图的定义域为整个内部ω，每个有限图都是并图的精确限制。
本层只消费实际节点列，不依赖原档案的编码或分支返回方式。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

structure Tg_node_sequence_d (I : kpair_convention_l.Interpretation M) (ω N D F : M.Domain) : Prop where
  omega : M.IsOmega ω
  transitive : M.TransitiveSet N
  function : Fn0_d ω D F
  codes : ∀ i r, Rd_entry_d i r F → ∃ v : Fin 5 → M.Domain, Rt_tuple_d v r
  rows : ∀ i r (v : Fin 5 → M.Domain), Rd_entry_d i r F → Rt_tuple_d v r →
    M.mem (v 0) ω ∧ (∀ a, M.mem (v a) N) ∧ Tg_node_d I (v 0) (v 1) (v 2) (v 3) (v 4)
  steps : ∀ i j r s (v w : Fin 5 → M.Domain), M.SuccessorOf j i → Rd_entry_d i r F → Rd_entry_d j s F →
    Rt_tuple_d v r → Rt_tuple_d w s → M.SuccessorOf (w 0) (v 0) ∧
      ∀ a : Fin 3, M.MemberSubset (v ([2,3,4].get a)) (w ([2,3,4].get a))

variable (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

def Tg_return_union_d (ω N F : M.Domain) (a : Fin 3) (g : M.Domain) : Prop := Fn0_d ω N g ∧
  (∀ p, M.mem p g ↔ ∃ i r, ∃ v : Fin 5 → M.Domain, Rd_entry_d i r F ∧ Rt_tuple_d v r ∧ M.mem p (v ([2,3,4].get a))) ∧
  ∀ i r (v : Fin 5 → M.Domain), Rd_entry_d i r F → Rt_tuple_d v r → M.IsRestrictionOf I (v ([2,3,4].get a)) g (v 0)

theorem Tg_node_sequence_d.union_l {ω N D F : M.Domain}
    (h : Tg_node_sequence_d I ω N D F) (a : Fin 3) : ∃ g, Tg_return_union_d hZF ω N F a g := by
  obtain ⟨L,lf,ls⟩ := rt_coordinate_l hZF (0 : Fin 5) h.function h.codes
    (fun i r v hr code => (h.rows i r v hr code).1)
  obtain ⟨G,gf,gs⟩ := rt_coordinate_l hZF ([2,3,4].get a : Fin 5) h.function h.codes
    (fun i r v hr code => (h.rows i r v hr code).2.1 ([2,3,4].get a))
  have lv {i r} {v : Fin 5 → M.Domain} (hr : Rd_entry_d i r F) (code : Rt_tuple_d v r) : Rd_entry_d i (v 0) L :=
    (ls i (v 0)).mpr ⟨r,hr,v,code,rfl⟩
  have gv {i r} {v : Fin 5 → M.Domain} (hr : Rd_entry_d i r F) (code : Rt_tuple_d v r) : Rd_entry_d i (v ([2,3,4].get a)) G :=
    (gs i (v ([2,3,4].get a))).mpr ⟨r,hr,v,code,rfl⟩
  have data i (hi : M.mem i ω) : ∃ r, ∃ v : Fin 5 → M.Domain, Rd_entry_d i r F ∧ Rt_tuple_d v r := by
    obtain ⟨r,_,hr⟩ := h.function.2.1 i hi
    obtain ⟨v,code⟩ := h.codes i r hr
    exact ⟨r,v,hr,code⟩
  have finite i n g (hn : Rd_entry_d i n L) (hg : Rd_entry_d i g G) : Tg_graph_d I n g := by
    obtain ⟨r,v,hr,code⟩ := data i (lf.bound_l hn).1
    have en := (fn0_function_l (ZF.modelsKP hZF) lf).1.2 i (v 0) n (lv hr code) hn
    have eg := (fn0_function_l (ZF.modelsKP hZF) gf).1.2 i (v ([2,3,4].get a)) g (gv hr code) hg
    have node := (h.rows i r v hr code).2.2
    exact en ▸ eg ▸ (Fin.cases node.1 (Fin.cases node.2.1 (Fin.cases node.2.2.1 (fun i => Fin.elim0 i))) a)
  have step i j n m (succ : M.SuccessorOf j i) (hn : Rd_entry_d i n L) (hm : Rd_entry_d j m L) : M.SuccessorOf m n := by
    obtain ⟨r,v,hr,code⟩ := data i (lf.bound_l hn).1
    obtain ⟨s,w,hs,pack⟩ := data j (lf.bound_l hm).1
    have en := (fn0_function_l (ZF.modelsKP hZF) lf).1.2 i (v 0) n (lv hr code) hn
    have em := (fn0_function_l (ZF.modelsKP hZF) lf).1.2 j (w 0) m (lv hs pack) hm
    exact en ▸ em ▸ (h.steps i j r s v w succ hr hs code pack).1
  have grow i j g k (succ : M.SuccessorOf j i) (hg : Rd_entry_d i g G) (hk : Rd_entry_d j k G) : M.MemberSubset g k := by
    obtain ⟨r,v,hr,code⟩ := data i (gf.bound_l hg).1
    obtain ⟨s,w,hs,pack⟩ := data j (gf.bound_l hk).1
    have eg := (fn0_function_l (ZF.modelsKP hZF) gf).1.2 i (v ([2,3,4].get a)) g (gv hr code) hg
    have ek := (fn0_function_l (ZF.modelsKP hZF) gf).1.2 j (w ([2,3,4].get a)) k (gv hs pack) hk
    exact eg ▸ ek ▸ (h.steps i j r s v w succ hr hs code pack).2 a
  obtain ⟨g,fn,union,cuts⟩ := tg_graph_union_l hZF h.omega h.transitive lf gf finite step grow
  refine ⟨g,fn,fun p => (union p).trans ⟨?_,?_⟩,
    fun i r v hr code => cuts i (v 0) (v ([2,3,4].get a)) (lv hr code) (gv hr code)⟩
  · rintro ⟨i,g,hg,hp⟩
    obtain ⟨r,hr,v,code,eq⟩ := (gs i g).mp hg
    exact ⟨i,r,v,hr,code,eq.symm ▸ hp⟩
  · rintro ⟨i,r,v,hr,code,hp⟩
    exact ⟨i,v ([2,3,4].get a),gv hr code,hp⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 同一有限节点列的三图合成为共尾分支

三张并图先合成实际ω列。每份有限节点的三图都包含于对应并图，
函数性与配对唯一性遂保持合成图；长度共尾保证任意指标之后都有属于共同树的前缀。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal Descriptive
universe u
variable {M : Structure.{u}} {I : kpair_convention_l.Interpretation M}

/-- 三张坐标图的包含与定义域包含共同保持合成图；不需要集合论公理。 -/
theorem Tg_join_d.subset_l {n m s t g q s' t' g' q' : M.Domain}
    (left : Tg_join_d I n s t g q) (right : Tg_join_d I m s' t' g' q')
    (fs : M.IsSetFunction I s') (ft : M.IsSetFunction I t') (fg : M.IsSetFunction I g')
    (nm : M.MemberSubset n m) (ss : M.MemberSubset s s') (tt : M.MemberSubset t t')
    (gg : M.MemberSubset g g') : M.MemberSubset q q' := by
  intro p hp
  obtain ⟨i,x,pair⟩ := left.1.1.1 p hp
  have hx : M.PairMember I i x q := ⟨p,pair,hp⟩
  have hi := (left.1.2 i).mpr ⟨x,hx⟩
  obtain ⟨a,b,c,z,y,ha,hb,hc,hz,hy,iy⟩ := left.2 i hi
  have xy := left.1.1.2 i x y hx iy
  have inc {a b U V : M.Domain} (sub : M.MemberSubset U V) (h : M.PairMember I a b U) : M.PairMember I a b V :=
    h.elim fun r hr => ⟨r,hr.1,sub r hr.2⟩
  obtain ⟨a',b',c',z',y',ha',hb',hc',hz',hy',iy'⟩ := right.2 i (nm i hi)
  have ea := fs.2 i a a' (inc ss ha) ha'
  have eb := ft.2 i b b' (inc tt hb) hb'
  have ec := fg.2 i c c' (inc gg hc) hc'
  have ez := I.unique hz (eb.symm ▸ ec.symm ▸ hz')
  have ey := I.unique hy (ea.symm ▸ ez.symm ▸ hy')
  obtain ⟨r,rp,hq⟩ := iy'
  exact I.unique rp ((xy.trans ey) ▸ pair) ▸ hq

variable (hZF : M.Models ZF)
local notation "J" => kp_pair_l (ZF.modelsKP hZF)

def Tg_cofinal_branch_d (ω X S f : M.Domain) : Prop := Fn0_d ω X f ∧
  ∀ n, M.mem n ω → ∃ m q, M.mem n m ∧ M.mem m ω ∧ M.mem q S ∧ Tg_graph_d J m q ∧ M.MemberSubset q f

/-- 共同树中的实际有限节点合成为三张并图的共尾无限合成。 -/
theorem Tg_node_sequence_d.branch_join_l {ω N D F S : M.Domain} {g : Fin 3 → M.Domain}
    (h : Tg_node_sequence_d J ω N D F)
    (trees : ∀ i r (v : Fin 5 → M.Domain), Rd_entry_d i r F → Rt_tuple_d v r → v 1 = S)
    (unions : ∀ a, Tg_return_union_d hZF ω N F a (g a)) :
    ∃ Y q, Tg_cofinal_branch_d hZF ω Y S q ∧ Tg_join_d J ω (g 0) (g 1) (g 2) q := by
  have fn a := fn0_function_l (ZF.modelsKP hZF) (unions a).1
  obtain ⟨V,Y,q,_,_,fq,join⟩ := tg_join_exists_l J hZF (fn 0) (fn 1) (fn 2)
  refine ⟨Y,q,⟨fn0_of_function_l (ZF.modelsKP hZF) fq,?_⟩,join⟩
  intro n hn
  obtain ⟨z,_,⟨p,pair,hp⟩⟩ := (unions 2).1.2.1 n hn
  obtain ⟨i,r,v,hr,code,hp⟩ := ((unions 2).2.1 p).mp hp
  obtain ⟨finite,_,node⟩ := h.rows i r v hr code
  have nlen : M.mem n (v 0) := (node.2.2.1.2 n).mpr ⟨z,p,pair,hp⟩
  have sub (a : Fin 3) : M.MemberSubset (v ([2,3,4].get a)) (g a) :=
    fun p hp => ((unions a).2.1 p).mpr ⟨i,r,v,hr,code,hp⟩
  obtain ⟨_,_,_,q',member,joined⟩ := node
  exact ⟨v 0,q',nlen,finite,trees i r v hr code ▸ member,joined.1,
    Tg_join_d.subset_l joined join (fn 0).1 (fn 1).1 (fn 2).1
      (h.omega.transitive (ZF.modelsKP hZF) _ finite) (sub 0) (sub 1) (sub 2)⟩

theorem Tg_cofinal_branch_d.branch_l {ω X S f A F : M.Domain}
    (h : Tg_cofinal_branch_d hZF ω X S f) (hw : M.IsOmega ω)
    (space : Fseq_space_d J ω A F) (tree : Tree_d F S) : Fn0_d ω A f ∧ Branch_d F S f := by
  have fn := fn0_function_l (ZF.modelsKP hZF) h.1
  have inside {n m q} (nm : M.mem n m) (hm : M.mem m ω) (gq : Tg_graph_d J m q) (sub : M.MemberSubset q f)
      {s} (fs : M.IsSetFunctionFromTo J s n A) (sf : M.MemberSubset s f) : M.MemberSubset s q := by
    intro p hp
    obtain ⟨i,x,pair⟩ := fs.1.1 p hp
    have ix : Rd_entry_d i x s := ⟨p,pair,hp⟩
    have hi := (hw.members_areOrdinals (ZF.modelsKP hZF) m hm).transitive n nm i (fs.input_mem_of_pairMember ix)
    obtain ⟨y,⟨r,rp,hr⟩⟩ := (gq.2 i).mp hi
    have eq := fn.1.2 i x y ⟨p,pair,sf p hp⟩ ⟨r,rp,sub r hr⟩
    exact kpair_unique_l M hZF.1 rp (eq ▸ pair) ▸ hr
  refine ⟨?_,fun s hs sub => ?_⟩
  · have bound {i x} (hx : Rd_entry_d i x f) : M.mem x A := by
      obtain ⟨m,q,im,_,hq,gq,sub⟩ := h.2 i (h.1.bound_l hx).1
      obtain ⟨y,⟨p,pp,hp⟩⟩ := (gq.2 i).mp im
      have eq := fn.1.2 i x y hx ⟨p,pp,sub p hp⟩
      obtain ⟨_,_,fq⟩ := (space q).mp (tree.1 q hq)
      exact eq.symm ▸ fq.output_mem_of_pairMember ⟨p,pp,hp⟩
    exact fn0_of_function_l (ZF.modelsKP hZF) ⟨fn.1,fn.2.1,
      fun i hi => (fn.2.2 i hi).elim fun x hx => ⟨x,bound hx.2,hx.2⟩⟩
  · obtain ⟨n,hn,fs⟩ := (space s).mp hs
    obtain ⟨m,q,nm,hm,hq,gq,qf⟩ := h.2 n hn
    exact tree.2 q hq s hs (inside nm hm gq qf fs sub)

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 三坐标树的投影博弈

两条策略转移共用同一个实际收益集合：树体第一投影的补集。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal Descriptive
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

def Tg_projection_d (ω Y T S x : M.Domain) : Prop := ∃ q t u,
  Fn0_d ω Y q ∧ Branch_d T S q ∧ Tg_graph_d I ω t ∧ Tg_graph_d I ω u ∧ Tg_join_d I ω x t u q

def tg_projection_m {d} (ω Y T S x : Term d) : Formula 1 d := set[d] ⟪∃ q t u,
  ⌜fn0_m⌝ₚ(⌜ω⌝ₛ,⌜Y⌝ₛ,q) ∧ ⌜branch_m⌝ₚ(⌜T⌝ₛ,⌜S⌝ₛ,q) ∧
  ⌜tg_graph_m⌝ₚ(⌜ω⌝ₛ,t) ∧ ⌜tg_graph_m⌝ₚ(⌜ω⌝ₛ,u) ∧ ⌜tg_join_m⌝ₚ(⌜ω⌝ₛ,⌜x⌝ₛ,t,u,q)⟫
derive_free_closed tg_projection_m

theorem tg_projection_sat_l {d} (ρ : Env M d) (ω Y T S x : Term d) :
    Formula.satisfies ρ (tg_projection_m ω Y T S x) ↔
      Tg_projection_d hZF (ω.eval ρ) (Y.eval ρ) (T.eval ρ) (S.eval ρ) (x.eval ρ) := by
  simp only [tg_projection_m, Tg_projection_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    fn0_sat_l hZF.1, branch_sat_l, tg_graph_sat_l I hZF.1, tg_join_sat_l I hZF.1, Definitional.Term.eval_weaken]; rfl

def Tg_projection_win_d (b : Bool) (ω A Y T S : M.Domain) : Prop :=
  ∃ F J B W σ, Fseq_space_d I ω A F ∧ M.IsFunctionSpace I B ω A ∧
    (∀ n, M.mem n J ↔ M.mem n ω ∧ Gm_even_d I ω n) ∧
    (∀ f, M.mem f W ↔ M.mem f B ∧ ¬ Tg_projection_d hZF ω Y T S f) ∧ Cg_win_d I b ω A F J B W σ

/-! 将固定偶数时序的 `Cg_win_d` 运输回原始 `Gm_win_d`。

`Tg_projection_win_d` 的收益策略已经是 scheduled game 的策略，而
`Det_d` 使用同一有限历史空间上的未显式命名时序。下面的两步只读取
`J` 的精确偶数刻画，不引入任何外部 ω 标准性或选择参数。
-/

theorem cg_follows_gm_l {b : Bool} {ω J σ f : M.Domain}
    (turns : ∀ n, M.mem n J ↔ M.mem n ω ∧ Gm_even_d I ω n) :
    Cg_follows_d I b ω J σ f ↔ Gm_follows_d I b ω σ f := by
  constructor
  · intro h i hi own s hs a ha
    have turn : (if b then M.mem i J else ¬ M.mem i J) := by
      cases b with
      | false =>
          intro hj
          exact own ((turns i).mp hj).2
      | true =>
          exact (turns i).mpr ⟨hi, own⟩
    exact h i hi turn s hs a ha
  · intro h i hi turn s hs a ha
    have own : Gm_turn_d I b ω i := by
      cases b with
      | false =>
          intro even
          exact turn ((turns i).mpr ⟨hi, even⟩)
      | true =>
          exact (turns i).mp turn |>.2
    exact h i hi own s hs a ha

theorem cg_win_gm_l {b : Bool} {ω F J B W σ : M.Domain}
    (turns : ∀ n, M.mem n J ↔ M.mem n ω ∧ Gm_even_d I ω n)
    (win : Cg_win_d I b ω ω F J B W σ) :
    Gm_win_d I b ω B F W σ := by
  exact ⟨fn0_function_l (ZF.modelsKP hZF) win.1, fun f hf follows => win.2 f hf
    ((cg_follows_gm_l hZF turns).mpr follows)⟩

theorem Tg_projection_win_d.det_l {b : Bool} {ω Y T S : M.Domain}
    (win : Tg_projection_win_d hZF b ω ω Y T S) :
    ∃ (B F W : M.Domain), Det_d I ω B F W ∧
      M.IsFunctionSpace I B ω ω ∧ Fseq_space_d I ω ω F := by
  rcases win with ⟨F, J, B, W, σ, space, runs, turns, payoff, win⟩
  have converted : Gm_win_d I b ω B F W σ := cg_win_gm_l hZF turns win
  cases b with
  | false => exact ⟨B, F, W, Or.inr ⟨σ, converted⟩, runs, space⟩
  | true => exact ⟨B, F, W, Or.inl ⟨σ, converted⟩, runs, space⟩

/-- 收益集已识别为投影补集时，将同一胜策放回指定的 Baire 空间。 -/
theorem Tg_projection_win_d.det_of_complement_l
    {b : Bool} {ω A Y T S B' T' : M.Domain}
    (hB : Baire_d I ω B') (hT : Fseq_space_d I ω ω T')
    (win : Tg_projection_win_d hZF b ω ω Y T S)
    (hA : M.MemberSubset A B')
    (eqA : ∀ f, M.mem f B' → (M.mem f A ↔ ¬Tg_projection_d hZF ω Y T S f)) :
    Det_d I ω B' T' A := by
  obtain ⟨F, J, B, W, σ, space, runs, turns, payoff, win⟩ := win
  have det : Det_d I ω B F W := by
    have gm := cg_win_gm_l hZF turns win
    cases b with
    | false => exact Or.inr ⟨σ, gm⟩
    | true => exact Or.inl ⟨σ, gm⟩
  have eB : B = B' := ds_space_unique_l I hZF.1 runs hB.2
  subst B
  have eF : F = T' := hZF.1.eq_of_same_members F T' (fun s => (space s).trans (hT s).symm)
  have eW : W = A := hZF.1.eq_of_same_members W A (fun f => by
    rw [payoff]
    exact ⟨fun ⟨hf, hn⟩ => (eqA f hf).mpr hn,
      fun hf => ⟨hA f hf, (eqA f (hA f hf)).mp hf⟩⟩)
  exact eF ▸ eW ▸ det

theorem tg_projection_game_l {ω : M.Domain} (hw : M.IsOmega ω) (A Y T S : M.Domain) :
    ∃ F J B W, Fseq_space_d I ω A F ∧ M.IsFunctionSpace I B ω A ∧
      (∀ n, M.mem n J ↔ M.mem n ω ∧ Gm_even_d I ω n) ∧
      ∀ f, M.mem f W ↔ M.mem f B ∧ ¬ Tg_projection_d hZF ω Y T S f := by
  obtain ⟨F, finite⟩ := ZF.fseq_space_exists_l I hZF hw A
  obtain ⟨B, bs⟩ := ZF.exists_functionSpace hZF I ω A
  let η : Env M 1 := ⟨fun _ => ω, fun _ => ω⟩
  let even : UnarySchema 1 := { body := gm_even_m (𝒞 := kpair_convention_l) (.bound 1) .newest }
  obtain ⟨J, js⟩ := ZF.separation_exists_d hZF even η ω
  have turns n : M.mem n J ↔ M.mem n ω ∧ Gm_even_d I ω n :=
    (js n).trans (and_congr_right fun _ => gm_even_sat_l I hZF.1 (η.push n) (.bound 1) .newest)
  let ρ : Env M 4 := ⟨fun i => [ω, Y, T, S].get i, fun _ => ω⟩
  let φ : UnarySchema 4 := { body := .neg (tg_projection_m (.bound 1) (.bound 2) (.bound 3) (.bound 4) .newest) }
  obtain ⟨W, ws⟩ := ZF.separation_exists_d hZF φ ρ B
  exact ⟨F, J, B, W, finite, bs, turns, fun f =>
    (ws f).trans (and_congr_right fun _ => (Formula.satisfies_neg_iff ..).trans (not_congr (tg_projection_sat_l hZF ..)))⟩

/-- 缺少空根时没有分支，实际常值策略已经获胜；不额外假设树非空。 -/
theorem tg_projection_no_root_l {ω A Y T S e a : M.Domain} (hw : M.IsOmega ω)
    (he : ∀ x, ¬ M.mem x e) (ha : M.mem a A) (space : Fseq_space_d I ω Y T) (root : ¬ M.mem e S) :
    Tg_projection_win_d hZF true ω A Y T S := by
  obtain ⟨F, J, B, W, finite, bs, turns, payoff⟩ := tg_projection_game_l hZF hw A Y T S
  obtain ⟨σ, fn, _⟩ := ZF.exists_constantFunction hZF I (source := F) ha
  refine ⟨F, J, B, W, σ, finite, bs, turns, payoff, fn0_of_function_l (ZF.modelsKP hZF) fn, fun f hf _ =>
    (payoff f).mpr ⟨hf, ?_⟩⟩
  rintro ⟨q, _, _, _, branch, _⟩
  have empty := tg_graph_empty_l I he
  exact root (branch e ((space e).mpr ⟨e, num_mem_l hZF.1 hw (show Num_d 0 e from he),
    empty.1, empty.2, fun i hi => (he i hi).elim⟩) (fun x hx => (he x hx).elim))

/-- 共尾节点与三图合成给出普通投影；此处没有第一辅助图的满射结论。 -/
theorem Tg_cofinal_branch_d.projection_l
    {ω X A F S x q t u : M.Domain}
    (h : Tg_cofinal_branch_d hZF ω X S q) (hw : M.IsOmega ω)
    (space : Fseq_space_d I ω A F) (tree : Tree_d F S)
    (gt : Tg_graph_d I ω t) (gu : Tg_graph_d I ω u)
    (join : Tg_join_d I ω x t u q) :
    Tg_projection_d hZF ω A F S x := by
  obtain ⟨typed, branch⟩ := h.branch_l hZF hw space tree
  exact ⟨q, t, u, typed, branch, gt, gu, join⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 固定有限序列空间的投影博弈数据

`tg_projection_game_l` 同时生成有限序列空间。本文件保留调用方已经拥有的
空间，单独生成函数空间、偶数时序和补投影收益集，避免策略域发生错配。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal

open Definitional.Project InnerModel Internal Descriptive
universe u
variable {M : Structure.{u}}

theorem tg_projection_game_on_space_l
    (hZF : M.Models ZF)
    {ω A Y T S : M.Domain}
    :
    ∃ J B W,
      M.IsFunctionSpace (kp_pair_l (ZF.modelsKP hZF)) B ω A ∧
      (∀ n, M.mem n J ↔
        M.mem n ω ∧ Gm_even_d (kp_pair_l (ZF.modelsKP hZF)) ω n) ∧
      (∀ f, M.mem f W ↔
        M.mem f B ∧ ¬ Tg_projection_d hZF ω Y T S f) := by
  let I := kp_pair_l (ZF.modelsKP hZF)
  obtain ⟨B, bs⟩ := ZF.exists_functionSpace hZF I ω A
  let η : Env M 1 := ⟨fun _ => ω, fun _ => ω⟩
  let even : UnarySchema 1 :=
    { body := gm_even_m (𝒞 := kpair_convention_l) (.bound 1) .newest }
  obtain ⟨J, js⟩ := ZF.separation_exists_d hZF even η ω
  have turns n : M.mem n J ↔
      M.mem n ω ∧ Gm_even_d I ω n :=
    (js n).trans (and_congr_right fun _ =>
      gm_even_sat_l I hZF.1 (η.push n) (.bound 1) .newest)
  let ρ : Env M 4 := ⟨fun i => [ω, Y, T, S].get i, fun _ => ω⟩
  let φ : UnarySchema 4 :=
    { body := .neg (tg_projection_m (.bound 1) (.bound 2) (.bound 3) (.bound 4) .newest) }
  obtain ⟨W, ws⟩ := ZF.separation_exists_d hZF φ ρ B
  refine ⟨J, B, W, bs, turns, ?_⟩
  intro f
  exact (ws f).trans (and_congr_right fun _ =>
    (Formula.satisfies_neg_iff ..).trans (not_congr (tg_projection_sat_l hZF ..)))

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 5.23 策略到投影博弈获胜

给定一个实际的本方回合策略，以及该策略所有服从对局的投影见证，
把它接到固定偶数时序的投影博弈。全域化和时序转换由描述性层的通用接口完成。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal

open Definitional.Project InnerModel Internal Descriptive
universe u
variable {M : Structure.{u}}

theorem Tg_projection_win_d.of_gm_strategy_l
    (hZF : M.Models ZF)
    {ω A F J B W Y T S σ a : M.Domain}
    (hw : M.IsOmega ω)
    (space : Fseq_space_d (kp_pair_l (ZF.modelsKP hZF)) ω A F)
    (functions : M.IsFunctionSpace (kp_pair_l (ZF.modelsKP hZF)) B ω A)
    (turns : ∀ n, M.mem n J ↔
      M.mem n ω ∧ Gm_even_d (kp_pair_l (ZF.modelsKP hZF)) ω n)
    (payoff : ∀ f, M.mem f W ↔
      M.mem f B ∧ ¬ Tg_projection_d hZF ω Y T S f)
    (strategy : Gm_strategy_d (kp_pair_l (ZF.modelsKP hZF)) false ω A F σ)
    (good : ∀ f, Fn0_d ω A f →
      Gm_follows_d (kp_pair_l (ZF.modelsKP hZF)) false ω σ f →
      Tg_projection_d hZF ω Y T S f)
    (ha : M.mem a A) :
    Tg_projection_win_d hZF false ω A Y T S := by
  obtain ⟨τ, win⟩ := Gm_strategy_d.to_cg_win_l hZF hw space functions turns payoff
    strategy (fun f input follows hnot => hnot (good f input follows)) ha
  exact ⟨F, J, B, W, τ, space, functions, turns, payoff, win⟩

/-! 调用方只需提供已有的有限序列空间和逐局投影见证时，
函数空间、偶数时序及补收益集均由分离自动生成。 -/
theorem Tg_projection_win_d.of_gm_strategy_on_space_l
    (hZF : M.Models ZF)
    {ω A F Y T S σ a : M.Domain}
    (hw : M.IsOmega ω)
    (space : Fseq_space_d (kp_pair_l (ZF.modelsKP hZF)) ω A F)
    (strategy : Gm_strategy_d (kp_pair_l (ZF.modelsKP hZF)) false ω A F σ)
    (good : ∀ f, Fn0_d ω A f →
      Gm_follows_d (kp_pair_l (ZF.modelsKP hZF)) false ω σ f →
      Tg_projection_d hZF ω Y T S f)
    (ha : M.mem a A) :
    Tg_projection_win_d hZF false ω A Y T S := by
  obtain ⟨J, B, W, functions, turns, payoff⟩ :=
    tg_projection_game_on_space_l hZF (ω := ω) (A := A) (Y := Y) (T := T) (S := S)
  exact Tg_projection_win_d.of_gm_strategy_l hZF hw space functions turns payoff strategy good ha

end YesMetaZFC.SetTheory.LargeCardinal

/-! 同一实际初等图上的投影见证搬运。

该接口把剩余 bookkeeping 明确拆成三个可检查字段：目标字母函数图、目标树枝、
以及五个 join 坐标的实际图像。`Smap_d.tg_graph_l` 与 `Smap_d.tg_join_l`
负责公式层运输，本定理只装配目标投影见证。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal

open Definitional.Project InnerModel Internal Descriptive
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

structure Tg_projection_transport_d (hZ : M.Models ZF)
    (ω Y F S Y' F' S' x : M.Domain) where
  q : M.Domain
  t : M.Domain
  u : M.Domain
  q' : M.Domain
  t' : M.Domain
  u' : M.Domain
  j : M.Domain
  source_fn : Fn0_d ω Y q
  source_branch : Branch_d F S q
  source_graph_t : Tg_graph_d (kp_pair_l (ZF.modelsKP hZ)) ω t
  source_graph_u : Tg_graph_d (kp_pair_l (ZF.modelsKP hZ)) ω u
  source_join : Tg_join_d (kp_pair_l (ZF.modelsKP hZ)) ω x t u q
  target_fn : Fn0_d ω Y' q'
  target_branch : Branch_d F' S' q'
  c : M.Domain
  d : M.Domain
  X : M.Domain
  R : M.Domain
  Z : M.Domain
  T : M.Domain
  xt : M.TransitiveSet X
  zt : M.TransitiveSet Z
  mx : Smem_d (kp_pair_l (ZF.modelsKP hZ)) c X R
  mz : Smem_d (kp_pair_l (ZF.modelsKP hZ)) d Z T
  map : Smap_d (kp_pair_l (ZF.modelsKP hZ)) ω c d X Z j
  hω : Rd_entry_d ω ω j
  hx : Rd_entry_d x x j
  ht : Rd_entry_d t t' j
  hu : Rd_entry_d u u' j
  hq : Rd_entry_d q q' j

theorem Smap_d.tg_projection_map_l
    {ω ω' x x' t t' u u' q q' Y' F' S' : M.Domain}
    {c d X R Z T : M.Domain}
    (hw : M.IsOmega ω)
    (xt : M.TransitiveSet X) (zt : M.TransitiveSet Z)
    (mx : Smem_d I c X R) (mz : Smem_d I d Z T)
    (map : Smap_d I ω c d X Z j)
    (images : Rd_entry_d ω ω' j ∧ Rd_entry_d x x' j ∧
      Rd_entry_d t t' j ∧ Rd_entry_d u u' j ∧ Rd_entry_d q q' j)
    (branch : Branch_d F' S' q')
    (graph_t : Tg_graph_d I ω t)
    (graph_u : Tg_graph_d I ω u)
    (join : Tg_join_d I ω x t u q)
    (target_fn : Fn0_d ω' Y' q') :
    Tg_projection_d hZF ω' Y' F' S' x' := by
  obtain ⟨hω, hx, ht, hu, hq⟩ := images
  have graph_t' := (map.tg_graph_l hZF hw xt zt mx mz hω ht).mp graph_t
  have graph_u' := (map.tg_graph_l hZF hw xt zt mx mz hω hu).mp graph_u
  have join_images : ∀ i : Fin 5,
      Rd_entry_d
        (Fin.cases ω (Fin.cases x (Fin.cases t (Fin.cases u (fun _ => q)))) i)
        (Fin.cases ω' (Fin.cases x' (Fin.cases t' (Fin.cases u' (fun _ => q')))) i) j := by
    intro i
    refine Fin.cases hω ?_ i
    intro i
    refine Fin.cases hx ?_ i
    intro i
    refine Fin.cases ht ?_ i
    intro i
    refine Fin.cases hu ?_ i
    intro i
    exact Fin.cases hq (fun i => Fin.elim0 i) i
  have join' := (map.tg_join_l hZF hw xt zt mx mz join_images).mp join
  exact ⟨q', t', u', target_fn, branch, graph_t', graph_u', join'⟩

theorem Tg_projection_win_d.of_gm_strategy_transport_l
    (hZ : M.Models ZF)
    {ω A C σ Y F S Y' F' S' : M.Domain}
    (hw : M.IsOmega ω)
    (space : Fseq_space_d (kp_pair_l (ZF.modelsKP hZ)) ω A C)
    (strategy : Gm_strategy_d (kp_pair_l (ZF.modelsKP hZ)) false ω A C σ)
    (transport : ∀ f, Fn0_d ω A f →
      Gm_follows_d (kp_pair_l (ZF.modelsKP hZ)) false ω σ f →
      Tg_projection_transport_d hZ ω Y F S Y' F' S' f)
    {a : M.Domain} (ha : M.mem a A) :
    Tg_projection_win_d hZ false ω A Y' F' S' := by
  exact Tg_projection_win_d.of_gm_strategy_on_space_l hZ hw space strategy
    (fun f input follows => by
      obtain ⟨q, t, u, q', t', u', j, source_fn, source_branch, graph_t, graph_u,
        source_join, target_fn, target_branch, c, d, X, R, Z, T, xt, zt, mx, mz, map,
        hω, hx, ht, hu, hq⟩ := transport f input follows
      exact Smap_d.tg_projection_map_l hZ hw xt zt mx mz map
        ⟨hω, hx, ht, hu, hq⟩ target_branch graph_t graph_u source_join target_fn)
    ha

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 6.7 的无约束坐标：实际字母映射与二坐标投影

删除三元字母的中坐标 (a,(n,γ))↦(a,γ)。该映射的逆像树保留任意中坐标，
二坐标投影直接量化原树分支，不以三坐标游戏充当定义。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal Descriptive
universe u
variable {M : Structure.{u}} (I : kpair_convention_l.Interpretation M)

def Tv_drop_value_d (p q : M.Domain) : Prop := ∃ a b c v,
  (I).Codes p a v ∧ (I).Codes v b c ∧ (I).Codes q a c

def tv_drop_value_m {d} (p q : Term d) : Formula 1 d := set[d] ⟪∃ a b c v,
  ⌜kpair_convention_l.code⌝ₚ(⌜p⌝ₛ,a,v) ∧ ⌜kpair_convention_l.code⌝ₚ(v,b,c) ∧ ⌜kpair_convention_l.code⌝ₚ(⌜q⌝ₛ,a,c)⟫
derive_free_closed tv_drop_value_m

theorem tv_drop_value_sat_l {d} (ρ : Env M d) (p q : Term d) :
    Formula.satisfies ρ (tv_drop_value_m p q) ↔ Tv_drop_value_d I (p.eval ρ) (q.eval ρ) := by
  simp only [tv_drop_value_m, Tv_drop_value_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    I.satisfies_code_iff, Definitional.Term.eval_weaken]; rfl

theorem Tv_drop_value_d.unique_l {p q r : M.Domain} (h : Tv_drop_value_d I p q) (k : Tv_drop_value_d I p r) : q = r := by
  obtain ⟨a, b, c, v, ap, bc, ac⟩ := h
  obtain ⟨a', b', c', v', ap', bc', ac'⟩ := k
  obtain ⟨rfl, rfl⟩ := I.injective ap ap'
  obtain ⟨rfl, rfl⟩ := I.injective bc bc'
  exact I.unique ac ac'

def Tv_drop_d (Y Z d : M.Domain) : Prop := M.IsSetFunctionFromTo I d Y Z ∧
  ∀ p q, M.PairMember I p q d ↔ M.mem p Y ∧ Tv_drop_value_d I p q

theorem tv_drop_l (hZF : M.Models ZF) {A B Γ P Y Z : M.Domain}
    (prod : M.IsCartesianProduct I P B Γ) (letters : M.IsCartesianProduct I Y A P)
    (pair : M.IsCartesianProduct I Z A Γ) : ∃ d, Tv_drop_d I Y Z d := by
  let ρ : Env M 0 := ⟨Fin.elim0, fun _ => Y⟩
  let φ : BinarySchema 0 := { body := tv_drop_value_m (.bound 1) .newest }
  have sat p q : φ.denote ρ p q ↔ Tv_drop_value_d I p q := tv_drop_value_sat_l I ..
  obtain ⟨d, fn, graph⟩ := ZF.exists_setFunctionFromTo_of_denote hZF I φ ρ (source := Y) (target := Z) (by
    intro p hp
    obtain ⟨a, _, v, hv, ap⟩ := (letters p).mp hp
    obtain ⟨b, _, c, _, bc⟩ := (prod v).mp hv
    obtain ⟨q, ac⟩ := I.total a c
    exact ⟨q, (sat p q).mpr ⟨a, b, c, v, ap, bc, ac⟩⟩)
    (fun _ _ _ _ h k => ((sat ..).mp h).unique_l I ((sat ..).mp k)) (by
      intro p q hp h
      obtain ⟨a, b, c, v, ap, bc, ac⟩ := (sat p q).mp h
      obtain ⟨a', ha, v', hv, ap'⟩ := (letters p).mp hp
      obtain ⟨rfl, rfl⟩ := I.injective ap ap'
      obtain ⟨b', _, c', hc, bc'⟩ := (prod v).mp hv
      obtain ⟨rfl, rfl⟩ := I.injective bc bc'
      exact (pair q).mpr ⟨a, ha, c, hc, ac⟩)
  exact ⟨d, fn, fun p q => (graph p q).trans (and_congr_right fun _ => sat p q)⟩

/-- 二坐标树体的第一投影，分支和第一坐标均为所在模型的实际函数图。 -/
def Tp_projection_d (ω A Y F T x : M.Domain) : Prop := ∃ q,
  M.IsSetFunctionFromTo I q ω Y ∧ Branch_d F T q ∧ M.IsLeftFunctionProjection I x q ω A

def tp_projection_m {d} (ω A Y F T x : Term d) : Formula 1 d := .existsE (.conj
  (Formula.isFunctionFromTo kpair_convention_l .newest ω.weaken Y.weaken) (.conj
    (branch_m F.weaken T.weaken .newest)
    (Formula.isLeftFunctionProjection kpair_convention_l x.weaken .newest ω.weaken A.weaken)))

@[simp] theorem tp_projection_closed_l {d} (ω A Y F T x : Term d)
    (hw : ω.freeSupport = []) (ha : A.freeSupport = []) (hy : Y.freeSupport = [])
    (hf : F.freeSupport = []) (ht : T.freeSupport = []) (hx : x.freeSupport = []) :
    (tp_projection_m ω A Y F T x).FreeClosed := by
  simp -implicitDefEqProofs [tp_projection_m, Formula.isLeftFunctionProjection, Definitional.Formula.FreeClosed, hw, ha, hy, hf, ht, hx]

theorem tp_projection_sat_l (hE : Extensional M) {d} (ρ : Env M d) (ω A Y F T x : Term d) :
    Formula.satisfies ρ (tp_projection_m ω A Y F T x) ↔ Tp_projection_d I
      (ω.eval ρ) (A.eval ρ) (Y.eval ρ) (F.eval ρ) (T.eval ρ) (x.eval ρ) := by
  simp only [tp_projection_m, Tp_projection_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    Formula.satisfies_isFunctionFromTo_iff I hE, branch_sat_l,
    Formula.satisfies_isLeftFunctionProjection_iff I hE, Definitional.Term.eval_weaken]; rfl

theorem tp_right_l (hZF : M.Models ZF) {D A Γ Y q : M.Domain} (pair : M.IsCartesianProduct I Y A Γ)
    (fq : M.IsSetFunctionFromTo I q D Y) : ∃ g, M.IsRightFunctionProjection I g q D Γ := by
  let ρ : Env M 1 := ⟨fun _ => q, fun _ => q⟩
  let φ := BinarySchema.rightFunctionProjectionValue kpair_convention_l
  have sat i z : φ.denote ρ i z ↔ ∃ v x, M.PairMember I i v q ∧ (I).Codes v x z :=
    Formula.denote_rightFunctionProjectionValue_iff I ..
  obtain ⟨g, fg, graph⟩ := ZF.exists_setFunctionFromTo_of_denote hZF I φ ρ (source := D) (target := Γ) (by
    intro i hi
    obtain ⟨v, hv, iv⟩ := fq.2.2 i hi
    obtain ⟨x, _, z, _, c⟩ := (pair v).mp hv
    exact ⟨z, (sat i z).mpr ⟨v, x, iv, c⟩⟩) (by
      intro i _ z z' iz iz'
      obtain ⟨v, x, iv, c⟩ := (sat i z).mp iz
      obtain ⟨v', x', iv', c'⟩ := (sat i z').mp iz'
      have eq := fq.1.2 i v v' iv iv'; subst v'
      exact (I.injective c c').2) (by
        intro i z _ iz
        obtain ⟨v, x, iv, c⟩ := (sat i z).mp iz
        obtain ⟨x', _, z', hz, c'⟩ := (pair v).mp (fq.output_mem_of_pairMember iv)
        exact (I.injective c c').2.symm ▸ hz)
  exact ⟨g, fg, fun i z => (graph i z).trans ((and_congr_right fun _ => sat i z).trans
    ⟨And.right, fun h => ⟨h.elim fun _ h => h.elim fun _ h => fq.input_mem_of_pairMember h.1, h⟩⟩)⟩

section Branch
variable (hZF : M.Models ZF)
local notation "J" => kp_pair_l (ZF.modelsKP hZF)

/-- 删除无约束坐标保持投影；反向在该坐标插入常值零列。 -/
theorem tv_projection_l {ω A Γ P Y Z F G T S d x : M.Domain} (hw : M.IsOmega ω)
    (prod : M.IsCartesianProduct J P ω Γ) (letters : M.IsCartesianProduct J Y A P)
    (pair : M.IsCartesianProduct J Z A Γ) (space : Fseq_space_d J ω Y F)
    (target : Fseq_space_d J ω Z G) (drop : Tv_drop_d J Y Z d) (pull : Tr_pull_d J d F T S)
    (fx : M.IsSetFunctionFromTo J x ω A) :
    Tg_projection_d hZF ω Y F S x ↔ Tp_projection_d J ω A Z G T x := by
  constructor
  · rintro ⟨q, t, g, fq, branch, _, _, join⟩
    -- 删除中坐标得到原树分支；逐项核对第一坐标仍是原对局。
    have fq := fn0_function_l (ZF.modelsKP hZF) fq
    obtain ⟨r, fr, qr⟩ := ZF.fseq_compose_l J hZF drop.1 fq
    have first i v (iv : M.PairMember J i v r) : ∃ a z, M.PairMember J i a x ∧ (J).Codes v a z := by
      obtain ⟨p, ip, pv⟩ := (qr.2 i v).mp iv
      obtain ⟨a, b, z, u, ap, bz, az⟩ := ((drop.2 p v).mp pv).2
      obtain ⟨a', b', z', u', p', ia, _, _, bu, au, ip'⟩ := join.2 i (fq.input_mem_of_pairMember ip)
      have eq := fq.1.2 i p' p ip' ip; subst p'
      obtain ⟨rfl, rfl⟩ := (J).injective au ap
      obtain ⟨rfl, rfl⟩ := (J).injective bu bz
      exact ⟨_, _, ia, az⟩
    refine ⟨r, fr, (pull.branch_l J hZF hw drop.1 space target fq qr).mp branch, fx, fun i a => ⟨?_, ?_⟩⟩
    · intro ia
      obtain ⟨v, _, iv⟩ := fr.2.2 i (fx.input_mem_of_pairMember ia)
      obtain ⟨a', z, ia', az⟩ := first i v iv
      have eq := fx.1.2 i a' a ia' ia; subst a'
      exact ⟨v, z, iv, az⟩
    · rintro ⟨v, z, iv, az⟩
      obtain ⟨a', z', ia', az'⟩ := first i v iv
      exact (J).injective az' az |>.1 ▸ ia'
  · rintro ⟨q, fq, branch, left⟩
    -- 从二坐标分支实际分离标签列，插入常值自然数列并合成为三坐标分支。
    obtain ⟨g, right⟩ := tp_right_l J hZF pair fq
    obtain ⟨z, _, hz⟩ := hw.1.1
    obtain ⟨t, ft, _⟩ := ZF.exists_constantFunction hZF J (source := ω) hz
    obtain ⟨P', Y', r, prod', letters', fr, join⟩ := tg_join_exists_l J hZF left.1 ft right.1
    have eq := hZF.1.eq_of_same_members P' P fun v => (prod' v).trans (prod v).symm; subst P'
    have eq := hZF.1.eq_of_same_members Y' Y fun v => (letters' v).trans (letters v).symm; subst Y'
    have compatible i p v (ip : M.PairMember J i p r) (iv : M.PairMember J i v q) : Tv_drop_value_d J p v := by
      obtain ⟨a, b, c, u, p', ia, _, ic, bc, au, ip'⟩ := join.2 i (fr.input_mem_of_pairMember ip)
      have eq := fr.1.2 i p' p ip' ip; subst p'
      obtain ⟨a', _, c', _, ac⟩ := (pair v).mp (fq.output_mem_of_pairMember iv)
      have ia' := (left.2 i a').mpr ⟨v, c', iv, ac⟩
      have ic' := (right.2 i c').mpr ⟨v, a', iv, ac⟩
      have eq := left.1.1.2 i a' a ia' ia; subst a'
      have eq := right.1.1.2 i c' c ic' ic; subst c'
      exact ⟨a, b, c, u, au, bc, ac⟩
    have rq : Fseq_recode_d J d r q := by
      refine ⟨fq.1.1, fun i v => ⟨?_, ?_⟩⟩
      · intro iv
        obtain ⟨p, hp, ip⟩ := fr.2.2 i (fq.input_mem_of_pairMember iv)
        exact ⟨p, ip, (drop.2 p v).mpr ⟨hp, compatible i p v ip iv⟩⟩
      · rintro ⟨p, ip, pv⟩
        obtain ⟨v', _, iv'⟩ := fq.2.2 i (fr.input_mem_of_pairMember ip)
        have pv' := (drop.2 p v').mpr ⟨fr.output_mem_of_pairMember ip, compatible i p v' ip iv'⟩
        exact drop.1.1.2 p v' v pv' pv ▸ iv'
    exact ⟨r, t, g, fn0_of_function_l (ZF.modelsKP hZF) fr,
      (pull.branch_l J hZF hw drop.1 space target fr rq).mpr branch,
      ⟨ft.1, ft.2.1⟩, ⟨right.1.1, right.1.2.1⟩, join⟩

end Branch
end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 6.10 的连续代换与投影

在实数和标签组成的节点前加任意一项。逆向构造首个标签时，从已有分支的首项读取，
因此不额外假设标签字母表非空。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal Descriptive
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem tp_shift_projection_l {ω A Γ Y F T S z a f g : M.Domain} (hw : M.IsOmega ω)
    (hz : ∀ x, ¬ M.mem x z) (ha : M.mem a A) (pair : M.IsCartesianProduct I Y A Γ)
    (space : Fseq_space_d I ω Y F) (subT : M.MemberSubset T F) (shift : Tr_shift_d I z F T S)
    (ff : M.IsSetFunctionFromTo I f ω A) (fg : M.IsSetFunctionFromTo I g ω A) (cons : Cons_d I z a f g) :
    Tp_projection_d I ω A Y F S g ↔ Tp_projection_d I ω A Y F T f := by
  constructor
  · rintro ⟨q', fq', branch, left⟩
    obtain ⟨v, q, hv, fq, cq⟩ := tail_omega_l I hZF hw hz fq'
    refine ⟨q, fq, (shift.branch_l I hZF hw hz hv space subT cq).mp branch, ff, fun i x => ⟨?_, ?_⟩⟩
    · intro ix
      have hi := ff.input_mem_of_pairMember ix
      obtain ⟨j, sj, _⟩ := hw.1.2 i hi
      obtain ⟨p, c, jp, cp⟩ := (left.2 j x).mp ((cons.successor_l I hZF hw hz hi sj).mpr ix)
      exact ⟨p, c, (cq.successor_l I hZF hw hz hi sj).mp jp, cp⟩
    · rintro ⟨p, c, ip, cp⟩
      have hi := fq.input_mem_of_pairMember ip
      obtain ⟨j, sj, _⟩ := hw.1.2 i hi
      exact (cons.successor_l I hZF hw hz hi sj).mp
        ((left.2 j x).mpr ⟨p, c, (cq.successor_l I hZF hw hz hi sj).mpr ip, cp⟩)
  · rintro ⟨q, fq, branch, left⟩
    obtain ⟨z', hz', hzω⟩ := hw.1.1
    have eq := hZF.1.eq_of_same_members z' z fun x => iff_of_false (hz' x) (hz x); subst z'
    obtain ⟨p, hp, _⟩ := fq.2.2 z hzω
    obtain ⟨_, _, c, hc, _⟩ := (pair p).mp hp
    obtain ⟨v, cv⟩ := (I).total a c
    have hv := (pair v).mpr ⟨a, ha, c, hc, cv⟩
    obtain ⟨q', fq', cq⟩ := cons_omega_l I hZF hw hz hv fq
    refine ⟨q', fq', (shift.branch_l I hZF hw hz hv space subT cq).mpr branch, fg, fun j x => ⟨?_, ?_⟩⟩
    · intro jx
      rcases (cons.2 j x).mp jx with ⟨rfl, rfl⟩ | ⟨i, ix, sj⟩
      · exact ⟨v, c, (cq.2 _ v).mpr (Or.inl ⟨rfl, rfl⟩), cv⟩
      · obtain ⟨p, c, ip, cp⟩ := (left.2 i x).mp ix
        exact ⟨p, c, (cq.2 j p).mpr (Or.inr ⟨i, ip, sj⟩), cp⟩
    · rintro ⟨p, c', jp, cp⟩
      rcases (cq.2 j p).mp jp with ⟨rfl, rfl⟩ | ⟨i, ip, sj⟩
      · have eq := ((I).injective cv cp).1
        exact (cons.2 _ x).mpr (Or.inl ⟨rfl, eq.symm⟩)
      · exact (cons.2 j x).mpr (Or.inr ⟨i, (left.2 i x).mpr ⟨p, c', ip, cp⟩, sj⟩)

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 普通迭代树的全枝广义投影

收益只记录真实迭代树、临界点界和全部良基共尾枝的投影。
执行超幂算法所需的数字解释不属于此数学定义。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal Descriptive
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

def Tg_mem_shifted_d (ω o c γ Y F S f : M.Domain) : Prop :=
  ∃ T Q G E, It_tree_core_d hZF ω c ω T Q G E ∧ It_critical_bound_d I γ Q E ∧
    ∀ b, It_wf_branch_d hZF ω ω T Q G b →
      ∃ d N W P j Y' F' S', Smem_d I d N W ∧ It_source_d hZF ω d ∧
        It_cone_d (kp_pair_l (ZF.modelsKP hZF)) ω b Q G d N W P ∧ Rd_entry_d o j P ∧
        Rd_entry_d Y Y' j ∧ Rd_entry_d F F' j ∧ Rd_entry_d S S' j ∧
        Fseq_space_d I ω Y' F' ∧ Tree_d F' S' ∧ Tg_projection_d hZF ω Y' F' S' f

/-! `Tg_mem_shifted_d` 的全称分支字段本身不保证分支族非空。
该引理把这个逻辑事实显式化，用于约束后续 producer 必须同时输出
至少一个良基枝或等价的 iterability 证书。 -/
theorem Tg_mem_shifted_d.vacuous_l
    {ω o c γ Y F S f T Q G E : M.Domain}
    (tree : It_tree_core_d hZF ω c ω T Q G E)
    (bound : It_critical_bound_d I γ Q E)
    (no_branch : ∀ b, ¬ It_wf_branch_d hZF ω ω T Q G b) :
    Tg_mem_shifted_d hZF ω o c γ Y F S f := by
  refine ⟨T, Q, G, E, tree, bound, ?_⟩
  intro b wf
  exact (no_branch b wf).elim

/-- 5.22 的广义投影，所有活动临界点严格越过字母集合的背景秩。 -/
def Tg_gp_d (ω o c A Y F S f : M.Domain) : Prop :=
  ∃ ρ γ, Rk_d I A ρ ∧ M.mem ρ γ ∧ M.IsOrdinal γ ∧ Tg_mem_shifted_d hZF ω o c γ Y F S f

/-! 从广义投影直接抽取指定良基枝上的普通投影。

该接口只展开已经存在的广义投影证书，不添加新的树、可数性或选择参数。
后续的 5.23 分支出口可以用它把 `Tg_gp_d` 的收益条件交给普通三图投影。
-/
theorem Tg_gp_d.wf_projection_l
    {ω o c A Y F S f : M.Domain}
    (h : Tg_gp_d hZF ω o c A Y F S f) :
    ∃ ρ γ T Q G E, Rk_d I A ρ ∧ M.mem ρ γ ∧ M.IsOrdinal γ ∧
      It_tree_core_d hZF ω c ω T Q G E ∧ It_critical_bound_d I γ Q E ∧
      ∀ b, It_wf_branch_d hZF ω ω T Q G b →
        ∃ d N W P j Y' F' S', Smem_d I d N W ∧ It_source_d hZF ω d ∧
          It_cone_d (kp_pair_l (ZF.modelsKP hZF)) ω b Q G d N W P ∧ Rd_entry_d o j P ∧
          Rd_entry_d Y Y' j ∧ Rd_entry_d F F' j ∧ Rd_entry_d S S' j ∧
          Fseq_space_d I ω Y' F' ∧ Tree_d F' S' ∧
          Tg_projection_d hZF ω Y' F' S' f := by
  rcases h with ⟨ρ, γ, hρ, hργ, hγ, shifted⟩
  rcases shifted with ⟨T, Q, G, E, tree, bound, branches⟩
  exact ⟨ρ, γ, T, Q, G, E, hρ, hργ, hγ, tree, bound, branches⟩

/-! 当上游给出同一 `Tg_gp_d` 见证上的一条良基枝时，直接读取该枝的
普通投影。这个接口把 5.23 的剩余义务精确隔离为枝存在性，不重复展开
广义投影或引入 image 字母表等额外条件。 -/
theorem Tg_gp_d.wf_projection_of_branch_l
    {ω o c A Y F S f : M.Domain}
    (h : Tg_gp_d hZF ω o c A Y F S f)
    (branch : ∀ ρ γ T Q G E,
      Rk_d I A ρ → M.mem ρ γ → M.IsOrdinal γ →
      It_tree_core_d hZF ω c ω T Q G E → It_critical_bound_d I γ Q E →
      ∃ b, It_wf_branch_d hZF ω ω T Q G b) :
    ∃ ρ γ T Q G E b d N W P j Y' F' S',
      Rk_d I A ρ ∧ M.mem ρ γ ∧ M.IsOrdinal γ ∧
      It_tree_core_d hZF ω c ω T Q G E ∧ It_critical_bound_d I γ Q E ∧
      It_wf_branch_d hZF ω ω T Q G b ∧
      Smem_d I d N W ∧ It_source_d hZF ω d ∧ It_cone_d (kp_pair_l (ZF.modelsKP hZF)) ω b Q G d N W P ∧
      Rd_entry_d o j P ∧ Rd_entry_d Y Y' j ∧ Rd_entry_d F F' j ∧ Rd_entry_d S S' j ∧
      Fseq_space_d I ω Y' F' ∧ Tree_d F' S' ∧ Tg_projection_d hZF ω Y' F' S' f := by
  rcases h with ⟨ρ, γ, hρ, hργ, hγ, T, Q, G, E, tree, bound, branches⟩
  obtain ⟨b, hb⟩ := branch ρ γ T Q G E hρ hργ hγ tree bound
  obtain ⟨d, N, W, P, j, Y', F', S', hdata⟩ := branches b hb
  exact ⟨ρ, γ, T, Q, G, E, b, d, N, W, P, j, Y', F', S',
    hρ, hργ, hγ, tree, bound, hb, hdata⟩


/-! 将已有良基分支选择器接入 shifted payoff。这里的选择函数只在
具体给定的迭代图、修剪条件和相容良基实现下使用，逐点返回的枝再由
原收益证书读取对应普通投影。 -/
theorem Tg_mem_shifted_d.choice_l
    {ω o Y F S f T Q G K Y₀ V P : M.Domain}
    (diagram : It_diagram_d (kp_pair_l (ZF.modelsKP hZF)) ω ω T Q G)
    (branches : ∀ b, It_wf_branch_d hZF ω ω T Q G b →
      ∃ d N W P' j Y' F' S', Smem_d I d N W ∧ It_source_d hZF ω d ∧
        It_cone_d (kp_pair_l (ZF.modelsKP hZF)) ω b Q G d N W P' ∧ Rd_entry_d o j P' ∧
        Rd_entry_d Y Y' j ∧ Rd_entry_d F F' j ∧ Rd_entry_d S S' j ∧
        Fseq_space_d I ω Y' F' ∧ Tree_d F' S' ∧
        Tg_projection_d hZF ω Y' F' S' f)
    (hω : M.IsOmega ω)
    (cf : M.IsCofinalOrdinalSequence I K ω ω)
    (pruned : ∀ i k, M.mem i ω → M.mem k ω →
      ∃ j, M.mem j ω ∧ Rd_entry_d i j T ∧ (k = j ∨ M.mem k j))
    (realizer : It_realizer_d hZF ω Q G Y₀ V P)
    (wf : Wf_rel_d Y₀ V) :
    ∃ choose : M.Domain → M.Domain,
      ∀ a, M.mem a ω →
        It_wf_branch_d hZF ω ω T Q G (choose a) ∧
        ∃ d N W P' j Y' F' S', Smem_d I d N W ∧ It_source_d hZF ω d ∧
          It_cone_d (kp_pair_l (ZF.modelsKP hZF)) ω (choose a) Q G d N W P' ∧ Rd_entry_d o j P' ∧
          Rd_entry_d Y Y' j ∧ Rd_entry_d F F' j ∧ Rd_entry_d S S' j ∧
          Fseq_space_d I ω Y' F' ∧ Tree_d F' S' ∧
          Tg_projection_d hZF ω Y' F' S' f := by
  obtain ⟨choose, choose_spec⟩ := it_pruned_wf_branch_choice_l hZF hω diagram cf
    pruned realizer wf
  refine ⟨choose, ?_⟩
  intro a ha
  obtain ⟨branch, _⟩ := choose_spec a ha
  exact ⟨branch, branches (choose a) branch⟩

end YesMetaZFC.SetTheory.LargeCardinal
