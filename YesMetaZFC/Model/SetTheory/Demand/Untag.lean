import YesMetaZFC.Model.SetTheory.Game.NodeEmbedding
import YesMetaZFC.SetTheory.TaggedUnionConstruction
import YesMetaZFC.SetTheory.Card.FiniteSequenceRecode
import YesMetaZFC.SetTheory.Card.FiniteSequenceEnd
import YesMetaZFC.SetTheory.Descriptive.Tree.HistoryTree

/-! # 辅助字母及有限图的实际标签编码

三元组解码保留原实数坐标；两张辅助图分别逐项加标签。
全部图由函数替换构造，不使用宿主选择。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel Descriptive
universe u
variable {M : Structure.{u}}

def Td_tag_d (e o x y : M.Domain) : Prop :=
  ∃ r a b t c d u, KPair_d M x r t ∧ KPair_d M t c d ∧
    KPair_d M c e a ∧ KPair_d M d o b ∧ KPair_d M y r u ∧ KPair_d M u a b

def td_tag_m {d} (e o x y : Term d) : Formula 1 d := set[d] ⟪
  ∃ r a b t c d u, ⌜kpair0_m⌝ₚ(⌜x⌝ₛ,r,t) ∧ ⌜kpair0_m⌝ₚ(t,c,d) ∧
    ⌜kpair0_m⌝ₚ(c,⌜e⌝ₛ,a) ∧ ⌜kpair0_m⌝ₚ(d,⌜o⌝ₛ,b) ∧
    ⌜kpair0_m⌝ₚ(⌜y⌝ₛ,r,u) ∧ ⌜kpair0_m⌝ₚ(u,a,b)⟫
derive_free_closed td_tag_m

theorem td_tag_sat_l (hE : Extensional M) {d} (ρ : Env M d) (e o x y : Term d) :
    Formula.satisfies ρ (td_tag_m e o x y) ↔ Td_tag_d (e.eval ρ) (o.eval ρ) (x.eval ρ) (y.eval ρ) := by
  simp only [td_tag_m,Td_tag_d,Formula.satisfies_exists_iff,Formula.satisfies_conj_iff,
    kpair0_sat_l hE,Definitional.Term.eval_weaken]
  rfl

theorem td_tag_unique_l (hE : Extensional M) {e o x y x' y' : M.Domain}
    (ha : Td_tag_d e o x y) (hb : Td_tag_d e o x' y') : (x = x' ↔ y = y') := by
  obtain ⟨r,a,b,t,c,d,u,xt,td,ca,db,yu,ub⟩ := ha
  obtain ⟨r',a',b',t',c',d',u',xt',td',ca',db',yu',ub'⟩ := hb
  constructor
  · intro eq
    subst x'
    obtain ⟨er,et⟩ := kpair_injective_l M xt xt'
    subst r' t'
    obtain ⟨ec,ed⟩ := kpair_injective_l M td td'
    subst c' d'
    have ea := (kpair_injective_l M ca ca').2
    have eb := (kpair_injective_l M db db').2
    subst a' b'
    have eu := kpair_unique_l M hE ub ub'
    subst u'
    exact kpair_unique_l M hE yu yu'
  · intro eq
    subst y'
    obtain ⟨er,eu⟩ := kpair_injective_l M yu yu'
    subst r' u'
    obtain ⟨ea,eb⟩ := kpair_injective_l M ub ub'
    subst a' b'
    have ec := kpair_unique_l M hE ca ca'
    have ed := kpair_unique_l M hE db db'
    subst c' d'
    have et := kpair_unique_l M hE td td'
    subst t'
    exact kpair_unique_l M hE xt xt'


def Tag_graph_d (e a c : M.Domain) : Prop :=
  (∀ p, M.mem p c → ∃ i z, KPair_d M p i z) ∧
    ∀ i z, Rd_entry_d i z c ↔ ∃ x, Rd_entry_d i x a ∧ KPair_d M z e x

def tag_graph_m {d} (e a c : Term d) : Formula 1 d := set[d] ⟪
  (∀ p ∈ ⌜c⌝ₛ, ∃ i z, ⌜kpair0_m⌝ₚ(p,i,z)) ∧
    (∀ i z, ⌜rd_entry0_m⌝ₚ(i,z,⌜c⌝ₛ) ↔ ∃ x, ⌜rd_entry0_m⌝ₚ(i,x,⌜a⌝ₛ) ∧ ⌜kpair0_m⌝ₚ(z,⌜e⌝ₛ,x))⟫
derive_free_closed tag_graph_m

theorem tag_graph_sat_l (hE : Extensional M)
    {d} (ρ : Env M d) (e a c : Term d) : Formula.satisfies ρ (tag_graph_m e a c) ↔
      Tag_graph_d (e.eval ρ) (a.eval ρ) (c.eval ρ) := by
  simp only [tag_graph_m,Tag_graph_d,Formula.satisfies_conj_iff,Formula.satisfies_forall_iff,Formula.satisfies_forallMem_iff,
    Formula.satisfies_iff_iff,Formula.satisfies_exists_iff,rd_entry0_sat_l hE,kpair0_sat_l hE,
    Definitional.Term.eval_weaken]
  rfl

variable (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)
include hZF

/-- 标签行与原字母集之间的实际集合双射。 -/
theorem tag_map_l {e U C : M.Domain}
    (row : ∀ z, M.mem z C ↔ ∃ x, M.mem x U ∧ KPair_d M z e x) :
    ∃ f, M.IsSetBijectionFromTo I f U C ∧
      ∀ x z, Rd_entry_d x z f ↔ M.mem x U ∧ KPair_d M z e x := by
  let ρ : Env M 1 := ⟨fun _ => e,fun _ => e⟩
  let φ : BinarySchema 1 := { body := kpair0_m .newest (.bound 2) (.bound 1) }
  have sat x z : φ.denote ρ x z ↔ KPair_d M z e x := kpair0_sat_l hZF.1 ..
  obtain ⟨f,fn,read⟩ := ZF.exists_setFunctionFromTo_of_denote hZF I φ ρ (source := U) (target := C)
    (fun x _ => ((I).total e x).imp fun z hz => (sat x z).mpr hz)
    (fun x _ z t hz ht => (I).unique ((sat x z).mp hz) ((sat x t).mp ht))
    (fun x z hx hz => (row z).mpr ⟨x,hx,(sat x z).mp hz⟩)
  have edges x z := (read x z).trans (and_congr_right fun _ => sat x z)
  exact ⟨f,⟨⟨fn,fun x y z xz yz => ((I).injective ((edges x z).mp xz).2 ((edges y z).mp yz).2).2⟩,
    fun z hz => ((row z).mp hz).imp fun x hx => ⟨hx.1,(edges x z).mpr hx⟩⟩,edges⟩

/-- 给定实际标签行，逐项加标签仍为同域函数。 -/
theorem tag_graph_l {e U C n a : M.Domain}
    (row : ∀ z, M.mem z C ↔ ∃ x, M.mem x U ∧ KPair_d M z e x) (fa : Fn0_d n U a) :
    ∃ c, Fn0_d n C c ∧ Tag_graph_d e a c := by
  let ρ : Env M 2 := ⟨fun i => [a,e].get i,fun _ => a⟩
  let φ : BinarySchema 2 := { body := set[4] ⟪∃ x,
    ⌜rd_entry0_m⌝ₚ(⌜(.bound 1 : Term 4)⌝ₛ,x,⌜(.bound 2 : Term 4)⌝ₛ) ∧
    ⌜kpair0_m⌝ₚ(⌜(.newest : Term 4)⌝ₛ,⌜(.bound 3 : Term 4)⌝ₛ,x)⟫ }
  have sat i z : φ.denote ρ i z ↔ ∃ x, Rd_entry_d i x a ∧ KPair_d M z e x := by
    simp only [BinarySchema.denote,φ,Formula.satisfies_exists_iff,Formula.satisfies_conj_iff,
      rd_entry0_sat_l hZF.1,kpair0_sat_l hZF.1,Definitional.Term.eval_weaken]
    rfl
  have af := fn0_function_l (ZF.modelsKP hZF) fa
  obtain ⟨c,fc,read⟩ := ZF.exists_setFunctionFromTo_of_denote hZF I φ ρ (source := n) (target := C)
    (fun i hi => by
      obtain ⟨x,_,ix⟩ := fa.2.1 i hi
      obtain ⟨z,pair⟩ := (I).total e x
      exact ⟨z,(sat i z).mpr ⟨x,ix,pair⟩⟩)
    (by
      intro i _ z t hz ht
      obtain ⟨x,ix,pair⟩ := (sat i z).mp hz
      obtain ⟨y,iy,pair'⟩ := (sat i t).mp ht
      exact (I).unique pair (af.1.2 i y x iy ix ▸ pair'))
    (by
      intro i z _ hz
      obtain ⟨x,ix,pair⟩ := (sat i z).mp hz
      exact (row z).mpr ⟨x,(fa.bound_l ix).2,pair⟩)
  exact ⟨c,fn0_of_function_l (ZF.modelsKP hZF) fc,fc.1.1,fun i z => (read i z).trans
    ⟨fun h => (sat i z).mp h.2,fun h => h.elim fun x hx => ⟨(fa.bound_l hx.1).1,(sat i z).mpr ⟨x,hx⟩⟩⟩⟩

theorem Tag_graph_d.function_l {e U C n a c : M.Domain}
    (row : ∀ z, M.mem z C ↔ ∃ x, M.mem x U ∧ KPair_d M z e x)
    (fa : Fn0_d n U a) (tag : Tag_graph_d e a c) : Fn0_d n C c := by
  obtain ⟨c',fc',tag'⟩ := tag_graph_l hZF row fa
  have eq : c = c' := (show M.IsSetRelation I c from tag.1).eq_of_pairMember_iff hZF.1 tag'.1
    (fun i z => (tag.2 i z).trans (tag'.2 i z).symm)
  exact eq.symm ▸ fc'

end YesMetaZFC.SetTheory.Internal

/-! ## 逐项标签编码与实际末项追加交换 -/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel Descriptive
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Tag_graph_d.append_l {ω n U C e a c a' c' x z : M.Domain}
    (tag : Tag_graph_d e a c) (fa : Fn0_d n U a) (fc : Fn0_d n C c)
    (ea : Fseq_end_d I ω a' a x) (ec : Fseq_end_d I ω c' c z) (pair : KPair_d M z e x) :
    Tag_graph_d e a' c' := by
  have ra := ea.entries_l I hZF.1 (fn0_function_l (ZF.modelsKP hZF) fa).2.1
  have rc := ec.entries_l I hZF.1 (fn0_function_l (ZF.modelsKP hZF) fc).2.1
  refine ⟨ec.elim fun _ h => h.elim fun _ d => d.source.2.2.1.1,fun i y => ⟨?_,?_⟩⟩
  · intro iy
    rcases (rc i y).mp iy with iy | ⟨eqi,eqy⟩
    · obtain ⟨t,it,yt⟩ := (tag.2 i y).mp iy
      exact ⟨t,(ra i t).mpr (Or.inl it),yt⟩
    · exact ⟨x,(ra i x).mpr (Or.inr ⟨eqi,rfl⟩),eqy.symm ▸ pair⟩
  · rintro ⟨t,it,yt⟩
    rcases (ra i t).mp it with it | ⟨eqi,eqt⟩
    · exact (rc i y).mpr (Or.inl ((tag.2 i y).mpr ⟨t,it,yt⟩))
    · exact (rc i y).mpr (Or.inr ⟨eqi,(I).unique (eqt ▸ yt) pair⟩)

end YesMetaZFC.SetTheory.Internal

/-! ## 标签编码精确保留完整三坐标节点

原实数图保持不动，两张辅助图逐项加标签。比较同域合成图的每个坐标，
得到真实解码复合关系，再由逆像树的成员方程双向读取节点。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel Descriptive
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem td_tag_join_l {n A U V Y Y' e o f h a b c d q q' : M.Domain}
    (ff : M.IsSetFunctionFromTo I f Y' Y)
    (decode : ∀ z y, Rd_entry_d z y f ↔ M.mem z Y' ∧ Td_tag_d e o z y)
    (fh : Fn0_d n A h) (fa : Fn0_d n U a) (fb : Fn0_d n V b)
    (fq' : Fn0_d n Y' q')
    (left : Tag_graph_d e a c) (right : Tag_graph_d o b d)
    (old : Tg_join_d I n h a b q) (tagged : Tg_join_d I n h c d q') : Fseq_recode_d I f q' q := by
  have matchAt i (hi : M.mem i n) : ∃ z y, Rd_entry_d i z q' ∧ Rd_entry_d i y q ∧ Rd_entry_d z y f := by
    obtain ⟨x,u,v,t,y,ix,iu,iv,tv,yt,iy⟩ := old.2 i hi
    obtain ⟨x',u',v',t',z,ix',iu',iv',tv',zt',iz⟩ := tagged.2 i hi
    have eq := (fn0_function_l (ZF.modelsKP hZF) fh).1.2 i x' x ix' ix
    subst x'
    obtain ⟨u₀,iu₀,pu⟩ := (left.2 i u').mp iu'
    obtain ⟨v₀,iv₀,pv⟩ := (right.2 i v').mp iv'
    have eq := (fn0_function_l (ZF.modelsKP hZF) fa).1.2 i u₀ u iu₀ iu
    subst u₀
    have eq := (fn0_function_l (ZF.modelsKP hZF) fb).1.2 i v₀ v iv₀ iv
    subst v₀
    exact ⟨z,y,iz,iy,(decode z y).mpr ⟨(fq'.bound_l iz).2,x,u,v,t',u',v',t,zt',tv',pu,pv,yt,tv⟩⟩
  refine ⟨old.1.1.1,fun i y => ⟨?_,?_⟩⟩
  · intro iy
    obtain ⟨z,y',iz,iy',zy⟩ := matchAt i ((old.1.2 i).mpr ⟨y,iy⟩)
    exact ⟨z,iz,old.1.1.2 i y' y iy' iy ▸ zy⟩
  · rintro ⟨z,iz,zy⟩
    obtain ⟨z',y',iz',iy',zy'⟩ := matchAt i (fq'.bound_l iz).1
    have eq := tagged.1.1.2 i z' z iz' iz
    exact ff.1.2 z y' y (eq ▸ zy') zy ▸ iy'

theorem td_tag_node_l {ω n A U V U' V' Y P' Y' F' S T e o f h a b c d : M.Domain}
    (ff : M.IsSetFunctionFromTo I f Y' Y)
    (decode : ∀ z y, Rd_entry_d z y f ↔ M.mem z Y' ∧ Td_tag_d e o z y)
    (space' : Fseq_space_d I ω Y' F') (pull : Tr_pull_d I f F' S T)
    (pair' : M.IsCartesianProduct I P' U' V') (triple' : M.IsCartesianProduct I Y' A P')
    (hn : M.mem n ω) (fh : Fn0_d n A h) (fa : Fn0_d n U a) (fb : Fn0_d n V b)
    (fc : Fn0_d n U' c) (fd : Fn0_d n V' d)
    (left : Tag_graph_d e a c) (right : Tag_graph_d o b d) :
    Tg_node_d I n S h a b ↔ Tg_node_d I n T h c d := by
  have graph {X z} (fz : Fn0_d n X z) : Tg_graph_d I n z :=
    ⟨(fn0_function_l (ZF.modelsKP hZF) fz).1,(fn0_function_l (ZF.modelsKP hZF) fz).2.1⟩
  obtain ⟨_,_,q,_,_,_,old⟩ := tg_join_exists_l I hZF (fn0_function_l (ZF.modelsKP hZF) fh)
    (fn0_function_l (ZF.modelsKP hZF) fa) (fn0_function_l (ZF.modelsKP hZF) fb)
  obtain ⟨_,_,q',_,_,_,tagged⟩ := tg_join_exists_l I hZF (fn0_function_l (ZF.modelsKP hZF) fh)
    (fn0_function_l (ZF.modelsKP hZF) fc) (fn0_function_l (ZF.modelsKP hZF) fd)
  have fq' := tagged.typed_l hZF fh fc fd pair' triple'
  have recode := td_tag_join_l hZF ff decode fh fa fb fq' left right old tagged
  have unique {r r'} (l : Tg_join_d I n h a b r) (rj : Tg_join_d I n h a b r') : r = r' := by
    apply l.1.1.1.eq_of_pairMember_iff hZF.1 rj.1.1.1
    intro i z
    have same i (hi : M.mem i n) : ∃ z, Rd_entry_d i z r ∧ Rd_entry_d i z r' := by
      obtain ⟨x,u,v,t,z,ix,iu,iv,uv,zt,iz⟩ := l.2 i hi
      obtain ⟨x',u',v',t',z',ix',iu',iv',uv',zt',iz'⟩ := rj.2 i hi
      have ex := (graph fh).1.2 i x' x ix' ix
      have eu := (graph fa).1.2 i u' u iu' iu
      have ev := (graph fb).1.2 i v' v iv' iv
      subst x' u' v'
      have et := (I).unique uv' uv
      have ez := (I).unique (et ▸ zt') zt
      exact ⟨z,iz,ez ▸ iz'⟩
    exact ⟨fun iz => (same i ((l.1.2 i).mpr ⟨z,iz⟩)).elim fun y hy => l.1.1.2 i y z hy.1 iz ▸ hy.2,
      fun iz => (same i ((rj.1.2 i).mpr ⟨z,iz⟩)).elim fun y hy => rj.1.1.2 i y z hy.2 iz ▸ hy.1⟩
  constructor
  · rintro ⟨_,_,_,r,hr,joined⟩
    have eq := unique joined old
    exact ⟨graph fh,graph fc,graph fd,q',(pull q').mpr
      ⟨(space' q').mpr ⟨n,hn,fn0_function_l (ZF.modelsKP hZF) fq'⟩,q,eq ▸ hr,recode⟩,tagged⟩
  · rintro ⟨_,_,_,r,hr,joined⟩
    obtain ⟨_,t,ht,rt⟩ := (pull r).mp hr
    have fr := joined.typed_l hZF fh fc fd pair' triple'
    have rq := td_tag_join_l hZF ff decode fh fa fb fr left right old joined
    have eq := rt.unique_l I hZF.1 rq
    exact ⟨graph fh,graph fa,graph fb,q,eq ▸ ht,old⟩

end YesMetaZFC.SetTheory.Internal

/-! ## 同一辅助树的实际标签重编码数据

记录两组标签行、三字母积、有限空间及唯一解码图。节点与无限分支对应
从这些实际对象推出，不另设节点运输或策略运输前提。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel Descriptive
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

structure Td_retag_d (ω A S U V e o T U' V' : M.Domain) where
  P : M.Domain
  Y : M.Domain
  F : M.Domain
  P' : M.Domain
  Y' : M.Domain
  F' : M.Domain
  f : M.Domain
  pair : M.IsCartesianProduct I P U V
  triple : M.IsCartesianProduct I Y A P
  pair' : M.IsCartesianProduct I P' U' V'
  triple' : M.IsCartesianProduct I Y' A P'
  space : Fseq_space_d I ω Y F
  space' : Fseq_space_d I ω Y' F'
  source : Tree_d F S
  map : M.IsSetBijectionFromTo I f Y' Y
  decode : ∀ x y, Rd_entry_d x y f ↔ M.mem x Y' ∧ Td_tag_d e o x y
  pull : Tr_pull_d I f F' S T
  left : ∀ z, M.mem z U' ↔ ∃ a, M.mem a U ∧ KPair_d M z e a
  right : ∀ z, M.mem z V' ↔ ∃ b, M.mem b V ∧ KPair_d M z o b

theorem Td_retag_d.tree_l {ω A S U V e o T U' V' : M.Domain}
    (r : Td_retag_d hZF ω A S U V e o T U' V') : Tree_d r.F' T :=
  r.pull.tree_l I hZF r.map.1.1 r.space' r.space r.source

theorem Td_retag_d.node_l {ω A S U V e o T U' V' : M.Domain}
    (r : Td_retag_d hZF ω A S U V e o T U' V')
    {n h a b c d} (hn : M.mem n ω) (fh : Fn0_d n A h) (fa : Fn0_d n U a) (fb : Fn0_d n V b)
    (fc : Fn0_d n U' c) (fd : Fn0_d n V' d) (left : Tag_graph_d e a c) (right : Tag_graph_d o b d) :
    Tg_node_d I n S h a b ↔ Tg_node_d I n T h c d :=
  td_tag_node_l hZF r.map.1.1 r.decode r.space' r.pull r.pair' r.triple' hn fh fa fb fc fd left right

theorem Td_retag_d.branch_l {ω A S U V e o T U' V' : M.Domain}
    (r : Td_retag_d hZF ω A S U V e o T U' V') (hw : M.IsOmega ω)
    {a b} (fa : M.IsSetFunctionFromTo I a ω r.Y') (ab : Fseq_recode_d I r.f a b) :
    Branch_d r.F' T a ↔ Branch_d r.F S b :=
  r.pull.branch_l I hZF hw r.map.1.1 r.space' r.space fa ab

end YesMetaZFC.SetTheory.Internal

/-! ## 实际标签图的去标签与满射保持

标签行的双射取逆，再与原图复合。原第一图的满射因而解码为原字母域的
满射，且每个轮号的字母对应仍由同一个标签图方程记录。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel Descriptive
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem tag_graph_decode_l {e U C n c : M.Domain}
    (row : ∀ z, M.mem z C ↔ ∃ x, M.mem x U ∧ KPair_d M z e x) (fc : Fn0_d n C c) :
    ∃ a, Fn0_d n U a ∧ Tag_graph_d e a c ∧
      (M.IsSetSurjectiveOnto I c n C → M.IsSetSurjectiveOnto I a n U) := by
  obtain ⟨f,bij,read⟩ := tag_map_l hZF row
  obtain ⟨g,back,inverse⟩ := ZF.exists_inverseBijectionWithPairs hZF I bij
  obtain ⟨a,fa,comp⟩ := ZF.fseq_compose_l I hZF back.1.1 (fn0_function_l (ZF.modelsKP hZF) fc)
  have graph : Tag_graph_d e a c := by
    refine ⟨(fn0_function_l (ZF.modelsKP hZF) fc).1.1,fun i z => ⟨?_,?_⟩⟩
    · intro iz
      obtain ⟨x,hx,pair⟩ := (row z).mp (fc.bound_l iz).2
      exact ⟨x,(comp.2 i x).mpr ⟨z,iz,(inverse z x).mpr ((read x z).mpr ⟨hx,pair⟩)⟩,pair⟩
    · rintro ⟨x,ix,pair⟩
      obtain ⟨z',iz',zx⟩ := (comp.2 i x).mp ix
      have eq := (I).unique ((read x z').mp ((inverse z' x).mp zx)).2 pair
      exact eq ▸ iz'
  refine ⟨a,fn0_of_function_l (ZF.modelsKP hZF) fa,graph,?_⟩
  intro onto x hx
  obtain ⟨z,hz,xz⟩ := bij.1.1.2.2 x hx
  obtain ⟨i,hi,iz⟩ := onto z hz
  exact ⟨i,hi,(comp.2 i x).mpr ⟨z,iz,(inverse z x).mpr xz⟩⟩

end YesMetaZFC.SetTheory.Internal
