import YesMetaZFC.SetTheory.LargeCardinal.Iteration.CopyCollapseCommon
import YesMetaZFC.SetTheory.LargeCardinal.Iteration.CopyRow
import YesMetaZFC.SetTheory.LargeCardinal.Extender.CopySuccessor
import YesMetaZFC.SetTheory.LargeCardinal.Cardinals.RelativeRankSegment
import YesMetaZFC.SetTheory.LargeCardinal.Iteration.CopyFixedBound
import YesMetaZFC.SetTheory.LargeCardinal.Iteration.ActivityRead
import YesMetaZFC.SetTheory.LargeCardinal.Extender.StrengthAgreement
import YesMetaZFC.SetTheory.LargeCardinal.Extender.RawCoherence
import YesMetaZFC.Model.SetTheory.Source.OmegaClosed
import YesMetaZFC.Model.SetTheory.Source.RankSizeInitial
import YesMetaZFC.Model.SetTheory.Source.RankClosure
import YesMetaZFC.SetTheory.LargeCardinal.Extender.OmegaClosed
import YesMetaZFC.SetTheory.LargeCardinal.Iteration.CopyQuality
import YesMetaZFC.SetTheory.LargeCardinal.Extender.SetCopy
import YesMetaZFC.SetTheory.LargeCardinal.Extender.SuccessorApplication
import YesMetaZFC.SetTheory.LargeCardinal.Iteration.CopyHistory
import YesMetaZFC.SetTheory.InnerModel.Rudimentary.Tuple
import YesMetaZFC.SetTheory.RelationChain
import YesMetaZFC.SetTheory.TransitiveClosure
import YesMetaZFC.SetTheory.LargeCardinal.Iteration.CopyExtend
import YesMetaZFC.Model.SetTheory.ClassChoice
import YesMetaZFC.SetTheory.LargeCardinal.Iteration.CopyNice

/-! # 固定复制因子在实际共同秩层上的交换

共同层自身携带的支撑枚举，把有限幂子集交换提升为整层逐点交换。
两张复制图随后搬运同一秩历史，直接接到原关系后继的完整共同层。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

/-- 只读取已经产生的共同层和同一因子，不另选原后继或工作秩段。 -/
theorem Ic_row_d.collapse_agree_l
    {ω L L' K K' c Y S B σ u U β e P T d N R g a C Q q k W : M.Domain}
    (row : Ic_row_d hZF ω c Y B σ u U β)
    (owner : Ep_source_d I ω L K Y S) (norm : Ep_source_d I ω L K' P T)
    (my : Smem_d I c Y S) (mp : Smem_d I e P T) (mn : Smdl_d I d N R)
    (collapse : Smap_d I ω d e N P g) (bij : M.IsSetBijectionFromTo I g N P)
    (mc : Smem_d I a C Q) (ct : M.TransitiveSet C)
    (copy : Smap_d I ω e a P C q) (conjugate : It_comp_d g q k)
    (hW : M.mem W Y) (rank : Vr_d Y L W) (level : Er_level_d P L W)
    (limit : M.IsLimitOrdinal L) (exactness : Es_strength_d Y L P)
    (endσ : Rd_entry_d L L' σ) (endq : Rd_entry_d L L' q)
    (fixed : ∀ α α', M.mem α L → Rd_entry_d α α' σ → Rd_entry_d α α' q)
    (maps : Ea_maps_d ω L P q σ) :
    ∃ l V t, Rd_entry_d l L g ∧ Rd_entry_d V W g ∧
      (∀ x E, Rd_entry_d x E t ↔ M.mem x W ∧ Rd_entry_d E x g) ∧
      Ic_agree_d I Y S B σ N R C k L l L' W V W t := by
  obtain ⟨S₀,Sb,Su,b,Kb,Ku,raw,mb,_,small,_,_,_,_,map⟩ := row
  have eq := (smdl_unique_l I raw my.1).2
  subst S₀
  obtain ⟨J,f,_,hf,iso⟩ := level.code
  have same := maps.transitive_l hZF norm owner ct small.transitive mp mc copy my mb map endq endσ fixed
    iso.transitive hf (iso.bijection_l (ZF.modelsKP hZF))
  obtain ⟨W',hWC,hWq⟩ := copy.1.1.2.2 W level.member
  have hWσ := same.2.2.1 W' hWq
  have rankB := (map.hierarchy_l hZF owner.omega owner.transitive small.transitive my mb endσ hWσ).mp rank
  have rankC := (copy.hierarchy_l hZF owner.omega norm.transitive ct mp mc endq hWq).mp level.hierarchy
  have limit' := (map.limit_l hZF owner.omega owner.transitive small.transitive my mb endσ).mp limit
  exact ic_collapse_agree_l hZF owner.omega my owner.transitive mn mp norm.transitive collapse bij
    owner.cardinal_mem norm.cardinal_mem hW level.member rank level.hierarchy limit exactness
    small.transitive ct limit' (map.1.1.output_mem_of_pairMember hWσ) hWC rankB rankC hWσ hWq endσ endq
    conjugate (fun x x' hx hxx => (same.2.2.2 x x' hx).mpr hxx)

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 固定活动步的有限幂复制交换

真实历史的共同图在已规范化的前缀上就是恒等图。共同端点的全局缺失子集
排除临界点达到该端点；因此施加条件涉及的全部有限幂子集都落入共同秩段，
两条原复制图在这些对象上的值由历史的同一交换证书确定。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

/-- 规范化只读取已有前驱方程，保留历史中给定的共同图。 -/
private theorem ic_common_mem_graph_l {X R Y S L l U V D t c d : M.Domain}
    (h : Ic_common_d I X R Y S L l U V D t)
    (mx : Smem_d I c X R) (my : Smem_d I d Y S)
    (xt : M.TransitiveSet X) (yt : M.TransitiveSet Y) :
    ∀ x y, Rd_entry_d x y t ↔ M.mem x U ∧ y = x := by
  have rank := (rr_rank_mem_l I (ZF.modelsKP hZF) mx xt h.left_rank.1 h.left_rank.2.1).mp h.left_rank
  have dc x : M.mem x D ↔ M.mem x U := (h.carrier x).trans
    ⟨fun hx => ((mx.2 x U).mp hx.2).2.2,fun hx =>
      ⟨xt U h.left_rank.2.1 x hx,(mx.2 x U).mpr ⟨xt U h.left_rank.2.1 x hx,h.left_rank.2.1,hx⟩⟩⟩
  have eq := hZF.1.eq_of_same_members D U dc
  subst D
  have layer : Rr_layer_d I U Y S V t := by
    refine ⟨rank.transitive_l xt h.left_rank.2.1,h.right_rank.2.1,h.injection,h.image,?_⟩
    intro x y hxy z
    apply (h.pred x y hxy z).trans
    constructor
    · rintro ⟨a,ha,az⟩
      exact ⟨a,((mx.2 a x).mp ha).2.2,az⟩
    · rintro ⟨a,ha,az⟩
      have hx := xt U h.left_rank.2.1 x (h.injection.1.input_mem_of_pairMember hxy)
      exact ⟨a,(mx.2 a x).mpr ⟨xt x hx a ha,hx,ha⟩,az⟩
  exact (layer.mem_l (ZF.modelsKP hZF) yt my).2

/-- 全局缺失子集迫使临界点严格低于共同端点，随后共同点方程给出全部复制交换。 -/
theorem Ic_agree_d.mem_read_l
    {ω κ K K' X R A π Y S B σ L l φ U V D t c d a RA : M.Domain}
    (h : Ic_agree_d I X R A π Y S B σ L l φ U V D t)
    (source : Ep_source_d I ω κ K X R) (target : Ep_source_d I ω κ K' Y S)
    (mx : Smem_d I c X R) (my : Smem_d I d Y S) (ma : Smem_d I a A RA)
    (copy : Smap_d I ω c a X A π) (ordinal : M.IsOrdinal κ)
    (agree : Ea_agree_d ω κ X Y) : M.mem κ L ∧ Ea_maps_d ω κ X π σ := by
  have rank := (rr_rank_mem_l I (ZF.modelsKP hZF) mx source.transitive
    h.common.left_rank.1 h.common.left_rank.2.1).mp h.common.left_rank
  have fixed := ic_common_mem_graph_l hZF h.common mx my source.transitive target.transitive
  obtain ⟨x,hx,sub,missing⟩ := h.common.exactness.2.2
  have sub' : M.MemberSubset x L := fun v hv => ((mx.2 v L).mp
    (sub v (source.transitive x hx v hv)
      ((mx.2 v x).mpr ⟨source.transitive x hx v hv,hx,hv⟩))).2.2
  have absent : ¬ M.mem x Y := by
    intro hy
    apply missing x
    refine ⟨hx,hy,fun v => ⟨?_,?_⟩⟩
    · intro hv
      have vx := ((my.2 v x).mp hv).2.2
      have vu := rank.ordinal_subset_l hZF source.transitive h.common.left_rank.2.1 v (sub' v vx)
      exact ⟨v,source.transitive x hx v vx,
        (mx.2 v x).mpr ⟨source.transitive x hx v vx,hx,vx⟩,(fixed v v).mpr ⟨vu,rfl⟩⟩
    · rintro ⟨v',_,vx,vv⟩
      have eq := ((fixed v' v).mp vv).2
      subst v'
      have vx := ((mx.2 v x).mp vx).2.2
      exact (my.2 v x).mpr ⟨target.transitive x hy v vx,hy,vx⟩
  have not_le (le : M.MemberSubset L κ) : False := absent
    (agree.subset_l.set_l hZF source target hx (fun v hv => le v (sub' v hv)))
  have below : M.mem κ L := by
    rcases (rank.ordinal_l h.common.left_rank.2.1).trichotomy hZF.1 ordinal
      (KP.difference_exists_d (ZF.modelsKP hZF)) (KP.intersection_exists_d (ZF.modelsKP hZF) L κ) with eq | lt | gt
    · exact (not_le (fun v hv => (eq v).mp hv)).elim
    · exact (not_le (ordinal.transitive L lt)).elim
    · exact gt
  have limit := (copy.limit_l hZF source.omega source.transitive h.left_trans mx ma h.left_end).mpr h.limit
  have low := source.rank_agree_l hZF h.common.left_rank.2.1 rank limit
    (rank.ordinal_subset_l hZF source.transitive h.common.left_rank.2.1 κ below)
  refine ⟨below,?_⟩
  intro n D' E E' hn space hE subE image
  exact h.points E E' E image ((fixed E E).mpr ⟨(low n D' E hn space subE).mpr hE,rfl⟩)

/-- 指定原活动步自动读取其两源及历史交换，不另要求源理论或规范化假设。 -/
theorem Ic_history_d.fixed_read_l
    {ω c₀ T Q G E L m H ST QT GT i n X A π z Z α Y B σ u U β c d b j p κ ρ F : M.Domain}
    (nice : It_pnice_d hZF ω c₀ ω T Q G E L)
    (hist : Ic_history_d hZF ω T Q G E L m H ST QT GT)
    (old : Ic_at_d H i X A π z Z α) (top : Ic_at_d H n Y B σ u U β)
    (hn : M.mem n ω) (before : i = n ∨ M.mem i n)
    (qd : Rd_entry_d i d Q) (qc : Rd_entry_d n c Q) (event : Rd_entry_d n p E)
    (payload : It_payload_d p κ ρ F) (active : It_active_d hZF ω c d b j p) :
    Ea_maps_d ω κ X π σ ∧ ∃ κ', Rd_entry_d κ κ' π ∧ Rd_entry_d κ κ' σ ∧ Ea_agree_d ω κ' Z U := by
  have level := (nice.levels n ρ).mpr ⟨p,κ,F,event,payload⟩
  obtain ⟨d',qd',_,row⟩ := hist.row_l hZF old
  have eq := nice.tree.diagram.model_function.2 i d' d qd' qd
  subst d'
  obtain ⟨c',qc',_,own⟩ := hist.row_l hZF top
  have eq := nice.tree.diagram.model_function.2 n c' c qc' qc
  subst c'
  have data := row
  obtain ⟨R,RA,RZ,a,KA,KZ,mx₀,ma,mz,sa,az,hA,ra,hα,copy⟩ := data
  have data := own
  obtain ⟨S,RB,RU,a',KB,KU,my₀,mb,mu,sb,bu,hB,rb,hβ,map⟩ := data
  obtain ⟨X',R',mx,xt⟩ := nice.active_prefix_l hZF hn level i d before qd
  obtain ⟨eqX,eqR⟩ := smdl_unique_l I mx.1 mx₀
  subst X' R'
  obtain ⟨Y',S',my,yt⟩ := nice.active_prefix_l hZF hn level n c (Or.inl rfl) qc
  obtain ⟨eqY,eqS⟩ := smdl_unique_l I my.1 my₀
  subst Y' S'
  obtain ⟨X',R',K,mx',parent⟩ := (row.source_l hZF).mem_l hZF ⟨X,R,mx,xt⟩
  obtain ⟨eqX,eqR⟩ := smdl_unique_l I mx'.1 mx.1
  subst X' R'
  obtain ⟨Y',S',K',my',owner⟩ := (own.source_l hZF).mem_l hZF ⟨Y,S,my,yt⟩
  obtain ⟨eqY,eqS⟩ := smdl_unique_l I my'.1 my.1
  subst Y' S'
  obtain ⟨loc,agree,K₀,_,_,_,_,_,_,_,_,_,_,source,_⟩ := active.system_l hZF owner parent my mx payload
  have ordinal := (loc.ordinals_l (ZF.modelsKP hZF) yt ⟨c,my⟩).1
  have back : Ea_agree_d ω κ X Y := fun n D A hn space sub => (agree n D A hn space sub).symm
  obtain ⟨K₁,target⟩ := back.subset_l.alphabet_l hZF source owner ordinal
  obtain ⟨κ',hκA,hκπ⟩ := copy.1.1.2.2 κ source.cardinal_mem
  have ord' := copy.ordinal_l hZF source.omega xt sa.transitive mx ma hκπ ordinal
  have below := copy.ordinal_le_l hZF source.omega xt sa.transitive mx ma hκπ ordinal
  have ωκ' : M.MemberSubset ω κ' := fun v hv => below v (source.below v hv)
  have finish (hκσ : Rd_entry_d κ κ' σ) (small : Ea_agree_d ω κ' A B) : Ea_agree_d ω κ' Z U := by
    obtain ⟨_,_,_,_,_,_,_,_,_,_,outer,_,_,_,_⟩ := row.rebase_l hZF ord' ωκ' hκπ
    obtain ⟨_,_,_,_,_,_,_,_,_,_,outer',_,_,_,_⟩ := own.rebase_l hZF ord' ωκ' hκσ
    have left := outer.source.rank_agree_l hZF hA ra hα hκA
    have right := outer'.source.rank_agree_l hZF hB rb hβ (map.1.1.output_mem_of_pairMember hκσ)
    exact fun n D C hn space sub => (left n D C hn space sub).symm.trans
      ((small n D C hn space sub).trans (right n D C hn space sub))
  have same (eqA : A = B) (eqπ : π = σ) :
      Ea_maps_d ω κ X π σ ∧ ∃ κ', Rd_entry_d κ κ' π ∧ Rd_entry_d κ κ' σ ∧ Ea_agree_d ω κ' Z U := by
    have hκσ := eqπ ▸ hκπ
    have small : Ea_agree_d ω κ' A B := by
      intro n D C hn space sub
      rw [eqA]
    exact ⟨fun _ _ _ _ _ _ _ _ h => eqπ ▸ h,κ',hκπ,hκσ,finish hκσ small⟩
  rcases before with eq | lt
  · subst i
    obtain ⟨_,eqA,eqπ,_,_,_⟩ := old.unique_l (ZF.modelsKP hZF) hist.function top
    exact same eqA eqπ
  rcases (hist.past i n X A π z Z α Y B σ u U β old top lt).prior_l with
      ⟨_,_,_,_,eqA,eqπ⟩ | ⟨μ,l,φ,V,W,D,t,d',c',R',S',qd',qc',mx',my',common⟩
  · exact same eqA eqπ
  have eq := nice.tree.diagram.model_function.2 i d' d qd' qd
  subst d'
  have eq := nice.tree.diagram.model_function.2 n c' c qc' qc
  subst c'
  have eq := (smdl_unique_l I mx' mx.1).2
  subst R'
  have eq := (smdl_unique_l I my' my.1).2
  subst S'
  obtain ⟨low,maps⟩ := common.mem_read_l hZF source target mx my ma copy ordinal back
  have rank := (rr_rank_mem_l I (ZF.modelsKP hZF) mx xt
    common.common.left_rank.1 common.common.left_rank.2.1).mp common.common.left_rank
  have hκV := rank.ordinal_subset_l hZF xt common.common.left_rank.2.1 κ low
  have fixed := ic_common_mem_graph_l hZF common.common mx my xt yt
  have hκσ := common.points κ κ' κ hκπ ((fixed κ κ).mpr ⟨hκV,rfl⟩)
  obtain ⟨C,hCA,hCB,rCA,rCB,hVC,_⟩ := common.work
  have hκC := ((ma.2 κ' C).mp ((copy.relation_l I hZF source.omega mx.1 ma.1 hκπ hVC).mp
    ((mx.2 κ V).mpr ⟨source.cardinal_mem,common.common.left_rank.2.1,hκV⟩))).2.2
  obtain ⟨KA',sa'⟩ := sa.rebase_l hκA ωκ'
    (sc_ordinal_small_l hZF sa.omega sa.transitive ma sa.theory hκA ord')
  have hκB := map.1.1.output_mem_of_pairMember hκσ
  obtain ⟨KB',sb'⟩ := sb.rebase_l hκB ωκ'
    (sc_ordinal_small_l hZF sb.omega sb.transitive mb sb.theory hκB ord')
  have left := sa'.rank_agree_l hZF hCA rCA common.limit hκC
  have right := sb'.rank_agree_l hZF hCB rCB common.limit hκC
  have small : Ea_agree_d ω κ' A B := fun n D C hn space sub =>
    (left n D C hn space sub).symm.trans (right n D C hn space sub)
  exact ⟨maps,κ',hκπ,hκσ,finish hκσ small⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 实际复制行的规范源与同一活动系统

工作外层的枝反射和完整结构核限制到已有的小秩段，再沿同一复制图回拉。
规范原源由此取得层级、幂集、覆盖和不可达闭包；两份实际行自动供应
给定原活动的测度族和协调性，不增加源公理或闭包假设。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Ic_row_d.source_closure_l {ω c X A π z Z α R : M.Domain}
    (row : Ic_row_d hZF ω c X A π z Z α) (mx : Smem_d I c X R) (xt : M.TransitiveSet X) :
    ∃ K, Ep_source_d I ω ω K X R ∧ Sc_branch_d ω X ∧ Sc_hierarchy_d X ∧
      Sc_power_d X ∧ Sc_cover_d X ∧ Sc_inaccessible_closure_d I ω X := by
  obtain ⟨X₀,R₀,K₀,mx₀,source⟩ := (row.source_l hZF).mem_l hZF ⟨X,R,mx,xt⟩
  obtain ⟨ex,er⟩ := smdl_unique_l I mx₀.1 mx.1
  subst X₀ R₀
  obtain ⟨R₁,S,V,a,K,K',raw,ma,mz,small,outer,hA,rank,limit,map⟩ := row
  have er := (smdl_unique_l I raw mx.1).2
  subst R₁
  obtain ⟨hierarchy,power,_,closure⟩ := outer.read_l hZF
  have branches := (outer.closed.bounded_l I).branch_l (ZF.modelsKP hZF)
    outer.source.omega outer.source.transitive mz outer.source.omega_mem
  have ba := branches.rank_l outer.source.transitive hA rank limit small.omega_mem
  have ha := hierarchy.rank_l hZF outer.source.transitive hA rank limit
  have pa := power.rank_l outer.source.transitive hA rank limit
  have ca := sc_rank_cover_l outer.source.transitive hA rank
  have ia := closure.rank_l hZF outer.source.transitive
    (outer.source.algebra_l (ZF.modelsKP hZF)).pair hA rank limit
  exact ⟨K₀,source,
    ba.pull_l hZF source.omega xt small.transitive source.omega_mem mx ma map,
    (sc_hierarchy_iff_l hZF source.omega xt small.transitive mx ma map).mpr ha,
    (sc_power_iff_l hZF source.omega xt small.transitive mx ma map).mpr pa,
    (sc_cover_iff_l hZF source.omega xt small.transitive mx ma map).mpr ca,
    (sc_inaccessible_closure_iff_l hZF source.omega xt small.transitive
      (source.algebra_l (ZF.modelsKP hZF)).pair (small.algebra_l (ZF.modelsKP hZF)).pair
      mx ma map source.omega_mem).mpr ia⟩

/-- 当前活动已给出的不可达支撑，取得同一规范源中的整层枚举及关系码。 -/
theorem Ic_row_d.level_l {ω c X A π z Z α R L : M.Domain}
    (row : Ic_row_d hZF ω c X A π z Z α) (mx : Smem_d I c X R) (xt : M.TransitiveSet X)
    (card : Sc_inaccessible_d ω X L) :
    M.IsLimitOrdinal L ∧ Sc_regular_d X L ∧ Sc_rank_size_d I X L ∧ ∃ W, Er_level_d X L W := by
  obtain ⟨K,source,_,_,_,_,closure⟩ := row.source_closure_l hZF mx xt
  obtain ⟨regular,sizes⟩ := closure L card
  obtain ⟨W,f,hW,rank,hf,bij⟩ := sizes.level
  obtain ⟨T,hT,_,iso⟩ := ep_transitive_code_l hZF source (rank.transitive_l xt hW) hf bij
  exact ⟨card.limit_l (ZF.modelsKP hZF) xt (source.algebra_l (ZF.modelsKP hZF)).pair,
    regular,sizes,W,hW,rank,T,f,hT,hf,iso⟩

/-- 两份真实规范行读取给定活动，并自动生产同一原系统所需的测度族及协调性。 -/
theorem It_active_d.row_data_l
    {ω c d b j p κ ℓ F X R Y S A π z Z α B σ u U β : M.Domain}
    (ownerRow : Ic_row_d hZF ω c X A π z Z α) (parentRow : Ic_row_d hZF ω d Y B σ u U β)
    (mx : Smem_d I c X R) (xt : M.TransitiveSet X) (my : Smem_d I d Y S) (yt : M.TransitiveSet Y)
    (payload : It_payload_d p κ ℓ F) (active : It_active_d hZF ω c d b j p) :
    It_local_d I ω X R κ ℓ F ∧ Ea_agree_d ω κ X Y ∧
      ∃ Ko Kp J O Z₀ H q V W r N T, Ep_source_d I ω κ Ko X R ∧ Ep_source_d I ω κ Kp Y S ∧
        Em_source_d ω κ ℓ Y F ∧ Ec_source_d I ω κ ℓ Y F ∧
        Ep_system_d I ω κ ℓ Y S F J O Z₀ H q V W ∧ Di_limit_d H q V W r N T ∧
        Smdl_d I b N T ∧ Smap_d I ω d b Y N j ∧ Ep_constants_d Y r j := by
  obtain ⟨K₀,owner₀,_,_,power,_,_⟩ := ownerRow.source_closure_l hZF mx xt
  obtain ⟨Y₀,S₀,K₁,my₀,parent₀⟩ := (parentRow.source_l hZF).mem_l hZF ⟨Y,S,my,yt⟩
  obtain ⟨ey,es⟩ := smdl_unique_l I my₀.1 my.1
  subst Y₀ S₀
  obtain ⟨loc,agree,Kp,J,O,Z₀,H,q,V,W,r,N,T,parent,system,limit,target,embed,constants⟩ :=
    active.system_l hZF owner₀ parent₀ mx my payload
  have ordinal := (loc.ordinals_l (ZF.modelsKP hZF) xt ⟨c,mx⟩).1
  have data := loc
  obtain ⟨_,hk,_,_,pre⟩ := (it_local_mem_l I ⟨c,mx⟩).mp data
  simp only [ex_short_m,ex_pre_m,Formula.satisfies_conj_iff,Formula.satisfies_mem_iff] at pre
  obtain ⟨Ko,owner⟩ := owner₀.rebase_l hk (ordinal.transitive ω pre.1.2.2.1)
    (sc_ordinal_small_l hZF owner₀.omega xt mx owner₀.theory hk ordinal)
  have family := (loc.measures_l hZF owner.omega (owner.read_source_l hZF) ⟨c,mx⟩ owner.theory
    (fun _ D _ hd _ => power D hd)).transfer_l agree
  have coherent := (loc.coherent_l hZF (owner.read_source_l hZF) ⟨c,mx⟩).transfer_l hZF agree
  exact ⟨loc,agree,Ko,Kp,J,O,Z₀,H,q,V,W,r,N,T,owner,parent,family,coherent,system,limit,target,embed,constants⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 给定原后继与所属源的共同支撑秩段

所属行与同一坍塌目标的真实复制行提供全部闭包。只在实际临界点和支撑
重定源证书，再把原最大强度送入指定后继；共同秩段、源内枚举及两个
支撑源一并返回，供同一原目标的共同图直接使用。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZFC : M.Models ZFC)
local notation "hZF" => ZFC.models_zf_l hZFC
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem It_local_d.fixed_rank_l
    {ω κ K X R Y S L F N T d B σ u U β b C τ z Z α : M.Domain}
    (source : Ep_source_d I ω κ K X R)
    (ownerRow : Ic_row_d hZF ω d Y B σ u U β)
    (normRow : Ic_row_d hZF ω b N C τ z Z α)
    (my : Smem_d I d Y S) (yt : M.TransitiveSet Y) (mn : Smem_d I b N T)
    (agree : Ea_agree_d ω κ X Y) (loc : It_local_d I ω Y S κ L F)
    (strength : Ex_strength_d I ω κ L Y F) (card : Sc_inaccessible_d ω Y L)
    (next : Ep_successor_d hZF ω κ L X R F N T) (member : M.mem L N) :
    ∃ Ko Kn, Ep_source_d I ω L Ko Y S ∧ Ep_source_d I ω L Kn N T ∧
      ∃ W, M.mem W Y ∧ Vr_d Y L W ∧ Er_level_d N L W ∧
        Sc_rank_size_d I N L ∧ Es_strength_d Y L N := by
  -- 传递性读取指定后继的实际坍塌；这里没有另选目标。
  have nt : M.TransitiveSet N := by
    obtain ⟨_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,trans,_⟩ := next
    exact trans
  obtain ⟨K₀,owner₀,branches,_,power,cover,_⟩ := ownerRow.source_closure_l hZF my yt
  obtain ⟨K₁,target₀,_,hierarchy,targetPower,_,_⟩ := normRow.source_closure_l hZF mn nt
  obtain ⟨limit,_,sizes,_⟩ := ownerRow.level_l hZF my yt card
  have ord := (loc.ordinals_l (ZF.modelsKP hZF) yt ⟨d,my⟩).1
  have data := loc
  obtain ⟨_,hκ,hL,_,_⟩ := data
  have inaccessible := card
  obtain ⟨_,_,valid⟩ := inaccessible
  have above : M.mem ω L := ((Formula.satisfies_conj_iff ..).mp valid).1
  have below : M.MemberSubset ω L := limit.1.transitive ω above
  -- 有限幂和内部编号只随实际 κ、L 重定，模型及其关系码保持同一份。
  obtain ⟨Kκ,owner⟩ := owner₀.rebase_l hκ source.below
    (sc_ordinal_small_l hZF source.omega yt my owner₀.theory hκ ord)
  obtain ⟨Ko,ownerL⟩ := owner₀.rebase_l hL below
    (sc_ordinal_small_l hZF source.omega yt my owner₀.theory hL limit.1)
  obtain ⟨Kn,target⟩ := target₀.rebase_l member below
    (sc_ordinal_small_l hZF source.omega nt mn target₀.theory member limit.1)
  obtain ⟨W,hW,rank,level,sizes',exactness,_⟩ :=
    loc.rank_agree_l hZFC source owner target agree branches power cover hierarchy targetPower
      sizes limit next strength
  exact ⟨Ko,Kn,ownerL,target,W,hW,rank,level,sizes',exactness⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 固定原活动系统的实际工作后继

所属行搬运同一扩展器的最大强度与不可达性；外层实际施加它后，
给定原商极限经代表复制进入这条大超幂边的集合像 j(A)。原目标、原常值边、
复制因子和代表求值均保留，下一行不预设原后继良基或已有共同层。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

/-- 同一次原商、大商和复制因子的证书，供下一共同层读取原代表。 -/
def Ic_fixed_factor_d (hZF : M.Models ZF)
    (ω κ L F c b j₀ κ' L' F' z v j A C π σ k : M.Domain) : Prop :=
  let I := kp_pair_l (ZF.modelsKP hZF)
  ∃ X R P Rₚ Z Rz N Rn a Sc a₀ Ra,
    Smem_d I c X R ∧ Smdl_d I b P Rₚ ∧ Smem_d I z Z Rz ∧ Smem_d I v N Rn ∧ Smem_d I a C Sc ∧
    Smem_d I a₀ A Ra ∧ Smap_d I ω c a₀ X A π ∧ Smap_d I ω c b X P j₀ ∧ Smap_d I ω b a P C k ∧
    ∃ J O D H p T V q,
      Ep_system_d I ω κ L X R F J O D H p T V ∧ Di_limit_d H p T V q P Rₚ ∧ Ep_constants_d X q j₀ ∧
      ∃ J₁ O₁ D₁ H₁ p₁ T₁ V₁ q₁ b₁ P₁ R₁ i₁ g₁,
        Ep_system_d I ω κ' L' Z Rz F' J₁ O₁ D₁ H₁ p₁ T₁ V₁ ∧ Di_limit_d H₁ p₁ T₁ V₁ q₁ P₁ R₁ ∧
        Smdl_d I b₁ P₁ R₁ ∧ Wc_graph_d P₁ R₁ g₁ ∧ M.IsSetBijectionFromTo I g₁ P₁ N ∧
        Smap_d I ω b₁ v P₁ N g₁ ∧ Smap_d I ω z v Z N j ∧ Ep_constants_d Z q₁ i₁ ∧ It_comp_d i₁ g₁ j ∧
        ∃ J₂ O₂ D₂ H₂ p₂ T₂ V₂ q₂ b₂ P₂ R₂ τ ν,
          Ep_system_d I ω κ' L' A Ra F' J₂ O₂ D₂ H₂ p₂ T₂ V₂ ∧
          Di_limit_d H₂ p₂ T₂ V₂ q₂ P₂ R₂ ∧ Smdl_d I b₂ P₂ R₂ ∧
          Smap_d I ω b b₂ P P₂ τ ∧ Smap_d I ω b₂ a P₂ C ν ∧
          (∀ E B, Rd_entry_d E B τ ↔ M.mem E P ∧ ∃ u, Rd_entry_d u E q ∧ Ec_node_d π σ q₂ u B) ∧
          (∀ a f E x, Ep_repr_d q₂ a f E → Rd_entry_d E x ν → Ep_value_d q₁ g₁ a f x) ∧
          It_comp_d τ ν k ∧ ∀ a a' f f' E x, Rd_entry_d a a' σ → Rd_entry_d f f' π →
            Ep_repr_d q a f E → Ep_value_d q₁ g₁ a' f' x → Rd_entry_d E x k

variable (hZFC : M.Models ZFC)
local notation "hZF" => ZFC.models_zf_l hZFC
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

/-- 两份实际行和真实活动系统生成下一行，兼容性只用已经读取的有限幂交换。 -/
theorem Ic_row_d.fixed_step_l
    {ω c X A π z Z α d Y B σ u U β R S b j₀ p κ κ' L F : M.Domain}
    (row : Ic_row_d hZF ω c X A π z Z α) (own : Ic_row_d hZF ω d Y B σ u U β)
    (mx : Smem_d I c X R) (xt : M.TransitiveSet X) (my : Smem_d I d Y S) (yt : M.TransitiveSet Y)
    (payload : It_payload_d p κ L F) (active : It_active_d hZF ω d c b j₀ p)
    (strength : Ex_strength_d I ω κ L Y F) (card : Sc_inaccessible_d ω Y L)
    (maps : Ea_maps_d ω κ X π σ) (hκπ : Rd_entry_d κ κ' π) (hκσ : Rd_entry_d κ κ' σ)
    (compatible : Ea_agree_d ω κ' Z U) :
    ∃ P Rₚ N v C γ j k L' F', Smdl_d I b P Rₚ ∧ Ic_row_d hZF ω b P C k v N γ ∧
      Rd_entry_d L L' σ ∧ Rd_entry_d F F' σ ∧ Rd_entry_d α γ j ∧ Rd_entry_d A C j ∧
      It_ultra_d I ω κ' L' F' z v j ∧
      (∀ x x' y y', Rd_entry_d x x' π → Rd_entry_d x y j₀ → Rd_entry_d x' y' j → Rd_entry_d y y' k) ∧
      Wf_rel_d P Rₚ ∧ It_source_d hZF ω b ∧ Ic_quality_d hZF ω κ' L' F' u U ∧
      (∃ D, M.mem D U ∧ Vr_d U L' D ∧ Er_level_d N L' D ∧ Sc_rank_size_d I N L' ∧
        Es_strength_d U L' N ∧ ∀ η, M.mem η L' → Ea_agree_d ω η U N) ∧
      Ic_fixed_factor_d hZF ω κ L F c b j₀ κ' L' F' z v j A C π σ k := by
  obtain ⟨loc,agree,Ko,Kp,J₀,O₀,D₀,H₀,p₀,T₀,V₀,q₀,P,Rₚ,owner,parent,family,coherent,
    system₀,limit₀,original,embed₀,constants₀⟩ := active.row_data_l hZF own row my yt mx xt payload
  have data := row
  obtain ⟨R₀,Ra,Rz,a,Ka,Kz,raw,ma,mz,small,ambient,hA,ra,hα,copy⟩ := data
  have eq := (smdl_unique_l I raw mx.1).2
  subst R₀
  have data := own
  obtain ⟨S₀,Rb,Ru,a₁,Kb,Ku,raw,mb,mu,cut,outer,hB,rb,hβ,map⟩ := data
  have eq := (smdl_unique_l I raw my.1).2
  subst S₀
  have ordinal := (loc.ordinals_l (ZF.modelsKP hZF) yt ⟨d,my⟩).1
  have ord' := copy.ordinal_l hZF parent.omega xt small.transitive mx ma hκπ ordinal
  have below := copy.ordinal_le_l hZF parent.omega xt small.transitive mx ma hκπ ordinal
  have ωκ' : M.MemberSubset ω κ' := fun x hx => below x (parent.below x hx)
  have hκA := copy.1.1.output_mem_of_pairMember hκπ
  have hκB := map.1.1.output_mem_of_pairMember hκσ
  obtain ⟨Ka',sa⟩ := small.rebase_l hκA ωκ'
    (sc_ordinal_small_l hZF parent.omega small.transitive ma small.theory hκA ord')
  have hκZ := ambient.source.transitive A hA κ' hκA
  obtain ⟨Kz',az⟩ := ambient.rebase_l hZF hκZ ωκ'
    (sc_ordinal_small_l hZF parent.omega ambient.source.transitive mz ambient.source.theory hκZ ord')
  have hκU := outer.source.transitive B hB κ' hκB
  obtain ⟨Ku',ou⟩ := outer.rebase_l hZF hκU ωκ'
    (sc_ordinal_small_l hZF parent.omega outer.source.transitive mu outer.source.theory hκU ord')
  obtain ⟨L',hL',hL⟩ := map.1.1.2.2 L strength.2.2.1
  obtain ⟨F',hF',hF⟩ := map.1.1.2.2 F strength.2.2.2.1
  have hw := map.omega_l I hZF parent.omega yt cut.transitive my mb owner.omega_mem
  have loc' := loc.map_l hZF parent.omega my.1 mb.1 map hw hκσ hL hF
  have strong' := strength.map_l hZF parent.omega yt cut.transitive my mb map cut.theory hκσ hL hF
  have card' := card.map_l hZF parent.omega yt cut.transitive my mb map hL
  have card_u := card'.of_rank_l hZF ou.source.transitive (ou.source.algebra_l (ZF.modelsKP hZF)).pair hB rb hβ
  obtain ⟨_,power,cover,inaccessible⟩ := ou.read_l hZF
  obtain ⟨regular,sizes⟩ := inaccessible L' card_u
  have above : M.mem ω L' := (Formula.satisfies_mem_iff _ _ _).mp
    ((Formula.satisfies_conj_iff _ _ _).mp card_u.2.2).1
  obtain ⟨up,strong,card_full,N,Rn,v,j,Kn,D,hn,big,next,hD,rD,level,rank_size,exactness,later⟩ :=
    az.rank_apply_l hZFC ou.source (ou.closed.bounded_l I) power cover (regular ω above) sizes
      compatible mz hB rb hβ ⟨a₁,mb⟩ loc' strong' card'
  -- 同一大超幂边搬运原工作秩段及其高度，得到实际的集合像。
  have hj := big.elementary_l hZF mz.1 hn.1
  obtain ⟨C,hC,hAC⟩ := hj.1.1.2.2 A hA
  obtain ⟨E,e,hE,he,cert⟩ := ra
  have hαZ := sc_function_domain_mem_l hZF parent.omega az.source.transitive mz az.source.theory he (cert A hA).2.1
  have ra : Vr_d Z α A := ⟨E,e,hE,he,cert⟩
  obtain ⟨γ,hγ,hαγ⟩ := hj.1.1.2.2 α hαZ
  have rc := (hj.hierarchy_l hZF parent.omega az.source.transitive next.source.transitive mz hn hαγ hAC).mp ra
  have hγlim := (hj.limit_l hZF parent.omega az.source.transitive next.source.transitive mz hn hαγ).mp hα
  have hwj := hj.omega_l I hZF parent.omega az.source.transitive next.source.transitive mz hn az.source.omega_mem
  have hωC := ((hn.2 ω C).mp ((hj.relation_l I hZF parent.omega mz.1 hn.1 hwj hAC).mp
    ((mz.2 ω A).mpr ⟨az.source.omega_mem,hA,small.omega_mem⟩))).2.2
  obtain ⟨a₂,Sc,mc⟩ := smdl_membership_l I hZF ⟨ω,hωC⟩
  have relation := ep_set_membership_l hZF az.source next.source mz hn hj ma mc hAC
  obtain ⟨r,_,hr⟩ := ep_set_restriction_l hZF az.source next.source mz hn hj ma.1 mc.1 hAC relation
  obtain ⟨Kc,sc⟩ := (it_source_mem_l hZF ma small).image_mem_l hZF ma.1 mc
    (rc.transitive_l next.source.transitive hC) hr
  -- 原源与完整工作源的两份商系统由同一次代表复制连接。
  have reverse : Ea_agree_d ω κ' U Z := fun n D A hn space sub => (compatible n D A hn space sub).symm
  have family' := (up.measures_l hZF parent.omega (ou.source.read_source_l hZF) ⟨u,mu⟩ ou.source.theory
    (fun _ D _ hD _ => power D hD)).transfer_l reverse
  have coherent' := (up.coherent_l hZF (ou.source.read_source_l hZF) ⟨u,mu⟩).transfer_l hZF reverse
  have saved := big
  obtain ⟨Z₀,Rz₀,N₀,Rn₀,J₁,O₁,D₁,H₁,p₁,T₁,V₁,q₁,b₁,P₁,R₁,i₁,g₁,
    mz₀,mn₀,system₁,limit₁,model₁,wc,bij,hg,_,constants₁,_,comp⟩ := saved
  obtain ⟨eqZ,eqR⟩ := smdl_unique_l I mz₀.1 mz.1
  subst Z₀ Rz₀
  obtain ⟨eqN,eqR⟩ := smdl_unique_l I mn₀.1 hn.1
  subst N₀ Rn₀
  have rank_agree := az.source.rank_agree_l hZF hA ra hα hκA
  obtain ⟨J₂,O₂,D₂,H₂,p₂,T₂,V₂,q₂,b₂,P₂,R₂,τ,ν,k,system₂,limit₂,model₂,hτ,hν,hk,
    nodes,values,copied,commute,factor⟩ :=
    ep_set_factor_l hZFC parent sa az.source next.source mx ma mz hn mc copy hκπ
      yt cut.transitive my mb map owner.theory owner.omega_mem hL hF family family' coherent coherent' maps
      system₀ limit₀ original constants₀ system₁ limit₁ model₁ hg hj constants₁ comp hAC
      (fun n D A hn space sub => (rank_agree n D A hn space sub).mpr)
  -- 原后继的完整源和良基性从实际集合像沿 k 回传，绝不先假定原后继为隶属模型。
  have ready := (it_source_mem_l hZF mc sc).pull_l hZF original mc.1 hk
  have wfC : Wf_rel_d C Sc := by
    intro B _ ne
    obtain ⟨x,hx,minimal⟩ := KP.mem_minimal_exists_d (ZF.modelsKP hZF) ne
    exact ⟨x,hx,fun y hy edge => minimal y hy ((mc.2 y x).mp edge).2.2⟩
  have wf := wf_of_map_l hZF wfC (fn0_of_function_l (ZF.modelsKP hZF) hk.1.1)
    (fun a b x y edge ha hb => (hk.relation_l I hZF parent.omega original mc.1 ha hb).mp edge)
  obtain ⟨Kn',nextω⟩ := next.rebase_l hZF next.source.omega_mem (fun _ h => h)
    (next.source.cardinal_small.mono_mem_l I hn next.source.omega_mem next.source.below)
  exact ⟨P,Rₚ,N,v,C,γ,j,k,L',F',original,
    ⟨Rₚ,Sc,Rn,a₂,Kc,Kn',original,mc,hn,sc,nextω,hC,rc,hγlim,hk⟩,
    hL,hF,hαγ,hAC,big,commute,wf,ready,⟨Ru,parent.omega,ou.source.transitive,mu,up,strong,card_full⟩,
    ⟨D,hD,rD,level,rank_size,exactness,later⟩,
    ⟨X,R,P,Rₚ,Z,Rz,N,Rn,a₂,Sc,a,Ra,mx,original,mz,hn,mc,ma,copy,embed₀,hk,
      J₀,O₀,D₀,H₀,p₀,T₀,V₀,q₀,system₀,limit₀,constants₀,
      J₁,O₁,D₁,H₁,p₁,T₁,V₁,q₁,b₁,P₁,R₁,i₁,g₁,system₁,limit₁,model₁,wc,bij,hg,hj,constants₁,comp,
      J₂,O₂,D₂,H₂,p₂,T₂,V₂,q₂,b₂,P₂,R₂,τ,ν,system₂,limit₂,model₂,hτ,hν,nodes,values,factor,copied⟩⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 给定原商的坍塌及固定复制图的共轭

原系统和原常值图保持不变。已证良基性给出这个原目标的完整 Mostowski 同构，
原复制图沿其逆图共轭；两条复合方程将后续支撑证明接回同一个原目标。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Ep_system_d.fixed_collapse_l
    {ω κ K L X R F J O Z A p V W q b P Rp c j a C k : M.Domain}
    (source : Ep_source_d I ω κ K X R) (mx : Smem_d I c X R)
    (system : Ep_system_d I ω κ L X R F J O Z A p V W)
    (limit : Di_limit_d A p V W q P Rp) (model : Smdl_d I b P Rp)
    (embed : Smap_d I ω c b X P j) (constants : Ep_constants_d X q j)
    (wf : Wf_rel_d P Rp) (copy : Smap_d I ω b a P C k) :
    ∃ N T d g inv j' k', Smem_d I d N T ∧ M.TransitiveSet N ∧ Wc_graph_d P Rp g ∧
      M.IsSetBijectionFromTo I g P N ∧ Smap_d I ω b d P N g ∧
      M.IsSetBijectionFromTo I inv N P ∧ (∀ x y, Rd_entry_d y x inv ↔ Rd_entry_d x y g) ∧
      Smap_d I ω d b N P inv ∧ Smap_d I ω d a N C k' ∧ It_comp_d g k' k ∧ It_comp_d j g j' ∧
      It_ultra_d I ω κ L F c d j' ∧ Ep_successor_d hZF ω κ L X R F N T ∧
      ∃ K', Ep_source_d I ω ω K' N T := by
  have ext : Wc_ext_d X R := fun x hx y hy same => hZF.1.eq_of_same_members x y (fun z =>
    ⟨fun hz => ((mx.2 z y).mp ((same z (source.transitive x hx z hz)).mp
      ((mx.2 z x).mpr ⟨source.transitive x hx z hz,hx,hz⟩))).2.2,
      fun hz => ((mx.2 z x).mp ((same z (source.transitive y hy z hz)).mpr
      ((mx.2 z y).mpr ⟨source.transitive y hy z hz,hy,hz⟩))).2.2⟩)
  obtain ⟨N,g,inv,d,T,trans,collapse,bij,mn,hg,bi,inverse,back⟩ :=
    wc_smaps_l hZF source.omega model wf (embed.extensional_l hZF source.omega mx.1 model ext)
  obtain ⟨j',hj,js⟩ := smap_comp_l I hZF embed hg
  have comp : It_comp_d j g j' := ⟨hj.1.1.1.1,fun x y => (js x y).trans
    ⟨And.right,fun ⟨E,hxE,hEy⟩ => ⟨embed.1.1.input_mem_of_pairMember hxE,E,hxE,hEy⟩⟩⟩
  obtain ⟨k',hk,ks⟩ := smap_comp_l I hZF back copy
  have conjugate : It_comp_d g k' k := by
    refine ⟨copy.1.1.1.1,fun x y => ⟨?_,?_⟩⟩
    · intro hxy
      obtain ⟨E,hE,hxE⟩ := hg.1.1.2.2 x (copy.1.1.input_mem_of_pairMember hxy)
      exact ⟨E,hxE,(ks E y).mpr ⟨hE,x,(inverse x E).mpr hxE,hxy⟩⟩
    · rintro ⟨E,hxE,hEy⟩
      obtain ⟨_,z,hEz,hzy⟩ := (ks E y).mp hEy
      exact bij.1.2 z x E ((inverse z E).mp hEz) hxE ▸ hzy
  have ultra : It_ultra_d I ω κ L F c d j' :=
    ⟨X,R,N,T,J,O,Z,A,p,V,W,q,b,P,Rp,j,g,mx,mn,system,limit,model,
      collapse,bij,hg,embed,constants,hj,comp⟩
  have hw := hj.omega_l I hZF source.omega source.transitive trans mx mn source.omega_mem
  obtain ⟨K',next⟩ := source.successor_l hZF mx mn trans hj
    (hj.1.1.output_mem_of_pairMember hw) (fun _ h => h)
    ((hj.small_l I hZF source.omega mx.1 mn.1 hw).mp
      (source.cardinal_small.mono_mem_l I mx source.omega_mem source.below))
  exact ⟨N,T,d,g,inv,j',k',mn,trans,collapse,bij,hg,bi,inverse,back,hk,conjugate,comp,ultra,
    ⟨J,O,Z,A,p,V,W,q,b,P,Rp,d,g,system,limit,model,mn,trans,collapse,bij,hg⟩,K',next⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 固定复制后继在支撑以下的实际对应

原商只使用因子包中保存的那一份系统。已证良基性给出同对象的坍塌呈示，
原复制图沿其逆图共轭；同一次代表方程随后确定全部支撑子集的复制值。
规范后继仍以原工作集合像为目标，因而也返回一条可直接读取结构闭包的真实行。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZFC : M.Models ZFC)
local notation "hZF" => ZFC.models_zf_l hZFC
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Ic_fixed_factor_d.support_l
    {ω κ L F c b j₀ κ' L' F' z v j A C π σ k X R Y S d B u U β Z α P Rp N γ p : M.Domain}
    (packet : Ic_fixed_factor_d hZF ω κ L F c b j₀ κ' L' F' z v j A C π σ k)
    (row : Ic_row_d hZF ω c X A π z Z α) (own : Ic_row_d hZF ω d Y B σ u U β)
    (next : Ic_row_d hZF ω b P C k v N γ)
    (mx : Smem_d I c X R) (xt : M.TransitiveSet X) (my : Smem_d I d Y S) (yt : M.TransitiveSet Y)
    (payload : It_payload_d p κ L F) (active : It_active_d hZF ω d c b j₀ p)
    (card : Sc_inaccessible_d ω Y L) (maps : Ea_maps_d ω κ X π σ)
    (hκπ : Rd_entry_d κ κ' π) (hκσ : Rd_entry_d κ κ' σ)
    (hLσ : Rd_entry_d L L' σ) (hFσ : Rd_entry_d F F' σ)
    (compatible : Ea_agree_d ω κ' Z U) (hAC : Rd_entry_d A C j)
    (original : Smdl_d I b P Rp) (wf : Wf_rel_d P Rp)
    (commute : ∀ x x' E y, Rd_entry_d x x' π → Rd_entry_d x E j₀ → Rd_entry_d x' y j → Rd_entry_d E y k) :
    ∃ Q T e g inv jn kn K a Sc, Smem_d I e Q T ∧ M.TransitiveSet Q ∧ Wc_graph_d P Rp g ∧
      M.IsSetBijectionFromTo I g P Q ∧ Smap_d I ω b e P Q g ∧
      M.IsSetBijectionFromTo I inv Q P ∧ (∀ x y, Rd_entry_d y x inv ↔ Rd_entry_d x y g) ∧
      Smap_d I ω e b Q P inv ∧ Smem_d I a C Sc ∧ Smap_d I ω e a Q C kn ∧
      Ic_row_d hZF ω e Q C kn v N γ ∧ It_comp_d g kn k ∧ It_comp_d j₀ g jn ∧
      It_ultra_d I ω κ L F c e jn ∧ Ep_successor_d hZF ω κ L X R F Q T ∧ Ep_source_d I ω ω K Q T ∧
      M.mem L Q ∧ M.mem L' C ∧
      (∀ ξ ξ', M.mem ξ L → Rd_entry_d ξ ξ' σ → Rd_entry_d ξ ξ' kn) ∧
      Rd_entry_d L L' kn ∧ Ea_maps_d ω L Q kn σ := by
  -- 这里只读取原源和所属数据；本次商系统始终从 packet 取得。
  obtain ⟨loc,agree,Ko,Kp,_,_,_,_,_,_,_,_,_,_,owner,parent,family,coherent,_⟩ :=
    active.row_data_l hZF own row my yt mx xt payload
  obtain ⟨_,_,_,_,power,_,_⟩ := own.source_closure_l hZF my yt
  obtain ⟨hlim,_,_,V₀,level⟩ := own.level_l hZF my yt card
  have data := row
  obtain ⟨R₀,Ra,Rz,a₀,Ka,Kz,raw,ma,mz,small,ambient,hA,ra,hα,copy⟩ := data
  have eq := (smdl_unique_l I raw mx.1).2
  subst R₀
  have data := own
  obtain ⟨S₀,Rb,Ru,a₁,Kb,Ku,raw,mb,mu,cut,outer,hB,rb,hβ,map⟩ := data
  have eq := (smdl_unique_l I raw my.1).2
  subst S₀
  have data := next
  obtain ⟨Rp₀,Sc,Rn,a₂,Kc,Kn,mp,mc,mn,cutC,outerN,hC,rc,hγ,copyN⟩ := data
  have eq := (smdl_unique_l I mp original).2
  subst Rp₀
  obtain ⟨X₀,R₀,P₀,Rp₀,Z₀,Rz₀,N₀,Rn₀,a₂',Sc₀,a₀',Ra₀,
    mx₀,mp₀,mz₀,mn₀,mc₀,ma₀,copy₀,embed,rawk,
    J₀,O₀,D₀,H₀,p₀,T₀,V₁,q₀,system₀,limit₀,constants₀,
    J₁,O₁,D₁,H₁,p₁,T₁,V₂,q₁,b₁,P₁,R₁,i₁,g₁,system₁,limit₁,model₁,wc₁,bij₁,hg₁,hj,constants₁,comp₁,
    J₂,O₂,D₂,H₂,p₂,T₂,V₃,q₂,b₂,P₂,R₂,τ,ν,system₂,limit₂,model₂,hτ,hν,nodes,values,factor,copied⟩ := packet
  obtain ⟨eqX,eqR⟩ := smdl_unique_l I mx₀.1 mx.1
  subst X₀ R₀
  obtain ⟨eqP,eqR⟩ := smdl_unique_l I mp₀ original
  subst P₀ Rp₀
  obtain ⟨eqZ,eqR⟩ := smdl_unique_l I mz₀.1 mz.1
  subst Z₀ Rz₀
  obtain ⟨eqN,eqR⟩ := smdl_unique_l I mn₀.1 mn.1
  subst N₀ Rn₀
  obtain ⟨eqA,eqR⟩ := smem_unique_l I hZF.1 ma₀ ma
  subst a₀' Ra₀
  obtain ⟨eqC,eqR⟩ := smem_unique_l I hZF.1 mc₀ mc
  subst a₂' Sc₀
  obtain ⟨Q,T,e,g,inv,jn,kn,mq,qt,wc,bij,hg,bi,inverse,back,hkn,conjugate,comp,ultra,successor,Kq,sq⟩ :=
    system₀.fixed_collapse_l hZF parent mx limit₀ original embed constants₀ wf rawk
  -- κ 的同一实际像重定工作源；两个外层的一致性限制到所属小秩段。
  have ordinal := (loc.ordinals_l (ZF.modelsKP hZF) yt ⟨d,my⟩).1
  have ord' := copy.ordinal_l hZF parent.omega xt small.transitive mx ma hκπ ordinal
  have below := copy.ordinal_le_l hZF parent.omega xt small.transitive mx ma hκπ ordinal
  have ωκ' : M.MemberSubset ω κ' := fun x hx => below x (parent.below x hx)
  have hκA := copy.1.1.output_mem_of_pairMember hκπ
  have hκB := map.1.1.output_mem_of_pairMember hκσ
  obtain ⟨Ka',sa⟩ := small.rebase_l hκA ωκ'
    (sc_ordinal_small_l hZF parent.omega small.transitive ma small.theory hκA ord')
  obtain ⟨Kb',sb⟩ := cut.rebase_l hκB ωκ'
    (sc_ordinal_small_l hZF parent.omega cut.transitive mb cut.theory hκB ord')
  have hκZ := ambient.source.transitive A hA κ' hκA
  obtain ⟨Kz',az⟩ := ambient.rebase_l hZF hκZ ωκ'
    (sc_ordinal_small_l hZF parent.omega ambient.source.transitive mz ambient.source.theory hκZ ord')
  have hκU := outer.source.transitive B hB κ' hκB
  obtain ⟨Ku',ou⟩ := outer.rebase_l hZF hκU ωκ'
    (sc_ordinal_small_l hZF parent.omega outer.source.transitive mu outer.source.theory hκU ord')
  have rankB := ou.source.rank_agree_l hZF hB rb hβ hκB
  have agree' : Ea_agree_d ω κ' Z B := fun n D A hn space sub =>
    (compatible n D A hn space sub).trans (rankB n D A hn space sub).symm
  have reverse : Ea_agree_d ω κ' B Z := fun n D A hn space sub => (agree' n D A hn space sub).symm
  have original_agree : Ea_agree_d ω κ X Y := fun n D A hn space sub => (agree n D A hn space sub).symm
  have hw := map.omega_l I hZF parent.omega yt cut.transitive my mb owner.omega_mem
  have loc' := loc.map_l hZF parent.omega my.1 mb.1 map hw hκσ hLσ hFσ
  have powerB := ((outer.read_l hZF).2.1).rank_l outer.source.transitive hB rb hβ
  have family' := (loc'.measures_l hZF parent.omega (sb.read_source_l hZF) ⟨a₁,mb⟩ sb.theory
    (fun _ D _ hD _ => powerB D hD)).transfer_l reverse
  have coherent' := (loc'.coherent_l hZF (sb.read_source_l hZF) ⟨a₁,mb⟩).transfer_l hZF reverse
  have rankA := az.source.rank_agree_l hZF hA ra hα hκA
  have hjn := ultra.elementary_l hZF mx.1 mq.1
  obtain ⟨_,hLQ,hLC,fixed,support,subsets,_⟩ :=
    ep_set_support_l hZFC parent sa az.source owner sb original_agree agree' power
      mx ma mz mn mc copy hκπ my mb map hκσ hLσ hFσ maps loc hlim level
      (fun n D A hn space sub => (rankA n D A hn space sub).mpr)
      family coherent family' coherent' system₀ limit₀ original mq qt wc bij hg hjn constants₀ comp
      system₁ limit₁ model₁ outerN.source.transitive wc₁ bij₁ hg₁ hj constants₁ comp₁ hAC
      system₂ limit₂ hτ.1.1 hν.1.1 nodes values factor conjugate hkn copied commute
  exact ⟨Q,T,e,g,inv,jn,kn,Kq,a₂,Sc,mq,qt,wc,bij,hg,bi,inverse,back,mc,hkn,
    ⟨T,Sc,Rn,a₂,Kc,Kn,mq.1,mc,mn,cutC,outerN,hC,rc,hγ,hkn⟩,
    conjugate,comp,ultra,successor,sq,hLQ,hLC,fixed,support,subsets⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 相容有限复制历史的并

三张实际图取并后仍为函数。每个旧定义域上的限制恰为原图，因此所有
有限元条件在包含其指标的同一阶段验证，得到长度ω的完整复制图列。
阶段长度只要求在ω内且覆盖本轮指标，不要求等于该指标的后继。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

def Ic_extend_d (s t : M.Domain) : Prop := ∃ H S Q G H' S' Q' G', Rd_quad_d s H S Q G ∧ Rd_quad_d t H' S' Q' G' ∧
  M.MemberSubset H H' ∧ M.MemberSubset Q Q' ∧ M.MemberSubset G G'
def ic_extend_m {d} (s t : Term d) : Formula 1 d := set[d] ⟪
  ∃ H S Q G H' S' Q' G', ⌜rd_quad_m⌝ₚ(⌜s⌝ₛ, H, S, Q, G) ∧ ⌜rd_quad_m⌝ₚ(⌜t⌝ₛ, H', S', Q', G') ∧
    H ⊆ H' ∧ Q ⊆ Q' ∧ G ⊆ G'⟫
derive_free_closed ic_extend_m
theorem ic_extend_sat_l (hE : Extensional M) {d} (η : Env M d) (s t : Term d) :
    Formula.satisfies η (ic_extend_m s t) ↔ Ic_extend_d (s.eval η) (t.eval η) := by
  simp only [ic_extend_m, Ic_extend_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    Formula.satisfies_subset_iff, rd_quad_sat_l hE, Definitional.Term.eval_weaken]; rfl

theorem Ic_extend_d.read_l {s t H S Q G H' S' Q' G' : M.Domain} (h : Ic_extend_d s t)
    (hs : Rd_quad_d s H S Q G) (ht : Rd_quad_d t H' S' Q' G') :
    M.MemberSubset H H' ∧ M.MemberSubset Q Q' ∧ M.MemberSubset G G' := by
  obtain ⟨A, B, C, D, A', B', C', D', hp, hq, keep⟩ := h
  obtain ⟨rfl, rfl, rfl, rfl⟩ := hp.unique_l hs
  obtain ⟨rfl, rfl, rfl, rfl⟩ := hq.unique_l ht
  exact keep

theorem Ic_extend_d.trans_l {s t u : M.Domain} (h : Ic_extend_d s t) (g : Ic_extend_d t u) : Ic_extend_d s u := by
  obtain ⟨H, S, Q, G, H', S', Q', G', hs, ht, hh, hq, hg⟩ := h
  have g₀ := g
  obtain ⟨A, B, C, D, H'', S'', Q'', G'', hp, hu, _⟩ := g
  obtain ⟨hh', hq', hg'⟩ := g₀.read_l ht hu
  exact ⟨H, S, Q, G, H'', S'', Q'', G'', hs, hu,
    fun x hx => hh' x (hh x hx), fun x hx => hq' x (hq x hx), fun x hx => hg' x (hg x hx)⟩

private def ic_pick {A : Type u} (H Q G : A) : Fin 3 → A := Fin.cases H (Fin.cases Q (fun _ => G))
private def Ic_union_d (a : Fin 3) (f x : M.Domain) : Prop := ∃ i s H S Q G,
  Rd_entry_d i s f ∧ Rd_quad_d s H S Q G ∧ M.mem x (ic_pick H Q G a)
private def ic_union_m (a : Fin 3) {d} (f x : Term d) : Formula 1 d := set[d] ⟪
  ∃ i s H S Q G, ⌜rd_entry0_m⌝ₚ(i, s, ⌜f⌝ₛ) ∧ ⌜rd_quad_m⌝ₚ(s, H, S, Q, G) ∧
    ⌜(fun H Q G x => (Definitional.Formula.mem x (ic_pick H Q G a) : Formula 1 _))⌝ₚ(H, Q, G, ⌜x⌝ₛ)⟫
@[simp] private theorem ic_union_closed_l (a : Fin 3) {d} (f x : Term d)
    (hf : f.freeSupport = []) (hx : x.freeSupport = []) : (ic_union_m a f x).FreeClosed := by
  refine Fin.cases ?_ (Fin.cases ?_ (fun _ => ?_)) a <;>
    simp -implicitDefEqProofs [ic_union_m, ic_pick, Definitional.Formula.FreeClosed, hf, hx] <;> rfl
private theorem ic_union_sat_l (hE : Extensional M) (a : Fin 3) {d} (η : Env M d) (f x : Term d) :
    Formula.satisfies η (ic_union_m a f x) ↔ Ic_union_d a (f.eval η) (x.eval η) := by
  refine Fin.cases ?_ (Fin.cases ?_ (fun _ => ?_)) a <;>
    simp only [ic_union_m, Ic_union_d, ic_pick, Fin.cases_zero, Fin.cases_succ,
      Formula.satisfies_exists_iff, Formula.satisfies_conj_iff, Formula.satisfies_mem_iff,
      rd_entry0_sat_l hE, rd_quad_sat_l hE, Definitional.Term.eval_weaken] <;> rfl

variable (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem ic_sequence_union_l {ω T Q G E L D f : M.Domain} (hω : M.IsOmega ω)
    (original : It_diagram_d (kp_pair_l (ZF.modelsKP hZF)) ω ω T Q G) (fn : Fn0_d ω D f)
    (valid : ∀ i s, Rd_entry_d i s f → ∃ m H S Q' G', M.mem m ω ∧ M.mem i m ∧
      Rd_quad_d s H S Q' G' ∧ Ic_history_d hZF ω T Q G E L m H S Q' G')
    (chain : ∀ i j s t, M.SuccessorOf j i → Rd_entry_d i s f → Rd_entry_d j t f → Ic_extend_d s t) :
    ∃ H Q' G', Ic_history_d hZF ω T Q G E L ω H T Q' G' ∧
      ∀ i s H₀ S₀ Q₀ G₀, Rd_entry_d i s f → Rd_quad_d s H₀ S₀ Q₀ G₀ →
        M.MemberSubset H₀ H ∧ M.MemberSubset Q₀ Q' ∧ M.MemberSubset G₀ G' := by
  have ff := fn0_function_l (ZF.modelsKP hZF) fn
  have read {i s H S Q' G'} (hs : Rd_entry_d i s f) (hp : Rd_quad_d s H S Q' G') :
      ∃ m, M.mem m ω ∧ M.mem i m ∧ Ic_history_d hZF ω T Q G E L m H S Q' G' := by
    obtain ⟨m, A, B, C, D, hmω, hm, pack, hist⟩ := valid i s hs
    obtain ⟨e₁, e₂, e₃, e₄⟩ := pack.unique_l hp
    subst A B C D
    exact ⟨m, hmω, hm, hist⟩
  let η : Env M 0 := ⟨Fin.elim0, fun _ => f⟩
  let φ : BinarySchema 0 := { body := ic_extend_m (.bound 1) .newest }
  have sat s t : φ.denote η s t ↔ Ic_extend_d s t := ic_extend_sat_l hZF.1 ..
  have increasing := ZF.rel_chain_l I hZF φ η hω ff
    (fun _ _ _ _ _ _ h g => (sat _ _).mpr (((sat _ _).mp h).trans_l ((sat _ _).mp g)))
    (fun i j s t hij hs ht => (sat s t).mpr (chain i j s t hij hs ht))
  have self {i s} (hs : Rd_entry_d i s f) : Ic_extend_d s s := by
    obtain ⟨_, H, S, Q', G', _, _, hp, _⟩ := valid i s hs
    exact ⟨H, S, Q', G', H, S, Q', G', hp, hp, fun _ h => h, fun _ h => h, fun _ h => h⟩
  have merge {i j s t} (hs : Rd_entry_d i s f) (ht : Rd_entry_d j t f) :
      ∃ k v, Rd_entry_d k v f ∧ Ic_extend_d s v ∧ Ic_extend_d t v := by
    rcases (hω.isOrdinal (ZF.modelsKP hZF)).wellOrder.linear.compare i (fn.bound_l hs).1 j (fn.bound_l ht).1 with eq | lt | gt
    · have eq := hZF.1.eq_of_same_members i j eq
      subst j
      have eq := ff.1.2 i t s ht hs
      subst t
      exact ⟨i, s, hs, self hs, self hs⟩
    · exact ⟨j, t, ht, (sat s t).mp (increasing i j s t lt hs ht), self ht⟩
    · exact ⟨i, s, hs, self hs, (sat t s).mp (increasing j i t s gt ht hs)⟩
  have part {m H S Q' G'} (hist : Ic_history_d hZF ω T Q G E L m H S Q' G') (a : Fin 3) :
      M.IsSetFunction I (ic_pick H Q' G' a) :=
    Fin.cases hist.function (Fin.cases hist.diagram.model_function (fun _ => hist.diagram.map_function)) a
  have keep {s t H S Q' G' H' S' Q'' G''} (ext : Ic_extend_d s t)
      (hs : Rd_quad_d s H S Q' G') (ht : Rd_quad_d t H' S' Q'' G'') (a : Fin 3) :
      M.MemberSubset (ic_pick H Q' G' a) (ic_pick H' Q'' G'' a) := by
    obtain ⟨hh, hq, hg⟩ := ext.read_l hs ht
    exact Fin.cases hh (Fin.cases hq (fun _ => hg)) a
  -- 传递闭包只给本次分离提供集合界；它不限制复制模型的高度。
  obtain ⟨U, tu, hDU, _⟩ := ZF.tc_exists_l I hZF D
  have owned {i s H S Q' G'} (hs : Rd_entry_d i s f) (pack : Rd_quad_d s H S Q' G') (a : Fin 3) :
      M.mem (ic_pick H Q' G' a) U := by
    obtain ⟨p, hp, q, hq, hr⟩ := pack
    obtain ⟨hH, hqU⟩ := hr.mem_l M tu (tu D hDU s (fn.bound_l hs).2)
    have hpU := (hq.mem_l M tu hqU).2
    obtain ⟨hQ, hG⟩ := hp.mem_l M tu hpU
    exact Fin.cases hH (Fin.cases hQ (fun _ => hG)) a
  have collect (a : Fin 3) : ∃ B, ∀ x, M.mem x B ↔ Ic_union_d a f x := by
    let ψ : UnarySchema 1 := { body := ic_union_m a (.bound 1) .newest }
    let ρ : Env M 1 := ⟨fun _ => f, fun _ => f⟩
    obtain ⟨B, hb⟩ := ZF.separation_exists_d hZF ψ ρ U
    refine ⟨B, fun x => (hb x).trans ?_⟩
    change (M.mem x U ∧ ψ.denote ρ x) ↔ _
    rw [show ψ.denote ρ x ↔ Ic_union_d a f x from ic_union_sat_l hZF.1 a ..]
    exact ⟨And.right, fun h => ⟨by obtain ⟨i, s, H, S, Q', G', hs, hp, hx⟩ := h; exact tu _ (owned hs hp a) x hx, h⟩⟩
  have graphs (a : Fin 3) {B} (bs : ∀ x, M.mem x B ↔ Ic_union_d a f x) :
      M.IsSetFunction I B ∧ ∀ x y, Rd_entry_d x y B ↔ ∃ i s H S Q' G',
        Rd_entry_d i s f ∧ Rd_quad_d s H S Q' G' ∧ Rd_entry_d x y (ic_pick H Q' G' a) := by
    have entries x y : Rd_entry_d x y B ↔ ∃ i s H S Q' G',
        Rd_entry_d i s f ∧ Rd_quad_d s H S Q' G' ∧ Rd_entry_d x y (ic_pick H Q' G' a) := by
      refine ⟨fun ⟨p, pair, hp⟩ => ?_, fun ⟨i, s, H, S, Q', G', hs, pack, p, pair, hp⟩ => ?_⟩
      · obtain ⟨i, s, H, S, Q', G', hs, pack, hp⟩ := (bs p).mp hp
        exact ⟨i, s, H, S, Q', G', hs, pack, p, pair, hp⟩
      · exact ⟨p, pair, (bs p).mpr ⟨i, s, H, S, Q', G', hs, pack, hp⟩⟩
    refine ⟨⟨fun p hp => ?_, fun x y z hy hz => ?_⟩, entries⟩
    · obtain ⟨i, s, H, S, Q', G', hs, pack, hp⟩ := (bs p).mp hp
      obtain ⟨m, _, _, hist⟩ := read hs pack
      exact (part hist a).1 p hp
    · obtain ⟨i, s, H, S, Q', G', hs, pack, hy⟩ := (entries x y).mp hy
      obtain ⟨j, t, H', S', Q'', G'', ht, pack', hz⟩ := (entries x z).mp hz
      obtain ⟨k, v, hv, sv, tv⟩ := merge hs ht
      obtain ⟨m, A, B, C, D, _, _, vp, vh⟩ := valid k v hv
      obtain ⟨p, pair, hp⟩ := hy
      obtain ⟨q, qp, hq⟩ := hz
      exact (part vh a).2 x y z ⟨p, pair, keep sv pack vp a p hp⟩ ⟨q, qp, keep tv pack' vp a q hq⟩
  obtain ⟨H, hs⟩ := collect 0
  obtain ⟨Q', qs⟩ := collect 1
  obtain ⟨G', gs⟩ := collect 2
  obtain ⟨hf, he⟩ := graphs 0 hs
  obtain ⟨qf, qe⟩ := graphs 1 qs
  obtain ⟨gf, ge⟩ := graphs 2 gs
  have inside {i s H₀ S₀ Q₀ G₀} (h : Rd_entry_d i s f) (hp : Rd_quad_d s H₀ S₀ Q₀ G₀) :
      M.MemberSubset H₀ H ∧ M.MemberSubset Q₀ Q' ∧ M.MemberSubset G₀ G' :=
    ⟨fun x hx => (hs x).mpr ⟨i, s, H₀, S₀, Q₀, G₀, h, hp, hx⟩,
      fun x hx => (qs x).mpr ⟨i, s, H₀, S₀, Q₀, G₀, h, hp, hx⟩,
      fun x hx => (gs x).mpr ⟨i, s, H₀, S₀, Q₀, G₀, h, hp, hx⟩⟩
  have below {m j} (hmω : M.mem m ω) (hj : M.mem j m) : M.mem j ω := hω.transitive (ZF.modelsKP hZF) m hmω j hj
  have hdom : M.IsDomainOf I ω H := by
    intro i
    constructor
    · intro hi
      obtain ⟨s, _, hsi⟩ := fn.2.1 i hi
      obtain ⟨m, A, B, C, D, hmω, hm, pack, hist⟩ := valid i s hsi
      obtain ⟨r, hr⟩ := (hist.domain i).mp hm
      exact ⟨r, (he i r).mpr ⟨i, s, A, B, C, D, hsi, pack, hr⟩⟩
    · rintro ⟨r, hr⟩
      obtain ⟨j, s, A, B, C, D, hj, pack, hr⟩ := (he i r).mp hr
      obtain ⟨m, hmω, hm, hist⟩ := read hj pack
      exact below hmω ((hist.domain i).mpr ⟨r, hr⟩)
  have qdom : M.IsDomainOf I ω Q' := by
    intro i
    constructor
    · intro hi
      obtain ⟨s, _, hsi⟩ := fn.2.1 i hi
      obtain ⟨m, A, B, C, D, hmω, hm, pack, hist⟩ := valid i s hsi
      obtain ⟨r, hr⟩ := (hist.diagram.model_domain i).mp hm
      exact ⟨r, (qe i r).mpr ⟨i, s, A, B, C, D, hsi, pack, hr⟩⟩
    · rintro ⟨r, hr⟩
      obtain ⟨j, s, A, B, C, D, hj, pack, hr⟩ := (qe i r).mp hr
      obtain ⟨m, hmω, hm, hist⟩ := read hj pack
      exact below hmω ((hist.diagram.model_domain i).mpr ⟨r, hr⟩)
  have pair_mem {r i j A} (pair : KPair_d M r i j) (hr : Rd_entry_d i j A) : M.mem r A := by
    obtain ⟨q, hq, hqA⟩ := hr
    exact kpair_unique_l M hZF.1 hq pair ▸ hqA
  have gdom : M.IsDomainOf I T G' := by
    intro r
    constructor
    · intro hr
      obtain ⟨i, j, pair⟩ := original.order.relation r hr
      have hj := (original.order.bound i j ⟨r, pair, hr⟩).2
      obtain ⟨s, _, hjs⟩ := fn.2.1 j hj
      obtain ⟨m, A, B, C, D, hmω, hm, pack, hist⟩ := valid j s hjs
      obtain ⟨g, hg⟩ := (hist.diagram.map_domain r).mp (pair_mem pair ((hist.order i j).mpr ⟨⟨r, pair, hr⟩, hm⟩))
      exact ⟨g, (ge r g).mpr ⟨j, s, A, B, C, D, hjs, pack, hg⟩⟩
    · rintro ⟨g, hg⟩
      obtain ⟨j, s, A, B, C, D, hj, pack, hg⟩ := (ge r g).mp hg
      obtain ⟨m, _, _, hist⟩ := read hj pack
      obtain ⟨i, k, pair⟩ := hist.diagram.order.relation r ((hist.diagram.map_domain r).mpr ⟨g, hg⟩)
      exact pair_mem pair ((hist.order i k).mp ⟨r, pair, (hist.diagram.map_domain r).mpr ⟨g, hg⟩⟩).1
  have map_bound {i j g} (hg : It_map_d G' i j g) : Rd_entry_d i j T := by
    obtain ⟨r, pair, hr⟩ := hg
    exact ⟨r, pair, (gdom r).mpr ⟨g, hr⟩⟩
  have recover {A B C} (af : M.IsSetFunction I A) (bd : M.IsDomainOf I C B) (sub : M.MemberSubset B A)
      {i} (hi : M.mem i C) (x) : Rd_entry_d i x A ↔ Rd_entry_d i x B := by
    refine ⟨fun h => ?_, fun ⟨p, pair, hp⟩ => ⟨p, pair, sub p hp⟩⟩
    obtain ⟨y, hy⟩ := (bd i).mp hi
    obtain ⟨p, pair, hp⟩ := hy
    exact af.2 i y x ⟨p, pair, sub p hp⟩ h ▸ (show Rd_entry_d i y B from ⟨p, pair, hp⟩)
  -- 任一有限阶段都恰为三张并图在其旧定义域上的限制。
  have stage i (hi : M.mem i ω) : ∃ m A B C D, M.mem i m ∧ Ic_history_d hZF ω T Q G E L m A B C D ∧
      (∀ j, M.mem j m → ∀ r, Rd_entry_d j r H ↔ Rd_entry_d j r A) ∧
      (∀ j, M.mem j m → ∀ r, Rd_entry_d j r Q' ↔ Rd_entry_d j r C) ∧
      ∀ k j, M.mem j m → ∀ g, It_map_d G' k j g ↔ It_map_d D k j g := by
    obtain ⟨s, _, his⟩ := fn.2.1 i hi
    obtain ⟨m, A, B, C, D, hmω, hm, pack, hist⟩ := valid i s his
    obtain ⟨ah, cq, dg⟩ := inside his pack
    refine ⟨m, A, B, C, D, hm, hist, fun j hj r => recover hf hist.domain ah hj r,
      fun j hj r => recover qf hist.diagram.model_domain cq hj r, ?_⟩
    intro k j hj g
    refine ⟨fun hg => ?_, fun ⟨r, pair, hr⟩ => ⟨r, pair, (recover gf hist.diagram.map_domain dg
      ((hist.diagram.map_domain r).mpr ⟨g, hr⟩) g).mpr hr⟩⟩
    obtain ⟨r, pair, hr⟩ := hg
    exact ⟨r, pair, (recover gf hist.diagram.map_domain dg
      (pair_mem pair ((hist.order k j).mpr ⟨map_bound ⟨r, pair, hr⟩, hj⟩)) g).mp hr⟩
  have small {i j m} (mo : M.IsOrdinal m) (hm : M.mem j m) (hij : Rd_entry_d i j T) : M.mem i m :=
    (original.order.forward i j hij).elim (fun eq => eq.symm ▸ hm) (mo.transitive j hm i)
  have diagram : It_diagram_d (kp_pair_l (ZF.modelsKP hZF)) ω ω T Q' G' := by
    refine ⟨original.order, qf, qdom, ?_, gf, gdom, ?_, ?_, ?_⟩
    · intro i c hc
      obtain ⟨m, A, B, C, D, hm, hist, _, q, _⟩ := stage i ((qdom i).mpr ⟨c, hc⟩)
      exact hist.diagram.models i c ((q i hm c).mp hc)
    · intro i j g c X R d Y S hg hc hd mx my
      have hij := map_bound hg
      obtain ⟨m, A, B, C, D, hm, hist, _, q, maps⟩ := stage j (original.order.bound i j hij).2
      exact hist.diagram.elementary i j g c X R d Y S ((maps i j hm g).mp hg)
        ((q i (small hist.diagram.order.ordinal hm hij) c).mp hc) ((q j hm d).mp hd) mx my
    · intro i g hg x y hxy
      obtain ⟨m, A, B, C, D, hm, hist, _, _, maps⟩ := stage i (original.order.bound i i (map_bound hg)).1
      exact hist.diagram.identity i g ((maps i i hm g).mp hg) x y hxy
    · intro i j k f g h hf hg hh x y z hxy hyz
      have hjk := map_bound hg
      obtain ⟨m, A, B, C, D, hm, hist, _, _, maps⟩ := stage k (original.order.bound j k hjk).2
      exact hist.diagram.comp i j k f g h ((maps i j (small hist.diagram.order.ordinal hm hjk) f).mp hf)
        ((maps j k hm g).mp hg) ((maps i k hm h).mp hh) x y z hxy hyz
  have at_stage {i m A X P π z Z α} (h : ∀ j, M.mem j m → ∀ r, Rd_entry_d j r H ↔ Rd_entry_d j r A) (hi : M.mem i m) :
      Ic_at_d H i X P π z Z α ↔ Ic_at_d A i X P π z Z α :=
    exists_congr fun r => and_congr (h i hi r) Iff.rfl
  refine ⟨H, Q', G', ⟨diagram, fun i j => ⟨fun hij => ⟨hij, (original.order.bound i j hij).2⟩, And.left⟩,
    hf, hdom, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, fun _ _ _ _ _ _ hs hp => inside hs hp⟩
  · intro i r hr
    obtain ⟨m, A, B, C, D, hm, hist, h, q, _⟩ := stage i ((hdom i).mpr ⟨r, hr⟩)
    obtain ⟨c, X, P, π, z, Z, α, cell, hc, hz, row⟩ := hist.rows i r ((h i hm r).mp hr)
    exact ⟨c, X, P, π, z, Z, α, cell, hc, (q i hm z).mpr hz, row⟩
  · intro i j X A π z Z α Y B σ u U β ai aj hij
    obtain ⟨r, hr, _⟩ := aj
    obtain ⟨m, C, S, Q₀, G₀, hm, hist, h, _, _⟩ := stage j ((hdom j).mpr ⟨r, hr⟩)
    exact hist.past i j X A π z Z α Y B σ u U β ((at_stage h (hist.diagram.order.ordinal.transitive j hm i hij)).mp ai)
      ((at_stage h hm).mp ⟨r, hr, ‹Ic_cell_d r Y B σ u U β›⟩) hij
  · intro i j X A π z Z α Y B σ u U β g ai aj hg
    have hij := map_bound hg
    obtain ⟨m, C, S, Q₀, G₀, hm, hist, h, _, maps⟩ := stage j (original.order.bound i j hij).2
    exact hist.cuts i j X A π z Z α Y B σ u U β g ((at_stage h (small hist.diagram.order.ordinal hm hij)).mp ai)
      ((at_stage h hm).mp aj) ((maps i j hm g).mp hg)
  · intro i j X A π z Z α Y B σ u U β g k ai aj hg hk
    have hij := map_bound hk
    obtain ⟨m, C, S, Q₀, G₀, hm, hist, h, _, maps⟩ := stage j (original.order.bound i j hij).2
    exact hist.squares i j X A π z Z α Y B σ u U β g k
      ((at_stage h (small hist.diagram.order.ordinal hm hij)).mp ai) ((at_stage h hm).mp aj)
      hg ((maps i j hm k).mp hk)
  · intro i j k N B σ u U β X A π z Z α P C τ v V γ p κ ρ F g succ pred ai ak aj hp pay hg
    obtain ⟨m, A₀, S, Q₀, G₀, hm, hist, h, _, maps⟩ := stage j (original.order.bound k j (map_bound hg)).2
    exact hist.steps i j k N B σ u U β X A π z Z α P C τ v V γ p κ ρ F g succ pred
      ((at_stage h (hist.diagram.order.ordinal.transitive j hm i succ.predecessor_mem)).mp ai)
      ((at_stage h (hist.diagram.order.ordinal.transitive j hm k pred.1)).mp ak) ((at_stage h hm).mp aj)
      hp pay ((maps k j hm g).mp hg)
  · intro i j p succ hj hp empty
    obtain ⟨m, A, B, C, D, hm, hist, h, _, maps⟩ := stage j hj
    have hi := hist.diagram.order.ordinal.transitive j hm i succ.predecessor_mem
    obtain ⟨same, ident⟩ := hist.pads i j p succ hm hp empty
    exact ⟨fun r => (h i hi r).trans ((same r).trans (h j hm r).symm),
      fun f x y hf => ident f x y ((maps i j hm f).mp hf)⟩

  · intro i j r X A π z Z α Y B σ u U β ρ ψ a b ai aj succ hr hρ hψ ha hb hij
    obtain ⟨m, C, S, Q₀, G₀, hm, hist, h, _, _⟩ := stage r hr
    have hj := hist.diagram.order.ordinal.transitive r hm j succ.predecessor_mem
    have hi := hist.diagram.order.ordinal.transitive j hj i hij
    exact hist.increasing i j r X A π z Z α Y B σ u U β ρ ψ a b
      ((at_stage h hi).mp ai) ((at_stage h hj).mp aj) succ hm hρ hψ ha hb hij

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 全部内部有限复制历史的实际 ω 序列

初值为给定嵌入。历史界、有限幂复制交换和工作施加条件均从实际历史读取。
同一原目标的下一复制行及相邻共同层给出活动延伸，类依赖选择收集全部内部有限历史。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}
section
variable (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

def Ic_state_d (ω T Q G E L i s : M.Domain) : Prop := ∃ m H S Q' G',
  M.SuccessorOf m i ∧ Rd_quad_d s H S Q' G' ∧ Ic_history_d hZF ω T Q G E L m H S Q' G'
def ic_state_m {d} (ω T Q G E L i s : Term d) : Formula 1 d := set[d] ⟪
  ∃ m H S Q' G', ⌜KP.succ0_m⌝ₚ(m, ⌜i⌝ₛ) ∧ ⌜rd_quad_m⌝ₚ(⌜s⌝ₛ, H, S, Q', G') ∧
    ⌜ic_history_m⌝ₚ(⌜ω⌝ₛ, ⌜T⌝ₛ, ⌜Q⌝ₛ, ⌜G⌝ₛ, ⌜E⌝ₛ, ⌜L⌝ₛ, m, H, S, Q', G')⟫
derive_free_closed ic_state_m
theorem ic_state_sat_l {d} (η : Env M d) (ω T Q G E L i s : Term d) :
    Formula.satisfies η (ic_state_m ω T Q G E L i s) ↔ Ic_state_d hZF
      (ω.eval η) (T.eval η) (Q.eval η) (G.eval η) (E.eval η) (L.eval η) (i.eval η) (s.eval η) := by
  simp only [ic_state_m, Ic_state_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    KP.succ0_sat_l hZF.1, rd_quad_sat_l hZF.1, ic_history_sat_l hZF, Definitional.Term.eval_weaken]; rfl

end

variable (hZFC : M.Models ZFC)
local notation "hZF" => ZFC.models_zf_l hZFC
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

/-- 从指定首行收集复制历史，活动步始终使用给定原树的同一个商系统和后继。 -/
theorem Ic_row_d.sequence_l {ω c X A π z Z α o T Q G E L : M.Domain}
    (nice : It_pnice_d hZF ω c ω T Q G E L) (row : Ic_row_d hZF ω c X A π z Z α) (ho : ∀ x, ¬ M.mem x o) :
    ∃ D f s₀ H₀ S₀ Q₀ G₀, Fn0_d ω D f ∧ Rd_entry_d o s₀ f ∧ Rd_quad_d s₀ H₀ S₀ Q₀ G₀ ∧
      Ic_at_d H₀ o X A π z Z α ∧ (∀ i s, Rd_entry_d i s f → Ic_state_d hZF ω T Q G E L i s) ∧
      ∀ i j s t, M.SuccessorOf j i → Rd_entry_d i s f → Rd_entry_d j t f → Ic_extend_d s t := by
  obtain ⟨m, H, S, Q', G', hm, hist, first⟩ := row.start_l hZF nice.tree.diagram ho (nice.tree.root o ho)
  obtain ⟨s₀, pack⟩ := rd_quad_exists_l (ZF.modelsKP hZF) H S Q' G'
  let η : Env M 6 := ⟨Fin.cases L (Fin.cases E (Fin.cases G (Fin.cases Q (Fin.cases T (fun _ => ω))))), fun _ => ω⟩
  let V : BinarySchema 6 := { body := ic_state_m (.bound 7) (.bound 6) (.bound 5) (.bound 4) (.bound 3) (.bound 2) (.bound 1) .newest }
  let φ : UnarySchema 8 := { body := ic_extend_m (.bound 1) .newest }
  have valid i s : V.denote η i s ↔ Ic_state_d hZF ω T Q G E L i s := ic_state_sat_l hZF ..
  have step i s t : φ.denote ((η.push i).push s) t ↔ Ic_extend_d s t := ic_extend_sat_l hZF.1 ..
  obtain ⟨D, f, hf, hs, all, next⟩ := ZFC.class_indexed_choice_l I hZFC V φ η nice.tree.omega ho
    ((valid o s₀).mpr ⟨m, H, S, Q', G', hm, pack, hist⟩) (by
      intro i j s hi hij hv
      obtain ⟨m, H, S, Q', G', hm, pack, hist⟩ := (valid i s).mp hv
      have eq := hm.eq hZF.1 hij
      subst m
      -- 固定树的原商系统、历史界与相邻共同层共同生产下一份完整历史。
      obtain ⟨l, J, S', Q'', G'', hl, hist', rows, codes, maps⟩ :
          ∃ l J S' Q'' G'', M.SuccessorOf l j ∧ Ic_history_d hZF ω T Q G E L l J S' Q'' G'' ∧
            M.MemberSubset H J ∧ M.MemberSubset Q' Q'' ∧ M.MemberSubset G' G'' := by
        classical
        by_cases active : ∃ ρ, Rd_entry_d i ρ L
        · obtain ⟨ρ,hρ⟩ := active
          obtain ⟨b,N,B,σ,u,U,β,top,qc,_,row⟩ := hist.at_l hZF hij.predecessor_mem
          have own := row
          obtain ⟨Rn,_,_,_,_,_,mn,_,_,_,_,_,_,_,_⟩ := row
          obtain ⟨χ,bound,above⟩ := hist.fixed_bound_l hZF nice top hi qc mn hρ
          obtain ⟨j₀,succ,hjω⟩ := nice.tree.omega.1.2 i hi
          have eq := succ.eq hZF.1 hij
          subst j₀
          obtain ⟨k,c₁,d,e,f,p,κ,ρ₀,F,X,R,Y,S,pred,qc₁,qd,qe,edge,event,pay,mx,xt,my,raw,strong,card,level⟩ :=
            nice.step_l hZF hjω hij ⟨ρ,hρ⟩
          have eq := nice.tree.diagram.model_function.2 i c₁ b qc₁ qc
          subst c₁
          obtain ⟨eqX,eqR⟩ := smdl_unique_l I mx.1 mn
          subst X R
          have eq := nice.function.2 i ρ₀ ρ level hρ
          subst ρ₀
          obtain ⟨d₀,Y₀,A₀,π₀,z₀,Z₀,α₀,old,qd₀,_,parentRow⟩ := hist.at_l hZF pred.1
          have eq := nice.tree.diagram.model_function.2 k d₀ d qd₀ qd
          subst d₀
          have data := parentRow
          obtain ⟨S₀,_,_,_,_,_,my₀,_,_,_,_,_,_,_,_⟩ := data
          obtain ⟨eqY,eqS⟩ := smdl_unique_l I my₀ my
          subst Y₀ S₀
          have before : k = i ∨ M.mem k i := ((hij k).mp pred.1).elim Or.inr
            (fun eq => Or.inl (hZF.1.eq_of_same_members k i eq))
          obtain ⟨maps,κ',hκπ,hκσ,compatible⟩ :=
            hist.fixed_read_l hZF nice old top hi before qd qc event pay raw
          obtain ⟨Y',S',parent,yt⟩ := nice.active_prefix_l hZF hi hρ k d before qd
          obtain ⟨eqY,eqS⟩ := smdl_unique_l I parent.1 my
          subst Y' S'
          obtain ⟨P,Rp,N',v,C,γ,j',τ,ρ',F',mp,next,hρσ,hFσ,hαγ,hAC,big,commute,wf,ready,quality,work,factor⟩ :=
            parentRow.fixed_step_l hZFC own parent yt mx xt pay raw strong card maps hκπ hκσ compatible
          obtain ⟨D,Td,ed,g,inv,jn,kn,Kd,aC,Sc,md,dt,wc,bij,hg,bi,inverse,back,mc,hkn,
              normRow,conjugate,comp,ultra,successor,base,hρD,hρC,fixed,endq,subsets⟩ :=
            factor.support_l hZFC parentRow own next parent yt mx xt pay raw card maps
              hκπ hκσ hρσ hFσ compatible hAC mp wf commute
          obtain ⟨loc,agree,Ko,Kp,_,_,_,_,_,_,_,_,_,_,owner,source,_⟩ :=
            raw.row_data_l hZF own parentRow mx xt parent yt pay
          have reverse : Ea_agree_d ω κ Y N := fun n D A hn space sub => (agree n D A hn space sub).symm
          obtain ⟨Ko',Kd',ownerL,normL,W,hW,rank,levelD,sizes,exactness⟩ :=
            loc.fixed_rank_l hZFC source own normRow mx xt md reverse strong card successor hρD
          have hlim := card.limit_l (ZF.modelsKP hZF) xt (ownerL.algebra_l (ZF.modelsKP hZF)).pair
          have data := next
          obtain ⟨_,_,_,_,_,_,_,_,_,cutC,_,_,_,_,_⟩ := data
          obtain ⟨l₀,V₀,t₀,hl,hV,graph,adjacent⟩ :=
            own.collapse_agree_l hZF ownerL normL mx md mp hg bij mc cutC.transitive hkn conjugate
              hW rank levelD hlim exactness hρσ endq fixed subsets
          obtain ⟨l,J,S',Q'',G'',hl,history,rows,codes,arrows,_,_⟩ :=
            hist.active_push_l hZF nice.tree hi hij pred qd qc qe edge event pay hρ nice.function
              top old my mn mp bound above next hκσ hρσ hFσ hAC big commute compatible quality adjacent
          exact ⟨l,J,S',Q'',G'',hl,history,rows,codes,arrows⟩
        · obtain ⟨j₀, hj₀, hjω⟩ := nice.tree.omega.1.2 i hi
          have eq := hj₀.eq hZF.1 hij
          subst j₀
          obtain ⟨l, J, S', Q'', G'', hl, next, rows, codes, maps, _⟩ :=
            hist.pad_extend_l hZF nice.tree nice.levels hij hjω (fun ρ hρ => active ⟨ρ, hρ⟩)
          exact ⟨l, J, S', Q'', G'', hl, next, rows, codes, maps⟩
      obtain ⟨t, pack'⟩ := rd_quad_exists_l (ZF.modelsKP hZF) J S' Q'' G''
      exact ⟨t, (valid j t).mpr ⟨l, J, S', Q'', G'', hl, pack', hist'⟩,
        (step i s t).mpr ⟨H, S, Q', G', J, S', Q'', G'', pack, pack', rows, codes, maps⟩⟩)
  exact ⟨D, f, s₀, H, S, Q', G', fn0_of_function_l (ZF.modelsKP hZF) hf, hs, pack, first,
    fun i s hs => (valid i s).mp (all i s hs), fun i j s t hij hs ht => (step i s t).mp (next i j s t hij hs ht)⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 原关系树的实际复制性质

支撑列来自原操作载荷。每个给定根嵌入都延长成同一原树的完整工作历史；
nice 树和 demanding 运行分别有实际构造。返回论证随后使用其自行构造的正规根行。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

def It_copyable_d (ω c T Q G E : M.Domain) : Prop := ∃ L, M.IsSetFunction I L ∧
  (∀ i ρ, Rd_entry_d i ρ L ↔ ∃ p κ F, Rd_entry_d i p E ∧ It_payload_d p κ ρ F) ∧
  ∀ o X A π z Z α, (∀ x, ¬ M.mem x o) → Ic_row_d hZF ω c X A π z Z α →
    ∃ H Q' G', Ic_history_d hZF ω T Q G E L ω H T Q' G' ∧ Ic_at_d H o X A π z Z α

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 有限历史递推得到完整 nice 复制树 -/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

/-- 给定首行自动复制整棵 nice 树，同时返回全部工作模型和原根嵌入。 -/
theorem Ic_row_d.copy_l (hZFC : M.Models ZFC) {ω c X A π z Z α o T Q G E L : M.Domain}
    (nice : It_pnice_d (ZFC.models_zf_l hZFC) ω c ω T Q G E L)
    (row : Ic_row_d (ZFC.models_zf_l hZFC) ω c X A π z Z α) (ho : ∀ x, ¬ M.mem x o) :
    ∃ H Q' G' E' L', Ic_history_d (ZFC.models_zf_l hZFC) ω T Q G E L ω H T Q' G' ∧
      It_pnice_d (ZFC.models_zf_l hZFC) ω z ω T Q' G' E' L' ∧ Ic_at_d H o X A π z Z α ∧
      ∀ i p, Rd_entry_d i p E' ↔ Ic_operation_d H E i p := by
  let hZF := ZFC.models_zf_l hZFC
  obtain ⟨D, f, s₀, H₀, S₀, Q₀, G₀, fn, first, pack, start, valid, chain⟩ := row.sequence_l hZFC nice ho
  obtain ⟨H, Q', G', hist, kept⟩ := ic_sequence_union_l hZF nice.tree.omega nice.tree.diagram fn (by
    intro i s hs
    obtain ⟨m,H,S,Q,G,succ,pack,hist⟩ := valid i s hs
    obtain ⟨j,sj,hj⟩ := nice.tree.omega.1.2 i (fn.bound_l hs).1
    exact ⟨m,H,S,Q,G,sj.eq hZF.1 succ ▸ hj,succ.predecessor_mem,pack,hist⟩) chain
  obtain ⟨r, ⟨p, pair, hp⟩, cell⟩ := start
  have first : Ic_at_d H o X A π z Z α := ⟨r, ⟨p, pair, (kept o s₀ H₀ S₀ Q₀ G₀ first pack).1 p hp⟩, cell⟩
  obtain ⟨E', L', copied, moves⟩ := hist.nice_l hZF nice.tree nice.levels ho first
  exact ⟨H, Q', G', E', L', hist, copied, first, moves⟩

/-- nice 树的已实现复制构造给出一般原树复制性质。 -/
theorem It_pnice_d.copyable_l (hZFC : M.Models ZFC) {ω c T Q G E L : M.Domain}
    (nice : It_pnice_d (ZFC.models_zf_l hZFC) ω c ω T Q G E L) :
    It_copyable_d (ZFC.models_zf_l hZFC) ω c T Q G E := by
  refine ⟨L,nice.function,nice.levels,?_⟩
  intro o X A π z Z α empty row
  obtain ⟨H,Q',G',_,_,hist,_,first,_⟩ := row.copy_l hZFC nice empty
  exact ⟨H,Q',G',hist,first⟩

end YesMetaZFC.SetTheory.LargeCardinal
