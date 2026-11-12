import YesMetaZFC.SetTheory.LargeCardinal.Extender.RawCoherence
import YesMetaZFC.Model.SetTheory.Relations.Collapse
import YesMetaZFC.Model.SetTheory.Reflection.ZfcTransfer
import YesMetaZFC.SetTheory.LargeCardinal.Game.RawCritical
import YesMetaZFC.SetTheory.CumulativeRelativeAlgebra
import YesMetaZFC.SetTheory.Rank
import YesMetaZFC.SetTheory.LargeCardinal.Iteration.CriticalBound
import YesMetaZFC.SetTheory.LargeCardinal.Game.RawArchiveSequence
import YesMetaZFC.SetTheory.LargeCardinal.Iteration.BranchTail
import YesMetaZFC.SetTheory.LargeCardinal.Game.RawBranchProjection
import YesMetaZFC.SetTheory.LargeCardinal.Iteration.Padding
import YesMetaZFC.SetTheory.LargeCardinal.Game.ShiftedProjection
import YesMetaZFC.SetTheory.Descriptive.Game.GameStrategyProjection
import YesMetaZFC.SetTheory.LargeCardinal.Game.RawTurnStrategy
import YesMetaZFC.Model.SetTheory.Embedding.PredicateTrace

/-! # 实际传递根的原生自然数及完整数字图

同一根中的自然数对象先由隶属绝对性识别，再限制实际恒等图。
该构造同时服务原游戏入口与同一控制表的规范化入口。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal Descriptive
universe u
variable {M : Structure.{u}}

/-- 原生 ω 的隶属读出和完整数字图共用给定的同一个根。 -/
theorem tg_numbers_mem_l (hZF : M.Models ZF)
    {Ω c X R : M.Domain} (hΩ : M.IsOmega Ω)
    (certificate : Zc_model_d (kp_pair_l (ZF.modelsKP hZF)) Ω c X R)
    (source : Smem_d (kp_pair_l (ZF.modelsKP hZF)) c X R) (trans : M.TransitiveSet X)
    (w : (smdl_structure_l (kp_pair_l (ZF.modelsKP hZF)) (R := R) certificate.model.2.1).Domain)
    (hw : (smdl_structure_l (kp_pair_l (ZF.modelsKP hZF)) (R := R) certificate.model.2.1).IsOmega w) :
    w.val = Ω ∧ ∃ z, Rr_layer_d (kp_pair_l (ZF.modelsKP hZF)) Ω X R w.val z := by
  let I := kp_pair_l (ZF.modelsKP hZF)
  let nx : Nonempty {x // M.mem x X} := ⟨w⟩
  let ρ : Env (rt_model_l X nx) 1 := ⟨fun _ => w,fun _ => w⟩
  have ground := certificate.membership_l I hZF hΩ source nx
  have localω : (rt_model_l X nx).IsOmega w :=
    (Formula.satisfies_isOmega_iff ρ .newest).mp
      ((smem_formula_l I source nx (Formula.isOmega .newest) ρ).mpr
        ((Formula.satisfies_isOmega_iff ..).mpr hw))
  have actual := fs_omega_relative_l hZF trans nx (ZFC.models_zf_l ground) w localω
  have eq : w.val = Ω := hZF.1.eq_of_same_members w.val Ω
    (fun x => ⟨actual.2 Ω hΩ.1 x,hΩ.2 w.val actual.1 x⟩)
  obtain ⟨z,layer,_⟩ := rr_layer_mem_l I hZF source trans w.property
    (actual.transitive (ZF.modelsKP hZF))
  exact ⟨eq,z,Eq.mp (congrArg (fun a => Rr_layer_d I a X R w.val z) eq) layer⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 任意原根的实际规范呈示

整个根若良基便作同一次 Mostowski 坍塌；若非良基则保留原根及恒等图。
目标只约定在良基时具有传递隶属呈示，不要求任意原模型本身规范。
两支都保存原模型码、目标码、完整同构及逆图，供同一次控制搬运消费。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

/-- 只规范整个良基根；非良基根仍保留它的真实关系。 -/
def Zc_normal_d (I : kpair_convention_l.Interpretation M) (c X R : M.Domain) : Prop :=
  Wf_rel_d X R → Smem_d I c X R ∧ M.TransitiveSet X

end YesMetaZFC.SetTheory.LargeCardinal

namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel LargeCardinal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

/-- 任意实际 ZFC 根自动选择所需呈示，两支都有完整可见的集合图实例。 -/
theorem Zc_model_d.normalize_l {ω c X R : M.Domain} (hw : M.IsOmega ω)
    (source : Zc_model_d I ω c X R) :
    ∃ d N S τ inv, ∃ _ : Zc_model_d I ω d N S,
      Zc_normal_d I d N S ∧ M.IsSetBijectionFromTo I τ X N ∧ Smap_d I ω c d X N τ ∧
      M.IsSetBijectionFromTo I inv N X ∧
      (∀ x y, Rd_entry_d y x inv ↔ Rd_entry_d x y τ) ∧ Smap_d I ω d c N X inv ∧
      ((Wf_rel_d X R ∧ Wc_graph_d X R τ ∧ Smem_d I d N S ∧ M.TransitiveSet N) ∨
        (¬ Wf_rel_d X R ∧ d = c ∧ N = X ∧ S = R ∧
          ∀ x y, Rd_entry_d x y τ ↔ M.mem x X ∧ x = y)) := by
  classical
  by_cases well : Wf_rel_d X R
  · obtain ⟨N,τ,inv,d,S,trans,collapse,bij,model,map,back,inverse,reverse⟩ :=
      wc_smaps_l hZF hw source.model well source.ext
    have target := source.map_l hZF hw model.1 map
    exact ⟨d,N,S,τ,inv,target,fun _ => ⟨model,trans⟩,bij,map,back,inverse,reverse,
      Or.inl ⟨well,collapse,model,trans⟩⟩
  · obtain ⟨τ,map,identity⟩ := smap_identity_l I hZF (c := c) (X := X) hw
    have bij : M.IsSetBijectionFromTo I τ X X :=
      ⟨map.1,fun y hy => ⟨y,hy,(identity y y).mpr ⟨hy,rfl⟩⟩⟩
    have inverse x y : Rd_entry_d y x τ ↔ Rd_entry_d x y τ := by
      constructor
      · intro h
        obtain ⟨hy,eq⟩ := (identity y x).mp h
        subst x
        exact (identity y y).mpr ⟨hy,rfl⟩
      · intro h
        obtain ⟨hx,eq⟩ := (identity x y).mp h
        subst y
        exact (identity x x).mpr ⟨hx,rfl⟩
    exact ⟨c,X,R,τ,τ,source,fun h => (well h).elim,bij,map,bij,inverse,map,
      Or.inr ⟨well,rfl,rfl,rfl,identity⟩⟩

end YesMetaZFC.SetTheory.Internal

/-! ## 实际传递隶属根的字母载体与严格秩界

同一相对累积历史只向背景层级作单向比较。传递载体内部的 Vγ
可以缺少背景子集；但它的全部成员仍属于背景 Vγ，这已足以读出
原字母对象的精确背景秩严格小于 γ。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

/-- 相对幂集历史的每个成员都进入对应背景层；不主张反向包含。 -/
private theorem tg_vr_upper_l {Z α V U : M.Domain} (trans : M.TransitiveSet Z)
    (member : M.mem V Z) (relative : Vr_d Z α V) (rank : V_d I α U) : M.MemberSubset V U := by
  obtain ⟨B,F,hB,_,cert⟩ := relative
  have ordinal := (cert V member).1
  have fn := (cert V member).2.1
  have step β W (ord : M.IsOrdinal β) (hW : M.mem W Z)
      (read : ∀ x, M.mem x Z → Vc_step_d β B F W x)
      (prev : ∀ δ, M.mem δ β → ∀ H, Rd_entry_d δ H F →
        ∀ K, V_d I δ K → M.MemberSubset H K) :
      ∀ K, V_d I β K → M.MemberSubset W K := by
    intro K hK x hx
    obtain ⟨δ,hδ,H,_,point,sub⟩ := (read x (trans W hW x hx)).mp hx
    obtain ⟨Q,hQ⟩ := ZF.v_exists_l I hZF (ord.mem hδ)
    exact (ZF.v_unfold_l I hZF hK x).mpr
      ⟨δ,Q,hδ,hQ,fun y hy => prev δ hδ H point Q hQ y (sub y hy)⟩
  let ρ : Env M 2 := ⟨Fin.cases α (fun _ => F),fun _ => α⟩
  let φ : UnarySchema 2 := { body := set[3] ⟪⌜(.newest : Term 3)⌝ₛ ∈ ⌜(.bound 1 : Term 3)⌝ₛ →
    ∀ H, ⌜rd_entry0_m⌝ₚ(⌜(.newest : Term 3)⌝ₛ,H,⌜(.bound 2 : Term 3)⌝ₛ) →
      ∀ K, ⌜(v_m kpair_convention_l)⌝ₚ(⌜(.newest : Term 3)⌝ₛ,K) → H ⊆ K⟫ }
  have sat β : φ.denote ρ β ↔ M.mem β α → ∀ H, Rd_entry_d β H F →
      ∀ K, V_d I β K → M.MemberSubset H K := by
    simp only [φ,UnarySchema.denote,Formula.satisfies_imp_iff,Formula.satisfies_mem_iff,
      Formula.satisfies_forall_iff,rd_entry0_sat_l hZF.1,v_sat_l I hZF.1,
      Formula.satisfies_subset_iff,Definitional.Term.eval_weaken]
    rfl
  have all β (hβ : M.mem β α) : ∀ H, Rd_entry_d β H F → ∀ K, V_d I β K → M.MemberSubset H K := by
    apply (sat β).mp (ZF.mem_ind_l M hZF I φ ρ ?_ β) hβ
    intro β ih
    apply (sat β).mpr
    intro hβ H point
    exact step β H (ordinal.mem hβ) (trans B hB H (fn.bound_l point).2)
      (fun x hx => (cert x hx).2.2.1 β hβ H (fn.bound_l point).2 point)
      (fun δ hδ H point => (sat δ).mp (ih δ hδ) (ordinal.transitive β hβ δ hδ) H point)
  exact step α V ordinal member (fun x hx => (cert x hx).2.2.2) all U rank

/-- 原生字母的完整成员载体在传递隶属根中就是原字母对象。 -/
theorem Tg_root_cut_d.letters_eq_l (hKP : M.Models KP) {c X R w γ B a D A : M.Domain}
    (cut : Tg_root_cut_d (kp_pair_l hKP) c X R w γ B a D A)
    (source : Smem_d (kp_pair_l hKP) c X R) (trans : M.TransitiveSet X) : A = a := by
  have ha := ((source.2 a B).mp cut.alphabet).1
  apply hKP.1.eq_of_same_members A a
  intro x
  apply (cut.letters x).trans
  exact ⟨fun hx => ((source.2 x a).mp hx.2).2.2,
    fun hx => ⟨trans a ha x hx,(source.2 x a).mpr ⟨trans a ha x hx,ha,hx⟩⟩⟩

/-- 实际切片自产精确背景秩；与所有原操作的 γ≤κ 结合即为论文的严格临界界。 -/
theorem Tg_root_cut_d.canonical_l {c X R w γ B a D A : M.Domain}
    (cut : Tg_root_cut_d I c X R w γ B a D A)
    (source : Smem_d I c X R) (trans : M.TransitiveSet X) :
    A = a ∧ M.IsOrdinal γ ∧ ∃ ρ, Rk_d I a ρ ∧ M.mem ρ γ := by
  have relative := (rr_rank_mem_l I (ZF.modelsKP hZF) source trans cut.rank.1 cut.rank.2.1).mp cut.rank
  have ordinal := relative.ordinal_l cut.rank.2.1
  obtain ⟨U,rank⟩ := ZF.v_exists_l I hZF ordinal
  have haU := tg_vr_upper_l hZF trans cut.rank.2.1 relative rank a ((source.2 a B).mp cut.alphabet).2.2
  obtain ⟨ρ,rk⟩ := ZF.rk_exists_l I hZF a
  exact ⟨cut.letters_eq_l (ZF.modelsKP hZF) source trans,ordinal,ρ,rk,(ZF.rk_mem_l I hZF rk rank).mp haU⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 真实隶属根中的临界点下界读出

只有给定根确有传递隶属呈示时，才把根内 γ₀ 读为背景的传递对象。
同一根切片限制到它的全部成员后给出完整序数层解释；原后继的构造
仍不要求这个呈示，也不要求任何后继模型传递。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

/-- 从实际源秩直接回收 γ₀ 的全部成员，并限制同一切片图。 -/
theorem Tg_root_slice_d.mem_layer_l
    {c X₀ R₀ γ₀ B₀ D₀ C₀ X R C q γ V t : M.Domain}
    (slice : Tg_root_slice_d I X₀ R₀ γ₀ D₀ C₀ X R C q γ V t)
    (source : Smem_d I c X₀ R₀) (trans : M.TransitiveSet X₀)
    (hN : (smdl_structure_l I (R := R₀) source.1.2.1).Models KP)
    (rank : Rr_rank_d I X₀ R₀ γ₀ B₀)
    (carrier : ∀ x, M.mem x D₀ ↔ M.mem x X₀ ∧ Rd_entry_d x B₀ R₀) :
    ∃ s, Rr_layer_d I γ₀ X R γ s ∧ M.IsRestrictionOf I s t γ₀ := by
  let N := smdl_structure_l I (R := R₀) source.1.2.1
  let gn : N.Domain := ⟨γ₀,rank.1⟩
  let Bn : N.Domain := ⟨B₀,rank.2.1⟩
  have native := (rr_rank_native_l I source.1.2.1 hN gn Bn).mp rank
  have ordinal := v_ordinal_l (kp_pair_l hN) native
  have member x (hx : M.mem x γ₀) : M.mem x X₀ := trans γ₀ rank.1 x hx
  have point x (hx : M.mem x γ₀) : Rd_entry_d x γ₀ R₀ :=
    (source.2 x γ₀).mpr ⟨member x hx,rank.1,hx⟩
  have baseTrans : M.TransitiveSet γ₀ := by
    intro x hx y hy
    have hyX := trans x (member x hx) y hy
    exact ((source.2 y γ₀).mp (ordinal.transitive ⟨x,member x hx⟩ (point x hx)
      ⟨y,hyX⟩ ((source.2 y x).mpr ⟨hyX,member x hx,hy⟩))).2.2
  have inside x (hx : M.mem x γ₀) : M.mem x D₀ := (carrier x).mpr
    ⟨member x hx,KP.v_ordinal_subset_l hN native ⟨x,member x hx⟩ (point x hx)⟩
  obtain ⟨s,rest⟩ := ZF.exists_restriction hZF I t γ₀
  refine ⟨s,⟨baseTrans,slice.rank.1,
    ⟨rest.isSetFunctionFromTo slice.injection.1 inside,fun x y z hx hy =>
      slice.injection.2 x y z ((rest.2 x z).mp hx).2 ((rest.2 y z).mp hy).2⟩,?_,?_⟩,rest⟩
  · intro y
    constructor
    · intro hy
      obtain ⟨a,_,ha,ay⟩ := (slice.endpoint.2.2 y).mp hy
      have haγ := ((source.2 a γ₀).mp ha).2.2
      exact ⟨a,haγ,(rest.2 a y).mpr ⟨haγ,ay⟩⟩
    · rintro ⟨a,ha,ay⟩
      exact (slice.endpoint.2.2 y).mpr ⟨a,member a ha,point a ha,((rest.2 a y).mp ay).2⟩
  · intro x z hx y
    obtain ⟨hxγ,xz⟩ := (rest.2 x z).mp hx
    constructor
    · intro hy
      obtain ⟨a,ax,ay⟩ := (slice.predecessors x z xz y).mp hy
      have ha := ((source.2 a x).mp ax).2.2
      exact ⟨a,ha,(rest.2 a y).mpr ⟨baseTrans x hxγ a ha,ay⟩⟩
    · rintro ⟨a,ha,ay⟩
      have haγ := baseTrans x hxγ a ha
      exact (slice.predecessors x z xz y).mpr
        ⟨a,(source.2 a x).mpr ⟨member a haγ,member x hxγ,ha⟩,((rest.2 a y).mp ay).2⟩

/-- 同一原操作列在真实隶属根实例中给出通常的背景临界点界。 -/
theorem Tg_raw_critical_d.mem_l
    {c X₀ R₀ γ₀ B₀ D₀ C₀ o Q G E : M.Domain}
    (h : Tg_raw_critical_d I X₀ R₀ γ₀ D₀ C₀ o Q G E)
    (source : Smem_d I c X₀ R₀) (trans : M.TransitiveSet X₀)
    (hN : (smdl_structure_l I (R := R₀) source.1.2.1).Models KP)
    (rank : Rr_rank_d I X₀ R₀ γ₀ B₀)
    (carrier : ∀ x, M.mem x D₀ ↔ M.mem x X₀ ∧ Rd_entry_d x B₀ R₀) :
    It_critical_bound_d I γ₀ Q E := by
  intro i p κ L F entry payload
  obtain ⟨d,X,R,C,q,γ,V,t,node,model,_,slice,lower⟩ := h i p κ L F entry payload
  obtain ⟨s,layer,_⟩ := slice.mem_layer_l hZF source trans hN rank carrier
  exact ⟨d,X,R,node,model,γ,s,layer,lower⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 传递隶属根切片的完整成员载体 -/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

/-- 同一切片图解释原载体的实际成员；不另选低层图。 -/
theorem Tg_root_slice_d.mem_carrier_l
    {c X₀ R₀ w₀ γ₀ B₀ A₀ D₀ A C₀ X R C p γ V t : M.Domain}
    (slice : Tg_root_slice_d I X₀ R₀ γ₀ D₀ C₀ X R C p γ V t)
    (cut : Tg_root_cut_d I c X₀ R₀ w₀ γ₀ B₀ A₀ D₀ A)
    (source : Smem_d I c X₀ R₀) (trans : M.TransitiveSet X₀)
    (hN : (smdl_structure_l I (R := R₀) cut.model.2.1).Models KP) :
    Rr_layer_d I D₀ X R V t := by
  have down := cut.down_l hZF hN
  have dt : M.TransitiveSet D₀ := by
    intro x hx y hy
    have xx := ((cut.carrier x).mp hx).1
    exact down x y hx ((source.2 y x).mpr ⟨trans x xx y hy,xx,hy⟩)
  refine ⟨dt,slice.rank.2.1,slice.injection,slice.image,?_⟩
  intro x y xy z
  apply (slice.predecessors x y xy z).trans
  constructor
  · rintro ⟨a,ax,az⟩
    exact ⟨a,((source.2 a x).mp ax).2.2,az⟩
  · rintro ⟨a,ax,az⟩
    exact ⟨a,(source.2 a x).mpr
      ⟨((cut.carrier a).mp (slice.injection.1.input_mem_of_pairMember az)).1,
        ((cut.carrier x).mp (slice.injection.1.input_mem_of_pairMember xy)).1,ax⟩,az⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 实际隶属根的同一极限腿固定原秩切片

原档案共尾地供应完整根切片。只有根本身已有传递隶属呈示时，才把
这些切片读成同一背景传递集的解释，并在指定锥中进行内部成员归纳。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

/-- 任意良基枝的原档案直接产生固定性所需的共尾锚点。 -/
theorem Tg_raw_iteration_run_d.root_fixed_l
    {ω c o X₀ R₀ γ₀ D₀ C₀ S₀ A₀ A X K r a f H w₀ B₀ b d N W P : M.Domain}
    (h : Tg_raw_iteration_run_d hZF ω c o X₀ R₀ γ₀ D₀ C₀ S₀ A₀ A X K r a f H)
    {U : Fin 6 → M.Domain} (u : Tg_raw_iteration_union_d hZF ω c o X₀ R₀ γ₀ D₀ C₀ H U)
    (cut : Tg_root_cut_d I c X₀ R₀ w₀ γ₀ B₀ A₀ D₀ A)
    (source : Smem_d I c X₀ R₀) (trans : M.TransitiveSet X₀)
    (hN : (smdl_structure_l I (R := R₀) cut.model.2.1).Models KP)
    (wf : It_wf_branch_d hZF ω ω (U 0) (U 1) (U 2) b)
    (target : Smem_d I d N W) (nt : M.TransitiveSet N)
    (cone : It_cone_d (kp_pair_l (ZF.modelsKP hZF)) ω b (U 1) (U 2) d N W P) :
    ∀ j, Rd_entry_d o j P → ∀ x, M.mem x D₀ → Rd_entry_d x x j := by
  obtain ⟨_,_,cofinal,_⟩ := h.wf_tail_l hZF u wf
  obtain ⟨e,_,he⟩ := u.tree.omega.1.1
  obtain ⟨s,_,hs⟩ := h.recursion.1.2.1 e he
  obtain ⟨v,code,state⟩ := (h.rows e s hs).1
  have root : Rd_entry_d o c (U 1) := by
    obtain ⟨p,pair,hp⟩ := state.root_node
    exact ⟨p,pair,(u.columns 1 p).mpr ⟨v,e,s,hs,code,hp⟩⟩
  apply cone.fixed_l hZF u.tree.omega u.tree.diagram wf.1 root source.1 target nt
  intro i hi
  obtain ⟨k,hk,ik,m,p,t,entry,pair⟩ := cofinal i (wf.1.subset i hi)
  obtain ⟨q,qp,hq⟩ := entry
  obtain ⟨v,n,s,hs,code,hq⟩ := (u.columns 5 q).mp hq
  obtain ⟨row,tuple,_⟩ := (h.read_l hZF v hs code).request.views m p ⟨q,qp,hq⟩
  have index : row.i = k := by
    obtain ⟨t',pair',_⟩ := tuple
    exact (kpair_injective_l M pair' pair).1
  have entry : Rd_entry_d m p (U 5) :=
    ⟨q,qp,(u.columns 5 q).mpr ⟨v,n,s,hs,code,hq⟩⟩
  obtain ⟨node,model,_,_,_,⟨γ,V,t,slice,_,_⟩,_,edge,_⟩ := h.archive_read_l hZF u row entry tuple
  have map := u.tree.diagram.elementary o row.i row.p c X₀ R₀ row.c row.X row.R edge root node source.1 model
  have layer := slice.mem_carrier_l hZF cut source trans hN
  refine ⟨row.i,row.p,row.c,row.X,row.R,index.symm ▸ hk,
    index.symm ▸ wf.1.forward_l u.tree.diagram.order hi hk ik,edge,node,model,
    layer.transitive,?_,?_⟩
  · intro x hx
    obtain ⟨y,_,xy⟩ := layer.injection.1.2.2 x hx
    exact ⟨y,slice.root x y xy⟩
  · intro x y hx xy z
    obtain ⟨y',_,xy'⟩ := layer.injection.1.2.2 x hx
    have same := map.1.1.1.2 x y' y (slice.root x y' xy') xy
    apply (layer.predecessors x y (same ▸ xy') z).trans
    apply exists_congr
    intro a
    apply and_congr_right
    intro ax
    refine ⟨slice.root a z,fun az => ?_⟩
    obtain ⟨z',_,az'⟩ := layer.injection.1.2.2 a (layer.transitive x hx a ax)
    exact map.1.1.1.2 a z' z (slice.root a z' az') az ▸ az'

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 实际传递根中的原对局投影

一般原关系结论先给出逐字母根像。指定实际隶属根后，同一良基锥的
根腿固定字母载体，因此精确复合就是原对局；全部分支见证保持原样。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal Descriptive
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Tg_raw_iteration_run_d.wf_mem_projection_l
    {ω c o X₀ R₀ w₀ γ₀ B₀ D₀ C₀ S₀ A₀ A X K r a f H b z Y₀ F₀ : M.Domain}
    (h : Tg_raw_iteration_run_d hZF ω c o X₀ R₀ γ₀ D₀ C₀ S₀ A₀ A X K r a f H)
    {U : Fin 6 → M.Domain} (u : Tg_raw_iteration_union_d hZF ω c o X₀ R₀ γ₀ D₀ C₀ H U)
    (root : Zc_model_d I ω c X₀ R₀)
    (cut : Tg_root_cut_d I c X₀ R₀ w₀ γ₀ B₀ A₀ D₀ A)
    (source : Smem_d I c X₀ R₀) (trans : M.TransitiveSet X₀)
    (numbers : Rr_layer_d I ω X₀ R₀ w₀ z) (space : Sc_fseq_d I w₀ Y₀ F₀ X₀ R₀)
    (closed : Rr_truth_d I X₀ R₀ (tree_m (.bound 1) .newest) (Fin.cases S₀ (fun _ : Fin 1 => F₀)))
    (input : Fn0_d ω A f)
    (played : ∀ n s q, Rd_entry_d n s H → Rt_coord_d (19 : Fin 66) s q → M.IsRestrictionOf I q f n)
    (wf : It_wf_branch_d hZF ω ω (U 0) (U 1) (U 2) b) :
    ∃ d N W P j Y' F' S', Smem_d I d N W ∧ M.TransitiveSet N ∧ It_source_d hZF ω d ∧
      It_cone_d (kp_pair_l (ZF.modelsKP hZF)) ω b (U 1) (U 2) d N W P ∧ Rd_entry_d o j P ∧
      Smap_d I ω c d X₀ N j ∧ Rd_entry_d Y₀ Y' j ∧ Rd_entry_d F₀ F' j ∧ Rd_entry_d S₀ S' j ∧
      Fseq_space_d I ω Y' F' ∧ Tree_d F' S' ∧ Tg_projection_d hZF ω Y' F' S' f := by
  obtain ⟨d,N,W,P,j,Y',F',S',f',target,nt,ready,cone,leg,map,iY,iF,iS,finite,tree,comp,proj⟩ :=
    h.wf_projection_l hZF u root cut numbers space closed input played wf
  have hN := ZF.modelsKP (ZFC.models_zf_l (root.native_l I hZF u.tree.omega))
  have fixed := h.root_fixed_l hZF u cut source trans hN wf target nt cone j leg
  have low x (hx : M.mem x A) : M.mem x D₀ :=
    cut.down_l hZF hN A₀ x ((cut.carrier A₀).mpr
      ⟨(cut.model.2.2.2 A₀ B₀ cut.alphabet).1,cut.alphabet⟩) ((cut.letters x).mp hx).2
  have self : It_comp_d f j f := by
    refine ⟨(fn0_function_l (ZF.modelsKP hZF) input).1.1,fun i y => ⟨?_,?_⟩⟩
    · intro iy
      exact ⟨y,iy,fixed y (low y (input.bound_l iy).2)⟩
    · rintro ⟨x,ix,xy⟩
      exact map.1.1.1.2 x x y (fixed x (low x (input.bound_l ix).2)) xy ▸ ix
  have eq := comp.unique_l hZF.1 self
  exact ⟨d,N,W,P,j,Y',F',S',target,nt,ready,cone,leg,map,iY,iF,iS,finite,tree,eq ▸ proj⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 非良基根上的真实恒等迭代与策略

直接构造普通 ω 长恒等迭代。任意良基共尾枝都会把根关系嵌入其同一个
良基直接极限，与根非良基矛盾。故全部良基枝条件成立，无需源数字解释。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal Descriptive
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem tg_ill_projection_l {ω o c X R A Y F S f : M.Domain}
    (hw : M.IsOmega ω) (model : Smdl_d I c X R) (ill : ¬ Wf_rel_d X R)
    (empty : ∀ x, ¬ M.mem x o) : Tg_gp_d hZF ω o c A Y F S f := by
  obtain ⟨ρ,rank⟩ := ZF.rk_exists_l I hZF A
  obtain ⟨γ,succ⟩ := KP.exists_successor (ZF.modelsKP hZF) ρ
  obtain ⟨e,_,he⟩ := hw.1.1
  obtain ⟨T,Q,G,E,_,tree,_,padding,_⟩ := it_padding_core_l hZF hw model
    (hw.isOrdinal (ZF.modelsKP hZF)) ⟨e,he⟩
  refine ⟨ρ,γ,rank,succ.predecessor_mem,KP.successor_isOrdinal (ZF.modelsKP hZF) rank.ordinal succ,
    T,Q,G,E,tree,?_,?_⟩
  · intro i p κ L F entry payload
    obtain ⟨_,⟨u,_,_,_,pair⟩,_⟩ := payload
    exact (padding i p entry u ((pair u).mpr (Or.inl rfl))).elim
  · intro b wf
    exact (ill (wf.root_wf_l hZF hw tree.diagram empty (tree.root o empty) model)).elim

/-- 任意字母表的实际本方策略均可用；空字母表由同一策略接口处理。 -/
theorem tg_ill_strategy_l {ω c X R : M.Domain}
    (hw : M.IsOmega ω) (model : Smdl_d I c X R) (ill : ¬ Wf_rel_d X R)
    (A Y F S : M.Domain) : ∃ o J σ, (∀ x, ¬ M.mem x o) ∧ Fseq_space_d I ω A J ∧
      Gm_strategy_d I false ω A J σ ∧
      ∀ f, Fn0_d ω A f → Gm_follows_d I false ω σ f → Tg_gp_d hZF ω o c A Y F S f := by
  obtain ⟨o,empty,_⟩ := hw.1.1
  obtain ⟨J,space⟩ := ZF.fseq_space_exists_l I hZF hw A
  have produce a (ha : M.mem a A) : ∃ σ, Fn0_d J A σ ∧
      ∀ f, Fn0_d ω A f → Gm_follows_d I false ω σ f → Tg_gp_d hZF ω o c A Y F S f := by
    obtain ⟨σ,fn,_⟩ := ZF.exists_constantFunction hZF I (source := J) ha
    exact ⟨σ,fn0_of_function_l (ZF.modelsKP hZF) fn,
      fun _ _ _ => tg_ill_projection_l hZF hw model ill empty⟩
  obtain ⟨σ,strategy,property⟩ := gm_ii_strategy_l hZF hw space produce
  exact ⟨o,J,σ,empty,space,strategy,property⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 实际传递根上的原对局全枝移位投影

同一原并树提供全部活动临界点界；任意良基共尾枝都在自己的实际极限
中投影原对局。这里使用普通迭代树，未把额外的 nice 性质写入目标。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal Descriptive
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Tg_raw_iteration_run_d.mem_shifted_l
    {ω c o X₀ R₀ w₀ γ₀ B₀ D₀ C₀ S₀ A₀ A X K r a f H z Y₀ F₀ : M.Domain}
    (h : Tg_raw_iteration_run_d hZF ω c o X₀ R₀ γ₀ D₀ C₀ S₀ A₀ A X K r a f H)
    {U : Fin 6 → M.Domain} (u : Tg_raw_iteration_union_d hZF ω c o X₀ R₀ γ₀ D₀ C₀ H U)
    (root : Zc_model_d I ω c X₀ R₀)
    (cut : Tg_root_cut_d I c X₀ R₀ w₀ γ₀ B₀ A₀ D₀ A)
    (source : Smem_d I c X₀ R₀) (trans : M.TransitiveSet X₀)
    (numbers : Rr_layer_d I ω X₀ R₀ w₀ z) (space : Sc_fseq_d I w₀ Y₀ F₀ X₀ R₀)
    (closed : Rr_truth_d I X₀ R₀ (tree_m (.bound 1) .newest) (Fin.cases S₀ (fun _ : Fin 1 => F₀)))
    (input : Fn0_d ω A f)
    (played : ∀ n s q, Rd_entry_d n s H → Rt_coord_d (19 : Fin 66) s q → M.IsRestrictionOf I q f n) :
    Tg_mem_shifted_d hZF ω o c γ₀ Y₀ F₀ S₀ f := by
  have hN := ZF.modelsKP (ZFC.models_zf_l (root.native_l I hZF u.tree.omega))
  refine ⟨U 0,U 1,U 2,U 3,u.tree.toIt_tree_core_d,u.critical.mem_l hZF source trans hN cut.rank cut.carrier,?_⟩
  intro b wf
  obtain ⟨d,N,W,P,j,Y',F',S',target,_,ready,cone,leg,_,iY,iF,iS,space,tree,proj⟩ :=
    h.wf_mem_projection_l hZF u root cut source trans numbers space closed input played wf
  exact ⟨d,N,W,P,j,Y',F',S',target,ready,cone,leg,iY,iF,iS,space,tree,proj⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 同一真实控制表直接生产全枝策略

控制表可以来自原辅助胜策，也可以沿实际同构搬运。两种来源都进入同一
六十六项零轮、统一响应表和本方策略；不重新选择语言表或辅助游戏。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal Descriptive
universe u
variable {M : Structure.{u}} (hZFC : M.Models ZFC)
local notation "hZF" => ZFC.models_zf_l hZFC
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem tg_control_mem_strategy_l
    {Ω c X R z : M.Domain} (hΩ : M.IsOmega Ω) (certificate : Zc_model_d I Ω c X R)
    (source : Smem_d I c X R) (trans : M.TransitiveSet X)
    {p : Tg_params_d (smdl_structure_l I (R := R) certificate.model.2.1).Domain}
    (numbers : Rr_layer_d I Ω X R p.ω.val z)
    {A F L G D σ H Y T : (smdl_structure_l I (R := R) certificate.model.2.1).Domain}
    (control : Formula.satisfies (⟨fun i =>
      [p.ω,p.e,p.a,p.b,p.c,p.δ,p.A,p.S,p.ν,p.E,p.P,p.Q,A,F,L,G,D,σ,H].get i,
      fun _ => p.ω⟩ : Env (smdl_structure_l I (R := R) certificate.model.2.1) 19) tg_control0_m)
    (space : Fseq_space_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l
      (certificate.native_l I hZF hΩ)))) p.ω Y T)
    (closed : Tree_d (M := smdl_structure_l I (R := R) certificate.model.2.1) T p.S) :
    ∃ o J σ₀, (∀ x, ¬ M.mem x o) ∧ Fseq_space_d I Ω p.A.val J ∧
      Gm_strategy_d I false Ω p.A.val J σ₀ ∧
      ∀ f, Fn0_d Ω p.A.val f → Gm_follows_d I false Ω σ₀ f →
        Tg_gp_d hZF Ω o c p.A.val Y.val T.val p.S.val f := by
  have native := ZFC.models_zf_l (certificate.native_l I hZF hΩ)
  have finite : Sc_fseq_d I p.ω.val Y.val T.val X R :=
    (sc_fseq_native_l I certificate.model.2.1 native.1 p.ω Y T).mpr
      (fun s => (space s).trans ⟨fun ⟨n,hn,fn⟩ => ⟨n,hn,fn0_of_function_l (ZF.modelsKP native) fn⟩,
        fun ⟨n,hn,fn⟩ => ⟨n,hn,fn0_function_l (ZF.modelsKP native) fn⟩⟩)
  let η : Env (smdl_structure_l I (R := R) certificate.model.2.1) 2 :=
    ⟨Fin.cases p.S (fun _ => T),fun _ => p.S⟩
  have truth : Rr_truth_d I X R (tree_m (.bound 1) .newest)
      (Fin.cases p.S.val (fun _ : Fin 1 => T.val)) := by
    have moved := (rr_truth_native_l I certificate.model.2.1 (tree_m (.bound 1) .newest)
      (by simp -implicitDefEqProofs) η.bound).mpr ((tree_sat_l η (.bound 1) .newest).mpr closed)
    have values : (fun i => (η.bound i).val) = Fin.cases p.S.val (fun _ : Fin 1 => T.val) :=
      funext (Fin.cases rfl (fun _ => rfl))
    exact values ▸ moved
  obtain ⟨η,C,r,u,o,m,T₀,Q,J₀,q,A₀,F₀,J₁,D₀,t₀,k₀,f₀,Dₛ,_,_,_,empty,cut,_,_,finites,
    _,_,_,_,_,s,tuple,code⟩ := tg_control_iteration_start_l hZF hΩ certificate numbers control
  obtain ⟨Xs,Ds,K,choice⟩ := code.choice_l hZFC certificate cut
  have zero : Rt_coord_d (18 : Fin 66) s o := ⟨_,tuple,by rfl⟩
  obtain ⟨σ₀,strategy,runs⟩ := choice.turn_strategy_l hZF zero empty finites
  obtain ⟨letters,ordinal,ρ,rank,lower⟩ := cut.canonical_l hZF source trans
  refine ⟨o,J₁,σ₀,empty,letters ▸ finites,letters ▸ strategy,fun f input follows => ?_⟩
  have input : Fn0_d Ω A₀ f := letters.symm ▸ input
  obtain ⟨a,H,U,_,run,tree,played⟩ := runs f input follows
  exact ⟨ρ,u 24,rank,lower,ordinal,
    run.mem_shifted_l hZF tree certificate cut source trans numbers finite truth input played⟩

/-- 规范呈示的任意根均有策略；良基性只用于选择已经实现的两种构造。 -/
theorem tg_control_normal_strategy_l
    {Ω c X R : M.Domain} (hΩ : M.IsOmega Ω) (certificate : Zc_model_d I Ω c X R)
    (normal : Zc_normal_d I c X R)
    {p : Tg_params_d (smdl_structure_l I (R := R) certificate.model.2.1).Domain}
    {A F L G D σ H Y T : (smdl_structure_l I (R := R) certificate.model.2.1).Domain}
    (control : Formula.satisfies (⟨fun i =>
      [p.ω,p.e,p.a,p.b,p.c,p.δ,p.A,p.S,p.ν,p.E,p.P,p.Q,A,F,L,G,D,σ,H].get i,
      fun _ => p.ω⟩ : Env (smdl_structure_l I (R := R) certificate.model.2.1) 19) tg_control0_m)
    (space : Fseq_space_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l
      (certificate.native_l I hZF hΩ)))) p.ω Y T)
    (closed : Tree_d (M := smdl_structure_l I (R := R) certificate.model.2.1) T p.S) :
    ∃ Aext o J σ₀, (∀ x, M.mem x Aext ↔ M.mem x X ∧ Rd_entry_d x p.A.val R) ∧
      (∀ x, ¬ M.mem x o) ∧ Fseq_space_d I Ω Aext J ∧ Gm_strategy_d I false Ω Aext J σ₀ ∧
      ∀ f, Fn0_d Ω Aext f → Gm_follows_d I false Ω σ₀ f →
        Tg_gp_d hZF Ω o c Aext Y.val T.val p.S.val f := by
  classical
  let φ : UnarySchema 2 := { body := rd_entry0_m .newest (.bound 1) (.bound 2) }
  obtain ⟨Aext,as⟩ := ZF.separation_exists_d hZF φ ⟨Fin.cases p.A.val (fun _ => R),fun _ => X⟩ X
  have letters x : M.mem x Aext ↔ M.mem x X ∧ Rd_entry_d x p.A.val R :=
    (as x).trans (and_congr_right fun _ => rd_entry0_sat_l hZF.1 ..)
  by_cases well : Wf_rel_d X R
  · obtain ⟨source,trans⟩ := normal well
    have eq : Aext = p.A.val := hZF.1.eq_of_same_members Aext p.A.val fun x => (letters x).trans
      ⟨fun hx => ((source.2 x p.A.val).mp hx.2).2.2,
        fun hx => ⟨trans p.A.val p.A.property x hx,
          (source.2 x p.A.val).mpr ⟨trans p.A.val p.A.property x hx,p.A.property,hx⟩⟩⟩
    let N := smdl_structure_l I (R := R) certificate.model.2.1
    have native := ZFC.models_zf_l (certificate.native_l I hZF hΩ)
    let ν : Env N 19 := ⟨fun i =>
      [p.ω,p.e,p.a,p.b,p.c,p.δ,p.A,p.S,p.ν,p.E,p.P,p.Q,A,F,L,G,D,σ,H].get i,fun _ => p.ω⟩
    have facts := control
    simp only [tg_control0_m,Formula.satisfies_conj_iff] at facts
    have rules : Tg_rules_d native p A F L D :=
      (tg_rules_sat_l native ν (tg_control_params_d Term.bound) (.bound 12) (.bound 13) (.bound 14) (.bound 16)).mp facts.2.2.1
    obtain ⟨_,z,numbers⟩ := tg_numbers_mem_l hZF hΩ certificate source trans p.ω rules.omega
    obtain ⟨o,J,σ₀,empty,finite,strategy,runs⟩ :=
      tg_control_mem_strategy_l hZFC hΩ certificate source trans numbers control space closed
    refine ⟨Aext,o,J,σ₀,letters,?_⟩
    exact eq.symm ▸ ⟨empty,finite,strategy,runs⟩
  · obtain ⟨o,J,σ₀,empty,finite,strategy,runs⟩ :=
      tg_ill_strategy_l hZF hΩ certificate.model well Aext Y.val T.val p.S.val
    exact ⟨Aext,o,J,σ₀,letters,empty,finite,strategy,runs⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 由原辅助胜策得到严格越过字母秩的全枝策略

实际传递根把原字母载体识别回字母集合本身，并给出其背景秩严格小于
同次初始化的临界界。所有服从对局均由同一策略产生，每条良基共尾枝
都投影该原对局；不附加非空字母集、非空树或 nice 树假设。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal Descriptive
universe u
variable {M : Structure.{u}}

variable (hZFC : M.Models ZFC)
local notation "hZF" => ZFC.models_zf_l hZFC
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Tg_game_d.mem_shifted_strategy_l
    {Ω c X R z : M.Domain} (hΩ : M.IsOmega Ω) (certificate : Zc_model_d I Ω c X R)
    (source : Smem_d I c X R) (trans : M.TransitiveSet X)
    {p : Tg_params_d (smdl_structure_l I (R := R) certificate.model.2.1).Domain}
    (numbers : Rr_layer_d I Ω X R p.ω.val z)
    {A F L G D B W O Z g σ Y T : (smdl_structure_l I (R := R) certificate.model.2.1).Domain}
    (game : Tg_game_d (certificate.native_l I hZF hΩ) p A F L G D B W O Z g)
    (woodin : Woodin_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l
      (certificate.native_l I hZF hΩ)))) p.δ)
    (win : Cg_win_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l
      (certificate.native_l I hZF hΩ)))) false p.ω A F D B W σ)
    (space : Fseq_space_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l
      (certificate.native_l I hZF hΩ)))) p.ω Y T)
    (closed : Tree_d (M := smdl_structure_l I (R := R) certificate.model.2.1) T p.S) :
    ∃ o J σ₀, (∀ x, ¬ M.mem x o) ∧ Fseq_space_d I Ω p.A.val J ∧
      Gm_strategy_d I false Ω p.A.val J σ₀ ∧
      ∀ f, Fn0_d Ω p.A.val f → Gm_follows_d I false Ω σ₀ f →
        Tg_gp_d hZF Ω o c p.A.val Y.val T.val p.S.val f := by
  have ground := certificate.native_l I hZF hΩ
  obtain ⟨H,_,_,control,_⟩ := game.control_l ground woodin (game.win_root_l ground win) win
  exact tg_control_mem_strategy_l hZFC hΩ certificate source trans numbers control space closed

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 实际传递隶属根自动生成数字对应并构造策略

游戏的原生自然数对象先在同一隶属载体中读取。源内 ZFC 来自原根的
实际证书，自然数绝对性随后识别背景 ω；完整数字图由恒等图构造，
不再作为最终策略入口的额外参数。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal Descriptive
universe u
variable {M : Structure.{u}}


variable (hZFC : M.Models ZFC)
local notation "hZF" => ZFC.models_zf_l hZFC
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

/-- 给定原辅助游戏和实际传递隶属根即生成策略；数字图和空树根均已自动生产。 -/
theorem Tg_game_d.mem_strategy_l
    {Ω c X R : M.Domain} (hΩ : M.IsOmega Ω) (certificate : Zc_model_d I Ω c X R)
    (source : Smem_d I c X R) (trans : M.TransitiveSet X)
    {p : Tg_params_d (smdl_structure_l I (R := R) certificate.model.2.1).Domain}
    {A F L G D B W O Z g σ Y T : (smdl_structure_l I (R := R) certificate.model.2.1).Domain}
    (game : Tg_game_d (certificate.native_l I hZF hΩ) p A F L G D B W O Z g)
    (woodin : Woodin_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l
      (certificate.native_l I hZF hΩ)))) p.δ)
    (win : Cg_win_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l
      (certificate.native_l I hZF hΩ)))) false p.ω A F D B W σ)
    (space : Fseq_space_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l
      (certificate.native_l I hZF hΩ)))) p.ω Y T)
    (closed : Tree_d (M := smdl_structure_l I (R := R) certificate.model.2.1) T p.S) :
    ∃ o J σ₀, (∀ x, ¬ M.mem x o) ∧ Fseq_space_d I Ω p.A.val J ∧
      Gm_strategy_d I false Ω p.A.val J σ₀ ∧
      ∀ f, Fn0_d Ω p.A.val f → Gm_follows_d I false Ω σ₀ f →
        Tg_gp_d hZF Ω o c p.A.val Y.val T.val p.S.val f := by
  obtain ⟨_,z,numbers⟩ := tg_numbers_mem_l hZF hΩ certificate source trans p.ω game.setup.omega
  exact game.mem_shifted_strategy_l hZFC hΩ certificate source trans numbers woodin win space closed

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 同一次规范化搬运原控制并实际产生策略

良基根使用坍塌，非良基根使用恒等图。十九个控制坐标沿同一个初等映射
搬运，原字母载体经同一图的限制双射到目标字母载体，内部字母对象另行保留。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal Descriptive
universe u
variable {M : Structure.{u}} (hZFC : M.Models ZFC)
local notation "hZF" => ZFC.models_zf_l hZFC
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Tg_game_d.normalize_strategy_l
    {Ω c X R : M.Domain} (hΩ : M.IsOmega Ω) (certificate : Zc_model_d I Ω c X R)
    {p : Tg_params_d (smdl_structure_l I (R := R) certificate.model.2.1).Domain}
    {A F L G D B W O Z g σ Y T : (smdl_structure_l I (R := R) certificate.model.2.1).Domain}
    (game : Tg_game_d (certificate.native_l I hZF hΩ) p A F L G D B W O Z g)
    (woodin : Woodin_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l
      (certificate.native_l I hZF hΩ)))) p.δ)
    (win : Cg_win_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l
      (certificate.native_l I hZF hΩ)))) false p.ω A F D B W σ)
    (space : Fseq_space_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l
      (certificate.native_l I hZF hΩ)))) p.ω Y T)
    (closed : Tree_d (M := smdl_structure_l I (R := R) certificate.model.2.1) T p.S) :
    ∃ N τ inv d V Aold a Anew Y' T' S' b H, ∃ v : Fin 19 → M.Domain, ∃ o J σ₀,
      Zc_model_d I Ω d N V ∧ Zc_normal_d I d N V ∧ M.IsSetBijectionFromTo I τ X N ∧
      Smap_d I Ω c d X N τ ∧ M.IsSetBijectionFromTo I inv N X ∧
      (∀ x y, Rd_entry_d y x inv ↔ Rd_entry_d x y τ) ∧ Smap_d I Ω d c N X inv ∧
      ((Wf_rel_d X R ∧ Wc_graph_d X R τ ∧ Smem_d I d N V ∧ M.TransitiveSet N) ∨
        (¬ Wf_rel_d X R ∧ d = c ∧ N = X ∧ V = R ∧
          ∀ x y, Rd_entry_d x y τ ↔ M.mem x X ∧ x = y)) ∧
      (∀ x, M.mem x Aold ↔ M.mem x X ∧ Rd_entry_d x p.A.val R) ∧
      (∀ y, M.mem y Anew ↔ M.mem y N ∧ Rd_entry_d y a V) ∧
      M.IsSetBijectionFromTo I b Aold Anew ∧ M.IsRestrictionOf I b τ Aold ∧
      Rd_entry_d p.A.val a τ ∧ Rd_entry_d Y.val Y' τ ∧ Rd_entry_d T.val T' τ ∧ Rd_entry_d p.S.val S' τ ∧
      M.mem H X ∧ Rr_truth_d I N V tg_control0_m v ∧
      (∀ i, Rd_entry_d ([p.ω.val,p.e.val,p.a.val,p.b.val,p.c.val,p.δ.val,p.A.val,p.S.val,p.ν.val,
        p.E.val,p.P.val,p.Q.val,A.val,F.val,L.val,G.val,D.val,σ.val,H].get i) (v i) τ) ∧
      (∀ x, ¬ M.mem x o) ∧ Fseq_space_d I Ω Anew J ∧ Gm_strategy_d I false Ω Anew J σ₀ ∧
      ∀ f, Fn0_d Ω Anew f → Gm_follows_d I false Ω σ₀ f → Tg_gp_d hZF Ω o d Anew Y' T' S' f := by
  obtain ⟨d,N,V,τ,inv,cert,normal,bij,map,back,inverse,reverse,cases⟩ := certificate.normalize_l hZF hΩ
  obtain ⟨e,elementary,points⟩ := map.project_l I hZF hΩ certificate.model cert.model
  let source := smdl_structure_l I (R := R) certificate.model.2.1
  let dest := smdl_structure_l I (R := V) cert.model.2.1
  have ground := certificate.native_l I hZF hΩ
  have ground' := cert.native_l I hZF hΩ
  let Kp := kp_pair_l (ZF.modelsKP (ZFC.models_zf_l ground))
  let Kp' := kp_pair_l (ZF.modelsKP (ZFC.models_zf_l ground'))
  obtain ⟨H,_,_,control,_⟩ := game.control_l ground woodin (game.win_root_l ground win) win
  let ρ : Env source 19 := ⟨fun i =>
    [p.ω,p.e,p.a,p.b,p.c,p.δ,p.A,p.S,p.ν,p.E,p.P,p.Q,A,F,L,G,D,σ,H].get i,fun _ => p.ω⟩
  let q := p.map_l e
  have moved := (elementary tg_control0_m tg_control0_closed_l ρ).mp control
  have bounds : (fun i => e (ρ.bound i)) = fun i =>
      [q.ω,q.e,q.a,q.b,q.c,q.δ,q.A,q.S,q.ν,q.E,q.P,q.Q,e A,e F,e L,e G,e D,e σ,e H].get i := by
    funext i
    exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun i => Fin.elim0 i))))))))))))))))))) i
  have control' : Formula.satisfies (⟨fun i =>
      [q.ω,q.e,q.a,q.b,q.c,q.δ,q.A,q.S,q.ν,q.E,q.P,q.Q,e A,e F,e L,e G,e D,e σ,e H].get i,
      fun _ => q.ω⟩ : Env dest 19) tg_control0_m := by
    change Formula.satisfies (⟨fun i => e (ρ.bound i),fun _ => q.ω⟩ : Env dest 19) tg_control0_m at moved
    rw [bounds] at moved
    exact moved
  let ξ : Env source 3 := ⟨fun i => [T,Y,p.ω].get i,fun _ => p.ω⟩
  have finite' : Fseq_space_d Kp' q.ω (e Y) (e T) := by
    have moved := (elementary (fseq_space_m (𝒞 := kpair_convention_l) (.bound 2) (.bound 1) .newest)
      (by simp -implicitDefEqProofs) ξ).mp
      ((fseq_space_sat_l Kp (ZFC.models_zf_l ground).1 ξ (.bound 2) (.bound 1) .newest).mpr space)
    exact (fseq_space_sat_l Kp' (ZFC.models_zf_l ground').1 (image_env_l e ξ) (.bound 2) (.bound 1) .newest).mp moved
  let ζ : Env source 2 := ⟨Fin.cases p.S (fun _ => T),fun _ => p.ω⟩
  have closed' : Tree_d (M := dest) (e T) q.S := (tree_sat_l (image_env_l e ζ) (.bound 1) .newest).mp
    ((elementary (tree_m (.bound 1) .newest) (by simp -implicitDefEqProofs) ζ).mp
      ((tree_sat_l ζ (.bound 1) .newest).mpr closed))
  obtain ⟨Anew,o,J,σ₀,targetLetters,empty,finite,strategy,runs⟩ :=
    tg_control_normal_strategy_l hZFC hΩ cert normal control' finite' closed'
  let φ : UnarySchema 2 := { body := rd_entry0_m .newest (.bound 1) (.bound 2) }
  obtain ⟨Aold,as⟩ := ZF.separation_exists_d hZF φ ⟨Fin.cases p.A.val (fun _ => R),fun _ => X⟩ X
  have letters x : M.mem x Aold ↔ M.mem x X ∧ Rd_entry_d x p.A.val R :=
    (as x).trans (and_congr_right fun _ => rd_entry0_sat_l hZF.1 ..)
  obtain ⟨b,rest⟩ := ZF.exists_restriction hZF I τ Aold
  have bf := rest.isSetFunctionFromTo bij.1.1 (fun x hx => ((letters x).mp hx).1)
  have image x y (xy : Rd_entry_d x y b) : M.mem y Anew := by
    obtain ⟨hx,xy⟩ := (rest.2 x y).mp xy
    exact (targetLetters y).mpr ⟨map.1.1.output_mem_of_pairMember xy,
      (map.relation_l I hZF hΩ certificate.model cert.model xy (points p.A)).mp ((letters x).mp hx).2⟩
  have fn := fn0_function_l (ZF.modelsKP hZF) ((fn0_of_function_l (ZF.modelsKP hZF) bf).retarget_l image)
  have lettersBij : M.IsSetBijectionFromTo I b Aold Anew := by
    refine ⟨⟨fn,fun x y z hx hy => bij.1.2 x y z ((rest.2 x z).mp hx).2 ((rest.2 y z).mp hy).2⟩,?_⟩
    intro y hy
    obtain ⟨x,hx,xy⟩ := bij.2 y ((targetLetters y).mp hy).1
    have hxA := (map.relation_l I hZF hΩ certificate.model cert.model xy (points p.A)).mpr
      ((targetLetters y).mp hy).2
    have ha := (letters x).mpr ⟨hx,hxA⟩
    exact ⟨x,ha,(rest.2 x y).mpr ⟨ha,xy⟩⟩
  have truth : Rr_truth_d I N V tg_control0_m (fun i => (e (ρ.bound i)).val) :=
    (rr_truth_native_l I cert.model.2.1 tg_control0_m tg_control0_closed_l
      (image_env_l e ρ).bound).mpr moved
  refine ⟨N,τ,inv,d,V,Aold,q.A.val,Anew,(e Y).val,(e T).val,q.S.val,b,H.val,
    (fun i => (e (ρ.bound i)).val),o,J,σ₀,cert,normal,bij,map,back,inverse,reverse,cases,
    letters,targetLetters,lettersBij,rest,points p.A,points Y,points T,points p.S,H.property,truth,?_,
    empty,finite,strategy,runs⟩
  intro i
  exact Fin.cases (points p.ω) (Fin.cases (points p.e) (Fin.cases (points p.a) (Fin.cases (points p.b) (Fin.cases (points p.c) (Fin.cases (points p.δ) (Fin.cases (points p.A) (Fin.cases (points p.S) (Fin.cases (points p.ν) (Fin.cases (points p.E) (Fin.cases (points p.P) (Fin.cases (points p.Q) (Fin.cases (points A) (Fin.cases (points F) (Fin.cases (points L) (Fin.cases (points G) (Fin.cases (points D) (Fin.cases (points σ) (Fin.cases (points H) (fun i => Fin.elim0 i))))))))))))))))))) i

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 5.23：原辅助胜策到全部良基分支的广义投影

论文约定良基模型采用传递隶属呈示。本入口只要求这一约定在整个根
良基时成立；非良基根由实际恒等迭代处理。任意未规范对象码则由
normalize_strategy_l 自动生产这样的呈示，原图与字母双射均完整保留。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal Descriptive
universe u
variable {M : Structure.{u}} (hZFC : M.Models ZFC)
local notation "hZF" => ZFC.models_zf_l hZFC
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Tg_game_d.normal_strategy_l
    {Ω c X R : M.Domain} (hΩ : M.IsOmega Ω) (certificate : Zc_model_d I Ω c X R)
    (normal : Zc_normal_d I c X R)
    {p : Tg_params_d (smdl_structure_l I (R := R) certificate.model.2.1).Domain}
    {A F L G D B W O Z g σ Y T : (smdl_structure_l I (R := R) certificate.model.2.1).Domain}
    (game : Tg_game_d (certificate.native_l I hZF hΩ) p A F L G D B W O Z g)
    (woodin : Woodin_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l
      (certificate.native_l I hZF hΩ)))) p.δ)
    (win : Cg_win_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l
      (certificate.native_l I hZF hΩ)))) false p.ω A F D B W σ)
    (space : Fseq_space_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l
      (certificate.native_l I hZF hΩ)))) p.ω Y T)
    (closed : Tree_d (M := smdl_structure_l I (R := R) certificate.model.2.1) T p.S) :
    ∃ Aext o J σ₀, (∀ x, M.mem x Aext ↔ M.mem x X ∧ Rd_entry_d x p.A.val R) ∧
      (∀ x, ¬ M.mem x o) ∧ Fseq_space_d I Ω Aext J ∧ Gm_strategy_d I false Ω Aext J σ₀ ∧
      ∀ f, Fn0_d Ω Aext f → Gm_follows_d I false Ω σ₀ f →
        Tg_gp_d hZF Ω o c Aext Y.val T.val p.S.val f := by
  have ground := certificate.native_l I hZF hΩ
  obtain ⟨H,_,_,control,_⟩ := game.control_l ground woodin (game.win_root_l ground win) win
  exact tg_control_normal_strategy_l hZFC hΩ certificate normal control space closed

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 5.23 一般策略的逐分支投影出口

把一般策略返回的 `Tg_gp_d` 收益证书立即扁平为树、临界点界和全部良基分支
投影。这里不新增策略、树或可数性前提，只固定已有策略结果的消费形状。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal Descriptive
universe u
variable {M : Structure.{u}}

theorem Tg_game_d.normal_strategy_wf_projection_l
    (hZFC : M.Models ZFC)
    {Ω c X R : M.Domain} (hΩ : M.IsOmega Ω)
    (certificate : Zc_model_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) Ω c X R)
    (normal : Zc_normal_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) c X R)
    {p : Tg_params_d (smdl_structure_l
      (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) (R := R) certificate.model.2.1).Domain}
    {A F L G D B W O Z g σ Y T :
      (smdl_structure_l (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC)))
        (R := R) certificate.model.2.1).Domain}
    (game : Tg_game_d (certificate.native_l (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC)))
      (ZFC.models_zf_l hZFC) hΩ) p A F L G D B W O Z g)
    (woodin : Woodin_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l
      (certificate.native_l (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC)))
        (ZFC.models_zf_l hZFC) hΩ)))) p.δ)
    (win : Cg_win_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l
      (certificate.native_l (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC)))
        (ZFC.models_zf_l hZFC) hΩ)))) false p.ω A F D B W σ)
    (space : Fseq_space_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l
      (certificate.native_l (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC)))
        (ZFC.models_zf_l hZFC) hΩ)))) p.ω Y T)
    (closed : Tree_d (M := smdl_structure_l
      (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) (R := R) certificate.model.2.1)
      T p.S) :
    ∃ Aext o J σ₀, (∀ x, M.mem x Aext ↔ M.mem x X ∧
      Rd_entry_d x p.A.val R) ∧
      (∀ x, ¬ M.mem x o) ∧
      Fseq_space_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) Ω Aext J ∧
      Gm_strategy_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) false Ω Aext J σ₀ ∧
      ∀ f, Fn0_d Ω Aext f → Gm_follows_d
        (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) false Ω σ₀ f →
        ∃ ρ γ T₀ Q₀ G₀ E₀, Rk_d
          (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) Aext ρ ∧
          M.mem ρ γ ∧ M.IsOrdinal γ ∧
          It_tree_core_d (ZFC.models_zf_l hZFC) Ω c Ω T₀ Q₀ G₀ E₀ ∧
          It_critical_bound_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) γ Q₀ E₀ ∧
          ∀ b, It_wf_branch_d (ZFC.models_zf_l hZFC) Ω Ω T₀ Q₀ G₀ b →
            ∃ d N W₀ P j Y' F' S', Smem_d
              (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) d N W₀ ∧
              It_source_d (ZFC.models_zf_l hZFC) Ω d ∧
              It_cone_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) Ω b Q₀ G₀ d N W₀ P ∧
              Rd_entry_d o j P ∧ Rd_entry_d Y.val Y' j ∧ Rd_entry_d T.val F' j ∧
              Rd_entry_d p.S.val S' j ∧
              Fseq_space_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) Ω Y' F' ∧
              Tree_d F' S' ∧ Tg_projection_d (ZFC.models_zf_l hZFC) Ω Y' F' S' f := by
  obtain ⟨Aext, o, J, σ₀, domain, empty, space', strategy, follows⟩ :=
    Tg_game_d.normal_strategy_l hZFC hΩ certificate normal game woodin win space closed
  refine ⟨Aext, o, J, σ₀, domain, empty, space', strategy, ?_⟩
  intro f input played
  exact Tg_gp_d.wf_projection_l (ZFC.models_zf_l hZFC) (follows f input played)

end YesMetaZFC.SetTheory.LargeCardinal
