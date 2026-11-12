import YesMetaZFC.SetTheory.LargeCardinal.Absorption.BranchGeneric
import YesMetaZFC.SetTheory.LargeCardinal.Absorption.Trace
import YesMetaZFC.Model.Forcing.Order.ProductRight
import YesMetaZFC.Model.Forcing.Boolean.GroundGeneric
import YesMetaZFC.Model.Forcing.Embedding.Rank
import YesMetaZFC.Model.Forcing.Extension.DenseFamily
import YesMetaZFC.SetTheory.Descriptive.Coding.SequenceCons
import YesMetaZFC.Model.Forcing.Order.GenericTreeGround
import YesMetaZFC.Model.Forcing.Ground.CheckPool
import YesMetaZFC.Model.Forcing.Order.FilterExtension
import YesMetaZFC.Model.Forcing.Ground.Collapse
import YesMetaZFC.SetTheory.LargeCardinal.Absorption.NoCollapse
import YesMetaZFC.SetTheory.LargeCardinal.Demand.Corollary712
import YesMetaZFC.SetTheory.LargeCardinal.Absorption.GroundPlay
import YesMetaZFC.SetTheory.LargeCardinal.Demand.UntagGeneral
import YesMetaZFC.SetTheory.LargeCardinal.Iteration.NiceReturn
import YesMetaZFC.SetTheory.LargeCardinal.Iteration.WeakBranch
import YesMetaZFC.SetTheory.LargeCardinal.Iteration.ReturnFactor
import YesMetaZFC.SetTheory.LargeCardinal.Iteration.CountableCover
import YesMetaZFC.SetTheory.LargeCardinal.Iteration.CountableLimit

/-! # 同一原对局把稠密名字要求传到泛型共尾条件

给定某个辅助要求，取小条件列中晚于该要求的共尾项。其实际原对局位置
为 2k，仍晚于要求；在分支原生模型中回读，便得到该条件上的非反驳。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal Descriptive Model.Forcing.Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Ag_branch_d.small_order_l {Ω c X R z Q G b f : M.Domain} (hw : M.IsOmega Ω)
    (source : Smem_d I c X R) (xt : M.TransitiveSet X)
    (native : (smdl_structure_l I (R := R) source.1.2.1).Models ZF)
    {ω κ δ A : (smdl_structure_l I (R := R) source.1.2.1).Domain}
    {p : Ag_forcing_d native ω κ δ A} (s : Ag_system_d native p)
    (inh : ∃ x, (smdl_structure_l I (R := R) source.1.2.1).mem x A)
    (r : Ag_branch_d hZF Ω z c X Q G b (fun i => (s.aux_params_l native i).val) f) :
    (r.w 1).val = p.Q.val ∧ ∀ x y, M.mem x p.Q.val → M.mem y p.Q.val →
      (Entry_d M x y p.T.val ↔ Entry_d M x y (r.w 2).val) := by
  obtain ⟨fixedQ,pointQ,_⟩ := s.fixed_small_l hZF hw source r.target xt r.transitive r.map native inh r.fixed r.point
  exact ⟨r.map.1.1.1.2 _ _ _ (r.images 1) fixedQ,
    fun x y hx hy => r.map.entry_l hZF hw xt r.transitive source r.target (pointQ x hx) (pointQ y hy) (r.images 2)⟩

theorem Ag_branch_d.demand_cofinal_l {Ω c X R z Q G b f x H q : M.Domain} (hΩ : M.IsOmega Ω)
    (source : Smem_d I c X R) (xt : M.TransitiveSet X)
    (native : (smdl_structure_l I (R := R) source.1.2.1).Models ZF)
    {ω κ δ A : (smdl_structure_l I (R := R) source.1.2.1).Domain}
    {p : Ag_forcing_d native ω κ δ A} (s : Ag_system_d native p)
    (hw : (smdl_structure_l I (R := R) source.1.2.1).IsOmega ω) (eqω : ω.val = Ω)
    (inh : ∃ y, (smdl_structure_l I (R := R) source.1.2.1).mem y A)
    (r : Ag_branch_d hZF Ω z c X Q G b (fun i => (s.aux_params_l native i).val) f)
    (sub : M.MemberSubset H p.Q.val) (trace : Ag_trace_d hZF Ω A.val s.A.val s.F₀.val s.R₀.val f x H)
    (fq : Fn0_d Ω p.Q.val q)
    (coords : ∀ k n a y t, M.mem k Ω → M.IsOrdinalAddition I n k k → Entry_d M n a f →
      KPair_d M a y t → Entry_d M k y x ∧ Entry_d M k t q)
    (cofinal : ∀ t, M.mem t H → ∀ i, M.mem i Ω → ∃ k u, M.mem i k ∧ Entry_d M k u q ∧ Entry_d M u t p.T.val)
    {i d l a : (smdl_structure_l I (R := r.W) r.target.1.2.1).Domain}
    (id : Entry_d M i.val d.val r.a) (la : Entry_d M l.val a.val r.u)
    (li : (smdl_structure_l I (R := r.W) r.target.1.2.1).SuccessorOf l i) :
    ∀ t : (smdl_structure_l I (R := r.W) r.target.1.2.1).Domain, M.mem t.val H →
      ∃ u, M.mem u.val H ∧ Entry_d (smdl_structure_l I (R := r.W) r.target.1.2.1) u t (r.w 2) ∧
        Ag_demand_d (r.w 1) (r.w 2) (r.w 7) u a d := by
  let N := smdl_structure_l I (R := R) source.1.2.1
  let L := smdl_structure_l I (R := r.W) r.target.1.2.1
  have srcInj : Function.Injective (Subtype.val : N.Domain → M.Domain) := fun _ _ eq => Subtype.ext eq
  have srcFull := smem_full_l I source xt
  have game := s.source.image_l native hZF Subtype.val srcInj srcFull hw (eqω.symm ▸ hΩ)
  have game : Ag_game_d hZF Ω A.val p.Q.val p.T.val s.E.val s.B.val s.A.val s.F₀.val s.R₀.val := by
    simpa only [eqω] using! game
  have inj : Function.Injective (Subtype.val : L.Domain → M.Domain) := fun _ _ eq => Subtype.ext eq
  have full := smem_full_l I r.target r.transitive
  have member {a b : L.Domain} : M.mem a.val b.val ↔ L.mem a b := image_member_l (M := L) (N := M) Subtype.val inj full
  have edge := (r.small_order_l hZF hΩ source xt native s inh).2
  intro t ht
  obtain ⟨k,u,lk,ku,ut⟩ := cofinal t.val ht l.val (r.second.bound_l la).1
  have hk := (fq.bound_l ku).1
  obtain ⟨y,_,ky⟩ := trace.real.2.1 k hk
  obtain ⟨n,a',add,na,pair⟩ := game.coordinate_read_l hZF hΩ trace.play trace.branch trace.real fq coords ky ku
  have uh := trace.small n a' y u na pair ⟨k,hk,add⟩
  have ln := ZF.ordinalAddition_left_member_mem_value hZF I
    (hΩ.members_areOrdinals (ZF.modelsKP hZF) k hk) (hΩ.members_areOrdinals (ZF.modelsKP hZF) k hk) lk add
  obtain ⟨n₀,_,eqn⟩ := (full (r.w 0) n).mp (r.omega.symm ▸ (trace.play.bound_l na).1)
  obtain ⟨a₀,_,eqa⟩ := (full (r.w 10) a').mp (r.input.bound_l na).2
  subst n a'
  obtain ⟨y₀,u₀,pair₀,eqy,equ⟩ := image_kpair_pull_l (ZF.modelsKP r.native) hZF.1 Subtype.val inj full pair
  subst y u
  have even : Gm_even_d (kp_pair_l (ZF.modelsKP r.native)) (r.w 0) n₀ :=
    (image_even_l r.native hZF Subtype.val inj full r.frame.omega).mpr
      (by simpa only [r.omega] using (show Gm_even_d I Ω n₀.val from ⟨k,hk,add⟩))
  have below : Entry_d L u₀ t (r.w 2) :=
    (image_entry_iff_l Subtype.val inj full (KP.exists_pair (ZF.modelsKP r.native)) hZF.1 u₀ t (r.w 2)).mpr
      ((edge u₀.val t.val (sub u₀.val uh) (sub t.val ht)).mp ut)
  exact ⟨u₀,uh,below,r.read.dense i d l a n₀ a₀ y₀ u₀ id la li na pair₀ even (Or.inl (member.mp ln))⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 分支中同一积力迫及函数名字的实际证书

完整初等性运输积、顶条件、两份规范参数名字和全部函数名字成员的证书。
函数名字是原第二辅助图首项所选的名字，不另外构造候选函数。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal Descriptive Model.Forcing.Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Ag_branch_d.product_data_l {Ω c X R z Q G b f : M.Domain} (hw : M.IsOmega Ω)
    (source : Smem_d I c X R)
    (native : (smdl_structure_l I (R := R) source.1.2.1).Models ZF)
    {ω κ δ A : (smdl_structure_l I (R := R) source.1.2.1).Domain}
    {p : Ag_forcing_d native ω κ δ A} (s : Ag_system_d native p)
    (r : Ag_branch_d hZF Ω z c X Q G b (fun i => (s.aux_params_l native i).val) f) :
    let N := smdl_structure_l I (R := r.W) r.target.1.2.1
    Prod_d r.native (r.w 1) (r.w 2) (r.w 3) (r.w 4) (r.w 5) (r.w 6) ∧
      Cond_order_d N (r.w 5) (r.w 6) (r.w 5) ∧ N.mem (r.w 8) (r.w 5) ∧
      (∀ q, N.mem q (r.w 5) → Entry_d N q (r.w 8) (r.w 6)) ∧ ∃ A t w,
        Check_d N (r.w 8) (r.w 0) t ∧ Check_d N (r.w 8) A w ∧
        ∀ τ, N.mem τ (r.w 9) → Fn_name_d N (r.w 5) (r.w 6) (r.w 5) (r.w 8) t w τ := by
  let N := smdl_structure_l I (R := R) source.1.2.1
  let N' := smdl_structure_l I (R := r.W) r.target.1.2.1
  let φ : Formula 1 9 := set[9] ⟪
    ⌜prod_m⌝ₚ(⌜(.bound 0 : Term 9)⌝ₛ,⌜(.bound 1 : Term 9)⌝ₛ,⌜(.bound 2 : Term 9)⌝ₛ,
      ⌜(.bound 3 : Term 9)⌝ₛ,⌜(.bound 4 : Term 9)⌝ₛ,⌜(.bound 5 : Term 9)⌝ₛ) ∧
    ⌜cond_order_m⌝ₚ(⌜(.bound 4 : Term 9)⌝ₛ,⌜(.bound 5 : Term 9)⌝ₛ,⌜(.bound 4 : Term 9)⌝ₛ) ∧
    ⌜(.bound 6 : Term 9)⌝ₛ ∈ ⌜(.bound 4 : Term 9)⌝ₛ ∧
    (∀ q ∈ ⌜(.bound 4 : Term 9)⌝ₛ, ⌜entry_m⌝ₚ(q,⌜(.bound 6 : Term 9)⌝ₛ,⌜(.bound 5 : Term 9)⌝ₛ)) ∧
    (∃ A t w, ⌜check_m⌝ₚ(⌜(.bound 6 : Term 9)⌝ₛ,⌜(.bound 7 : Term 9)⌝ₛ,t) ∧
      ⌜check_m⌝ₚ(⌜(.bound 6 : Term 9)⌝ₛ,A,w) ∧
      (∀ τ ∈ ⌜(.bound 8 : Term 9)⌝ₛ, ⌜fn_name_m⌝ₚ(⌜(.bound 4 : Term 9)⌝ₛ,⌜(.bound 5 : Term 9)⌝ₛ,
        ⌜(.bound 4 : Term 9)⌝ₛ,⌜(.bound 6 : Term 9)⌝ₛ,t,w,τ)))⟫
  let ρ : Env N 9 := ⟨fun i => [p.Q,p.T,p.P,p.U,p.C,p.R,p.c,ω,p.N].get i,fun _ => p.C⟩
  let η : Env N' 9 := ⟨fun i => [r.w 1,r.w 2,r.w 3,r.w 4,r.w 5,r.w 6,r.w 8,r.w 0,r.w 9].get i,fun _ => r.w 5⟩
  have truth : Formula.satisfies ρ φ := by
    simp only [φ,Formula.satisfies_conj_iff,prod_sat_l native,cond_order_sat_l native.1,Formula.satisfies_mem_iff,
      Formula.satisfies_forallMem_iff,entry_sat_l N native.1,Formula.satisfies_exists_iff,
      check_sat_l N native.1,fn_name_sat_l native.1,Definitional.Term.eval_weaken]
    refine ⟨p.product,p.product_order,p.base_mem,p.top,A,p.t,p.w,p.check_omega,p.check_letters,?_⟩
    intro τ hτ
    have family := (p.function_family τ).mp hτ
    exact ⟨check_name_l N (check_range_l N native) p.base_mem p.check_omega,
      check_name_l N (check_range_l N native) p.base_mem p.check_letters,⟨p.W,family.1,p.function_pool.closed⟩,
      family.2 p.c p.base_mem (fun eq => KP.mem_irrefl_d (ZF.modelsKP native) p.C (eq ▸ p.base_mem))⟩
  have points : ∀ i, Rd_entry_d (ρ.bound i).val (η.bound i).val r.j :=
    Fin.cases (r.images 1) (Fin.cases (r.images 2) (Fin.cases (r.images 3) (Fin.cases (r.images 4)
      (Fin.cases (r.images 5) (Fin.cases (r.images 6) (Fin.cases (r.images 8)
        (Fin.cases (r.images 0) (Fin.cases (r.images 9) (fun i => Fin.elim0 i)))))))))
  have result := (smap_source_l I hZF hw source.1 r.target.1 r.map φ
    (by simp -implicitDefEqProofs [φ,Definitional.Formula.FreeClosed,prod_m_freeClosed,cond_order_m_freeClosed,check_m_freeClosed])
    ρ η points).mp truth
  simp only [φ,Formula.satisfies_conj_iff,prod_sat_l r.native,cond_order_sat_l r.native.1,Formula.satisfies_mem_iff,
    Formula.satisfies_forallMem_iff,entry_sat_l N' r.native.1,Formula.satisfies_exists_iff,
    check_sat_l N' r.native.1,fn_name_sat_l r.native.1,Definitional.Term.eval_weaken] at result
  exact result

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 分支小扩张中的实际命中与大泛型结果

保存同一规范地映射、大条件尾列及环境中的滤子集合。泛型性量化小扩张
自己的全部稠密集；名字覆盖使用该分支已运输的规范名字族。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal Descriptive Model.Forcing.Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

def Ag_hits_d {Ω z c X Q G b f : M.Domain} {v : Fin 19 → M.Domain}
    (r : Ag_branch_d hZF Ω z c X Q G b v f) (H : M.Domain) : Prop :=
  let N := smdl_structure_l I (R := r.W) r.target.1.2.1
  let E := extension_l N r.native (r.w 1) (r.w 2) (r.w 1) (fun q => M.mem q.val H)
  ∃ e : N.Domain → E.Domain, Function.Injective e ∧
    (∀ a y, E.mem y (e a) ↔ ∃ t, N.mem t a ∧ e t = y) ∧
    (∀ a t, Check_d N (r.w 7) a t → Qval_d N (r.w 1) (r.w 2) (r.w 1) (fun q => M.mem q.val H) t (e a)) ∧
    ∀ i d l p, Entry_d M i.val d.val r.a → Entry_d M l.val p.val r.u → N.SuccessorOf l i →
      ∃ D : E.Domain, Qval_d N (r.w 1) (r.w 2) (r.w 1) (fun q => M.mem q.val H) d D ∧ E.mem (e p) D

structure Ag_tail_d {Ω z c X Q G b f : M.Domain} {v : Fin 19 → M.Domain}
    (r : Ag_branch_d hZF Ω z c X Q G b v f) (t K : M.Domain) : Prop where
  function : Fn0_d Ω (r.w 3).val t
  members : ∀ a, M.mem a K ↔ M.mem a (r.w 3).val ∧ ∃ i p, Entry_d M i p t ∧ Entry_d M p a (r.w 4).val
  filter : Gset_d (r.w 3).val (r.w 4).val (r.w 3).val (r.w 7).val K
  chain : ∀ i j a q, M.mem i j → Entry_d M i a t → Entry_d M j q t → Entry_d M q a (r.w 4).val
  follow : ∀ i l p : (smdl_structure_l I (R := r.W) r.target.1.2.1).Domain,
    (smdl_structure_l I (R := r.W) r.target.1.2.1).SuccessorOf l i →
      (Entry_d M l.val p.val r.u ↔ Entry_d M i.val p.val t)

def Ag_big_d {Ω z c X Q G b f : M.Domain} {v : Fin 19 → M.Domain}
    (r : Ag_branch_d hZF Ω z c X Q G b v f) (H : M.Domain) : Prop :=
  let N := smdl_structure_l I (R := r.W) r.target.1.2.1
  let E := extension_l N r.native (r.w 1) (r.w 2) (r.w 1) (fun q => M.mem q.val H)
  ∃ e : N.Domain → E.Domain, Function.Injective e ∧
    (∀ a y, E.mem y (e a) ↔ ∃ p, N.mem p a ∧ e p = y) ∧
    (∀ a t, Check_d N (r.w 7) a t → Qval_d N (r.w 1) (r.w 2) (r.w 1) (fun q => M.mem q.val H) t (e a)) ∧
    (∀ D, Dense_set_d E (e (r.w 3)) (e (r.w 4)) (e (r.w 3)) D →
      ∃ d, N.mem d (r.w 12) ∧ Qval_d N (r.w 1) (r.w 2) (r.w 1) (fun q => M.mem q.val H) d D) ∧
    ∃ t K, Ag_tail_d hZF r t K ∧
      Generic_d E (e (r.w 3)) (e (r.w 4)) (e (r.w 3)) (Em_generic_d e (fun p => M.mem p.val K))

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 分支模型内同一小力迫的序、顶元与实际名字

这四项直接运输原模型中的同一公式；稠密名字来自已构造的闭名字库。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal Descriptive Model.Forcing.Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Ag_branch_d.small_data_l {Ω c X R z Q G b f : M.Domain} (hw : M.IsOmega Ω)
    (source : Smem_d I c X R)
    (native : (smdl_structure_l I (R := R) source.1.2.1).Models ZF)
    {ω κ δ A : (smdl_structure_l I (R := R) source.1.2.1).Domain}
    {p : Ag_forcing_d native ω κ δ A} (s : Ag_system_d native p)
    (r : Ag_branch_d hZF Ω z c X Q G b (fun i => (s.aux_params_l native i).val) f) :
    let N := smdl_structure_l I (R := r.W) r.target.1.2.1
    Cond_order_d N (r.w 1) (r.w 2) (r.w 1) ∧ N.mem (r.w 7) (r.w 1) ∧
      (∀ q, N.mem q (r.w 1) → Entry_d N q (r.w 7) (r.w 2)) ∧
      ∀ d, N.mem d (r.w 12) → Name_d N (r.w 1) d := by
  let N := smdl_structure_l I (R := R) source.1.2.1
  let N' := smdl_structure_l I (R := r.W) r.target.1.2.1
  let φ : Formula 1 4 := set[4] ⟪
    ⌜cond_order_m⌝ₚ(⌜(.bound 0 : Term 4)⌝ₛ,⌜(.bound 1 : Term 4)⌝ₛ,⌜(.bound 0 : Term 4)⌝ₛ) ∧
    ⌜(.bound 2 : Term 4)⌝ₛ ∈ ⌜(.bound 0 : Term 4)⌝ₛ ∧
    (∀ q ∈ ⌜(.bound 0 : Term 4)⌝ₛ, ⌜entry_m⌝ₚ(q,⌜(.bound 2 : Term 4)⌝ₛ,⌜(.bound 1 : Term 4)⌝ₛ)) ∧
    (∀ d ∈ ⌜(.bound 3 : Term 4)⌝ₛ, ⌜name_m⌝ₚ(⌜(.bound 0 : Term 4)⌝ₛ,d))⟫
  let ρ : Env N 4 := ⟨fun i => [p.Q,p.T,p.b,p.D].get i,fun _ => p.Q⟩
  let η : Env N' 4 := ⟨fun i => [r.w 1,r.w 2,r.w 7,r.w 12].get i,fun _ => r.w 1⟩
  have truth : Formula.satisfies ρ φ := by
    simp only [φ,Formula.satisfies_conj_iff,cond_order_sat_l native.1,Formula.satisfies_mem_iff,
      Formula.satisfies_forallMem_iff,entry_sat_l N native.1,name_sat_l N native.1,Definitional.Term.eval_weaken]
    exact ⟨p.small_order,p.small_base,fun q hq => (p.small_edges q p.b).mpr
      ⟨hq,p.small_base,fun x hx => (p.empty x hx).elim⟩,
      fun d hd => ⟨p.Wd,((p.dense_family d).mp hd).1,p.dense_pool.closed⟩⟩
  have transported := (smap_source_l I hZF hw source.1 r.target.1 r.map φ
    (by simp -implicitDefEqProofs [φ,Definitional.Formula.FreeClosed,cond_order_m_freeClosed,name_m_freeClosed])
    ρ η (Fin.cases (r.images 1) (Fin.cases (r.images 2)
      (Fin.cases (r.images 7) (Fin.cases (r.images 12) (fun i => Fin.elim0 i)))))).mp truth
  simp only [φ,Formula.satisfies_conj_iff,cond_order_sat_l r.native.1,Formula.satisfies_mem_iff,
    Formula.satisfies_forallMem_iff,entry_sat_l N' r.native.1,name_sat_l N' r.native.1,Definitional.Term.eval_weaken] at transported
  exact transported

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 规范名字族覆盖分支小扩张的全部大稠密集

完整初等性运输名字库及其全局稠密成员方程。目标重新应用实际名字正规化
与修补定理，因此覆盖其全部扩张稠密集，而非仅覆盖原根的旧稠密集。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal Descriptive Model.Forcing.Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Ag_branch_d.dense_data_l {Ω c X R z Q G b f : M.Domain} (hw : M.IsOmega Ω)
    (source : Smem_d I c X R)
    (native : (smdl_structure_l I (R := R) source.1.2.1).Models ZF)
    {ω κ δ A : (smdl_structure_l I (R := R) source.1.2.1).Domain}
    {p : Ag_forcing_d native ω κ δ A} (s : Ag_system_d native p)
    (r : Ag_branch_d hZF Ω z c X Q G b (fun i => (s.aux_params_l native i).val) f) :
    let N := smdl_structure_l I (R := r.W) r.target.1.2.1
    Cond_order_d N (r.w 3) (r.w 4) (r.w 3) ∧ ∃ a t W,
      Check_d N (r.w 7) (r.w 3) a ∧ Check_d N (r.w 7) (r.w 4) t ∧
      Name_pool_d N (r.w 1) a a W ∧ Dn_family_d (r.w 1) (r.w 2) (r.w 1) a t W (r.w 12) := by
  let N := smdl_structure_l I (R := R) source.1.2.1
  let N' := smdl_structure_l I (R := r.W) r.target.1.2.1
  let φ : Formula 1 6 := set[6] ⟪
    ⌜cond_order_m⌝ₚ(⌜(.bound 2 : Term 6)⌝ₛ,⌜(.bound 3 : Term 6)⌝ₛ,⌜(.bound 2 : Term 6)⌝ₛ) ∧
    (∃ a t W, ⌜check_m⌝ₚ(⌜(.bound 4 : Term 6)⌝ₛ,⌜(.bound 2 : Term 6)⌝ₛ,a) ∧
      ⌜check_m⌝ₚ(⌜(.bound 4 : Term 6)⌝ₛ,⌜(.bound 3 : Term 6)⌝ₛ,t) ∧
      ⌜name_pool_m⌝ₚ(⌜(.bound 0 : Term 6)⌝ₛ,a,a,W) ∧
      ⌜dn_family_m⌝ₚ(⌜(.bound 0 : Term 6)⌝ₛ,⌜(.bound 1 : Term 6)⌝ₛ,⌜(.bound 0 : Term 6)⌝ₛ,
        a,t,W,⌜(.bound 5 : Term 6)⌝ₛ))⟫
  let ρ : Env N 6 := ⟨fun i => [p.Q,p.T,p.P,p.U,p.b,p.D].get i,fun _ => p.Q⟩
  let η : Env N' 6 := ⟨fun i => [r.w 1,r.w 2,r.w 3,r.w 4,r.w 7,r.w 12].get i,fun _ => r.w 1⟩
  have truth : Formula.satisfies ρ φ := by
    simp only [φ,Formula.satisfies_conj_iff,Formula.satisfies_exists_iff,cond_order_sat_l native.1,
      check_sat_l N native.1,name_pool_sat_l N native.1,dn_family_sat_l native.1,Definitional.Term.eval_weaken]
    exact ⟨p.big_order,p.dp,p.du,p.Wd,p.check_big,p.check_order,p.dense_pool,p.dense_family⟩
  have transported := (smap_source_l I hZF hw source.1 r.target.1 r.map φ
    (by simp -implicitDefEqProofs [φ,Definitional.Formula.FreeClosed,cond_order_m_freeClosed,
      check_m_freeClosed,name_pool_m_freeClosed]) ρ η
    (Fin.cases (r.images 1) (Fin.cases (r.images 2) (Fin.cases (r.images 3)
      (Fin.cases (r.images 4) (Fin.cases (r.images 7) (Fin.cases (r.images 12) (fun i => Fin.elim0 i)))))))).mp truth
  simp only [φ,Formula.satisfies_conj_iff,Formula.satisfies_exists_iff,cond_order_sat_l r.native.1,
    check_sat_l N' r.native.1,name_pool_sat_l N' r.native.1,dn_family_sat_l r.native.1,Definitional.Term.eval_weaken] at transported
  exact transported

theorem Ag_branch_d.dense_cover_l {Ω c X R z Q G b f H : M.Domain} (hw : M.IsOmega Ω)
    (source : Smem_d I c X R)
    (native : (smdl_structure_l I (R := R) source.1.2.1).Models ZF)
    {ω κ δ A : (smdl_structure_l I (R := R) source.1.2.1).Domain}
    {p : Ag_forcing_d native ω κ δ A} (s : Ag_system_d native p)
    (r : Ag_branch_d hZF Ω z c X Q G b (fun i => (s.aux_params_l native i).val) f)
    (generic : Generic_d (smdl_structure_l I (R := r.W) r.target.1.2.1) (r.w 1) (r.w 2) (r.w 1) (fun q => M.mem q.val H))
    (e : (smdl_structure_l I (R := r.W) r.target.1.2.1).Domain →
      (extension_l _ r.native (r.w 1) (r.w 2) (r.w 1) (fun q => M.mem q.val H)).Domain)
    (checks : ∀ a t, Check_d _ (r.w 7) a t → Qval_d _ (r.w 1) (r.w 2) (r.w 1) (fun q => M.mem q.val H) t (e a)) :
    ∀ K, Dense_set_d (extension_l _ r.native (r.w 1) (r.w 2) (r.w 1) (fun q => M.mem q.val H))
      (e (r.w 3)) (e (r.w 4)) (e (r.w 3)) K →
      ∃ d, (smdl_structure_l I (R := r.W) r.target.1.2.1).mem d (r.w 12) ∧
        Qval_d _ (r.w 1) (r.w 2) (r.w 1) (fun q => M.mem q.val H) d K := by
  let N := smdl_structure_l I (R := r.W) r.target.1.2.1
  obtain ⟨O,hb,top,_⟩ := r.small_data_l hZF hw source native s
  obtain ⟨L,a,t,W,ca,ct,pool,family⟩ := r.dense_data_l hZF hw source native s
  have hn := check_name_l N (check_range_l N r.native) hb ct
  have pre q hq nz := check_preord_force_l O r.native hb ca ct ⟨L.refl,L.trans⟩ ⟨hq,nz,top q hq⟩
  intro K dense
  exact pool.dense_cover_l O r.native hn pre family generic (checks _ _ ca) (checks _ _ ct) dense

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 分支第二辅助图的大条件尾列及实际滤子

去掉首项函数名字后，全部取值是同一大力迫条件。相邻加强由原生分支规则
读出；内部可定义链归纳生成递降列的上闭包。该滤子是环境中的实际集合。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal Descriptive Model.Forcing.Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Ag_branch_d.big_filter_l {Ω c X R z Q G b f : M.Domain} (hw : M.IsOmega Ω)
    (source : Smem_d I c X R)
    (native : (smdl_structure_l I (R := R) source.1.2.1).Models ZF)
    {ω κ δ A : (smdl_structure_l I (R := R) source.1.2.1).Domain}
    {p : Ag_forcing_d native ω κ δ A} (s : Ag_system_d native p)
    (r : Ag_branch_d hZF Ω z c X Q G b (fun i => (s.aux_params_l native i).val) f) :
    ∃ t K, Ag_tail_d hZF r t K := by
  let N := smdl_structure_l I (R := r.W) r.target.1.2.1
  have inj : Function.Injective (Subtype.val : N.Domain → M.Domain) := fun _ _ eq => Subtype.ext eq
  have full := smem_full_l I r.target r.transitive
  have member {a b : N.Domain} : M.mem a.val b.val ↔ N.mem a b := image_member_l (M := N) (N := M) Subtype.val inj full
  have edge := image_entry_iff_l Subtype.val inj full (KP.exists_pair (ZF.modelsKP r.native)) hZF.1
  have empty x (hx : M.mem x (r.w 7).val) : False :=
    (full (r.w 7) x).mp hx |>.elim fun a ha => r.frame.empty a ha.1
  have positive {i a} (hi : M.mem i Ω) (nz : i ≠ (r.w 7).val) (ia : Entry_d M i a r.u) : M.mem a (r.w 3).val := by
    obtain ⟨i₀,_,eqi⟩ := (full (r.w 0) i).mp (r.omega.symm ▸ hi)
    obtain ⟨a₀,_,eqa⟩ := (full (r.w 18) a).mp (r.second.bound_l ia).2
    subst i a
    exact member.mpr ((r.read.names i₀ a₀ ia).2 (fun eq => nz (congrArg Subtype.val eq)))
  obtain ⟨_,t,_,ft,cons⟩ := tail_omega_l I hZF hw empty (fn0_function_l (ZF.modelsKP hZF) r.second)
  have typed : Fn0_d Ω (r.w 3).val t := by
    apply (fn0_of_function_l (ZF.modelsKP hZF) ft).retarget_l
    intro i a ia
    have hi := ft.input_mem_of_pairMember ia
    obtain ⟨j,succ,hj⟩ := hw.1.2 i hi
    exact positive hj (fun eq => empty i (eq ▸ succ.predecessor_mem))
      ((cons.successor_l I hZF hw empty hi succ).mpr ia)
  have step i j a q (succ : M.SuccessorOf j i) (ia : Entry_d M i a t) (jq : Entry_d M j q t) :
      Entry_d M q a (r.w 4).val := by
    have hi := (typed.bound_l ia).1
    have hj := (typed.bound_l jq).1
    obtain ⟨k,next,hk⟩ := hw.1.2 j hj
    have ja := (cons.successor_l I hZF hw empty hi succ).mpr ia
    have kq := (cons.successor_l I hZF hw empty hj next).mpr jq
    have nz : j ≠ (r.w 7).val := fun eq => empty i (eq ▸ succ.predecessor_mem)
    obtain ⟨j₀,_,eqj⟩ := (full (r.w 0) j).mp (r.omega.symm ▸ hj)
    obtain ⟨k₀,_,eqk⟩ := (full (r.w 0) k).mp (r.omega.symm ▸ hk)
    obtain ⟨a₀,_,eqa⟩ := (full (r.w 3) a).mp (typed.bound_l ia).2
    obtain ⟨q₀,_,eqq⟩ := (full (r.w 3) q).mp (typed.bound_l jq).2
    subst j k a q
    exact (edge q₀ a₀ (r.w 4)).mp (r.read.decreasing k₀ j₀ q₀ a₀ kq ja
      ((image_successor_iff_l (ZF.modelsKP r.native) hZF.1 Subtype.val inj full).mpr next)
      (fun eq => nz (congrArg Subtype.val eq)))
  obtain ⟨O,_⟩ := r.dense_data_l hZF hw source native s
  have order := image_cond_order_l (ZF.modelsKP r.native) hZF.1 Subtype.val inj full O
  let ρ : Env M 1 := ⟨fun _ => (r.w 4).val,fun _ => (r.w 4).val⟩
  let φ : BinarySchema 1 := { body := entry_m .newest (.bound 1) (.bound 2) }
  have sat a q : φ.denote ρ a q ↔ Entry_d M q a (r.w 4).val := entry_sat_l M hZF.1 ..
  have chain i j a q (ij : M.mem i j) (ia : Entry_d M i a t) (jq : Entry_d M j q t) : Entry_d M q a (r.w 4).val :=
    (sat a q).mp (ZF.rel_chain_l I hZF φ ρ hw (fn0_function_l (ZF.modelsKP hZF) typed)
      (fun a q b ha hq hb aq qb => (sat a b).mpr (order.trans b q a hb hq ha ((sat q b).mp qb) ((sat a q).mp aq)))
      (fun i j a q succ ia jq => (sat a q).mpr (step i j a q succ ia jq)) i j a q ij ia jq)
  obtain ⟨K,members,filter,_⟩ := sequence_filter_l hZF order hw (fn0_function_l (ZF.modelsKP hZF) typed) step
    (D := (r.w 7).val) (fun E hE => (empty E hE).elim)
  refine ⟨t,K,⟨typed,members,filter,chain,?_⟩⟩
  intro i l a li
  have succ := image_successor_l (hEN := hZF.1) Subtype.val inj full r.native.1 li
  constructor
  · intro la
    have hi := hw.transitive (ZF.modelsKP hZF) l.val (r.second.bound_l la).1 i.val succ.predecessor_mem
    exact (cons.successor_l I hZF hw empty hi succ).mp la
  · intro ia
    exact (cons.successor_l I hZF hw empty (typed.bound_l ia).1 succ).mpr ia

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 分支大滤子在同一小扩张中泛型

任意大稠密集先取同一名字族中的代表，满射辅助图给出它的真实出现轮号。
紧随的大条件属于已构造滤子，并由实际命中定理属于该稠密集。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal Descriptive Model.Forcing.Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Ag_branch_d.big_generic_l {Ω c X R z Q G b f H : M.Domain} (hw : M.IsOmega Ω)
    (source : Smem_d I c X R)
    (native : (smdl_structure_l I (R := R) source.1.2.1).Models ZF)
    {ω κ δ A : (smdl_structure_l I (R := R) source.1.2.1).Domain}
    {p : Ag_forcing_d native ω κ δ A} (s : Ag_system_d native p)
    (r : Ag_branch_d hZF Ω z c X Q G b (fun i => (s.aux_params_l native i).val) f)
    (generic : Generic_d (smdl_structure_l I (R := r.W) r.target.1.2.1) (r.w 1) (r.w 2) (r.w 1) (fun q => M.mem q.val H))
    (hit : Ag_hits_d hZF r H) : Ag_big_d hZF r H := by
  let N := smdl_structure_l I (R := r.W) r.target.1.2.1
  let H₀ := fun q : N.Domain => M.mem q.val H
  let E := extension_l N r.native (r.w 1) (r.w 2) (r.w 1) H₀
  obtain ⟨O,_,_,_⟩ := r.small_data_l hZF hw source native s
  have hE : E.Models ZF := preserves_zf_l O r.native generic
  obtain ⟨L,_⟩ := r.dense_data_l hZF hw source native s
  obtain ⟨e,ei,ef,checks,hits⟩ := hit
  have cover := r.dense_cover_l hZF hw source native s generic e checks
  obtain ⟨t,K,tail⟩ := r.big_filter_l hZF hw source native s
  have inj : Function.Injective (Subtype.val : N.Domain → M.Domain) := fun _ _ eq => Subtype.ext eq
  have full := smem_full_l I r.target r.transitive
  have member {a b : N.Domain} : M.mem a.val b.val ↔ N.mem a b := image_member_l (M := N) (N := M) Subtype.val inj full
  have allhits : ∀ D, Dense_set_d E (e (r.w 3)) (e (r.w 4)) (e (r.w 3)) D →
      ∃ a : N.Domain, M.mem a.val K ∧ E.mem (e a) D := by
    intro D dense
    obtain ⟨d,hd,vd⟩ := cover D dense
    obtain ⟨i,hi,id⟩ := r.onto d.val (member.mpr hd)
    obtain ⟨i₀,hi₀,eqi⟩ := (full (r.w 0) i).mp (r.omega.symm ▸ hi)
    subst i
    obtain ⟨l,li,hl⟩ := r.frame.omega.1.2 i₀ hi₀
    have hl' : M.mem l.val Ω := by simpa only [r.omega] using (show M.mem l.val (r.w 0).val from member.mpr hl)
    obtain ⟨a,_,la⟩ := r.second.2.1 l.val hl'
    obtain ⟨a₀,_,eqa⟩ := (full (r.w 18) a).mp (r.second.bound_l la).2
    subst a
    have ne : l ≠ r.w 7 := fun eq => r.frame.empty i₀ (eq ▸ li.predecessor_mem)
    have ha := (r.read.names l a₀ la).2 ne
    have ia := (tail.follow i₀ l a₀ li).mp la
    have accepted := (tail.members a₀.val).mpr ⟨member.mpr ha,i₀.val,a₀.val,ia,
      (image_entry_iff_l Subtype.val inj full (KP.exists_pair (ZF.modelsKP r.native)) hZF.1 a₀ a₀ (r.w 4)).mp (L.refl a₀ ha)⟩
    obtain ⟨D',vd',aD⟩ := hits i₀ d l a₀ id la li
    exact ⟨a₀,accepted,qval_unique_l vd' vd ▸ aD⟩
  have big := tail.filter.extension_generic_l r.native hZF.1 hE Subtype.val inj full e ei ef L allhits
  exact ⟨e,ei,ef,checks,cover,t,K,tail,big⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 同一 H 与大滤子 K 诱导实际积泛型

接受条件精确为坐标分别属于 H、K 的原积条件；规范嵌入的单射性消去
第二坐标名字商的中间表示，供同一原对局上的值约束使用。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal Descriptive Model.Forcing.Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

def Ag_prod_d {Ω z c X Q G b f : M.Domain} {v : Fin 19 → M.Domain}
    (r : Ag_branch_d hZF Ω z c X Q G b v f) (H K : M.Domain)
    (p : (smdl_structure_l I (R := r.W) r.target.1.2.1).Domain) : Prop :=
  (smdl_structure_l I (R := r.W) r.target.1.2.1).mem p (r.w 5) ∧ ∃ q a,
    KPair_d (smdl_structure_l I (R := r.W) r.target.1.2.1) p q a ∧ M.mem q.val H ∧ M.mem a.val K

theorem Ag_branch_d.product_generic_l {Ω c X R z Q G b f H : M.Domain} (hw : M.IsOmega Ω)
    (source : Smem_d I c X R)
    (native : (smdl_structure_l I (R := R) source.1.2.1).Models ZF)
    {ω κ δ A : (smdl_structure_l I (R := R) source.1.2.1).Domain}
    {p : Ag_forcing_d native ω κ δ A} (s : Ag_system_d native p)
    (r : Ag_branch_d hZF Ω z c X Q G b (fun i => (s.aux_params_l native i).val) f)
    (small : Generic_d (smdl_structure_l I (R := r.W) r.target.1.2.1) (r.w 1) (r.w 2) (r.w 1) (fun q => M.mem q.val H))
    (big : Ag_big_d hZF r H) :
    let N := smdl_structure_l I (R := r.W) r.target.1.2.1
    let E := extension_l N r.native (r.w 1) (r.w 2) (r.w 1) (fun q => M.mem q.val H)
    ∃ e : N.Domain → E.Domain, Function.Injective e ∧
      (∀ a y, E.mem y (e a) ↔ ∃ p, N.mem p a ∧ e p = y) ∧
      (∀ a t, Check_d N (r.w 7) a t → Qval_d N (r.w 1) (r.w 2) (r.w 1) (fun q => M.mem q.val H) t (e a)) ∧
      (∀ D, Dense_set_d E (e (r.w 3)) (e (r.w 4)) (e (r.w 3)) D →
        ∃ d, N.mem d (r.w 12) ∧ Qval_d N (r.w 1) (r.w 2) (r.w 1) (fun q => M.mem q.val H) d D) ∧
      ∃ t K, Ag_tail_d hZF r t K ∧ Generic_d E (e (r.w 3)) (e (r.w 4)) (e (r.w 3)) (Em_generic_d e (fun p => M.mem p.val K)) ∧
        Generic_d N (r.w 5) (r.w 6) (r.w 5) (Ag_prod_d hZF r H K) := by
  let N := smdl_structure_l I (R := r.W) r.target.1.2.1
  obtain ⟨e,ei,ef,checks,cover,t,K,tail,generic⟩ := big
  obtain ⟨O,hb,top,_⟩ := r.small_data_l hZF hw source native s
  obtain ⟨L,_⟩ := r.dense_data_l hZF hw source native s
  obtain ⟨product,OP,_⟩ := r.product_data_l hZF hw source native s
  obtain ⟨q,hq⟩ := small.inhabited
  have base := small.upward q (r.w 7) hq hb (top q (small.proper q hq).1)
  have hE := preserves_zf_l O r.native small
  have order := image_cond_order_l (ZF.modelsKP r.native) hE.1 e ei ef L
  obtain ⟨prod,_⟩ := product.extension_l r.native O L OP top small base e checks (fun _ _ _ _ => Iff.rfl) order generic
  have same : Prod_generic_d r.native (r.w 5) e (Em_generic_d e (fun p : N.Domain => M.mem p.val K)) = Ag_prod_d hZF r H K := by
    funext p
    apply propext
    constructor
    · rintro ⟨hp,q,a,pair,hq,a',ha',eq⟩
      exact ⟨hp,q,a,pair,hq,ei eq ▸ ha'⟩
    · rintro ⟨hp,q,a,pair,hq,ha⟩
      exact ⟨hp,q,a,pair,hq,a,ha,rfl⟩
  exact ⟨e,ei,ef,checks,cover,t,K,tail,generic,same ▸ prod⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 同一偶数回合的积条件共尾且保留指定旧函数值

先选一个同时越过大条件见证和旧实数坐标的内部轮号，再在 H 中取小条件
共尾项。原时刻 2k 越过二者；大尾列递降使该时刻的大条件同时加强原积条件。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal Descriptive Model.Forcing.Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Ag_branch_d.value_cofinal_l {Ω c X R z Q G b f x H qs t K : M.Domain} (hΩ : M.IsOmega Ω)
    (source : Smem_d I c X R) (xt : M.TransitiveSet X)
    (native : (smdl_structure_l I (R := R) source.1.2.1).Models ZF)
    {ω κ δ A : (smdl_structure_l I (R := R) source.1.2.1).Domain}
    {p : Ag_forcing_d native ω κ δ A} (s : Ag_system_d native p)
    (hw : (smdl_structure_l I (R := R) source.1.2.1).IsOmega ω) (eqω : ω.val = Ω)
    (inh : ∃ y, (smdl_structure_l I (R := R) source.1.2.1).mem y A)
    (r : Ag_branch_d hZF Ω z c X Q G b (fun i => (s.aux_params_l native i).val) f)
    (sub : M.MemberSubset H p.Q.val) (trace : Ag_trace_d hZF Ω A.val s.A.val s.F₀.val s.R₀.val f x H)
    (fq : Fn0_d Ω p.Q.val qs)
    (coords : ∀ k n a y q, M.mem k Ω → M.IsOrdinalAddition I n k k → Entry_d M n a f →
      KPair_d M a y q → Entry_d M k y x ∧ Entry_d M k q qs)
    (cofinal : ∀ q, M.mem q H → ∀ i, M.mem i Ω → ∃ k u, M.mem i k ∧ Entry_d M k u qs ∧ Entry_d M u q p.T.val)
    (tail : Ag_tail_d hZF r t K)
    {τ i k a y q : (smdl_structure_l I (R := r.W) r.target.1.2.1).Domain}
    (head : Entry_d M (r.w 7).val τ.val r.u) (old : Entry_d M i.val a.val f)
    (pair : KPair_d (smdl_structure_l I (R := r.W) r.target.1.2.1) a y q)
    (hk : (smdl_structure_l I (R := r.W) r.target.1.2.1).mem k (r.w 0))
    (add : (smdl_structure_l I (R := r.W) r.target.1.2.1).IsOrdinalAddition (kp_pair_l (ZF.modelsKP r.native)) i k k) :
    ∀ v, Ag_prod_d hZF r H K v → ∃ w, Ag_prod_d hZF r H K w ∧
      Entry_d (smdl_structure_l I (R := r.W) r.target.1.2.1) w v (r.w 6) ∧ ∃ q p,
        KPair_d (smdl_structure_l I (R := r.W) r.target.1.2.1) w q p ∧
          Ag_value_d (r.w 5) (r.w 6) (r.w 8) τ q p k y := by
  let N := smdl_structure_l I (R := R) source.1.2.1
  let L := smdl_structure_l I (R := r.W) r.target.1.2.1
  have srcInj : Function.Injective (Subtype.val : N.Domain → M.Domain) := fun _ _ eq => Subtype.ext eq
  have srcFull := smem_full_l I source xt
  have game := s.source.image_l native hZF Subtype.val srcInj srcFull hw (eqω.symm ▸ hΩ)
  have game : Ag_game_d hZF Ω A.val p.Q.val p.T.val s.E.val s.B.val s.A.val s.F₀.val s.R₀.val := by
    simpa only [eqω] using! game
  have inj : Function.Injective (Subtype.val : L.Domain → M.Domain) := fun _ _ eq => Subtype.ext eq
  have full := smem_full_l I r.target r.transitive
  have member {a b : L.Domain} : M.mem a.val b.val ↔ L.mem a b := image_member_l (M := L) (N := M) Subtype.val inj full
  have edge := image_entry_iff_l Subtype.val inj full (KP.exists_pair (ZF.modelsKP r.native)) hZF.1
  have empty z (hz : M.mem z (r.w 7).val) : False :=
    (full (r.w 7) z).mp hz |>.elim fun a ha => r.frame.empty a ha.1
  obtain ⟨eqQ,smallEdge⟩ := r.small_order_l hZF hΩ source xt native s inh
  obtain ⟨bigOrder,_⟩ := r.dense_data_l hZF hΩ source native s
  have order := image_cond_order_l (ZF.modelsKP r.native) hZF.1 Subtype.val inj full bigOrder
  obtain ⟨product,_,_⟩ := r.product_data_l hZF hΩ source native s
  rintro v ⟨hv,q₀,p₀,pair₀,qH,pK⟩
  obtain ⟨hp₀,j,u,ju,up⟩ := (tail.members p₀.val).mp pK
  obtain ⟨l,jl,hl⟩ := hΩ.1.2 j (tail.function.bound_l ju).1
  have hi := (trace.play.bound_l old).1
  -- 内部轮号越过大尾列见证及旧实数时刻，再用 H 中的逐尾共尾性选轮。
  have upper : ∃ m, M.mem m Ω ∧ (M.mem l m ∨ l = m) ∧ (M.mem i.val m ∨ i.val = m) := by
    rcases (hΩ.isOrdinal (ZF.modelsKP hZF)).wellOrder.linear.compare l hl i.val hi with eq | li | il
    · exact ⟨l,hl,Or.inr rfl,Or.inr (hZF.1.eq_of_same_members l i.val eq).symm⟩
    · exact ⟨i.val,hi,Or.inl li,Or.inr rfl⟩
    · exact ⟨l,hl,Or.inr rfl,Or.inl il⟩
  obtain ⟨m,hm,lm,im⟩ := upper
  obtain ⟨k',q',mk,kq,qq₀⟩ := cofinal q₀.val qH m hm
  have hk' := (fq.bound_l kq).1
  obtain ⟨y',_,ky⟩ := trace.real.2.1 k' hk'
  obtain ⟨n,a',sum,na,pair'⟩ := game.coordinate_read_l hZF hΩ trace.play trace.branch trace.real fq coords ky kq
  have hn := (trace.play.bound_l na).1
  have qH' := trace.small n a' y' q' na pair' ⟨k',hk',sum⟩
  have mn := ZF.ordinalAddition_left_member_mem_value hZF I
    (hΩ.members_areOrdinals (ZF.modelsKP hZF) k' hk') (hΩ.members_areOrdinals (ZF.modelsKP hZF) k' hk') mk sum
  have before {a} (am : M.mem a m ∨ a = m) : M.mem a n :=
    am.elim (fun am => (hΩ.members_areOrdinals (ZF.modelsKP hZF) n hn).transitive m mn a am) (fun eq => eq.symm ▸ mn)
  have ln := before lm
  have inn := before im
  obtain ⟨n₁,hn₁,eqn⟩ := (full (r.w 0) n).mp (r.omega.symm ▸ hn)
  obtain ⟨a₁,_,eqa⟩ := (full (r.w 10) a').mp (r.input.bound_l na).2
  subst n a'
  obtain ⟨y₁,q₁,paired,eqy,eqq⟩ := image_kpair_pull_l (ZF.modelsKP r.native) hZF.1 Subtype.val inj full pair'
  subst y' q'
  obtain ⟨p',_,np'⟩ := r.second.2.1 n₁.val hn
  obtain ⟨p₁,_,eqp⟩ := (full (r.w 18) p').mp (r.second.bound_l np').2
  subst p'
  have nz : n₁ ≠ r.w 7 := fun eq => empty l (congrArg Subtype.val eq ▸ ln)
  have hp₁ := (r.read.names n₁ p₁ np').2 nz
  have ne : ∃ a, L.mem a n₁ := by
    apply Classical.byContradiction
    intro no
    exact nz (r.native.1.eq_of_same_members n₁ (r.w 7)
      (fun a => iff_of_false (fun ha => no ⟨a,ha⟩) (r.frame.empty a)))
  obtain ⟨m₁,hm₁,nm⟩ := r.frame.omega.exists_predecessor_of_mem_of_nonempty r.native hn₁ ne
  have nm' := image_successor_l (hEN := hZF.1) Subtype.val inj full r.native.1 nm
  have hm' : M.mem m₁.val Ω := by simpa only [r.omega] using (show M.mem m₁.val (r.w 0).val from member.mpr hm₁)
  have jm : M.mem j m₁.val := by
    rcases (nm' l).mp ln with lm' | eq
    · exact (hΩ.members_areOrdinals (ZF.modelsKP hZF) m₁.val hm').transitive l lm' j jl.predecessor_mem
    · exact hZF.1.eq_of_same_members l m₁.val eq ▸ jl.predecessor_mem
  have mp := (tail.follow m₁ n₁ p₁ nm).mp np'
  -- 同一偶时刻的大条件是尾列的后来项，故加强原大条件且仍属于 K。
  have pp₀ : Entry_d L p₁ p₀ (r.w 4) := (edge p₁ p₀ (r.w 4)).mpr
    (order.trans p₁.val u p₀.val (member.mpr hp₁) (tail.function.bound_l ju).2 hp₀ (tail.chain j m₁.val u p₁.val jm ju mp) up)
  have pH' := (tail.members p₁.val).mpr ⟨member.mpr hp₁,m₁.val,p₁.val,mp,(edge p₁ p₁ (r.w 4)).mp (bigOrder.refl p₁ hp₁)⟩
  have hq₁ : L.mem q₁ (r.w 1) := member.mp (eqQ.symm ▸ sub q₁.val qH')
  have qq₀ : Entry_d L q₁ q₀ (r.w 2) := (edge q₁ q₀ (r.w 2)).mpr
    ((smallEdge q₁.val q₀.val (sub q₁.val qH') (sub q₀.val qH)).mp qq₀)
  have even : Gm_even_d (kp_pair_l (ZF.modelsKP r.native)) (r.w 0) n₁ :=
    (image_even_l r.native hZF Subtype.val inj full r.frame.omega).mpr
      (by simpa only [r.omega] using (show Gm_even_d I Ω n₁.val from ⟨k',hk',sum⟩))
  have value := r.read.values n₁ a₁ y₁ q₁ p₁ τ i k a y q na paired even nz np' head old pair hk add (Or.inl (member.mp inn))
  -- 两坐标一起加强原积条件；保留的正是首项名字关于原 k、y 的值约束。
  obtain ⟨w,pw⟩ := (kp_pair_l (ZF.modelsKP r.native)).total q₁ p₁
  have hwC := (product.pair w).mpr ⟨q₁,hq₁,p₁,hp₁,pw⟩
  exact ⟨w,⟨hwC,q₁,p₁,pw,qH',pH'⟩,
    (product.order w v).mpr ⟨hwC,hv,q₁,p₁,q₀,p₀,pw,pair₀,qq₀,pp₀⟩,q₁,p₁,pw,value⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 指定实数是同一函数名字的唯一图解释

保留小扩张中的大泛型、同一积泛型及原首项名字的实际商值。
规范地映射给出双向完整图对应；背景中的任意关系若解释该名字，便等于 x。
同一 H、K 的两步扩张与积扩张按地参数同构，并保留这个唯一图解释。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal Descriptive Model.Forcing.Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

def Ag_real_d {Ω z c X Q G b f : M.Domain} {v : Fin 19 → M.Domain}
    (r : Ag_branch_d hZF Ω z c X Q G b v f) (H x : M.Domain) : Prop :=
  let N := smdl_structure_l I (R := r.W) r.target.1.2.1
  let E := extension_l N r.native (r.w 1) (r.w 2) (r.w 1) (fun q => M.mem q.val H)
  ∃ e : N.Domain → E.Domain, Function.Injective e ∧
    (∀ a y, E.mem y (e a) ↔ ∃ p, N.mem p a ∧ e p = y) ∧
    (∀ a t, Check_d N (r.w 7) a t → Qval_d N (r.w 1) (r.w 2) (r.w 1) (fun q => M.mem q.val H) t (e a)) ∧
    (∀ D, Dense_set_d E (e (r.w 3)) (e (r.w 4)) (e (r.w 3)) D →
      ∃ d, N.mem d (r.w 12) ∧ Qval_d N (r.w 1) (r.w 2) (r.w 1) (fun q => M.mem q.val H) d D) ∧
    ∃ t K, Ag_tail_d hZF r t K ∧
      Generic_d E (e (r.w 3)) (e (r.w 4)) (e (r.w 3)) (Em_generic_d e (fun p => M.mem p.val K)) ∧
      Generic_d N (r.w 5) (r.w 6) (r.w 5) (Ag_prod_d hZF r H K) ∧
      let F := extension_l N r.native (r.w 5) (r.w 6) (r.w 5) (Ag_prod_d hZF r H K)
      ∃ τ A, Entry_d M (r.w 7).val τ.val r.u ∧ N.mem τ (r.w 9) ∧
      ∃ j : N.Domain → F.Domain, Function.Injective j ∧
        (∀ a y, F.mem y (j a) ↔ ∃ p, N.mem p a ∧ j p = y) ∧
        (∀ a t, Check_d N (r.w 8) a t → Qval_d N (r.w 5) (r.w 6) (r.w 5) (Ag_prod_d hZF r H K) t (j a)) ∧
        ∃ y, Qval_d N (r.w 5) (r.w 6) (r.w 5) (Ag_prod_d hZF r H K) τ y ∧
          Fn0_d (j (r.w 0)) (j A) y ∧ Fn_read_d Subtype.val j y x ∧
          (∀ i a, Entry_d F i a y ↔ ∃ k w, j k = i ∧ j w = a ∧ Entry_d M k.val w.val x) ∧
          (∀ g, M.IsSetRelation I g → (Fn_read_d Subtype.val j y g ↔ g = x)) ∧
          ∃ hE : E.Models ZF,
          let D := extension_l E hE (e (r.w 3)) (e (r.w 4)) (e (r.w 3)) (Em_generic_d e (fun p => M.mem p.val K))
          ∃ u : F.Domain → D.Domain, (∀ a b, F.mem a b ↔ D.mem (u a) (u b)) ∧
            Function.Injective u ∧ Function.Surjective u ∧
            (∀ a b, Gval_d N (r.w 5) (r.w 6) (r.w 5) (Ag_prod_d hZF r H K) a b ↔
              Gval_d E (e (r.w 3)) (e (r.w 4)) (e (r.w 3)) (Em_generic_d e (fun p => M.mem p.val K)) (e a) (u b)) ∧
            Fn0_d (u (j (r.w 0))) (u (j A)) (u y) ∧ Fn_read_d Subtype.val (u ∘ j) (u y) x ∧
            ∀ g, M.IsSetRelation I g → (Fn_read_d Subtype.val (u ∘ j) (u y) g ↔ g = x)

def Ag_hgp_d (Ω z c X : M.Domain) (v : Fin 19 → M.Domain) (f H x : M.Domain) : Prop :=
  ∃ ρ γ, Rk_d I (v 10) ρ ∧ M.mem ρ γ ∧ M.IsOrdinal γ ∧ ∃ T Q G E,
    It_tree_d hZF Ω c Ω T Q G E ∧ It_owned_d I Ω Q E ∧
      It_copyable_d hZF Ω c T Q G E ∧ It_critical_bound_d I γ Q E ∧
      ∀ b, It_wf_branch_d hZF Ω Ω T Q G b → ∃ r : Ag_branch_d hZF Ω z c X Q G b v f,
        Generic_d (smdl_structure_l I (R := r.W) r.target.1.2.1) (r.w 1) (r.w 2) (r.w 1) (fun q => M.mem q.val H) ∧
          Ag_real_d hZF r H x

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 指定实数每个坐标在同一原对局中的原生行

先读取原实数及小条件的同轮坐标，再沿分支的成员满包含回收该落子。
原生加法的唯一性保证回收后的时刻仍是同一个 k+k。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal Descriptive Model.Forcing.Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Ag_branch_d.real_row_l {Ω c X R z Q G b f x H qs : M.Domain} (hΩ : M.IsOmega Ω)
    (source : Smem_d I c X R) (xt : M.TransitiveSet X)
    (native : (smdl_structure_l I (R := R) source.1.2.1).Models ZF)
    {ω κ δ A : (smdl_structure_l I (R := R) source.1.2.1).Domain}
    {p : Ag_forcing_d native ω κ δ A} (s : Ag_system_d native p)
    (hw : (smdl_structure_l I (R := R) source.1.2.1).IsOmega ω) (eqω : ω.val = Ω)
    (r : Ag_branch_d hZF Ω z c X Q G b (fun i => (s.aux_params_l native i).val) f)
    (trace : Ag_trace_d hZF Ω A.val s.A.val s.F₀.val s.R₀.val f x H) (fq : Fn0_d Ω p.Q.val qs)
    (coords : ∀ k n a y q, M.mem k Ω → M.IsOrdinalAddition I n k k → Entry_d M n a f →
      KPair_d M a y q → Entry_d M k y x ∧ Entry_d M k q qs)
    {k : (smdl_structure_l I (R := r.W) r.target.1.2.1).Domain}
    (hk : (smdl_structure_l I (R := r.W) r.target.1.2.1).mem k (r.w 0)) :
    ∃ i a y q, (smdl_structure_l I (R := r.W) r.target.1.2.1).IsOrdinalAddition
      (kp_pair_l (ZF.modelsKP r.native)) i k k ∧ Entry_d M i.val a.val f ∧
      KPair_d (smdl_structure_l I (R := r.W) r.target.1.2.1) a y q ∧ Entry_d M k.val y.val x := by
  let N := smdl_structure_l I (R := R) source.1.2.1
  let L := smdl_structure_l I (R := r.W) r.target.1.2.1
  have srcInj : Function.Injective (Subtype.val : N.Domain → M.Domain) := fun _ _ eq => Subtype.ext eq
  have srcFull := smem_full_l I source xt
  have game := s.source.image_l native hZF Subtype.val srcInj srcFull hw (eqω.symm ▸ hΩ)
  have game : Ag_game_d hZF Ω A.val p.Q.val p.T.val s.E.val s.B.val s.A.val s.F₀.val s.R₀.val := by
    simpa only [eqω] using! game
  have inj : Function.Injective (Subtype.val : L.Domain → M.Domain) := fun _ _ eq => Subtype.ext eq
  have full := smem_full_l I r.target r.transitive
  have hk' : M.mem k.val Ω := by
    have hm := (image_member_l (M := L) (N := M) Subtype.val inj full).mpr hk
    simpa only [r.omega] using hm
  obtain ⟨y,_,ky⟩ := trace.real.2.1 k.val hk'
  obtain ⟨q,_,kq⟩ := fq.2.1 k.val hk'
  obtain ⟨n,a,sum,na,pair⟩ := game.coordinate_read_l hZF hΩ trace.play trace.branch trace.real fq coords ky kq
  obtain ⟨i,add,_⟩ := ZF.ordinalAddition_existsUnique r.native (kp_pair_l (ZF.modelsKP r.native)) k
    (r.frame.omega.members_areOrdinals (ZF.modelsKP r.native) k hk)
  have sum' := image_nat_add_l r.native hZF Subtype.val inj full r.frame.omega hk add
  obtain ⟨_,_,unique⟩ := ZF.ordinalAddition_existsUnique hZF I k.val (hΩ.members_areOrdinals (ZF.modelsKP hZF) k.val hk')
  have eq := (unique n sum).trans (unique i.val sum').symm
  subst n
  obtain ⟨a₀,_,eqa⟩ := (full (r.w 10) a).mp (r.input.bound_l na).2
  subst a
  obtain ⟨y₀,q₀,pair₀,eqy,eqq⟩ := image_kpair_pull_l (ZF.modelsKP r.native) hZF.1 Subtype.val inj full pair
  exact ⟨i,a₀,y₀,q₀,add,na,pair₀,eqy.symm ▸ ky⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 原首项函数名字解释为指定实数 x

先用同一 H、K 构造积泛型及首项名字的实际商值。每个内部 k 的同轮积条件
共尾性给出真实坐标等式；函数性排除其他值，完整图解释的唯一性给出 g=x。
最后沿保持地参数的积／两步扩张同构运输同一名字值和完整图解释。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal Descriptive Model.Forcing.Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Ag_branch_d.function_value_l {Ω c X R z Q G b f x H qs : M.Domain} (hΩ : M.IsOmega Ω)
    (source : Smem_d I c X R) (xt : M.TransitiveSet X)
    (native : (smdl_structure_l I (R := R) source.1.2.1).Models ZF)
    {ω κ δ A : (smdl_structure_l I (R := R) source.1.2.1).Domain}
    {p : Ag_forcing_d native ω κ δ A} (s : Ag_system_d native p)
    (hw : (smdl_structure_l I (R := R) source.1.2.1).IsOmega ω) (eqω : ω.val = Ω)
    (inh : ∃ y, (smdl_structure_l I (R := R) source.1.2.1).mem y A)
    (r : Ag_branch_d hZF Ω z c X Q G b (fun i => (s.aux_params_l native i).val) f)
    (sub : M.MemberSubset H p.Q.val) (trace : Ag_trace_d hZF Ω A.val s.A.val s.F₀.val s.R₀.val f x H)
    (fq : Fn0_d Ω p.Q.val qs)
    (coords : ∀ k n a y q, M.mem k Ω → M.IsOrdinalAddition I n k k → Entry_d M n a f →
      KPair_d M a y q → Entry_d M k y x ∧ Entry_d M k q qs)
    (cofinal : ∀ q, M.mem q H → ∀ i, M.mem i Ω → ∃ k u, M.mem i k ∧ Entry_d M k u qs ∧ Entry_d M u q p.T.val)
    (small : Generic_d (smdl_structure_l I (R := r.W) r.target.1.2.1) (r.w 1) (r.w 2) (r.w 1) (fun q => M.mem q.val H))
    (big : Ag_big_d hZF r H) : Ag_real_d hZF r H x := by
  let N := smdl_structure_l I (R := r.W) r.target.1.2.1
  obtain ⟨e,ei,ef,echecks,cover,t,K,tail,bigG,prodG⟩ := r.product_generic_l hZF hΩ source native s small big
  let V := Ag_prod_d hZF r H K
  let F := extension_l N r.native (r.w 5) (r.w 6) (r.w 5) V
  obtain ⟨product,OP,hc,top,A',a,w,ca,cw,names⟩ := r.product_data_l hZF hΩ source native s
  have hF : F.Models ZF := preserves_zf_l OP r.native prodG
  have inj : Function.Injective (Subtype.val : N.Domain → M.Domain) := fun _ _ eq => Subtype.ext eq
  have full := smem_full_l I r.target r.transitive
  have member {a b : N.Domain} : M.mem a.val b.val ↔ N.mem a b := image_member_l (M := N) (N := M) Subtype.val inj full
  -- 零项固定原函数名字；其全局函数性在同一积泛型中给出实际函数值。
  have hb := num_mem_l r.native.1 r.frame.omega (show Num_d 0 (r.w 7) from r.frame.empty)
  have hb' : M.mem (r.w 7).val Ω := by simpa only [r.omega] using (show M.mem (r.w 7).val (r.w 0).val from member.mpr hb)
  obtain ⟨τ',_,hτ'⟩ := r.second.2.1 (r.w 7).val hb'
  obtain ⟨τ,_,eqτ⟩ := (full (r.w 18) τ').mp (r.second.bound_l hτ').2
  subst τ'
  have hτ := (r.read.names (r.w 7) τ hτ').1 rfl
  have fnτ := names τ hτ
  obtain ⟨p₀,hp₀⟩ := prodG.inhabited
  have base := prodG.upward p₀ (r.w 8) hp₀ hc (top p₀ (prodG.proper p₀ hp₀).1)
  obtain ⟨j,checks,jfull,ji⟩ := check_map_l OP r.native prodG base
  obtain ⟨y,value⟩ := name_value_l (R := r.w 6) (z := r.w 5) (U := V) fnτ.2.2.1
  have fn : F.IsSetFunctionFromTo (kp_pair_l (ZF.modelsKP hF)) y (j (r.w 0)) (j A') :=
    fn_name_val_l OP r.native prodG fnτ base (checks _ _ ca) (checks _ _ cw) value
  -- 对每个内部坐标，后来同轮积条件保持旧值约束，真值定理排除取值不等。
  have rows k (hk : N.mem k (r.w 0)) : ∃ a : N.Domain,
      Entry_d M k.val a.val x ∧ Entry_d F (j k) (j a) y := by
    obtain ⟨i,a,y₀,q,add,old,pair,xy⟩ := r.real_row_l hZF hΩ source xt native s hw eqω trace fq coords hk
    have consistent := r.value_cofinal_l hZF hΩ source xt native s hw eqω inh sub trace fq coords cofinal
      tail hτ' old pair hk add
    exact ⟨y₀,xy,ag_entry_of_cofinal_value_l r.native OP prodG hc j checks value consistent⟩
  have fx : M.IsSetFunctionFromTo I x (r.w 0).val A.val := by
    simpa only [r.omega] using! fn0_function_l (ZF.modelsKP hZF) trace.real
  -- 输入域相同且逐点输出相同，故两个完整函数图双向对应，并唯一确定背景实数。
  obtain ⟨read,graph,unique⟩ := function_read_l (ZF.modelsKP hZF) (ZF.modelsKP hF) Subtype.val inj full j ji jfull fx fn rows
  -- 同一积扩张与同一 H、K 的两步扩张识别，地参数沿同构原样保留。
  obtain ⟨O,hbQ,smallTop,_⟩ := r.small_data_l hZF hΩ source native s
  obtain ⟨L,_⟩ := r.dense_data_l hZF hΩ source native s
  let E := extension_l N r.native (r.w 1) (r.w 2) (r.w 1) (fun q => M.mem q.val H)
  have hE : E.Models ZF := preserves_zf_l O r.native small
  have order := image_cond_order_l (ZF.modelsKP r.native) hE.1 e ei ef L
  obtain ⟨q₀,hq₀⟩ := small.inhabited
  have hbH := small.upward q₀ (r.w 7) hq₀ hbQ (smallTop q₀ (small.proper q₀ hq₀).1)
  obtain ⟨_,iso⟩ := product.extension_l r.native O L OP smallTop small hbH e echecks
    (fun _ _ _ _ => Iff.rfl) order bigG
  have same : Prod_generic_d r.native (r.w 5) e (Em_generic_d e (fun p : N.Domain => M.mem p.val K)) = V := by
    funext p
    apply propext
    exact ⟨fun ⟨hp,q,a,pair,hq,a',ha,eq⟩ => ⟨hp,q,a,pair,hq,ei eq ▸ ha⟩,
      fun ⟨hp,q,a,pair,hq,ha⟩ => ⟨hp,q,a,pair,hq,a,ha,rfl⟩⟩
  let D := extension_l E hE (e (r.w 3)) (e (r.w 4)) (e (r.w 3)) (Em_generic_d e (fun p => M.mem p.val K))
  have iso : Miso_over_d F D (Gval_d N (r.w 5) (r.w 6) (r.w 5) V)
      (fun a => Gval_d E (e (r.w 3)) (e (r.w 4)) (e (r.w 3)) (Em_generic_d e (fun p => M.mem p.val K)) (e a)) := by
    dsimp only [F]
    exact same ▸ iso
  obtain ⟨u,mem,ui,uo,over⟩ := iso
  have uf a b : D.mem b (u a) ↔ ∃ c, F.mem c a ∧ u c = b := by
    obtain ⟨c,rfl⟩ := uo b
    exact ⟨fun h => ⟨c,(mem c a).mpr h,rfl⟩,fun ⟨d,hd,eq⟩ => eq ▸ (mem d a).mp hd⟩
  have jf a b : D.mem b ((u ∘ j) a) ↔ ∃ c, N.mem c a ∧ (u ∘ j) c = b := by
    apply (uf (j a) b).trans
    constructor
    · rintro ⟨d,hd,eq⟩
      obtain ⟨c,hc,cd⟩ := (jfull a d).mp hd
      exact ⟨c,hc,(congrArg u cd).trans eq⟩
    · rintro ⟨c,hc,eq⟩
      exact ⟨j c,(jfull a (j c)).mpr ⟨c,hc,rfl⟩,eq⟩
  have hD : D.Models ZF := preserves_zf_l order hE bigG
  have fn' : D.IsSetFunctionFromTo (kp_pair_l (ZF.modelsKP hD)) (u y) (u (j (r.w 0))) (u (j A')) :=
    image_function_l (hEN := hD.1) (hPN := KP.exists_pair (ZF.modelsKP hD)) u ui uf fn
  have rows' k (hk : N.mem k (r.w 0)) : ∃ a : N.Domain,
      Entry_d M k.val a.val x ∧ Entry_d D ((u ∘ j) k) ((u ∘ j) a) (u y) := by
    obtain ⟨a,ka,ka'⟩ := rows k hk
    exact ⟨a,ka,(image_entry_iff_l u ui uf (KP.exists_pair (ZF.modelsKP hF)) hD.1 (j k) (j a) y).mp ka'⟩
  obtain ⟨read',_,unique'⟩ := function_read_l (ZF.modelsKP hZF) (ZF.modelsKP hD) Subtype.val inj full
    (u ∘ j) (ui.comp ji) jf fx fn' rows'
  exact ⟨e,ei,ef,echecks,cover,t,K,tail,bigG,prodG,τ,A',hτ',hτ,j,ji,jfull,checks,y,value,
    fn0_of_function_l (ZF.modelsKP hF) fn,read,graph,unique,hE,u,mem,ui,uo,over,
    fn0_of_function_l (ZF.modelsKP hD) fn',read',unique'⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 同一良基分支的稠密名字要求在小扩张中实际成立

H 已在该分支模型中证明泛型。规范地嵌入只构造一次；每个稠密名字在
原辅助列中出现后，下一大条件的规范像确实属于其解释值。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal Descriptive Model.Forcing.Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Ag_branch_d.dense_truth_l {Ω c X R z Q G b f x H q : M.Domain} (hΩ : M.IsOmega Ω)
    (source : Smem_d I c X R) (xt : M.TransitiveSet X)
    (native : (smdl_structure_l I (R := R) source.1.2.1).Models ZF)
    {ω κ δ A : (smdl_structure_l I (R := R) source.1.2.1).Domain}
    {p : Ag_forcing_d native ω κ δ A} (s : Ag_system_d native p)
    (hw : (smdl_structure_l I (R := R) source.1.2.1).IsOmega ω) (eqω : ω.val = Ω)
    (inh : ∃ y, (smdl_structure_l I (R := R) source.1.2.1).mem y A)
    (r : Ag_branch_d hZF Ω z c X Q G b (fun i => (s.aux_params_l native i).val) f)
    (sub : M.MemberSubset H p.Q.val)
    (generic : Generic_d (smdl_structure_l I (R := R) source.1.2.1) p.Q p.T p.Q (fun t => M.mem t.val H))
    (trace : Ag_trace_d hZF Ω A.val s.A.val s.F₀.val s.R₀.val f x H) (fq : Fn0_d Ω p.Q.val q)
    (coords : ∀ k n a y t, M.mem k Ω → M.IsOrdinalAddition I n k k → Entry_d M n a f →
      KPair_d M a y t → Entry_d M k y x ∧ Entry_d M k t q)
    (cofinal : ∀ t, M.mem t H → ∀ i, M.mem i Ω → ∃ k u, M.mem i k ∧ Entry_d M k u q ∧ Entry_d M u t p.T.val) :
    Ag_hits_d hZF r H := by
  let N := smdl_structure_l I (R := r.W) r.target.1.2.1
  let H₀ := fun q : N.Domain => M.mem q.val H
  have generic' := r.small_generic_l hZF hΩ source xt native s inh sub generic
  obtain ⟨O,hb,top,names⟩ := r.small_data_l hZF hΩ source native s
  obtain ⟨t,ht⟩ := generic'.inhabited
  have base := generic'.upward t (r.w 7) ht hb (top t (generic'.proper t ht).1)
  obtain ⟨e,checks,full,inj⟩ := check_map_l O r.native generic' base
  refine ⟨e,inj,full,checks,?_⟩
  intro i d l a id la li
  have hd : N.mem d (r.w 12) := (r.target.2 d.val (r.w 12).val).mpr
    ⟨d.property,(r.w 12).property,(r.first.bound_l id).2⟩
  obtain ⟨D,value⟩ := name_value_l (R := r.w 2) (z := r.w 1) (U := H₀) (names d hd)
  exact ⟨D,value,ag_value_of_cofinal_demand_l r.native O generic' hb e checks value
    (r.demand_cofinal_l hZF hΩ source xt native s hw eqω inh sub trace fq coords cofinal id la li)⟩

theorem Ag_gp_d.realize_l {Ω c X R z f x H q : M.Domain} (hΩ : M.IsOmega Ω)
    (source : Smem_d I c X R) (xt : M.TransitiveSet X)
    (native : (smdl_structure_l I (R := R) source.1.2.1).Models ZF)
    {ω κ δ A : (smdl_structure_l I (R := R) source.1.2.1).Domain}
    {p : Ag_forcing_d native ω κ δ A} (s : Ag_system_d native p)
    (hw : (smdl_structure_l I (R := R) source.1.2.1).IsOmega ω) (eqω : ω.val = Ω)
    (inh : ∃ y, (smdl_structure_l I (R := R) source.1.2.1).mem y A)
    (good : Ag_gp_d hZF Ω z c X (fun i => (s.aux_params_l native i).val) f)
    (sub : M.MemberSubset H p.Q.val)
    (generic : Generic_d (smdl_structure_l I (R := R) source.1.2.1) p.Q p.T p.Q (fun t => M.mem t.val H))
    (trace : Ag_trace_d hZF Ω A.val s.A.val s.F₀.val s.R₀.val f x H) (fq : Fn0_d Ω p.Q.val q)
    (coords : ∀ k n a y t, M.mem k Ω → M.IsOrdinalAddition I n k k → Entry_d M n a f →
      KPair_d M a y t → Entry_d M k y x ∧ Entry_d M k t q)
    (cofinal : ∀ t, M.mem t H → ∀ i, M.mem i Ω → ∃ k u, M.mem i k ∧ Entry_d M k u q ∧ Entry_d M u t p.T.val) :
    Ag_hgp_d hZF Ω z c X (fun i => (s.aux_params_l native i).val) f H x := by
  obtain ⟨ρ,γ,rank,lower,ordinal,T,Q,G,E,tree,owned,copy,bound,branches⟩ := good
  refine ⟨ρ,γ,rank,lower,ordinal,T,Q,G,E,tree,owned,copy,bound,?_⟩
  intro b wf
  obtain ⟨r⟩ := branches b wf
  have small := r.small_generic_l hZF hΩ source xt native s inh sub generic
  have hits := r.dense_truth_l hZF hΩ source xt native s hw eqω inh sub generic trace fq coords cofinal
  have big := r.big_generic_l hZF hΩ source native s small hits
  exact ⟨r,small,r.function_value_l hZF hΩ source xt native s hw eqω inh sub trace fq coords cofinal small big⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 7.23 专用博弈的实际地面 II 策略

分离树、第一字母域编码和低秩界均由原小、大坍缩构造取得。
7.12 的泛型分支被实际大泛型排除，余下的同一 II 策略在全部合法对局上
给出原专用辅助树的广义 demanding 投影；分离标签已沿每条真实根腿解码。
给定同一根的小泛型和实数时，实际构造服从此策略的原对局，保留指定实数，
并使小条件列在该泛型中逐尾共尾。每条良基枝保留字母表的逐点固定性，
自动取得同一 H 的泛型性，并把稠密名字的非反驳要求解释为实际成员关系。
同一名字族覆盖分支小扩张的全部大稠密集，大条件尾列的上闭包因而给出实际大泛型。
原首项函数名字在同一积泛型下的完整图唯一解释为指定实数；该结论沿保持地参数的
同构进入同一 H、K 的两步扩张，所有良基枝均保留这个 x。
出口保留完整原树、各活动边的所属强度证书和全运行的实际复制性质；返回入口据此选择同一原树的枝。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal Descriptive Model.Forcing.Internal
universe u
variable {M : Structure.{u}} (hZFC : M.Models ZFC)
local notation "hZF" => ZFC.models_zf_l hZFC
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem ag_strategy_l {Ω c X R : M.Domain} (hΩ : M.IsOmega Ω)
    (certificate : Zc_model_d I Ω c X R) (source : Smem_d I c X R) (trans : M.TransitiveSet X)
    {ω κ δ A Z : (smdl_structure_l I (R := R) certificate.model.2.1).Domain}
    (hw : (smdl_structure_l I (R := R) certificate.model.2.1).IsOmega ω)
    (woodin : Woodin_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l (certificate.native_l I hZF hΩ)))) δ)
    (rank : V_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l (certificate.native_l I hZF hΩ)))) δ Z)
    (letters : (smdl_structure_l I (R := R) certificate.model.2.1).mem A Z)
    (inh : ∃ x, (smdl_structure_l I (R := R) certificate.model.2.1).mem x A)
    (small : (smdl_structure_l I (R := R) certificate.model.2.1).mem κ δ)
    (count : Pc_count_d I Ω X R δ.val) :
    ∃ p : Ag_forcing_d (ZFC.models_zf_l (certificate.native_l I hZF hΩ)) ω κ δ A,
    ∃ s : Ag_system_d (ZFC.models_zf_l (certificate.native_l I hZF hΩ)) p,
    ∃ e o T U V : (smdl_structure_l I (R := R) certificate.model.2.1).Domain,
      Nonempty (Td_retag_d (ZFC.models_zf_l (certificate.native_l I hZF hΩ)) ω s.A s.S p.D s.V₀ e o T U V) ∧
      Td_separated_d T ∧ Td_alphabet_d T U V ∧ ∃ z σ : M.Domain,
        (∀ x, ¬ M.mem x z) ∧ Gt_strategy_d hZF false Ω s.A.val s.R₀.val σ ∧
        (∀ f, Fn0_d Ω s.A.val f → Branch_d s.F₀.val s.R₀.val f → Gm_follows_d I false Ω σ f →
          Ag_gp_d hZF Ω z c X (fun i => (s.aux_params_l (ZFC.models_zf_l (certificate.native_l I hZF hΩ)) i).val) f) ∧
        ∀ H x, M.MemberSubset H p.Q.val →
          Generic_d (smdl_structure_l I (R := R) certificate.model.2.1) p.Q p.T p.Q (fun r => M.mem r.val H) →
          Fn0_d Ω A.val x → ∃ f q,
            Ag_trace_d hZF Ω A.val s.A.val s.F₀.val s.R₀.val f x H ∧
            Gm_follows_d I false Ω σ f ∧
            Ag_hgp_d hZF Ω z c X (fun i => (s.aux_params_l (ZFC.models_zf_l (certificate.native_l I hZF hΩ)) i).val) f H x ∧
            Fn0_d Ω p.Q.val q ∧
            (∀ k n a y r, M.mem k Ω → M.IsOrdinalAddition I n k k → Entry_d M n a f →
              KPair_d M a y r → Entry_d M k y x ∧ Entry_d M k r q) ∧
            (∀ i j r t, M.mem i j → Entry_d M i r q → Entry_d M j t q → Entry_d M t r p.T.val) ∧
            ∀ r, M.mem r H → ∀ i, M.mem i Ω → ∃ k t, M.mem i k ∧ Entry_d M k t q ∧ Entry_d M t r p.T.val := by
  let N := smdl_structure_l I (R := R) certificate.model.2.1
  have native := certificate.native_l I hZF hΩ
  have hN := ZFC.models_zf_l native
  let J := kp_pair_l (ZF.modelsKP hN)
  have wd := woodin
  obtain ⟨ω₀,_,hw₀,above,regular,strong,_,_⟩ := woodin
  have eq := hN.1.eq_of_same_members ω₀ ω (fun n => ⟨hw₀.2 ω hw.1 n,hw.2 ω₀ hw₀.1 n⟩)
  subst ω₀
  obtain ⟨p⟩ := ag_forcing_l hN native hw above regular strong (strong.1.1.transitive κ small) inh
  obtain ⟨s⟩ := p.system_l hN hw inh
  obtain ⟨e,o,T,U,V,a,_,tree,sep,alphabet,⟨retag⟩,chosen,_,coding⟩ := s.separate_l hN hw
  have hA := (s.rank_mem_l hN hw regular.isLimitOrdinal above small rank letters).2.2.1
  obtain ⟨v,F,L,G,J₀,B,W,O,Z₀,g,eω,eδ,eA,eT,game⟩ := td_game_l native (S := T) hw regular.isLimitOrdinal above rank hA
  have zero := hN.1.eq_of_same_members v.e p.b (fun x => iff_of_false (game.setup.empty x) (p.empty x))
  have root : N.mem v.e s.R₀ := zero.symm ▸ s.source.root_l hN hw p.empty
  have next := s.source.pruned_l hN hw ⟨p.b,p.small_base⟩ inh
  have result := game.corollary712_l hZFC hΩ certificate source trans
    (by simpa only [eδ] using wd) (by simpa only [eω,eA,eT] using tree)
    (by simpa only [eT] using alphabet) chosen (by simpa only [eT] using sep)
    (by simpa only [eδ] using count) (by simpa only [eδ] using (show ∃ P, N.IsPowerSetOf P δ ∧ N.CardinalLessOrEqual J U P from ⟨p.K,p.power,coding⟩))
    (by simpa only [eω,eA] using! s.source.space) (s.source.tree_l hN) root
    (by simpa only [eω] using! next)
  rcases result with good | bad
  · have good : ∃ z σ, (∀ x, ¬ M.mem x z) ∧ Gt_strategy_d hZF false Ω s.A.val s.R₀.val σ ∧
        ∀ f, Fn0_d Ω s.A.val f → Branch_d s.F₀.val s.R₀.val f → Gm_follows_d I false Ω σ f →
          Td_fixed_gp_d hZF Ω z c X s.A.val T.val f := by
      simpa only [eA,eT] using good
    obtain ⟨z,σ,empty,strategy,taggedPlays⟩ := good
    obtain ⟨eqω,_,_⟩ := tg_numbers_mem_l hZF hΩ certificate source trans ω hw
    have plays f (ff : Fn0_d Ω s.A.val f) (branch : Branch_d s.F₀.val s.R₀.val f)
        (follows : Gm_follows_d I false Ω σ f) : Ag_gp_d hZF Ω z c X (fun i => (s.aux_params_l hN i).val) f := by
      have raw := (taggedPlays f ff branch follows).untag_l hZF hΩ source trans hN hw eqω retag
        s.alphabet alphabet empty ff
      exact (s.frame_l hN hw).read_gp_l hZF hΩ source trans hN eqω ff raw
    refine ⟨p,s,e,o,T,U,V,⟨retag⟩,sep,alphabet,z,σ,empty,strategy,plays,?_⟩
    intro H x sub generic fx
    have infinite : N.IsInfiniteCardinal J ω δ :=
      ⟨strong.1,ZF.exists_inclusionInjection hN J (strong.1.1.transitive ω above)⟩
    obtain ⟨f,q,trace,follows,fq,coords,chain,cofinal⟩ := s.ground_play_l hZF hΩ (ZFC.dc_l I hZFC hΩ)
      source trans hN hw infinite (strong.1.1.transitive κ small) count sub generic fx strategy
    exact ⟨f,q,trace,follows,(plays f trace.play trace.branch follows).realize_l hZF hΩ
      source trans hN s hw eqω inh sub generic trace fq coords cofinal,fq,coords,chain,cofinal⟩
  · have bad : Td_tree_collapse_d hN ω δ s.A s.F₀ s.R₀ U V T := by
      simpa only [eω,eδ,eA,eT] using bad
    exact (s.not_collapse_l hZF hΩ certificate source trans (ZFC.dc_l I hZFC hΩ) hw above strong small retag count bad).elim

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 7.23 同一原对局的实际返回枝

demanding 运行生产完整复制证书，返回定理据此选择共尾良基枝。
该枝同时保留原临界点界、小泛型 H、实际大泛型和指定实数 x 的名字解释。
可数根入口自动生产幂集计数，不把它作为另一项独立前提。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal Descriptive Model.Forcing.Internal
universe u
variable {M : Structure.{u}}
section
variable (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

def Ag_return_d (Ω z c X d Y π : M.Domain) (v : Fin 19 → M.Domain) (f H x : M.Domain) : Prop :=
  ∃ ρ γ T Q G E b, Rk_d I (v 10) ρ ∧ M.mem ρ γ ∧ M.IsOrdinal γ ∧
    It_tree_d hZF Ω c Ω T Q G E ∧ It_critical_bound_d I γ Q E ∧
    It_return_at_d hZF Ω z T Q G d Y π b ∧ It_wf_branch_d hZF Ω Ω T Q G b ∧
    ∃ r : Ag_branch_d hZF Ω z c X Q G b v f, ∃ σ,
      Smap_d I Ω r.d d r.N Y σ ∧ It_comp_d r.j σ π ∧
      M.CardinalLessOrEqual I r.N Ω ∧
      Generic_d (smdl_structure_l I (R := r.W) r.target.1.2.1)
        (r.w 1) (r.w 2) (r.w 1) (fun q => M.mem q.val H) ∧ Ag_real_d hZF r H x

end
variable (hZFC : M.Models ZFC)
local notation "hZF" => ZFC.models_zf_l hZFC
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

/-- 从已构造的全分支结论选择实际返回枝；使用同一原树和同一 H、x。 -/
theorem Ag_hgp_d.return_l {Ω z c X R d Y S θ π f H x : M.Domain} {v : Fin 19 → M.Domain}
    (good : Ag_hgp_d hZF Ω z c X v f H x)
    (source : Smem_d I c X R) (trans : M.TransitiveSet X)
    (count : M.CardinalLessOrEqual I X Ω) (empty : ∀ a, ¬ M.mem a z)
    (rank : V_d I θ Y) (target : Smem_d I d Y S) (embed : Smap_d I Ω c d X Y π) :
    Ag_return_d hZF Ω z c X d Y π v f H x := by
  obtain ⟨ρ,γ,rk,lower,ordinal,T,Q,G,E,tree,_,copy,bound,branches⟩ := good
  obtain ⟨b,returned⟩ := it_copyable_return_l hZFC tree copy source trans count empty rank target embed
  have data := returned
  obtain ⟨L,A,p,F,R₀,q,d₀,N,W,P,σ,branch,system,limit,mn,_,_,_,_,_,_,_,order,wfN⟩ := data
  have wf := It_branch_d.wf_of_limit_l hZF tree.diagram tree.omega branch system order limit mn wfN
  obtain ⟨r,small,real⟩ := branches b wf
  obtain ⟨σ,embed,square⟩ := returned.factor_l hZF tree.omega tree.diagram r.cone r.leg
  obtain ⟨ec,enumerated⟩ := tree.ja_enum_l hZFC source.1 count
  have count' := r.cone.countable_enum_l hZF tree.omega tree.diagram wf.1.subset
    (ZF.exists_inclusionInjection hZF I wf.1.subset) enumerated
  exact ⟨ρ,γ,T,Q,G,E,b,rk,lower,ordinal,tree,bound,returned,wf,r,σ,embed,square,count',small,real⟩

/-- 给定可数原根及其秩层嵌入，专用博弈自动产生吸收指定实数的返回枝。 -/
theorem ag_absorb_l {Ω c X R d Y S θ π : M.Domain} (hΩ : M.IsOmega Ω)
    (certificate : Zc_model_d I Ω c X R) (source : Smem_d I c X R) (trans : M.TransitiveSet X)
    (count : M.CardinalLessOrEqual I X Ω)
    (targetRank : V_d I θ Y) (target : Smem_d I d Y S) (embed : Smap_d I Ω c d X Y π)
    {ω κ δ A Z : (smdl_structure_l I (R := R) certificate.model.2.1).Domain}
    (hw : (smdl_structure_l I (R := R) certificate.model.2.1).IsOmega ω)
    (woodin : Woodin_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l (certificate.native_l I hZF hΩ)))) δ)
    (rank : V_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l (certificate.native_l I hZF hΩ)))) δ Z)
    (letters : (smdl_structure_l I (R := R) certificate.model.2.1).mem A Z)
    (inh : ∃ x, (smdl_structure_l I (R := R) certificate.model.2.1).mem x A)
    (small : (smdl_structure_l I (R := R) certificate.model.2.1).mem κ δ) :
    ∃ p : Ag_forcing_d (ZFC.models_zf_l (certificate.native_l I hZF hΩ)) ω κ δ A,
    ∃ s : Ag_system_d (ZFC.models_zf_l (certificate.native_l I hZF hΩ)) p,
    ∃ z, (∀ a, ¬ M.mem a z) ∧
      ∀ H x, M.MemberSubset H p.Q.val →
        Generic_d (smdl_structure_l I (R := R) certificate.model.2.1) p.Q p.T p.Q (fun t => M.mem t.val H) →
        Fn0_d Ω A.val x → ∃ f,
          Ag_trace_d hZF Ω A.val s.A.val s.F₀.val s.R₀.val f x H ∧
          Ag_return_d hZF Ω z c X d Y π
            (fun i => (s.aux_params_l (ZFC.models_zf_l (certificate.native_l I hZF hΩ)) i).val) f H x := by
  have native := ZFC.models_zf_l (certificate.native_l I hZF hΩ)
  obtain ⟨P,power⟩ := ZF.exists_powerSet native δ
  have carrier x : M.mem x P.val ↔ M.mem x X ∧ Rd_entry_d x P.val R :=
    ⟨fun hx => ⟨trans P.val P.property x hx,
      (source.2 x P.val).mpr ⟨trans P.val P.property x hx,P.property,hx⟩⟩,
      fun hx => ((source.2 x P.val).mp hx.2).2.2⟩
  obtain ⟨i,hi⟩ := count
  obtain ⟨j,hj⟩ := ZF.exists_inclusionInjection hZF I (trans P.val P.property)
  have pc := pc_count_l hZF certificate.model.2.1 δ P power carrier
    (ZF.exists_compositionInjection hZF I hj hi)
  obtain ⟨p,s,e,o,T,U,V,_,_,_,z,σ,empty,_,_,plays⟩ :=
    ag_strategy_l hZFC hΩ certificate source trans hw woodin rank letters inh small pc
  refine ⟨p,s,z,empty,?_⟩
  intro H x sub generic fx
  obtain ⟨f,_,trace,_,good,_⟩ := plays H x sub generic fx
  exact ⟨f,trace,good.return_l hZFC source trans ⟨i,hi⟩ empty targetRank target embed⟩

end YesMetaZFC.SetTheory.LargeCardinal
